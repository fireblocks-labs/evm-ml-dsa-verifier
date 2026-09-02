// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// Correctness + gas benchmarks for the NTT variants in ZZZ_NttVariants.sol,
// using the repo's nttFw as the oracle. See ZZZ_NttVariants.sol for design notes.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {nttFw} from "./vendor/ZKNOX_NTT_dilithium.sol";
import {q} from "./vendor/ZKNOX_dilithium_utils.sol";
import {
    nttFwV2,
    nttFwV3,
    lazyBarrett,
    packCoeffs,
    unpackCoeffs,
    macOne,
    macOneLazy,
    reduceOne,
    macPackedExact,
    macPackedLazy,
    reducePacked
, nttFwTable} from "./ZZZ_NttVariants.sol";

contract NttVariantsTest is Test {
    // ------------------------------------------------------------------ utils

    function rndPoly(uint256 seed) internal pure returns (uint256[] memory a) {
        a = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            a[i] = uint256(keccak256(abi.encodePacked(seed, i))) % q;
        }
    }

    function clonePoly(uint256[] memory a) internal pure returns (uint256[] memory b) {
        b = new uint256[](a.length);
        for (uint256 i = 0; i < a.length; i++) {
            b[i] = a[i];
        }
    }

    function assertEqPoly(uint256[] memory x, uint256[] memory y, string memory tag) internal pure {
        assertEq(x.length, y.length, tag);
        for (uint256 i = 0; i < x.length; i++) {
            assertEq(x[i], y[i], tag);
        }
    }

    // ------------------------------------------------------------ correctness

    /// V2 must be bit-exact equal to the repo's nttFw.
    function testCorrectnessV2() public view {
        uint256[] memory prof = new uint256[](16);
        for (uint256 s = 0; s < 3; s++) {
            uint256[] memory a = rndPoly(s + 1);
            uint256[] memory ref = nttFw(clonePoly(a));
            uint256[] memory got = nttFwV2(clonePoly(a), prof);
            assertEqPoly(got, ref, "V2 vs nttFw");
        }
        // edge: all coefficients q-1
        uint256[] memory e = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            e[i] = q - 1;
        }
        assertEqPoly(nttFwV2(clonePoly(e), prof), nttFw(clonePoly(e)), "V2 edge q-1");
    }

    /// V3 (packed SWAR) emits LAZY lanes: every coefficient must be < 17q and
    /// congruent mod q to nttFw's canonical output (C9a/C9f; the lazy matvec
    /// accumulator, the only consumer, admits < 17q lanes — O7/O8).
    function assertEqPolyLazy(uint256[] memory got, uint256[] memory ref, string memory tag)
        internal
        pure
    {
        for (uint256 i = 0; i < 256; i++) {
            assertLt(got[i], 17 * q, tag);
            assertEq(got[i] % q, ref[i], tag);
        }
    }

    function testCorrectnessV3() public view {
        uint256[] memory prof = new uint256[](16);
        for (uint256 s = 0; s < 3; s++) {
            uint256[] memory a = rndPoly(s + 101);
            uint256[] memory ref = nttFw(clonePoly(a));
            uint256[] memory got = unpackCoeffs(nttFwV3(packCoeffs(a), prof, nttFwTable()));
            assertEqPolyLazy(got, ref, "V3 vs nttFw");
        }
        // edge: all coefficients q-1 (worst case for the lazy lane bounds)
        uint256[] memory e = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            e[i] = q - 1;
        }
        assertEqPolyLazy(unpackCoeffs(nttFwV3(packCoeffs(e), prof, nttFwTable())), nttFw(clonePoly(e)), "V3 edge q-1");
        // pack/unpack roundtrip sanity
        uint256[] memory r = rndPoly(999);
        assertEqPoly(unpackCoeffs(packCoeffs(r)), r, "pack roundtrip");
    }

    /// Barrett constant check: for x <= 15q(q-1) (max product in any V3 layer),
    /// the TWO-STEP LANE-LOCAL reduction lazyBarrett(x) is congruent to x mod q
    /// and < 2q. Step 1 uses MU33 = floor(2^33/q) = 1025, step 2 the unit step
    /// floor(2^23/q) == 1 (multiply elided).
    function testBarrettConstants() public pure {
        uint256 xmax = 15 * q * (q - 1); // 1053470710702080 < 2^50
        for (uint256 i = 0; i < 500; i++) {
            uint256 x = uint256(keccak256(abi.encodePacked("barrett", i))) % (xmax + 1);
            uint256 r = lazyBarrett(x);
            assertLt(r, 2 * q, "barrett range");
            assertEq(r % q, x % q, "barrett congruence");
        }
        // edges
        assertEq(lazyBarrett(0), 0);
        assertEq(lazyBarrett(q) % q, 0);
        assertLt(lazyBarrett(q), 2 * q);
        assertEq(lazyBarrett(xmax) % q, xmax % q);
        assertLt(lazyBarrett(xmax), 2 * q);
        assertEq(lazyBarrett(1 << 50) % q, (1 << 50) % q);
        assertLt(lazyBarrett(1 << 50), 2 * q);
        // LANE-LOCALITY over the forward domain: the coarse multiply stays
        // inside its own 64-bit lane, so the packed V3 kernel needs no spread
        // and no repack, and the step-1 quotient fits the 31-bit QHATM31 window.
        assertLt(xmax * 1025, 1 << 64, "x*MU33 < 2^64");
        assertLt((xmax * 1025) >> 33, 1 << 31, "qhat < 2^31");
        uint256 x1 = xmax - (((xmax * 1025) >> 33) * q);
        assertLe(x1, 7508854654, "step 1 output < 2^33");
        assertLe(x1 >> 23, 895, "step 2 quotient fits the 31-bit mask");
        // TIGHTNESS: the first x whose reduction is no longer < 2q is
        // 10285325456994078, which is 9.7633x the forward worst product.
        assertEq(lazyBarrett(10285325456994078), 2 * q, "first failure");
        assertLt(lazyBarrett(10285325456994077), 2 * q, "one below still holds");
        assertEq((10285325456994078 * 10000) / xmax, 97632, "forward margin is 9.7633x");
    }

    // -------------------------------------------------------------------- gas
    // Each variant is measured in its own test at fresh memory, and the
    // vendored nttFw reference (testGasV1Baseline) is measured the same way, so
    // the two are directly comparable: 182,470 for nttFw against 45,701 for V3.
    // Both sides are compiled through via-IR — foundry.toml sets via_ir = true
    // for the whole tree, vendored files included — which is why nttFw prints
    // ~7% under the legacy-codegen figure (~195.6k) quoted for it elsewhere.

    function testGasV1Baseline() public view {
        uint256[] memory a = rndPoly(1);
        uint256 g0 = gasleft();
        a = nttFw(a);
        uint256 used = g0 - gasleft();
        console.log("V1 nttFw (repo) fresh-mem gas:", used);
    }

    function testGasV2() public view {
        uint256[] memory a = rndPoly(1);
        uint256[] memory prof = new uint256[](16);
        uint256 g0 = gasleft();
        a = nttFwV2(a, prof);
        uint256 used = g0 - gasleft();
        console.log("V2 tight one-per-word gas:", used);
        string[8] memory names = ["L1 t=128", "L2 t=64", "L3 t=32", "L4 t=16", "L5 t=8", "L6 t=4", "L7 t=2", "L8 t=1"];
        for (uint256 i = 0; i < 8; i++) {
            console.log(string.concat("  V2 ", names[i]), prof[i] - prof[i + 1]);
        }
    }

    function testGasV3() public view {
        uint256[] memory a = rndPoly(1);
        uint256[] memory w = packCoeffs(a);
        uint256[] memory prof = new uint256[](16);
        uint256 g0 = gasleft();
        w = nttFwV3(w, prof, nttFwTable());
        uint256 used = g0 - gasleft();
        console.log("V3 packed SWAR gas (LAZY < 17q output):", used);
        // four radix-4 fused passes, two layers each
        string[4] memory names = ["L1+L2 fused", "L3+L4 fused", "L5+L6 fused", "L7+L8 fused (lazy)"];
        for (uint256 i = 0; i < 4; i++) {
            console.log(string.concat("  V3 ", names[i]), prof[i] - prof[i + 1]);
        }
    }

    function testGasPackUnpack() public view {
        uint256[] memory a = rndPoly(1);
        uint256 g0 = gasleft();
        uint256[] memory w = packCoeffs(a);
        console.log("packCoeffs 256->64 gas:", g0 - gasleft());
        g0 = gasleft();
        a = unpackCoeffs(w);
        console.log("unpackCoeffs 64->256 gas:", g0 - gasleft());
    }

    // ------------------------------------------------------- pointwise MAC ---
    // kernel: c[i] += a[i]*b[i] mod q over 256 coeffs (the A*z matvec kernel:
    // 16 such passes = 4 output polys x 4 accumulated products each).

    function refMacAccum(uint256[] memory c, uint256[] memory a, uint256[] memory b) internal pure {
        for (uint256 i = 0; i < 256; i++) {
            c[i] = (c[i] + a[i] * b[i]) % q;
        }
    }

    function testCorrectnessMAC() public pure {
        // simulate one matvec output poly: 4 accumulated pointwise products
        uint256[] memory cRef = new uint256[](256);
        uint256[] memory c1 = new uint256[](256);
        uint256[] memory c2 = new uint256[](256);
        uint256[] memory c3 = packCoeffs(new uint256[](256));
        uint256[] memory c4 = packCoeffs(new uint256[](256));
        for (uint256 t = 0; t < 4; t++) {
            uint256[] memory a = rndPoly(2 * t + 11);
            uint256[] memory b = rndPoly(2 * t + 12);
            refMacAccum(cRef, a, b);
            macOne(c1, a, b);
            macOneLazy(c2, a, b);
            uint256[] memory ap = packCoeffs(a);
            uint256[] memory bp = packCoeffs(b);
            macPackedExact(c3, ap, bp);
            macPackedLazy(c4, ap, bp);
        }
        reduceOne(c2);
        reducePacked(c4);
        assertEqPoly(c1, cRef, "macOne");
        assertEqPoly(c2, cRef, "macOneLazy+reduce");
        assertEqPoly(unpackCoeffs(c3), cRef, "macPackedExact");
        assertEqPoly(unpackCoeffs(c4), cRef, "macPackedLazy+reduce");
    }

    function testGasMAC() public view {
        uint256[] memory a = rndPoly(21);
        uint256[] memory b = rndPoly(22);
        uint256[] memory c = new uint256[](256);
        uint256[] memory ap = packCoeffs(a);
        uint256[] memory bp = packCoeffs(b);
        uint256[] memory cp = packCoeffs(new uint256[](256));
        uint256 g0;

        g0 = gasleft();
        macOne(c, a, b);
        console.log("MAC one-per-word exact (256 coeffs):", g0 - gasleft());

        g0 = gasleft();
        macOneLazy(c, a, b);
        console.log("MAC one-per-word lazy:", g0 - gasleft());
        g0 = gasleft();
        reduceOne(c);
        console.log("  reduceOne pass (amortize /4 for matvec):", g0 - gasleft());

        g0 = gasleft();
        macPackedExact(cp, ap, bp);
        console.log("MAC packed-4 exact:", g0 - gasleft());

        g0 = gasleft();
        macPackedLazy(cp, ap, bp);
        console.log("MAC packed-4 lazy:", g0 - gasleft());
        g0 = gasleft();
        reducePacked(cp);
        console.log("  reducePacked pass (amortize /4 for matvec):", g0 - gasleft());
    }
}
