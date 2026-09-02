// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// Correctness + gas benchmarks for the packed SWAR inverse NTT in
// ZZZ_InvNtt.sol, using the repo's nttFw/nttInv as oracles.
// See ZZZ_InvNtt.sol for the lane-growth / Barrett design notes.
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {nttFw, nttInv} from "./vendor/ZKNOX_NTT_dilithium.sol";
import {q, N_MINUS_1_MOD_Q} from "./vendor/ZKNOX_dilithium_utils.sol";
import {nttInvV3, invLazyBarrett, ipackCoeffs, iunpackCoeffs, nttInvTable} from "./ZZZ_InvNtt.sol";

contract InvNttTest is Test {
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

    /// Roundtrip: packed inverse applied to packed(nttFw(x)) must unpack to
    /// exactly x, for pseudorandom x with coeffs in [0,q) and for the
    /// all-(q-1) edge case.
    function testCorrectnessInvV3Roundtrip() public view {
        uint256[] memory prof = new uint256[](8);
        for (uint256 s = 0; s < 3; s++) {
            uint256[] memory x = rndPoly(s + 201);
            uint256[] memory y = nttFw(clonePoly(x));
            uint256[] memory got = iunpackCoeffs(nttInvV3(ipackCoeffs(y), prof, nttInvTable()));
            assertEqPoly(got, x, "invV3(nttFw(x)) roundtrip");
        }
        // edge: all coefficients q-1
        uint256[] memory e = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            e[i] = q - 1;
        }
        uint256[] memory ye = nttFw(clonePoly(e));
        assertEqPoly(iunpackCoeffs(nttInvV3(ipackCoeffs(ye), prof, nttInvTable())), e, "invV3 roundtrip edge q-1");
    }

    /// Direct equality vs the repo's nttInv on the same inputs, including
    /// arbitrary canonical vectors that are NOT NTT images and the all-(q-1)
    /// edge case (worst case for the doubling sum-lane bounds).
    function testCorrectnessInvV3Direct() public view {
        uint256[] memory prof = new uint256[](8);
        for (uint256 s = 0; s < 3; s++) {
            // NTT image
            uint256[] memory y = nttFw(rndPoly(s + 201));
            assertEqPoly(iunpackCoeffs(nttInvV3(ipackCoeffs(y), prof, nttInvTable())), nttInv(clonePoly(y)), "invV3 vs nttInv (image)");
            // raw pseudorandom canonical vector
            uint256[] memory r = rndPoly(s + 301);
            assertEqPoly(iunpackCoeffs(nttInvV3(ipackCoeffs(r), prof, nttInvTable())), nttInv(clonePoly(r)), "invV3 vs nttInv (raw)");
        }
        // edge: all coefficients q-1 fed directly into the inverse
        uint256[] memory e = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            e[i] = q - 1;
        }
        assertEqPoly(iunpackCoeffs(nttInvV3(ipackCoeffs(e), prof, nttInvTable())), nttInv(clonePoly(e)), "invV3 vs nttInv edge q-1");
        // pack/unpack roundtrip sanity
        uint256[] memory p = rndPoly(999);
        assertEqPoly(iunpackCoeffs(ipackCoeffs(p)), p, "pack roundtrip");
    }

    /// Canonical output check: every unpacked coefficient of the packed
    /// inverse is in [0, q).
    function testInvV3OutputCanonical() public view {
        uint256[] memory prof = new uint256[](8);
        uint256[] memory e = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            e[i] = q - 1;
        }
        uint256[] memory got = iunpackCoeffs(nttInvV3(ipackCoeffs(e), prof, nttInvTable()));
        for (uint256 i = 0; i < 256; i++) {
            assertLt(got[i], q, "canonical output");
        }
    }

    /// Barrett constant check on the WIDER inverse domain: the largest product
    /// any inverse layer feeds the two-step reduction is 128q(q-1) < 2^53
    /// (layer 7, inputs < 64q, offset 64q, twiddle <= q-1). The reduction is a
    /// coarse step with MU33 = floor(2^33/q) = 1025 (d33 = 2^33 - MU33*q = 7167)
    /// followed by the unit step floor(2^23/q) == 1. Its guaranteed r < 2q
    /// domain runs up to 10285325456994077 -- the first failure is exactly
    /// 10285325456994078 -- so 128q(q-1) = 8.9896e15 has a 1.1441x margin.
    function testInvBarrettDomain() public pure {
        uint256 xmax = 128 * q * (q - 1); // 8989616731324416 < 2^53
        for (uint256 i = 0; i < 500; i++) {
            uint256 x = uint256(keccak256(abi.encodePacked("invbarrett", i))) % (xmax + 1);
            uint256 r = invLazyBarrett(x);
            assertLt(r, 2 * q, "barrett range");
            assertEq(r % q, x % q, "barrett congruence");
        }
        // edges
        assertEq(invLazyBarrett(0), 0);
        assertEq(invLazyBarrett(q) % q, 0);
        assertLt(invLazyBarrett(q), 2 * q);
        assertEq(invLazyBarrett(xmax) % q, xmax % q);
        assertLt(invLazyBarrett(xmax), 2 * q);
        assertEq(invLazyBarrett(1 << 53) % q, (1 << 53) % q);
        assertLt(invLazyBarrett(1 << 53), 2 * q);
        // LANE-LOCALITY: the coarse multiply never leaves its own 64-bit lane,
        // which is what lets the packed form drop the spread/repack pair...
        assertLt(xmax * 1025, 1 << 64, "x*MU33 < 2^64");
        // ... and equivalently the step-1 quotient stays inside the 31-bit
        // QHATM31 window (the two statements are the same fact)
        assertLt((xmax * 1025) >> 33, 1 << 31, "qhat < 2^31");
        // step 2 reuses that same mask: its quotient is <= 895
        assertLe((xmax * 1025) >> 33, 1072692352, "qhat max over the domain");
        uint256 x1 = xmax - (((xmax * 1025) >> 33) * q);
        assertLe(x1, 7508854654, "step 1 output < 2^33");
        assertLe(x1 >> 23, 895, "step 2 quotient fits the 31-bit mask");
        // TIGHTNESS: the documented margin is real but thin
        assertEq(invLazyBarrett(10285325456994078), 2 * q, "first failure");
        assertLt(invLazyBarrett(10285325456994077), 2 * q, "one below still holds");
        assertEq((10285325456994078 * 10000) / xmax, 11441, "margin is 1.1441x");
    }

    /// The folded constants: NINV is the oracle's n^{-1}, and the fused L8
    /// twiddle S8P = 0xb662 equals psirev_inv[1] * n^{-1} mod q (idx1 of the
    /// nttInv table is 0x3681ff).
    function testFoldedConstants() public pure {
        assertEq(mulmod(256, N_MINUS_1_MOD_Q, q), 1, "n * n^-1 = 1");
        assertEq(uint256(8347681), N_MINUS_1_MOD_Q, "NINV literal");
        assertEq(mulmod(0x3681ff, N_MINUS_1_MOD_Q, q), 0xb662, "S8P = idx1 * n^-1");
    }

    // -------------------------------------------------------------------- gas
    // Measured at fresh memory with gasleft() brackets (same condition as the
    // forward V3 numbers in ZZZ_nttvariants.t.sol).

    function testGasInvV1Baseline() public view {
        uint256[] memory a = nttFw(rndPoly(1));
        uint256 g0 = gasleft();
        a = nttInv(a);
        uint256 used = g0 - gasleft();
        console.log("V1 nttInv (repo oracle) fresh-mem gas:", used);
    }

    function testGasInvV3() public view {
        uint256[] memory a = nttFw(rndPoly(1));
        uint256[] memory w = ipackCoeffs(a);
        uint256[] memory prof = new uint256[](8);
        uint256 g0 = gasleft();
        w = nttInvV3(w, prof, nttInvTable());
        uint256 used = g0 - gasleft();
        console.log("V3 packed SWAR inverse gas (canonical output):", used);
        string[6] memory names = ["L1+L2 fused t=1,2", "L3 t=4", "L4 t=8", "L5 t=16", "L6 t=32", "L7+L8+scale fused"];
        for (uint256 i = 0; i < 6; i++) {
            console.log(string.concat("  invV3 ", names[i]), prof[i] - prof[i + 1]);
        }
        console.log("x4 transforms (verifier budget):", 4 * used);
    }

    function testGasInvPackUnpack() public view {
        uint256[] memory a = rndPoly(1);
        uint256 g0 = gasleft();
        uint256[] memory w = ipackCoeffs(a);
        console.log("ipackCoeffs 256->64 gas:", g0 - gasleft());
        g0 = gasleft();
        a = iunpackCoeffs(w);
        console.log("iunpackCoeffs 64->256 gas:", g0 - gasleft());
    }
}
