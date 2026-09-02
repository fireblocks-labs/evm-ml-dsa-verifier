// SPDX-License-Identifier: MIT
// FILE: test/Kernels.t.sol
//
// Differential correctness + gas for the shipped kernels in src/Decode.sol.
// Every shipped kernel is compared BIT-FOR-BIT against the reference kernel
// composition it replaces (unpackZStrict + packFromFlat, iunpackCoeffs +
// useHintFast2, sampleInBallE2E + packCoeffs, macCompactLazy/macSubCT1Lazy)
// on randomised and boundary inputs — a kernel is only correct if the outputs
// are identical, never "close".
pragma solidity ^0.8.25;

import {Test, console} from "forge-std/Test.sol";
import {_F1600_AT, _F1600_CODE} from "./ZZZ_FastKeccak.sol";
import {deployF1600_170} from "./ZZZ_FastKeccak170.sol";
import {useHintFast2} from "./ZZZ_decode2.t.sol";
import {packCoeffs} from "./ZZZ_NttVariants.sol";
import {iunpackCoeffs} from "./ZZZ_InvNtt.sol";
import {unpackZStrict, sampleInBallE2E, packFromFlat, E2E_Q} from "./ZZZ_E2ERef.sol";
import {unpackZPacked, useHintSwar, sampleInBallPacked, macCompactPre, macSubCT1Pre, matvecRow} from "../src/Decode.sol";
import {macCompactLazy, macSubCT1Lazy} from "./ZZZ_E2ERef.sol";
import {nttFwV3, reducePacked, nttFwTable} from "./ZZZ_NttVariants.sol";

contract KernelsTest is Test {
    address f1600;

    function setUp() public {
        vm.etch(_F1600_AT, _F1600_CODE);
        f1600 = deployF1600_170();
    }

    // ---------------------------------------------------------------- helpers

    /// encode 1024 coefficients as FIPS 204 z (18-bit little-endian fields,
    /// 4 coefficients per 9 bytes); `v` values are the RAW field values
    /// (v = gamma1 - z), i.e. exactly what the decoders slice out.
    function _encodeZ(uint256[] memory v) internal pure returns (bytes memory out) {
        out = new bytes(2304);
        for (uint256 i = 0; i < 1024; ++i) {
            uint256 base = (i / 4) * 9;
            uint256 sh = (i % 4) * 18;
            uint256 x = v[i];
            for (uint256 b = 0; b < 18; ++b) {
                if ((x >> b) & 1 == 1) {
                    uint256 bit = sh + b;
                    out[base + bit / 8] = bytes1(uint8(out[base + bit / 8]) | uint8(1 << (bit % 8)));
                }
            }
        }
    }

    function _randValid(uint256 seed) internal pure returns (uint256[] memory v) {
        v = new uint256[](1024);
        // 79 .. 262065 inclusive is the strict-FIPS acceptance window
        for (uint256 i = 0; i < 1024; ++i) {
            v[i] = 79 + (uint256(keccak256(abi.encodePacked(seed, i))) % 261987);
        }
        // pin the exact boundaries into the corpus
        v[0] = 79;
        v[1] = 262065;
        v[2] = 131072; // z == 0 -> must canonicalise to 0, not q
        v[3] = 131071;
        v[4] = 131073;
    }

    function _canonPoly(uint256 seed) internal pure returns (uint256[] memory a) {
        a = new uint256[](256);
        for (uint256 i = 0; i < 256; ++i) {
            a[i] = uint256(keccak256(abi.encodePacked(seed, i))) % E2E_Q;
        }
    }

    // ============================================================== unpackZ
    function test_kernel_10_unpackZPacked_matches_reference() public view {
        for (uint256 s = 0; s < 6; ++s) {
            bytes memory z = _encodeZ(_randValid(s));
            (uint256[] memory flat, bool ok1) = unpackZStrict(z);
            (uint256[][] memory zp, bool ok2) = unpackZPacked(z);
            assertTrue(ok1, "reference rejected a valid corpus");
            assertEq(ok2, ok1, "norm verdict diverged");
            for (uint256 p = 0; p < 4; ++p) {
                uint256[] memory want = packFromFlat(flat, p << 8);
                for (uint256 w = 0; w < 64; ++w) {
                    assertEq(zp[p][w], want[w], "packed word mismatch");
                }
            }
        }
    }

    function test_kernel_11_unpackZPacked_rejects_out_of_range() public view {
        uint256[] memory v = _randValid(99);
        // just below / just above the strict window: both must be REJECTED
        uint256[2] memory bad = [uint256(78), 262066];
        for (uint256 k = 0; k < 2; ++k) {
            for (uint256 pos = 0; pos < 4; ++pos) {
                uint256[] memory vv = new uint256[](1024);
                for (uint256 i = 0; i < 1024; ++i) {
                    vv[i] = v[i];
                }
                vv[pos * 257] = bad[k];
                bytes memory z = _encodeZ(vv);
                (, bool ok1) = unpackZStrict(z);
                (, bool ok2) = unpackZPacked(z);
                assertFalse(ok1, "reference accepted an out-of-range coefficient");
                assertFalse(ok2, "shipped decoder accepted an out-of-range coefficient");
            }
        }
    }

    function test_kernel_12_unpackZ_gas() public view {
        bytes memory z = _encodeZ(_randValid(1));
        uint256 g0 = gasleft();
        (uint256[] memory flat,) = unpackZStrict(z);
        uint256 gRef = g0 - gasleft();
        g0 = gasleft();
        uint256[] memory p0 = packFromFlat(flat, 0);
        uint256[] memory p1 = packFromFlat(flat, 256);
        uint256[] memory p2 = packFromFlat(flat, 512);
        uint256[] memory p3 = packFromFlat(flat, 768);
        uint256 gPack = g0 - gasleft();
        g0 = gasleft();
        (uint256[][] memory zp,) = unpackZPacked(z);
        uint256 gNew = g0 - gasleft();
        console.log("unpackZStrict:", gRef);
        console.log("4x packFromFlat:", gPack);
        console.log("reference total:", gRef + gPack);
        console.log("unpackZPacked (shipped):", gNew);
        console.log("saving:", gRef + gPack - gNew);
        require(p0[0] + p1[0] + p2[0] + p3[0] + zp[0][0] != type(uint256).max);
    }

    // ============================================================== useHint
    function test_kernel_20_useHintSwar_matches_reference() public view {
        for (uint256 s = 0; s < 4; ++s) {
            uint256[][] memory flat = new uint256[][](4);
            uint256[][] memory packed = new uint256[][](4);
            for (uint256 i = 0; i < 4; ++i) {
                flat[i] = _canonPoly(1000 * s + i);
                packed[i] = packCoeffs(flat[i]);
            }
            uint256[4] memory hm;
            for (uint256 i = 0; i < 4; ++i) {
                hm[i] = uint256(keccak256(abi.encodePacked("hm", s, i)));
            }
            bytes memory want = useHintFast2(hm, flat);
            bytes memory got = useHintSwar(hm, packed);
            assertEq(got.length, 768);
            assertEq(keccak256(got), keccak256(want), "w1Encode output diverged");
        }
    }

    function test_kernel_21_useHintSwar_boundaries() public view {
        // every structurally interesting r value, in every lane position
        uint256[10] memory corner =
            [uint256(0), 1, 95232, 95233, 190463, 190464, 8285184, 8285185, 8380415, 8380416];
        uint256[][] memory flat = new uint256[][](4);
        uint256[][] memory packed = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            uint256[] memory a = new uint256[](256);
            for (uint256 j = 0; j < 256; ++j) {
                a[j] = corner[(j + i) % 10];
            }
            flat[i] = a;
            packed[i] = packCoeffs(a);
        }
        for (uint256 pat = 0; pat < 8; ++pat) {
            uint256[4] memory hm;
            for (uint256 i = 0; i < 4; ++i) {
                hm[i] = pat == 0
                    ? 0
                    : (pat == 1 ? type(uint256).max : uint256(keccak256(abi.encodePacked("bp", pat, i))));
            }
            bytes memory want = useHintFast2(hm, flat);
            bytes memory got = useHintSwar(hm, packed);
            assertEq(keccak256(got), keccak256(want), "boundary w1Encode diverged");
        }
    }

    function test_kernel_22_useHint_gas() public view {
        uint256[] memory prof = new uint256[](10);
        prof;
        uint256[][] memory packed = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            packed[i] = packCoeffs(_canonPoly(77 + i));
        }
        uint256[4] memory hm;
        for (uint256 i = 0; i < 4; ++i) {
            hm[i] = uint256(keccak256(abi.encodePacked("g", i)));
        }
        uint256 g0 = gasleft();
        uint256[][] memory flat = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            flat[i] = iunpackCoeffs(packed[i]);
        }
        uint256 gUnpack = g0 - gasleft();
        g0 = gasleft();
        bytes memory want = useHintFast2(hm, flat);
        uint256 gRef = g0 - gasleft();
        g0 = gasleft();
        bytes memory got = useHintSwar(hm, packed);
        uint256 gNew = g0 - gasleft();
        console.log("4x iunpackCoeffs:", gUnpack);
        console.log("useHintFast2:", gRef);
        console.log("reference total:", gUnpack + gRef);
        console.log("useHintSwar (shipped):", gNew);
        console.log("saving:", gUnpack + gRef - gNew);
        assertEq(keccak256(got), keccak256(want));
    }

    // ========================================================= sampleInBall
    function test_kernel_30_sampleInBallPacked_matches_reference() public view {
        for (uint256 s = 0; s < 8; ++s) {
            bytes32 ct = keccak256(abi.encodePacked("sib", s));
            uint256[] memory ref = packCoeffs(sampleInBallE2E(ct));
            uint256[] memory got = sampleInBallPacked(ct, f1600);
            for (uint256 w = 0; w < 64; ++w) {
                assertEq(got[w], ref[w], "sampleInBall packed word mismatch");
            }
        }
    }

    function test_kernel_31_sampleInBall_gas() public view {
        bytes32 ct = keccak256("gas");
        uint256 g0 = gasleft();
        uint256[] memory flat = sampleInBallE2E(ct);
        uint256 gSib = g0 - gasleft();
        g0 = gasleft();
        uint256[] memory pk = packCoeffs(flat);
        uint256 gPack = g0 - gasleft();
        g0 = gasleft();
        uint256[] memory got = sampleInBallPacked(ct, f1600);
        uint256 gNew = g0 - gasleft();
        console.log("sampleInBallE2E:", gSib);
        console.log("packCoeffs:", gPack);
        console.log("reference total:", gSib + gPack);
        console.log("sampleInBallPacked (shipped):", gNew);
        require(pk[0] == got[0]);
    }

    // ============================================================== matvec
    function _fakeRow(uint256 seed) internal pure returns (uint256 ptr) {
        uint256[] memory row = new uint256[](32);
        for (uint256 i = 0; i < 32; ++i) {
            uint256 wrd;
            for (uint256 s = 0; s < 8; ++s) {
                wrd |= (uint256(keccak256(abi.encodePacked(seed, i, s))) % E2E_Q) << (32 * s);
            }
            row[i] = wrd;
        }
        assembly ("memory-safe") {
            ptr := add(row, 32)
        }
    }

    /// per-lane offset delta between the shipped KQ28 (= q*2^28) MACs and the
    /// reference KQ24 (= q*2^24) MACs, replicated across the four lanes; both
    /// offsets are multiples of q, so the delta vanishes under reduction
    uint256 constant KQ_DELTA_REP = ((E2E_Q << 28) - (E2E_Q << 24)) * 0x0000000000000001000000000000000100000000000000010000000000000001;

    function test_kernel_40_matvec_pre_matches_reference() public view {
        uint256[] memory prof = new uint256[](10);
        uint256[] memory zHat = nttFwV3(packCoeffs(_canonPoly(41)), prof, nttFwTable());
        uint256[] memory cHat = nttFwV3(packCoeffs(_canonPoly(42)), prof, nttFwTable());
        uint256 a0 = _fakeRow(1);
        uint256 a1 = _fakeRow(2);
        uint256 t1 = _fakeRow(3);

        // the reference lazy kernels (KQ24 offset) require canonical lanes;
        // the shipped kernels accept the forward NTT's LAZY (< 17q) lanes —
        // canonicalise a copy for the reference side
        uint256[] memory zC = _clonePacked(zHat);
        uint256[] memory cC = _clonePacked(cHat);
        reducePacked(zC);
        reducePacked(cC);

        uint256[] memory accRef = new uint256[](64);
        macCompactLazy(accRef, a0, zC);
        macCompactLazy(accRef, a1, zC);
        macSubCT1Lazy(accRef, cC, t1);

        // (a) shipped kernels on the SAME canonical lanes: bit-identical up to
        // the exact per-lane KQ28-KQ24 offset delta
        uint256[] memory accNew = new uint256[](64);
        macCompactPre(accNew, a0, zC);
        macCompactPre(accNew, a1, zC);
        macSubCT1Pre(accNew, cC, t1);
        for (uint256 i = 0; i < 64; ++i) {
            assertEq(accNew[i], accRef[i] + KQ_DELTA_REP, "lazy accumulator diverged");
        }

        // (b) shipped kernels on the LAZY lanes: congruent after reduction
        uint256[] memory accLazy = new uint256[](64);
        macCompactPre(accLazy, a0, zHat);
        macCompactPre(accLazy, a1, zHat);
        macSubCT1Pre(accLazy, cHat, t1);

        reducePacked(accRef);
        reducePacked(accNew);
        reducePacked(accLazy);
        for (uint256 i = 0; i < 64; ++i) {
            assertEq(accNew[i], accRef[i], "reduced accumulator diverged");
            assertEq(accLazy[i], accRef[i], "lazy-lane accumulator diverged mod q");
        }
    }

    function _clonePacked(uint256[] memory a) internal pure returns (uint256[] memory b) {
        b = new uint256[](a.length);
        for (uint256 i = 0; i < a.length; ++i) {
            b[i] = a[i];
        }
    }

    function test_kernel_41_matvec_worstcase() public view {
        // all-(q-1) inputs: the maximum-magnitude lane case
        uint256[] memory maxp = new uint256[](256);
        for (uint256 i = 0; i < 256; ++i) {
            maxp[i] = E2E_Q - 1;
        }
        uint256[] memory z = packCoeffs(maxp);
        uint256[] memory row = new uint256[](32);
        for (uint256 i = 0; i < 32; ++i) {
            uint256 wrd;
            for (uint256 s = 0; s < 8; ++s) {
                wrd |= (E2E_Q - 1) << (32 * s);
            }
            row[i] = wrd;
        }
        uint256 ptr;
        assembly ("memory-safe") {
            ptr := add(row, 32)
        }
        uint256[] memory accRef = new uint256[](64);
        uint256[] memory accNew = new uint256[](64);
        for (uint256 k = 0; k < 4; ++k) {
            macCompactLazy(accRef, ptr, z);
            macCompactPre(accNew, ptr, z);
        }
        macSubCT1Lazy(accRef, z, ptr);
        macSubCT1Pre(accNew, z, ptr);
        for (uint256 i = 0; i < 64; ++i) {
            assertEq(accNew[i], accRef[i] + KQ_DELTA_REP, "worst-case accumulator diverged");
        }
    }

    function test_kernel_42_matvec_gas() public view {
        uint256[] memory prof = new uint256[](10);
        uint256[] memory zHat = nttFwV3(packCoeffs(_canonPoly(43)), prof, nttFwTable());
        uint256 a0 = _fakeRow(9);
        uint256[] memory acc = new uint256[](64);
        uint256 g0 = gasleft();
        macCompactLazy(acc, a0, zHat);
        uint256 gRef = g0 - gasleft();
        g0 = gasleft();
        macCompactPre(acc, a0, zHat);
        uint256 gNew = g0 - gasleft();
        console.log("macCompactLazy:", gRef);
        console.log("macCompactPre :", gNew);
        g0 = gasleft();
        macSubCT1Lazy(acc, zHat, a0);
        uint256 gRef2 = g0 - gasleft();
        g0 = gasleft();
        macSubCT1Pre(acc, zHat, a0);
        uint256 gNew2 = g0 - gasleft();
        console.log("macSubCT1Lazy :", gRef2);
        console.log("macSubCT1Pre  :", gNew2);
        console.log("matvec saving per verify (16x + 4x):", 16 * (gRef - gNew) + 4 * (gRef2 - gNew2));
    }

    // ======================================================= fused matvec row
    function test_kernel_50_matvecRow_matches_reference() public view {
        uint256[] memory prof = new uint256[](10);
        uint256[][] memory z = new uint256[][](4);
        for (uint256 j = 0; j < 4; ++j) {
            z[j] = nttFwV3(packCoeffs(_canonPoly(50 + j)), prof, nttFwTable());
        }
        uint256[] memory cHat = nttFwV3(packCoeffs(_canonPoly(60)), prof, nttFwTable());
        // one contiguous 4x32-word A row block + a t1 block
        uint256[] memory blockA = new uint256[](128);
        for (uint256 i = 0; i < 128; ++i) {
            uint256 wrd;
            for (uint256 s = 0; s < 8; ++s) {
                wrd |= (uint256(keccak256(abi.encodePacked("A", i, s))) % E2E_Q) << (32 * s);
            }
            blockA[i] = wrd;
        }
        uint256 t1 = _fakeRow(1234);
        uint256 aRow;
        assembly ("memory-safe") {
            aRow := add(blockA, 32)
        }

        uint256[] memory ref = new uint256[](64);
        macCompactPre(ref, aRow, z[0]);
        macCompactPre(ref, aRow + 1024, z[1]);
        macCompactPre(ref, aRow + 2048, z[2]);
        macCompactPre(ref, aRow + 3072, z[3]);
        macSubCT1Pre(ref, cHat, t1);

        uint256[] memory got = matvecRow(aRow, z, cHat, t1);
        assertEq(got.length, 64);
        for (uint256 i = 0; i < 64; ++i) {
            assertEq(got[i], ref[i], "fused matvec row diverged");
        }
    }

    function test_kernel_51_matvecRow_worstcase() public view {
        // worst admissible input lanes: the LAZY forward NTT's 17q-1 ceiling
        uint256[] memory maxp = new uint256[](256);
        for (uint256 i = 0; i < 256; ++i) {
            maxp[i] = 17 * E2E_Q - 1;
        }
        uint256[] memory zm = packCoeffs(maxp);
        uint256[] memory blockA = new uint256[](128);
        uint256 wmax;
        for (uint256 s = 0; s < 8; ++s) {
            wmax |= (E2E_Q - 1) << (32 * s);
        }
        for (uint256 i = 0; i < 128; ++i) {
            blockA[i] = wmax;
        }
        uint256[] memory t1arr = new uint256[](32);
        for (uint256 i = 0; i < 32; ++i) {
            t1arr[i] = wmax;
        }
        uint256 aRow;
        uint256 t1;
        assembly ("memory-safe") {
            aRow := add(blockA, 32)
            t1 := add(t1arr, 32)
        }
        uint256[] memory ref = new uint256[](64);
        macCompactPre(ref, aRow, zm);
        macCompactPre(ref, aRow + 1024, zm);
        macCompactPre(ref, aRow + 2048, zm);
        macCompactPre(ref, aRow + 3072, zm);
        macSubCT1Pre(ref, zm, t1);
        uint256[][] memory zz = new uint256[][](4);
        for (uint256 i = 0; i < 4; ++i) {
            zz[i] = zm;
        }
        uint256[] memory got = matvecRow(aRow, zz, zm, t1);
        // O8's lane ceiling: 4(q-1)(17q-1) + q*2^28 = the inverse NTT's ACC_ENTRY
        uint256 accEntry = 4 * (E2E_Q - 1) * (17 * E2E_Q - 1) + (E2E_Q << 28);
        for (uint256 i = 0; i < 64; ++i) {
            assertEq(got[i], ref[i], "worst-case fused row diverged");
            for (uint256 l = 0; l < 4; ++l) {
                uint256 lane = (got[i] >> (64 * l)) & 0xffffffffffffffff;
                assertLe(lane, accEntry, "lane exceeded O8's ACC_ENTRY bound");
                assertLt(lane, uint256(1) << 53, "lane bound");
            }
        }
    }

    function test_kernel_52_matvecRow_gas() public view {
        uint256[] memory prof = new uint256[](10);
        uint256[][] memory z = new uint256[][](4);
        for (uint256 j = 0; j < 4; ++j) {
            z[j] = nttFwV3(packCoeffs(_canonPoly(70 + j)), prof, nttFwTable());
        }
        uint256[] memory cHat = nttFwV3(packCoeffs(_canonPoly(80)), prof, nttFwTable());
        uint256[] memory blockA = new uint256[](128);
        uint256 aRow;
        assembly ("memory-safe") {
            aRow := add(blockA, 32)
        }
        uint256 t1 = _fakeRow(4321);

        uint256 g0 = gasleft();
        uint256[] memory ref = new uint256[](64);
        macCompactPre(ref, aRow, z[0]);
        macCompactPre(ref, aRow + 1024, z[1]);
        macCompactPre(ref, aRow + 2048, z[2]);
        macCompactPre(ref, aRow + 3072, z[3]);
        macSubCT1Pre(ref, cHat, t1);
        uint256 gRef = g0 - gasleft();
        g0 = gasleft();
        uint256[] memory got = matvecRow(aRow, z, cHat, t1);
        uint256 gNew = g0 - gasleft();
        console.log("5-pass row (macCompactPre x4 + macSubCT1Pre):", gRef);
        console.log("2-pass fused matvecRow:", gNew);
        console.log("saving per verify (x4 rows):", 4 * (gRef - gNew));
        require(got[0] == ref[0]);
    }
}
