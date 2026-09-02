// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// FILE: test/SEC3_HintPaddingGrid.t.sol
//
// FIPS 204 Algorithm 21, lines 16-18 — "every UNUSED index byte is zero" — over
// the COMPLETE reachable grid, on chain, against the SHIPPED decoder.
//
// WHY THIS FILE EXISTS.  The shipped `unpackHFast` discharges the padding check
// BRANCHLESSLY, over three words of 32 / 32 / 16 index bytes:
//
//     let s1 := mul(gt(c3, 32), sub(c3, 32))
//     let s2 := mul(gt(c3, 64), sub(c3, 64))
//     let pad := or(or(shl(shl(3, c3), w0), shl(shl(3, s1), w1)), shl(shl(3, s2), w2))
//
// so its correctness is a claim about SHIFT ARITHMETIC at the two word
// boundaries c3 = 32 and c3 = 64, and nothing else.  Without this file, no
// test, no mutant and no obligation in the tree reaches the c3 >= 64 branch at
// all — and a ONE-TOKEN change there, `sub(c3, 64)` to `sub(c3, 63)`, yields a
// SECOND distinct, valid 2,420-byte signature for one (pk, message) pair: a
// strong-unforgeability break, because the first padding byte of every encoding
// with hint weight in [64, 79] stops being checked.  Under that change the
// whole test corpus, every obligation, every conjunct and every hypothesis row
// stays GREEN.  Hint weights >= 64 are common: an unguided search reaches
// weight 69 on its second signature.
//
// THE GRID.  For every reachable total weight c3 in [0, omega] the canonical
// encoding (indices 0..c3-1 in row 0, all four cut counters at c3, the rest
// zero) must be ACCEPTED with weight c3, and for every padding position
// p in [c3, 80) the same encoding with byte p set to 0xFF must be REJECTED.
// That is 81 acceptances and 3,240 rejections, and it takes ~30 ms.
//
// The counts are ASSERTED, not printed: a grid that silently stopped early
// would otherwise report a smaller green number, which is the failure mode this
// whole tree is built to refuse.  Obligation E15 in formal/z3/verify_all.py runs
// the same grid against a model of the same Yul whose six numbers are EXTRACTED
// from src/Decode.sol, so the artefact and the model are checked apart.
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {unpackHFast} from "../src/Decode.sol";

contract SEC3HintPaddingGridTest is Test {
    uint256 constant OMEGA = 80;
    uint256 constant K_ROWS = 4;

    /// The canonical 84-byte hint encoding of total weight `c3`: indices
    /// 0..c3-1 in polynomial 0 (strictly increasing, as Alg. 21 line 12
    /// requires), zero padding, and all four cut counters at `c3`.
    function _canonical(uint256 c3) internal pure returns (bytes memory h) {
        h = new bytes(OMEGA + K_ROWS);
        for (uint256 j = 0; j < c3; ++j) {
            h[j] = bytes1(uint8(j));
        }
        for (uint256 i = 0; i < K_ROWS; ++i) {
            h[OMEGA + i] = bytes1(uint8(c3));
        }
    }

    function test_padding_gate_over_the_complete_weight_x_position_grid() public pure {
        uint256 rejected;
        uint256 accepted;
        for (uint256 c3 = 0; c3 <= OMEGA; ++c3) {
            bytes memory clean = _canonical(c3);
            (bool okC,, uint256 wC) = unpackHFast(clean);
            assertTrue(okC, "FALSE REJECT: canonical zero-padded encoding");
            assertEq(wC, c3, "accepted weight must be the last cut counter");
            accepted++;
            for (uint256 p = c3; p < OMEGA; ++p) {
                bytes memory dirty = bytes.concat(clean);
                dirty[p] = bytes1(uint8(0xFF));
                (bool okD,, uint256 wD) = unpackHFast(dirty);
                assertFalse(okD, "PADDING CHECK HOLE: a nonzero padding byte was accepted");
                assertEq(wD, 0, "a rejected encoding must report weight 0");
                rejected++;
            }
        }
        // The grid is COMPLETE, and that is asserted rather than reported.
        assertEq(accepted, OMEGA + 1, "one canonical acceptance per reachable weight");
        assertEq(rejected, (OMEGA * (OMEGA + 1)) / 2, "3,240 dirty-padding rejections");
    }

    /// The two word boundaries on their own, spelled out, so a failure names the
    /// branch rather than a position in a 3,321-point sweep.  `c3 = 64` is the
    /// exact weight at which `s2` switches on, and `c3 = 32` the same for `s1`.
    function test_padding_gate_at_both_word_boundaries() public pure {
        uint256[6] memory weights = [uint256(31), 32, 33, 63, 64, 65];
        for (uint256 i = 0; i < weights.length; ++i) {
            uint256 c3 = weights[i];
            bytes memory clean = _canonical(c3);
            (bool okC,, uint256 wC) = unpackHFast(clean);
            assertTrue(okC, "canonical encoding rejected at a word boundary");
            assertEq(wC, c3, "weight at a word boundary");
            // the FIRST padding byte — the one the demonstrated mutation freed
            bytes memory dirty = bytes.concat(clean);
            dirty[c3] = bytes1(uint8(0x01));
            (bool okD,,) = unpackHFast(dirty);
            assertFalse(okD, "first padding byte unchecked at a word boundary");
            // ... and the LAST index byte, which only the third word covers
            bytes memory tail = bytes.concat(clean);
            tail[OMEGA - 1] = bytes1(uint8(0x01));
            (bool okT,,) = unpackHFast(tail);
            assertFalse(okT, "index byte 79 is not covered by the padding check");
        }
    }
}
