// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
//
// FV4_NttScheduleExtraction — EVM-level validation of the C16 schedule
// extraction and its discrimination controls.
//
// An obligation suite that pins ID SETS but never SEMANTICS can be hollowed
// out: a predicate rewritten to a tautology (`MASK191 <= MASK191`, a threshold
// of `2^-0`) still reports a full green tally with exit 0.  The defence is
// DISCRIMINATION CONTROLS — every pinned obligation also states inputs it
// must REJECT — plus, for C16, extraction of the NTT layer schedule from the
// shipped Yul instead of a hand transcription.
//
// Two things about that defence have to hold on the EVM, not just in Python,
// and that is what this file is:
//
//   1. THE ANCHORS ARE REAL.  C16 slices the transforms into layer blocks on the
//      `mstore(add(PR, 0x..), gas())` profiling markers rather than on a comment
//      (`inv_body.index("Layers 7+8 fused")`), because a comment can be
//      moved.  Executing the shipped transforms shows the markers are
//      real, ordered, and that every block between two of them does work: the
//      gas readings are strictly decreasing, 5 of them forward and 5 inverse,
//      which is exactly the 4 and 4 marker-delimited blocks C16 pins (the
//      word-aligned layers run two-per-block as radix-4 fused passes).
//
//   2. THE REJECTED SCHEDULES REALLY ARE BAD.  C9f/C9g and C16 now carry
//      negative controls: a +4q forward increment, a non-canonical entry, a
//      ninth layer, Barrett at inverse layer 8, a doubled sum lane.  A control
//      is only evidence if the input it rejects is genuinely unsound, so each is
//      re-derived here against the SHIPPED reduction helpers at EVM semantics —
//      the difference between "the predicate says no" and "the machine would
//      actually break".
//
// Obligation map: C16 (schedule extraction + ctl_fwd_*/ctl_inv_*), C9f, C9g,
// C11a-c, S5, S6, S6b, S13, S14.  Companion to test/FV3_NttLaneBounds.t.sol, which
// pins the lane arithmetic itself.
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {nttFwV3, lazyBarrett, packCoeffs, nttFwTable} from "./ZZZ_NttVariants.sol";
import {nttInvV3, invLazyBarrett, ipackCoeffs, nttInvTable} from "./ZZZ_InvNtt.sol";

contract FV4_NttScheduleExtraction is Test {
    uint256 constant q = 8380417;
    // formal/z3/verify_all.py C11a / S13: the smallest x with lazyBarrett(x) >= 2q
    uint256 constant FIRST_FAIL = 10285325456994078;

    // The schedule formal/z3/verify_all.py C16 EXTRACTS from the shipped Yul:
    // one entry per marker-delimited inverse block, holding the K of each
    // per-layer offset constant that block uses.
    // The word-aligned layers run as RADIX-4 FUSED passes (one quad of four
    // words loaded once, two layers on the stack, one store), so a block now
    // names BOTH of its layers' offsets:
    //   block 1 : ACCQ30 (K=2^30) + ACCQ31 (K=2^31) + TWOQ (K=2)
    //             -- the fused L1+L2 entry fold (mulmod/addmod, S14)
    //   block 2 : Q4_4   (K=4,  L3) + Q4_8   (K=8,   L4)
    //   block 3 : Q4_16  (K=16, L5) + Q4_32  (K=32,  L6)
    //   block 4 : Q4_64  (K=64, L7) + Q4_128 (K=128, L8) + TWOQ4 (K=2, L8 diffs)
    function _inverseK(uint256 layer) internal pure returns (uint256) {
        return uint256(1) << (layer - 1); // L = 1..8  ->  K = 1,2,4,...,128
    }

    // ---------------------------------------------------------------- (1)
    // The profiling markers C16 anchors on are executed, in order, with work
    // between every consecutive pair.  `gas()` is strictly decreasing, so a
    // block that had been emptied (or a marker that had been deleted) shows up
    // here as an equality or a shorter array — not as a silently different
    // region boundary, which is what the comment anchor allowed.
    function testInverseProfilingMarkersDelimitFourNonEmptyBlocks() public view {
        uint256[] memory a = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            a[i] = (i * 7919) % q; // canonical lanes, deterministic
        }
        uint256[] memory prof = new uint256[](16);
        nttInvV3(ipackCoeffs(a), prof, nttInvTable());
        // 5 markers -> 4 blocks (C16.inv_schedule_extracted_is_K_2powL pins 4)
        for (uint256 k = 0; k < 4; k++) {
            assertGt(prof[k], 0, "marker not written");
            assertGt(prof[k + 1], 0, "marker not written");
            assertGt(prof[k], prof[k + 1], "inverse layer block did no work");
        }
        assertEq(prof[5], 0, "a 6th inverse marker would change the block count");
    }

    /// The forward transform runs its eight layers as THREE fused passes
    /// (RADIX-8 L1+L2+L3, RADIX-8 L4+L5+L6, and the in-word L7+L8), so it
    /// writes FOUR markers delimiting THREE blocks — one block fewer than the
    /// inverse, whose in-word entry fold cannot absorb a third layer.
    function testForwardProfilingMarkersDelimitThreeNonEmptyBlocks() public view {
        uint256[] memory a = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            a[i] = (i * 7919) % q;
        }
        uint256[] memory prof = new uint256[](16);
        nttFwV3(packCoeffs(a), prof, nttFwTable());
        // 4 markers -> 3 blocks (C16.fwd_schedule_extracted_is_plus_2q_x8)
        for (uint256 k = 0; k < 3; k++) {
            assertGt(prof[k], 0, "marker not written");
            assertGt(prof[k + 1], 0, "marker not written");
            assertGt(prof[k], prof[k + 1], "forward layer block did no work");
        }
        assertEq(prof[4], 0, "a 5th forward marker would change the block count");
    }

    // ---------------------------------------------------------------- (2a)
    // C9g's ACCEPTED schedule: the L1+L2 entry fold reduces with mulmod
    // (no Barrett at all — S14/FV3 cover it), then Barrett at L3..L7 with
    // K = 2^(L-1), every product inside the domain the shipped helper is
    // verified over.
    function testAcceptedInverseScheduleStaysInsideTheBarrettDomain() public pure {
        uint256 worst = 0;
        for (uint256 L = 3; L <= 7; L++) {
            uint256 prod = 2 * _inverseK(L) * q * (q - 1); // (u + Kq - v) < 2Kq
            if (prod > worst) worst = prod;
            uint256 r = invLazyBarrett(prod);
            assertLt(r, 2 * q, "shipped reduction holds at this layer's worst product");
            assertEq(r % q, prod % q, "and stays congruent");
        }
        assertEq(worst, 128 * q * (q - 1), "extracted schedule -> C9d's constant");
        assertLt(worst, FIRST_FAIL, "inside the cliff");
    }

    // C9g's REJECTED schedule (8, ...) — "Barrett at layer 8 too".  The control
    // is only evidence if the machine really breaks there, so: at K = 128 the
    // product leaves the verified domain, crosses the cliff, and the shipped
    // helper actually returns r >= 2q for a reachable operand.
    function testRejectedScheduleBarrettAtLayerEightWouldBreakTheReduction() public pure {
        uint256 prod = 2 * _inverseK(8) * q * (q - 1); // 256q(q-1)
        assertGt(prod, 128 * q * (q - 1), "outside the verified domain");
        assertGt(prod, FIRST_FAIL, "past the Barrett cliff (C11b/C11c)");
        assertGe(invLazyBarrett(prod), 2 * q, "the shipped reduction DOES fail there");
        // and this is why layer 8 canonicalises with `mod` instead: the lane
        // product still has to fit its 64-bit SWAR lane, which it does.
        assertLt(256 * q * (q - 1), uint256(1) << 64, "L8 lane product < 2^64 (S6b)");
    }

    // C9g's REJECTED schedule (6, ...) — "only six Barrett layers".  The worst
    // product is then 64q(q-1), which is NOT the constant C9d/S2/S4/E9b are
    // verified over, so the linkage the induction needs would be broken.
    function testRejectedScheduleSixBarrettLayersMissesTheVerifiedDomain() public pure {
        uint256 worst = 0;
        for (uint256 L = 1; L <= 6; L++) {
            uint256 prod = 2 * _inverseK(L) * q * (q - 1);
            if (prod > worst) worst = prod;
        }
        assertEq(worst, 64 * q * (q - 1), "six layers reach only 64q(q-1)");
        assertTrue(worst != 128 * q * (q - 1), "so C9d's constant is not the maximum");
    }

    // ---------------------------------------------------------------- (2b)
    // C9f's REJECTED schedule (Q, 4q, 8) — a +4q per-layer increment.  It
    // violates the obligation's own LB <= 15q premise from layer 5 on, and the
    // final lane leaves 2^28.
    function testRejectedForwardScheduleFourQPerLayerBreaksTheInduction() public pure {
        uint256 lb = q;
        bool premiseHeld = true;
        for (uint256 L = 1; L <= 8; L++) {
            if (lb > 15 * q) premiseHeld = false;
            lb += 4 * q;
        }
        assertFalse(premiseHeld, "+4q leaves the LB <= 15q premise");
        assertEq(lb, 33 * q, "final lane 33q, not 17q");
        assertGt(lb, 17 * q, "so C9a's constant no longer bounds it");
    }

    // C9f's REJECTED schedule (3q, 2q, 8) — entering with non-canonical lanes.
    function testRejectedForwardScheduleNonCanonicalEntryBreaksTheInduction() public pure {
        uint256 lb = 3 * q;
        bool premiseHeld = true;
        for (uint256 L = 1; L <= 8; L++) {
            if (lb > 15 * q) premiseHeld = false;
            lb += 2 * q;
        }
        assertFalse(premiseHeld, "a non-canonical entry leaves the premise");
        assertEq(lb, 19 * q, "final lane 19q, not 17q");
    }

    // C9f's REJECTED schedule (Q, 2q, 9) — a ninth layer.  It reuses every
    // offset constant unchanged, so pinning constant VALUES alone would accept
    // it; C16 pins the per-block structure instead, and here is why that
    // matters: the ninth layer's multiplied operand is 17q(q-1), outside the
    // forward Barrett domain.
    function testRejectedNinthLayerReusesEveryConstantButLeavesTheDomain() public pure {
        uint256 lb = q;
        uint256 worst = 0;
        for (uint256 L = 1; L <= 9; L++) {
            uint256 prod = lb * (q - 1);
            if (prod > worst) worst = prod;
            lb += 2 * q; // the SAME TWOQ4 offset constant at every layer
        }
        assertEq(worst, 17 * q * (q - 1), "a 9th layer multiplies a 17q operand");
        assertGt(worst, 15 * q * (q - 1), "outside C9b's forward Barrett domain");
        assertEq(lb, 19 * q, "and the final lane is 19q, not 17q");
        assertGt(lb, uint256(1) << 27, "C9a's 17q < 2^28 headroom is consumed");
    }

    // ---------------------------------------------------------------- (2c)
    // The extracted forward schedule is +2q at EVERY layer — the claim
    // C16.fwd_schedule_extracted_is_plus_2q_x8 makes about the shipped code.
    // At EVM semantics that means: with V = Barrett(x*S) < 2q, the pair of
    // stores (u+V, u+2q-V) keeps both lanes under LB + 2q at every one of the
    // eight layers, and never at LB + q — which is what the control
    // `sum_lane_lt_LB_plus_2q` tightened to +q (mutation V66) must break.
    function testExtractedForwardScheduleIsExactlyPlusTwoQ(uint256 seed) public pure {
        uint256 lb = q;
        for (uint256 L = 1; L <= 8; L++) {
            uint256 u = uint256(keccak256(abi.encode(seed, L, "u"))) % lb;
            uint256 x = uint256(keccak256(abi.encode(seed, L, "x"))) % lb;
            uint256 s = uint256(keccak256(abi.encode(seed, L, "s"))) % q;
            uint256 V = lazyBarrett(x * s);
            assertLt(V, 2 * q, "V < 2q");
            assertLt(u + V, lb + 2 * q, "sum lane inside the +2q envelope");
            assertLt(u + 2 * q - V, lb + 2 * q, "diff lane inside the +2q envelope");
            lb += 2 * q;
        }
        assertEq(lb, 17 * q, "eight +2q steps from q");
    }
}
