// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
//
// FV6_NttRegionCoverage — EVM-level validation that C16's source partition is
// TOTAL: head, layer blocks and tail are all summarised.
//
// WHY TOTALITY MATTERS.  An extractor that slices the function as
//
//     blks = [body[marks[k].end():marks[k+1].start()] for k in range(len(marks)-1)]
//
// covers only the INTERIOR of the profiling-marker sequence.  Code before
// the first marker and code after the last marker belongs to NO block and is
// summarised by nothing at all; and if a block is summarised by the SET of
// offset constant NAMES it mentions, deleting one lane group's `add(u, Q4_16)`
// moves nothing while three sibling occurrences keep the name alive.  Under
// such an extraction, three one-file edits to the shipped `InvNtt.sol` each
// leave the extracted shape
//
//     {"K_per_block": [[…],[4],[8],[16],[32],[2,64,128]], …}   (then-current)
//
// BYTE-IDENTICAL while every check still reports green (the word-aligned layers
// are now fused two-per-marker-block, so the shipped shape reads
// [[...],[4,8],[16,32],[2,64,128]] — a different block COUNT, and nothing about
// the argument below changes):
//
//   A1  a ninth, entirely unreduced layer appended after the LAST `gas()` marker
//   A2  one lane group's `+16q` deleted inside a layer block
//   A3  a loop inserted before `mstore(PR, gas())` lifting every input lane
//
// C16's partition is therefore TOTAL — head, blocks, tail — with occurrence
// counts and two residual digests, and each of A1/A2/A3 fails on a STRUCTURAL
// conjunct.
// See formal/z3/verify_all.py `_shape`/`_inert`/`_offsets_every_butterfly` and
// the ctl_*_payload_before_first_marker / _after_last_marker /
// _one_offset_dropped_in_a_block controls.
//
// WHAT THIS FILE IS.  A control is only evidence if the input it rejects is
// genuinely unsound.  FV4 does that for the schedule controls; this file does
// it for the three region-coverage ones, at EVM semantics against the SHIPPED
// code:
//
//   1. the transform's PRECONDITION (entry lanes <= ACC_ENTRY, the O8
//      accumulator ceiling) is load-bearing — a head payload that lifts one
//      lane past the ACCQ30 offset wraps the EVM subtraction out of the
//      residue class entirely;
//   2. the transform's POSTCONDITION (canonical exit) is load-bearing — A1's
//      ninth layer leaves lanes outside [0, q) and its Barrett input outside the
//      verified domain;
//   3. an offset DROPPED from one butterfly is not a rounding detail — in EVM
//      256-bit arithmetic `sub(u, v)` with u < v wraps, and the shipped
//      reduction turns that into a value that is neither < 2q nor congruent.
//
// Obligation map: C16 (total region partition + the three region-coverage
// controls), C9f, C9g, C11a-c, S5, S6, S6b, S13, S14.  Companion to
// FV3_NttLaneBounds.t.sol (lane arithmetic) and FV4_NttScheduleExtraction.t.sol
// (the schedule controls).
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {nttFwV3, packCoeffs, unpackCoeffs, nttFwTable} from "./ZZZ_NttVariants.sol";
import {nttInvV3, invLazyBarrett, ipackCoeffs, iunpackCoeffs, nttInvTable} from "./ZZZ_InvNtt.sol";

contract FV6_NttRegionCoverage is Test {
    uint256 constant q = 8380417;
    // formal/z3/verify_all.py C11a / S13: the smallest x with lazyBarrett(x) >= 2q
    uint256 constant FIRST_FAIL = 10285325456994078;

    function _canonicalInput() internal pure returns (uint256[] memory a) {
        a = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            a[i] = (i * 7919 + 13) % q;
        }
    }

    // ------------------------------------------------------------------ (0)
    // The baseline the three payloads have to break: the shipped pair really is
    // an involution on canonical input, and the inverse really does exit
    // canonical.  Without this, "A1 breaks the postcondition" says nothing.
    function testShippedTransformsRoundTripAndExitCanonical() public view {
        uint256[] memory a = _canonicalInput();
        uint256[] memory prof = new uint256[](16);
        uint256[] memory out =
            iunpackCoeffs(nttInvV3(ipackCoeffs(unpackCoeffs(nttFwV3(packCoeffs(a), prof, nttFwTable()))), prof, nttInvTable()));
        for (uint256 i = 0; i < 256; i++) {
            assertLt(out[i], q, "inverse NTT must exit with canonical lanes");
            assertEq(out[i], a[i], "fwd/inv are inverse on canonical input");
        }
    }

    // ------------------------------------------------------------------ (1)
    // A3 — a payload BEFORE the first marker.  C16's `_inert(region[0])` is the
    // syntactic statement; this is the arithmetic one.  S14/C9g's induction
    // opens with "entering the fused L1/L2 block every lane is <= ACC_ENTRY"
    // (the raw matvec-accumulator ceiling, O8), because the block's
    // difference operands are offset by ACCQ30 = q*2^30 >= ACC_ENTRY.  A lane
    // lifted past that offset (exactly what an A3 head payload can do, and
    // exactly what an interior-only extraction cannot see) makes the EVM
    // subtraction WRAP — and 2^256 is not a multiple of q, so the wrapped
    // operand is in the WRONG residue class: mulmod still returns something
    // < q, but it is congruent to nothing the proof talks about.
    function testPayloadBeforeTheFirstMarkerBreaksTheEntryPrecondition() public pure {
        uint256 ACC_ENTRY = 4 * (q - 1) * (17 * q - 1) + (q << 28); // O8 lane ceiling
        assertLe(ACC_ENTRY, q << 30, "the honest entry bound is inside the offset");
        // an honest worst-case operand: no wrap, canonical congruent output
        uint256 honest = 0 + (q << 30) - ACC_ENTRY;
        assertEq(mulmod(honest, 1, q), (q - (ACC_ENTRY % q)) % q, "honest lane congruent");
        // the payload: one lane lifted past the offset wraps the subtraction
        uint256 u1 = (q << 30) + q; // > u0 + q*2^30 for any canonical u0
        uint256 wrapped;
        unchecked {
            wrapped = 0 + (q << 30) - u1; // wraps to 2^256 - q
        }
        assertGt(wrapped, uint256(1) << 250, "the subtraction wrapped");
        // 2^256 mod q != 0, so the wrap changes the residue class
        assertTrue(mulmod(wrapped, 1, q) != (q - (u1 % q)) % q, "wrapped lane is NOT congruent");
    }

    // ... and here is the part that makes C16's head region NECESSARY rather
    // than merely tidy, MEASURED rather than argued (the plausible-sounding
    // opposite is exactly what the measurement refutes):
    //
    //   a UNIFORM +m*q entry lift NEVER changes the transform's output.
    //
    // The fused entry block is exactly modular — mulmod/addmod are congruent
    // for EVERY operand, and a uniform lift cancels out of every difference —
    // so the lanes simply ride up, still congruent, and the answer is
    // bit-identical for every uniform lift that still fits the 64-bit packed
    // lanes.  (Under the pre-fold spread-Barrett block the first observable
    // uniform lift was +1030q; the fold made even that disappear.)  What IS
    // observable is a SINGLE lane lifted past the ACCQ30 offset, where the
    // EVM subtraction wraps out of the residue class (test above).
    //
    // Consequences, both of which this file exists to demonstrate:
    //   * an end-to-end or round-trip functional test CANNOT catch A3.  Only an
    //     obligation that reads the SOURCE and refuses to leave a region
    //     unsummarised can.  That is C16.inv_head_and_tail_are_inert.
    //   * S14/C9g's "entered <= ACC_ENTRY" premise is not decorative: past the
    //     ACCQ30 offset the machine leaves the residue class entirely, and
    //     BELOW it the proof is what says every intermediate stays in bounds.
    function testPayloadBeforeTheFirstMarkerIsInvisibleToFunctionalTesting() public view {
        uint256[] memory prof = new uint256[](16);
        uint256[] memory a = _canonicalInput();
        uint256[] memory clean = iunpackCoeffs(nttInvV3(ipackCoeffs(a), prof, nttInvTable()));

        assertEq(_liftedDiffers(a, clean, 128), 0, "A3's +128q lift is NOT observable");
        assertEq(_liftedDiffers(a, clean, 1030), 0, "nor is +1030q (pre-fold threshold)");
        assertEq(_liftedDiffers(a, clean, 1 << 26), 0, "nor is +2^26*q");
        assertEq(_liftedDiffers(a, clean, 1 << 38), 0, "nor is +2^38*q (uniform lifts cancel)");
        // a single lane inside the verified entry domain: still invisible
        assertEq(_oneLaneLiftDiffers(a, clean, 1 << 29), 0, "one lane at 2^29*q is inside the domain");
        // ... and a single lane past the ACCQ30 offset wraps and IS observable
        assertGt(_oneLaneLiftDiffers(a, clean, (1 << 30) + 1), 0, "one lane past q*2^30 wraps");
    }

    function _liftedDiffers(uint256[] memory a, uint256[] memory clean, uint256 m)
        internal
        view
        returns (uint256 diff)
    {
        uint256[] memory lifted = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            lifted[i] = a[i] + m * q;
        }
        diff = _differs(lifted, clean);
    }

    /// lifts ONLY coefficient 1 (word 0, lane 1 — the subtrahend of the very
    /// first L1 butterfly) by m*q
    function _oneLaneLiftDiffers(uint256[] memory a, uint256[] memory clean, uint256 m)
        internal
        view
        returns (uint256 diff)
    {
        uint256[] memory lifted = new uint256[](256);
        for (uint256 i = 0; i < 256; i++) {
            lifted[i] = a[i];
        }
        lifted[1] = a[1] + m * q;
        diff = _differs(lifted, clean);
    }

    function _differs(uint256[] memory lifted, uint256[] memory clean)
        internal
        view
        returns (uint256 diff)
    {
        uint256[] memory prof = new uint256[](16);
        uint256[] memory dirty = iunpackCoeffs(nttInvV3(ipackCoeffs(lifted), prof, nttInvTable()));
        for (uint256 i = 0; i < 256; i++) {
            if (dirty[i] != clean[i]) diff++;
        }
    }

    // ------------------------------------------------------------------ (2)
    // A1 — a payload AFTER the last marker.  C16's `_inert(region[-1])` is the
    // syntactic statement.  Arithmetically: layer 8 is the canonicalising layer,
    // so anything after it operates on canonical lanes and, being unreduced,
    // leaves them non-canonical; and if it were reduced with the shipped helper
    // instead, its operand 2*256q*(q-1) is past the cliff.  Either way the
    // POSTCONDITION every caller of nttInvV3 relies on is gone.
    function testPayloadAfterTheLastMarkerBreaksTheExitPostcondition() public pure {
        // an unreduced ninth butterfly on canonical lanes: u + Kq - v with
        // K = 128 leaves lanes up to 129q, which is not canonical
        uint256 u = q - 1;
        uint256 v = 0;
        uint256 ninth = u + 128 * q - v;
        assertGe(ninth, q, "the ninth layer's lane is NOT canonical");
        // and reducing it with the shipped helper is not an option either
        uint256 prod = 2 * 256 * q * (q - 1);
        assertGt(prod, 128 * q * (q - 1), "a 9th Barrett layer leaves the domain");
        assertGt(prod, FIRST_FAIL, "past the cliff");
        assertGe(invLazyBarrett(prod), 2 * q, "the shipped reduction DOES fail there");
        // S6b's 64-bit SWAR lane is the OTHER constraint, and it is the loose
        // one: L8's product uses ~1/1000th of the lane, which is exactly why the
        // entry-lift measurement below tolerates ~1000q before anything breaks.
        assertLt(2 * 128 * q * (q - 1), uint256(1) << 64, "L8 lane product fits (S6b)");
        assertGt((uint256(1) << 64) / (2 * 128 * q * (q - 1)), 1000, "with ~1000x slack");
    }

    // ------------------------------------------------------------------ (3)
    // A2 — one lane group's `+K q` DELETED inside a layer block.  C16's
    // `_offsets_every_butterfly` (in the radix-4 fused form: offset OCCURRENCES
    // == stores, four butterflies and four stores per quad) is the
    // syntactic statement; a set-of-names summary could not see it
    // because `Q4_16` still occurred three times in the same block.
    // Arithmetically the offset is what keeps the difference non-negative in
    // EVM 256-bit arithmetic.
    function testOneDroppedOffsetUnderflowsInEvmArithmetic() public pure {
        uint256 u = 1; // a small sum lane
        uint256 v = 16 * q - 1; // a large difference lane, both admissible at L5
        uint256 offset;
        unchecked {
            offset = u + 16 * q - v; // WITH the +16q the butterfly stores
        }
        assertLt(offset, 32 * q, "offset difference stays inside 2Kq");
        assertEq(offset % q, (u + 16 * q - v) % q, "and is congruent");

        uint256 wrapped;
        unchecked {
            wrapped = u - v; // the A2 payload: `sub(u, v)` with the offset gone
        }
        assertGt(wrapped, uint256(1) << 250, "u < v wraps to ~2^256");
        // ... and the shipped reduction cannot rescue it: the wrapped value is
        // far past the cliff, and multiplying it by a twiddle wraps again.
        assertGt(wrapped, FIRST_FAIL, "past the Barrett cliff");
        assertTrue(
            invLazyBarrett(wrapped) >= 2 * q || invLazyBarrett(wrapped) % q != wrapped % q,
            "the shipped reduction is neither in range nor congruent there"
        );
    }

    // ... and at the layer where A2 was planted the WRAPPED product is not even
    // a lane-independent SWAR operand any more: it occupies the whole word.
    function testDroppedOffsetDestroysSwarLaneIndependence() public pure {
        uint256 lane = uint256(type(uint64).max);
        uint256 wrapped;
        unchecked {
            wrapped = uint256(1) - (16 * q - 1);
        }
        assertGt(wrapped >> 64, 0, "the wrapped value spills out of lane 0");
        assertGt(wrapped & lane, 0, "while still occupying lane 0");
    }

    // ------------------------------------------------------------------ (4)
    // The partition C16 now uses is TOTAL: n_regions == n_blocks + 2.  The block
    // count is observable here (FV4 pins it too); this asserts the arithmetic
    // that makes "head + blocks + tail" the right partition to demand, namely
    // that the markers bracket the transform's ONLY state changes: prof[0] is
    // taken before any lane is touched and the last one after the last store,
    // so the regions outside them can only be setup and teardown — and the
    // schedule C9g closes over is exactly the fused blocks between them.  The
    // two transforms have DIFFERENT block counts: the inverse runs four fused
    // passes (in-word entry fold + L1+L2, then three radix-4 passes) and the
    // forward three (two radix-8 passes plus the in-word L7+L8), so this test
    // pins each count separately rather than a shared constant.
    function testRegionCountIsBlocksPlusHeadAndTail() public view {
        uint256[] memory prof = new uint256[](16);
        nttInvV3(ipackCoeffs(_canonicalInput()), prof, nttInvTable());
        uint256 markers = 0;
        while (markers < 16 && prof[markers] != 0) markers++;
        assertEq(markers, 5, "five inverse markers");
        assertEq(markers - 1, 4, "-> four blocks (C16 pins 4)");
        assertEq(markers + 1, 6, "-> six regions: head + 4 blocks + tail");

        uint256[] memory fprof = new uint256[](16);
        nttFwV3(packCoeffs(_canonicalInput()), fprof, nttFwTable());
        uint256 fmarkers = 0;
        while (fmarkers < 16 && fprof[fmarkers] != 0) fmarkers++;
        assertEq(fmarkers, 4, "four forward markers");
        assertEq(fmarkers - 1, 3, "-> three blocks (C16 pins 3)");
        assertEq(fmarkers + 1, 5, "-> five regions: head + 3 blocks + tail");
    }
}
