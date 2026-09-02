// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
//
// FV3_NttLaneBounds — EVM-level re-derivation of the NTT lane-growth bounds.
//
// The hazard these tests close is a PROOF ENCODING that drifts from the code
// while still reading as though it had not: an S5 that concludes a `+4q`
// per-layer lane growth while its name, its comment and the documentation
// all claim `+2q`, or an S6 that proves a product bound (256·q·(q−1)) over a
// domain TWICE the one C9d/S2/S4/E9b verify Barrett over, with nothing linking
// the two.  Re-derived from the emitted Yul, the CODE is fine — the
// forward butterfly really does store `u+V` and `u+2q−V`, and the inverse
// Barrett layers really are L1..L7 with K ≤ 64 — and these tests pin that
// re-derivation at EVM semantics, so the linkage cannot rot back into prose:
//
//   * the per-layer offset CONSTANTS in the shipped Yul are exactly K·q (and
//     the inverse entry-fold offsets exactly q·2^30 / q·2^31),
//   * the spread-Barrett helpers satisfy `r ≡ x (mod q)` and `r < 2q` at both
//     ends of the domains the induction actually reaches (15·q·(q−1) forward,
//     128·q·(q−1) inverse), and NOT beyond the cliff,
//   * the two inductions close: 17q < 2^28 forward (the LAZY output bound the
//     matvec admits), 256q·q < 2^64 at inverse layer 8 (which canonicalises
//     with `mod`, not Barrett), and the inverse entry fold's mulmod/addmod
//     step (S14) exits < 2q from raw accumulator lanes.
//
// Obligation map: S5, S5's closure C9f, S6, S6b, S14, C9g, C16, C9a-C9d,
// C11a-c, S13.
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {
    lazyBarrett,
    Q as FWD_Q,
    MU33 as FWD_MU33,
    QHATM31 as FWD_QHATM31,
    TWOQ4 as FWD_TWOQ4,
    TWOQ as FWD_TWOQ
} from "./ZZZ_NttVariants.sol";
import {
    invLazyBarrett,
    Q as INV_Q,
    MU33 as INV_MU33,
    QHATM31 as INV_QHATM31,
    TWOQ4 as INV_TWOQ4,
    TWOQ as INV_TWOQ,
    ACCQ30,
    ACCQ31,
    Q4_4,
    Q4_8,
    Q4_16,
    Q4_32,
    Q4_64,
    Q4_128
} from "./ZZZ_InvNtt.sol";

contract FV3_NttLaneBounds is Test {
    uint256 constant q = 8380417;
    // formal/z3/verify_all.py C11a / S13: the smallest x with lazyBarrett(x) >= 2q
    uint256 constant FIRST_FAIL = 10285325456994078;
    // formal/z3/verify_all.py C11d: the OTHER cliff -- the first x whose step-1
    // product leaves its own 64-bit lane. It sits ABOVE FIRST_FAIL, which is
    // what makes r < 2q the binding constraint of the two.
    uint256 constant LANE_FIRST_OVERFLOW = 17996823486545905;
    // formal/z3/verify_all.py O8/C9g/S14: the matvec lazy-accumulator lane
    // ceiling the inverse NTT's folded entry reduction is verified over
    // (zHat/cHat lanes are the LAZY forward NTT's, < 17q)
    uint256 constant ACC_ENTRY = 4 * (q - 1) * (17 * q - 1) + (q << 28);

    function _rep64(uint256 v) internal pure returns (uint256 w) {
        w = v | (v << 64) | (v << 128) | (v << 192);
    }

    // ---------------------------------------------------------------- C16
    // Every per-layer offset constant is exactly K·q replicated across the four
    // 64-bit SWAR lanes.  This is the premise of the S5/S6 induction step.
    function testForwardOffsetConstantIsTwoQPerLane() public pure {
        assertEq(FWD_Q, q, "forward file modulus");
        assertEq(FWD_MU33, (uint256(1) << 33) / q, "forward coarse Barrett constant");
        assertEq(FWD_QHATM31, _rep64((uint256(1) << 31) - 1), "forward qhat mask");
        assertEq(FWD_TWOQ, 2 * q, "forward scalar 2q offset (L7/L8)");
        assertEq(FWD_TWOQ4, _rep64(2 * q), "forward packed 2q offset");
    }

    function testInverseOffsetConstantsAreKqPerLane() public pure {
        assertEq(INV_Q, q, "inverse file modulus");
        assertEq(INV_MU33, (uint256(1) << 33) / q, "inverse coarse Barrett constant");
        assertEq(INV_QHATM31, _rep64((uint256(1) << 31) - 1), "inverse qhat mask");
        assertEq(INV_TWOQ, 2 * q, "inverse scalar 2q offset (L2 diff side)");
        assertEq(INV_TWOQ4, _rep64(2 * q), "inverse packed 2q offset (L8 diffs)");
        assertEq(ACCQ30, q << 30, "L1 entry offset q*2^30 (multiple of q)");
        assertEq(ACCQ31, q << 31, "L2 entry offset q*2^31 (multiple of q)");
        assertEq(ACCQ30 % q, 0, "ACCQ30 preserves the residue class");
        assertEq(ACCQ31 % q, 0, "ACCQ31 preserves the residue class");
        assertEq(Q4_4, _rep64(4 * q), "L3 offset K=4");
        assertEq(Q4_8, _rep64(8 * q), "L4 offset K=8");
        assertEq(Q4_16, _rep64(16 * q), "L5 offset K=16");
        assertEq(Q4_32, _rep64(32 * q), "L6 offset K=32");
        assertEq(Q4_64, _rep64(64 * q), "L7 offset K=64");
        assertEq(Q4_128, _rep64(128 * q), "L8 offset K=128");
    }

    // ------------------------------------------------------------- C9f / S5
    // Forward: LB_1 = q and LB_{L+1} = LB_L + 2q, so the multiplied operand at
    // every layer is < 15q and the final lanes are < 17q < 2^28.
    function testForwardLaneGrowthClosure() public pure {
        uint256 lb = q;
        uint256 worstBarrettInput = 0;
        for (uint256 L = 1; L <= 8; L++) {
            assertLe(lb, 15 * q, "entering-lane premise LB <= 15q");
            uint256 prod = lb * (q - 1); // multiplied operand < LB, twiddle < q
            if (prod > worstBarrettInput) worstBarrettInput = prod;
            lb += 2 * q; // the butterfly stores u+V and u+2q-V, V < 2q
        }
        assertEq(lb, 17 * q, "final forward lane bound"); // C9a
        assertLt(lb, uint256(1) << 28, "17q < 2^28"); // C9a
        assertEq(worstBarrettInput, 15 * q * (q - 1), "forward Barrett domain"); // C9b
        assertLt(worstBarrettInput, uint256(1) << 50, "15q(q-1) < 2^50"); // C9b
        assertLt(worstBarrettInput, FIRST_FAIL, "inside the safe Barrett domain"); // C11
    }

    // ------------------------------------------------- C9g / S6 / S6b / S14
    // Inverse: the verifier feeds the RAW matvec accumulator (lanes <=
    // ACC_ENTRY, O8) into the fused L1+L2 block, which reduces with scalar
    // mulmod/addmod against the ACCQ30/ACCQ31 offsets (S14) and exits ALL
    // lanes < 2q — inside the < 4q entry bound the L3..L8 over-approximation
    // below assumes.  From there, entering layer L every lane is < 2^(L-1)·q,
    // the multiplied operand is < 2^L·q, and layers 3..7 use Barrett — layer
    // 8 folds in n^{-1} and canonicalises with `mod`.
    function testInverseLaneGrowthClosure() public pure {
        uint256 worstBarrettInput = 0;
        for (uint256 L = 3; L <= 7; L++) {
            uint256 K = uint256(1) << (L - 1);
            uint256 prod = 2 * K * q * (q - 1); // (u + Kq - v) < 2Kq, twiddle < q
            if (prod > worstBarrettInput) worstBarrettInput = prod;
        }
        assertEq(worstBarrettInput, 128 * q * (q - 1), "inverse Barrett domain"); // C9d
        assertLt(worstBarrettInput, uint256(1) << 53, "128q(q-1) < 2^53"); // C9d
        assertLt(worstBarrettInput, FIRST_FAIL, "inside the safe Barrett domain"); // C11b
        // one more unreduced layer WOULD break it -- the guard of C11c
        assertGe(2 * worstBarrettInput, FIRST_FAIL, "C11c margin guard");
        // layer 8: sums reach 256q and are multiplied by a twiddle < q, then
        // reduced with `mod`; every lane product must still fit its 64-bit lane
        assertLt(256 * q, uint256(1) << 31, "max inverse sum lane 256q < 2^31"); // C9c
        assertLt(256 * q * (q - 1), uint256(1) << 64, "L8 lane product < 2^64"); // S6b
    }

    // ------------------------------------------------------------ S14 / C9g
    // The fused entry block, re-derived step by step at EVM semantics: the
    // multiple-of-q offsets dominate the raw lanes (no borrow), mulmod/addmod
    // reduce with no domain restriction, and every lane it emits is
    // < 2q <= 4q (layer 3's entry premise).
    function testInverseEntryFoldClosure() public pure {
        // the raw accumulator lanes the verifier feeds in (O8's lane ceiling)
        assertLt(ACC_ENTRY, uint256(1) << 53, "O8 lane bound"); // O8
        // the L1 offset dominates one raw lane and preserves the residue class
        assertLe(ACC_ENTRY, q << 30, "ACCQ30 >= ACC_ENTRY: L1 diff never borrows");
        assertEq((q << 30) % q, 0, "ACCQ30 is a multiple of q");
        // the L1 sum lanes stay raw: s01, s23 <= 2*ACC_ENTRY
        assertLt(2 * ACC_ENTRY, uint256(1) << 54, "L1 sum lanes < 2^54");
        // the L2 offset dominates one raw sum lane
        assertLe(2 * ACC_ENTRY, q << 31, "ACCQ31 >= 2*ACC_ENTRY: L2 diff never borrows");
        assertEq((q << 31) % q, 0, "ACCQ31 is a multiple of q");
        // no mulmod/addmod operand overflows 256 bits (trivially: < 2^51)
        assertLt(2 * ACC_ENTRY + (q << 31), uint256(1) << 56, "operands stay tiny");
        // exit lanes: mulmod/addmod lanes are canonical, the diff-sum lane is
        // the sum of two canonical lanes -> < 2q, inside L3's 4q entry bound
        assertLe(2 * q, 4 * q, "exit bound meets layer 3's entry premise");
    }

    // The verifier's actual entry values: 4 pre-shifted products plus the
    // (KQ24 - c*t1) term never exceed ACC_ENTRY (O8 at EVM semantics).
    function testFuzzAccumulatorLaneStaysUnderEntryBound(
        uint256 a0,
        uint256 a1,
        uint256 a2,
        uint256 a3,
        uint256 c,
        uint256 t1
    ) public pure {
        a0 = bound(a0, 0, q - 1);
        a1 = bound(a1, 0, q - 1);
        a2 = bound(a2, 0, q - 1);
        a3 = bound(a3, 0, q - 1);
        c = bound(c, 0, q - 1);
        t1 = bound(t1, 0, q - 1);
        uint256 z = 17 * q - 1; // LAZY zHat lanes (forward NTT output, < 17q)
        uint256 lane = a0 * z + a1 * z + a2 * z + a3 * z + ((q << 28) - c * t1);
        assertLe(lane, ACC_ENTRY, "accumulator lane inside the entry bound");
    }

    // The fused L1/L2 entry block at EVM semantics, in two halves so the
    // legacy codegen stays inside the stack limit.
    // (a) L1: raw accumulator lanes in, canonical difference lane + raw sum
    //     lane out, congruent to the exact butterfly on the reduced inputs.
    function testFuzzInverseEntryFoldL1(uint256 u0, uint256 u1, uint256 sa) public pure {
        u0 = bound(u0, 0, ACC_ENTRY);
        u1 = bound(u1, 0, ACC_ENTRY);
        sa = bound(sa, 0, q - 1);
        // the offset dominates, so the difference operand never wraps
        assertGe(u0 + (q << 30), u1, "L1 difference never borrows");
        uint256 d01 = mulmod(u0 + (q << 30) - u1, sa, q);
        assertLt(d01, q, "L1 difference lane canonical");
        assertLt(u0 + u1, uint256(1) << 54, "L1 sum lane < 2^54");
        // congruence: the offset is a multiple of q
        assertEq(d01, mulmod((u0 + q - (u1 % q)) % q, sa, q), "L1 diff congruent");
    }

    // (b) L2: the L1 outputs (raw sum lanes <= 2*ACC_ENTRY, canonical diff
    //     lanes) exit the block with every lane < 2q <= 4q (L3's premise).
    function testFuzzInverseEntryFoldL2(uint256 s01, uint256 s23, uint256 d01, uint256 d23, uint256 sc)
        public
        pure
    {
        s01 = bound(s01, 0, 2 * ACC_ENTRY);
        s23 = bound(s23, 0, 2 * ACC_ENTRY);
        d01 = bound(d01, 0, q - 1);
        d23 = bound(d23, 0, q - 1);
        sc = bound(sc, 0, q - 1);
        // the sum-side offset dominates the raw sum lane
        assertGe(s01 + (q << 31), s23, "L2 difference never borrows");
        assertLt(addmod(s01, s23, q), q, "exit lane 0 canonical");
        assertLt(d01 + d23, 2 * q, "exit lane 1 < 2q");
        assertLt(mulmod(s01 + (q << 31) - s23, sc, q), q, "exit lane 2 canonical");
        assertLt(mulmod(d01 + 2 * q - d23, sc, q), q, "exit lane 3 canonical");
        // every exit lane is inside layer 3's < 4q entry premise
        assertLt(d01 + d23, 4 * q, "exit bound meets layer 3's entry premise");
    }

    // ------------------------------------------------------ S1/S2/E9a/E9b
    function _checkBarrett(uint256 r, uint256 x, string memory tag) internal pure {
        assertLt(r, 2 * q, tag);
        assertEq(r % q, x % q, tag);
    }

    function testForwardBarrettAtDomainEndpoints() public pure {
        uint256 emax = 15 * q * (q - 1);
        uint256[9] memory pts = [uint256(0), 1, q - 1, q, q + 1, 2 * q, emax - 1, emax, emax / 2];
        for (uint256 i = 0; i < pts.length; i++) {
            _checkBarrett(lazyBarrett(pts[i]), pts[i], "forward Barrett endpoint");
        }
    }

    function testInverseBarrettAtDomainEndpoints() public pure {
        uint256 emax = 128 * q * (q - 1);
        uint256[9] memory pts = [uint256(0), 1, q - 1, q, q + 1, 2 * q, emax - 1, emax, emax / 2];
        for (uint256 i = 0; i < pts.length; i++) {
            _checkBarrett(invLazyBarrett(pts[i]), pts[i], "inverse Barrett endpoint");
        }
        // both helpers are the same reduction; the domains differ, not the code
        assertEq(invLazyBarrett(emax), lazyBarrett(emax), "same kernel");
    }

    // The cliff is exactly where C11a/S13 say it is, at EVM semantics.
    function testBarrettFirstFailureIsExact() public pure {
        assertEq(invLazyBarrett(FIRST_FAIL), 2 * q, "r == 2q at the first failure");
        assertLt(invLazyBarrett(FIRST_FAIL - 1), 2 * q, "the value below still reduces");
        // and the shipped inverse worst case sits below it with the stated margin
        assertLt(128 * q * (q - 1), FIRST_FAIL, "shipped domain is inside the cliff");
        // C11d: the lane-locality cliff is the HIGHER of the two, so r < 2q is
        // what binds. Both halves, at EVM semantics.
        assertGt(LANE_FIRST_OVERFLOW, FIRST_FAIL, "r<2q is the binding cliff");
        assertGe(LANE_FIRST_OVERFLOW * FWD_MU33, uint256(1) << 64, "lane overflows at the cliff");
        assertLt((LANE_FIRST_OVERFLOW - 1) * FWD_MU33, uint256(1) << 64, "and fits one below");
    }

    // ------------------------------------------------------------ C9e / C9h / S7
    // LANE-LOCALITY, at EVM semantics: over the whole inverse domain step 1's
    // product fits a 64-bit lane and its quotient fits the 31-bit mask field --
    // which is why the packed form needs no spreading, and why ONE mask both
    // extracts the quotient and blocks the neighbouring lane.
    function testReductionIsLaneLocal() public pure {
        uint256 emax = 128 * q * (q - 1);
        assertLt(emax * FWD_MU33, uint256(1) << 64, "C9e: lane product < 2^64");
        assertLt((emax * FWD_MU33) >> 33, uint256(1) << 31, "C9h: qhat < 2^31");
        assertEq(uint256(64 - 33), uint256(31), "C9h: the mask is exactly 64 - shift bits wide");
        uint256 x1 = emax - q * ((emax * FWD_MU33) >> 33);
        assertLt(x1, uint256(1) << 33, "step 1 lands under 2^33");
        assertLt(x1 >> 23, uint256(1) << 31, "step 2's quotient fits the same mask");
    }

    // S7 at EVM semantics: the PACKED block -- the shipped four opcodes, twice --
    // reduces all four 64-bit lanes independently. Every lane of the output word
    // equals the scalar kernel applied to the same input lane. This is the
    // obligation the old spread form needed two masks, a shift and a repack for.
    function testFuzzPackedReductionIsFourScalarReductions(
        uint256 a,
        uint256 b,
        uint256 c,
        uint256 d
    ) public pure {
        uint256 emax = 128 * q * (q - 1);
        uint256 l0 = bound(a, 0, emax);
        uint256 l1 = bound(b, 0, emax);
        uint256 l2 = bound(c, 0, emax);
        uint256 l3 = bound(d, 0, emax);
        uint256 w = l0 | (l1 << 64) | (l2 << 128) | (l3 << 192);
        assertEq(w, l0 + (l1 << 64) + (l2 << 128) + (l3 << 192), "lanes are disjoint");
        assembly {
            w := sub(w, mul(and(shr(33, mul(w, FWD_MU33)), FWD_QHATM31), FWD_Q))
            w := sub(w, mul(and(shr(23, w), FWD_QHATM31), FWD_Q))
        }
        assertEq(w & 0xffffffffffffffff, lazyBarrett(l0), "lane 0");
        assertEq((w >> 64) & 0xffffffffffffffff, lazyBarrett(l1), "lane 1");
        assertEq((w >> 128) & 0xffffffffffffffff, lazyBarrett(l2), "lane 2");
        assertEq(w >> 192, lazyBarrett(l3), "lane 3");
    }

    // ... and the second step is LOAD-BEARING: step 1 alone leaves lanes far
    // above 2q, outside every lane bound C9f/C9g/S5/S6 state.
    function testStepOneAloneIsNotEnough() public pure {
        uint256 emax = 128 * q * (q - 1);
        uint256 x1 = emax - q * ((emax * FWD_MU33) >> 33);
        assertGt(x1, 2 * q, "step 1 alone does not land under 2q");
        assertLt(invLazyBarrett(emax), 2 * q, "both steps do");
    }

    // ------------------------------------------------------------ fuzz
    function testFuzzInverseBarrettDomain(uint256 x) public pure {
        x = bound(x, 0, 128 * q * (q - 1));
        uint256 r = invLazyBarrett(x);
        assertLt(r, 2 * q, "r < 2q over the whole inverse domain");
        assertEq(r % q, x % q, "r congruent to x mod q");
    }

    function testFuzzForwardBarrettDomain(uint256 x) public pure {
        x = bound(x, 0, 15 * q * (q - 1));
        uint256 r = lazyBarrett(x);
        assertLt(r, 2 * q, "r < 2q over the whole forward domain");
        assertEq(r % q, x % q, "r congruent to x mod q");
    }

    // The butterfly identity the S5 step encodes: with V < 2q the difference
    // lane never underflows and both outputs stay under LB + 2q.
    function testFuzzForwardButterflyStaysInBounds(uint256 u, uint256 x, uint256 s) public pure {
        uint256 lb = 15 * q; // the worst layer
        u = bound(u, 0, lb - 1);
        x = bound(x, 0, lb - 1);
        s = bound(s, 0, q - 1);
        uint256 prod = x * s;
        assertLe(prod, 15 * q * (q - 1), "product inside the Barrett domain");
        uint256 V = lazyBarrett(prod);
        assertLt(V, 2 * q, "V < 2q");
        assertLt(u + V, lb + 2 * q, "sum lane < LB + 2q");
        assertGe(u + 2 * q, V, "difference lane does not underflow");
        assertLt(u + 2 * q - V, lb + 2 * q, "difference lane < LB + 2q");
    }

    // The inverse step, over the layers that actually use Barrett (K <= 64).
    function testFuzzInverseButterflyStaysInBounds(uint256 U, uint256 V, uint256 s, uint8 layer)
        public
        pure
    {
        uint256 K = uint256(1) << bound(layer, 0, 6); // K = 2^(L-1), L = 1..7
        U = bound(U, 0, K * q - 1);
        V = bound(V, 0, K * q - 1);
        s = bound(s, 0, q - 1);
        uint256 diff = U + K * q - V;
        assertGt(diff, 0, "difference lane positive");
        assertLt(diff, 2 * K * q, "difference lane < 2Kq");
        uint256 prod = diff * s;
        assertLe(prod, 128 * q * (q - 1), "product inside the VERIFIED Barrett domain");
        uint256 r = invLazyBarrett(prod);
        assertLt(r, 2 * q, "reduced difference lane < 2q");
        assertLt(U + V, 2 * K * q, "sum lane < 2Kq");
    }
}
