// SPDX-License-Identifier: MIT
// FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
// ===========================================================================
// FV2_Barrett.sol — bytecode-level obligations that CLOSE the ten halmos
// TIMEOUTs of test/FV_Kernels.sol, by changing what is asked of the
// bit-vector engine rather than how long it is given.
//
// THE PROBLEM
// -----------
// `check_c1/c2/c1a/c1c/c1d/c1e/c3/c4/c6/c7` all ask a QF_BV solver to bound a
// QUOTIENT: for the shipped two-step kernel,
//     x1 = x  - q*((x*MU33) >> 33)   then   r = x1 - q*(x1 >> 23)   with r < 2q
// for x up to 2^53.  Measured on the equivalent SINGLE-step form of exactly
// this shape (`x - q*((x*MU52) >> 52) < 2q`, same 2^53 domain):
//   * halmos 0.3.3 + yices 2.6.4      -> TIMEOUT at 300 s (every one)
//   * halmos 0.3.3 + z3 4.12.6        -> TIMEOUT at 300 s
//   * halmos 0.3.3 + bitwuzla 0.8.1   -> TIMEOUT at 300 s
//   * narrowing the symbolic input to a 53-bit TERM (not just a 53-bit range
//     constraint) does not help — still TIMEOUT at 300 s
//   * a raw QF_BV query with no EVM layer at all returns `unknown` at word
//     widths 96/128/160/256 (z3, 120 s each)
// It is not a budget problem.  Bit-blasting is the wrong engine for a
// linear-integer fact about a floor division, and splitting one floor division
// into two does not change that.
//
// THE FIX
// -------
// Split the statement along the line where each tool is strong:
//
//   (1) the ARITHMETIC — `q*⌊x·MU33/2^33⌋ ≤ x`, `q*⌊x1/2^23⌋ ≤ x1` and
//       `r < 2q`, plus the 4-lane SWAR non-interference — is proved in Lean 4,
//       in `formal/lean/Mldsa/Barrett.lean`, **under exact EVM 256-bit
//       semantics** (`evmMul a b = (a*b) % 2^256`, `evmShr k a = a / 2^k`,
//        `evmSub a b = (a + (2^256 - b % 2^256)) % 2^256`).  Wrap-around is in
//       the definitions, and the proof shows it does not occur.  Kernel-checked,
//       zero `sorry`, axiom-audited.
//
//   (2) the REFINEMENT — that the compiled bytecode really is that opcode
//       chain, and that every intermediate stays inside a word AND inside its
//       own 64-bit lane — is proved here.  Those are pure bit-slicing facts;
//       halmos discharges each in milliseconds.
//
// Nothing is assumed twice and nothing is assumed away.  What remains is stated
// exactly, in FORMAL_VERIFICATION.md §2d: the composition of (1) and (2) is a
// modus ponens over named theorems, performed by a reader, not by a tool.
// [LEAN] tags below name the theorem in formal/lean/Mldsa/Barrett.lean that
// supplies the arithmetic side of the step.
//
// Run:
//   halmos --contract FV2Barrett  --function check_ --loop 16 \
//          --solver-timeout-assertion 60000
//   halmos --contract FV2Canaries --function check_ --loop 16   # all MUST fail
// ===========================================================================
pragma solidity ^0.8.25;

uint256 constant Q = 8380417; // == 2^23 - 2^13 + 1
uint256 constant MU33 = 1025; // == floor(2^33 / Q) == 2^10 + 1
uint256 constant LANE = 0xffffffffffffffff;
// 31 bits at the bottom of each of the four 64-bit lanes
uint256 constant QHATM31 = 0x000000007fffffff000000007fffffff000000007fffffff000000007fffffff;

uint256 constant FWD_MAX = 15 * Q * (Q - 1); // 1_053_470_710_702_080  < 2^50
uint256 constant INV_MAX = 128 * Q * (Q - 1); // 8_989_616_731_324_416  < 2^53

// the smallest x whose reduction is no longer < 2q (z3 Optimize; Lean firstFail)
uint256 constant FIRST_FAIL = 10285325456994078; // > 2^53, < 2^54
// the smallest x whose product x*MU33 leaves its own 64-bit lane. It sits ABOVE
// FIRST_FAIL, so `r < 2q` — not lane overflow — is the binding constraint.
uint256 constant LANE_CLIFF = 17996823486545905;
// exact bound on step 1's output over the whole documented domain
uint256 constant STEP1_MAX = 7508854654; // < 2^33; STEP1_MAX >> 23 == 895

uint256 constant MASK31 = (1 << 31) - 1;
uint256 constant MASK33 = (1 << 33) - 1;
uint256 constant MASK50 = (1 << 50) - 1;
uint256 constant MASK53 = (1 << 53) - 1;
uint256 constant MASK54 = (1 << 54) - 1;

// ---------------------------------------------------------------------------
// KERNEL COPIES — character-identical to test/FV_Kernels.sol, which is in turn
// character-identical to ZZZ_NttVariants.sol:724-729 / ZZZ_InvNtt.sol:447-452
// (scalar) and ZZZ_NttVariants.sol:470-471 / ZZZ_InvNtt.sol:303-304 (packed
// SWAR). The scalar form carries no QHATM31 masks — exactly as the sources do —
// because a scalar has no neighbouring lane to protect.
// ---------------------------------------------------------------------------
function kLazyBarrett(uint256 x) pure returns (uint256 r) {
    assembly ("memory-safe") {
        r := sub(x, mul(shr(33, mul(x, MU33)), Q))
        r := sub(r, mul(shr(23, r), Q))
    }
}

function kBarrettStep1(uint256 x) pure returns (uint256 r) {
    assembly ("memory-safe") {
        r := sub(x, mul(shr(33, mul(x, MU33)), Q))
    }
}

function kQhat(uint256 x) pure returns (uint256 qhat) {
    assembly ("memory-safe") {
        qhat := shr(33, mul(x, MU33))
    }
}

/// step-2 quotient: the same Barrett step with mu = floor(2^23/Q) == 1, so the
/// reciprocal multiply is elided
function kQhat2(uint256 x1) pure returns (uint256 qhat) {
    assembly ("memory-safe") {
        qhat := shr(23, x1)
    }
}

function kProd(uint256 x) pure returns (uint256 p) {
    assembly ("memory-safe") {
        p := mul(x, MU33)
    }
}

/// the shipped packed block: four 64-bit lanes reduced IN PLACE, no spreading
/// and no repacking
function kSwarBarrett4(uint256 t0in) pure returns (uint256 out) {
    assembly ("memory-safe") {
        let t0 := t0in
        t0 := sub(t0, mul(and(shr(33, mul(t0, MU33)), QHATM31), Q))
        t0 := sub(t0, mul(and(shr(23, t0), QHATM31), Q))
        out := t0
    }
}

function kSwarStep1(uint256 t0in) pure returns (uint256 out) {
    assembly ("memory-safe") {
        let t0 := t0in
        t0 := sub(t0, mul(and(shr(33, mul(t0, MU33)), QHATM31), Q))
        out := t0
    }
}

function kSwarStep2(uint256 t0in) pure returns (uint256 out) {
    assembly ("memory-safe") {
        let t0 := t0in
        t0 := sub(t0, mul(and(shr(23, t0), QHATM31), Q))
        out := t0
    }
}

// the two mask extractions, isolated
function kAndQhatm31(uint256 y) pure returns (uint256 m) {
    assembly ("memory-safe") {
        m := and(y, QHATM31)
    }
}

function kStep2Mask(uint256 y) pure returns (uint256 m) {
    assembly ("memory-safe") {
        m := and(shr(23, y), QHATM31)
    }
}

// ===========================================================================
contract FV2Barrett {
    // -----------------------------------------------------------------------
    // w0: the domain constants are what the Lean theorems are instantiated at,
    // and the width masks used below do not narrow them.
    //   [LEAN] Mldsa.Barrett.fwdMax_val / invMax_val / invMax_lt_two_pow_53
    // -----------------------------------------------------------------------
    function check_w0_domainConstants(uint256 x) public pure {
        assert(INV_MAX == 8989616731324416);
        assert(FWD_MAX == 1053470710702080);
        assert(INV_MAX <= MASK53);
        assert(FWD_MAX <= MASK50);
        assert(Q + (1 << 13) == (1 << 23) + 1); // Q == 2^23 - 2^13 + 1
        assert(MU33 == (1 << 10) + 1); // MU33 == floor(2^33/Q)
        assert(MU33 * Q + 7167 == (1 << 33)); // d33 == 2^33 - MU33*Q == 7167
        if (x > INV_MAX) return;
        assert((x & MASK53) == x); // masking is the identity on the domain
    }

    // -----------------------------------------------------------------------
    // w1: the first MUL cannot wrap — and much more: it cannot even leave its
    // own 64-bit LANE. `x*MU33 <= 9214357149607526400 < 2^64`. This is the
    // whole reason the spread/repack pair could be deleted from the kernel.
    //   feeds Lean hypothesis `hW : X * mu < W` of barrettEVM_eq_nat
    // -----------------------------------------------------------------------
    function check_w1_firstMulIsLaneLocal(uint256 xin) public pure {
        uint256 x = xin & MASK53;
        if (x > INV_MAX) return;
        assert(kProd(x) < (1 << 64)); // LANE-LOCALITY, not merely no-wrap
        // and it really is the mathematical product: MU33 = 2^10 + 1, so the
        // shift-add form is the same integer whenever nothing wraps.
        // (Stated without DIV on purpose: a 256-bit non-power-of-two DIV is what
        // makes these queries intractable, and it is not needed here.)
        assert(kProd(x) == (x << 10) + x);
    }

    // -----------------------------------------------------------------------
    // w2: `shr(33, .)` is exactly floor division by 2^33 — i.e. the EVM SHR the
    // kernel emits is the `evmShr` of the Lean model, with an exact remainder.
    // The same for step 2's `shr(23, .)`.
    // -----------------------------------------------------------------------
    function check_w2_shrIsFloorDiv(uint256 xin) public pure {
        uint256 x = xin & MASK53;
        if (x > INV_MAX) return;
        uint256 p = kProd(x);
        uint256 qh = kQhat(x);
        uint256 s = p & MASK33;
        assert(p == (qh << 33) + s); // exact Euclidean split
        assert(s < (1 << 33));
        assert(qh == p / (1 << 33)); // == floor division

        uint256 x1 = kBarrettStep1(x);
        uint256 qh2 = kQhat2(x1);
        uint256 t = x1 & ((1 << 23) - 1);
        assert(x1 == (qh2 << 23) + t);
        assert(qh2 == x1 / (1 << 23));
    }

    // -----------------------------------------------------------------------
    // w3: both quotients fit the 31-bit QHATM31 window, and neither of the two
    // second MULs can wrap.
    //   [LEAN] Mldsa.Barrett.qhat_lt_two_pow_31
    // qhat < 2^31 is the SAME fact as w1's lane-locality: after shr(33, .) the
    // next lane's bits start at bit 31, so one mask both extracts the quotient
    // and blocks the neighbour, and it is exact precisely while x*MU33 < 2^64.
    // -----------------------------------------------------------------------
    function check_w3_qhatFitsAndSecondMulNoWrap(uint256 xin) public pure {
        uint256 x = xin & MASK53;
        if (x > INV_MAX) return;
        uint256 qh = kQhat(x);
        assert(qh <= MASK31);
        assert(qh <= 1072692352); // the exact maximum over the domain
        uint256 prod;
        assembly {
            prod := mul(qh, Q)
        }
        assert(prod < (1 << 54)); // no wrap
        // Q = 2^23 - 2^13 + 1, so this is the mathematical product, DIV-free
        assert(prod + (qh << 13) == (qh << 23) + qh);

        // step 2 reuses the very same mask: its quotient is <= 895, and after
        // shr(23, .) the neighbour's bits begin at bit 41 — far above bit 31.
        uint256 x1 = kBarrettStep1(x);
        assert(x1 <= STEP1_MAX);
        uint256 qh2 = kQhat2(x1);
        assert(qh2 <= 895);
        assert(qh2 <= MASK31);
        uint256 prod2;
        assembly {
            prod2 := mul(qh2, Q)
        }
        assert(prod2 < (1 << 33)); // no wrap
        assert(prod2 + (qh2 << 13) == (qh2 << 23) + qh2);
    }

    // -----------------------------------------------------------------------
    // w4: the EVM SUB is ordinary subtraction on the no-borrow branch — the
    // refinement step that turns Lean's `Nat` subtraction into `SUB`.
    //   [LEAN] Mldsa.Barrett.no_borrow supplies the hypothesis `p <= x`.
    // Quantified over ALL 256-bit (x, p): no domain assumption at all.
    // -----------------------------------------------------------------------
    function check_w4_subIsExactWhenNoBorrow(uint256 x, uint256 p) public pure {
        if (p > x) return; // [LEAN] Mldsa.Barrett.no_borrow
        uint256 got;
        assembly {
            got := sub(x, p)
        }
        assert(got == x - p);
        assert(got <= x);
    }

    // -----------------------------------------------------------------------
    // w5: the kernel IS the opcode chain the Lean model defines. Purely
    // structural, and it is what makes the model faithful rather than a
    // restatement:
    //   `barrettEVM x = evmSub x1 (evmMul (evmShr 23 x1) q)` where
    //   `x1 = evmSub x (evmMul (evmShr 33 (evmMul x mu)) q)`.
    // Over ALL 256-bit x — no domain assumption.
    // -----------------------------------------------------------------------
    function check_w5_kernelIsTheOpcodeChain(uint256 x) public pure {
        uint256 qh = kQhat(x);
        uint256 step1;
        assembly {
            step1 := sub(x, mul(qh, Q))
        }
        assert(kBarrettStep1(x) == step1);

        uint256 qh2 = kQhat2(step1);
        uint256 recomposed;
        assembly {
            recomposed := sub(step1, mul(qh2, Q))
        }
        assert(kLazyBarrett(x) == recomposed);

        // and qhat is the shift of the product, not something else
        uint256 p = kProd(x);
        assembly {
            recomposed := shr(33, p)
        }
        assert(qh == recomposed);
    }

    // -----------------------------------------------------------------------
    // w6: THE TRANSFER. With the Lean facts as explicit hypotheses, the
    // compiled kernel satisfies the lazy bound. The hypotheses are named
    // theorems, not assumptions:
    //     [LEAN] Mldsa.Barrett.no_borrow           : q*qhat(x) <= x   (per step)
    //     [LEAN] Mldsa.Barrett.barrett_inverse     : barrettEVM x < 2q
    // and w1-w5 are what license reading those `Nat` statements as statements
    // about these 256-bit words.
    // -----------------------------------------------------------------------
    function check_w6_transfer(uint256 xin) public pure {
        uint256 x = xin & MASK53;
        if (x > INV_MAX) return;
        uint256 qh = kQhat(x);
        uint256 p1;
        assembly {
            p1 := mul(qh, Q)
        }
        if (p1 > x) return; // [LEAN] no_borrow, step 1
        uint256 x1 = x - p1;
        uint256 qh2 = kQhat2(x1);
        uint256 p2;
        assembly {
            p2 := mul(qh2, Q)
        }
        if (p2 > x1) return; // [LEAN] no_borrow, step 2
        if (x1 - p2 >= 2 * Q) return; // [LEAN] barrett_inverse
        assert(kBarrettStep1(x) == x1);
        assert(kLazyBarrett(x) == x1 - p2);
        assert(kLazyBarrett(x) < 2 * Q);
        // both steps subtract an exact multiple of Q, so the congruence holds
        // with no domain assumption at all
        assert(kLazyBarrett(x) == x - p1 - p2);
    }

    // -----------------------------------------------------------------------
    // w7: `and(y, QHATM31)` is exactly the Lean model `andQHATM31`, i.e. the
    // FOUR 31-bit windows at bits 0, 64, 128, 192 and nothing else.
    // Over ALL 256-bit y.
    // -----------------------------------------------------------------------
    function check_w7_andQhatm31Model(uint256 y) public pure {
        uint256 model = (y % (1 << 31)) + ((y / (1 << 64)) % (1 << 31)) * (1 << 64) + ((y / (1 << 128)) % (1 << 31))
            * (1 << 128) + ((y / (1 << 192)) % (1 << 31)) * (1 << 192);
        assert(kAndQhatm31(y) == model);
    }

    // -----------------------------------------------------------------------
    // w8: step 2's mask, `and(shr(23, y), QHATM31)`, is the same model applied
    // to the shifted word — the neighbour's bits land at bit 41 of each lane,
    // which the 31-bit window discards. Over ALL 256-bit y.
    // -----------------------------------------------------------------------
    function check_w8_step2MaskModel(uint256 y) public pure {
        uint256 sh = y >> 23;
        uint256 model = (sh % (1 << 31)) + ((sh / (1 << 64)) % (1 << 31)) * (1 << 64) + ((sh / (1 << 128)) % (1 << 31))
            * (1 << 128) + ((sh / (1 << 192)) % (1 << 31)) * (1 << 192);
        assert(kStep2Mask(y) == model);
        assert(kStep2Mask(y) == kAndQhatm31(y >> 23));
    }

    // -----------------------------------------------------------------------
    // w8b: the 4-lane packing is lossless and its lanes are recoverable —
    // `|` of disjoint lanes is `+`, and each 64-bit window reads back its lane.
    // -----------------------------------------------------------------------
    function check_w8b_lanePackingIsLossless(uint256 a, uint256 b, uint256 c, uint256 d) public pure {
        uint256 l0 = a & MASK53;
        uint256 l1 = b & MASK53;
        uint256 l2 = c & MASK53;
        uint256 l3 = d & MASK53;
        uint256 t0 = l0 | (l1 << 64) | (l2 << 128) | (l3 << 192);
        assert(t0 == l0 + (l1 << 64) + (l2 << 128) + (l3 << 192));
        assert((t0 & LANE) == l0);
        assert(((t0 >> 64) & LANE) == l1);
        assert(((t0 >> 128) & LANE) == l2);
        assert((t0 >> 192) == l3);
    }

    // -----------------------------------------------------------------------
    // w9: the PACKED first multiply is lane-local: `mul(t0, MU33)` is the
    // concatenation of the four per-lane products, because each of them is
    // < 2^64 (w1). This is the fact that replaced the spread step.
    //   [LEAN] Mldsa.Barrett.swar_lane_fits
    // -----------------------------------------------------------------------
    function check_w9_packedMulIsLaneLocal(uint256 a, uint256 b, uint256 c, uint256 d) public pure {
        uint256 l0 = a & MASK53;
        uint256 l1 = b & MASK53;
        uint256 l2 = c & MASK53;
        uint256 l3 = d & MASK53;
        if (l0 > INV_MAX || l1 > INV_MAX || l2 > INV_MAX || l3 > INV_MAX) return;
        uint256 p0 = l0 * MU33;
        uint256 p1 = l1 * MU33;
        uint256 p2 = l2 * MU33;
        uint256 p3 = l3 * MU33;
        assert(p0 < (1 << 64) && p1 < (1 << 64) && p2 < (1 << 64) && p3 < (1 << 64));
        uint256 t0 = l0 | (l1 << 64) | (l2 << 128) | (l3 << 192);
        uint256 got;
        assembly {
            got := mul(t0, MU33)
        }
        assert(got == p0 + (p1 << 64) + (p2 << 128) + (p3 << 192));
    }

    // -----------------------------------------------------------------------
    // w10: the SWAR block IS the composition of the two masked steps w7/w8 and
    // w11 name, so the Lean theorem `swar_lane_independent` is about this
    // bytecode. Over ALL 256-bit t0 — purely structural.
    // -----------------------------------------------------------------------
    function check_w10_swarIsTheComposition(uint256 t0) public pure {
        assert(kSwarBarrett4(t0) == kSwarStep2(kSwarStep1(t0)));
    }

    // -----------------------------------------------------------------------
    // w11: each packed step IS the scalar step applied to a MASKED quotient —
    // the structural half of lane independence (the arithmetic half is Lean's
    // `swar_lane_independent`). Over ALL 256-bit inputs.
    // -----------------------------------------------------------------------
    function check_w11_swarStepsAreMaskedScalarSteps(uint256 t0) public pure {
        uint256 recomposed;
        uint256 masked = kAndQhatm31(kQhat(t0));
        assembly {
            recomposed := sub(t0, mul(masked, Q))
        }
        assert(kSwarStep1(t0) == recomposed);

        uint256 masked2 = kStep2Mask(t0);
        assembly {
            recomposed := sub(t0, mul(masked2, Q))
        }
        assert(kSwarStep2(t0) == recomposed);
    }

    // -----------------------------------------------------------------------
    // w11b: on a word whose lanes are inside the domain, the packed block is
    // lane-wise the SCALAR kernel — no spread step left to hide behind.
    //   [LEAN] Mldsa.Barrett.swar_lane_independent
    // -----------------------------------------------------------------------
    function check_w11b_swarIsLanewiseScalar(uint256 a, uint256 b, uint256 c, uint256 d) public pure {
        uint256 l0 = a & MASK53;
        uint256 l1 = b & MASK53;
        uint256 l2 = c & MASK53;
        uint256 l3 = d & MASK53;
        if (l0 > INV_MAX || l1 > INV_MAX || l2 > INV_MAX || l3 > INV_MAX) return;
        uint256 t0 = l0 | (l1 << 64) | (l2 << 128) | (l3 << 192);
        uint256 out = kSwarBarrett4(t0);
        assert((out & LANE) == kLazyBarrett(l0));
        assert(((out >> 64) & LANE) == kLazyBarrett(l1));
        assert(((out >> 128) & LANE) == kLazyBarrett(l2));
        assert((out >> 192) == kLazyBarrett(l3));
    }

    // -----------------------------------------------------------------------
    // w12: the first failure point, at the bytecode level. This is what makes
    // every domain restriction above non-vacuous.
    //   [LEAN] Mldsa.Barrett.firstFail_breaks / firstFail_pred_ok
    // -----------------------------------------------------------------------
    function check_w12_firstFailIsReal(uint256 dummy) public pure {
        dummy;
        assert(kLazyBarrett(FIRST_FAIL) == 2 * Q); // the bound FAILS here
        assert(kLazyBarrett(FIRST_FAIL - 1) < 2 * Q); // and holds one below
        assert(FIRST_FAIL <= 2 * INV_MAX); // one more layer would break it
        assert(FIRST_FAIL > INV_MAX); // ... but the shipped domain is inside it
        // the margin is 1.1441x over the inverse bound, 9.76x over the forward
        assert((FIRST_FAIL * 10000) / INV_MAX == 11441);
        assert((FIRST_FAIL * 10000) / FWD_MAX == 97632);
        // it is BELOW the lane-overflow cliff, so `r < 2q` is what binds
        assert(FIRST_FAIL < LANE_CLIFF);
        assert(LANE_CLIFF * MU33 >= (1 << 64));
        assert((LANE_CLIFF - 1) * MU33 < (1 << 64));
        // and it sits in (2^53, 2^54] — which is exactly the width canary k1
        // has to open up to in order to see it
        assert(FIRST_FAIL > MASK53);
        assert(FIRST_FAIL <= MASK54);
    }
}

// ===========================================================================
// CANARIES — every one MUST report a counterexample under halmos.
// A suite of obligations with no failing canaries proves nothing about itself.
// ===========================================================================
contract FV2Canaries {
    /// K0: the tool sees assertion violations in this file at all.
    function check_k0_toolBites(uint256 x) public pure {
        assert((x & MASK53) != 12345);
    }

    /// K1: w6's domain restriction is load-bearing — ONE BIT wider and the
    /// tight bound is FALSE. The first violation is at 10,285,325,456,994,078,
    /// which is > 2^53 and <= 2^54 - 1, so a 53-bit mask (w6's own width) does
    /// NOT admit it and a 54-bit mask does: this canary fails, and the same
    /// assertion under MASK53 would not (w12 pins both halves of that).
    function check_k1_domainIsLoadBearing(uint256 xin) public pure {
        uint256 x = xin & MASK54;
        assert(kLazyBarrett(x) < 2 * Q); // must FAIL
    }

    /// K2: w6's path is satisfiable (its hypotheses are not contradictory).
    function check_k2_w6NotVacuous(uint256 xin) public pure {
        uint256 x = xin & MASK53;
        if (x > INV_MAX) return;
        uint256 qh = kQhat(x);
        uint256 p1;
        assembly {
            p1 := mul(qh, Q)
        }
        if (p1 > x) return;
        uint256 x1 = x - p1;
        uint256 qh2 = kQhat2(x1);
        uint256 p2;
        assembly {
            p2 := mul(qh2, Q)
        }
        if (p2 > x1) return;
        if (x1 - p2 >= 2 * Q) return;
        assert(false); // must be reachable
    }

    /// K3: the SWAR lane bound is load-bearing — with unconstrained 64-bit
    /// lanes a lane's product x*MU33 leaves its own lane (any lane value
    /// >= 17,996,823,486,545,905 does it, and every such value fits in 64 bits),
    /// the 31-bit QHATM31 mask then truncates that lane's qhat, and the lane
    /// stops agreeing with the scalar kernel while its neighbour is corrupted
    /// by the spill.
    function check_k3_swarNeedsLaneBound(uint256 v0, uint256 v1) public pure {
        uint256 t0 = (v0 & LANE) | ((v1 & LANE) << 64);
        assert((kSwarBarrett4(t0) & LANE) == kLazyBarrett(v0 & LANE)); // must FAIL
    }

    /// K4: the no-borrow hypothesis of w4 is load-bearing — drop it and EVM SUB
    /// is NOT subtraction.
    function check_k4_subNeedsNoBorrow(uint256 x, uint256 p) public pure {
        uint256 got;
        assembly {
            got := sub(x, p)
        }
        assert(got <= x); // must FAIL (wraps when p > x)
    }

    /// K5: STEP 2 IS LOAD-BEARING — the coarse step alone does not land under
    /// 2q. Its output only has to be < 2^33, and at the top of the documented
    /// domain it is nowhere near 2q: kBarrettStep1(INV_MAX) == 7_508_853_632,
    /// which is 448x the lazy bound 2q == 16_760_834.
    function check_k5_step2IsLoadBearing(uint256 xin) public pure {
        uint256 x = xin & MASK53;
        if (x > INV_MAX) return;
        assert(kBarrettStep1(x) < 2 * Q); // must FAIL
    }

    /// K6: the QHATM31 mask is not the identity — w7's model has content.
    function check_k6_qhatm31IsNotIdentity(uint256 y) public pure {
        assert(kAndQhatm31(y) == y); // must FAIL
    }
}
