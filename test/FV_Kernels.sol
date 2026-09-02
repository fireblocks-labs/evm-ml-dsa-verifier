// SPDX-License-Identifier: MIT
// ===========================================================================
// FV_Kernels.sol — formal-verification harness for the ML-DSA-44 verifier
// arithmetic kernels.
//
// Contents:
//   1. VERBATIM copies of the arithmetic kernels under proof, each with
//      file:line provenance. The ONLY mechanical change is that the operand
//      that the production kernel loads from memory/calldata (mload/byte/
//      calldataload of a packed field) is passed in as a function argument, so
//      a symbolic value can be substituted; every arithmetic/logic expression
//      is character-identical to the source. Where the surrounding loop is
//      irrelevant (one coefficient / one lane), only the loop body is copied.
//   2. Division-free FIPS-204 reference models (pythonref/dilithium_py/
//      utilities/utils.py: reduce_mod_pm / decompose / use_hint /
//      check_norm_bound, FIPS 204 Alg. 15/28/36/39).
//   3. halmos `check_*` proof obligations over symbolic inputs.
//
// This file deliberately has NO imports, so it cannot be broken by, and
// cannot break, files owned by other work streams.
//
// ---------------------------------------------------------------------------
// TOOL NOTE (read before trusting the halmos verdicts)
// ---------------------------------------------------------------------------
// halmos (<= 0.2.6) does NOT interpret EVM DIV/MOD when the divisor is not a
// power of two: sevm.py:mk_div/mk_mod replace them by the uninterpreted
// functions evm_bvudiv / evm_bvurem, constrained only by (x/y) <= x and
// (x%y) <= y. Any obligation whose kernel contains `div(x, 190464)`,
// `mod(x, 8380417)` or `mod(x, 44)` therefore cannot be discharged out of
// the box.
//
// Two devices are used to keep those proofs sound and non-vacuous, both
// flagged at every use site with the tag  [PIN]  or  [WITNESS]:
//
//  [PIN]     The abstract term is pinned to its true value by assuming a
//            relation that (a) is a theorem about real EVM DIV/MOD and
//            (b) determines the term UNIQUELY on the reachable numerator
//            range. Example: for N < 2q, `mod(N, q) == (N < q ? N : N - q)`.
//            Pinning is done by recomputing the identical Yul expression in
//            the check function; z3's congruence closure identifies the two
//            occurrences of the abstract term even if solc compiles them
//            differently. Because the pinned relation has exactly one
//            solution, "for all interpretations satisfying the pin" == "for
//            the real EVM semantics" — no generality is lost, but the pin
//            IS an assumption on the tool, and is independently discharged by
//            the exhaustive tests in FV_Kernels.t.sol and the machine-checked
//            queries in formal/z3/.
//  [WITNESS] The FIPS reference itself is division-free: instead of computing
//            r % q / r / alpha, the check function takes the quotient and the
//            centered remainder as extra symbolic arguments and assumes the
//            defining (division-free) relation. The relation is total and
//            functional on the stated domain (proved in the comment at each
//            use site), so quantifying over (input, witness) pairs that
//            satisfy it is exactly quantifying over inputs.
// ===========================================================================
pragma solidity ^0.8.25;

// ---------------------------------------------------------------------------
// Constants. Names and values are those of the source files, so that the
// kernel copies below can be character-identical to the originals:
//   Q, MU33, QHATM31, LANE  from test/ZZZ_NttVariants.sol:35-44
//                           and test/ZZZ_InvNtt.sol:46-64
//                           (== src/Ntt.sol / src/InvNtt.sol)
// ---------------------------------------------------------------------------
uint256 constant Q = 8380417; // ML-DSA / Dilithium prime, == 2^23 - 2^13 + 1
uint256 constant MU33 = 1025; // floor(2^33 / Q) == 2^10 + 1, coarse Barrett constant
uint256 constant LANE = 0xffffffffffffffff; // 64-bit lane mask
// qhat mask, 31 bits at the bottom of each of the four 64-bit lanes. After
// shr(33, mul(w, MU33)) the NEXT lane's bits begin at bit 31 of this lane, and a
// lane's qhat is < 2^31 exactly when its own product is < 2^64 — so ONE mask
// both extracts the quotient and stops a lane from seeing its neighbour. The
// second step reuses it: its quotient is <= 895 < 2^10 and, after shr(23, .),
// the neighbour's bits begin at bit 41.
uint256 constant QHATM31 = 0x000000007fffffff000000007fffffff000000007fffffff000000007fffffff;

// ML-DSA-44 parameters (FIPS 204 Table 1)
uint256 constant GAMMA1 = 131072; // 2^17
uint256 constant BETA = 78; // tau * eta = 39 * 2
uint256 constant GAMMA2 = 95232; // (q-1)/88
uint256 constant ALPHA = 190464; // 2 * GAMMA2
uint256 constant MHI = 44; // (q-1)/(2*GAMMA2)

// Barrett input bounds documented by the kernels
uint256 constant FWD_MAX = 15 * Q * (Q - 1); // forward NTT worst product
uint256 constant INV_MAX = 128 * Q * (Q - 1); // inverse NTT worst product (< 2^53)

// ===========================================================================
// 1. KERNEL COPIES (verbatim)
// ===========================================================================

// ---------------------------------------------------------------------------
// (a) z decode, strict variant.
// Source: test/ZZZ_E2ERef.sol:65-68 (unpackZStrict, first coefficient
// block; all 1024 blocks are textually identical modulo the field extraction
// and the destination offset):
//     let v := or(or(byte(0, w), shl(8, byte(1, w))), shl(16, and(byte(2, w), 3)))
//     fail := or(fail, iszero(lt(sub(v, 79), 261987)))
//     mstore(dst, mod(sub(8511489, v), 8380417))
// ---------------------------------------------------------------------------
function kStrictNormFail(uint256 v) pure returns (uint256 fail) {
    assembly ("memory-safe") {
        fail := or(fail, iszero(lt(sub(v, 79), 261987)))
    }
}

function kStrictCenter(uint256 v) pure returns (uint256 out) {
    assembly ("memory-safe") {
        out := mod(sub(8511489, v), 8380417)
    }
}

// numerator of the MOD above, needed to pin the abstract mod term
function kStrictCenterNum(uint256 v) pure returns (uint256 n) {
    assembly ("memory-safe") {
        n := sub(8511489, v)
    }
}

// ---------------------------------------------------------------------------
// (a) z decode, loose variant (the upstream kernel the strict decoder is
// differentially tested against; its off-by-one norm bound and its
// "z == 0 stored as q" convention are documented divergences from FIPS 204).
// Source: test/ZZZ_decode2.t.sol:43-47 (unpackZFast2, first coefficient block)
//     fail := or(fail, iszero(lt(sub(v, 78), 261989)))
//     mstore(dst, sub(add(131072, mul(8380417, shr(17, v))), v))
// ---------------------------------------------------------------------------
function kLooseNormFail(uint256 v) pure returns (uint256 fail) {
    assembly ("memory-safe") {
        fail := or(fail, iszero(lt(sub(v, 78), 261989)))
    }
}

function kLooseCenter(uint256 v) pure returns (uint256 out) {
    assembly ("memory-safe") {
        out := sub(add(131072, mul(8380417, shr(17, v))), v)
    }
}

// ---------------------------------------------------------------------------
// (a) 18-bit field extraction from a 9-byte group (4 coefficients / 72 bits).
// Source: test/ZZZ_E2ERef.sol:67,72,77,82 == test/ZZZ_decode2.t.sol:44,49,
// 54,59 (identical in both kernels), with `w := mload(src)`.
// ---------------------------------------------------------------------------
function kUnpack4(bytes32 win) pure returns (uint256 v0, uint256 v1, uint256 v2, uint256 v3) {
    assembly ("memory-safe") {
        let w := win
        v0 := or(or(byte(0, w), shl(8, byte(1, w))), shl(16, and(byte(2, w), 3)))
        v1 := or(or(shr(2, byte(2, w)), shl(6, byte(3, w))), shl(14, and(byte(4, w), 15)))
        v2 := or(or(shr(4, byte(4, w)), shl(4, byte(5, w))), shl(12, and(byte(6, w), 63)))
        v3 := or(or(shr(6, byte(6, w)), shl(2, byte(7, w))), shl(10, byte(8, w)))
    }
}

// ---------------------------------------------------------------------------
// (b) fused UseHint + decompose, one coefficient.
// Source: test/ZZZ_decode2.t.sol:82-92 (useHintFast2, first coefficient
// block; all 1024 blocks are textually identical modulo the hint-bit
// selector `and(shr(k, hmask), 1)` and the memory offsets):
//     let rv := mload(rdata)
//     let q0 := div(rv, 190464)
//     let r0 := sub(rv, mul(q0, 190464))
//     let c := gt(r0, 95232)
//     let s1 := add(q0, c)
//     let r1 := mul(s1, iszero(eq(s1, 44)))
//     let hb := and(hmask, 1)
//     r1 := mod(add(r1, mul(hb, add(1, mul(42, or(iszero(r0), c))))), 44)
// ---------------------------------------------------------------------------
function kUseHint(uint256 rv, uint256 hb) pure returns (uint256 out) {
    assembly ("memory-safe") {
        let q0 := div(rv, 190464)
        let r0 := sub(rv, mul(q0, 190464))
        let c := gt(r0, 95232)
        let s1 := add(q0, c)
        let r1 := mul(s1, iszero(eq(s1, 44)))
        r1 := mod(add(r1, mul(hb, add(1, mul(42, or(iszero(r0), c))))), 44)
        out := r1
    }
}

// the kernel's abstract DIV term (for [PIN])
function kUseHintQ0(uint256 rv) pure returns (uint256 q0) {
    assembly ("memory-safe") {
        q0 := div(rv, 190464)
    }
}

// the kernel's MOD-44 numerator, recomputed identically (for [PIN])
function kUseHintModArg(uint256 rv, uint256 hb) pure returns (uint256 x) {
    assembly ("memory-safe") {
        let q0 := div(rv, 190464)
        let r0 := sub(rv, mul(q0, 190464))
        let c := gt(r0, 95232)
        let s1 := add(q0, c)
        let r1 := mul(s1, iszero(eq(s1, 44)))
        x := add(r1, mul(hb, add(1, mul(42, or(iszero(r0), c)))))
    }
}

// ---------------------------------------------------------------------------
// (f) 6-bit w1 packing, one 4-coefficient group -> 3 bytes.
// Source: test/ZZZ_decode2.t.sol:80-127 (useHintFast2, first group): the
// `packed := ...` accumulation and the three mstore8s
//     mstore8(wp, packed); mstore8(add(wp,1), shr(8,packed)); mstore8(add(wp,2), shr(16,packed))
// mstore8 stores the LOW byte of its argument, which is what the
// `and(.., 0xff)` below models.
// ---------------------------------------------------------------------------
function kPack6(uint256 r1a, uint256 r1b, uint256 r1c, uint256 r1d)
    pure
    returns (uint256 b0, uint256 b1, uint256 b2)
{
    assembly ("memory-safe") {
        let packed := 0
        packed := r1a
        packed := or(packed, shl(6, r1b))
        packed := or(packed, shl(12, r1c))
        packed := or(packed, shl(18, r1d))
        b0 := and(packed, 0xff)
        b1 := and(shr(8, packed), 0xff)
        b2 := and(shr(16, packed), 0xff)
    }
}

// ---------------------------------------------------------------------------
// (c) TWO-STEP LANE-LOCAL lazy Barrett, scalar and packed-SWAR.
// Sources:
//   test/ZZZ_NttVariants.sol:724-729  lazyBarrett      (scalar, forward)
//   test/ZZZ_InvNtt.sol:447-452       invLazyBarrett   (scalar, inverse; the
//                                     SAME expression, different documented
//                                     input bound)
//   test/ZZZ_NttVariants.sol:470-471 / test/ZZZ_InvNtt.sol:303-304
//                                     the packed reduction, applied DIRECTLY to
//                                     the 4-lane word: no spreading, no repack,
//                                     the same opcode sequence as the scalar
//                                     form serves all four lanes at once.
// The two steps are
//   step 1   x1 := x  - Q*floor(x  * MU33 / 2^33)    MU33 = floor(2^33/Q) = 1025
//   step 2   r  := x1 - Q*floor(x1        / 2^23)    floor(2^23/Q) == 1, elided
// The scalar copy omits the QHATM31 masks — exactly as the sources do — because
// a scalar has no neighbouring lane to protect; every other token is identical.
// ---------------------------------------------------------------------------
function kLazyBarrett(uint256 x) pure returns (uint256 r) {
    assembly ("memory-safe") {
        r := sub(x, mul(shr(33, mul(x, MU33)), Q))
        r := sub(r, mul(shr(23, r), Q))
    }
}

/// the coarse step alone, exposed so the two steps can be bounded separately
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

/// step-2 quotient floor(x1 / 2^23): the same Barrett step with mu = 1, so the
/// reciprocal multiply is elided (floor(2^23/Q) == 1)
function kQhat2(uint256 x1) pure returns (uint256 qhat) {
    assembly ("memory-safe") {
        qhat := shr(23, x1)
    }
}

/// full SWAR block: all four 64-bit lanes of one word reduced IN PLACE by the
/// two-step lane-local Barrett (verbatim from test/ZZZ_NttVariants.sol:470-471,
/// `t0` being the product word)
function kSwarBarrett4(uint256 t0in) pure returns (uint256 out) {
    assembly ("memory-safe") {
        let t0 := t0in
        t0 := sub(t0, mul(and(shr(33, mul(t0, MU33)), QHATM31), Q))
        t0 := sub(t0, mul(and(shr(23, t0), QHATM31), Q))
        out := t0
    }
}

/// the two halves of that block, isolated (kSwarBarrett4 == step2 . step1)
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

// ===========================================================================
// 2. FIPS-204 REFERENCE MODELS (division-free where used symbolically)
// ===========================================================================

/// FIPS 204 sigDecode / BitUnpack(z, gamma1-1, gamma1): the packed 18-bit field
/// v encodes gamma1 - z, so z = gamma1 - v; the canonical field element is
/// z mod q.  (z == 0  <->  v == gamma1  ->  0)
function refZCenterCanonical(uint256 v) pure returns (uint256) {
    if (v <= GAMMA1) return GAMMA1 - v;
    return Q + GAMMA1 - v;
}

/// the same map with the upstream kernel's "z == 0 is stored as q" convention
function refZCenterQForZero(uint256 v) pure returns (uint256) {
    if (v < GAMMA1) return GAMMA1 - v;
    return Q + GAMMA1 - v;
}

/// pythonref/dilithium_py/utilities/utils.py:check_norm_bound(z, gamma1-beta, q)
/// -> true when the coefficient must be REJECTED: |z|_inf >= gamma1 - beta
function refNormBadStrict(uint256 v) pure returns (bool) {
    int256 z = int256(GAMMA1) - int256(v);
    int256 az = z >= 0 ? z : -z;
    return az >= int256(GAMMA1 - BETA);
}

/// the upstream kernel's (non-FIPS, off-by-one) bound: reject iff |z| > gamma1-beta
function refNormBadLoose(uint256 v) pure returns (bool) {
    int256 z = int256(GAMMA1) - int256(v);
    int256 az = z >= 0 ? z : -z;
    return az > int256(GAMMA1 - BETA);
}

/// FIPS 204 Alg. 39 UseHint / utils.py:use_hint, computed from a DIVISION-FREE
/// decomposition witness [WITNESS]:
///     r1pre in [0, 44], x in [-95231, 95232], rv == r1pre * ALPHA + x
/// which exists and is unique for every rv in [0, q) (the half-open intervals
/// {r1pre*ALPHA + x} tile the integers with period ALPHA = 190464, and
/// 0 <= rv <= 44*ALPHA = q-1).
/// Given the witness: reduce_mod_pm(rv mod ALPHA, ALPHA) == x and
/// rv - x == r1pre*ALPHA, so decompose() returns (r1pre, x) unless
/// r1pre*ALPHA == q-1 (i.e. r1pre == 44), in which case (0, x-1).
function refUseHintFromWitness(uint256 r1pre, int256 x, uint256 h) pure returns (uint256) {
    uint256 r1;
    int256 r0;
    if (r1pre == MHI) {
        r1 = 0;
        r0 = x - 1;
    } else {
        r1 = r1pre;
        r0 = x;
    }
    if (h == 1) {
        if (r0 > 0) return r1 + 1 == MHI ? 0 : r1 + 1; // (r1+1) mod 44
        return r1 == 0 ? MHI - 1 : r1 - 1; // (r1-1) mod 44
    }
    return r1;
}

/// FIPS 204 Alg. 15 (reduce_mod_pm) + Alg. 36 (decompose) + Alg. 39 (use_hint),
/// straightforward transliteration of utils.py using real division. Used by the
/// exhaustive tests (where DIV/MOD are executed, not abstracted).
function refUseHintDiv(uint256 rv, uint256 h) pure returns (uint256) {
    uint256 rp = rv % Q;
    int256 x = int256(rp % ALPHA);
    if (x > int256(GAMMA2)) x -= int256(ALPHA);
    uint256 r1;
    int256 r0;
    if (int256(rp) - x == int256(Q) - 1) {
        r1 = 0;
        r0 = x - 1;
    } else {
        r1 = uint256((int256(rp) - x) / int256(ALPHA));
        r0 = x;
    }
    if (h == 1) {
        if (r0 > 0) return (r1 + 1) % MHI;
        return (r1 + MHI - 1) % MHI;
    }
    return r1;
}

/// FIPS 204 Alg. 28 SimpleBitPack(w1, 43): 6 bits per coefficient, LSB-first
/// bitstream. Returns the 3 bytes covering 4 coefficients.
function refW1Pack(uint256 a0, uint256 a1, uint256 a2, uint256 a3)
    pure
    returns (uint256 b0, uint256 b1, uint256 b2)
{
    b0 = (a0 | (a1 << 6)) & 0xff;
    b1 = ((a1 >> 2) | (a2 << 4)) & 0xff;
    b2 = ((a2 >> 4) | (a3 << 2)) & 0xff;
}

// ===========================================================================
// 3. PROOF OBLIGATIONS  (halmos: `--function check_`)
// ===========================================================================
contract FVKernels {
    // -----------------------------------------------------------------------
    // (a-i) centered map, strict/canonical kernel == FIPS reference, for ALL
    // 2^18 packed field values.
    // [PIN] mod(sub(8511489, v), 8380417): the numerator is
    //       8511489 - v in [8249346, 8511489] c [0, 2q) for v < 2^18, and for
    //       N < 2q the EVM MOD is exactly (N < q ? N : N - q).
    // -----------------------------------------------------------------------
    function check_a1_centeredMapStrict(uint256 vin) public pure {
        uint256 v = vin & 0x3ffff; // 18-bit packed field
        uint256 n = kStrictCenterNum(v);
        assert(n < 2 * Q); // PROVEN, not assumed: pin precondition
        uint256 out = kStrictCenter(v);
        if (out != (n < Q ? n : n - Q)) return; // [PIN]
        assert(out == refZCenterCanonical(v));
        assert(out < Q); // canonical output (the packed NTT requires it)
    }

    // -----------------------------------------------------------------------
    // (a-ii) strict branchless norm test flags EXACTLY |z|_inf >= gamma1-beta.
    // Pure sub/lt: no abstraction, no assumptions.
    // -----------------------------------------------------------------------
    function check_a2_normTestStrict(uint256 vin) public pure {
        uint256 v = vin & 0x3ffff;
        assert((kStrictNormFail(v) != 0) == refNormBadStrict(v));
    }

    // -----------------------------------------------------------------------
    // (a-ii') the loose kernel's test flags EXACTLY |z|_inf > gamma1-beta
    // (i.e. it accepts the boundary |z| == gamma1-beta, which FIPS rejects).
    // -----------------------------------------------------------------------
    function check_a3_normTestLoose(uint256 vin) public pure {
        uint256 v = vin & 0x3ffff;
        assert((kLooseNormFail(v) != 0) == refNormBadLoose(v));
    }

    // -----------------------------------------------------------------------
    // (a-i') loose kernel decode == reference with the "z==0 -> q" convention,
    // and it is injective-free of MOD (mul/shr only: no abstraction).
    // -----------------------------------------------------------------------
    function check_a4_centeredMapLoose(uint256 vin) public pure {
        uint256 v = vin & 0x3ffff;
        uint256 out = kLooseCenter(v);
        assert(out == refZCenterQForZero(v));
        assert(out >= 1 && out <= Q);
    }

    // -----------------------------------------------------------------------
    // (a-iii) 18-bit field extraction from a 9-byte group equals the
    // little-endian bit layout of FIPS 204 BitUnpack (4 x 18 bits / 72 bits).
    // -----------------------------------------------------------------------
    function check_a5_bitExtract(bytes32 win) public pure {
        (uint256 v0, uint256 v1, uint256 v2, uint256 v3) = kUnpack4(win);
        // reference: W = the 9 bytes read little-endian, field k = bits [18k, 18k+18)
        uint256 W;
        for (uint256 i = 0; i < 9; ++i) {
            W |= uint256(uint8(win[i])) << (8 * i);
        }
        assert(v0 == (W & 0x3ffff));
        assert(v1 == ((W >> 18) & 0x3ffff));
        assert(v2 == ((W >> 36) & 0x3ffff));
        assert(v3 == ((W >> 54) & 0x3ffff));
    }

    // -----------------------------------------------------------------------
    // (b) UseHint/decompose branchless kernel == FIPS 204 Alg. 39, and the
    // output is in [0, 44), for ALL r in [0, q) and h in {0,1}.
    //
    // [WITNESS] (r1pre, x) is the division-free decomposition of rv.
    // [PIN]     div(rv, 190464): pinned by the Euclidean property. halmos
    //           already constrains the abstract term by (rv/190464) <= rv, so
    //           q0 <= rv < 2^23 and the pin's multiplication cannot wrap;
    //           the pin therefore has the unique solution floor(rv/190464).
    // [PIN]     mod(arg, 44): the argument is < 88 (PROVEN below), and for
    //           N < 88 the EVM MOD is exactly (N < 44 ? N : N - 44).
    // -----------------------------------------------------------------------
    function check_b1_useHint(uint256 rvin, uint256 hin, uint256 r1pre, int256 x) public pure {
        uint256 rv = rvin;
        if (rv >= Q) return; // domain: canonical w' (the caller guarantees this
            // via the canonicalising final pass of the inverse NTT)
        uint256 h = hin & 1;

        // [WITNESS] relation
        if (r1pre > MHI) return;
        if (x < -95231 || x > 95232) return;
        if (int256(rv) != int256(r1pre) * int256(ALPHA) + x) return;

        // [PIN] the kernel's DIV
        uint256 q0 = kUseHintQ0(rv);
        uint256 pinOk;
        assembly {
            let p := mul(q0, 190464)
            pinOk := and(iszero(gt(p, rv)), lt(sub(rv, p), 190464))
        }
        if (pinOk == 0) return;

        // [PIN] the kernel's MOD 44 — first PROVE the numerator is < 88
        uint256 arg = kUseHintModArg(rv, h);
        assert(arg < 88);
        uint256 m;
        assembly {
            m := mod(arg, 44)
        }
        if (m != (arg < 44 ? arg : arg - 44)) return;

        uint256 out = kUseHint(rv, h);
        assert(out == refUseHintFromWitness(r1pre, x, h));
        assert(out < MHI); // w1 coefficient range, required by the 6-bit packing
    }

    // -----------------------------------------------------------------------
    // (c) forward-NTT lazy Barrett: r = x (mod Q) with explicit witnesses,
    // r < 2Q. Division-free formulation: BOTH quotients are exhibited, so
    //   x == r + (qhat + qhat2)*Q  /\  r < 2Q
    //     =>  r = x mod Q  or  r = (x mod Q) + Q.
    // Each step subtracts an exact multiple of Q, so the congruence is
    // unconditional; the domain restriction is what buys the bound r < 2Q.
    // -----------------------------------------------------------------------
    function check_c1_lazyBarrettForward(uint256 x) public pure {
        if (x > FWD_MAX) return; // documented forward bound 15*q*(q-1)
        uint256 qhat = kQhat(x);
        assert(qhat < (1 << 31)); // QHATM31-safety (31-bit mask per 64-bit lane)
        uint256 p1;
        assembly {
            p1 := mul(qhat, Q) // wrapping mul: no Panic(0x11) path to hide in
        }
        assert(p1 <= x); // no borrow in step 1's SUB
        uint256 x1 = kBarrettStep1(x);
        assert(x1 == x - p1);
        assert(x1 <= 7508854654); // < 2^33: step 2's shift sees a 33-bit value
        uint256 qhat2 = kQhat2(x1);
        assert(qhat2 <= 895); // < 2^31: the SAME mask serves step 2
        uint256 p2;
        assembly {
            p2 := mul(qhat2, Q)
        }
        assert(p2 <= x1); // no borrow in step 2's SUB
        uint256 r = kLazyBarrett(x);
        assert(r == x1 - p2);
        assert(r == x - p1 - p2); // r === x (mod Q), witnesses qhat, qhat2
        assert(r < 2 * Q); // lazy bound
    }

    // -----------------------------------------------------------------------
    // (c) inverse-NTT lazy Barrett: same expression, larger documented bound
    // 128*q*(q-1) (worst product at layer 7). This is also the bound at which
    // LANE-LOCALITY is tightest: x*MU33 <= 9214357149607526400 < 2^64, so in
    // the packed form each lane's product stays inside its own 64-bit lane.
    // -----------------------------------------------------------------------
    function check_c2_lazyBarrettInverse(uint256 x) public pure {
        if (x > INV_MAX) return;
        uint256 qhat = kQhat(x);
        assert(qhat < (1 << 31));
        uint256 p1;
        assembly {
            p1 := mul(qhat, Q)
        }
        assert(p1 <= x);
        uint256 x1 = kBarrettStep1(x);
        assert(x1 == x - p1);
        assert(x1 <= 7508854654);
        uint256 qhat2 = kQhat2(x1);
        assert(qhat2 <= 895);
        uint256 p2;
        assembly {
            p2 := mul(qhat2, Q)
        }
        assert(p2 <= x1);
        uint256 r = kLazyBarrett(x);
        assert(r == x - p1 - p2);
        assert(r < 2 * Q);
    }

    // -----------------------------------------------------------------------
    // (c) SPLIT versions of the two obligations above. Bit-blasting the TIGHT
    // bound r < 2q (r < 2^24 against 2q = 16760834) is what makes c1/c2 time
    // out; the definitional parts are cheap and are recorded separately so the
    // timeout is scoped as narrowly as possible (obligation (g)).
    // -----------------------------------------------------------------------
    function check_c1a_barrettCongruenceOnly(uint256 x) public pure {
        if (x > INV_MAX) return;
        uint256 qhat = kQhat(x);
        uint256 x1 = kBarrettStep1(x);
        uint256 p1;
        assembly {
            p1 := mul(qhat, Q)
        }
        assert(p1 <= x); // no borrow in step 1's SUB
        assert(x1 == x - p1);
        uint256 qhat2 = kQhat2(x1);
        uint256 p2;
        assembly {
            p2 := mul(qhat2, Q)
        }
        assert(p2 <= x1); // no borrow in step 2's SUB
        assert(kLazyBarrett(x) == x - p1 - p2); // r === x (mod Q), both witnesses
    }

    /// the 31-bit mask width AND the lane-locality of the first multiply. The
    /// two are the same fact: qhat < 2^31 holds exactly when x*MU33 < 2^64.
    function check_c1b_barrettQhatBound(uint256 x) public pure {
        if (x > INV_MAX) return;
        uint256 p;
        assembly {
            p := mul(x, MU33) // < 2^64: cannot leave its own 64-bit lane
        }
        assert(p < (1 << 64)); // LANE-LOCALITY: no spreading needed
        assert(kQhat(x) < (1 << 31)); // QHATM31-safety
    }

    function check_c1c_barrettLazyBound(uint256 x) public pure {
        if (x > INV_MAX) return;
        assert(kLazyBarrett(x) < 2 * Q); // the tight one
    }

    /// scope-reduced version of the tight bound: x <= 2^40 instead of 2^53
    function check_c1d_barrettLazyBoundNarrow(uint256 x) public pure {
        if (x > (1 << 40)) return;
        assert(kLazyBarrett(x) < 2 * Q);
    }

    /// witness-assisted version of the tight bound over the FULL domain.
    /// [WITNESS] (qh, s) is the Euclidean division of x*MU33 by 2^33; the
    /// relation is total and functional, and `prod` is computed with the very
    /// same MUL the kernel uses, so `kQhat(x) == qh` is asserted (not assumed).
    function check_c1e_barrettLazyBoundWitness(uint256 x, uint256 qh, uint256 s) public pure {
        if (x > INV_MAX) return;
        if (s >= (1 << 33)) return;
        // qh < 2^31 is PROVEN for the true quotient by check_c1b above; without
        // it `qh << 33` may wrap and admit spurious witnesses per x.
        if (qh >= (1 << 31)) return;
        uint256 prod;
        assembly {
            prod := mul(x, MU33) // < 2^64: cannot wrap
        }
        if (prod != (qh << 33) + s) return; // [WITNESS] (unique, given qh < 2^31)
        assert(kQhat(x) == qh);
        // the algebraic identity that linearises step 1's bound:
        //   (x - qh*Q) << 33 == x*d33 + Q*s   with d33 = 2^33 - MU33*Q = 7167
        uint256 lhs;
        uint256 rhs;
        assembly {
            lhs := shl(33, sub(x, mul(qh, Q)))
            rhs := add(mul(x, 7167), mul(Q, s))
        }
        assert(lhs == rhs);
        // numeric bound from x <= INV_MAX, s < 2^33: step 1 lands below 2^33
        assert(rhs < 7508854655 * (1 << 33));
        uint256 x1 = kBarrettStep1(x);
        assert(x1 <= 7508854654);
        // step 2 is then pure 33-bit arithmetic: with x1 = k*2^23 + t,
        // r == (2^23 - Q)*k + t == 8191*k + t, k <= 895, t < 2^23, so
        // r <= 8191*895 + 2^23 - 1 == 15719552 < 2q.
        assert(kQhat2(x1) <= 895);
        assert(kLazyBarrett(x) < 2 * Q);
    }

    // -----------------------------------------------------------------------
    // (c) the packed word's MASKED QUOTIENTS carry exactly the four lane
    // quotients — the structural core of lane independence, and the reason the
    // spread/repack pair could be deleted. For a word whose four 64-bit lanes
    // are each <= INV_MAX:
    //   step 1: and(shr(33, mul(t0, MU33)), QHATM31) == the four kQhat's,
    //           each at its own 64-bit offset;
    //   step 2: and(shr(23, .), QHATM31)             == the four kQhat2's.
    // Nothing crosses a lane boundary in either direction.
    // -----------------------------------------------------------------------
    function check_c3_swarQhatMasksLanes(uint256 v0, uint256 v1, uint256 v2, uint256 v3) public pure {
        if (v0 > INV_MAX || v1 > INV_MAX || v2 > INV_MAX || v3 > INV_MAX) return;
        uint256 t0 = v0 | (v1 << 64) | (v2 << 128) | (v3 << 192);
        uint256 qs;
        assembly {
            qs := and(shr(33, mul(t0, MU33)), QHATM31)
        }
        assert(qs == (kQhat(v0) | (kQhat(v1) << 64) | (kQhat(v2) << 128) | (kQhat(v3) << 192)));

        uint256 y = kSwarStep1(t0);
        assert((y & LANE) == kBarrettStep1(v0));
        assert(((y >> 64) & LANE) == kBarrettStep1(v1));
        assert(((y >> 128) & LANE) == kBarrettStep1(v2));
        assert((y >> 192) == kBarrettStep1(v3));

        uint256 qs2;
        assembly {
            qs2 := and(shr(23, y), QHATM31)
        }
        uint256 want2 = kQhat2(kBarrettStep1(v0)) | (kQhat2(kBarrettStep1(v1)) << 64);
        want2 |= (kQhat2(kBarrettStep1(v2)) << 128) | (kQhat2(kBarrettStep1(v3)) << 192);
        assert(qs2 == want2);
    }

    // -----------------------------------------------------------------------
    // (c) full 4-lane SWAR block: every lane of the output word equals the
    // scalar reduction of the same input lane, and nothing leaks across the
    // 64-bit lane boundaries. This is now a DIRECT statement about the shipped
    // four opcodes — there is no spread step left for it to hide behind — and
    // it additionally pins every output lane under 2q.
    // -----------------------------------------------------------------------
    function check_c4_swarBarrett4(uint256 t0) public pure {
        uint256 l0 = t0 & LANE;
        uint256 l1 = (t0 >> 64) & LANE;
        uint256 l2 = (t0 >> 128) & LANE;
        uint256 l3 = (t0 >> 192) & LANE;
        if (l0 > INV_MAX || l1 > INV_MAX || l2 > INV_MAX || l3 > INV_MAX) return;
        uint256 out = kSwarBarrett4(t0);
        assert((out & LANE) == kLazyBarrett(l0));
        assert(((out >> 64) & LANE) == kLazyBarrett(l1));
        assert(((out >> 128) & LANE) == kLazyBarrett(l2));
        assert((out >> 192) == kLazyBarrett(l3));
        assert((out & LANE) < 2 * Q);
        assert(((out >> 64) & LANE) < 2 * Q);
        assert(((out >> 128) & LANE) < 2 * Q);
        assert((out >> 192) < 2 * Q);
    }

    // -----------------------------------------------------------------------
    // (c) WITNESS-ASSISTED lane independence over the FULL documented bound.
    // The direct forms (c3/c4) time out because the bit-blaster has to bound
    // 2^53 x 2^30 products; supplying the Euclidean division of each lane's
    // product by 2^33 turns the mask/shift argument into pure bit-slicing of a
    // sum of provably non-overlapping terms (0.1 s instead of a timeout).
    //
    // [WITNESS] (qh_i, s_i) with  v_i*MU33 == qh_i*2^33 + s_i,  s_i < 2^33,
    //           qh_i < 2^31. Such a triple exists and is unique for every
    //           v_i <= 128q(q-1): existence/uniqueness of the Euclidean
    //           division is standard, and qh_i < 2^31 is exactly obligation
    //           c1b/c2 (proved for the true quotient by the linear-integer
    //           queries in formal/z3/). That the witness IS the value the
    //           kernel's own SHR produces is ASSERTED below, not assumed.
    // -----------------------------------------------------------------------
    function check_c6_swarQhatMaskWitness(uint256 v0, uint256 v1, uint256 qh0, uint256 s0, uint256 qh1, uint256 s1)
        public
        pure
    {
        if (v0 > INV_MAX || v1 > INV_MAX) return;
        if (s0 >= (1 << 33) || s1 >= (1 << 33)) return;
        if (qh0 >= (1 << 31) || qh1 >= (1 << 31)) return;
        uint256 p0;
        uint256 p1;
        assembly {
            p0 := mul(v0, MU33) // the kernel's own MUL
            p1 := mul(v1, MU33)
        }
        if (p0 != (qh0 << 33) + s0) return; // [WITNESS]
        if (p1 != (qh1 << 33) + s1) return;

        assert(kQhat(v0) == qh0); // the witness is the kernel's quotient
        assert(kQhat(v1) == qh1);

        // two ADJACENT lanes — the hardest case, since 64 bits is the smallest
        // gap any lane pair has in the packed word
        uint256 t0 = v0 | (v1 << 64);
        uint256 r = kSwarBarrett4(t0);
        // the masked quotient word carries exactly the two lane quotients
        uint256 qs;
        assembly {
            qs := and(shr(33, mul(t0, MU33)), QHATM31)
        }
        assert(qs == (qh0 | (qh1 << 64)));
        assert((r & LANE) == kLazyBarrett(v0)); // no leak into lane 0
        assert(((r >> 64) & LANE) == kLazyBarrett(v1)); // no leak out of lane 1
    }

    /// same for the full 4-lane SWAR word: all four lanes are reduced in place
    /// by the same two opcodes pairs, so all four claims are one statement
    function check_c7_swarBarrettWitness(
        uint256 t0,
        uint256 qh0,
        uint256 s0,
        uint256 qh1,
        uint256 s1,
        uint256 qh2,
        uint256 s2,
        uint256 qh3,
        uint256 s3
    ) public pure {
        uint256[4] memory l;
        l[0] = t0 & LANE;
        l[1] = (t0 >> 64) & LANE;
        l[2] = (t0 >> 128) & LANE;
        l[3] = t0 >> 192;
        uint256[4] memory qh = [qh0, qh1, qh2, qh3];
        uint256[4] memory s = [s0, s1, s2, s3];
        for (uint256 i = 0; i < 4; ++i) {
            if (l[i] > INV_MAX) return;
            if (s[i] >= (1 << 33)) return;
            if (qh[i] >= (1 << 31)) return;
            uint256 p;
            assembly {
                p := mul(mload(add(l, mul(0x20, i))), MU33)
            }
            if (p != (qh[i] << 33) + s[i]) return; // [WITNESS]
        }
        uint256 out = kSwarBarrett4(t0);
        assert((out & LANE) == kLazyBarrett(l[0]));
        assert(((out >> 64) & LANE) == kLazyBarrett(l[1]));
        assert(((out >> 128) & LANE) == kLazyBarrett(l[2]));
        assert((out >> 192) == kLazyBarrett(l[3]));
    }

    // -----------------------------------------------------------------------
    // (f) 6-bit w1 packing == FIPS 204 SimpleBitPack layout, and recoverable.
    // -----------------------------------------------------------------------
    function check_f1_pack6(uint256 a0in, uint256 a1in, uint256 a2in, uint256 a3in) public pure {
        uint256 a0 = a0in;
        uint256 a1 = a1in;
        uint256 a2 = a2in;
        uint256 a3 = a3in;
        if (a0 >= MHI || a1 >= MHI || a2 >= MHI || a3 >= MHI) return; // guaranteed by (b)

        (uint256 b0, uint256 b1, uint256 b2) = kPack6(a0, a1, a2, a3);
        (uint256 e0, uint256 e1, uint256 e2) = refW1Pack(a0, a1, a2, a3);
        assert(b0 == e0 && b1 == e1 && b2 == e2);
        assert(b0 < 256 && b1 < 256 && b2 < 256);

        // recoverability from the 24-bit little-endian byte stream
        uint256 s = b0 | (b1 << 8) | (b2 << 16);
        assert((s & 63) == a0);
        assert(((s >> 6) & 63) == a1);
        assert(((s >> 12) & 63) == a2);
        assert(((s >> 18) & 63) == a3);
    }
}

// ===========================================================================
// 4. CANARIES — these MUST report counterexamples.
//
// A "PASS" from a symbolic tool is worthless if the path condition is
// unsatisfiable (vacuous) or if the tool cannot see assertion failures at all.
// Every contract below is expected to FAIL under halmos; a PASS invalidates
// the corresponding proof above. Run them with:
//   halmos --contract FVCanaries --function check_
//
// They are deliberately NOT forge tests, so `forge test` stays green.
// ===========================================================================
contract FVCanaries {
    /// C0: the tool can see assertion violations at all.
    function check_c0_toolDetectsFailures(uint256 vin) public pure {
        uint256 v = vin & 0x3ffff;
        assert(v != 12345); // false for v == 12345
    }

    /// C1: the [PIN] path of check_a1 is satisfiable (non-vacuous).
    function check_c1_vacuity_a1(uint256 vin) public pure {
        uint256 v = vin & 0x3ffff;
        uint256 n = kStrictCenterNum(v);
        uint256 out = kStrictCenter(v);
        if (out != (n < Q ? n : n - Q)) return; // [PIN]
        assert(false); // must be reachable
    }

    /// C2: the [WITNESS]+[PIN] path of check_b1 is satisfiable (non-vacuous).
    function check_c2_vacuity_b1(uint256 rvin, uint256 hin, uint256 r1pre, int256 x) public pure {
        uint256 rv = rvin;
        if (rv >= Q) return;
        uint256 h = hin & 1;
        if (r1pre > MHI) return;
        if (x < -95231 || x > 95232) return;
        if (int256(rv) != int256(r1pre) * int256(ALPHA) + x) return;
        uint256 q0 = kUseHintQ0(rv);
        uint256 pinOk;
        assembly {
            let p := mul(q0, 190464)
            pinOk := and(iszero(gt(p, rv)), lt(sub(rv, p), 190464))
        }
        if (pinOk == 0) return;
        uint256 arg = kUseHintModArg(rv, h);
        uint256 m;
        assembly {
            m := mod(arg, 44)
        }
        if (m != (arg < 44 ? arg : arg - 44)) return;
        assert(false); // must be reachable
    }

    /// C4: the useHint domain precondition r < q is load-bearing: dropping it
    /// must produce a counterexample (found independently at r == q, h == 1:
    /// kernel 1 vs FIPS 43).
    function check_c4_useHintNeedsCanonicalInput(uint256 rvin, uint256 hin, uint256 r1pre, int256 x) public pure {
        uint256 rv = rvin;
        if (rv >= 2 * Q) return; // relaxed domain
        uint256 h = hin & 1;
        if (r1pre > 2 * MHI) return;
        if (x < -95231 || x > 95232) return;
        // witness for the FIPS reference is taken on the CANONICAL value rv % q
        uint256 rp = rv < Q ? rv : rv - Q;
        if (int256(rp) != int256(r1pre) * int256(ALPHA) + x) return;
        uint256 q0 = kUseHintQ0(rv);
        uint256 pinOk;
        assembly {
            let p := mul(q0, 190464)
            pinOk := and(iszero(gt(p, rv)), lt(sub(rv, p), 190464))
        }
        if (pinOk == 0) return;
        uint256 arg = kUseHintModArg(rv, h);
        uint256 m;
        assembly {
            m := mod(arg, 44)
        }
        if (m != (arg < 44 ? arg : arg - 44)) return;
        assert(kUseHint(rv, h) == refUseHintFromWitness(r1pre, x, h)); // must FAIL
    }

    /// C5: the SWAR lane bound is load-bearing: with unconstrained 64-bit lanes
    /// a lane's product x*MU33 leaves its own lane (x >= 17996823486545905
    /// suffices), the 31-bit QHATM31 mask truncates that lane's qhat, and the
    /// lane no longer agrees with the scalar reduction.
    function check_c5_swarNeedsLaneBound(uint256 v0, uint256 v1) public pure {
        uint256 t0 = (v0 & LANE) | ((v1 & LANE) << 64);
        assert((kSwarBarrett4(t0) & LANE) == kLazyBarrett(v0 & LANE)); // must FAIL
    }

    /// C6: step 2 is load-bearing — the coarse step alone does NOT land under
    /// 2q anywhere near the top of the domain (x == INV_MAX already gives
    /// 7508853632 >> 2q).
    function check_c6_step2IsLoadBearing(uint256 x) public pure {
        if (x > INV_MAX) return;
        assert(kBarrettStep1(x) < 2 * Q); // must FAIL
    }
}
