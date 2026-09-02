#!/usr/bin/env python3
# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
"""
Mutation catalogue for the ML-DSA-44 EVM verifier corpus.

Each entry is a *deliberate defect* injected into a security-critical site of
the shipped verifier, a shipped kernel, or one of the reference implementations
the differential tests rely on.  A mutant is KILLED if `forge test` fails on it
and SURVIVES if the whole suite still passes.  A surviving mutant is a
concrete, named test gap — not an opinion about coverage.

Design rules for entries (they are what make the number meaningful):
  * `count` is asserted before patching.  If the source moves and the pattern no
    longer occurs exactly `count` times, the run ABORTS instead of silently
    reporting a survivor.  A stale catalogue that "kills nothing" is the classic
    way mutation scores lie.
  * `occ` selects which occurrences to patch: None = all of them, or a 0-based
    index list.  Single-occurrence mutants are the strong form: they ask whether
    the suite catches a defect in ONE check site out of many, which is what a
    real bug looks like.
  * `cls` groups mutants by the obligation they attack, so a surviving mutant
    can be mapped back to the property that was supposed to cover it.
  * `equivalent=True` marks a mutant that is provably semantics-preserving.  It
    MUST survive; a "kill" means a test is asserting something it should not
    (e.g. pinning gas or bytecode where it means to pin behaviour).

Subjects (paths relative to the repository/foundry root):
  * the SHIPPED verifier and kernels under src/ — what a deployment would run;
  * the reference verifier and kernels under test/ — the differential oracles;
  * the vendored reference decoder under test/vendor/ — mutating the oracle
    itself must break the differential tests, or they are not differential.
"""
import os, sys

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

# ---------------------------------------------------------------------------
# paths are relative to the repository root (= the foundry root) mirrored into
# the mutation workspace by run_mutation.py
# ---------------------------------------------------------------------------
V = "src/MLDSA44Verifier.sol"            # shipped verifier (FIPS 204 Alg. 3)
SD = "src/Decode.sol"                    # shipped decode/UseHint/SampleInBall/matvec kernels
SN = "src/Ntt.sol"                       # shipped forward NTT
SI = "src/InvNtt.sol"                    # shipped inverse NTT
O = "test/ZZZ_E2ERef.sol"                # reference verifier (differential oracle)
D1 = "test/ZZZ_decode.t.sol"             # reference unpackHFast + decode battery
D2 = "test/ZZZ_decode2.t.sol"            # reference unpackZFast2 / useHintFast2
NV = "test/ZZZ_NttVariants.sol"          # forward NTT variants + Barrett
IN = "test/ZZZ_InvNtt.sol"               # inverse NTT variants
VR = "test/vendor/ZKNOX_dilithium_core.sol"  # vendored reference decoder (oracle)

MUTANTS = [
    # =======================================================================
    # CLASS: NORM — the strict FIPS 204 bound ||z||inf < gamma1 - beta
    # (Alg. 3; the strict window is v in [79, 262065] on the wire encoding).
    # The published implementation-bug class here is an off-by-one that
    # accepts the +/-(gamma1-beta) boundary (see libcrux PR #1347, cited in
    # test/SEC2_Fips204Gates.t.sol).  Both the reference decoders and the
    # shipped unpackZPacked carry the check; each is mutated independently.
    # =======================================================================
    # The reference decoder's quad loop was unrolled by 8 (32 check sites, 32
    # iterations) until the tree moved to via-IR codegen, whose stack scheduler
    # cannot place that many live loads without a memoryguard; it now runs ONE
    # quad per iteration (4 check sites, 256 iterations) and still checks all
    # 1024 coefficients. Site counts below follow the shipped shape.
    dict(id="M11", cls="NORM", file=O, count=4, occ=None,
         old="fail := or(fail, iszero(lt(sub(v, 79), 261987)))",
         new="fail := or(fail, iszero(lt(sub(v, 78), 261989)))",
         desc="reference verifier: strict norm bound relaxed to the loose (off-by-one) window"),
    dict(id="M12", cls="NORM", file=O, count=4, occ=[0],
         old="fail := or(fail, iszero(lt(sub(v, 79), 261987)))",
         new="fail := or(fail, iszero(lt(sub(v, 79), 261988)))",
         desc="reference verifier: norm window widened by 1 at ONE of the 4 check sites "
              "(coefficients == 0 mod 4)"),
    dict(id="M13", cls="NORM", file=O, count=4, occ=None,
         old="fail := or(fail, iszero(lt(sub(v, 79), 261987)))",
         new="fail := or(fail, 0)",
         desc="reference verifier: z norm check REMOVED entirely"),
    # NOTE: the z-decode copy in test/ZZZ_decode2.t.sol (unpackZFast2) carries
    # the LOOSE check on purpose (the boundary acceptance is documented and
    # pinned by test/ZZZ_e2eref.t.sol) and its norm flag is consumed only in
    # agreement and memory-safety checks, never as a rejection surface, so
    # mutants on that check are unkillable by construction and are not in the
    # catalogue.  The NORM obligation is carried by the reference verifier
    # (M11-M13) and the shipped decoder (M40-M42).
    # The shipped decoder no longer evaluates a predicate per coefficient: one
    # `and(add(o, Z_NLO), sub(Z_NHI, o))` checks FOUR coefficients at once, with
    # bit 32 of each 64-bit lane carrying that lane's verdict (Z3 S8b/E4b/E5b).
    # Two consequences for this catalogue.  (1) The window edges are now
    # CONSTANTS, one per edge, so M40/M40b move each edge on its own -- and
    # relaxing a constant relaxes every one of the 1024 coefficients at once,
    # which is the strongest form of the bound-relaxation defect.  (2) per-lane
    # coverage is carried by the REPLICATION of those constants rather than by a
    # repeated expression, so M60/M61 break ONE LANE of one constant: a defect
    # that leaves three quarters of the coefficients correctly checked and is
    # invisible to any test that only probes coefficient 0.
    dict(id="M40", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_NLO = 0x00000000fffe004e00000000fffe004e00000000fffe004e00000000fffe004e;",
         new="uint256 constant Z_NLO = 0x00000000fffe004d00000000fffe004d00000000fffe004d00000000fffe004d;",
         desc="shipped unpackZPacked: LOW window edge relaxed by one in all four lanes "
              "(accepts |z| == gamma1-beta, the published off-by-one)"),
    dict(id="M40b", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_NHI = 0x00000001007de04f00000001007de04f00000001007de04f00000001007de04f;",
         new="uint256 constant Z_NHI = 0x00000001007de04e00000001007de04e00000001007de04e00000001007de04e;",
         desc="shipped unpackZPacked: HIGH window edge relaxed by one in all four lanes "
              "(accepts z == -(gamma1-beta), the other tail of the same off-by-one)"),
    dict(id="M41", cls="NORM", file=SD, count=4, occ=None,
         old="mstore(0, or(mload(0), and(add(o, Z_NLO), sub(Z_NHI, o))))",
         new="mstore(0, or(mload(0), 0))",
         desc="shipped unpackZPacked: norm check REMOVED at every one of the 4 quad sites"),
    dict(id="M42", cls="NORM", file=SD, count=4, occ=[0],
         old="mstore(0, or(mload(0), and(add(o, Z_NLO), sub(Z_NHI, o))))",
         new="mstore(0, or(mload(0), and(add(o, Z_NLO), sub(sub(Z_NHI, 1), o))))",
         desc="shipped unpackZPacked: high edge relaxed by one at ONE check site, LANE 0 only "
              "(a single false-accept for coefficients == 0 mod 16)"),
    dict(id="M60", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_NLO = 0x00000000fffe004e00000000fffe004e00000000fffe004e00000000fffe004e;",
         new="uint256 constant Z_NLO = 0x000000000000000000000000fffe004e00000000fffe004e00000000fffe004e;",
         desc="shipped unpackZPacked: LANE 3 of the low-edge constant zeroed -- every "
              "coefficient == 3 (mod 4) is left completely unchecked"),
    dict(id="M61", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_NHI = 0x00000001007de04f00000001007de04f00000001007de04f00000001007de04f;",
         new="uint256 constant Z_NHI = 0x00000001007de04f00000001007de04f00000001007de04e00000001007de04f;",
         desc="shipped unpackZPacked: LANE 1 of the high-edge constant relaxed by one -- "
              "coefficients == 1 (mod 4) accept the -(gamma1-beta) boundary"),
    dict(id="M62", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_QB32 = 0x00000000ff801fff00000000ff801fff00000000ff801fff00000000ff801fff;",
         new="uint256 constant Z_QB32 = 0x00000000ff801ffe00000000ff801ffe00000000ff801ffe00000000ff801ffe;",
         desc="shipped unpackZPacked: the canonicalisation flag becomes [u > q] instead of "
              "[u >= q], so the z == 0 field is stored as q -- the ZKNox defect of EXPLAINER 10"),
    dict(id="M63", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_M18 = 0x000000000003ffff000000000003ffff000000000003ffff000000000003ffff;",
         new="uint256 constant Z_M18 = 0x000000000003ffff000000000001ffff000000000003ffff000000000003ffff;",
         desc="shipped unpackZPacked: LANE 2 of the field mask narrowed to 17 bits -- every "
              "coefficient == 2 (mod 4) loses the top bit of its 18-bit field"),

    # The three straddling bytes are placed at BOTH of their bit positions by
    # ONE multiply (Z_P2/Z_P4/Z_P6 == 2^s + 2^t).  A constant with one of the
    # two powers missing is still a multiply and still type-checks; it silently
    # drops the low four bits of every field-2 coefficient.  O10's
    # `fused_multiply_is_the_two_terms` enumerates the identity over all 256
    # byte values, and this mutant is the executable half of that claim.
    dict(id="M64", cls="NORM", file=SD, count=1, occ=None,
         old="uint256 constant Z_P4 = 0x10000000000040000000000000000000; // 2^124 + 2^78",
         new="uint256 constant Z_P4 = 0x10000000000000000000000000000000; // 2^124 only",
         desc="shipped unpackZPacked: the fused byte-4 placement loses its 2^78 copy, so "
              "field 1 of every quad loses the low bits byte 4 contributes"),

    # =======================================================================
    # CLASS: HINT_ENC — HintBitUnpack canonicality (FIPS 204 Algorithm 21).
    # This is the signature-malleability class of the RustCrypto ml-dsa
    # "repeated hint" advisory (CVE-2026-24850): if more than one hint
    # encoding decodes to the same hint set, signatures are malleable.  The
    # decoder appears twice — reference (test/) and shipped (src/) — and the
    # suite must catch a defect in EITHER copy, so both are mutated.
    # =======================================================================
    dict(id="M20", cls="HINT_ENC", file=D1, count=1, occ=None,
         old="if (j > kIdx && idx <= uint8(hBytes[j - 1])) return (false, masks, 0);",
         new="if (j > kIdx && idx < uint8(hBytes[j - 1])) return (false, masks, 0);",
         desc="reference decoder: strict index increase weakened to non-decreasing (repeat accepted)"),
    dict(id="M21", cls="HINT_ENC", file=D1, count=1, occ=None,
         old="if (j > kIdx && idx <= uint8(hBytes[j - 1])) return (false, masks, 0);",
         new="if (false) return (false, masks, 0);",
         desc="reference decoder: index monotonicity check REMOVED (permutations accepted)"),
    # NOTE: the FIPS-check battery (test/SEC2_Fips204Gates.t.sol) asserts the
    # SHIPPED decoder, and the differential tests reach the test-side copy in
    # test/ZZZ_decode.t.sol only through the encodings they generate.  The
    # omega-bound and cut-monotonicity checks of the TEST-SIDE copy are not on
    # any rejection surface of the current corpus, so mutants there are
    # unkillable by construction and are not in the catalogue; those checks are
    # mutation-covered on the shipped copy (M44, M45), and the test-side checks
    # that ARE differentially reachable stay covered (M20, M21, M24).
    dict(id="M24", cls="HINT_ENC", file=D1, count=1, occ=None,
         old="            if (uint8(hBytes[j]) != 0) return (false, masks, 0);",
         new="            if (false) return (false, masks, 0);",
         desc="reference decoder: trailing-zero padding check REMOVED (free malleability room)"),
    # The SHIPPED decoder is assembly -- 8,146 gas against 21,001 for the
    # Solidity form: each of its four Algorithm 21 checks is one Yul
    # assignment, and each is mutated on its own line.  The strict-increase
    # check is `bad |= idx < prevP` with prevP = previous index + 1 (0 at a row
    # start), so weakening `<=` to `<` on the ORIGINAL is exactly seeding prevP
    # with the index instead of index+1 here -- the same defect, expressed in
    # the shape the shipped assembly uses.
    dict(id="M43", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="prevP := add(idx, 1)",
         new="prevP := idx",
         desc="shipped unpackHFast: strict index increase weakened to non-decreasing"),
    dict(id="M44", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="bad := or(bad, gt(c3, 80))",
         new="bad := or(bad, 0)",
         desc="shipped unpackHFast: weight <= omega bound REMOVED"),
    dict(id="M45", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="bad := or(bad, or(or(gt(c0, c1), gt(c1, c2)), gt(c2, c3)))",
         new="bad := or(bad, 0)",
         desc="shipped unpackHFast: non-decreasing cut positions REMOVED"),
    dict(id="M46", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="bad := or(bad, iszero(iszero(pad)))",
         new="bad := or(bad, 0)",
         desc="shipped unpackHFast: trailing-zero padding check REMOVED"),
    # -----------------------------------------------------------------------
    # THE PADDING CHECK'S SHIFT ARITHMETIC.
    # M43-M46 mutate `prevP`, the omega bound, the counter monotonicity and
    # DELETE the padding check wholesale.  None of them touches the arithmetic
    # that decides WHICH bytes the padding check covers -- and that arithmetic is
    # the whole content of the check, because it is branchless over three words
    # of 32/32/16 index bytes:
    #     s1 := mul(gt(c3, 32), sub(c3, 32))     s2 := mul(gt(c3, 64), sub(c3, 64))
    #     pad := or(or(shl(shl(3,c3), w0), shl(shl(3,s1), w1)), shl(shl(3,s2), w2))
    # Changing ONE token of that arithmetic yields a SECOND distinct valid
    # 2,420-byte signature for one (pk, message) -- a strong-unforgeability
    # break that leaves every test, every obligation, every conjunct and every
    # hypothesis row GREEN.  Each mutant below is a one-token edit of exactly
    # that arithmetic; each is killed by
    # test/SEC3_HintPaddingGrid.t.sol (obligation E15 is the model-side twin).
    # NOTE which perturbations are NOT here: `gt(c3, 64) -> gt(c3, 63)` ALONE is
    # provably EQUIVALENT (the two differ only at c3 = 64, where `sub(c3, 64)`
    # is 0 either way), so it is not a mutant -- the non-equivalent forms move
    # the SUBTRAHEND, or move both, or move the threshold the other way.
    dict(id="M65", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="let s2 := mul(gt(c3, 64), sub(c3, 64))",
         new="let s2 := mul(gt(c3, 63), sub(c3, 63))",
         desc="shipped unpackHFast: the third padding word is shifted one byte too far for "
              "every weight in [64,79], so the FIRST padding byte goes unchecked "
              "(SECOND-PREIMAGE / signature malleability — the demonstrated break)"),
    dict(id="M66", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="let s2 := mul(gt(c3, 64), sub(c3, 64))",
         new="let s2 := mul(gt(c3, 64), sub(c3, 63))",
         desc="shipped unpackHFast: the same hole via the SUBTRAHEND alone, weights [65,79]"),
    dict(id="M67", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="let s2 := mul(gt(c3, 64), sub(c3, 64))",
         new="let s2 := mul(gt(c3, 65), sub(c3, 65))",
         desc="shipped unpackHFast: the third word's threshold moved UP, so a canonical "
              "encoding of weight 65 is falsely REJECTED (the completeness side)"),
    dict(id="M68", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="let s1 := mul(gt(c3, 32), sub(c3, 32))",
         new="let s1 := mul(gt(c3, 32), sub(c3, 31))",
         desc="shipped unpackHFast: the SECOND padding word is shifted one byte too far, "
              "so the first padding byte of every weight in [33,63] goes unchecked"),
    dict(id="M69", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="let s1 := mul(gt(c3, 32), sub(c3, 32))",
         new="let s1 := mul(gt(c3, 33), sub(c3, 33))",
         desc="shipped unpackHFast: the second word's threshold moved UP, so a canonical "
              "encoding of weight 33 is falsely REJECTED"),
    dict(id="M70", cls="HINT_ENC", file=SD, count=1, occ=None,
         old="let w2 := shl(128, mload(add(d, 48)))",
         new="let w2 := shl(128, mload(add(d, 47)))",
         desc="shipped unpackHFast: the third padding word covers index bytes 63..78 "
              "instead of 64..79, so index byte 79 is covered by NO word at all"),

    # =======================================================================
    # CLASS: USEHINT — UseHint + w1Encode (FIPS 204 Algorithms 40 and 28),
    # branchless.  Both the reference per-word kernel (useHintFast2) and the
    # shipped SWAR kernel (useHintSwar) are mutated.
    # =======================================================================
    dict(id="M25", cls="USEHINT", file=D2, count=256, occ=[0],
         old="let c := gt(r0, 95232)",
         new="let c := gt(r0, 95233)",
         desc="reference useHintFast2: decompose threshold off-by-one at ONE site"),
    # PROVABLY EQUIVALENT.  `r1` is only ever fed into
    #   r1 := mod(add(r1, ADJ), 44)
    # and s1 <= 44 always (q0 <= 44, c <= 1, and q0 = 44 forces r0 = 0 hence
    # c = 0).  Since 44 = 0 (mod 44), replacing "s1 unless s1 == 44 then 0" by
    # "s1" cannot change (r1 + ADJ) mod 44.  The correction is therefore DEAD
    # CODE given the unconditional final reduction — a real observation about
    # the kernel, not a test gap.  The test battery pins the q0 = 44 edge case
    # against FIPS 204 anyway (it is the only input at which it is reachable).
    dict(id="M26", cls="USEHINT", file=D2, count=256, occ=None, equivalent=True,
         old="let r1 := mul(s1, iszero(eq(s1, 44)))",
         new="let r1 := s1",
         desc="reference useHintFast2: r1==44 correction REMOVED (dead given the final mod 44)"),
    dict(id="M27", cls="USEHINT", file=D2, count=256, occ=None,
         old="mul(42, or(iszero(r0), c))",
         new="mul(42, iszero(r0))",
         desc="reference useHintFast2: hint direction wrong when r0 is negative"),
    # EQUIVALENT (empirical, but over a COMPLETE differing set).
    # SW_MDIV = 2886404 makes the intermediate Q0 wrong (Q0 = r/D + 1) on
    # exactly 60 of the 8,380,417 values of r — and on none of them does the
    # OUTPUT change: the resulting R0 = -1 makes C = 1, which the S1/R1
    # reduction absorbs.  Swept over all 60 differing r x 4 lane positions x 16
    # hint patterns x 13 critical neighbour lane values (49,920 configurations,
    # 0 mismatches) and re-checked on-chain.  Any obligation that pins the
    # intermediate Q0 is therefore stronger than the pipeline needs — fine, but
    # "Q0 differs" would not by itself mean "the kernel is wrong".  Recorded
    # rather than papered over.
    dict(id="M28", cls="USEHINT", file=SD, count=1, occ=None, equivalent=True,
         old="uint256 constant SW_MDIV = 2886403;",
         new="uint256 constant SW_MDIV = 2886404;",
         desc="shipped useHintSwar: SWAR division constant +1 (self-correcting through C/S1)"),
    dict(id="M47", cls="USEHINT", file=SD, count=1, occ=None,
         old="uint256 constant SW_D = 190464;",
         new="uint256 constant SW_D = 190465;",
         desc="shipped useHintSwar: 2*gamma2 constant wrong (R0 wrong whenever Q0 > 0)"),
    # The mod-44 MAGIC constant.  ceil(2^12/44) = 94 makes (T*M44)>>12 exactly
    # floor(T/44) for every T < 131, and the reachable T is <= 87; at 93 the
    # division is wrong for every reachable T >= 44.  A conjunct that restated
    # 94 in Python would prove nothing about the SHIPPED constant and would
    # leave this mutant green, so C18 EXTRACTS it from the shipped source.
    dict(id="M71", cls="USEHINT", file=SD, count=1, occ=None,
         old="uint256 constant SW_M44 = 94;",
         new="uint256 constant SW_M44 = 93;",
         desc="shipped useHintSwar: the mod-44 magic multiplier off by one, so the single "
              "reduction is wrong for every reachable T >= 44"),
    # the useHint loop is unrolled EIGHT packed words per iteration (one 24-byte
    # output chunk), so the adjustment site now occurs eight times; occ=[0]
    # keeps this the STRONG form (a defect in ONE of the eight unrolled sites
    # must still be caught)
    dict(id="M48", cls="USEHINT", file=SD, count=8, occ=[0],
         old="mul(NEG, 42)",
         new="mul(NEG, 43)",
         desc="shipped useHintSwar: negative-side adjustment becomes 44 == 0 (mod 44), hint ignored"),

    # =======================================================================
    # CLASS: NTT / BARRETT — the TWO-STEP lane-local reduction.  Three things
    # are mutated, because the reduction now has three separable parts and a
    # single constant mutation would leave two of them untested:
    #   (a) the coarse constant MU33 (M29/M30/M49/M50).  An off-by-one
    #       PRESERVES congruence mod q (both steps only ever subtract multiples
    #       of q), so nothing but the lane-bound checks and the end-to-end
    #       vectors can catch it — which is exactly what this class asks.
    #   (b) the SECOND STEP, deleted (M57/M58).  Step 1 alone lands under 2^33,
    #       three orders of magnitude above the < 2q every lane bound assumes;
    #       this is the mutant for the line C16's
    #       `*_every_reduction_has_both_steps` conjunct exists to pin.
    #   (c) the 31-bit-per-lane MASK widened to 32 bits (M59).  The extra bit is
    #       the low bit of the NEXT lane's step-1 remainder, so lane k's
    #       quotient is corrupted by lane k+1 — the exact cross-lane leak the
    #       spread form spends two masks, a shift and a repack to avoid.
    # Both the variant kernels under test/ (used by the reference verifier) and
    # the shipped src/ kernels (used by MLDSA44Verifier) are mutated.
    # =======================================================================
    dict(id="M29", cls="NTT", file=NV, count=1, occ=None,
         old="uint256 constant MU33 = 1025;",
         new="uint256 constant MU33 = 1026;",
         desc="variant forward NTT: coarse Barrett constant off-by-one (+1)"),
    dict(id="M30", cls="NTT", file=IN, count=1, occ=None,
         old="uint256 constant MU33 = 1025;",
         new="uint256 constant MU33 = 1024;",
         desc="variant inverse NTT: coarse Barrett constant off-by-one (-1)"),
    dict(id="M49", cls="NTT", file=SN, count=1, occ=None,
         old="uint256 constant MU33 = 1025;",
         new="uint256 constant MU33 = 1026;",
         desc="shipped forward NTT: coarse Barrett constant off-by-one (+1)"),
    # NOTE: the -1 direction is observable here only because MU33 is COARSE: it
    # leaves step 1 short by ~x/1025 and step 2 exits ~1000x above 2q.  A
    # spread-Barrett reduction masks -1 end-to-end on the shipped inverse — one
    # extra q of under-reduction, inside the lazy slack, erased by the final
    # canonical reduction — so -1 is carried on the variant copy (M30), where
    # the lane-bound micro-tests see it directly under either form; +1
    # underflows a lane either way, so the shipped copies (M49/M50) take it.
    dict(id="M50", cls="NTT", file=SI, count=1, occ=None,
         old="uint256 constant MU33 = 1025;",
         new="uint256 constant MU33 = 1026;",
         desc="shipped inverse NTT: coarse Barrett constant off-by-one (+1)"),
    dict(id="M57", cls="NTT", file=SN, count=24, occ=[0],
         old="t0 := sub(t0, mul(and(shr(23, t0), QHATM31), Q))\n",
         new="",
         desc="shipped forward NTT: the SECOND reduction step deleted from one "
              "fused pass (lanes exit < 2^33 instead of < 2q)"),
    dict(id="M58", cls="NTT", file=SI, count=2, occ=[0],
         old="d0 := sub(d0, mul(and(shr(23, d0), QHATM31), Q))\n",
         new="",
         desc="shipped inverse NTT: the SECOND reduction step deleted from one "
              "fused pass (lanes exit < 2^33 instead of < 2q)"),
    dict(id="M59", cls="NTT", file=SN, count=1, occ=None,
         old="uint256 constant QHATM31 = 0x000000007fffffff000000007fffffff"
             "000000007fffffff000000007fffffff;",
         new="uint256 constant QHATM31 = 0x00000000ffffffff00000000ffffffff"
             "00000000ffffffff00000000ffffffff;",
         desc="shipped forward NTT: quotient mask widened to 32 bits, so each "
              "lane's quotient absorbs the low bit of the NEXT lane's remainder"),

    # =======================================================================
    # CLASS: VERIFIER — the assembled shipped verifier's own checks: sigDecode
    # length (FIPS 204 Alg. 27), the pk data-contract size pin (EXTCODECOPY
    # zero-pads silently, so the exact-size check is load-bearing), mu domain
    # separation (M' = 0x00 || 0x00 || M), the final c-tilde comparison, and
    # the helper content pin (docs/SAFETY.md section 2.3).
    # =======================================================================
    dict(id="M51", cls="VERIFIER", file=V, count=1, occ=None,
         old="if (sig.length != 2420) return false;",
         new="if (sig.length < 2420) return false;",
         desc="shipped verifier: exact signature length relaxed to a lower bound"),
    dict(id="M52", cls="VERIFIER", file=V, count=1, occ=None,
         old="if eq(extcodesize(pkPtr), add(PK_SIZE, 1))",
         new="if iszero(lt(extcodesize(pkPtr), add(PK_SIZE, 1)))",
         desc="shipped verifier: exact pk data-contract size pin relaxed to a lower bound"),
    # M52 mutates the check's SHAPE.  This one mutates the CONSTANT the check
    # compares against, which the shape pin cannot see: the pattern
    # `pat="if eq(extcodesize(pkPtr), add(PK_SIZE, 1))"` matches whatever
    # PK_SIZE happens to be, and C15b's width arithmetic is Python about a
    # number the apparatus takes on faith.  At 20000 the check admits a
    # zero-padded blob (EXTCODECOPY pads silently).
    dict(id="M72", cls="VERIFIER", file=V, count=1, occ=None,
         old="uint256 constant PK_SIZE = 20544;",
         new="uint256 constant PK_SIZE = 20000;",
         desc="shipped verifier: the pk blob width constant shrunk, so the exact-size check "
              "now pins the WRONG size and admits a truncated/zero-padded blob"),
    # The z-decode DRIVER's trip count.  hypotheses.py pins the CALL SITE
    # (`fail |= _unpackZPoly(src + 576 * p, dst);`) and the inner loop's 16
    # iterations, neither of which moves when the driver runs three polynomials
    # instead of four: 256 of the 1024 coefficients are then left undecoded AND
    # un-norm-checked, which is the gap this mutant exists to close.
    dict(id="M73", cls="NORM", file=SD, count=1, occ=None,
         old="for (uint256 p = 0; p < 4; ++p) {",
         new="for (uint256 p = 0; p < 3; ++p) {",
         desc="shipped unpackZPacked: the per-polynomial driver stops one polynomial short, "
              "leaving 256 coefficients undecoded and outside the norm check"),
    dict(id="M53", cls="VERIFIER", file=V, count=1, occ=None,
         old="            extcodecopy(pkPtr, d, 1, 64)",
         new="            extcodecopy(pkPtr, d, 1, 64)\n            mstore8(add(d, 64), 1)",
         desc="shipped verifier: wrong FIPS 204 domain byte in mu (pure vs pre-hashed)"),
    dict(id="M54", cls="VERIFIER", file=V, count=1, occ=None,
         old="return _finalHash(mu, w1) == bytes32(sig[0:32]);",
         new="return _finalHash(mu, w1) == bytes32(sig[0:32]) || bytes32(sig[0:32]) == bytes32(0);",
         desc="shipped verifier: backdoor shape — attacker-supplied all-zero c-tilde accepted"),
    dict(id="M55", cls="VERIFIER", file=V, count=1, occ=None,
         old="if (F1600.codehash != F1600_CODEHASH) revert BadHelper();",
         new="if (false) revert BadHelper();",
         desc="shipped verifier: per-call helper codehash re-check is dead (post-deploy swap unnoticed)"),
    # PROVABLY EQUIVALENT.  unpackHFast already enforces omegaVal <= OMEGA_ on
    # every row and omegaVal >= kIdx, so the returned weight telescopes to the
    # final cut position: weight = kIdx_final <= 80 whenever hOk is true.  The
    # verifier-level `hWeight > 80` branch is therefore unreachable — the omega
    # bound is enforced at decode time, and this mutant documents that.  It
    # MUST survive; a kill would mean a test pins gas or bytecode.
    dict(id="M56", cls="VERIFIER", file=V, count=1, occ=None, equivalent=True,
         old="if (!hOk || hWeight > 80) return false;",
         new="if (!hOk) return false;",
         desc="shipped verifier: hint-weight bound REMOVED (subsumed by unpackHFast's row checks)"),

    # =======================================================================
    # CLASS: REFERENCE — the vendored reference decoder used as the oracle in
    # the differential decode tests.  If mutating the ORACLE does not break
    # anything, the differential tests are not actually differential.
    # =======================================================================
    dict(id="M39", cls="REFERENCE", file=VR, count=1, occ=None,
         old="            if (omegaVal < kIdx || omegaVal > OMEGA) {",
         new="            if (omegaVal < kIdx) {",
         desc="vendored reference decoder: omega bound REMOVED (oracle liveness check)"),

    # =======================================================================
    # CLASS: EQUIVALENT — provably semantics-preserving controls.  These MUST
    # survive.  A kill means some test pins gas or bytecode where it means to
    # pin behaviour, which would make every other kill in this table suspect.
    # =======================================================================
    dict(id="E01", cls="EQUIVALENT", file=SD, count=4, occ=None, equivalent=True,
         old="mstore(0, or(mload(0), and(add(o, Z_NLO), sub(Z_NHI, o))))",
         new="mstore(0, or(mload(0), and(sub(Z_NHI, o), add(o, Z_NLO))))",
         desc="shipped norm check with its two operands swapped (AND is commutative)"),
    dict(id="E02", cls="EQUIVALENT", file=O, count=4, occ=None, equivalent=True,
         old="fail := or(fail, iszero(lt(sub(v, 79), 261987)))",
         new="fail := or(fail, iszero(lt(sub(v, 79), 261987)))  // eq-mutant",
         desc="comment-only change (control: the harness must not kill this)"),
]


def by_class():
    out = {}
    for m in MUTANTS:
        out.setdefault(m["cls"], []).append(m)
    return out


if __name__ == "__main__":
    cls = by_class()
    eq = [m["id"] for m in MUTANTS if m.get("equivalent")]
    print(f"{len(MUTANTS)} mutants in {len(cls)} classes "
          f"({len(MUTANTS) - len(eq)} must be killed, {len(eq)} must survive: {', '.join(eq)})")
    for c, ms in sorted(cls.items()):
        print(f"  {c:<10} {len(ms):>3}   {', '.join(m['id'] for m in ms)}")
