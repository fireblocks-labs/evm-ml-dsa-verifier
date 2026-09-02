#!/usr/bin/env python3
"""
docs/SAFETY.md hypothesis <-> enforcing check <-> evidence, checked mechanically.

    python3 formal/hypotheses.py            # exit 0 iff every row still holds

The security argument (docs/SAFETY.md, docs/FORMAL_VERIFICATION.md) is a
chain of implications whose hypotheses
are things the *implementation* is supposed to enforce ("the verifier MUST
range-check every decoded field", "the VERIFIER constructs M' itself", ...).
Prose cannot check that those hypotheses are actually enforced, that the check
is reachable, or that it is load-bearing.  This table does, in three columns:

  ENFORCED   a literal pattern that must occur in a named source file, with an
             expected occurrence count.  Delete or weaken the check and this
             script fails -- it is a tripwire, not a description.
  LOAD-BEARING  the ID of a mutant in formal/mutation/mutants.py that removes or
             weakens exactly this check.  If that mutant is KILLED, some test
             depends on the check; if it SURVIVES, the check is untested (or,
             as for M26/M28/M56, provably redundant -- which is recorded).
  PROVED     the obligation (Z3 ID, Lean theorem, or halmos obligation) that
             proves the check does what its name says.

A hypothesis with no ENFORCED pattern is listed explicitly as ASSUMED, with the
reason.  Those are the honest residual: assumptions on the environment or on the
registration process, which no on-chain check can discharge.
"""
import ast, fnmatch, hashlib, json, os, re, sys

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, ".."))

VER = "src/MLDSA44Verifier.sol"
DEC = "src/Decode.sol"
REF = "test/ZZZ_E2ERef.sol"
D1 = "test/ZZZ_decode.t.sol"


def raw_text(path):
    """`path`'s text, read through RAW FILE DESCRIPTORS.

    Every read in this apparatus that decides whether something is the
    reviewed artefact goes through `os.open`/`os.read`, precisely so that a
    `builtins.open` shim is not enough to serve forged text to a checker (see
    source_pins.raw_bytes and verify_all.raw_bytes, which duplicate this on
    purpose -- no file may depend on another to read the bytes it is
    verifying).  The reads that decide every ENFORCED verdict in this file go
    through this function, never through `open()`.
    """
    fd = os.open(path, os.O_RDONLY)
    try:
        chunks = []
        while True:
            b = os.read(fd, 1 << 20)
            if not b:
                return b"".join(chunks).decode("utf-8")
            chunks.append(b)
    finally:
        os.close(fd)

ROWS = [
    # ---- §1  setup assumption S1 -----------------------------------------
    dict(sec="§1 S1", hyp="the pk blob is a real, correctly-transformed public key",
         enforced=None,
         assumed="REGISTRATION-TIME. No on-chain check can certify the transform; "
                 "a correctly-sized but bogus blob passes every structural check and "
                 "admits key-free forgery (demonstrated in SEC_pkcache.t.sol). The "
                 "verifier's half is the exact-size check below. The registrar's check "
                 "must be BYTE-FOR-BYTE equality with prepare(pk) on a validated "
                 "1312-byte pk (len(pk) == 1312 EXACTLY, degenerate keys rejected -- "
                 "see docs/SAFETY.md section 3). CANONICAL COEFFICIENTS (< q) ARE A "
                 "SOUNDNESS PRECONDITION, not hygiene. It is FALSE that a "
                 "congruent-but-lifted blob 'accepts exactly what the canonical blob "
                 "accepts', and false that a lifted encoding is 'just a "
                 "de-duplication problem'. "
                 "Coefficient fields are 32-bit and q < 2^32, so lifted encodings "
                 "v + k*q pass every structural check the chain can apply -- but "
                 "MEASURED on the deployed artefact, t1hat[0..255] += 4q, or "
                 "t1hat[0] += 511q, or Ahat[0..255] += 128q each make a VALID signature "
                 "REJECT. Mechanism: the inverse NTT's entry fold "
                 "`sub(add(u0, ACCQ30), u1)` (src/InvNtt.sol) is correct at "
                 "ACCQ30 = q*2^30 and silently WRONG at ACCQ30+1 while still emitting "
                 "canonical-looking lanes, so nothing downstream can notice; the same "
                 "applies to `sub(MV_KQ28REP, c*t1)` past q*2^28. O8's ACC_ENTRY sits "
                 "1.28x below that cliff ONLY because every coefficient is < q, which "
                 "is why C9g/O7/O8/S14 now carry PK_AMAX as an EXPLICIT premise with a "
                 "discrimination control that FAILS at 2q. A lifted blob is therefore "
                 "not a forgery, and not benign either: it is outside every bound this "
                 "apparatus proves. Blob identity is also NOT key identity, so a "
                 "registry must de-duplicate on the canonical 1312-byte pk or on "
                 "tr = SHAKE256(pk, 64), never on the blob, its address or its "
                 "EXTCODEHASH. Also a REGISTRAR obligation: mu = SHAKE256(tr || M', 64) "
                 "is injective in (tr, M') only because |tr| is FIXED at 64 bytes (the "
                 "verifier reads a fixed 64 bytes at a fixed blob offset); any registry "
                 "that hashes a variable-length tr concatenated with anything, without "
                 "a length prefix, is unsound for a fraction of keys.",
         proved="docs/SAFETY.md section 3 validator obligations; "
                "SEC_pkcache.t.sol; C9g.ctl_pk_canonical_premise_rejects_* and "
                "O8.ctl_amax_rejects_* (the domination FAILS at 2q); "
                "O7.lane*_ctl_lane_locality_needs_a_ceiling; "
                "Lean: none (out of scope)"),
    # ---- §1 S1: THE DEGENERACY CHECK, AND WHAT IS NOT ONE --------------------
    # docs/SAFETY.md section 3's mitigation for the documented universal-forgery
    # class must NOT be "lead with proof-of-possession", and the justification
    # "a key-free-forgeable pk has no owner" is backwards.  Such a key has EVERY
    # owner, so PoP -- a signature check -- is satisfied by anyone with no
    # secret material and is PRECISELY VACUOUS on exactly the class it would be
    # named to remove.  A registrar implementing that rule admits the keys the
    # rule exists to exclude, which makes this the one documentation claim in
    # this tree with a direct real-world consequence.  The correct claim is
    # pinned in two pieces, because prose is exactly what is fragile here: the
    # SLOGAN (four placements: the headline, section 2.1, section 3.1 and
    # section 7, so dropping it anywhere fails) and the REASON (one line,
    # section 3.1).
    dict(sec="§1 S1", hyp="proof-of-possession is NOT a degeneracy check, and the "
                          "registration validator must carry an explicit criterion ON "
                          "THE KEY instead",
         file="docs/SAFETY.md",
         pat="Proof-of-possession does not reject degenerate keys",
         count=4,
         mutant="— (a DOCUMENT claim; its executable half is "
                "SEC_pkcache.t.sol::test_proof_of_possession_does_not_reject_a_degenerate_key, "
                "which shows a registrar-chosen challenge answered under a t1 = 0 key "
                "with no secret material, accepted by BOTH verifiers and by the "
                "reference FIPS 204 verifier)",
         proved="SEC_pkcache.t.sol::test_proof_of_possession_does_not_reject_a_degenerate_key "
                "(PoP satisfied) and its centred-lift assertion (the criterion section 3.1 "
                "mandates REFUSES the same key); tools/fixtures/degen.py"),
    dict(sec="§1 S1", hyp="... and the REASON it is not one is stated, not merely the "
                          "conclusion (a key-free-forgeable key has every owner, not none)",
         file="docs/SAFETY.md",
         pat="A key-free-forgeable public key does not have NO owner: it has EVERY owner.",
         count=1,
         mutant="— (a DOCUMENT claim; deleting the sentence and keeping the slogan would "
                "leave a rule with no argument, which is how an inverted version of "
                "the rule escapes notice)",
         proved="SEC_pkcache.t.sol::test_proof_of_possession_does_not_reject_a_degenerate_key; "
                "docs/SAFETY.md sections 2.1 / 3.1 / 7"),
    # ---- NO PROOF ABOUT THE SECRET KEY IS A DEGENERACY CHECK EITHER ----------
    # "A proof of knowledge of (s1, s2)" is no substitute for the criterion
    # above, and it is not THE COMPLETE ANSWER either: the one object it
    # demands -- a norm-conforming secret key -- is one a degenerate key HAS,
    # and it is PUBLIC, so such a proof is vacuous for the same reason one
    # level up.  Both flagship members of the class carry an exact,
    # norm-conforming ML-DSA secret key that is a function of the public key:
    #     t1 = 0    everywhere  <-  (s1, s2, t0) = ( 0,  0, 0)
    #     t1 = 1023 everywhere  <-  (s1, s2, t0) = ( 0, -1, 0)
    # since Power2Round(0,13) = (0,0) and 1023 * 2^13 == q - 1 EXACTLY, so
    # Power2Round(q-1,13) = (1023,0) with ||s2||inf = 1 <= eta = 2.  They are
    # not formal curiosities: the reference FIPS 204 SIGNER produces signatures
    # with them that both on-chain subjects accept.
    #
    # Degeneracy guidance in prose is the most error-prone claim this document
    # carries, so it is pinned in FIVE pieces -- the
    # slogan (4 placements), the reason, the witness that is not obvious, the
    # completeness statement, and the EXTCODEHASH binding.  These rows are
    # what stops a rewrite for readability quietly reverting any of it, and
    # they are load-bearing for exactly that reason.
    dict(sec="§1 S1", hyp="... and NO proof about the secret key is one either: the "
                          "degenerate class has publicly computable, norm-conforming "
                          "witnesses, so a proof of knowledge of (s1, s2) is answered "
                          "with no secret material",
         file="docs/SAFETY.md",
         pat="No proof about the secret key rejects degenerate keys",
         count=4,
         mutant="— (a DOCUMENT claim; its executable half is "
                "SEC_pkcache.t.sol::test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key, "
                "which builds the FIPS 204 secret key from the PUBLIC witness, signs a "
                "registrar-chosen challenge with the reference signer, and has the result "
                "accepted by the reference FIPS 204 verifier and BOTH subjects)",
         proved="SEC_pkcache.t.sol::test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key "
                "(both witnesses sign; norms inside eta; the exact key relation re-derived "
                "independently over all 1,024 coefficients); tools/fixtures/degen2.py"),
    dict(sec="§1 S1", hyp="... and the REASON that one is not a check is stated too (a "
                          "key-free-forgeable key does not LACK a secret key)",
         file="docs/SAFETY.md",
         pat="A key-free-forgeable public key does not lack a secret key: it has one that anyone",
         count=1,
         mutant="— (a DOCUMENT claim; keeping the slogan while losing its argument is "
                "how a bullet claiming to be 'the complete answer' gets written)",
         proved="SEC_pkcache.t.sol::test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key"),
    dict(sec="§1 S1", hyp="... and the non-obvious witness is written out, so a reader can "
                          "check the claim with a pencil rather than by running anything",
         file="docs/SAFETY.md", pat="(s1, s2, t0) = ( 0, -1, 0)", count=1,
         mutant="— (a DOCUMENT claim; the t1 = 1023 witness is the one that is not "
                "obvious, and it exists only because 1023 * 2^13 == q - 1 EXACTLY)",
         proved="SEC_pkcache.t.sol::test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key "
                "(the t1 = 1023 case: ||s2||inf = 1 <= eta, relation holds, and it signs); "
                "SEC_pkcache.t.sol::test_maximal_t1_key_is_key_free_forgeable"),
    dict(sec="§1 S1", hyp="section 3.1 says PLAINLY that it contains no complete "
                          "degeneracy check other than the KeyGen-seed binding",
         file="docs/SAFETY.md",
         pat="Only one check in this section rejects every degenerate key: the KeyGen-seed",
         count=1,
         mutant="— (a DOCUMENT claim; both wrong versions of this bullet were wrong by "
                "claiming COMPLETENESS for a check that did not have it, so the "
                "completeness statement is pinned separately from the checks)",
         proved="docs/SAFETY.md section 3.1 (the centred-lift criterion is stated as a "
                "floor; the KeyGen-seed binding is the only complete check, with its "
                "operational cost -- the registrant must retain xi -- stated)"),
    dict(sec="§1 S1", hyp="the registrar must BIND the validated blob by EXTCODEHASH and "
                          "re-check it at use (the metamorphic hazard section 2.3 closes "
                          "for the Keccak helper)",
         file="docs/SAFETY.md",
         pat="Bind the validated blob by `EXTCODEHASH`, and re-check the binding at every use.",
         count=1,
         mutant="— (a DOCUMENT claim; were section 3's ONLY mention of EXTCODEHASH the "
                "negative one -- 'never de-duplicate on EXTCODEHASH' -- it would steer "
                "a reader away from the correct use)",
         proved="SEC_helper.t.sol::test_metamorphic_substitution_is_caught_even_if_functionally_correct "
                "(the same hazard, closed for the helper); docs/SAFETY.md sections 2.3 / 3.1 "
                "(EIP-6780 closes the classic CREATE2 route on post-Cancun chains only)"),
    dict(sec="§1 S1", hyp="the pk blob address really holds a 20,545-byte data contract "
                          "(0x00 prefix + 20,544-byte payload), read from code offset 1",
         file=VER, pat="if eq(extcodesize(pkPtr), add(PK_SIZE, 1))", count=1,
         mutant="M52 KILLED (the check relaxed to a lower bound); "
                "SEC_pkcache.t.sol (codeless / truncated / oversized / precompile)",
         proved="C15b (width); C18.ver_pk_size_gate_is_exact; SEC_pkcache.t.sol"),
    # ... and the CONSTANT the check compares against.  The row above matches
    # the check's EXPRESSION TEXT, which does not move when PK_SIZE does, and
    # C15b derives `64 + 4*256*4 + 16*256*4 == 20544` in Python without ever
    # reading the Solidity.  So `PK_SIZE = 20000` alone would leave this file
    # at "45 enforced, 0 BROKEN" while the shipped verifier accepted
    # zero-padded blobs.  A PIN OVER EXPRESSION TEXT IS NOT A PIN OVER THE
    # CONSTANT VALUE, which is why the row below pins the value itself.
    dict(sec="§1 S1", hyp="... and the width that check pins is exactly the 20,544-byte "
                          "payload C15b's arithmetic derives (tr | t1hat | Ahat)",
         file=VER, pat="uint256 constant PK_SIZE = 20544;", count=1,
         mutant="M72 KILLED",
         proved="C15b.shipped_PK_SIZE_is_this_width (the width is compared against the "
                "value EXTRACTED from this line); C18.ver_PK_SIZE_is_the_C15b_blob_width, "
                "C18.ver_pk_size_gate_constant_is_the_proved_width; SEC_pkcache.t.sol"),
    dict(sec="§1 S1", hyp="the reference verifier enforces the same exact-size check "
                          "on its raw 20,544-byte blob",
         file=REF, pat="if eq(extcodesize(pkPtr), E2E_PK_SIZE)", count=1,
         mutant="SEC_pkcache.t.sol",
         proved="C15b (width); SEC_pkcache.t.sol"),
    dict(sec="§1", hyp="the Keccak-f[1600] helper is bound by CODE HASH -- at "
                       "construction AND on every verify() call",
         file=VER, pat="!= F1600_CODEHASH) revert BadHelper();", count=2,
         mutant="SEC_helper.t.sol (hostile / codeless / metamorphic helper)",
         proved="SEC_helper.t.sol; docs/SAFETY.md section 2.3 (a hostile permutation "
                "helper yields acceptance of a never-signed message)"),

    # ---- §2 step 1  sigma decoding ----------------------------------------
    dict(sec="§2.1", hyp="HintBitUnpack: indices strictly increasing per row",
         file=D1, pat="if (j > kIdx && idx <= uint8(hBytes[j - 1])) return (false, masks, 0);",
         count=1, mutant="M20, M21 KILLED",
         proved="E12/E13 (complete scaled enumeration); "
                "Lean Encoding.strictInc_rejects_repeat / _permutation"),
    # This row's evidence column cites NO mutant, and that is correct: the
    # check below is one formal/mutation/mutants.py itself documents as
    # "unkillable by construction", because the omega and cut-monotonicity
    # checks of the TEST-SIDE decoder are on no rejection surface of the
    # corpus.  A citation to a mutant that was never written reads exactly
    # like a citation to one that passes, so nothing here may cite an ID the
    # catalogues do not define; `main()` checks every mutant ID cited in this
    # file against the catalogues for exactly that reason.
    dict(sec="§2.1", hyp="HintBitUnpack: cut positions non-decreasing AND weight <= omega",
         file=D1, pat="if (omegaVal < kIdx || omegaVal > OMEGA_) return (false, masks, 0);",
         count=1,
         mutant="— (TEST-SIDE check, unkillable by construction: it is on no rejection "
                "surface of the corpus, see mutants.py's note above M24. The SHIPPED "
                "copy's two checks are mutation-covered by M44 and M45)",
         proved="E12/E13; Lean Encoding.hint_weight_le_omega"),
    dict(sec="§2.1", hyp="HintBitUnpack: trailing index bytes are zero",
         file=D1, pat="            if (uint8(hBytes[j]) != 0) return (false, masks, 0);",
         count=1, mutant="M24 KILLED",
         proved="E12/E13; Lean Encoding.padding_gate_rejects_nonzero"),
    # The SHIPPED decoder is assembly (8,146 gas against 21,001 for the
    # Solidity form), so its four Algorithm 21 checks are four Yul assignments
    # rather than one Solidity `if`.  Each is pinned SEPARATELY, and each has
    # its own mutant (M43-M46): one row per check is strictly more tripwire than
    # a single row covering all four would be.
    dict(sec="§2.1", hyp="the SHIPPED verifier enforces the same HintBitUnpack checks "
                         "(src/Decode.sol unpackHFast): indices strictly increasing "
                         "inside one polynomial",
         file=DEC, pat="bad := or(bad, lt(idx, prevP))",
         count=1, mutant="M43 KILLED; MUT_Gaps / SEC2_Fips204Gates coverage",
         proved="E12/E13; Lean Encoding.hint_decode_canonical"),
    dict(sec="§2.1", hyp="... and the shipped decoder's strict-increase comparison RESETS "
                         "at each polynomial boundary (prevP = previous index + 1, seeded "
                         "to 0 per row, so index 0 stays legal and `First <- Index` holds)",
         file=DEC, pat="prevP := add(idx, 1)",
         count=1, mutant="M43 KILLED (prevP := idx accepts a repeated index)",
         proved="E12/E13; SEC2_Fips204Gates.test_strict_increase_resets_per_polynomial"),
    dict(sec="§2.1", hyp="... and the shipped decoder rejects cut counters that run backwards",
         file=DEC, pat="bad := or(bad, or(or(gt(c0, c1), gt(c1, c2)), gt(c2, c3)))",
         count=1, mutant="M45 KILLED",
         proved="E12/E13; Lean Encoding.hint_weight_le_omega"),
    dict(sec="§2.1", hyp="... and rejects any cut counter above omega = 80 (with the "
                         "counters non-decreasing, bounding the LAST one bounds all four, "
                         "and the accepted weight is exactly y[83])",
         file=DEC, pat="bad := or(bad, gt(c3, 80))",
         count=1, mutant="M44 KILLED",
         proved="E12/E13; Lean Encoding.hint_weight_le_omega"),
    dict(sec="§2.1", hyp="... and rejects a nonzero byte anywhere in the unused index "
                         "padding (branchless: the index bytes shifted left by 8*y[83])",
         file=DEC, pat="bad := or(bad, iszero(iszero(pad)))",
         count=1, mutant="M46 KILLED",
         proved="E12/E13; Lean Encoding.padding_gate_rejects_nonzero"),
    # THE PADDING CHECK'S SHIFT ARITHMETIC.  The row above pins that the check's
    # VERDICT is consumed; it says nothing about WHICH bytes the check covers,
    # and that is the whole content of a branchless padding check over three
    # words of 32/32/16 index bytes.  Changing `sub(c3, 64)` to `sub(c3, 63)`
    # -- one token, none of M43-M46 near it -- yields a SECOND distinct valid
    # 2,420-byte signature for one (pk, message): every hint weight in
    # [64, 79] loses the check on its first padding byte, and every test,
    # obligation, conjunct and hypothesis row in this tree stays green.  Each
    # of the three numbers is therefore pinned WITH BOTH ITS OPERANDS,
    # because it is the AGREEMENT between the threshold and the
    # subtrahend that makes the shift cover exactly the padding, and neither
    # operand alone says which bytes are covered.
    dict(sec="§2.1", hyp="... and the padding check's SECOND word is shifted by exactly "
                         "the number of used bytes it holds (threshold and subtrahend "
                         "are both the w1 boundary, 32)",
         file=DEC, pat="let s1 := mul(gt(c3, 32), sub(c3, 32))",
         count=1, mutant="M68, M69 KILLED",
         proved="E15 (complete weight x dirty-position grid, parameters extracted from "
                "this line); C18.dec_h_pad_s1_threshold_is_the_w1_boundary; "
                "SEC3_HintPaddingGrid.t.sol on chain"),
    dict(sec="§2.1", hyp="... and the THIRD word likewise at the w2 boundary, 64 -- the "
                         "branch no test, mutant or obligation reached before",
         file=DEC, pat="let s2 := mul(gt(c3, 64), sub(c3, 64))",
         count=1, mutant="M65, M66, M67 KILLED",
         proved="E15; C18.dec_h_pad_s2_threshold_is_the_w2_boundary; "
                "SEC3_HintPaddingGrid.t.sol"),
    dict(sec="§2.1", hyp="... and that third word really holds index bytes 64..79 (the "
                         "load is at d+48 and the shift lifts them to the top 16 bytes, "
                         "so byte 79 is covered by SOME word)",
         file=DEC, pat="let w2 := shl(128, mload(add(d, 48)))",
         count=1, mutant="M70 KILLED",
         proved="E15; C18.dec_h_pad_w2_covers_index_bytes_64_79; "
                "SEC3_HintPaddingGrid.t.sol"),
    # A SITE COUNT alone never covered "every coefficient is checked": it pins how
    # many check sites the unrolled loop body has and says nothing about how many
    # times that body runs.  A mutant that halved the trip count would have left
    # both site counts intact.  Each decoder therefore now pins BOTH factors, and
    # their product must be the 1024 coefficients of z.
    dict(sec="§2.1", hyp="||z||inf < gamma1 - beta  (STRICT FIPS bound), reference verifier",
         file=REF, pat="fail := or(fail, iszero(lt(sub(v, 79), 261987)))", count=4,
         mutant="M11, M12, M13 KILLED",
         proved="S8, E4, E5; halmos FVKernels check_a2_normTestStrict PASS "
                "(formal/mutation/halmos_fv1.json)"),
    dict(sec="§2.1", hyp="... and the reference decoder's quad loop runs 256 times, so its "
                         "4 check sites cover all 1024 coefficients",
         file=REF, pat="for { let blk := 0 } lt(blk, 256) { blk := add(blk, 1) }", count=1,
         mutant="M11, M12, M13 KILLED (a shortened loop leaves tail coefficients unchecked)",
         proved="S8, E4, E5; Kernels.t.sol / ZZZ_e2eref.t.sol differential over all 1024 fields"),
    # The shipped decoder checks FOUR coefficients per site: bit 32 of each 64-bit
    # lane of `and(add(o, Z_NLO), sub(Z_NHI, o))` is that lane's verdict.  So the
    # product that must come to 1024 has THREE factors now (sites x iterations x
    # lanes), and the third one lives in the REPLICATION of the two window
    # constants -- which is why each constant is pinned in full below.  A pin on
    # the check expression alone would have been satisfied by a constant with one
    # lane blanked, i.e. by 256 unchecked coefficients (mutant M60).
    dict(sec="§2.1", hyp="||z||inf < gamma1 - beta  (STRICT FIPS bound), shipped verifier",
         file=DEC, pat="mstore(0, or(mload(0), and(add(o, Z_NLO), sub(Z_NHI, o))))", count=4,
         mutant="M40, M40b, M41, M42, M60, M61 KILLED; Kernels.t.sol differential vs "
                "unpackZStrict; SEC2_Fips204Gates boundary sweep",
         proved="S8b (four lanes, EVM semantics), E4b (all 2^18), E5b (both boundaries); "
                "predicate provably the reference decoder's, which still carries the "
                "per-coefficient form"),
    dict(sec="§2.1", hyp="... and the LOW window edge is the same constant in all four "
                         "lanes (2^32 - (gamma1-beta), so bit 32 of o + Z_NLO is "
                         "[|z| >= gamma1-beta] on the near side)",
         file=DEC,
         pat="uint256 constant Z_NLO = "
             "0x00000000fffe004e00000000fffe004e00000000fffe004e00000000fffe004e;",
         count=1, mutant="M40, M60 KILLED (M60 blanks LANE 3 of exactly this constant)",
         proved="S8b.lane{0,1,2,3}_low_edge_iff_o_ge_bound; E4b; E5b"),
    dict(sec="§2.1", hyp="... and the HIGH window edge likewise (2^32 + q - (gamma1-beta), "
                         "so bit 32 of Z_NHI - o is the far side of the same bound)",
         file=DEC,
         pat="uint256 constant Z_NHI = "
             "0x00000001007de04f00000001007de04f00000001007de04f00000001007de04f;",
         count=1, mutant="M40b, M42, M61 KILLED (M61 relaxes LANE 1 of exactly this constant)",
         proved="S8b.lane{0,1,2,3}_high_edge_iff_o_le_bound; E4b; E5b"),
    dict(sec="§2.1", hyp="... and the verdict bits are actually READ: the accumulated word "
                         "is masked with bit 32 of every lane",
         file=DEC, pat="fail := and(mload(0), Z_BIT32)", count=1,
         mutant="M41 KILLED (a check whose verdict is never read is not a check)",
         proved="S8b.lane{k}_low/high_edge_mask_exposes_the_flag"),
    dict(sec="§2.1", hyp="... and the stored coefficient is CANONICAL (one conditional "
                         "subtraction of q, taken at u >= q so that the z = 0 field "
                         "becomes 0 and not q)",
         file=DEC,
         pat="let o := sub(u, mul(shr(32, and(add(u, Z_QB32), Z_BIT32)), MLDSA_Q))",
         count=4, mutant="M62 KILLED (the flag taken strictly stores q for z = 0)",
         proved="S8b.lane{k}_o_canonical / _o_is_the_centered_map; E3b (all 2^18); O9"),
    dict(sec="§2.1", hyp="... and the shipped decoder's 4-quad body runs 16 times per "
                         "polynomial, so its 4 check sites x 16 iterations x 4 lanes cover "
                         "all 256 coefficients of one",
         file=DEC, pat="for { let b := 0 } lt(b, 16) { b := add(b, 1) }", count=1,
         mutant="M40, M41, M42 KILLED (a shortened loop leaves tail coefficients unchecked)",
         proved="S8b, E4b, E5b; Kernels.t.sol differential vs unpackZStrict over all 1024 fields"),
    # The three bytes that straddle two 18-bit fields are placed at BOTH of their
    # positions by one multiply each. The identity b*(2^s + 2^t) == (b<<s)|(b<<t)
    # holds because the shifts are 46 apart and b < 2^8, so it is the SAME twelve
    # disjoint terms O10 models -- but only if the constants really are those two
    # powers, which is why each is pinned in full beside its site count.
    dict(sec="§2.1", hyp="... and byte 2 of each 9-byte group is placed at BOTH bit 16 "
                         "(field 0's top) and bit 62 (field 1's bottom) by one multiply",
         file=DEC, pat="mul(byte(2, w), Z_P2)", count=4,
         mutant="M64 KILLED (a constant that drops one of the two copies)",
         proved="O10.fused_multiply_is_the_two_terms (all 256 byte values), "
                "O10.fused_constants_are_the_two_powers, "
                "O10.mul_pairs_are_the_doubled_terms, O10.coordinate_sweep_exact"),
    dict(sec="§2.1", hyp="... and byte 4 likewise at bits 78 and 124",
         file=DEC, pat="mul(byte(4, w), Z_P4)", count=4,
         mutant="M64 KILLED", proved="O10 (as above)"),
    dict(sec="§2.1", hyp="... and byte 6 likewise at bits 140 and 186",
         file=DEC, pat="mul(byte(6, w), Z_P6)", count=4,
         mutant="M64 KILLED", proved="O10 (as above)"),
    dict(sec="§2.1", hyp="... and the three fused constants are exactly the two powers "
                         "of two their pairs name (2^62+2^16, 2^124+2^78, 2^186+2^140)",
         file=DEC,
         pat="uint256 constant Z_P2 = 0x4000000000010000; // 2^62 + 2^16",
         count=1, mutant="M64 KILLED",
         proved="O10.fused_constants_are_the_two_powers + ctl_fused_const"),
    dict(sec="§2.1", hyp="... (byte 4's constant)",
         file=DEC,
         pat="uint256 constant Z_P4 = 0x10000000000040000000000000000000; // 2^124 + 2^78",
         count=1, mutant="M64 KILLED", proved="O10.fused_constants_are_the_two_powers"),
    dict(sec="§2.1", hyp="... (byte 6's constant)",
         file=DEC,
         pat="uint256 constant Z_P6 = "
             "0x40000000000100000000000000000000000000000000000; // 2^186 + 2^140",
         count=1, mutant="M64 KILLED", proved="O10.fused_constants_are_the_two_powers"),
    # Two z-decode constants that need a pin of their own, because no check
    # expression covers them: Z_UOFF is the centred map's offset and
    # Z_BIT32 is the bit every one of the three comparisons reads.  A wrong lane
    # in either silently stops one coefficient in four from being decoded or
    # checked, exactly as M60/M61 do for the two window edges.
    dict(sec="§2.1", hyp="... and the centred-map offset is q + gamma1 in all four lanes "
                         "(u := Z_UOFF - V, so the decode is FIPS BitUnpack per lane)",
         file=DEC,
         pat="uint256 constant Z_UOFF = "
             "0x000000000081e001000000000081e001000000000081e001000000000081e001;",
         count=1, mutant="— (S8b/O10 model it; C18 extracts its VALUE from this line)",
         proved="S8b.lane{k}_o_is_the_centered_map; E3b (all 2^18); "
                "C18.dec_Z_UOFF_is_q_plus_gamma1_per_lane"),
    dict(sec="§2.1", hyp="... and the flag bit read by the canonicalisation and by BOTH "
                         "window edges is bit 32 of every lane",
         file=DEC,
         pat="uint256 constant Z_BIT32 = "
             "0x0000000100000000000000010000000000000001000000000000000100000000;",
         count=1, mutant="M41 KILLED (the verdict word is masked with exactly this)",
         proved="S8b.lane{k}_low/high_edge_mask_exposes_the_flag; "
                "C18.dec_Z_BIT32_is_the_flag_bit_per_lane"),

    # ---- §2.5  UseHint + w1Encode: the SWAR constants, each pinned ---------
    # Every one of these is reachable from a mutant or an obligation and needs
    # a pin of its own here.  SW_M44 in particular:
    # C17 proves the magic division exact for every reachable T against a 94
    # written in Python, so `SW_M44 = 93` in the shipped file would leave the
    # whole apparatus green while the mod-44 reduction went wrong for T >= 44.
    dict(sec="§2.5", hyp="useHintSwar folds FIPS 204's two reductions into ONE magic "
                         "division, whose multiplier is ceil(2^12/44) = 94",
         file=DEC, pat="uint256 constant SW_M44 = 94;", count=1,
         mutant="M71 KILLED",
         proved="C17 (exact for every reachable T; the subject is now READ from this "
                "line); C18.dec_SW_M44_is_ceil_2p12_over_44; O4 (Z3, T <= 87)"),
    dict(sec="§2.5", hyp="... and the four 6-bit results are gathered by ONE multiply, "
                         "K = 2^174 + 2^116 + 2^58 + 1",
         file=DEC,
         pat="uint256 constant SW_GATHERK = "
             "0x0000000000000000000040000000000000100000000000000400000000000001;",
         count=1, mutant="— (O5 enumerates all 64^4 lane tuples against this K)",
         proved="O5 (complete 16,777,216-tuple sweep); "
                "C18.dec_SW_GATHERK_is_the_four_gather_powers"),
    dict(sec="§2.5", hyp="... and the [r0 > gamma2] comparator is 2^32 - (gamma2+1) per lane",
         file=DEC,
         pat="uint256 constant SW_K32G2 = "
             "0x00000000fffe8bff00000000fffe8bff00000000fffe8bff00000000fffe8bff;",
         count=1, mutant="— (O3/O6 model it; C18 extracts its VALUE from this line)",
         proved="O3.K95233_comparator_iff; O6 (COMPLETE r domain); "
                "C18.dec_SW_K32G2_is_the_gamma2_comparator_per_lane"),
    dict(sec="§2.5", hyp="... and the [r0 != 0] comparator is 2^32 - 1 per lane",
         file=DEC,
         pat="uint256 constant SW_K321 = "
             "0x00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff;",
         count=1, mutant="— (O3/O6 model it; C18 extracts its VALUE from this line)",
         proved="O3.K1_comparator_iff; O6 (COMPLETE r domain); "
                "C18.dec_SW_K321_is_the_nonzero_comparator_per_lane"),
    dict(sec="§2.1", hyp="... and that per-polynomial decode is driven over all 4 "
                         "polynomials of z, each from its own 576-byte encoding slice",
         file=DEC, pat="fail |= _unpackZPoly(src + 576 * p, dst);", count=1,
         mutant="M40, M41, M42 KILLED",
         proved="S8b, E4b, E5b; Kernels.t.sol differential vs unpackZStrict over all 4 rows"),
    # ... and the DRIVER'S TRIP COUNT, which is a different fact from its call
    # site.  The comment above the z rows claims its pinned factors multiply to
    # "the 1024 coefficients of z"; true of the REFERENCE decoder (4 sites x 256
    # iterations), but for the SHIPPED one sites x iterations x lanes reaches
    # 256 -- ONE polynomial.  The missing factor is this driver: `p < 4` ->
    # `p < 3` moves none of the three and leaves 256 of the 1024 coefficients
    # undecoded and un-norm-checked with every check green.  C18 multiplies all four.
    dict(sec="§2.1", hyp="... and that driver runs exactly 4 times, so its 4 check sites "
                         "x 16 iterations x 4 lanes x 4 polynomials cover all 1024 "
                         "coefficients of z",
         file=DEC, pat="for (uint256 p = 0; p < 4; ++p) {", count=1,
         mutant="M73 KILLED (a driver that stops one polynomial short)",
         proved="C18.dec_z_driver_runs_all_4_polynomials, "
                "C18.dec_z_gates_cover_all_1024_coefficients; "
                "Kernels.t.sol differential vs unpackZStrict over all 1024 fields"),

    # ---- §2 step 3  message representative --------------------------------
    dict(sec="§2.3", hyp="the VERIFIER builds M' = 00 || 00 || M itself (pure ML-DSA, "
                         "empty context; the two zero bytes come from zero-initialised "
                         "memory of exactly 66 + |M| bytes)",
         file=VER, pat="bytes memory muIn = new bytes(66 + message.length);", count=1,
         mutant="—",
         proved="E14; Lean Encoding.mprime_injective, Encoding.pure_prehash_disjoint"),
    dict(sec="§2.3", hyp="mu = SHAKE256(tr || M', 64) with tr taken from the bound pk "
                         "blob (fixed 64 bytes at payload offset 0 = code offset 1)",
         file=VER, pat="extcodecopy(pkPtr, d, 1, 64)", count=1,
         mutant="—",
         proved="C15b (blob layout); SHAKE256 ACVP KATs (FUZZ_Shake.t.sol)"),

    # ---- §2 step 7  acceptance --------------------------------------------
    dict(sec="§2.7", hyp="accept iff c~ equals the recomputed digest — no other path",
         file=VER, pat="return _finalHash(mu, w1) == bytes32(sig[0:32]);", count=1,
         mutant="MUT_Gaps magic-value tests",
         proved="FUZZ_MLDSA44 must-reject batteries; ACVP invalid-case corpus"),

    # ---- §4.1  the SHAKE256 sponge's write and read footprints -------------
    # A 160-byte-per-block writer or a 24-byte overread is exactly what these
    # two rows exclude, and each is ONE address, so a single edit is enough to
    # reintroduce either.  They are pinned here so the shipped footprints
    # cannot silently drift: the squeeze's fifth store must land flush with the
    # end of the rate block and the absorb's last load must stay inside it, and
    # both are the reason the shipped sponge is honestly
    # `memory-safe` rather than benignly out of bounds.
    dict(sec="§4.1", hyp="the squeeze writes EXACTLY the 136-byte rate block: its fifth "
                         "store lands flush with the end of the block (outPtr+104 "
                         "carrying lanes 13..16) instead of overhanging it by 24 bytes",
         file="src/FastKeccak170.sol", pat="add(outPtr, 104),", count=1,
         mutant="— (SEC_memsafety.t.sol asserts the shipped spill is EXACTLY 0, not "
                "merely bounded, so the old overhanging form fails that test)",
         proved="SEC_memsafety.test_shake_squeeze_write_footprint_is_bounded "
                "(spill == 0 at outLen 32/64/136/272); FUZZ_Shake.t.sol ACVP KATs"),
    dict(sec="§4.1", hyp="... and the absorb READS exactly the same 136 bytes: lane 16 is "
                         "taken from the word at ptr+104, not ptr+128, so no load reaches "
                         "past the block",
         file="src/FastKeccak170.sol", pat="v := grev(mload(add(ptr, 104)))", count=1,
         mutant="— (a load past the block is invisible to a functional test; this is a "
                "TRIPWIRE on the address, which is the only thing that can be checked "
                "from outside)",
         proved="SEC_memsafety.t.sol (FMP integrity + footprint); the `memory-safe` "
                "annotation on _xorBlockFast170 is only honest with this address"),

    # ---- §5  overflow safety ----------------------------------------------
    dict(sec="§5", hyp="the lane reduction stays inside 0 <= r < 2q -- STEP 1, the "
                       "coarse Barrett whose product fits a 64-bit lane",
         file="test/ZZZ_NttVariants.sol",
         pat="r := sub(x, mul(shr(33, mul(x, MU33)), Q))", count=1,
         mutant="M29, M30, M49, M50 KILLED",
         proved="Lean Barrett.barrett_forward / barrett_inverse (EXACT EVM semantics); "
                "S1-S4, S13, C11a-d, E9a/b; halmos FV2Barrett 13/15 PASS "
                "(w3 and w11b TIMEOUT at 300 s -- NOT proved at the bytecode level; "
                "see formal/mutation/halmos_fv2.json and RESULTS.md). The bound "
                "itself rests on the Lean theorems and the Z3 obligations named "
                "above, which do not depend on the halmos pass"),
    dict(sec="§5", hyp="... and STEP 2, which is LOAD-BEARING: step 1 alone lands under "
                       "2^33, three orders of magnitude above 2q",
         file="test/ZZZ_NttVariants.sol",
         pat="r := sub(r, mul(shr(23, r), Q))", count=1,
         mutant="M57, M58 KILLED (the second step deleted from a shipped kernel)",
         proved="Lean Barrett.step1_alone_is_not_enough / barrettEVM_lt_two_q; "
                "S1/S2 step1_lt_2p33; C16 fwd/inv_every_reduction_has_both_steps "
                "(step-1 and step-2 occurrences must agree region by region); "
                "test/FV3_NttLaneBounds.t.sol testStepOneAloneIsNotEnough"),
    dict(sec="§5", hyp="the packed reduction is LANE-LOCAL: one 31-bit-per-lane mask both "
                       "extracts the quotient and blocks the neighbouring lane, so no lane "
                       "is ever spread to 128-bit spacing",
         file="src/Ntt.sol",
         pat="uint256 constant QHATM31 = 0x000000007fffffff000000007fffffff"
             "000000007fffffff000000007fffffff;", count=1,
         mutant="M59 KILLED (mask widened to 32 bits: lane k picks up lane k+1's low bit)",
         proved="Lean Barrett.swar_lane_independent / lane_product_lt_two_pow_63 "
                "(all four lanes, EXACT EVM semantics); S7 (4 lanes, 60 conjuncts); "
                "C9e/C9h (product < 2^64 and mask width == 64 - 33); "
                "C16 fwd/inv_QHATM31_is_2p31m1_per_lane; "
                "test/FV3_NttLaneBounds.t.sol testFuzzPackedReductionIsFourScalarReductions"),
    # ---- the lazy lane budget the Barrett domain depends on ----------------
    dict(sec="§5", hyp="forward NTT lanes grow by exactly +2q per layer "
                       "(the butterfly stores u+V and u+2q-V, not u+2q+V)",
         file="test/ZZZ_NttVariants.sol",
         pat=", TWOQ4), t0)", count=24,
         mutant="M29, M30 KILLED (the reduction the budget feeds)",
         proved="S5 (the step, 6 conjuncts); C9f (the 8-layer closure); "
                "C16 (TWOQ4 == 2q per lane; _SUM_RE/_DIFF_RE pin the FULL "
                "`sub(add(X, TWOQ4), t0)` form, so the subtraction direction is "
                "pinned too, and require 24 sum stores paired with 24 diff "
                "stores across the two radix-8 fused passes); "
                "C9a/C9b; test/FV3_NttLaneBounds.t.sol"),
    dict(sec="§5", hyp="inverse NTT layer 8 canonicalises with `mod`, NOT with Barrett "
                       "-- this is what keeps the Barrett domain at 128q(q-1)",
         file="test/ZZZ_InvNtt.sol",
         pat="or(shl(128, mod(and(shr(128, t0), LANE), Q)), shl(192, mod(shr(192, t0), Q)))",
         count=4,
         mutant="M29, M30 KILLED (the reduction the budget feeds)",
         proved="S6 (K <= 64 only, product <= 128q(q-1)); S6b (layer 8 lane products "
                "< 2^64); C9g (the closure); C16 (16 mod-canonicalisations in the "
                "L7+L8 block and none elsewhere); C9c/C9d/C11b/C11c"),
    # ---- the profiling markers C16 anchors its regions on ------------------
    # C16 must not slice the inverse transform's layer-8 region on a COMMENT
    # (`inv_body.index("Layers 7+8 fused")`): moving that comment would turn one
    # of its conjuncts into `n == n`.  The regions are instead
    # delimited by these profiling markers, which are CODE.  They are therefore
    # load-bearing for C16 and are pinned here like any other enforcing check.
    dict(sec="§5", hyp="the inverse NTT's layer blocks are delimited by profiling "
                       "markers (the CODE anchors C16 slices its regions on)",
         file="test/ZZZ_InvNtt.sol", pat="mstore(add(PR, 0x60), gas())", count=1,
         mutant="V117 (unreadable source) KILLED; VT01 (predicate -> tautology) KILLED",
         proved="C16.inv_schedule_extracted_is_K_2powL and its five ctl_inv_* "
                "controls; C16.all_shipped_inv_copies_agree"),
    dict(sec="§5", hyp="the forward NTT's layer blocks are delimited by profiling "
                       "markers too, and there are THREE of them (radix-8 L1+L2+L3, "
                       "radix-8 L4+L5+L6, in-word L7+L8), so the last marker is the "
                       "fourth",
         file="test/ZZZ_NttVariants.sol",
         pat="mstore(add(PR, 0x60), gas())\n    }\n    return a;", count=1,
         mutant="V117 (unreadable source) KILLED; VT01 (predicate -> tautology) KILLED",
         proved="C16.fwd_schedule_extracted_is_plus_2q_x8 (n_blocks == 3) and its "
                "ctl_fwd_* controls incl. ctl_fwd_octet_block_is_only_radix4; "
                "C16.all_shipped_fwd_copies_agree; "
                "FV4.testForwardProfilingMarkersDelimitThreeNonEmptyBlocks"),
    dict(sec="§5", hyp="... and the final marker closes the fused L7+L8 block",
         file="test/ZZZ_InvNtt.sol", pat="mstore(add(PR, 0x80), gas())", count=1,
         mutant="V115, V116 KILLED",
         proved="C16.inv_layer8_canonicalises_with_mod (16 mod()s in the LAST "
                "marker-delimited block, counted over comment- and "
                "string-stripped code), C16.inv_layer8_no_extra_mod_elsewhere"),

    # ---- the residual ASSUMPTION behind the rows above ---------------------
    dict(sec="§5", hyp="the NTT LAYER SCHEDULE used by C9f/C9g is the one the bytecode "
                       "executes (8 forward layers of +2q; inverse: mulmod/addmod entry "
                       "fold at L1+L2 against the ACCQ30/ACCQ31 offsets (S14), K = "
                       "2^(L-1) with Barrett at L3..L7 and `mod` at L8). The forward "
                       "runs its eight layers as THREE fused passes and the inverse as "
                       "FOUR; the layer sequence, and therefore every bound, is the "
                       "same in both groupings",
         enforced=None,
         assumed="EXTRACTED FROM SOURCE, NOT DERIVED FROM BYTECODE. What this row "
                 "registers is a residual ASSUMPTION. The gap it names is a DEFECT rather "
                 "than an assumption, and the difference matters -- a defect gets closed, "
                 "and this one is. C16 EXTRACTS the layer schedule rather than trusting a "
                 "hand transcription; but an extraction that reads only the INTERIOR of "
                 "the profiling-marker sequence, and only as a SET of constant names per "
                 "block, leaves a gap -- 'a re-tuning that regrouped layers would not be "
                 "seen'. Three payloads realise that gap, each leaving the extracted shape "
                 "byte-identical and the suite at ALL CHECKS PASS: a ninth, entirely "
                 "unreduced layer appended AFTER the last marker; a payload inserted "
                 "BEFORE the first marker that adds 128q to every input lane (which "
                 "falsifies S6/C9g's 'entered canonical' premise outright); and one lane "
                 "group's `add(u, Q4_16)` DELETED, invisible because three other "
                 "occurrences keep the NAME Q4_16 in the block's set. An assumption that "
                 "an attacker can realise with a one-file, no-trace edit is a defect, so "
                 "the extraction is hardened: the partition is TOTAL (head, blocks, tail; the "
                 "head and the tail must be INERT -- no offset constant, no reduction, "
                 "no mstore/mload/mul), the per-region summary counts OCCURRENCES rather "
                 "than naming a set, every word-aligned layer block must offset every "
                 "butterfly (in the FUSED form now shipped: 2 x offset occurrences "
                 "== layers x stores -- twelve offsets against eight stores in the "
                 "forward's two radix-8 blocks, four against four in the inverse's "
                 "radix-4 blocks), and two "
                 "residual digests -- the "
                 "normalised function body and the whole normalised FILE, all three "
                 "shipped copies of each -- make any change the summary does not model a "
                 "FAILURE rather than a blind spot. All three payloads are re-run "
                 "against both shipped copies and fail on the STRUCTURAL "
                 "conjuncts, not merely on the digests. WHAT IS STILL ASSUMED, and it is "
                 "not small: C16 reads SOURCE TEXT, so the mapping from that pinned text "
                 "to 'eight layers with these K' is still read by a human; and the "
                 "extraction sees which constants a region uses and how often, not the "
                 "DATA FLOW between them. FV4_NttScheduleExtraction.t.sol re-derives the "
                 "lane bounds at EVM semantics for the extracted K sequence and "
                 "FV6_NttRegionCoverage.t.sol executes the shipped transforms to show "
                 "that each of the three payloads really is unsound (entry precondition, "
                 "exit postcondition, EVM underflow of a dropped offset). Neither parses "
                 "Yul; they cover the payloads arithmetically, not the source-to-"
                 "semantics step. FV6 also MEASURES the reason the source-linkage "
                 "obligation is necessary: with the entry fold, a UNIFORM +m*q entry "
                 "lift NEVER changes the transform's output (measured up to +2^38*q; "
                 "the fused block is exactly modular and uniform lifts cancel out of "
                 "every difference), so no functional test can see a head payload; what "
                 "is observable is a SINGLE lane lifted past the ACCQ30 offset, where "
                 "the EVM subtraction wraps out of the residue class.",
         proved="C16 (total region extraction + 17 negative controls, incl. "
                "ctl_*_payload_before_first_marker / _after_last_marker / "
                "_one_offset_dropped_in_a_block / ctl_inv_entry_fold_dropped); "
                "C9f/C9g (5 + 6 negative controls); S14; "
                "FV3_NttLaneBounds.t.sol; FV4_NttScheduleExtraction.t.sol; "
                "FV6_NttRegionCoverage.t.sol; "
                "FORMAL_VERIFICATION.md §5 item 6"),

    # ---- the assumptions the FORMAL APPARATUS ITSELF rests on --------------
    # Registered because any pinning scheme is a bootstrap, and a bootstrap by
    # definition terminates somewhere -- in an assumption rather than in a
    # check.  These three rows ARE where it terminates.
    dict(sec="§FV.1", hyp="the TRUST ANCHOR at the top of formal/z3/verify_all.py is "
                          "the reviewed code (nothing above or inside it has been "
                          "edited)",
         enforced=None,
         assumed="BOOTSTRAP. The anchor digests source_pins.py's CODE against a "
                 "constant it holds, execs the bytes it digested, then digests THIS "
                 "file's whole AST against the pinned `verify_all::@@file` region and "
                 "exits 2 on any mismatch -- all before the first statement of the "
                 "suite runs, so a payload planted lower in the file never executes. "
                 "It cannot certify ITSELF: an attacker who edits the anchor block, or "
                 "inserts statements above it (rebinding `hashlib.sha256`, say), "
                 "subverts it. What the anchor buys is that the surface is a fixed ~90-"
                 "line prefix of ONE file rather than 140 KB across eight, and that a "
                 "silent edit now requires several coordinated ones: verify_all.py's "
                 "anchor constant, source_pins.py's tables, and run_checks.sh check 0, "
                 "which re-derives all anchor digests under an interpreter found OUTSIDE "
                 "this repository before any check runs. Three attacks on that anchor "
                 "(an unpinned module-level slot, an unpinned `def` line, and a "
                 "shadowing .pyc) are each closed; the residue is the anchor itself. "
                 "The 'several coordinated edits' floor holds ONLY while check 0's "
                 "interpreter is not repository-owned: run `\"$PY\" -I -S` with $PY "
                 "defaulting to pythonref/myenv/bin/python -- a path this repository "
                 "owns -- and TWO files (a payload in verify_all.py plus a wrapper "
                 "replacing that symlink) print the ORIGINAL anchor line and ALL "
                 "CHECKS PASS. Check 0 therefore discovers its own interpreter outside "
                 "$ROOT, refuses if it cannot, refuses if $PY's realpath is inside "
                 "$ROOT, and requires the two interpreters' independently computed "
                 "digests to AGREE -- so a lying $PY must contradict the bootstrap "
                 "interpreter, which reports the bytes actually on disk. A SECOND, much "
                 "larger overstatement of that same floor comes from BLANKING. Both anchor "
                 "computations BLANK source_pins.py's two pinned tables before digesting -- "
                 "deliberately, so that regenerating pins cannot move the anchor -- and a "
                 "dict display is EXECUTABLE CODE. ONE line inside `PINS = {...}`, "
                 "`'kernel_obligations::@@file': exec(\"<builtins.open shim>\") or "
                 "'<the real hash>',`, is line-count-neutral (so the LINE-RANGE digest "
                 "does not move) and leaves the table's value byte-identical, and it "
                 "printed `anchor OK` with all digests unchanged and "
                 "ALL CHECKS PASS over a tree with a real defect planted in the shipped "
                 "Ntt.sol: ONE file, ONE line, ZERO hash literals, ZERO anchor movement. "
                 "THE CLASS is `a pinned file must have no region that is both EXECUTABLE "
                 "and EXEMPT from the pin`. It is closed by proving inertness "
                 "before blanking: all three blankers refuse unless each table is a dict "
                 "display whose every key and value is a string CONSTANT, at column 0, "
                 "with nothing else on its first or last line; run_checks.sh's six "
                 "ANCHOR_* lines are held to the same rule; and every read that decides "
                 "whether something is the reviewed artefact goes through os.open/os.read "
                 "rather than builtins.open. THE FLOOR, RESTATED HONESTLY: with no "
                 "control over the process that runs the checks, a silent edit needs "
                 "verify_all.py's two constants, source_pins.py's tables and "
                 "run_checks.sh's six anchors -- three files, and the visible hash "
                 "literals are the two in verify_all.py. WITH control over the driver it "
                 "is cheaper, and that is a separate row: see section FV.6.",
         proved="META-PINS (10 conjuncts, incl. blanked_regions_are_inert_data); "
                "run_checks.sh check 0 (bootstrap interpreter, "
                "5 anchors, two-interpreter agreement); "
                "FORMAL_VERIFICATION.md §2f"),
    dict(sec="§FV.2", hyp="the Python interpreter, its standard library and its "
                          "installed packages (z3-solver) are the ones they claim to be",
         enforced=None,
         assumed="ENVIRONMENT. Every digest in this apparatus is computed by "
                 "`hashlib`, `ast` and `os.walk` from that interpreter; a poisoned "
                 "stdlib, `sitecustomize.py` or `.pth` file defeats all of it, and so "
                 "does a Z3 that answers `unsat` to everything (which is why the "
                 "canary/vacuity controls exist: VT01-VT09 falsify the guards and must "
                 "kill). run_checks.sh check 0 re-derives all anchor digests under "
                 "`python -I -S`, which ignores user site-packages, PYTHON* env vars "
                 "and sitecustomize -- that narrows the surface to the interpreter and "
                 "stdlib themselves, and no further. Note it does so TWICE, "
                 "once under BOOT_PY -- an interpreter whose realpath is outside $ROOT, "
                 "taken from $CHECK0_PY, /usr/bin/python3 or PATH and never from a "
                 "repository path -- and once under $PY, and the two must agree. That "
                 "removes THIS repository from the trusted set; it does not remove the "
                 "machine. BOOT_PY is still an assumption, and a deliberately narrow "
                 "one: it is used only for `ast`, `hashlib` and `os.walk`. Note also "
                 "that `ast.unparse` output is version-dependent (different CPython versions may disagree "
                 "on this tree's anchor, 3.11.15 does not), which is why the two BYTES "
                 "anchors -- computed with `hashlib` and `str.split` alone -- are the "
                 "ones checked on every version and the AST anchors are checked in "
                 "addition on ANCHOR_AST_PYVERS. CI pins the interpreter and the z3 "
                 "version; nothing on chain depends on this. ONE PART OF THIS ROW IS "
                 "realisable the same way as the anchor above: the z3 "
                 "PACKAGE is imported by check 1 from wherever $PY resolves it, and in "
                 "the default configuration that is INSIDE the repository "
                 "(pythonref/myenv/.../site-packages/z3). No digest in "
                 "this apparatus covers it, and check 0 now REPORTS its path and version "
                 "on every run so the exposure is on the record. Three hostile solvers "
                 "were built and run to find where the coverage actually ends: (i) "
                 "`check() -> unsat` unconditionally falsifies every S*.premises_sat and "
                 "S*.claims_discriminate; (ii) a context-sensitive one -- sat to "
                 "premise-only checks, unsat to premises+Not(claim), sat to the "
                 "premise-free probe -- is caught by the BIDIRECTIONAL theory_valid "
                 "staleness check (S11 fails with `stale theory_valid "
                 "entries`) and by kernel_obligations' ctl_*_is_refutable controls (O3, O4, "
                 "O7); (iii) a two-pass shim that records the honest verdicts and "
                 "replays them, flipping only the checks it needs, defeats check 1 "
                 "outright. And (iii) DOES buy a broken CONTRACT. It is FALSE that "
                 "laundering a broken contract needs an edit to verify_all.py which "
                 "check 0 catches -- false twice over, in two independent ways. "
                 "(a) `from z3 import "
                 "...` sits INSIDE a function in verify_all.py, ~1000 lines after "
                 "source_pins is loaded, so a payload in source_pins.py's BLANKED `PINS` "
                 "table intercepts the import: measured, `72 x \"z3 delivered through the "
                 "PINS hook\"`, all checks green. The record-and-replay solver needs no "
                 "repository-owned z3 and no verify_all.py edit at all. (b) C16 and the "
                 "source-pin obligations -- the ENTIRE link from the proofs to the "
                 "shipped artefact -- read files, and the same one-line hook laundered "
                 "them through a `builtins.open` shim with a real defect on disk in "
                 "the shipped Ntt.sol. The hook is removed (see FV.1) and "
                 "routes those reads through os.open/os.read, so a shim must now be "
                 "installed by something other than a pinned file. What remains true: a "
                 "hostile z3 that only lies about solver verdicts is still bounded by the "
                 "bidirectional theory_valid staleness check and the ctl_*_is_refutable "
                 "controls, and closing (iii) properly means an out-of-repository solver, "
                 "which is a deployment property. Check 0 prints the solver's path and "
                 "version on every run.",
         proved="run_checks.sh check 0 (bootstrap interpreter outside $ROOT, "
                "`python -I -S`, two-interpreter agreement); vacuity audit VT01-VT09; "
                "FORMAL_VERIFICATION.md §2f"),
    dict(sec="§FV.3", hyp="no pinned file is swapped between the moment a check reads it "
                          "and the moment the checks finish",
         enforced=None,
         assumed="TIME-OF-CHECK/TIME-OF-USE. The anchor digests the bytes it then "
                 "executes, so for the three z3 modules check and use are the same "
                 "read. For every OTHER file under formal/ the manifest is a read at "
                 "META-PINS time and the check that consumes it is a separate read "
                 "(`check_axioms.py`, `hypotheses.py` run as "
                 "subprocesses of run_checks.sh). META-PINS re-reads source_pins.py at "
                 "report time and fails if it moved under the running process, which "
                 "catches the lazy case but is not a proof of atomicity. Closing this "
                 "properly needs the filesystem to be read-only for the duration; that "
                 "is a deployment property, not a code one.",
         proved="META-PINS.executing_modules_are_the_pinned_bytes; "
                "FORMAL_VERIFICATION.md §2f"),

    # ---- two check mechanisms that are themselves ENFORCED ------------------
    # These are ENFORCED rows over `formal/` rather than over the EVM corpus,
    # because what they cover are CHECKS, not contracts, and a check
    # mechanism that no tripwire covers is how check 0 decays into
    # a claim about flags instead of about provenance.
    dict(sec="§FV.1", root="repo",
         hyp="check 0 re-derives the trust anchor under an interpreter found "
             "OUTSIDE this repository, and refuses if it cannot find one",
         file="formal/run_checks.sh", pat='BOOT_PY="$(find_boot_py || true)"', count=1,
         mutant="— (check mechanism; its absence is demonstrably a 2-file defeat, "
                "written out in run_checks.sh's BOOTSTRAP INTERPRETER header)",
         proved="run_checks.sh check 0 steps (a)-(d); hypotheses §FV.2 (BOOT_PY is "
                "itself an environment assumption)"),
    dict(sec="§FV.1", root="repo",
         hyp="... and refuses if the interpreter the other checks run under "
             "resolves INSIDE the repository",
         file="formal/run_checks.sh", pat='  case "$py_rp" in', count=1,
         mutant="— (check mechanism; a 7-byte symlink here is replaceable by a wrapper)",
         proved="run_checks.sh check 0 step (b); the two-interpreter agreement in "
                "step (d) covers a lying interpreter that is not inside $ROOT"),
    dict(sec="§FV.1", root="repo",
         hyp="... and resolves the $PY PATH, not just sys.executable, so a "
             "repository-owned WRAPPER SCRIPT is caught too",
         file="formal/run_checks.sh", pat='  case "$py_link" in', count=1,
         mutant="— (check mechanism; the wrapper attack it closes: a "
                "two-line `#!/bin/sh; exec <outside python>` at "
                "pythonref/myenv/bin/python keeps sys.executable "
                "OUTSIDE $ROOT and prints `-- trust anchor ...: PASS`)",
         proved="run_checks.sh check 0 step (b2), resolved with BOOT_PY and never "
                "with $PY itself; step (d)'s two-interpreter agreement is the "
                "second, independent catch for the lying-interpreter case"),
    dict(sec="§FV.4", root="repo",
         hyp="check 2 elaborates the Lean development in a directory that HAS no "
             "build cache, so no `.lake` artefact can be replayed",
         file="formal/lean/check_axioms.py",
         pat='tmp = tempfile.mkdtemp(prefix="mldsa-lean-elab-")', count=1,
         mutant="— (check mechanism; a warm-cache replay blesses a zero-byte olean and a "
                "sorryAx olean alike, with the check printing PASS)",
         proved="check_axioms.py step [2] prints the elaboration time and the sha256 "
                "of every source it copied; formal/z3/source_pins.py pins those same "
                "sources and META-PINS checks them"),
    dict(sec="§FV.4", root="repo",
         hyp="... and asserts the sandbox is cache-free before it builds",
         file="formal/lean/check_axioms.py",
         pat='if os.path.exists(os.path.join(tmp, ".lake")):', count=1,
         mutant="— (check mechanism)",
         proved="check_axioms.py run_lake; this is what makes SKIP_REL_DIRS = ('lean/.lake',) "
                "in source_pins.py sound rather than merely convenient"),
    dict(sec="§FV.5", hyp="the Lean toolchain (`lake`, `lean`, and the compiler elan "
                          "selects from lean-toolchain) is the one it claims to be",
         enforced=None,
         assumed="ENVIRONMENT, and the Lean-side twin of §FV.2. Check 2 does not trust "
                 "`formal/lean/.lake` at all -- it discards it and always "
                 "elaborates from source in a throwaway tree, so a forged olean, a "
                 "forged `.trace` log or a deleted cache changes nothing (all three "
                 "were tried against check 2 directly). What it does NOT cover is the "
                 "compiler: `#print axioms` is computed by that binary, `$LAKE` is an "
                 "environment variable, and `lean-toolchain` names a toolchain elan "
                 "resolves and downloads. A compiler that omits `sorryAx` from an axiom "
                 "list defeats check 2 completely, and no in-band check can see it. CI "
                 "pins the elan version and verifies the elan tarball by sha256; the "
                 "toolchain itself is trusted the way any proof assistant's kernel is.",
         proved="check_axioms.py steps [1]-[6] (the static scan is independent of the "
                "compiler and catches every FORBIDDEN token in source, which is the one "
                "cross-check that does not go through it); "
                "FORMAL_VERIFICATION.md §2f"),

    # ---- what BLANKING costs, and who drives the checks ---------------------
    dict(sec="§FV.1", root="repo",
         hyp="what the anchors BLANK before digesting is proved to be inert "
             "data, so no blanked region can be executable",
         file="formal/z3/verify_all.py",
         pat="source_pins.py's BLANKED tables are not inert data", count=1,
         mutant="— (check mechanism; the inert-data attack demonstrates that its absence "
                "is a ONE-FILE, ONE-LINE, ZERO-hash-literal defeat)",
         proved="META-PINS.blanked_regions_are_inert_data; run_checks.sh check 0 "
                "`table_nodes`; source_pins.py `table_problems`; three "
                "independent implementations, all three refusing"),
    dict(sec="§FV.6", root="repo",
         hyp="the check script that drives every check is itself pinned, outside "
             "every blanked region",
         file="formal/z3/verify_all.py", pat="RUN_CHECKS_SH_SHA256 = ", count=1,
         mutant="— (check mechanism; without it the driver is pinned ONLY by one "
                "row of the blanked FILES table: a 2-file, 1-hash-literal, "
                "zero-anchor-movement defeat, reproduced)",
         proved="verify_all.py `_anchor_gate_script` (refuses before the suite "
                "runs); run_checks.sh check 0 `blank_gate_anchors` + "
                "ANCHOR_RUN_CHECKS_SH, re-derived under both interpreters"),
    dict(sec="§FV.6", root="repo",
         hyp="... and the six ANCHOR_* lines it blanks are nothing but "
             "hex/version string assignments",
         file="formal/run_checks.sh",
         pat='if not re.match(r\'^ANCHOR_[A-Z0-9_]+="[0-9a-f. ]*"$\', line):',
         count=1,
         mutant="— (check mechanism)",
         proved="source_pins.blank_gate_script and verify_all._anchor_gate_script "
                "recompute the same rule independently; a payload smuggled into a "
                "blanked ANCHOR_ line is refused by all three"),
    dict(sec="§FV.6",
         hyp="the process that RUNS the checks is not itself hostile",
         enforced=None,
         assumed="DRIVER. Registered separately from FV.1 because the two are truly "
                 "different assumptions, with "
                 "different floors. `formal/run_checks.sh` launches every check, "
                 "including the two `python -I -S` bootstrap kernels of check 0 and "
                 "the `verify_all.py` process of check 1. Whoever can write the "
                 "driver can therefore choose what those processes see. MEASURED, "
                 "with the driver unpinned: replacing check 1's invocation with one that "
                 "injects a `builtins.open` shim, plus ONE hash literal in the "
                 "blanked `FILES` row for run_checks.sh, is a TWO-file defeat that "
                 "prints `anchor OK` verbatim, ALL CHECKS PASS over a "
                 "tree with a real defect in the shipped Ntt.sol. What the driver pin "
                 "buys, exactly: (1) the driver is pinned by RUN_CHECKS_SH_SHA256 in "
                 "verify_all.py, a constant in ordinary code that no blanking exempts, "
                 "so the cheapest driver edit must either move a VISIBLE hash literal "
                 "or grow into a shim that forges the driver's own bytes back to the "
                 "checker; (2) the anchor's reads use os.open/os.read, so a "
                 "`builtins.open` shim is not sufficient; (3) running check 1 ON "
                 "ITS OWN -- `MLDSA_REPO=$PWD python3 formal/z3/verify_all.py`, which "
                 "no driver mediates -- DETECTS a tampered driver, and that is the "
                 "check to run when the driver is what you doubt. What it does NOT "
                 "buy: a driver payload that also patches `os.read` still wins, and "
                 "nothing in-band can change that. Closing it properly means invoking "
                 "the checks from a process this tree did not start, on a checkout it "
                 "did not create, or from a read-only checkout. "
                 "`.github/workflows/ci.yml` does the first two: its `formal` job "
                 "checks the tree out onto a fresh runner, builds the venv and the "
                 "Lean toolchain from the pinned manifests, and runs `run_checks.sh` "
                 "with CHECK0_PY set to the runner's own /usr/bin/python3, so neither "
                 "interpreter nor the launching process comes from the tree. THE "
                 "RESIDUE, stated rather than glossed: that workflow file lives IN "
                 "this repository, so an attacker who can write the tree can write it "
                 "too. It is NOT a workflow 'the tree does not own', and calling it "
                 "one would be false: the tree owns every byte of `.github/`. "
                 "Removing the last step needs an "
                 "organisation-level required workflow or a reusable workflow owned by "
                 "a different repository; this repository has neither.",
         proved="verify_all.py RUN_CHECKS_SH_SHA256 / _anchor_gate_script; "
                "run_checks.sh check 0 rg_bytes under both interpreters; "
                "FORMAL_VERIFICATION.md §2f"),

    # ---- §FV.7  THE CORPUS IS THE SIZE IT SAYS IT IS, ON CHAIN -------------
    # This is the "a claim computed against a truncated sample" class, applied
    # to the fixture corpus.  Shard case counts and
    # corpus digests asserted ONLY inside the Python builders are not enough:
    # `fx_common.serve` short-circuits to `target.read_text()` whenever the
    # cache file exists, so with a warm `test/fixtures/` neither the SHA-256
    # nor the 176/165/120 counts would be checked anywhere, and on chain the
    # only guard would be `assertGt(ran, 0)` in the Wycheproof runner with
    # nothing at all in the ACVP runner.  The shard runners therefore assert
    # the count they expect, exactly as FV2_AcvpKeyGen.t.sol asserts its 5.
    dict(sec="§FV.7", hyp="every Wycheproof shard runs the number of cases it is "
                          "documented to run, asserted ON CHAIN rather than in the "
                          "builder that produced the cache",
         file="test/SEC2_Wycheproof.t.sol",
         pat='assertEq(s.sigs.length, nWant, "shard case count");', count=1,
         mutant="— (a TEST-HARNESS check; a truncated or substituted cache file under a "
                "warm test/fixtures/ ran fewer cases and still passed)",
         proved="tools/fixtures/wycheproof_build.py (176 representable = 4 x 44, plus the "
                "per-flag class shards); test/SEC2_Wycheproof.t.sol call sites carry the "
                "pinned 44/8/35/42/61/44/3/8"),
    dict(sec="§FV.7", hyp="... and every ACVP shard likewise (165 = 28+28+28+27+27+27 "
                          "official cases, 120 = 4 x 30 FIPS204-tr1 cases)",
         file="test/ACVP_MLDSA44.t.sol",
         pat='assertEq(s.sigs.length, nWant, "shard case count");', count=1,
         mutant="— (a TEST-HARNESS check; `_runNamedShard` had no count assertion of any "
                "kind, so a short shard was indistinguishable from a full one)",
         proved="tools/fixtures/acvp_build.py asserts 165 and 120 at BUILD time; the call "
                "sites here assert the per-shard split at RUN time"),
    dict(sec="§FV.7", hyp="test/FV2_Barrett.sol's Barrett kernels really are the shipped "
                          "reductions -- the character-identity its header asserts in a "
                          "COMMENT, and which FORMAL_VERIFICATION.md 5.7 calls Closed",
         file="test/FV_Kernels.t.sol",
         pat="assertEq(fv2LazyBarrett(x), shippedFwdLazyBarrett(x)", count=1,
         mutant="— (a TEST-HARNESS check; FV2_Barrett.sol declared 22 `check_*` and 0 "
                "`test*`, was imported by no test and was under no digest, so `forge "
                "test` compiled it and ran nothing)",
         proved="FV_Kernels.t.sol::testFuzz_FV2_barrett_kernels_are_the_shipped_reductions "
                "(against src/Ntt.sol::lazyBarrett AND src/InvNtt.sol::invLazyBarrett); "
                "C18.fv2_refinement_harness_is_the_pinned_bytes (the residual digest)"),
]


# ---------------------------------------------------------------------------
# THE ROW SET IS AN ASSERTION
# ---------------------------------------------------------------------------
# A check printing `All {len(checks)} numeric claims agree` with no
# expected-name set is not a check: nine deleted claims read as a green
# "All 24".  A COUNTED `n_enf` and `n_asm` with no digest over the file has
# exactly that shape.  Were three ROWS deleted -- the 15,425-byte pk-cache
# size pin, the EXTCODEHASH binding of `pkid`, and the HintBitUnpack
# trailing-zero check -- such a report would print
#     <n> enforced hypotheses checked, <m> explicitly ASSUMED, all present
# and exit 0 -- which is why the row set below is pinned BY VALUE.
#
# `EXPECTED_ROWS` is `"<sec> | <hyp>"` for every row, in order, asserted exactly.
# Regenerate with `--print-rows` ONLY after reviewing the diff; the file is also
# byte-pinned by `FILES` in formal/z3/source_pins.py.
#
# See also `cited_mutant_problems` and `doc_count_problems` below: the ROW SET
# being an assertion is not enough on its own, because nothing in it checks
# what the rows SAY.  Two failure modes live exactly there -- a row
# citing mutants that do not exist, and published counts in the
# documentation drifting from every tool that produces them.
EXPECTED_ROWS = [
    '§1 S1 | the pk blob is a real, correctly-transformed public key',
    '§1 S1 | proof-of-possession is NOT a degeneracy check, and the registration validator must carry an explicit criterion ON THE KEY instead',
    '§1 S1 | ... and the REASON it is not one is stated, not merely the conclusion (a key-free-forgeable key has every owner, not none)',
    '§1 S1 | ... and NO proof about the secret key is one either: the degenerate class has publicly computable, norm-conforming witnesses, so a proof of knowledge of (s1, s2) is answered with no secret material',
    '§1 S1 | ... and the REASON that one is not a check is stated too (a key-free-forgeable key does not LACK a secret key)',
    '§1 S1 | ... and the non-obvious witness is written out, so a reader can check the claim with a pencil rather than by running anything',
    '§1 S1 | section 3.1 says PLAINLY that it contains no complete degeneracy check other than the KeyGen-seed binding',
    '§1 S1 | the registrar must BIND the validated blob by EXTCODEHASH and re-check it at use (the metamorphic hazard section 2.3 closes for the Keccak helper)',
    '§1 S1 | the pk blob address really holds a 20,545-byte data contract (0x00 prefix + 20,544-byte payload), read from code offset 1',
    "§1 S1 | ... and the width that check pins is exactly the 20,544-byte payload C15b's arithmetic derives (tr | t1hat | Ahat)",
    '§1 S1 | the reference verifier enforces the same exact-size check on its raw 20,544-byte blob',
    '§1 | the Keccak-f[1600] helper is bound by CODE HASH -- at construction AND on every verify() call',
    '§2.1 | HintBitUnpack: indices strictly increasing per row',
    '§2.1 | HintBitUnpack: cut positions non-decreasing AND weight <= omega',
    '§2.1 | HintBitUnpack: trailing index bytes are zero',
    '§2.1 | the SHIPPED verifier enforces the same HintBitUnpack checks (src/Decode.sol unpackHFast): indices strictly increasing inside one polynomial',
    "§2.1 | ... and the shipped decoder's strict-increase comparison RESETS at each polynomial boundary (prevP = previous index + 1, seeded to 0 per row, so index 0 stays legal and `First <- Index` holds)",
    '§2.1 | ... and the shipped decoder rejects cut counters that run backwards',
    '§2.1 | ... and rejects any cut counter above omega = 80 (with the counters non-decreasing, bounding the LAST one bounds all four, and the accepted weight is exactly y[83])',
    '§2.1 | ... and rejects a nonzero byte anywhere in the unused index padding (branchless: the index bytes shifted left by 8*y[83])',
    "§2.1 | ... and the padding check's SECOND word is shifted by exactly the number of used bytes it holds (threshold and subtrahend are both the w1 boundary, 32)",
    '§2.1 | ... and the THIRD word likewise at the w2 boundary, 64 -- the branch no test, mutant or obligation reached before',
    '§2.1 | ... and that third word really holds index bytes 64..79 (the load is at d+48 and the shift lifts them to the top 16 bytes, so byte 79 is covered by SOME word)',
    '§2.1 | ||z||inf < gamma1 - beta  (STRICT FIPS bound), reference verifier',
    "§2.1 | ... and the reference decoder's quad loop runs 256 times, so its 4 check sites cover all 1024 coefficients",
    '§2.1 | ||z||inf < gamma1 - beta  (STRICT FIPS bound), shipped verifier',
    '§2.1 | ... and the LOW window edge is the same constant in all four lanes (2^32 - (gamma1-beta), so bit 32 of o + Z_NLO is [|z| >= gamma1-beta] on the near side)',
    '§2.1 | ... and the HIGH window edge likewise (2^32 + q - (gamma1-beta), so bit 32 of Z_NHI - o is the far side of the same bound)',
    '§2.1 | ... and the verdict bits are actually READ: the accumulated word is masked with bit 32 of every lane',
    '§2.1 | ... and the stored coefficient is CANONICAL (one conditional subtraction of q, taken at u >= q so that the z = 0 field becomes 0 and not q)',
    "§2.1 | ... and the shipped decoder's 4-quad body runs 16 times per polynomial, so its 4 check sites x 16 iterations x 4 lanes cover all 256 coefficients of one",
    "§2.1 | ... and byte 2 of each 9-byte group is placed at BOTH bit 16 (field 0's top) and bit 62 (field 1's bottom) by one multiply",
    '§2.1 | ... and byte 4 likewise at bits 78 and 124',
    '§2.1 | ... and byte 6 likewise at bits 140 and 186',
    '§2.1 | ... and the three fused constants are exactly the two powers of two their pairs name (2^62+2^16, 2^124+2^78, 2^186+2^140)',
    "§2.1 | ... (byte 4's constant)",
    "§2.1 | ... (byte 6's constant)",
    '§2.1 | ... and the centred-map offset is q + gamma1 in all four lanes (u := Z_UOFF - V, so the decode is FIPS BitUnpack per lane)',
    '§2.1 | ... and the flag bit read by the canonicalisation and by BOTH window edges is bit 32 of every lane',
    "§2.5 | useHintSwar folds FIPS 204's two reductions into ONE magic division, whose multiplier is ceil(2^12/44) = 94",
    '§2.5 | ... and the four 6-bit results are gathered by ONE multiply, K = 2^174 + 2^116 + 2^58 + 1',
    '§2.5 | ... and the [r0 > gamma2] comparator is 2^32 - (gamma2+1) per lane',
    '§2.5 | ... and the [r0 != 0] comparator is 2^32 - 1 per lane',
    '§2.1 | ... and that per-polynomial decode is driven over all 4 polynomials of z, each from its own 576-byte encoding slice',
    '§2.1 | ... and that driver runs exactly 4 times, so its 4 check sites x 16 iterations x 4 lanes x 4 polynomials cover all 1024 coefficients of z',
    "§2.3 | the VERIFIER builds M' = 00 || 00 || M itself (pure ML-DSA, empty context; the two zero bytes come from zero-initialised memory of exactly 66 + |M| bytes)",
    "§2.3 | mu = SHAKE256(tr || M', 64) with tr taken from the bound pk blob (fixed 64 bytes at payload offset 0 = code offset 1)",
    '§2.7 | accept iff c~ equals the recomputed digest — no other path',
    '§4.1 | the squeeze writes EXACTLY the 136-byte rate block: its fifth store lands flush with the end of the block (outPtr+104 carrying lanes 13..16) instead of overhanging it by 24 bytes',
    '§4.1 | ... and the absorb READS exactly the same 136 bytes: lane 16 is taken from the word at ptr+104, not ptr+128, so no load reaches past the block',
    '§5 | the lane reduction stays inside 0 <= r < 2q -- STEP 1, the coarse Barrett whose product fits a 64-bit lane',
    '§5 | ... and STEP 2, which is LOAD-BEARING: step 1 alone lands under 2^33, three orders of magnitude above 2q',
    '§5 | the packed reduction is LANE-LOCAL: one 31-bit-per-lane mask both extracts the quotient and blocks the neighbouring lane, so no lane is ever spread to 128-bit spacing',
    '§5 | forward NTT lanes grow by exactly +2q per layer (the butterfly stores u+V and u+2q-V, not u+2q+V)',
    '§5 | inverse NTT layer 8 canonicalises with `mod`, NOT with Barrett -- this is what keeps the Barrett domain at 128q(q-1)',
    "§5 | the inverse NTT's layer blocks are delimited by profiling markers (the CODE anchors C16 slices its regions on)",
    "§5 | the forward NTT's layer blocks are delimited by profiling markers too, and there are THREE of them (radix-8 L1+L2+L3, radix-8 L4+L5+L6, in-word L7+L8), so the last marker is the fourth",
    '§5 | ... and the final marker closes the fused L7+L8 block',
    '§5 | the NTT LAYER SCHEDULE used by C9f/C9g is the one the bytecode executes (8 forward layers of +2q; inverse: mulmod/addmod entry fold at L1+L2 against the ACCQ30/ACCQ31 offsets (S14), K = 2^(L-1) with Barrett at L3..L7 and `mod` at L8). The forward runs its eight layers as THREE fused passes and the inverse as FOUR; the layer sequence, and therefore every bound, is the same in both groupings',
    '§FV.1 | the TRUST ANCHOR at the top of formal/z3/verify_all.py is the reviewed code (nothing above or inside it has been edited)',
    '§FV.2 | the Python interpreter, its standard library and its installed packages (z3-solver) are the ones they claim to be',
    '§FV.3 | no pinned file is swapped between the moment a check reads it and the moment the checks finish',
    '§FV.1 | check 0 re-derives the trust anchor under an interpreter found OUTSIDE this repository, and refuses if it cannot find one',
    '§FV.1 | ... and refuses if the interpreter the other checks run under resolves INSIDE the repository',
    '§FV.1 | ... and resolves the $PY PATH, not just sys.executable, so a repository-owned WRAPPER SCRIPT is caught too',
    '§FV.4 | check 2 elaborates the Lean development in a directory that HAS no build cache, so no `.lake` artefact can be replayed',
    '§FV.4 | ... and asserts the sandbox is cache-free before it builds',
    '§FV.5 | the Lean toolchain (`lake`, `lean`, and the compiler elan selects from lean-toolchain) is the one it claims to be',
    '§FV.1 | what the anchors BLANK before digesting is proved to be inert data, so no blanked region can be executable',
    '§FV.6 | the check script that drives every check is itself pinned, outside every blanked region',
    '§FV.6 | ... and the six ANCHOR_* lines it blanks are nothing but hex/version string assignments',
    '§FV.6 | the process that RUNS the checks is not itself hostile',
    '§FV.7 | every Wycheproof shard runs the number of cases it is documented to run, asserted ON CHAIN rather than in the builder that produced the cache',
    '§FV.7 | ... and every ACVP shard likewise (165 = 28+28+28+27+27+27 official cases, 120 = 4 x 30 FIPS204-tr1 cases)',
    "§FV.7 | test/FV2_Barrett.sol's Barrett kernels really are the shipped reductions -- the character-identity its header asserts in a COMMENT, and which FORMAL_VERIFICATION.md 5.7 calls Closed",
]


def _row_key(r):
    return f"{r['sec']} | {r['hyp']}"


# ---------------------------------------------------------------------------
# THE EVIDENCE COLUMNS ARE ASSERTIONS TOO
# ---------------------------------------------------------------------------
# The `mutant` column is this file's LOAD-BEARING claim: "delete this check and
# mutant X catches it", and prose alone does not validate it.  A row citing
# `M22, M23 KILLED` where NEITHER ID EXISTS -- for a check mutants.py itself
# documents as unkillable by construction -- is indistinguishable, to a reader,
# from a citation to a mutant that passes.  That is the general class this
# apparatus is built against: something a check
# COUNTS that nothing DIGESTS.  Every ID cited below is checked against the
# catalogue it belongs to, and an unknown ID FAILS the check.
_MUT_ID_RE = re.compile(r"\b(M\d+[a-z]?|E0\d|VT\d+|V\d+[a-z]?\d?)\b")


def _module_list(rel, name):
    """A module-level list/dict of CONSTANTS, read without executing the file."""
    tree = ast.parse(raw_text(os.path.join(REPO, rel)))
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id == name:
            return ast.literal_eval(node.value)
    raise KeyError(f"{rel}: no module-level {name}")


def _catalogue_ids():
    """(mutation IDs, vacuity-mutation IDs) — the two catalogues, as they are."""
    tree = ast.parse(raw_text(os.path.join(REPO, "formal/mutation/mutants.py")))
    muts = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) \
                and node.func.id == "dict":
            for kw in node.keywords:
                if kw.arg == "id" and isinstance(kw.value, ast.Constant):
                    muts.add(kw.value.value)
    vac = set(_module_list("formal/z3/vacuity_audit.py", "EXPECTED_MUTATIONS"))
    return muts, vac


def cited_mutant_problems():
    """Every mutant/vacuity ID cited in a row that no catalogue defines."""
    try:
        muts, vac = _catalogue_ids()
    except Exception as exc:                       # never a silent skip
        return [f"CANNOT READ THE MUTATION CATALOGUES: {exc!r}"]
    bad = []
    for r in ROWS:
        for field in ("mutant", "proved"):
            for cid in _MUT_ID_RE.findall(r.get(field) or ""):
                if field == "proved" and not cid.startswith(("M", "V")):
                    continue
                if cid.startswith(("VT", "V")) and cid in vac:
                    continue
                if cid in muts:
                    continue
                bad.append(f"{_row_key(r)[:60]!r} cites {cid}, which is in NO catalogue")
    return sorted(set(bad))


# ---------------------------------------------------------------------------
# THE PUBLISHED COUNTS ARE TOOL-GENERATED
# ---------------------------------------------------------------------------
# Obligation counts, conjunct counts, Lean theorem and module counts, mutant
# catalogue sizes and kill rates are all quantities a tool in this tree
# PRODUCES, so none of them should ever be typed into a document: a hand-typed
# 50 obligations / 367 conjuncts, or 30 Lean theorems in two modules, drifts
# silently from the 60 / 657 / 64-in-three the tools report (Decode.lean and
# its 26 audited theorems about the SHIPPED SWAR z-decode check are the third
# module), and a kill rate in RESULTS.md can contradict the driver's own pinned
# constant.  The rule below is: wherever a documented
# sentence names one of these quantities, the number in it must equal what the
# tool says NOW, and the sentence must exist somewhere (deleting it is drift
# too).  `--print-counts` prints the authoritative values.
# `test/MUT_Gaps.t.sol` is in the list because its whole premise is that every
# test NAMES the mutant it kills, so a name carrying a non-catalogue ID
# (`M14`, `M15`, `M19`, `M22`, `M31`, `M35`, `M36` are all absent from the
# catalogue) reads exactly like a citation to something that passes.
# `.github/workflows/ci.yml` is in the list because a workflow file that
# names a published count is a published file: leave it out and nothing under
# `.github/` is seen at all, so its "the whole EVM corpus (307 tests)" can
# stand against a derived corpus size of 315 with every check green, in a file
# nothing else in this tree scans.
DOC_FILES = ("docs/FORMAL_VERIFICATION.md", "docs/SAFETY.md", "README.md",
             "formal/README.md", "formal/run_checks.sh",
             "formal/mutation/RESULTS.md", "formal/mutation/run_mutation.py",
             "test/MUT_Gaps.t.sol", ".github/workflows/ci.yml")

# THIS FILE is a published file too, and its module docstring is the region
# most easily missed: `doc_id_problems` scans the DOCUMENTS and the evidence
# COLUMNS of the rows below, so an ID cited in the prose of the file doing the
# scanning -- `M36`, say, which is in no catalogue, credited as a
# provably-redundant survivor -- would go unchecked.  So it is scanned too.
#
# It is scanned by DOCSTRING and not whole, and the boundary is deliberate: the
# body of this file (and of the drivers) quotes IDs and COUNTS that deliberately
# DO NOT hold -- "a row citing mutants `M22, M23` that do not exist", "obligation
# `S12c`, which does not exist", "a `28 hypotheses are ENFORCED` held against
# what this very file reports".  Those are correct precisely BECAUSE the IDs
# they name are absent and the counts they carry disagree, so a whole-file scan
# would be a false-positive generator that gets silenced rather than a check.  A
# module docstring is the file's own current published description of itself,
# carries no such counterexamples, and is exactly the region worth scanning.
DOC_DOCSTRING_FILES = ("formal/hypotheses.py",)


# The EVM corpus, counted the way `forge test` counts it: a SUITE is a contract
# under test/ that declares at least one test entry point, and a TEST is such an
# entry point (a fuzz test is one test, exactly as forge reports it).  This is
# derived rather than typed for the same reason as every other count here: a
# typed "305 tests across 37 suites" is a published number NOTHING can
# contradict, and it drifts -- to 307/38, say -- with nothing noticing.
_TEST_FN_RE = re.compile(r"\bfunction\s+((?:test|invariant)[A-Za-z0-9_]*)\s*\(")
_CONTRACT_RE = re.compile(r"^\s*(?:abstract\s+)?contract\s+(\w+)", re.M)
# Not compiled as test sources by this count: the vendored oracle tree and the
# generated fixture/vector directories hold no test entry points.
_TEST_SKIP_DIRS = ("fixtures", "vectors")


def evm_corpus_counts(root=None):
    """(test entry points, suites) over test/**.sol, statically."""
    base = os.path.join(root or REPO, "test")
    tests, suites = 0, 0
    for dirpath, dirnames, filenames in os.walk(base):
        dirnames[:] = [d for d in sorted(dirnames) if d not in _TEST_SKIP_DIRS]
        for name in sorted(filenames):
            if not name.endswith(".sol"):
                continue
            text = raw_text(os.path.join(dirpath, name))
            marks = [(m.start(), m.group(1)) for m in _CONTRACT_RE.finditer(text)]
            for i, (pos, _cname) in enumerate(marks):
                end = marks[i + 1][0] if i + 1 < len(marks) else len(text)
                fns = set(_TEST_FN_RE.findall(text[pos:end]))
                if fns:
                    suites += 1
                    tests += len(fns)
    return tests, suites


_SOL_CONST_RE = "uint256 constant {} = ([0-9_]+);"


def _sol_uint_const(rel, name):
    """A Solidity `uint256 constant NAME = <literal>;`, read from the source.

    The published GAS figure is derived exactly like every other published
    number: from the artefact that produces it.  `test/E2E.t.sol` holds the
    measured value as a constant and asserts the SHIPPED verifier against it on
    every run, so the chain is  documents -> this constant -> the EVM.
    """
    m = re.search(_SOL_CONST_RE.format(re.escape(name)),
                  raw_text(os.path.join(REPO, rel)))
    if not m:
        raise KeyError(f"{rel}: no `uint256 constant {name}`")
    return int(m.group(1).replace("_", ""))


def authoritative_counts():
    """The counts, from the tools that produce them.  Never typed."""
    obl = _module_list("formal/z3/verify_all.py", "EXPECTED_OBLIGATIONS")
    con = _module_list("formal/z3/verify_all.py", "EXPECTED_CONJUNCTS")
    thm = _module_list("formal/lean/check_axioms.py", "EXPECTED_THEOREMS")
    stm = _module_list("formal/lean/check_axioms.py", "EXPECTED_STATEMENTS")
    muts = _module_list("formal/mutation/run_mutation.py", "EXPECTED_MUTANTS")
    equiv = _module_list("formal/mutation/run_mutation.py", "EXPECTED_EQUIVALENT")
    lean_mods = sorted({t.split(".")[1] for t in thm if t.count(".") >= 2})
    tests, suites = evm_corpus_counts()
    # THE HYPOTHESIS TABLE COUNTS ITSELF.  A documented `28 hypotheses are
    # ENFORCED` can sit in FORMAL_VERIFICATION.md while this file reports 58
    # unless a pattern here names the quantity and a key holds it.
    n_enf = sum(1 for r in ROWS if r.get("enforced", "yes") is not None)
    n_asm = len(ROWS) - n_enf
    return dict(obligations=len(obl), conjuncts=len(con),
                lean_theorems=len(thm), lean_statements=len(stm),
                lean_modules=len(lean_mods), mutants=len(muts),
                nonequiv=len(muts) - len(equiv), equivalents=len(equiv),
                hypothesis_rows=len(ROWS), hypotheses_enforced=n_enf,
                hypotheses_assumed=n_asm, tests=tests, test_suites=suites,
                verify_gas=_sol_uint_const("test/E2E.t.sol", "VERIFY_GAS_MEASURED"))


# (regex with ONE capturing group, the key whose value every match must equal).
# Phrasing-tolerant on purpose: the rule is about the NUMBER, wherever a
# documented sentence states that quantity.
#
# A pattern list that scans the right files but matches none of the phrasings
# the documents actually use lets published numbers drift underneath it, twenty
# and more at a time -- and four of the phrasings below live inside
# `run_checks.sh`'s own check LABELS, which is the mechanism designated to stop a
# sampled run being quoted as the full campaign, so drift there is worse than
# drift in prose.  Two quantities are also
# STRUCTURALLY unauditable unless a key holds them: the hypothesis-table row
# counts (this file's own output) and the EVM corpus's test/suite counts.  Both
# are derived (`evm_corpus_counts`, `ROWS`), and the phrasings below are
# normalised in the documents where a tight pattern needs a stable form -- the
# sample sentence is always "<n> of [the] <catalogue> mutants", because "8 of 40"
# alone cannot be told apart from "24 of 1024" or "256 of the 1024".
DOC_COUNT_PATTERNS = [
    (r"(\d+) machine-checked obligations", "obligations"),
    (r"(\d+)/\d+ obligations", "obligations"),
    (r"the (\d+) obligation IDs", "obligations"),
    (r"all (\d+) IDs", "obligations"),
    (r"(\d+) Z3 obligations", "obligations"),
    (r"(\d+) Z3 / exhaustive / exact-arithmetic obligations", "obligations"),
    (r"(\d+) named CONJUNCTS", "conjuncts"),
    (r"(\d+) conjunct IDs", "conjuncts"),
    (r"(\d+)/\d+ conjuncts", "conjuncts"),
    (r"all (\d+) conjunct IDs", "conjuncts"),
    (r"obligations / (\d+) conjuncts", "conjuncts"),
    (r"obligations \((\d+) conjuncts\)", "conjuncts"),
    (r"(\d+) audited Lean theorems", "lean_theorems"),
    (r"(\d+) axiom-audited (?:Lean 4 )?theorems", "lean_theorems"),
    (r"(\d+) Lean 4 theorems", "lean_theorems"),
    (r"`EXPECTED_THEOREMS` \((\d+) entries\)", "lean_theorems"),
    (r"(\d+) theorems \+ \d+ statement digests", "lean_theorems"),
    (r"\d+ theorems \+ (\d+) statement digests", "lean_statements"),
    (r"(\d+) statement digests", "lean_statements"),
    (r"The (\d+) theorems are in", "lean_theorems"),
    (r"(\d+)-mutant catalogue", "mutants"),
    (r"(\d+)-mutant campaign", "mutants"),
    (r"(\d+)-mutant mutation campaign", "mutants"),
    (r"the FULL (\d+)-mutant", "mutants"),
    (r"complete (\d+)-mutant", "mutants"),
    (r"\d+ of (?:the )?(\d+) mutants", "mutants"),
    # run_checks.sh's two SAMPLED check labels interpolate the sample size, so the
    # left-hand number is a shell variable and not a digit -- and those two
    # labels are the mechanism that stops a sampled scrollback being quoted as
    # the campaign, which makes drift there worse than drift in prose.
    (r"\$MUT_SAMPLE of (\d+) mutants", "mutants"),
    (r"all (\d+) catalogued mutants", "mutants"),
    (r"all (\d+) mutants", "mutants"),
    (r"every one of the (\d+) mutants", "mutants"),
    (r"(\d+) ?/ ?\d+ non-equivalent", "nonequiv"),
    (r"\d+ ?/ ?(\d+) non-equivalent", "nonequiv"),
    (r"published (\d+)/\d+ kill rate", "nonequiv"),
    (r"That (\d+)/\d+ is a claim", "nonequiv"),
    (r"\((\d+)/\d+; the", "nonequiv"),
    (r"(\d+) documented equivalents", "equivalents"),
    (r"all (\d+) pinned equivalent mutants", "equivalents"),
    (r"(\d+) equivalent survivors", "equivalents"),
    (r"(\d+) hypotheses are ENFORCED", "hypotheses_enforced"),
    (r"(\d+) enforced \(pattern \+ count pinned\)", "hypotheses_enforced"),
    (r"(\d+) enforced \+ \d+ ASSUMED", "hypotheses_enforced"),
    (r"\d+ enforced \+ (\d+) ASSUMED", "hypotheses_assumed"),
    (r"(\d+) (?:are )?explicitly ASSUMED", "hypotheses_assumed"),
    (r"(\d+) tests across \d+ suites", "tests"),
    (r"\d+ tests across (\d+) suites", "test_suites"),
    (r"(\d+) tests, \d+ suites", "tests"),
    (r"\d+ tests, (\d+) suites", "test_suites"),
    (r"(\d+) tests:", "tests"),
    # `.github/workflows/ci.yml`'s job description.  Unless the workflow is
    # inside DOC_FILES this number cannot be seen at all, and a stale 307
    # against a corpus of 315 stands with every check green.
    (r"the whole EVM corpus \((\d+) tests\)", "tests"),
]

# ---------------------------------------------------------------------------
# THE HEADLINE GAS FIGURE IS A PUBLISHED NUMBER TOO
# ---------------------------------------------------------------------------
# `1,226,311` is the first number in README.md and appears five times in
# docs/EXPLAINER.md.  A `VERIFY_GAS_CEILING = 1_700_000` in test/E2E.t.sol is
# no mechanical guard on it: at 39% above the
# real value, a 38% regression leaves every check green and the
# README silently false.  The figure is therefore (a) asserted against the
# measured value inside a +-0.5% band by
# `test_e2e_10_seed_vector_accepts_and_gas`, and (b) re-derived here from that
# test's own constant, exactly like every other published count.
#
# WHY A SECOND FILE LIST, and it is a deliberate boundary: docs/EXPLAINER.md is
# a NARRATIVE with a changelog, so it quotes obligation counts, conjunct counts
# and mutant counts as of EARLIER SNAPSHOTS ("52 Z3 obligations / 408
# conjuncts ...", five counts frozen at the point that sentence describes), and
# IDs that no longer exist.  Putting it in DOC_FILES would make the whole
# pattern set and the whole ID scan fire on deliberate history -- a
# false-positive generator that gets silenced rather than a check, which is the
# same reason DOC_DOCSTRING_FILES scans only a docstring.  The GAS figure
# carries no such history: every occurrence below is a claim about the CURRENT
# artefact, and each pattern names the sentence it lives in, so it is pinned.
DOC_GAS_FILES = ("README.md", "docs/EXPLAINER.md")
DOC_GAS_PATTERNS = [
    (r"costs \*\*([\d,]+) gas\*\*", "verify_gas"),
    (r"\*\*([\d,]+) gas\*\*, against the reproduced", "verify_gas"),
    (r"measured end-to-end ([\d,]+) gas", "verify_gas"),
    (r"\(shipped\) → ([\d,]+) /", "verify_gas"),
    (r"\| end-to-end `verify\(\)` \| [\d,]+ \| \*\*([\d,]+)\*\* \|", "verify_gas"),
    (r"\| \*\*Total \(measured end-to-end\)\*\* \| \*\*[\d,]+\*\* \| \*\*([\d,]+)\*\* \|",
     "verify_gas"),
]


# ---------------------------------------------------------------------------
# THE IDs CITED IN THE DOCUMENTATION ARE ASSERTIONS TOO
# ---------------------------------------------------------------------------
# `cited_mutant_problems` above checks the evidence columns of THIS file.  The
# documents need the same check, because a citation to an ID nobody defined is
# wrong in exactly the way a citation to a mutant nobody wrote is wrong: it
# reads exactly like a citation to something that passes.  Three examples:
#
#   docs/SAFETY.md          `O7.lane*_ctl_lifted_pk_breaks_lane_locality`, a
#                           conjunct that does not exist, credited with a claim
#                           (`domination FAILS at PK_AMAX = 2q`) that O7's real
#                           conjuncts deliberately REFUSE to make, because at 2q
#                           O7's control could not come out false.
#   docs/FORMAL_VERIFICATION.md   mutant `M05`, which is in no catalogue.
#   formal/run_checks.sh     obligation `S12c`, which does not exist (the
#                           bidirectional `theory_valid` check is S11 and S14).
#
# The rule: every obligation ID, conjunct ID, mutant ID and vacuity-mutation ID
# that appears in a published file must exist in the set that defines it.  A
# `*` is a glob and must match at least one pinned conjunct; `{m..n}` is a range
# and EVERY member of it must match, so `O7.lane{0..3}_...` asserts four
# conjuncts rather than one.
#
# WHAT THIS DELIBERATELY DOES NOT COVER, so the boundary is on the record: BARE
# Lean theorem names (`canon_zero_field`).  They are indistinguishable from
# Solidity/Python identifiers, of which the documents cite hundreds, so checking
# them would be a false-positive generator rather than a check.  FULLY QUALIFIED
# names (`Mldsa.Barrett.no_borrow`) are checked against EXPECTED_THEOREMS.
_DOC_ID_RE = re.compile(
    r"(?<![A-Za-z0-9_])("
    # C18 / S8b / E15 / O7, optionally with a conjunct suffix that may carry a
    # `*` glob and/or a `{m..n}` range
    # (the suffix needs at least one character after the dot, so a sentence that
    #  simply ENDS in an obligation ID -- "... extracted by C16." -- is read as
    #  the obligation and not as a conjunct called `C16.`)
    r"(?:C|S|E|O)\d{1,2}[a-z]?"
    r"(?:\.[A-Za-z0-9_*]+(?:\{\d+\.\.\d+\}[A-Za-z0-9_*]*)*)?"
    r"|M\d{1,3}[a-z]?"            # EVM-corpus mutants
    r"|VT\d{1,2}|V\d{1,3}[a-z]?"  # vacuity mutations
    r"|Mldsa\.[A-Za-z0-9_.*]+"    # fully qualified Lean theorems
    r")(?![A-Za-z0-9_])")
_RANGE_RE = re.compile(r"\{(\d+)\.\.(\d+)\}")


def _expand_ranges(tok):
    """`O7.lane{0..3}_x` -> the four concrete globs it stands for."""
    m = _RANGE_RE.search(tok)
    if not m:
        return [tok]
    lo, hi = int(m.group(1)), int(m.group(2))
    out = []
    for k in range(lo, hi + 1):
        out += _expand_ranges(tok[:m.start()] + str(k) + tok[m.end():])
    return out


def doc_id_problems():
    """Every ID cited in a published file that no pinned set defines."""
    try:
        muts, vac = _catalogue_ids()
        obl = set(_module_list("formal/z3/verify_all.py", "EXPECTED_OBLIGATIONS"))
        con = set(_module_list("formal/z3/verify_all.py", "EXPECTED_CONJUNCTS"))
        thm = set(_module_list("formal/lean/check_axioms.py", "EXPECTED_THEOREMS"))
    except Exception as exc:                       # never a silent skip
        return [f"CANNOT READ THE PINNED ID SETS: {exc!r}"]
    bad = []
    scan = []
    for rel in DOC_FILES:
        try:
            scan.append((rel, raw_text(os.path.join(REPO, rel))))
        except OSError as exc:
            bad.append(f"{rel}: {exc!r}")
    for rel in DOC_DOCSTRING_FILES:
        # the MODULE DOCSTRING only -- and a missing one is a failure, not a
        # silent skip, because deleting the docstring would delete the scan
        try:
            doc = ast.get_docstring(ast.parse(raw_text(os.path.join(REPO, rel))))
        except (OSError, SyntaxError) as exc:
            bad.append(f"{rel}: {exc!r}")
            continue
        if not doc:
            bad.append(f"{rel}: no module docstring to scan (it is DOC_DOCSTRING_FILES"
                       " precisely because its own prose cites IDs)")
            continue
        scan.append((f"{rel} (module docstring)", doc))
    for rel, text in scan:
        for m in _DOC_ID_RE.finditer(text):
            tok = m.group(1)
            for cited in _expand_ranges(tok):
                if cited.startswith("Mldsa."):
                    ok = any(fnmatch.fnmatchcase(t, cited) for t in thm)
                    what = "Lean theorem"
                elif "." in cited:
                    ok = any(fnmatch.fnmatchcase(c, cited) for c in con)
                    what = "conjunct"
                else:
                    ok = cited in obl or cited in muts or cited in vac
                    what = "obligation/mutant/vacuity-mutation"
                if not ok:
                    bad.append(f"{rel}: cites {cited!r}, which is in NO pinned "
                               f"{what} set"
                               + (f" (cited as {tok!r})" if cited != tok else ""))
    return sorted(set(bad))


# ---------------------------------------------------------------------------
# THE MUTANT ATTRIBUTIONS IN test/MUT_Gaps.t.sol ARE ASSERTIONS TOO
# NOT MERELY THAT THE IDs THEY NAME EXIST
# ---------------------------------------------------------------------------
# `doc_id_problems` above asks whether a cited id EXISTS.  That is not the claim
# `test/MUT_Gaps.t.sol` publishes.  Its header says "every test names the mutant
# id it kills, so the link between a test and the defect it detects is
# reproducible rather than asserted" -- and without this check it is asserted:
#
#   * a test named `test_MUT_M39_reference_decoder_gates` need not kill M39 at
#     all -- M39's sole killer in the whole corpus is
#     `test_MUT_M44_hint_weight_omega_bound` -- and because M39 exists, the
#     existence check passes and the wrong attribution stands.
#   * a test naming M26 or M28 names a PINNED EQUIVALENT mutant, which nothing
#     can kill by construction, so such a name could never be true.
#
# The ground truth cannot support the claim either unless the campaign that
# produced it is complete: a `killers[:12]` cap, or a full run inheriting
# `--fail-fast` (which cancels the forge run), leaves the recorded lists a
# truncated, order-dependent prefix -- M11's entry being exactly 12 names from
# one suite is the cap, hit.  So the artefact carries a `_meta` block naming
# the mode, the fail-fast setting and the SHA-256 of the two files the
# attribution is ABOUT, and this check refuses a stale or sampled artefact.
#
# The convention, and it is checked in both directions:
#   test_MUT_M<nn>_*        -> M<nn> must be NON-EQUIVALENT and this test must
#                              appear in its killer list
#   test_equivalent_M<nn>_* -> M<nn> must be in EXPECTED_EQUIVALENT and must
#                              have SURVIVED
#
# WHAT THIS CHECK CHECKS IS CO-OCCURRENCE, NOT CAUSATION.  The rule above is
# "the named test must appear in that mutant's killer list".  For a mutant with
# a LARGE killer set that is very weak: 23 of the 45 non-equivalent mutants are
# killed by 24 or more tests each (M64 by 66), so for those the check accepts
# almost any name in the corpus.
# The document's literal wording -- "every test names the mutant id it kills" --
# is true of what is checked; the impression it leaves ("this test is why that
# mutant dies") is stronger than the check.  Said plainly here rather than left
# to be inferred.
#
# THE ONE CASE WHERE CO-OCCURRENCE *IS* CAUSATION is a killer set of size one:
# remove that test and the mutant survives, by definition.  Those are the
# fragile attributions and the ones worth pinning, so they are pinned BY VALUE
# below and checked in both directions.  The case that makes this concrete and
# mechanical rather than anecdotal: M44 and M39 are each
# killed by EXACTLY ONE test in the whole corpus and it is the SAME test
# (`test_MUT_M44_hint_weight_omega_bound`) -- and M39 has no test named after
# it, so the attribution check above never looks at M39 at all.  Weakening that
# single test silently un-kills two catalogued mutants.
MUT_GAPS_REL = "test/MUT_Gaps.t.sol"
MUT_ARTEFACT_REL = "formal/mutation/mutation_results_final.json"
# mutant -> its ONE killer in the whole EVM corpus.  Regenerate from a full
# campaign (`run_mutation.py --full`) after a REVIEWED change; a new entry means
# a new single point of failure in the corpus and should be read as one.
SOLE_KILLER_PINS = {
    "M20": "test_hint_decoder_is_identical_across_builds",
    "M21": "test_hint_decoder_is_identical_across_builds",
    "M25": "test_kernel_21_useHintSwar_boundaries",
    "M39": "test_MUT_M44_hint_weight_omega_bound",
    "M44": "test_MUT_M44_hint_weight_omega_bound",
}
_MUT_KILL_TEST_RE = re.compile(
    r"function\s+(test(?:Fuzz)?_MUT_(M\d{1,3}[a-z]?)_[A-Za-z0-9_]*)\s*\(")
_MUT_EQUIV_TEST_RE = re.compile(
    r"function\s+(test(?:Fuzz)?_equivalent_(M\d{1,3}[a-z]?)_[A-Za-z0-9_]*)\s*\(")


def _sha256_of(rel):
    return hashlib.sha256(raw_text(os.path.join(REPO, rel)).encode("utf-8")).hexdigest()


def mut_attribution_problems():
    """Every kill/equivalence claim made by a test NAME, checked against the run."""
    try:
        src = raw_text(os.path.join(REPO, MUT_GAPS_REL))
        art = json.loads(raw_text(os.path.join(REPO, MUT_ARTEFACT_REL)))
        equiv = set(_module_list("formal/mutation/run_mutation.py",
                                 "EXPECTED_EQUIVALENT"))
        expected = _module_list("formal/mutation/run_mutation.py",
                                "EXPECTED_MUTANTS")
    except Exception as exc:                       # never a silent skip
        return [f"CANNOT READ THE MUTATION ATTRIBUTION GROUND TRUTH: {exc!r}"]
    bad = []
    if not isinstance(art, dict) or "_meta" not in art or "results" not in art:
        return [f"{MUT_ARTEFACT_REL}: not a self-describing {{_meta, results}} "
                f"artefact; re-run `formal/mutation/run_mutation.py --full`"]
    meta, rows = art["_meta"], art["results"]
    by_id = {r["id"]: r for r in rows}
    if meta.get("mode") != "FULL":
        bad.append(f"{MUT_ARTEFACT_REL}: mode is {meta.get('mode')!r}, not FULL — "
                   "a sample is not an attribution")
    if meta.get("fail_fast"):
        bad.append(f"{MUT_ARTEFACT_REL}: produced WITH --fail-fast, so its killer "
                   "lists are an order-dependent prefix, not a killer set")
    if not meta.get("complete") or sorted(by_id) != sorted(expected):
        bad.append(f"{MUT_ARTEFACT_REL}: {len(by_id)} of {len(expected)} catalogued "
                   "mutants have a verdict; an incomplete campaign cannot attribute")
    # THE ARTEFACT MUST BE ABOUT THESE BYTES.  Without this, editing a test name
    # here and not re-running the campaign leaves the check quoting a file that
    # describes different sources -- the same "nothing detects it going stale"
    # class this whole apparatus exists to close.
    want_src = {"formal/mutation/mutants.py", MUT_GAPS_REL}
    got_src = meta.get("source_sha256") or {}
    if set(got_src) != want_src:
        bad.append(f"{MUT_ARTEFACT_REL}: _meta.source_sha256 pins {sorted(got_src)}, "
                   f"expected {sorted(want_src)}")
    for rel, want in sorted(got_src.items()):
        if rel not in want_src:
            continue
        try:
            got = _sha256_of(rel)
        except OSError as exc:
            bad.append(f"{rel}: {exc!r}")
            continue
        if got != want:
            bad.append(f"{MUT_ARTEFACT_REL}: describes {rel} at sha256 {want[:16]}…, "
                       f"but the file is {got[:16]}… — the campaign predates the "
                       "current sources; re-run `run_mutation.py --full`")
    claims = list(_MUT_KILL_TEST_RE.finditer(src))
    if not claims:
        bad.append(f"{MUT_GAPS_REL}: no `test_MUT_M<nn>_*` test remains; the file's "
                   "whole premise is that its names are attributions, so deleting "
                   "them all is drift too")
    for m in claims:
        fn, mid = m.group(1), m.group(2)
        rec = by_id.get(mid)
        if rec is None:
            bad.append(f"{MUT_GAPS_REL}: {fn} names {mid}, which has no verdict in "
                       f"{MUT_ARTEFACT_REL}")
            continue
        if rec.get("equivalent"):
            bad.append(f"{MUT_GAPS_REL}: {fn} claims to KILL {mid}, a PINNED "
                       "EQUIVALENT mutant that nothing can kill by construction; "
                       f"name it test_equivalent_{mid}_... and argue the equivalence")
            continue
        if fn not in (rec.get("killers") or []):
            bad.append(f"{MUT_GAPS_REL}: {fn} claims to kill {mid}, but the campaign's "
                       f"killers for {mid} are {sorted(rec.get('killers') or [])!r}")
    for m in _MUT_EQUIV_TEST_RE.finditer(src):
        fn, mid = m.group(1), m.group(2)
        rec = by_id.get(mid)
        if mid not in equiv:
            bad.append(f"{MUT_GAPS_REL}: {fn} is labelled an equivalence argument, but "
                       f"{mid} is not in EXPECTED_EQUIVALENT")
        elif rec is None or rec.get("verdict") != "SURVIVED":
            bad.append(f"{MUT_GAPS_REL}: {fn} argues {mid} is equivalent, but the "
                       f"campaign records {rec and rec.get('verdict')!r}, not SURVIVED")
    # ---- the SOLE-KILLER pins: the attributions that really are causal ----
    # A mutant with one killer has a single point of failure in the corpus, and
    # the check above cannot see it (it only asks whether a NAMED test is IN the
    # list).  Checked in both directions, so a new fragile attribution is a
    # failure rather than a silence, and a pin that stopped describing anything
    # is a failure too.
    sole = {r["id"]: (r.get("killers") or [])[0]
            for r in rows
            if not r.get("equivalent") and len(r.get("killers") or []) == 1}
    for mid, killer in sorted(sole.items()):
        want = SOLE_KILLER_PINS.get(mid)
        if want is None:
            bad.append(f"{MUT_ARTEFACT_REL}: {mid} is now killed by EXACTLY ONE test "
                       f"({killer!r}) and is not in SOLE_KILLER_PINS. A single-killer "
                       f"mutant is a single point of failure in the corpus: pin it "
                       f"(and consider whether a second test should reach it)")
        elif want != killer:
            bad.append(f"{MUT_ARTEFACT_REL}: {mid}'s sole killer is {killer!r}, "
                       f"SOLE_KILLER_PINS says {want!r}")
    for mid, want in sorted(SOLE_KILLER_PINS.items()):
        rec = by_id.get(mid)
        if rec is None:
            bad.append(f"SOLE_KILLER_PINS names {mid}, which has no verdict in "
                       f"{MUT_ARTEFACT_REL}")
        elif mid not in sole:
            n = len(rec.get("killers") or [])
            bad.append(f"SOLE_KILLER_PINS says {mid} is killed only by {want!r}, but "
                       f"the campaign records {n} killer(s). A pin that no longer "
                       f"describes anything is drift: re-derive it from the full run")
    return sorted(set(bad))


def doc_count_problems():
    """Published counts that disagree with the tool that produces them."""
    try:
        counts = authoritative_counts()
    except Exception as exc:                       # never a silent skip
        return [f"CANNOT DERIVE THE AUTHORITATIVE COUNTS: {exc!r}"], {}
    bad = []
    seen = {k: 0 for _rx, k in DOC_COUNT_PATTERNS}
    # every PATTERN must fire too, not merely every key: the gas patterns each
    # name one published sentence, so a deleted sentence is drift even when a
    # sibling sentence still carries the same key.
    pat_seen = {rx: 0 for rx, _k in DOC_COUNT_PATTERNS + DOC_GAS_PATTERNS}
    for pats, files in ((DOC_COUNT_PATTERNS, DOC_FILES),
                        (DOC_GAS_PATTERNS, DOC_GAS_FILES)):
        for rel in files:
            try:
                text = raw_text(os.path.join(REPO, rel))
            except OSError as exc:
                bad.append(f"{rel}: {exc!r}")
                continue
            for rx, key in pats:
                for m in re.finditer(rx, text):
                    seen[key] = seen.get(key, 0) + 1
                    pat_seen[rx] += 1
                    # documents write 1,226,311; sources write 1_226_311
                    if int(m.group(1).replace(",", "").replace("_", "")) != counts[key]:
                        bad.append(f"{rel}: {m.group(0)!r} — the tools say "
                                   f"{key} = {counts[key]}")
    for key in sorted(set(seen)):
        if not seen[key]:
            bad.append(f"no document states the {key} count any more "
                       f"({key} = {counts[key]}); a deleted claim is drift too")
    for rx, key in DOC_GAS_PATTERNS:
        if not pat_seen[rx]:
            bad.append(f"no document states {rx!r} any more ({key} = "
                       f"{counts[key]}); a deleted claim is drift too")
    return sorted(set(bad)), counts


def main():
    ok = True
    print("=" * 78)
    print("SAFETY.md hypotheses -> enforcing checks -> evidence")
    print("=" * 78)
    if "--print-counts" in sys.argv:
        for k, v in sorted(authoritative_counts().items()):
            print(f"{k:<16} {v}")
        return 0
    if "--print-rows" in sys.argv:
        print("EXPECTED_ROWS = [")
        for r in ROWS:
            print(f"    {_row_key(r)!r},")
        print("]")
        return 0
    n_enf = n_asm = 0
    for r in ROWS:
        if r.get("enforced", "yes") is None:
            n_asm += 1
            print(f"[ASSUMED ] {r['sec']:<7} {r['hyp']}")
            print(f"           reason: {r['assumed']}")
            print(f"           evidence: {r['proved']}")
            continue
        n_enf += 1
        # `root="repo"` rows are tripwires over the APPARATUS (formal/**) rather
        # than over the EVM corpus (src/**, test/**); they exist because a CHECK
        # mechanism can be defeated exactly as a contract can.
        path = os.path.join(REPO, r["file"])
        try:
            src = raw_text(path)                   # os.open/os.read, never open()
        except OSError as e:
            print(f"[MISSING ] {r['sec']:<7} {r['hyp']}  ({e})")
            ok = False
            continue
        got = src.count(r["pat"])
        good = got == r["count"]
        ok &= good
        print(f"[{'ENFORCED' if good else '  BROKEN'}] {r['sec']:<7} {r['hyp']}")
        print(f"           {r['file']}: {got}/{r['count']} occurrence(s) of "
              f"{r['pat'][:64]!r}")
        print(f"           load-bearing: {r['mutant']}")
        print(f"           proved by:    {r['proved']}")
    got = [_row_key(r) for r in ROWS]
    problems = []
    if len(got) != len(set(got)):
        problems.append("duplicate row key(s): "
                        + str(sorted({k for k in got if got.count(k) > 1})))
    for k in EXPECTED_ROWS:
        if k not in got:
            problems.append(f"hypothesis row DELETED (pinned but not present): {k}")
    for k in got:
        if k not in EXPECTED_ROWS:
            problems.append(f"hypothesis row UNPINNED (present but not pinned): {k}")
    if got != EXPECTED_ROWS:
        problems.append(f"row ORDER/COUNT differs: {len(got)} rows, "
                        f"{len(EXPECTED_ROWS)} pinned")
    problems += cited_mutant_problems()            # the evidence columns
    problems += doc_id_problems()                  # the cited IDs
    problems += mut_attribution_problems()         # the CLAIMED attributions
    doc_bad, counts = doc_count_problems()         # the published counts
    problems += doc_bad
    for p in problems:
        print(f"  !! {p}")
    ok = ok and not problems
    print("-" * 78)
    print("published counts, re-derived from the tools that produce them: "
          + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    print("=" * 78)
    print(f"{n_enf} enforced hypotheses checked, {n_asm} explicitly ASSUMED, "
          f"{len(got)}/{len(EXPECTED_ROWS)} pinned rows present and in order, "
          f"{'all present' if ok else 'SOME MISSING OR UNPINNED'}")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
