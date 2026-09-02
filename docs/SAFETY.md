# Safety Report

> **FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE.** This verifier is
> **unaudited** research code. Parts of it are machine-checked (see
> `FORMAL_VERIFICATION.md`), but it has had **no professional implementation
> audit and no independent cryptographic review**, and it is not deployed.
> §3 lists what a deployment must provide. Those requirements are *mandatory*,
> not advice. Two of them are things the verifier cannot do for itself, and it
> cannot compensate for their absence.

This report is the consolidated result of the safety campaign run against the
shipped verifier, `MLDSA44Verifier` (`src/MLDSA44Verifier.sol`). A second,
independently written verifier in the same tree (`test/ZZZ_E2ERef.sol`) is a
*differential oracle*: both verifiers see the same input, and any disagreement
between them is a finding. Every finding below is backed by a test that
reproduces it. The full suite is **320 tests across 39 suites**, all passing
(`forge test`).

Companion document: `FORMAL_VERIFICATION.md`. It separates what is *proved*
from what is *tested* and carries the coverage matrix against the external
state of the art.

## What the system is made of

Three things live on-chain.

1. **The verifier.** The contract holding `verify()`.
2. **One pk blob per public key.** A data contract whose *code* is the
   expanded form of that key. A standard ML-DSA-44 public key is 1,312 bytes.
   `prepare/prepare.py` expands it offline into the 20,544-byte layout the
   verifier's arithmetic reads directly, and that layout is deployed as
   contract code.
3. **A shared Keccak-f[1600] helper.** One contract holding the Keccak
   permutation, which the verifier calls to compute SHAKE-256.

Every input to `verify()` is public, and an attacker may choose all of it. The
one thing the verifier trusts is the *contents* of the pk blob. That trust is
recorded as **assumption S1**, and nothing inside the verifier can establish
it. It has to be established once, before the blob's address is ever handed to
`verify()`, by a registration step that validates the blob. That step sits
outside the verifier, and §3 says exactly what it must do.

## Terms used in this report

* **ML-DSA-44, FIPS 204.** ML-DSA is the NIST post-quantum signature standard,
  published as FIPS 204. ML-DSA-44 is its smallest parameter set: public keys
  are 1,312 bytes and signatures are 2,420 bytes.
* **`q`, canonical, lifted.** All arithmetic is modulo the prime
  `q = 8,380,417`. A coefficient is **canonical** when it is stored as a value
  in `[0, q)`. The values `v + q`, `v + 2q`, … stand for the same field element
  but are not canonical; this report calls them **lifted**.
* **Parameters.** These are FIPS 204's ML-DSA-44 values, not choices made here:
  `d = 13` dropped low bits, `η = 2` bounds the secret-key coefficients,
  `τ = 39` non-zero coefficients in the challenge, `γ1 = 2^17 = 131,072`,
  `γ2 = (q−1)/88 = 95,232`, and `β = τ·η = 78`.
* **Infinity norm, `‖x‖∞`.** The largest absolute value among a polynomial's
  coefficients, each taken in the centred range. A **norm bound** is a rule of
  the form "reject unless `‖x‖∞` is below this number".
* **`pk`, `ρ`, `t1`.** A public key is `pkEncode(ρ, t1)`: a 32-byte seed `ρ`,
  from which the matrix `A` is expanded, followed by 1,280 bytes holding the
  1,024 ten-bit coefficients of `t1`. `t1` is the high part of `t = A·s₁ + s₂`.
* **`s₁`, `s₂`, `t₀`, `ξ`.** The secret material. `s₁` and `s₂` are short
  secret vectors, `t₀` is the low `d` bits of `t`, and `ξ` is the 32-byte seed
  that key generation (KeyGen) expands into all of them.
* **`tr`, `μ`.** `tr = SHAKE256(pk, 64)` is a 64-byte digest of the public key.
  `μ = SHAKE256(tr ‖ M′, 64)` is the message digest that binds a signature to
  the message *and* to the key.
* **pk blob, pk cache.** The blob is the deployed data contract described
  above. The verifier's arithmetic reads it as the NTT-domain arrays `Â` and
  `t̂1` plus `tr`; the loaded copy is what this report calls the **cache**.
* **Hint (`h`), UseHint, w1Encode.** A signature carries a few bits per
  polynomial, the hint, which tell the verifier how to correct rounding when it
  rebuilds the signer's commitment. `UseHint` applies those bits and
  `w1Encode` serialises the result.
* **`z`, `c̃`, and the final check.** A signature is `(c̃, z, h)`. The verifier
  rebuilds the commitment, recomputes the challenge from it and from the
  message, and accepts only if the recomputed value equals the `c̃` carried in
  the signature.
* **Degenerate key.** A public key that is correctly formatted, accepted by
  every FIPS 204 verifier including the reference one, and yet lets anybody
  forge signatures under it. §2.1 and §3.1 describe the class.
* **Key-free-forgeable.** Said of such a key: signatures under it can be
  produced from public data alone, with no secret key and no search.
* **Centred lift.** `lift(v) = 2^13·v mod± q`, the signed representative of a
  `t1` coefficient scaled back up by `2^d`. Its magnitude is what decides
  whether a key is degenerate (§3.1).
* **Proof-of-possession (PoP).** A registration step in which the applicant
  signs a challenge the registrar chose. It shows the applicant can sign. It
  does not show the key is non-degenerate (§3.1).
* **Registrar, registration.** Whatever component decides that a pk blob may
  be used: a registry contract, or the account-creation path of a smart
  account. §3.1 is its checklist.
* **The SOTA baseline.** The state-of-the-art on-chain implementation this work
  is measured against, ZKNoxHQ/ETHDILITHIUM. `FORMAL_VERIFICATION.md` §4 has
  the details of its two compliance defects.

---

## 0. Headline

- **No soundness break was found in the verifier's cryptographic core.**
  Thousands of adversarial tuples (each a public key, a message and a
  signature) were tried: mutated signatures, signatures spliced across keys
  and messages, and one attempt at universal forgery with no key at all. All
  were rejected; 0 were accepted.
- **The official NIST ACVP vectors pass on-chain**, including the deliberately
  invalid sigVer cases: 0 mismatches. The expected verdicts are ACVP's own,
  narrowed by this interface's empty-context rule. ML-DSA signatures may be
  bound to a context string. This verifier has no context parameter, so it
  behaves as if the context is always empty, and it must reject any signature
  made with a non-empty one. Under that rule the ACVP sigVer corpus
  contributes **zero must-accept coverage**, because its three
  `testPassed: true` cases all carry a non-empty context. The must-accept
  coverage comes from elsewhere: the 3 sigGen cases with an empty context, and
  15 repo-derived vectors that re-sign ACVP's own `(sk, message)` pairs with
  `ctx = ""`. Those 15 are NIST key material re-signed by the Python
  reference, not NIST answers.
- **The Wycheproof ML-DSA-44 corpus** (180 cases, 176 of them representable at
  this interface) runs with 0 divergences from the expected verdicts.
- **Two real compliance defects in the SOTA baseline were found here and fixed
  here.** The first is the missing existence-and-size check on the pk blob
  (§2.1). The second is the ‖z‖∞ norm boundary, which FIPS 204 makes strict
  (§2.2). A third defect, latent in the baseline's UseHint, is neutralized here
  (`FORMAL_VERIFICATION.md` §4).
- **The Keccak-f[1600] helper is bound by code hash**, both at construction and
  on every `verify()` call (§2.3). Binding it by address instead would open a
  route to accepting a message that was never signed.
- **One requirement is not negotiable.** The pk blob must be validated when it
  is registered. Without that the verifier is universally forgeable, and no
  check inside the verifier can substitute for it (§2.1, §3).
- **The EIP-3541 blob-prefix hazard is fixed** in the shipped layout (§4.2).
- **Two registration checks that look sufficient are not.**
  **Proof-of-possession does not reject degenerate keys**, and neither does a
  proof of knowledge of `(s₁, s₂)`:
  **No proof about the secret key rejects degenerate keys**. The degenerate
  class has secret keys that anyone can compute, that satisfy the norm bounds,
  and that really do sign under the reference FIPS 204 signer. A registrar
  relying on either check would admit exactly the keys the check was added to
  exclude. §3.1 states a criterion that works.
- **A lifted-but-congruent pk blob can make a valid signature *reject*.**
  Canonical coefficients are a precondition for soundness, not housekeeping
  (§3).
- **The differential evidence behind §3:** 606 adversarial tuples against an
  independently written FIPS 204 verifier, exhaustive check-by-check
  differentials, and bound-stress at the proved ceilings: zero divergences.
  Every claim in this headline list is pinned by a passing test and by a row in
  `formal/hypotheses.py`, not by prose.

---

## 1. What was run

| Stream | Scale | Result |
|---|---|---|
| NIST ACVP ML-DSA-44 (`ACVP_MLDSA44.t.sol`, `FV2_AcvpKeyGen.t.sol`) | **285 cases** across two official key populations that share no keys. `ah_*`: 165 cases, 18 must-accept / 147 must-reject, made up of all 15 official sigVer cases (all must-reject: 12 invalid, 3 valid but context-bound), 30 sigGen, 45 HashML-DSA domain-separation must-rejects, and 75 repo-derived cases that re-sign or mutate ACVP key material. `at_*` (ML-DSA-sigGen-**FIPS204-tr1**): 120 cases on 120 further official keys that appear nowhere else, 5 must-accept / 115 must-reject; those 5 are the only official-answer must-accepts at this interface. All 25 keyGen key pairs are also re-derived and verified on-chain | 0 mismatches |
| 100-key KAT breadth (`KAT_MLDSA44.t.sol`) | all 100 records of `pythonref/assets/PQCsignKAT_Dilithium2.rsp`: 100 distinct keys and messages, all must-accept, on both verifiers. This is third-party breadth, not NIST authority. The DRBG stream is the NIST harness's, replayed byte-for-byte at build time, but the keys and signatures are `dilithium_py`'s; see `pythonref/assets/provenance.txt` | 0 divergences |
| Wycheproof ML-DSA-44 (`SEC2_Wycheproof.t.sol`) | 180 cases, 176 representable. Flags exercised: `InvalidHintsEncoding`, `ZeroPublicKey`, `InfinityNormViolation`, `BoundaryCondition`, `IncorrectSignatureLength`, `InvalidContext` | 0 divergences; **found a bug in the reference oracle** (`FORMAL_VERIFICATION.md` §4b) |
| FIPS 204 acceptance-rule suite (`SEC2_Fips204Gates.t.sol`) | tests keyed to the property IDs P1–P48 of the external state-of-the-art coverage matrix (`FORMAL_VERIFICATION.md` §6.1), including the false-reject directions, plus a boundary sweep at 0 / 1 / γ2 / 2γ2 / γ1 / 2^23 / q−1 / q / q+1 / 2q / 2^32−1 | all pass |
| Differential + mutation fuzz (`FUZZ_MLDSA44.t.sol`) | 800 must-accept cases over 20 message lengths, plus 1,380 must-reject cases over 23 mutation classes. Every case is run differentially against the reference verifier and the Python reference | 0 divergences |
| SHAKE / FIPS-202 (`FUZZ_Shake.t.sol`) | 251 official ACVP SHAKE-256 known-answer tests, plus randomized inputs, squeeze continuation and absorb-in-chunks | all bit-exact |
| EVM-level audit (`SEC_*.t.sol`) | memory safety, calldata out-of-bounds reads, purity and opcode census, hostile and missing helper, pk-cache abuse, SampleInBall tail bound | findings in §2–§4 |
| Machine-checked proofs | 62 Z3 / exhaustive / exact-arithmetic obligations (794 conjuncts), plus 64 axiom-audited, zero-`sorry` Lean theorems | all pass |

---

## 2. Findings — fixed

### 2.1 The pk cache needed an existence-and-size check (it was a universal forgery with no setup) — **fixed; the residual is S1**

*The problem.* `EXTCODECOPY` zero-pads silently: copying code from an address
that holds none yields zeros rather than an error. Without a check that the
caller-supplied pk-blob address really holds a blob of the right size, an
attacker points it at any codeless address (`0xdead`, a precompile, anything)
and the cache loads as all zeros: Â = 0, t̂1 = 0, tr = 0. With z = 0 the
per-row identity the verifier checks collapses to `0 ≡ 0`, and the FIPS hash
check reduces to `c̃ = SHAKE256(μ ‖ w1Encode(0))`, which anyone can compute.
That is **universal forgery: no signing key, no grinding, any message.**

*The fix, applied.* `_loadPk` accepts the blob only if `extcodesize` is
**exactly** `PK_SIZE + 1 = 20,545` bytes: the `0x00` prefix byte plus the
20,544-byte payload. Anything else makes `verify()` return false. Codeless
addresses, precompiles, truncated blobs and unrelated contracts all fail
closed. The reference verifier enforces the same exact-size check.
Regression-tested in `SEC_pkcache.t.sol` and `ZZZR3_adversarial.t.sol`.

*What remains, and why the verifier cannot fix it.* A cache that has the right
size but bogus contents still passes, and the forgery still succeeds. No cheap
on-chain test can tie (Â, t̂1) to a real public key: doing so means running
ExpandA on-chain, which is exactly the work that caching the expanded key
exists to avoid. Checking `tr = SHAKE256(pk, 64)` does not help either, because
the forgery needs no relationship between `tr` and (Â, t̂1). **So assumption S1
is a hard requirement on the deployment architecture** (§3), not a nicety.

*And S1 needs more than "a real `prepare(pk)`".* Some format-valid public keys
are **degenerate**: honestly prepared, accepted by every FIPS 204 verifier, and
forgeable with no secret key. The flagship example is `pk = ρ ‖ 0^1280`, that
is `t1 = 0`. The verifier rebuilds the commitment as
`w′approx = Â·z − c·t1·2^d`, so a zero `t1` removes the challenge `c` from the
identity entirely. That leaves `z` and `h` free to be chosen, and
`c̃ = SHAKE256(μ ‖ w1Encode(UseHint(h, Â·z)))` then completes a signature on
any chosen message from public data alone. This is a property of the *scheme*,
not of this implementation: ML-DSA is not key-substitution robust. The
reference verifier accepts these keys too.

*The forgeable class is not "t1 = 0 and other low-weight keys".* What
characterises it is the **centred lift** `lift(v) = 2^13·v mod± q`, which
wraps. Take `t1 = 1023` in all 1,024 coefficients: maximal weight, maximal
value, and equally key-free forgeable, because `2^13·1023 = q−1 ≡ −1`. Of the
1,024 possible single-coefficient values, 24 collapse this way,
`{0..11} ∪ {1012..1023}`, both **ends** of the range. A validator written to
a "low weight" rule catches none of the upper half
(`SEC_pkcache.t.sol::test_maximal_t1_key_is_key_free_forgeable`).

§3.1 states the criterion precisely enough to implement. Two things it does
**not** recommend, both of which look as though they would work:
**Proof-of-possession does not reject degenerate keys**, and
**No proof about the secret key rejects degenerate keys**. This class has
publicly computable, norm-conforming secret keys, so both checks are answered
with no secret material. §3.1 has the demonstrations. The centred-lift
criterion is a **floor**, not a certificate; the only complete check in §3.1 is
the KeyGen-seed binding.

### 2.2 The strict FIPS norm boundary — **fixed**

FIPS 204 requires rejecting a signature whose `‖z‖∞` equals `γ1 − β`. The SOTA
repo accepts it. This verifier implements the strict test `‖z‖∞ < γ1 − β`, and
its equivalence to the FIPS rule is *proved* over all 2^18 field values: Z3
obligation S8, with exhaustive obligations E4/E5 for the per-coefficient form
the reference decoder carries. The shipped code tests four lanes at a time, and
that form has its own proofs: S8b (four lanes, EVM semantics, 96 conjuncts),
the exhaustive E3b/E4b/E5b, and the Lean theorem
`Mldsa.Decode.reject_iff_fips`. The fuzz battery exercises both sides of the
boundary at every lane of every polynomial.

### 2.3 The Keccak-f[1600] helper is bound by code hash, not by address — **fixed**

*The problem.* EIP-170's code-size limit forces the fully unrolled permutation
into its own contract, reached by `STATICCALL`. If that helper's address came
from an unvalidated constructor argument, a **hostile permutation helper would
make the verifier accept a valid signature for a different message that was
never signed.** The permutation output feeds every hash in the pipeline,
including the `μ` that binds the message.

*The fix, applied.* The helper is deployed byte-for-byte as raw runtime code
(`helpers/f1600_170.hex`), so the `keccak256` of that code is a constant that
does not depend on compiler settings:

```
F1600_CODEHASH = 0x4afb4435879cdf8e50474c7aab2bc3a679caed432550ad6dba64f509309a817b
```

The constructor reverts (`BadHelper`) unless the helper account's code hash
matches, and `verify()` re-asserts the match on **every call**, so a helper
account swapped after deployment is caught as well. Because the helper is raw
runtime code with no solc metadata trailer, the plain code hash is exact and
toolchain-independent. The check is effectively free: `EXTCODEHASH` is the
first touch of the helper account, so it absorbs the cold-account charge that
the `STATICCALL`s after it would otherwise pay. Regression-tested in
`SEC_helper.t.sol` with hostile, codeless and metamorphic helpers.

*A missing helper is already safe.* `f1600Fast170` requires
`returndatasize() == 800` and `shake256Batch170` requires
`returndatasize() == 136`, both in `src/FastKeccak170.sol`. Both fail closed if
the helper is absent, short, reverting or returning garbage.

*A design note: a fully in-process design has no such trust edge.* The
UseHint/w1Encode stage is computed in-process here (`useHintSwar` in
`src/Decode.sol`), and its 768-byte output *is* the second input to the final
check `c̃ = SHAKE256(μ ‖ w1Encode(w1))`. Any alternative build that splits that
stage out into its own contract **must** pin the new helper by content, for the
same reason as the Keccak helper.

---

## 3. Deployment requirements (all mandatory, none optional)

A production deployment **must** provide all of the following. Two of these are
outside the verifier's reach; the verifier cannot compensate for them.

### 3.1 A registration validator for the pk blob (assumption S1)

Before a blob address is usable, it must be established that the blob is the
deterministic transform of a genuine FIPS 204 public key. Two shapes do this:

* **(a) On-chain derivation.** A registry performs the derivation on-chain,
  once per key. ExpandA is expensive, but this is a one-time cost.
* **(b) Client-side derivation.** The account stores the blob address at
  creation time, from a client-side derivation it trusts, and the verifier is
  only ever called with that stored address. This is the ERC-4337 /
  account-abstraction shape.

In both shapes the validator must do **all seven** of the following.

**(1) Compare the blob byte for byte against `prepare(pk)`.** The blob must be
exactly `prepare(pk)` of a public key that is genuine, non-degenerate and
exactly 1,312 bytes long. "The blob is *a* real `prepare()` of *some*
well-formed pk" is **not** sufficient. A coefficient range check is weaker
still.

**(2) Reject degenerate keys, by an explicit criterion applied to the key
itself.** Two criteria are given below; use the strongest one available.

* **(i) The centred-lift criterion** is the *primary* one, because a registrar
  can evaluate it from the submitted key alone. Treat it as a **hard floor to
  refuse beneath**, never as a certificate that anything above it is safe. For
  a coefficient value v ∈ [0, 2^10):

  ```python
  Q, D, GAMMA2 = 8380417, 13, (8380417 - 1) // 88

  def centred_lift(v):                 # v is one 10-bit t1 coefficient
      t = (v << D) % Q
      return t - Q if t > Q // 2 else t

  def degenerate_t1(t1_rows):          # t1_rows: 4 x 256 ints in [0, 2^10)
      # Refuse unless enough coefficients have a centred lift LARGE relative
      # to gamma2.  v = 0 gives lift 0; v = 1023 gives lift -1; both are
      # caught by |lift|.
      big = sum(1 for row in t1_rows for v in row if abs(centred_lift(v)) > GAMMA2)
      return big < 4 * 256 // 2        # e.g. at least half must be large
  ```

  It is stated on `|lift|` deliberately. That is what catches the **maximal**
  degenerate key: `t1 = 1023` everywhere, every `pkEncode` byte `0xff`, nothing
  that looks like the `t1 = 0` fixture. Any "low weight" or "near zero" rule
  admits it.

  Why this can only ever be a floor. The quantity that actually decides
  forgeability is `‖c ⊛ lift(t1)‖∞`, the challenge polynomial convolved with
  the centred lift, because that is what must stay inside the hint machinery
  for a key-free forgery to close. `c` has τ = 39 non-zero coefficients, each
  ±1, so a single coefficient's lift is **amplified** by a τ-dependent factor,
  and the attacker chooses `c` by **grinding the message**. **Measured:**
  one-shot forgery works at `v ∈ {0, 1022, 1023}`; with message grinding,
  `{0, 1, 2, 3}` and `{1020…1023}` fall within ~1,156 hashes, while
  `{5, 8, 11, 12, 16, 1011, 1012, 1016}` survive > 4,000. So the cheaply
  forgeable set is roughly `|lift| ≲ γ₂/4`, and the documented
  `{0…11} ∪ {1012…1023}` threshold errs conservative. That is the right
  direction, but it is a margin around an amplified, grindable quantity, not
  the boundary of forgeability.

* **(ii) A binding of the key to its KeyGen seed ξ** is the only **complete**
  criterion. FIPS 204 Algorithm 1 expands a 32-byte seed ξ into `(ρ, ρ′, K)`,
  derives `(s₁, s₂)`, and sets `(t1, t₀) = Power2Round(A·s₁ + s₂, d)`. The
  registrant supplies ξ and the registrar **re-runs Algorithm 1 and requires
  the derived `pkEncode(ρ, t1)` to equal the submitted 1,312-byte pk byte for
  byte**. That is sound in the client-side / account-abstraction shape (b),
  where the derivation is already done by software the account trusts. Where ξ
  must not be revealed, the registrant instead **proves knowledge of ξ in zero
  knowledge**.

  Why (ii) is complete where (i) is a floor: (i) tests the *key*, which the
  attacker chooses freely, while (ii) tests the *process that produced it*,
  which the attacker cannot fake without inverting SHAKE. A `t1` derived from
  KeyGen is essentially uniform, and a key-free-forgeable `t1` needs **all
  1,024** coefficients inside a 24-value window: `(24/1024)^1024 ≈ 2^−5545`
  per seed, about `2^−5289` expected over the whole 2^256 seed space. **No ξ
  maps to a degenerate key.** There is no threshold to tune and no
  amplification argument to get wrong.

  **The operational cost, stated rather than glossed.** The registrant must
  **retain ξ**, or be able to prove things about it. FIPS 204 allows a
  seed-only private-key format, so this is within the standard, but it
  constrains key import. A key that arrives as a bare 1,312-byte pk, from an
  HSM that discarded ξ, or migrated from a system that never stored it,
  **cannot be registered under this criterion at all**. Such a key falls back
  to (i) and inherits (i)'s limits. A deployment offering both paths should
  record which keys took which.

**Only one check in this section rejects every degenerate key: the KeyGen-seed
binding.** The two candidate checks below both read like sound advice and are
wrong in opposite directions.

* **Proof-of-possession does not reject degenerate keys.** The tempting advice
  is to "lead with proof-of-possession; it removes the whole class exactly",
  justified by "a key-free-forgeable pk has no owner". That justification is
  backwards:

  > A key-free-forgeable public key does not have NO owner: it has EVERY owner.

  Anyone answers a proof-of-possession challenge under such a key, with no
  secret material. PoP is a *signature* check, and on this class a signature is
  exactly what is free. PoP is sound against a *different* threat: registering
  someone else's honest key, and binding a key to the account that uses it. So
  use it **in addition to** the criteria above, never instead of them.
  Demonstrated end to end, one shot, no grinding, against a registrar-chosen
  challenge:

  ```
  pythonref/myenv/bin/python tools/fixtures/degen.py <32-byte-rho-hex> 0x<challenge-hex>
  ```

  That emits a `t1 = 0` pk, its honest `prepare()` blob, and a signature over
  the challenge that the reference FIPS 204 verifier accepts. Both on-chain
  subjects accept it too:
  `SEC_pkcache.t.sol::test_proof_of_possession_does_not_reject_a_degenerate_key`.

* **No proof about the secret key rejects degenerate keys.** The natural
  replacement for PoP is "a proof of knowledge of `(s₁, s₂)`: the complete
  answer, because it demands the one object a degenerate key does not have".
  It fails for the same reason. A degenerate key *has* that object, and the
  object is **public**:

  > A key-free-forgeable public key does not lack a secret key: it has one that anyone
  > can write down.

  Here are the two flagship members of the class, with `η = 2` and `d = 13`:

  ```
  t1 = 0    in all 1024 coefficients   <-   (s1, s2, t0) = ( 0,  0, 0)
  t1 = 1023 in all 1024 coefficients   <-   (s1, s2, t0) = ( 0, -1, 0)
  ```

  Check them with a pencil. For `t1 = 0`: `A·0 + 0 = 0` and
  `Power2Round(0, 13) = (0, 0)`, so the key relation `A·s₁ + s₂ = t1·2¹³ + t₀`
  holds exactly, with norms 0 ≤ η. For `t1 = 1023`: `A·0 + (−1) ≡ q − 1` and
  `1023 · 2¹³ = q − 1` **exactly** (`8380416 = 1023 × 8192`), so
  `Power2Round(q − 1, 13) = (1023, 0)` and `‖s₂‖∞ = 1 ≤ η`. These are secret
  keys in the operational sense, not merely algebraically. The reference FIPS
  204 signer uses `s₁` in `z = y + c·s₁`, `s₂` in the `r₀` check and `t₀` in
  the hint, and **both** witnesses produce signatures on a registrar-chosen
  challenge that the reference verifier and both on-chain subjects accept
  (`SEC_pkcache.t.sol::test_proof_of_knowledge_of_s1_s2_does_not_reject_a_degenerate_key`).

  No amount of rigour fixes this. Make it an exact-relation, norm-bounded,
  zero-knowledge proof of knowledge and it is still answered with no secret
  material, because **the class publishes its own secret keys**. That kills
  every check of the form "prove something about the private key", which is why
  the claim is stated about that whole family rather than about proofs of
  knowledge alone.

  Hardening the *challenge* does not rescue it either. The published fixture
  answers with `z = 0, h = 0`, the most conspicuous signature possible. But a
  registrar that refuses conspicuous responses is defeated by a response with
  `‖z‖∞ = 130,845` (the bound is `γ₁ − β = 130,994`) and 60 real hint bits,
  accepted by all three verifiers
  (`SEC_pkcache.t.sol::test_degenerate_forgery_with_an_ordinary_looking_signature`).

**(3) Bind the validated blob by `EXTCODEHASH`, and re-check the binding at every use.**
Validation happens once, at registration. `verify()` is called later, and it is
called with an *address*. If nothing ties the code at that address to the bytes
that were validated, the validation never reaches the call. So record
`EXTCODEHASH(blobAddr)` next to the address at registration, and require a
match before the address is handed to the verifier. This is exactly the
metamorphic hazard §2.3 closes for the Keccak helper, with the same shape of
regression test
(`SEC_helper.t.sol::test_metamorphic_substitution_is_caught_even_if_functionally_correct`).

Do not confuse binding with de-duplication. They point in opposite directions
and both are right. **De-duplicate on the canonical 1,312-byte `pk` or on
`tr`, never on the blob**, because blob identity is not key identity. See (4).
**Bind on `EXTCODEHASH`**, because one address may hold different blobs over
time and only the validated one may be used.

EIP-6780 (Cancun) closes the classic CREATE2 metamorphic route: a persistent
data contract can no longer be destroyed and re-created with different code at
the same address. But that is a property of the *chain*, not of the registrar.
Pre-Cancun chains still permit it, and the binding costs one storage word and
one `EXTCODEHASH`. A key-integrity invariant should not rest on which hard fork
the deployment chain has taken.

**(4) Enforce canonical coefficients (every one below q).** This is a
**soundness precondition of the verifier's arithmetic**, not hygiene.

**This is not a de-duplication problem.** It is *false* that a
congruent-but-lifted blob "accepts exactly what the canonical blob accepts".
Measured on the deployed artifact, each of `t1hat[0..255] += 4q`,
`t1hat[0] += 511q` and `Ahat[0..255] += 128q` makes a **valid signature
reject**.

The mechanism. The inverse NTT's entry fold computes
`sub(add(u0, ACCQ30), u1)` (`src/InvNtt.sol`), which is exact while
`u1 ≤ ACCQ30 = q·2^30`. Past that, the 256-bit subtraction wraps by 2^256,
which is **not** a multiple of q, so the lane leaves its residue class while
still looking canonical to everything downstream. Obligation O8's accumulator
ceiling sits 1.28× below that cliff, and it does so *only because* every pk
coefficient is < q. That premise is now explicit and falsifiable: `PK_AMAX`
parameterises C9g / O7 / O8 / S14, and both
`C9g.ctl_pk_canonical_premise_rejects_*` and `O8.ctl_amax_rejects_*` assert
that the entry fold's domination **fails** at `PK_AMAX = 2q`. (O7's
lane-locality controls are deliberately stated at `2^40`, where that claim
really is refutable: `O7.lane{0..3}_ctl_lane_locality_needs_a_ceiling`. A
lifted blob breaks the entry fold, not lane locality.)

So a lifted blob is **not a forgery**: no lift makes the verifier accept
anything it should reject. It is **not benign** either. It lies outside every
bound the proofs establish, and it can silently break availability for the key
it impersonates. It also means **blob identity is not key identity**. A
registry that de-duplicates on blob hash, blob address or `EXTCODEHASH` sees
many "different keys" where there is one, so anything keyed off that
(one-registration-per-key, rate limits, revocation lists, replay state) is
bypassed by re-deploying a lifted blob. De-duplicate on the canonical
1,312-byte `pk` or on `tr = SHAKE256(pk, 64)`. Reducing every cached
coefficient mod q at registration collapses the class to one representative,
which is another reason the byte-for-byte `prepare(pk)` check in (1) is the
right one.

**(5) Check `len(pk) == 1312` exactly, before hashing.** Wycheproof
`mldsa_44_verify_test.json` tcId 65 is a *genuine* ML-DSA-44 key with one
trailing `0x00` appended, signed over the real key. A registrar that
"helpfully" truncates an over-long pk builds a cache that **accepts**: two
distinct pk byte strings then collapse onto one on-chain cache, which is
pk-encoding malleability. FIPS 204 §3.6.2 is explicit that other lengths
*shall* be rejected. (The other wrong-length cases reject naturally, because
`tr = SHAKE256(pk, 64)` binds the exact byte string.)

**(6) Keep `μ = SHAKE256(tr ‖ M′, 64)` injective in (tr, M′).** The verifier
reads a fixed 64 bytes of `tr` at a fixed offset in the blob. A registry that
hashes a variable-length `tr` concatenated with anything, without a length
prefix, is unsound for a fraction of keys.

**(7) Keep the blob deployable under EIP-3541** (§4.2). The shipped
`prepare.py` handles this with its `0x00` prefix; a registrar that builds blobs
itself must preserve that prefix.

### 3.2 Bind every external call target by code hash

The shipped verifier already does this for the Keccak-f[1600] helper (§2.3).
Any other build, and any build that splits further helpers out for EIP-170
reasons, must apply the same content pin. A functional self-test of a helper is
**not** sufficient: a helper that answers the probe honestly and lies
afterwards defeats it. A missing helper is already fail-closed, by the
`returndatasize()` checks.

### 3.3 Build without test-only scaffolding

Ship only `verify()`. No gas-instrumentation twins, no cheatcode self-heal
paths. This tree's shipped `src/` is free of both.

There is one deliberate exception, and it is there to be understood rather than
removed. `src/Ntt.sol` and `src/InvNtt.sol` write `gas()` snapshots into an
array supplied by the caller. Those writes are **load-bearing for the formal
apparatus**: obligation C16 anchors its total region partition of the
transforms on exactly those markers, and the EVM-side harnesses (`test/FV4_*`,
`test/FV6_*`) prove the markers are real. The writes go to a caller-owned
buffer, read nothing, branch on nothing, and cost a few gas per transform, so
they cannot affect the verdict. Anyone who wants them gone must first move
C16's anchoring to another pinned feature of the source.

---

## 4. Findings — closed or benign, and the invariant each imposes

### 4.1 Closed: `shake256Fast170`'s write and read footprints are exactly 136 bytes

A writer that touched 160 bytes per block, or a read that ran 24 bytes past the
block, is exactly what the two `formal/hypotheses.py` §4.1 rows exclude. Each
of those behaviours turns on a single address, so one edit would reintroduce
either. Both footprints are pinned there so they cannot regress silently:

* `_squeezeBlockFast170` writes `[outPtr, outPtr+136)`. Its fifth store lands
  flush with the end of the rate block, rewriting three lanes with identical
  bytes. There is no overhang at any `outLen`.
* `_xorBlockFast170` reads `[ptr, ptr+136)`. Lane 16 is taken from the word at
  `ptr+104` rather than `ptr+128`: the same two opcodes, and no load past the
  block.

Both are therefore honestly `assembly ("memory-safe")`, which is also what lets
via-IR emit a memoryguard. `SEC_memsafety.t.sol` asserts that the shipped
squeeze's spill is **exactly 0** at `outLen` 32 / 64 / 136 / 272, so a
regression fails a test rather than shrinking a margin. (The old 160-byte form
survives on purpose in `test/ZZZ_FastKeccak170.sol` as the differential oracle;
nothing in `src/` calls it.)

**One residual read past an object, stated exactly.** `unpackZPacked`'s tail
load reads **23 bytes** past the end of the z object: the last quad is loaded
with `mload(add(src, 27))`, which touches bytes 2,295…2,326 of a 2,304-byte
object. It is a read of bump-allocated memory in the same arena, covered by
`SEC_memsafety.t.sol`'s sentinel probes. A future editor who places an object
immediately after the z region must give it at least 23 bytes of slack.

### 4.2 The EIP-3541 blob prefix — **fixed**

The pk blob's first byte would otherwise be `tr[0]`. When `tr[0] == 0xEF`,
`CREATE` rejects the deployment, because EIP-3541 reserves the `0xEF` prefix,
so roughly 1 public key in 256 would be unregisterable. **Fixed in the shipped
layout:** `prepare.py` emits `0x00 || payload` (20,545 bytes) and `_loadPk`
reads the payload from code offset 1. Confirmed by a deployment test on an ACVP
key with a real `CREATE`.

### 4.3 Non-canonical calldata (note)

Trailing garbage after the ABI-encoded arguments is ignored; that is standard
Solidity behaviour. Signature malleability is unaffected. Every one of the
2,420 signature bytes is load-bearing, verified by mutating each byte in turn,
and the only mutations that still accepted were provable no-ops. The hint
encoding is **canonical**: proved in Lean at the real parameters
(`Encoding.hint_decode_canonical` / `hint_decode_injective`) and enumerated
completely on a scaled model (Z3 E12/E13).

---

## 5. Explicitly cleared (audited, no finding)

- **Purity.** An opcode census of the deployed runtime finds zero
  `SSTORE`/`SLOAD`/`TSTORE`/`TLOAD`/`CREATE`/`CREATE2`/`CALL`/`CALLCODE`/
  `DELEGATECALL`/`SELFDESTRUCT`/`LOG*`/`BALANCE`, and zero environment
  opcodes. `vm.record` shows no storage access. The verdict **and** the gas are
  identical under
  `roll`/`warp`/`chainId`/`fee`/`coinbase`/`txGasPrice`/`prevrandao`/`prank`
  (`SEC_purity.t.sol`).
- **Calldata bounds.** Every out-of-bounds read is unreachable: the length
  check plus solc's own bounds checks. Tested at 2,419 / 2,420 / 2,421
  signature bytes, message lengths 0…65,536, lying length words (2^32, 2^64,
  2^256−1), hostile head offsets and aliased tails. All revert or return false
  (`SEC_memsafety.t.sol`).
- **Memory safety** beyond §4.1: no attacker-controlled length reaches a write
  past an allocation, and the free-memory pointer stays aligned and monotone
  after every kernel.
- **SampleInBall termination.** τ = 39 draws, each accepted with probability at
  least 218/256. The exact dynamic program gives
  **P(needing a second permutation) = 8.17e−62 = 2^−202.9** (Z3 C10/C10b).
  Over 1,024 attacker-chosen challenges the maximum consumed was 52 of the 128
  budget bytes. No cap is needed, and a cap would break FIPS semantics. **This
  also discharges FIPS 204 Appendix C**, which says an implementation *shall
  not* bound SampleInBall below its floor: this implementation refills rate
  blocks indefinitely (`SEC_sampleinball.t.sol`).
- **A missing helper** is fail-closed (§2.3).
- **Hostile-but-nonzero pk blobs** (helper code used as a blob, or a
  0xff-filled blob) never accept and never revert unexpectedly.

---

## 6. On harness failures

A harness that never fails is a harness that isn't checking anything. Four of
the obligations discussed in `FORMAL_VERIFICATION.md` §2 carry notes on exactly
this distinction. An alarm in one of them can indicate a defect in the
*harness* (EVM wrap semantics, or a false `q0 ≤ 43` invariant) rather than in
the verifier, and which one it is has to be chased to ground rather than
smoothed over.

---

## 7. Bottom line

The cryptographic core stands up to everything thrown at it: official NIST
vectors including the negative cases, the Wycheproof negative corpus, thousands
of adversarial tuples, and machine-checked proofs of the arithmetic and of the
encoding layer's canonicality.

The remaining risks are **integration risks**, and they are sharp. A verifier
of this shape is only as safe as three things.

1. The **registration validator** that establishes S1 (§3.1, all seven
   requirements). In particular it needs an explicit degeneracy criterion
   applied to the key: the centred-lift **floor**, plus the KeyGen-seed binding
   wherever completeness is needed.
   **Proof-of-possession does not reject degenerate keys**. Such a key has
   every owner, not none. And
   **No proof about the secret key rejects degenerate keys** either, because
   the class has publicly computable, norm-conforming secret keys.
2. The **content pin on the Keccak helper**, applied here (§2.3), and required
   for any other external call target.
3. A build that **excludes test scaffolding** (§3.3).

Those are stated as requirements, with reproducing tests, rather than left as
assumptions. Two things are still unaddressed and still required before anyone
relies on this: **independent cryptographic review and a professional
implementation audit.** Residual uncertainty: security@fireblocks.com.

---

## Security Considerations (summary for reviewers)

* **Threat model.** All inputs are public and attacker-controlled: the pk-blob
  address, the message, and the 2,420-byte signature. The only trusted object
  is the pk blob's *contents*, and that trust is assumption S1, discharged at
  registration rather than in the verifier.
* **No secrets, therefore no side channels.** Argued in
  `FORMAL_VERIFICATION.md` §6.2. Gas is a deterministic public function of
  public inputs.
* **Soundness of the arithmetic and encoding** is machine-checked (Z3 and
  Lean). The range checks and the acceptance checks are proved equivalent to
  the FIPS rules in both directions, against the emitted code.
* **Known-unsafe without integration work.** See §3 and §7. This is research
  code: **not audited, not deployed.**
* **Attack code in this repository** (hostile helpers, degenerate-key blobs,
  adversarial decoders in the test tree) is prefixed `FOR SECURITY RESEARCH
  ONLY — NOT FOR PRODUCTION USE` and exists only to make the findings
  reproducible.
* **No live key material, credentials or secrets** are committed anywhere in
  this tree, and nothing here protects a deployed key. One exception is the
  breadth corpus `pythonref/assets/PQCsignKAT_Dilithium2.rsp`, which does
  commit 100 ML-DSA-44 `sk` fields as file bytes. Those are test-only keys
  over the NIST KAT harness's public DRBG stream
  (`AES256_CTR_DRBG(bytes(range(48)))`, whose seeds and messages
  `tools/fixtures/kat_build.py` replays and asserts byte-for-byte before use)
  and they correspond to no deployed key. Every other test key is derived at
  run time from a published seed.
