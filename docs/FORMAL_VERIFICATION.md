# Formal & Machine-Checked Verification

> **FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE.** Unaudited research
> code. Machine-checked as described below, but with **no professional
> implementation audit and no independent cryptographic review**.

This document sorts the evidence behind this verifier into four kinds: what is
*proved*, what is *exhaustively checked*, what is *tested*, and what is none of
those. Nothing here rests on "someone read it and it looked right". Every row
comes from a tool you can re-run yourself.

§0 defines the four labels used throughout. §0b is the glossary.

## Contents

- [0. How to read this document](#0-how-to-read-this-document)
- [0b. Glossary](#0b-glossary)
- [0c. Reproducing every result](#0c-reproducing-every-result)
- [1. Assurance ladder, strongest first](#1-assurance-ladder-strongest-first)
- [2. Machine-checked obligations](#2-machine-checked-obligations)
  - [The counts are assertions, not tallies](#the-counts-are-assertions-not-tallies)
  - [What a pin actually pins](#what-a-pin-actually-pins)
  - [What the controls cannot detect](#what-the-controls-cannot-detect)
  - [SMT proofs: universally quantified, unbounded domains](#smt-proofs-universally-quantified-unbounded-domains)
  - [Exhaustive proofs](#exhaustive-proofs)
  - [Exact-arithmetic and code-linkage facts](#exact-arithmetic-and-code-linkage-facts)
  - [The optimized-kernel obligations, O1 to O10](#the-optimized-kernel-obligations-o1-to-o10)
  - [The suite found bugs in itself, which is the point](#the-suite-found-bugs-in-itself-which-is-the-point)
- [2b. Lean 4 development](#2b-lean-4-development)
- [2c/2d. Symbolic execution at the bytecode level](#2c2d-symbolic-execution-at-the-bytecode-level)
- [2e. Mutation testing](#2e-mutation-testing)
  - [A sample is not the campaign](#a-sample-is-not-the-campaign)
  - [Why the killer lists have to be complete](#why-the-killer-lists-have-to-be-complete)
  - [Why forge coverage is not quoted](#why-forge-coverage-is-not-quoted)
- [2f. Hypotheses vs code, checked mechanically](#2f-hypotheses-vs-code-checked-mechanically)
- [3. EVM-corpus verification](#3-evm-corpus-verification)
- [4. FIPS and binding defects found in the state of the art](#4-fips-and-binding-defects-found-in-the-state-of-the-art)
  - [4b. A third defect, in the reference oracle itself](#4b-a-third-defect-in-the-reference-oracle-itself)
- [5. What is not verified, stated explicitly](#5-what-is-not-verified-stated-explicitly)
  - [5.7 The Lean-to-Solidity refinement gap, stated exactly](#57-the-lean-to-solidity-refinement-gap-stated-exactly)
- [6. External state of the art: coverage matrix](#6-external-state-of-the-art-coverage-matrix)
  - [6.1 The matrix, abridged](#61-the-matrix-abridged)
  - [6.2 The constant-time argument, written down](#62-the-constant-time-argument-written-down)
  - [6.3 Gaps left open, and why](#63-gaps-left-open-and-why)

## 0. How to read this document

Every claim below carries one of four labels. They are ranked, and the ranking
tells you how much to trust each result.

| Label | What it means | What it does *not* mean |
|---|---|---|
| **PROOF** | A machine established the statement for *every* input in the stated domain. Four flavours: a solver (Z3), complete enumeration, exact integer arithmetic, or the Lean 4 kernel. | That the domain is the right one, or that the compiled bytecode matches the model. |
| **VALIDATED** | Bit-for-bit agreement with an independent implementation or with official published vectors. | Proof. It holds on the inputs that were run. |
| **TESTED** | Adversarial batteries and fuzzing: things that must be rejected, and are. | Coverage of inputs nobody thought of. |
| **UNVERIFIED** | An acknowledged gap. Listed in §5, not glossed over. | That it is unimportant. |

§1 expands PROOF into its four flavours and says where each is used. A second
question sits next to the label: **would the check fail if the thing it names
were broken?** A check that cannot fail proves nothing. A green test suite that
cannot detect a defect is not evidence.

## 0b. Glossary

The words below are used precisely. Several of them mean nothing outside a
project like this one.

**Obligation.** One named thing the machine has to establish, carrying an ID
such as `S8`, `E15` or `C18`. `formal/z3/verify_all.py` holds 62 of them.

**Conjunct.** One individual claim inside an obligation, reported on its own
line and audited on its own, with an ID such as
`C18.ctl_extracted_value_is_the_proved_value_*`. Most obligations make several
claims at once, so counting only obligations would let a deleted claim hide.

**Pin, pinned.** A value written down in advance (a list of IDs, a hash, a
source expression) so that a later change surfaces as a mismatch, not as a
smaller green number.

**Discrimination control.** A pair of values placed either side of a check's
true boundary: one the check must accept, one it must reject. A check quietly
rewritten so that it always passes will accept the value it should reject, and
fail.

**Vacuity audit.** `formal/z3/vacuity_audit.py`. It deliberately breaks the
models that the obligations are about, then records which conjuncts notice. A
conjunct that no injected defect can break is checking something else, or
nothing.

**Mutant.** A deliberate one-token defect injected into the verifier or its
kernels, catalogued in `formal/mutation/mutants.py` with an ID such as `M44`. A
mutant is **killed** when at least one test fails on it, and **survives**
otherwise.

**Documented equivalent.** A mutant that provably changes nothing observable.
Its survival is the required outcome, and the equivalence argument is written
beside it.

**Mutation campaign.** A run over the entire catalogue
(`run_mutation.py --full`). A routine run samples 8 of 50 mutants instead, so
its numbers are not the campaign's numbers.

**Sole killer.** The one test in the whole corpus that kills a given mutant.
Remove it and the mutant survives, so a sole-killer attribution is causal rather
than coincidental.

**Canary.** A check written so that it *must* fail. If a canary passes, the tool
running it is not really checking anything.

**Hypothesis row.** One line in `formal/hypotheses.py` that ties an assumption
`docs/SAFETY.md` relies on to the code that enforces it, the mutant showing the
enforcement is load-bearing, and the obligation showing the enforcement does
what its name says.

**Trust anchor.** The set of digests everything else is checked against,
re-derived independently before any check runs. It cannot certify itself; that
limit is recorded in §2f.

**Lazy reduction.** Leaving an intermediate value larger than `q` for a few
steps instead of reducing it fully every time, because the arithmetic still fits
the machine word. Cheaper, and correct only inside a proved bound.

**Lane.** One fixed-width slice of a 256-bit EVM word, holding one coefficient.

**SWAR.** "SIMD within a register": packing several coefficients into one
256-bit word and operating on all of them with a single opcode. Sound only if
no operation lets one lane's bits reach a neighbour. That is the *lane
independence* claim proved in several places below.

**Refinement gap.** The distance between a proof about a model and the bytecode
that actually runs. Lean proves things about a model; the EVM runs bytecode.
§5.7 says exactly where that gap is closed and where it is not.

**Oracle, differential test.** An oracle is an independent implementation; a
differential test compares this verifier against one, output by output. A
differential test is only as strong as its oracle. See §4b.

**KAT.** Known-answer test: fixed published input/output pairs, so a wrong
implementation fails against absolute data, not against a peer.

**SMT, Z3.** An automatic prover for formulas over integers and bit-vectors. To
prove a statement, the solver is asked to satisfy its negation; `unsat` means no
counterexample exists anywhere in the domain.

**halmos.** A symbolic executor that runs the *compiled bytecode* on symbolic
256-bit inputs, which is a layer the Z3 models cannot reach (§2c/2d).

## 0c. Reproducing every result

Set `PY=pythonref/myenv/bin/python`, or use any interpreter with `z3-solver`
installed.

```bash
# every fast check in one command.  --full adds the vacuity audit + a SAMPLED
# mutation run (8 of 50 mutants, minutes); --extended runs the FULL 50-mutant
# campaign, the only scope that establishes the published kill rate.
#
# CHECK0_PY is OPTIONAL — check 0 already tries /usr/bin/python3 and friends. If
# you set it, set it to a python3 that is NOT the venv's interpreter: check 0
# wants a genuinely independent second opinion from a different executable.
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh --full
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh --extended

# 62 machine-checked obligations / 794 conjuncts (Z3 + complete-domain enumeration
# + exact integer facts).  Both ID sets are asserted, so a deleted obligation is a
# failure and not a smaller number; every pinned obligation carries discrimination
# controls, so an obligation rewritten into a tautology is a failure too.
MLDSA_REPO=$PWD $PY formal/z3/verify_all.py

# 64 axiom-audited Lean 4 theorems, zero `sorry`, mathlib-free, each statement
# pinned by digest.  Note that `lake build` alone exits 0 even with `sorry` in a
# headline theorem, so the check is:
$PY formal/lean/check_axioms.py

# the EVM test corpus (unit, differential, fuzz, KAT, adversarial, end-to-end)
forge test                                    # 320 tests across 39 suites

# --- the audits that check the checkers ------------------------------------------
$PY formal/z3/vacuity_audit.py --jobs 6       # would each conjunct fail if it were wrong?
$PY formal/mutation/run_mutation.py           # would the test corpus detect a defect?
                                              #   ^ samples 8 of 50 mutants (routine, parallel)
$PY formal/mutation/run_mutation.py --full --jobs 6   # the full 50-mutant campaign
$PY formal/hypotheses.py                      # is every SAFETY.md hypothesis enforced in code?
HALMOS=$(which halmos) $PY formal/mutation/run_halmos.py   # bytecode-level obligations
```

## 1. Assurance ladder, strongest first

| Level | Meaning | Where used here |
|---|---|---|
| **PROOF (SMT)** | Z3 shows the negation is unsatisfiable, so the statement holds for *every* input in an unbounded or very large domain | two-step Barrett reduction (both transforms), NTT lane growth, packed 4-lane non-interference, the strict norm predicate, the range checks |
| **PROOF (exhaustion)** | every input in the domain is enumerated and compared against the FIPS reference | UseHint (all 8,380,417 × 2), z decode + norm (all 2^18), HintBitUnpack canonicality (scaled model), edge cases |
| **PROOF (exact arithmetic)** | closed-form integer facts, with no floating point anywhere | all bound constants, degrees, the NTT lane-growth ceilings, the Barrett safe-domain cliff, the SampleInBall dynamic program |
| **PROOF (proof assistant)** | Lean 4, kernel-checked, zero `sorry`, only Lean's own axioms | the two-step Barrett reduction and 4-lane SWAR lane independence at exact EVM 256-bit semantics; the z decoder; the HintBitUnpack and M′ encoding layer |
| **VALIDATED (oracle equality)** | bit-exact against independent implementations and official vectors | SHAKE256/Keccak-f, NIST KATs, differential against the Python reference and the in-tree reference verifier |
| **TESTED (adversarial)** | must-reject batteries, fuzzing | malformed encodings, bit-flips, hostile environment, hostile helper |
| **UNVERIFIED** | acknowledged gaps | see §5 |

A second question runs at right angles to the ladder: **does the evidence
bite?**

| Check on the checkers | Question it answers | Result |
|---|---|---|
| **vacuity audit, per conjunct** (`vacuity_audit.py`) | would this obligation, and each of its individual claims, fail if the thing it names were broken? | every non-exempt conjunct is killed by at least one injected defect |
| **ID-set assertion** (`META-IDS`) | is the obligation still *there*? | the 62 obligation IDs and 794 conjunct IDs are pinned and self-inclusive; deleting one fails the tally |
| **discrimination controls** | does the obligation still *mean* anything: would it reject a value its predicate has to reject? | every pinned obligation carries accept and reject controls at its true boundary, so a predicate rewritten into a tautology fails |
| **source digests** (`META-PINS`) | is this the same obligation that was pinned? | AST-normalised source-region digests plus a byte digest of every file under `formal/`; tamper-evidence, not tamper-proofing |
| **Lean statement pins** (`check_axioms.py`) | is this the same theorem that was pinned, or one weakened while keeping its name? | 64 statement digests; `sorryAx` is a hard failure; the user-`axiom` scan is de-anchored |
| **mutation testing** (`run_mutation.py --full`) | would the test corpus *detect* this defect? | 45/45 non-equivalent mutants killed; 5 documented equivalents survive. Routine runs sample 8 of the 50 mutants (§2e); this row is the full campaign |
| **hypothesis table** (`hypotheses.py`) | is every hypothesis `SAFETY.md` relies on actually enforced, reachable and load-bearing? | 68 enforced (pattern + count pinned), 7 explicitly ASSUMED |

A position on the ladder is only worth what this second axis says about it. An
obligation that cannot fail is not a proof of anything.

## 2. Machine-checked obligations

`formal/z3/verify_all.py` reports 62/62 obligations and 794/794 conjuncts. The
obligations are proved by Z3, by complete enumeration of a domain, or by exact
integer arithmetic. Every one is pinned by its ID, its source, and control
values at the boundary of the property it claims.

### The counts are assertions, not tallies

`verify_all.py` pins `EXPECTED_OBLIGATIONS` (all 62 obligation IDs) and
`EXPECTED_CONJUNCTS` (all 794 conjunct IDs). Both lists include their own
entries. The script reconciles the printed totals against `len(EXPECTED_*)`.

Deleting an obligation, or a single conjunct inside one, is a failure. It
does not quietly become a smaller green number.

### What a pin actually pins

An obligation is recorded as a **predicate applied to a subject**, together with
control points straddling the predicate's true boundary. The controls are values
the predicate must accept and values it must reject, written out as their own
literal expressions so that editing the predicate does not move them.

That structure catches:

- a predicate rewritten into a tautology, which accepts its negative controls
  and fails;
- a threshold that has drifted and no longer discriminates at the boundary;
- a flipped operator, which fails one side.

SMT obligations carry two extra conjuncts. `claims_discriminate` requires the
claim to be falsifiable once the premises are dropped. `premises_sat` requires
the premise set on its own to be satisfiable, so an `unsat` verdict is never
free. Every exhaustive enumeration is written as a detector parameterised over
its kernel, and each carries a **deliberately broken kernel that it must
catch**.

`META-PINS` (`formal/z3/source_pins.py`) digests the unparsed AST of each
obligation's source region, plus a byte digest of every file under `formal/`.
This is tamper-evidence, not tamper-proofing. An attacker who can edit the suite
can regenerate the table, but the edit then shows up as a visible diff of a
pinned hash.

### What the controls cannot detect

Four blind spots:

1. **Subject substitution.** A predicate fed a trivially satisfying argument.
   The whole-file AST digest and the vacuity audit's kernel mutations answer
   this; the controls do not.
2. **A coordinated rewrite** of a predicate and its controls in one edit.
   Nothing in-band stops it.
3. **An upstream-wrong subject.** The controls say the predicate discriminates,
   not that the modelled quantity is the right quantity.
4. **A conjunct that does not route through the pinned predicate at all.**

Blind spot 4 is how this mechanism gets misapplied. C18's
`ctl_extracted_value_is_the_proved_value` rows pin `_agrees`. A substantive C18
conjunct that spelled its comparison out *inline* would leave the controls
unable to fail when that conjunct failed. All of them route through `_agrees`,
so inverting it fails the accept controls **and** every substantive conjunct.
That is vacuity mutation `V217`.

The reader's rule: whenever you see a `ctl_*` row, check that the predicate it
names is the predicate the claim actually evaluates.

### SMT proofs: universally quantified, unbounded domains

| ID | Statement proved | Covers |
|---|---|---|
| S1, S2 | ∀ e ≤ 15q(q−1) (fwd) / 128q(q−1) (inv), 6 conjuncts: the step-1 product is lane-local (`e·MU33 < 2^64`), its quotient fits the 31-bit mask field, step 1 lands in `[0, 2^33)`, and the two-step output r satisfies 0 ≤ r < 2q | packed NTT reduction |
| S3, S4 | ∀ e in domain: r ∈ {e mod q, (e mod q) + q}: the reduction is *congruence-exact*, not merely bounded | packed NTT reduction |
| S5 | forward NTT (`nttFwV3`) butterfly, 6 conjuncts: the multiplied operand's product ≤ 15q(q−1), the reduction output V in `[0, 2q)`, and both stored lanes `u+V` and `u+2q−V` in `[0, LB+2q)`; lane growth is exactly +2q per layer | lazy-reduction safety |
| S6 | inverse NTT (Gentleman–Sande) over the layers that use Barrett, K = 2^(L−1) ≤ 64, 6 conjuncts: difference lane `u+Kq−v ∈ (0,2Kq)`, product ≤ 128q(q−1) (literally C9d's domain), Barrett output in `[0,2q)`, sum lane < 2Kq | lazy-reduction safety |
| S6b | inverse NTT **layer 8** is not a Barrett layer: with sum lanes < 128q and twiddle < q, every 64-bit SWAR lane product is < 2^64, so the per-lane `mod` sees non-overlapping lanes | lazy-reduction safety |
| S7 | the packed two-step reduction on the word the transform actually holds: four 64-bit lanes, no spreading (60 conjuncts modelling the emitted `mul`/`shr(33)`/`and(QHATM31)`/`sub`, twice): the packed product fits 2^256, every lane's product stays in its lane, every lane's quotient field is exactly that lane's quotient, no lane borrows, and every reduced lane is recovered in place below 2q | SWAR correctness |
| S8 | the single-comparison strict-FIPS norm test, modelled with EVM wrapping `sub` plus unsigned `lt`, is equivalent to `‖z‖∞ < γ1 − β` for all 2^18 fields (the form the reference decoder carries) | signature validity |
| S8b | the shipped decoder's packed z block (`sub(Z_UOFF,V)`, the one conditional subtraction of q selected by bit 32, and `and(add(o,Z_NLO), sub(Z_NHI,o))`) for four arbitrary 18-bit fields at EVM semantics (96 conjuncts): per lane, no borrow, no carry on any flag word, the flag is a bit, the mask exposes exactly that bit, the flag is `[u ≥ q]`, the stored lane is canonical and equals the centered map, each edge bit is its comparison, and the AND of the two is the strict FIPS rejection | signature validity, SWAR correctness |
| S11, S11b | UseHint intermediates: q0 ∈ [0,44], r0 ∈ [0,2γ2), and q0 = 44 *only* at r = q−1, so the edge-case correction is exact, not heuristic | w1 correctness |
| S13 | the reduction's safe-domain guard: correct below `BARRETT_FIRST_FAIL` and wrong at it (r = 2q on the nose; minimality machine-proved) | lazy-reduction margin |

### Exhaustive proofs

| ID | Domain enumerated | Result |
|---|---|---|
| E1 | UseHint: all 8,380,417 values × both hint bits, against the FIPS reference | 0 mismatches |
| E2 | UseHint output ∈ [0,44) for 6-bit packing safety: the complete domain, folded into E1's sweep | holds |
| E3 | z centered map: all 2^18 fields against FIPS BitUnpack | 0 mismatches |
| E4 | strict norm predicate: all 2^18 fields | 0 mismatches |
| E3b | the shipped decoder's SWAR conditional subtract equals the FIPS BitUnpack centered map: all 2^18 fields, every output canonical, z = 0 field → 0 | 0 mismatches |
| E4b | the shipped decoder's bit-32 norm check equals strict FIPS: all 2^18 fields, with each window edge moved by ±1 in its own control | 0 mismatches |
| E5b | the packed norm check's boundary at both tails in both directions (v ∈ {78, 79, 262065, 262066}): the far tail is reached by a different constant and a different opcode, so it is a separate claim | holds |
| E5 | boundary regression: \|z\| = γ1−β **rejected**, γ1−β−1 accepted | holds (this is the SOTA bug, §4) |
| E6 | z = 0 field canonicalizes to 0, not q | holds (the other SOTA bug, §4) |
| E9a/b | Barrett dense sweep of both full domains (200k points plus all edges): 4 conjuncts each, so a mutation that breaks only one is attributable | holds |
| E12 | **HintBitUnpack canonicality**, complete over all 8^6 = 262,144 encodings of a scaled model (k=2, ω=4, index alphabet 0..7): every accepted encoding maps to a distinct hint set, 0 collisions | no malleability |
| E13 | every accepted HintBitUnpack encoding equals the canonical encoder's output | round-trip |
| E14 | `M′ = 00‖len(ctx)‖ctx‖M` is injective in (ctx, M) over a complete small domain, and the `01` HashML-DSA domain is constructed and shown disjoint (both non-empty) | FIPS 204 §5.2 |

### Exact-arithmetic and code-linkage facts

**C1/C1b. The two reduction constants.** `MU33 = ⌊2^33/q⌋ = 1025` is step 1's
coarse Barrett constant, chosen so the lane product fits 64 bits. `⌊2^23/q⌋ = 1`
is step 2's, which is why step 2's multiply is elided. That second fact is a
fact about `q = 2^23 − 2^13 + 1`.

**C9e/C9h. Lane locality and the mask width.** `max·MU33 < 2^64`, and
`64 − 33 == 31`, and `qhat < 2^31` **iff** the lane product is lane-local. One
31-bit-per-lane mask therefore does two jobs: it extracts the quotient and it
blocks the neighbour.

**C9a–e. The NTT lane ceilings.** 17q < 2^28 forward, 256q < 2^31 inverse, plus
the cross-lane-carry margin.

**C9f, C9g. The two whole-transform lane-growth inductions.** S5 and S6 prove
one layer's step; these two compose those steps over a schedule.

- C9f runs the forward schedule (`LB₁ = q`, `+2q` per layer, 8 layers). It
  asserts the premise `LB ≤ 15q` at every layer, the maximum Barrett input
  15q(q−1) below the cliff, and the final lane 17q < 2^28. The forward output is
  not canonicalised: lanes below 17q are exactly the domain O7 and O8's matvec
  admits.
- C9g runs the inverse schedule. Entry is a `mulmod`/`addmod` fold at L1+L2 over
  raw accumulator lanes ≤ `ACC_ENTRY`, which is O8's ceiling; the per-step proof
  is S14. From there `K_L = 2^(L−1)`, with Barrett at L3 through L7 only. C9g
  asserts that the entry offsets dominate, that the block exit < 2q meets L3's
  < 4q premise, the maximum Barrett input 128q(q−1), the maximum sum lane
  256q < 2^31, and that layer 8's lane products fit 64 bits.

**C11a–d. The reduction's safety margin.** The inverse NTT's worst product sits
only **1.144×** below `BARRETT_FIRST_FAIL`. The other cliff (the first input
whose step-1 product leaves its 64-bit lane) is higher, so `r < 2q` is the
binding constraint. One extra unreduced layer would silently break the field
arithmetic. Any re-tuning of the NTT must re-derive this budget.

**C10, C10b. SampleInBall.** The exact dynamic program gives
P(second permutation) = 8.17e−62 = 2^−202.9 and E[rejection bytes] = 42.22.

**C15b, C15c. The two wire widths every bound is stated at.** The pk blob
layout width, and the exactly-2,420-byte signature.

**C16. The proof-to-code link for the NTT.** C16 reads the shipped Yul; it does
not restate facts about it in Python.

- It extracts, from both shipped copies of each transform (`src/Ntt.sol` and
  `test/ZZZ_NttVariants.sol`; `src/InvNtt.sol` and `test/ZZZ_InvNtt.sol`), the
  marker-delimited block structure. Per block it extracts the offset constants
  used, the number of reduction steps (both steps, counted separately and
  required to agree), and the number of `mod`s.
- It works over comment- and string-stripped code, anchored on the
  `mstore(add(PR, …), gas())` profiling markers, not on a comment.
- The two transforms are fused differently, and the extraction pins each shape
  separately. The inverse runs its eight layers as four *radix-4 fused* passes:
  a quad of four words loaded once, two layers on the stack, one store. The
  forward runs as three passes: two *radix-8* passes (an octet of eight words,
  three layers on the stack) plus the in-word L7+L8.
- A block therefore names all of its layers' offsets. The extracted inverse
  schedule is `K = 1,2 | 4,8 | 16,32 | 2,64,128`, where `K_L = 2^(L−1)` and
  `mod` appears only in the final block. The forward schedule is `+2q` at every
  layer of every block: 24 sum stores paired with 24 offset-difference stores.
  The difference is pinned as the whole `sub(add(X, TWOQ4), t0)` expression, so
  the subtraction *direction* is pinned too, over a closed enumeration of the
  octet's twelve minuend names.
- The partition is *total*: head, blocks, tail, and head and tail must be inert.
  It counts occurrences, not names. In a radix-2^L fused block,
  `2 × offset occurrences == L × stores`. A dropped `+Kq` is therefore visible
  even though its constant name survives elsewhere. So is a block that has
  quietly become one layer shallower.

**C18. The proof-to-code link for the FIPS validity checks.** Without C18,
nothing under `formal/` reads `src/Decode.sol` or `src/MLDSA44Verifier.sol` at
all, even though those two files carry every validity check the verifier
applies. Four one-token mutations in them leave every obligation, conjunct and
hypothesis row green, and one of the four is a strong-unforgeability break.

The class of defect at stake: **a pin over expression text is not a pin over the
constant value**, and a numeric fact restated in Python is not a fact about the
shipped code.

So C18 extracts every number from the source:

- the 18 SWAR/decode constants, as the arithmetic they have to be;
- the four factors whose product is z's 1,024 coefficients (check sites × loop
  trips × lanes × polynomials);
- both padding-shift boundaries, with both operands;
- the mod-44 magic shift and subtrahend, from all eight unrolled sites;
- the signature length, the ω check, the `tr` offset and width;
- `PK_SIZE`, compared against **C15b's** width arithmetic, not standing beside
  it.

`ctl_extracted_value_is_the_proved_value` is the discrimination control for the
extraction method itself. Four whole-file normalised digests are the residual,
exactly as C16's are. C17's magic constant and shift are likewise *read* from
`Decode.sol`, not restated.

**The same shape recurs one file over.** `src/FastKeccak170.sol` and
`src/IMLDSAVerifier.sol` are otherwise the only `src/` files outside both C16's
and C18's digests, and `FastKeccak170.sol` runs on every call. C18 reads them
too, by value:

- FIPS 202's `0x1f` domain byte and `0x80` final bit, and the word offset the
  final bit lands in;
- the 136-byte rate, at all six sites that spend it, and the squeeze-block
  round-up;
- the 800-byte raw-permutation protocol on both sides of the `staticcall`;
- both `returndatasize()` fail-closed checks;
- the `input.length != 800` dispatch guard, required to equal the
  raw-permutation length (that collision is what the guard exists to avoid);
- the round-up mask of the deliberately non-zero-filled return buffer;
- the two lane-16 windows (`ptr+104` and `outPtr+104`), each required to end
  flush with the rate block;
- the 64-bit lane mask.

The interface file contributes its digest plus the assertion that the shipped
entry point *is* the declared `external view` one. That mutability keyword is the
whole of the "safe to call via `STATICCALL`" claim.

**E15. The same validity check, semantically.** A digest tells you something
changed, not what broke.

FIPS 204 Alg. 21 lines 16–18 are discharged branchlessly over three words of
32/32/16 index bytes, so their correctness is a claim about shift arithmetic at
`c3 = 32` and `c3 = 64`. No test, mutant or obligation in the tree reaches the
`c3 ≥ 64` branch on its own.

E15 enumerates the **complete** reachable grid: every weight `c3 ∈ [0, ω]`
against every dirty padding position `p ∈ [c3, 80)`. That is 81 canonical
acceptances and 3,240 rejections, checked against a model of the shipped Yul
whose numbers are C18's extracted ones, with ten reject controls: the
demonstrated defect and its neighbours, each of which survives everything else.
`test/SEC3_HintPaddingGrid.t.sol` runs the same grid **on chain** against the
shipped decoder, so the model and the artefact are checked apart.

E15 also carries the **memory-safety** half of the same decoder, which the grid
provably cannot reach. The index scan runs to
`cut := sub(cut, mul(sub(cut, 80), gt(cut, 80)))`, and C18's pattern captures
both operands, including the `gt` threshold. A pattern that left the threshold
uncaptured would be verdict-equivalent either way. The clamp is not there for
the verdict. It is what keeps the scan of a *rejected* encoding inside the
80-byte index array, inside a block annotated `memory-safe`. At `gt(cut, 255)`
the scan reads about 171 bytes past that object. The conjunct
`scan_clamp_keeps_the_index_scan_inside_the_index_array` therefore states the
consequence over the **whole byte domain** `[0, 255]`, not over the grid: every
counter in the grid is `≤ ω`, so a control stated there could not come out
false.

### The optimized-kernel obligations, O1 to O10

These live in `formal/z3/kernel_obligations.py` and pin the opcode-swept
decode, UseHint and matvec kernels of `src/Decode.sol`.

- **O1–O6** (`useHintSwar`): the SWAR UseHint and w1Encode.
  Division-by-multiplication over four lanes, the `>=` comparator, the `mod 44`
  output, and the 6-bit packing.
- **O7, O8** (`matvecRow`): the pre-shifted lane masks (`mul(a_k, wz & L_k)`
  lands the product in its own lane) and the lazy accumulator's no-overflow
  bound. Both are stated over a pk-coefficient ceiling `PK_AMAX`, which is an
  **explicit premise**, not a literal `Q − 1` buried in the arithmetic. That
  matters because a congruent-but-lifted pk blob passes every on-chain validity
  check. `O8.ctl_amax_rejects_*`, together with
  `C9g.ctl_pk_canonical_premise_rejects_*`, asserts that the entry-fold
  domination **fails** at `PK_AMAX = 2q`. See `SAFETY.md` §3.
- **O9** (`unpackZPacked`): the packed store is a disjoint OR of canonical
  lanes.
- **O10** (`unpackZPacked`): the 18-bit field extraction. Twelve byte terms at
  pairwise disjoint left shifts, plus one 18-bit-per-lane mask, is FIPS 204
  BitUnpack. This is complete over the whole 2^72 nine-byte domain. Disjointness
  makes both maps bytewise additive (its own conjunct on each side), and a map
  that is a sum of nine per-byte functions is determined by the 9 × 256
  coordinate sweep the obligation runs. The three bytes that straddle a field
  boundary are emitted by one multiply each (`b * (2^s + 2^t)`), covered by
  three more conjuncts: the constants are exactly those two powers, the identity
  `b*(2^s+2^t) == or(shl(s,b), shl(t,b))` is enumerated over all 256 byte
  values, and the fused pairs are tied back to the doubled entries of the
  twelve-term model. A constant encoding some *other* pair of shifts therefore
  cannot pass by agreeing with itself.

Two of these obligations are provably *stronger than the code needs*. That is a
finding about the code, not about the tests. **O1** pins a SWAR-division
intermediate that the pipeline is self-correcting for a `+1` error in (mutant
`M28`). The `s1 == 44` correction is dead code given the unconditional final
`mod 44` (mutant `M26`, on the reference kernel). Neither is a defect. Both mean
that a *failure* of the corresponding obligation would not by itself imply the
verifier is wrong.

The shipped kernel takes that observation into account: `useHintSwar` performs
one `mod 44` on `S1 + ADJ`, not two. Obligation **C17** enumerates the
magic-number division that evaluates it (exact for every `T < 131`, against a
reachable maximum of 87) and the fold itself. See docs/EXPLAINER.md §7.1.

### The suite found bugs in itself, which is the point

Four obligations failed on their first run, and all four were defects in the
*verification harness*, not in the verifier.

- The model used Python's unbounded integers where the kernel relies on the
  EVM's wrapping `sub` plus *unsigned* `lt`. That wrap is exactly how one
  comparison covers both norm tails.
- The model asserted `q0 ≤ 43`, where the truth is `q0 = 44` exactly at r = q−1,
  which the kernel corrects.

Fixing them produced *stronger* obligations. S8, E4 and E5 now model EVM
semantics, and S11 plus S11b prove the UseHint correction is exactly reachable
and exactly targeted. A harness that never fails is a harness that is not
checking anything.

## 2b. Lean 4 development

`formal/lean/` holds 64 axiom-audited theorems with zero `sorry`, no mathlib,
and each statement pinned by digest.

`lake build` on its own is not enough. `#print axioms` is an `info:` message and
`sorry` is a *warning*, so a planted `sorry` leaves `lake build` at exit 0.
`formal/lean/check_axioms.py` is the machine check. It fails if:

- a source file contains `sorry`, `admit`, `native_decide`, a user `axiom`
  (matched by a de-anchored `\baxiom\b`, so `private axiom` and `@[simp] axiom`
  do not evade it), or an `unsafe` / `@[extern]` / `@[implemented_by]`
  declaration;
- `lake build` exits non-zero;
- any theorem depends on anything outside `{propext, Quot.sound,
  Classical.choice}`, above all `sorryAx`;
- the audited theorem-name set differs from
  the pinned `EXPECTED_THEOREMS` (64 entries);
- any audited theorem's *statement* differs from its pinned digest.

It forces a full elaboration in a **cache-free sandbox**, because a warm `.lake`
cache replays stored traces that the digests do not cover. The check's output is
therefore a statement about the sources it just digested, not about a build
artefact. mathlib is not used at all; this is a self-contained Lean-core
development.

The 64 theorems are in three modules, and all three are about **EVM opcodes and
FIPS encodings**, not idealised mathematics.

**`Mldsa/Barrett.lean` (27 theorems).** The two-step lazy Barrett reduction and
SWAR lane independence, proved about the exact 256-bit opcode chain:

```lean
def W       : Nat := 2 ^ 256
def evmMul (a b : Nat) : Nat := (a * b) % W
def evmShr (k a : Nat) : Nat := a / 2 ^ k
def evmSub (a b : Nat) : Nat := (a + (W - b % W)) % W
def barrettEVM (x : Nat) : Nat := evmSub x (evmMul (evmShr 33 (evmMul x mu)) q)
```

Wrap-around is part of the definition, and the proof *shows* that it does not
occur (`barrettEVM_eq_nat`):

- `no_borrow` and `second_no_borrow`;
- `barrett_forward` and `barrett_inverse` (`barrettEVM x < 2q` on 15q(q−1) and
  128q(q−1) respectively);
- `barrettNat_congr` and `barrett_inverse_congr`: this is a *reduction*, so
  `≡ x (mod q)`;
- `qhat_lt_two_pow_31` and `lane_product_lt_two_pow_63`;
- `swar_step1_lane_independent` and `swar_lane_independent`: the one-step and
  4-lane SWAR reductions are exactly the pair and quad of scalar reductions;
- `firstFail_breaks`, `invMax_lt_firstFail` and `margin_guard`: the domain
  restrictions are non-vacuous, at the 1.144× cliff.

**`Mldsa/Decode.lean` (26 theorems).** The shipped packed z decoder, which is
the check that decides signature validity on every call. Proved in exact
`Nat` arithmetic with the EVM's `div` and `mod` semantics:

| Theorem | Statement | Closes |
|---|---|---|
| `canon_zero_field` | the `z = 0` field (`v = γ₁`) canonicalises to **0**, not to `q` | the ZKNox decoder defect (EXPLAINER §10) |
| `flag_iff_u_ge_q`, `canon_lt_q`, `canon_closed_form` | the single conditional subtraction *is* `mod q`, and the stored lane is FIPS BitUnpack's centred map | signature validity |
| `flag_no_carry`, `lo_no_carry`, `hi_no_borrow` | each of the three flag words stays below `2^33`, so bit 32 is a flag and not a carry | SWAR correctness |
| `lo_iff`, `hi_iff` | bit 32 of `o + Z_NLO` and of `Z_NHI − o` is exactly its comparison | the strict norm window |
| `reject_iff_fips` | their AND is exactly the FIPS 204 rejection `‖z‖∞ ≥ γ₁ − β` | the libcrux off-by-one class |
| `boundary_low_rejected` / `_high_rejected`, plus the two `_inside_accepted` | both tails of the boundary are rejected and both neighbours accepted | strictness, pinned at four witnesses |
| `swar_z_lane_independent`, `addSplit4`, `subFromRep4`, `flag_word_lane_fits` | the packed word is four independent copies: neither the `add` nor the `sub` moves a bit across a lane boundary | the four-lane claim S8b makes symbolically |
| `fused_split`, `fused_disjoint`, `zp2/zp4/zp6_is_two_powers` | `b·(2^s + 2^t)` is the OR of the two shifted copies, and the three shipped constants are those powers | the fused byte placement (O10) |

This module is the Lean twin of Z3 S8b (the same statement, symbolically, for
four symbolic lanes) and of E3b, E4b and E5b (the same statement by complete
enumeration of all 2^18 fields). Three methods, because a proof, a symbolic
model and an enumeration fail differently.

**`Mldsa/Encoding.lean` (11 theorems).** Every publicly known ML-DSA *verifier*
bug is in the encoding layer (see §6), so the encoding layer is proved directly:

| Theorem | Statement | Closes |
|---|---|---|
| `hint_decode_canonical` | any 84-byte string FIPS 204 Alg. 21 accepts *is* the canonical encoding of the hint set it decodes to | the draft-FIPS-204 hint-malleability class, at the real parameters (k = 4, ω = 80) |
| `hint_decode_injective` | two encodings that decode to the same hint set are equal, so no hint re-encoding | encoding-layer strong unforgeability |
| `hint_weight_le_omega` | every accepted encoding has total weight ≤ ω | FIPS Alg. 21 line 4 |
| `strictInc_rejects_repeat` / `…_permutation` | the strict-increase check rejects a repeated index and a reordering | the RustCrypto CVE-2026-24850 class |
| `padding_gate_rejects_nonzero` | the trailing-zero check is load-bearing | FIPS Alg. 21 lines 16–18 |
| `decRows_canonical`, `all_zero_replicate` | the decode is total and canonical on the empty and degenerate rows | FIPS Alg. 21 |
| `mprime_injective` | `M′ = 00‖\|ctx\|‖ctx‖M` determines `(ctx, M)`, so context binding holds | FIPS 204 §5.2 |
| `ctx_len_gate_is_load_bearing` | *without* the `\|ctx\| ≤ 255` check the byte-level `M′` is provably ambiguous (explicit witness pair) | why that check is soundness logic |
| `pure_prehash_disjoint` | the `0x00` / `0x01` domain byte makes pure ML-DSA and HashML-DSA representative sets disjoint | FIPS 204 Alg. 3 vs Alg. 5 |

The HintBitUnpack canonicality statement is checked a second way, by complete
enumeration on a scaled model, in Z3 E12 and E13.

**Not formalized, out of scope, stated plainly:** SHAKE and UseHint
bit-exactness (covered by KATs and the exhaustive Z3 sweeps); S1 pk-blob
integrity; the NTT as a *transform* (proved sound and oracle-equal, not proved
to be the negacyclic transform, §5); and the link from these `.lean` models to
the deployed bytecode (§5.7).

## 2c/2d. Symbolic execution at the bytecode level

Halmos proves properties about the **compiled bytecode** over symbolic 256-bit
inputs, which is the layer the Z3 models cannot reach. `test/FV_Kernels.sol`
covers the centered maps, both norm predicates as iffs, the 18-bit BitUnpack
extraction, UseHint against FIPS with output ∈ [0,44), `qhat < 2^32`, the range
checks as iffs, and the 6-bit w1 packing. Each comes with
**deliberately-failing canaries**, because a suite with no canaries cannot be
trusted.

The **Barrett family** (the tight `r < 2q` bound and its SWAR forms) *times
out* under halmos. Bit-blasting is the wrong engine for a linear-integer fact
about a floor division, and the result is `unknown` under yices, z3 and
bitwuzla alike. Those obligations are left in place, still timing out,
deliberately, so that the tool limitation stays visible. The arithmetic they
cover is discharged instead by `Mldsa/Barrett.lean` at exact EVM semantics, plus
the fast bytecode-level refinement obligations of `test/FV2_Barrett.sol`.

Measured (halmos 0.3.3, `--loop 16`, 300 s solver timeout; artefacts
`formal/mutation/halmos_fv1.json` and `halmos_fv2.json`; driver
`formal/mutation/run_halmos.py`):

| contract | file | result |
|---|---|---|
| FVKernels | `test/FV_Kernels.sol` | **9/18 PASS**; `c1, c2, c1a, c1c, c1e, c3, c4, c6, c7` TIMEOUT |
| FVCanaries | `test/FV_Kernels.sol` | **6/6 FAIL**, as required |
| FV2Barrett | `test/FV2_Barrett.sol` | **13/15 PASS**; `w3` and `w11b` TIMEOUT |
| FV2Canaries | `test/FV2_Barrett.sol` | **7/7 FAIL**, as required |

`w0`, `w1`, `w2`, `w4`–`w11` and `w12` all return in seconds where the direct
statement returns nothing in five minutes. The split does not cover `w3` and
`w11b`: those still time out, and no claim in this repository rests on either.
Nothing here is reported as a pass that was really a timeout. The driver tags
every verdict, because halmos prints a timeout as `0 passed; 1 failed`.

One step no tool performs: composing "Lean proves `prod ≤ x` and
`x − prod < 2q`" with "halmos proves the bytecode computes `sub(x, prod)`". That
composition is a single modus ponens, written out at the obligation site and
done by a reader.

Results from this layer:

1. `useHintSwar`'s canonical-input precondition is load-bearing and undetectable
   downstream. It diverges from FIPS at the very first non-canonical input, and
   because the final `mod 44` is unconditional the output *stays in range*. So
   soundness rests entirely on the upstream canonicalizing validity checks, both
   of which are verified.
2. The reduction's safe domain is exactly 1.144× above the inverse NTT's worst
   product.
3. The strict/loose norm composition removes precisely the FIPS-forbidden set,
   with no over-rejection. Verified exhaustively.

## 2e. Mutation testing

Coverage tells you which lines ran. Mutation testing tells you whether the suite
would *notice* a defect.
`formal/mutation/` holds a **50-mutant catalogue** that injects deliberate
defects into the security-critical sites: range checks, norm windows,
hint-encoding checks, the UseHint edge case, Barrett constants, the c̃
comparison, the pk-blob size pin, the length checks, and the reference decoder
used as the differential oracle.

The driver never edits the repository. It mirrors the tree into a scratch
workspace, asserts each pattern's occurrence count before patching (a stale
catalogue aborts), and treats a `FAIL` that names no test as `UNATTRIB`, which
is excluded from the denominator. A transient failure therefore cannot inflate
the score.

**45/45 non-equivalent mutants are killed.** Five mutants are documented
equivalents that must survive because they change nothing observable. Examples:
`useHintSwar`'s `s1 == 44` correction (dead code given the final `mod 44`), the
self-correcting SWAR division constant, and the pk-blob liveness check subsumed
by the exact size pin. The equivalence proofs are written next to the mutants
they justify, in `formal/mutation/mutants.py`.

### A sample is not the campaign

That 45/45 is a claim about a **full campaign**:
`run_mutation.py --full`, all 50 mutants.

Each mutant is a complete via-IR rebuild at `optimizer_runs = 10000`, so a full
campaign costs about 3.4 h of mutant time: 12,348 s measured across the 50,
median 242 s each. At `--jobs 6` that is roughly 40 minutes of wall clock. A
release-candidate cost, not an every-edit cost.

The driver therefore defaults to a **seeded random sample of 8**, run in
parallel. Each `--jobs N` worker gets its own workspace, because mutants patch
files in place. The two scopes are kept visibly apart:

| scope | invocation | headline it may print |
|---|---|---|
| routine | `run_mutation.py`, `run_checks.sh --full` | `SAMPLE 8/50 (seed=S)`: every statistic labelled *sampled*, plus a pointer to `--full` |
| campaign | `run_mutation.py --full`, `run_checks.sh --extended` | `45/45 non-equivalent KILLED` |

A sampled run never overwrites `mutation_results_final.json`, which is a
full-campaign artefact, and never prints the campaign's headline. A sampled
scrollback therefore cannot be quoted as the campaign.

Parallelism changes no verdict. Verdict classes, the `--fail-fast` retry and the
exit rules are all per mutant, so `--full --jobs N` agrees with a serial run.

**Sampling is stratified and reproducible.** The catalogue is grouped into its
seven families (NORM, HINT_ENC, USEHINT, NTT, VERIFIER, REFERENCE, EQUIVALENT).
Each family is shuffled by `random.Random(seed)`, and the sample is drawn
round-robin across families. A sample of 8 therefore spans all seven families
and always includes at least one pinned equivalent mutant, whose **survival is
the required outcome**. The seed is printed at the start, in the summary banner
and on the last line, and a sampled failure is replayed exactly with the command
the run itself prints:

```bash
$PY formal/mutation/run_mutation.py --sample 8 --seed <the printed seed>
$PY formal/mutation/run_mutation.py --ids M49            # then narrow to the one that failed
```

### Why the killer lists have to be complete

The killer lists are an attribution, so they are complete.

`test/MUT_Gaps.t.sol` publishes that every `test_MUT_M<nn>_*` names the mutant
it kills, and `formal/hypotheses.py::mut_attribution_problems()` *checks* that
against the artefact. The artefact therefore has to be usable as ground truth.
Two things would stop it being that, and neither is present:

- storing `killers[:12]` turns any list of twelve into a sample that reads like
  a set;
- letting a full run inherit `--fail-fast` cancels the forge run, so the
  recorded set becomes an *order-dependent prefix*. Measured: under
  `--fail-fast`, mutant `M39` lists seven tests; under `--no-fail-fast` its
  killer set is exactly one test, and not the test named after it.

So there is no cap, `--full` implies `--no-fail-fast`, and the artefact carries a
`_meta` block (mode, fail-fast setting, and the SHA-256 of `mutants.py` and
`test/MUT_Gaps.t.sol`). The check refuses a stale or sampled artefact instead
of quoting one.

**What that check establishes is co-occurrence, not causation, and for most
mutants that is weak.** The rule it enforces is "the named test must appear in
that mutant's killer list", and **23 of the 45 non-equivalent mutants are killed
by 24 or more tests each** (`M64` by 66). For those, almost any test name in the
corpus would satisfy the rule. The published wording is literally accurate about
what is checked. The impression it leaves (*this test is why that mutant dies*)
is stronger. The difference is said plainly here.

The one case where co-occurrence *is* causation is a killer set of size one:
remove that test and the mutant survives, by definition. Those are also the
fragile attributions, so they are pinned by value in
`formal/hypotheses.py::SOLE_KILLER_PINS` and checked in both directions. A
mutant that becomes single-killed and is not pinned fails the check; a pin that
no longer describes a single-killed mutant fails it too.

**`M44` and `M39` are each killed by exactly one test in the whole corpus, and
it is the same test**: `test_MUT_M44_hint_weight_omega_bound`. `M39` has no test
named after it, so the attribution check never examined `M39` at all, and
weakening that one test silently un-kills two catalogued mutants. `M20` and
`M21` share a sole killer likewise, and `M25` has one of its own.

A causal check for the rest (re-run the corpus with one test removed, per
mutant) is **not** implemented. It costs a full campaign per candidate test and
buys nothing for the 23 mutants whose killer sets are large, which is where the
weakness actually lies.

### Why forge coverage is not quoted

`forge coverage` is not quoted, for structural reasons:

- coverage instrumentation changes the bytecode this project deliberately pins
  (the helper code hash, an embedded data constant);
- `--ir-minimum` makes the exhaustive 2^18-field obligation exceed the block gas
  limit;
- Solidity source-line coverage does not see inside `assembly`, and the kernels
  are about 90% inline Yul.

Mutation testing is the replacement, and it is strictly stronger. It found a
defect class no coverage number reaches: a window constant broken in **one of
its four SWAR lanes**, which leaves 256 of the 1024 z coefficients silently
unchecked and changed no test result. `test/MUT_Gaps.t.sol` closes that class
(both boundaries, both directions, at every lane of the first and last quad of
all four polynomials), and mutants `M60` (lane 3 of `Z_NLO` blanked), `M61`
(lane 1 of `Z_NHI` relaxed by one) and `M63` (lane 2 of `Z_M18` narrowed to 17
bits) are its regression.

## 2f. Hypotheses vs code, checked mechanically

`SAFETY.md`'s argument depends on hypotheses that the *implementation* has to
discharge: "the verifier builds M′ itself", "the helper is bound by code hash",
"‖z‖∞ < γ1 − β is strict". Prose cannot check that those are enforced.
`formal/hypotheses.py` does.

Each row has three columns: a literal pattern with an expected occurrence count
in a named source file (a tripwire, not a description); the mutant ID that shows
the check is load-bearing; and the obligation that shows the check does what its
name says.

**68 hypotheses are ENFORCED** (pattern plus count pinned)
and **7 are explicitly ASSUMED**. `ENFORCED` and `ASSUMED` are the status labels
the tool itself prints. The seven assumptions are S1's registration-time half (no
on-chain check can discharge it), the NTT layer schedule (extracted from source,
not derived from bytecode; see §5), and the bootstrap assumptions of the formal
apparatus itself: the trust anchor cannot certify itself, and the interpreter,
its standard library, the Z3 package and the Lean toolchain are environment
assumptions.

**The same tool checks this document.** Three mechanisms run over
`FORMAL_VERIFICATION.md`, `SAFETY.md`, both `README.md`s, `run_checks.sh`,
`RESULTS.md`, `run_mutation.py`, `test/MUT_Gaps.t.sol` and
`.github/workflows/ci.yml`.

**`doc_id_problems()`.** Every obligation ID, conjunct ID, mutant ID and
vacuity-mutation ID cited in those files must exist in the set that defines it. A
`*` is a glob that must match at least one pinned conjunct, and `{m..n}` is a
range in which *every* member must match. A citation to something nobody wrote
reads exactly like a citation to something that passes, and there were three: in
`SAFETY.md`, in this file, and in `run_checks.sh`. None is reproduced literally
here, because this check has no exemption list, on purpose, so a document cannot
both cite a dead ID and pass. Out of scope, deliberately: bare Lean theorem
names, which are indistinguishable from the hundreds of Solidity and Python
identifiers these documents also cite. Fully qualified `Mldsa.*` names *are*
checked.

**`doc_count_problems()`.** Every published count must equal what the tool that
produces it says **now**, and the sentence stating it must still exist, because
a deleted claim is drift too. More than twenty published numbers had drifted
under the earlier version of this check, four of them inside `run_checks.sh`'s own
printed labels: the mechanism that stops a sampled run being quoted as the full
campaign, where drift is worse than drift in prose. The hypothesis-row counts and
the EVM corpus's test and suite counts are derived too: `evm_corpus_counts`
reproduces `forge test`'s totals statically. No number in this document is typed
by hand.

The **headline gas figure** is one of those derived numbers. Without the
derivation it would sit outside every mechanical guard. It is re-derived from
`test/E2E.t.sol`'s `VERIFY_GAS_MEASURED`, which that suite asserts against the
EVM inside a ±0.5 % band, and each of its six published sentences (one in
`README.md`, five in `EXPLAINER.md`) has its own pattern, so deleting a sentence
is drift too. `formal/hypotheses.py --print-counts` prints all of them.

**`mut_attribution_problems()`.** `test/MUT_Gaps.t.sol`'s test *names* are
claims, so they are checked, not asserted. Every `test_MUT_M<nn>_*` must
appear in `M<nn>`'s killer list in `mutation_results_final.json`, and every
`test_equivalent_M<nn>_*` must name a pinned equivalent mutant that survived.
`doc_id_problems()` only asks whether a cited ID *exists*, so without this check
a test named after a mutant it does not kill would pass. See §2e for why the
artefact cannot be the ground truth either.

## 3. EVM-corpus verification

`forge test` runs 320 tests across 39 suites. Bit-exactness and behaviour are
pinned by oracle equality, not by inspection.

**Keccak-f[1600] and SHAKE256.** Bit-exact against ZKNox's `f1600` *and*
Optimism's production `LibKeccak` on random chained states. Every generated
binary is re-checked against a FIPS-202 model. SHAKE256 KATs include the exact
832-byte ML-DSA shape (`FUZZ_Shake.t.sol`, `ZZZ_fastkeccak170.t.sol`).

**NTT, forward and inverse.** Oracle-equal to the vendored ZKNox transforms
`nttFw` and `nttInv` (`test/vendor/ZKNOX_NTT_dilithium.sol`) on pseudorandom
inputs and on the all-(q−1) worst case; round-trip identity; canonical-output
assertions (`ZZZ_nttvariants.t.sol`, `ZZZ_invntt.t.sol`).

*Read the chain, because one of its links is a digest and not a test.*
`test/ZZZ_NttVariants.sol` and `test/ZZZ_InvNtt.sol` are **not** oracles. C16
requires them to be byte-identical to `src/Ntt.sol` and `src/InvNtt.sol` modulo
comments, and that is what lets them stand in for the shipped files. So the chain
is: *shipped ≡ test-tree copy* (C16, by normalised whole-file digest), then
*copy ≡ vendored ZKNox transform* (the two suites above).

**The E2E differential therefore does not independently cover the NTT.**
`test/ZZZ_E2ERef.sol` imports `nttFwV3` and `nttInvV3` from those same copies, so
a defect present in *both* copies cancels out of the shipped-versus-reference
comparison. Four things cover it instead:

1. the vendored-oracle equality above, which is an independent implementation;
2. the **absolute** must-accept vectors in the same E2E suite: the NIST KAT and
   the FFI-signed vectors are fixed data, not a differential, and they fail if
   the transform is wrong at all;
3. `FV3`, `FV4` and `FV6` below;
4. the NTT mutant family (`M49`, `M50`, `M57`, `M58`, `M59` on the shipped
   transforms and `M29`/`M30` on the copies), all killed.

*Why `ZZZ_E2ERef.sol` is not switched to the vendored transforms.* It could be;
the layouts convert cleanly. It is not, for two reasons. The reference verifier
is simultaneously the **pre-extraction gas baseline** the headline figures are
measured against, and the vendored `nttFw` costs 182,470 gas per transform as
this tree compiles it (`testGasV1Baseline` in `test/ZZZ_nttvariants.t.sol`,
fresh memory, via-IR like everything else here), so nine of them would move
the baseline. And it would add no coverage the chain above lacks: a defect in
both copies is a defect in one *file*, and that file is already tested against
the vendored oracle directly.

Three further NTT suites:

- `test/FV3_NttLaneBounds.t.sol` pins the S5/S6/C9f/C9g/C16 lane-growth facts at
  EVM semantics: per-layer offset constants, both Barrett domains at their
  endpoints, the cliff at `BARRETT_FIRST_FAIL`, and fuzzed butterfly steps.
- `test/FV4_NttScheduleExtraction.t.sol` checks that the profiling markers C16
  slices on are executed in order with work between every consecutive pair, and
  re-derives each schedule C16 *rejects*.
- `test/FV6_NttRegionCoverage.t.sol` executes the shipped transforms to show that
  a payload C16 must reject (a `+128q` entry lift, for instance) really is
  unsound even though it does **not** change the transform's output. That is
  exactly why a source-reading obligation is necessary and no functional test
  suffices.

**Decode kernels.** Bit-equal to the reference decoder across FFI-signed
vectors, malformed-encoding rejection cases, and boundary regressions
(`ZZZ_decode*.t.sol`, `Kernels.t.sol`).

**End-to-end.** The verifier accepts the NIST KAT vector and FFI-signed vectors,
and rejects bit-flips in c̃, z, h and the message, as well as wrong keys, wrong
lengths and weight-0 hints (`E2E.t.sol`, `FUZZ_MLDSA44.t.sol`). A message-length
sweep over 0…206 bytes empirically confirms the 9-permutation model and the
+1-permutation step at each 136-byte boundary.

**NIST ACVP.** The ML-DSA-44 sigVer set including must-reject cases
(`ACVP_MLDSA44.t.sol`). All **25 keyGen** key pairs are re-derived and verified
on chain: both the public-key transform (ExpandA → InvNTT, `t = 2^d·t1`, `tr`)
and a produced signature (`FV2_AcvpKeyGen.t.sol`).

Internal-interface ACVP cases, which hand the implementation a pre-formatted
`M′`, are **not applicable** here, deliberately. This verifier implements the
*external* interface and constructs `M′` itself. Accepting a caller-supplied `M′`
is the domain-separation hazard FIPS 204 §5.2 warns about, and it is exactly
what `mprime_injective` and `pure_prehash_disjoint` guard against.

**Wycheproof.** The ML-DSA-44 corpus: **180 cases, 176 representable**, with the
file stored byte-for-byte and its SHA-256 recorded in `provenance.txt`
(`SEC2_Wycheproof.t.sol`). The four `IncorrectPublicKeyLength` cases carry a
1,311- or 1,313-byte pk, which cannot become the fixed-size 20,544-byte blob
either verifier consumes, so they are **registration-layer** cases and run as
such (`test_wycheproof_wrong_lengths`). The 176 are round-robin sharded 4 × 44,
and each shard asserts its own 44 **on chain**.

Read the "0 divergences" figure exactly. The expected verdicts are Wycheproof's
own `result` field **narrowed by this interface's empty-context rule**: a case
Wycheproof marks `valid` that carries a non-empty `ctx` becomes must-reject
here. Two cases flip that way (tcId 3 and 4, labelled `:ctxbind`), so the
on-chain expectation is 75 must-accept and 101 must-reject, where the file's own
census over all 180 is 77 and 103. That is real domain-separation coverage, not
a skip, but it is not Wycheproof's verdict unmodified.

A separate divergence is against the *oracle*, not the corpus:
`dilithium_py` accepts tcId 18 (§4b), and the expectation stays Wycheproof's.

## 4. FIPS and binding defects found in the state of the art

The same checks found defects in other implementations. ZKNoxHQ/ETHDILITHIUM,
the 8.09M baseline, contains two latent compliance defects. Both are fixed here
and both are worth upstreaming.

1. `useHintDilithium(r = q)` returns 44, an out-of-domain w1 value where FIPS
   requires 0. It is latent in their pipeline, but their own `unpackZ`
   *produces* the value q, because it encodes z = 0 as q, so any reuse is
   hazardous. This kernel is FIPS-correct here (E1/E6).
2. The z-norm check accepts ‖z‖∞ = γ1 − β, which FIPS 204 requires be
   **rejected**. Honest signers never emit the boundary, so KATs cannot catch
   it; a crafted vector would. This verifier implements the strict test, proved
   equivalent to FIPS: S8/E4/E5 for the reference decoder's per-coefficient
   form, S8b/E4b/E5b for the shipped four-lane one.

### 4b. A third defect, in the reference oracle itself

`dilithium_py` (the Python ML-DSA in `pythonref/`, which is the test tree's
ground truth) **accepts** a Wycheproof case with a *repeated hint index*
(`mldsa_44_verify_test.json` tcId 18). Its `_unpack_h` does not enforce FIPS 204
Alg. 21's strict index ordering, so a signature can be re-encoded into a second,
distinct byte string that still verifies. That is the CVE-2026-24850 class, in
the oracle.

This verifier **rejects** it: `unpackHFast`'s strict-increase check is
the FIPS rule, pinned by `SEC2_Wycheproof.t.sol` and `SEC2_Fips204Gates.t.sol`.

**A differential test is only as strong as its oracle**: every "0 divergences"
result that used `dilithium_py` alone is blind to exactly this bug class, and it
took an independent negative corpus to see it. **ACVP is not sufficient**: this
signature passes ACVP-style checking and fails FIPS. Worth upstreaming to
`dilithium-py`.

## 5. What is not verified, stated explicitly

1. **Compiler and toolchain.** Obligations are proved about the *algorithms and
   their EVM semantics*, and validated against the compiled artifacts by
   differential tests. solc 0.8.30's codegen is not itself verified. Mitigation:
   bit-exact oracle equality on the compiled bytecode, plus the halmos
   bytecode-level pass.
2. **Enrollment integrity (S1).** The pk data contract is trusted to be the
   deterministic transform of the standard pk. A registration-time validator is
   a hard requirement (`SAFETY.md` §3) and is not part of the verifier.
3. **Generated code provenance.** The Keccak helper's permutation core
   (`helpers/f1600_core.hex`) was emitted by a generator that no longer exists;
   it lived in a session scratchpad, and the recipe survives in
   `test/ZZZ_FastKeccak170.sol`. The core is pinned as a verbatim artifact
   (sha256 in `tools/build_f1600_batch.py`) and verified *behaviourally*:
   FIPS-202-model equivalence in the builder's mini-EVM, two independent
   reference implementations, and the SHAKE256 KATs. The shipped runtime
   (`helpers/f1600_170.hex`) *is* reproducible: `tools/build_f1600_batch.py`
   rebuilds it deterministically from the core, and `--check` re-derives and
   compares byte-for-byte. Auditors review the builder, the pinned core bytes and
   the equivalence tests, not 21,622 bytes (~21.6KB) of bytecode.
4. **No professional audit, no deployment.** These are research artifacts.
5. **The reference oracle is not itself verified,** and it was found wrong on one
   FIPS rule (§4b). Differential results against it alone inherit its blind
   spots, which is why the independent negative corpora exist: Wycheproof, and
   the ACVP invalid cases.
6. **The NTT layer schedule is extracted from source, not derived from
   bytecode.** S5 and S6 prove one layer's step; C9f and C9g compose those steps
   over a *schedule*. C16 extracts that schedule from the shipped Yul and
   rejects re-tunings (a ninth layer, a payload before the first marker, a
   dropped per-lane offset), and `FV4_` and `FV6_` re-derive the rejections at
   EVM semantics. Two things remain assumed: that a marker-delimited block *is*
   the layer group it claims to be (the markers are author-placed, and the passes
   are fused), and that a block mentioning an offset constant applies it to every
   lane of that layer's butterfly (the extraction sees which constants a block
   uses and how often, not the data flow between them). Nothing derives the
   schedule from *bytecode*. Registered as an `[ASSUMED]` row in
   `formal/hypotheses.py`.
7. **The NTT is not proved to be the negacyclic transform (P40).** It is proved
   *sound* (no overflow, congruence-exact reductions) and *equal to a
   reference* on many inputs, which is weaker. Closing it needs a Lean or Coq
   development of the transform itself. Not attempted.
8. **The halmos artefacts are a dated measurement, not a check that fails the
   build.**
   `halmos_fv1.json` and `halmos_fv2.json` carry no digest of the harnesses they
   describe, and `run_halmos.py` is invoked by neither `formal/run_checks.sh` nor
   `.github/workflows/ci.yml`. So nothing re-runs it and nothing detects the
   files going stale. That is how a previous `halmos_fv2.json` came to record
   `14/14` for a harness a rewrite had re-cut. The driver aborts (exit 4) when
   the discovered `check_*` set differs from its pins, so a renamed or deleted
   obligation is caught the next time anyone runs it. A changed *body* is not.
   This is left open deliberately: wiring it in means a hard CI dependency on a
   solver that times out on nine of these obligations. And **no claim in this
   repository rests on a halmos verdict**. `test/FV2_Barrett.sol`, the one file
   that would otherwise be an exception to that sentence's spirit, has
   independent standing (see §5.7). `formal/mutation/RESULTS.md` states all of
   this in full.
9. **Crash-safety of the obligation suite is a property of the catalogue, not of
   the code.** `verify_all.py` contains about 100 division and modulo operations
   whose divisor is not a literal and which sit outside any `try`. So "a mutated
   input makes an obligation fail rather than crash the suite" holds because of
   what the vacuity catalogue happens to contain. The 232-mutation audit reports
   0 crashes today, and a crash is a hard error there.

   What an unhandled crash would look like is **measured**. Absent the handler
   described below, a `ZeroDivisionError` in `ref_decompose` aborts the suite
   after emitting 575 `[PASS]` rows and 0 `[FAIL]` rows. Nothing silently
   starves, but an operator triaging the crash scrolls up into a wall of green,
   which is the wrong signal at the wrong moment.

   The handler sits at one site, not 62. `main()` catches any exception
   escaping the four obligation groups, emits an explicit
   `[FAIL] <id>  CRASH  never ran` row for **every** obligation that reached no
   verdict, and then prints a banner saying the run is void. Wrapping all 62
   obligation bodies instead would be 62 chances to draw the `try` boundary
   wrong, and it would let the suite keep proving things on top of a kernel that
   had just raised. C16, C18 and E15 keep their own body wrappers, which are a
   different thing: they turn an unreadable *source* into a failure and let the
   rest of the suite run.

### 5.7 The Lean-to-Solidity refinement gap, stated exactly

Lean proves things about a *model*; the EVM runs *bytecode*.

**Closed, for the arithmetic in the Barrett family.** `Mldsa/Barrett.lean`
models the EVM opcodes with their exact 256-bit wrap-around semantics, so its
theorems are about the opcode chain and not about ℤ. The remaining link is
*syntactic*: that the Yul `sub(x, mul(shr(33, mul(x, MU33)), Q))` compiles to
`MUL`/`SHR`/`MUL`/`SUB` in that order, and that nothing wraps.
`test/FV2_Barrett.sol` discharges exactly that at the bytecode level. Composing
the two is one modus ponens, done by a reader.

**What "Closed" rests on.** `FV2_Barrett.sol` reasons about its own copies of
the kernel. Absent the two checks below, nothing would establish that those
copies are the shipped ones, nothing would run the file (22 `check_*`, 0
`test*`, so `forge test` compiles it and runs nothing), and nothing would digest
it. Two checks carry it, and **neither is a halmos verdict**, so this claim and
§5 item 8 are consistent:

- `FV_Kernels.t.sol::testFuzz_FV2_barrett_kernels_are_the_shipped_reductions`:
  the copies equal `src/Ntt.sol::lazyBarrett` and `src/InvNtt.sol::invLazyBarrett`
  over the full documented domain, so the character-identity the header asserts
  is a *test*;
- C18's `fv2_*` conjuncts: a residual digest over the whole normalised file,
  its `22 check_* / 0 test*` census, and the presence of both shipped kernel
  forms, so a changed `check_*` *body* is a failed obligation.

The halmos runs remain what §5 item 8 says they are: a dated measurement, not a
check that fails the build.

**Open, and precisely where.** For the encoding module the gap is a named pair
(Lean function against Solidity function) with **no mechanised link**. What
stands in for a refinement proof is complete enumeration plus the FIPS 204
acceptance-rule suite plus Wycheproof plus mutants:

| Lean object | Solidity object | what stands in for a refinement proof |
|---|---|---|
| `Encoding.decRows` (FIPS 204 Alg. 21) | `unpackHFast` (`src/Decode.sol`, assembly; `test/ZZZ_decode.t.sol`, Solidity) | complete enumeration of a scaled model (E12/E13), the FIPS-204 acceptance-rule suite, Wycheproof, mutants M20/M21/M24 (reference) and M43/M44/M45/M46 (shipped) killed |
| `Decode.canon` / `Decode.reject` (z canonicalization) | `unpackZPacked` (`src/Decode.sol`, `test/ZZZ_decode2.t.sol`) | E3/E6 over all 2^18 fields; halmos centered-map checks; mutants M11–M13 |
| `Encoding.mprime` | `_computeMu` (`src/MLDSA44Verifier.sol`) | E14; the ACVP HashML-DSA must-reject corpus |
| `Barrett.mu` / `Barrett.d` and the `Decode` constants | the constants in the sources | `verify_all.py` recomputes them independently |

**What would close them.** Not more tests. Either a verified extraction
(generate the Yul from the Lean definitions, or import the compiled bytecode into
Lean, which needs an EVM semantics in Lean at the fidelity required for `mcopy`,
`calldatacopy` and memory aliasing) or a symbolic executor with an
integer-arithmetic backend, not a bit-blaster. That second capability is
exactly what §2c/2d shows to be missing from yices, z3 and bitwuzla for a single
Barrett bound, let alone for a 256-term inner product.

## 6. External state of the art: coverage matrix

Nobody has published a full machine-checked FIPS 204 **verifier** correctness
proof. What exists splits cleanly. The gaps are not where one would guess.

| Effort | Tool | What is actually proved | What is explicitly not |
|---|---|---|---|
| Cryspen **libcrux ML-DSA** | hax → F* | panic freedom, bounds preservation, functional correctness of **field arithmetic, NTT, serialization** against hand-written F* specs | the verifier's *control logic*, sampling, hint decode; side channels. Both of its published ML-DSA bugs were in the unverified part |
| formosa-crypto/**dilithium** (EasyCrypt) | EasyCrypt | mechanized **ROM CMA-security** of Dilithium, including a fix to the CMA→NMA reduction; HVZK simulator; NMA → MLWE + SelfTargetMSIS | the **abstract** scheme only: no t1/t0 compression, no hints, no byte encodings; no implementation |
| formosa-crypto/**formosa-mldsa** | Jasmin | — | README: *"has not been formally verified or proven"* |
| pq-code-package/**mldsa-native** | CBMC + HOL Light / s2n-bignum + Isabelle | **UB and memory-safety of all C**; **functional correctness, memory safety and constant-time of all AArch64/x86-64 assembly**; Isabelle proofs of the Decompose/Power2Round rounding identities and the Barrett/Montgomery core | source-level end-to-end spec equivalence; power/EM, microarchitectural, fault |
| **HACL*** | F*/Low* | memory safety, functional correctness, secret independence; **no ML-DSA**. Its verified SHA-3/SHAKE is the nearest machine-checked reference for our sponge | ML-DSA absent |
| aws-lc-verification, LibMLKEM (SPARK) | SAW/Cryptol, NSym, SPARK | SHA-2/HMAC/AES-GCM; ML-**KEM** in SPARK | **no ML-DSA** |

The bug record is short and it points at one place: the draft-FIPS-204 missing
strict hint-index ordering check ("not strongly existentially unforgeable");
RustCrypto CVE-2026-24850, which accepted a repeated hint index; libcrux's
final-row ω overflow check and its `2γ1 − β` dead-code norm check; FIPS 204
§3.6.2 length checks; and `dilithium_py`'s repeated-hint acceptance (§4b).

**Every publicly known ML-DSA *verifier* bug is in hint decoding, the ‖z‖∞
bound, or length checking**, and those three are the most heavily covered areas
here.

### 6.1 The matrix, abridged

Legend: ✅ covered · ◐ partially · ➜ moved to the registration layer
(`SAFETY.md` §3) · N/A with reason.

| ID | Property | Status | Where |
|---|---|---|---|
| P1 | pk length exactly 1312 | ➜ | the verifier consumes a pre-expanded blob; blob size checked exactly (`SEC_pkcache.t.sol`). The registrar must check `len(pk) == 1312` **before** hashing (Wycheproof tcId 65) |
| P2 | signature length exactly 2420 | ✅ | `SEC2_Fips204Gates`, `SEC_memsafety`, C15c; returns false on a wrong length |
| P3 | `\|ctx\| ≤ 255` | ✅ | Lean `ctx_len_gate_is_load_bearing`, E14. The shipped verifier is empty-context by construction and forms `M′` itself |
| P4 | exact length checking, no silent truncation or extension | ✅ | `SEC_memsafety` (2419/2420/2421, lying length words, hostile offsets) |
| P6 | decoded hint indices cannot drive an out-of-bounds write | ✅ structurally | an index only feeds `1 << idx` into a 256-bit mask; there is no index-addressed store |
| P8 | cut counters non-strictly monotone; a decrease means reject | ✅ | `SEC2_Fips204Gates`, including the false-reject (empty-row-legal) direction |
| P9 | `y[ω+i] > ω` means reject, in **every** row including the last | ✅ | the libcrux #1348 bug |
| P10 | indices strictly increasing within a polynomial | ✅ | Wycheproof tcId 18; Lean `strictInc_rejects_repeat` |
| P11 | the strict-increase test resets at each row | ✅ | false-reject direction |
| P12 | trailing padding bytes all zero | ✅ | Lean `padding_gate_rejects_nonzero` |
| P14 | total weight ≤ ω | ✅ | Lean `hint_weight_le_omega` |
| P15 | one accepted encoding per hint set (canonicity) | ✅ proved | Lean `hint_decode_canonical` and `hint_decode_injective`; Z3 E12/E13 |
| P16 | z BitUnpack total and in range | ✅ | E3, E6 (all 2^18) |
| P18–P20 | ‖z‖∞ over centered reps; strict `< γ1 − β = 130994`; boundary rejected | ✅ | S8, E4, E5 plus S8b, E4b, E5b (the libcrux #1347 / SOTA bug class) |
| P21 | full 32-byte c̃ comparison | ✅ | `_finalHash` compares all 32 bytes |
| P22 | do **not** add signer-side checks to Verify | ✅ | no `‖r0‖∞` or extra weight test exists; the must-accept cases would false-reject if one were added |
| P28–P31 | SampleInBall exactly Alg. 29; τ = 39 non-zeros in {−1,+1}; rejection sampling; **no cap below FIPS Table 3** | ✅ | `SEC_sampleinball.t.sol`; C10 gives P(second block) = 2^−202.9 |
| P33–P37 | Decompose special case; centered r0; UseHint branches including `r0 = 0` → decrement; output ∈ [0,43] | ✅ | S11/S11b, E1 (all 8,380,417 × 2), E2 |
| P41 | reductions preserve the residue class | ✅ | S3/S4 (congruence-exact over the full domain) |
| P42 | no word overflow, no cross-lane carry | ✅ | S1–S7, C9a–e, C11a–c |
| P40 | NTT and NTT⁻¹ correctness and round-trip | ◐ | oracle equality and round-trip; **not proved as a transform**; stated gap (§5) |
| P43/P44 | `tr = H(pk,64)`; `μ = H(tr‖M′,64)`; domain bytes and context binding | ◐ ➜ / ✅ | byte order and lengths verified in-verifier; that `tr` really is `H(pk,64)` is part of S1. `M′` binding proved (Lean `mprime_injective`, `pure_prehash_disjoint`; E14) |
| P45/P46 | `c̃′ = H(μ ‖ w1Encode(w1), 32)`; SHAKE correct at all lengths and rate boundaries | ✅ | `_finalHash`; 251 ACVP SHAKE-256 KATs plus randomized |
| P47/P48 | degenerate `t1 = 0` keys forgeable; `pkDecode` totality | ➜ | known, not fixable in-verifier; the reference verifier accepts them too; `SAFETY.md` §3 makes rejection a registration requirement |
| N1–N8 | constant time, zeroization, RBG, skDecode, signer-side bounds, fault injection, timing, panic freedom | N/A / reframed | see §6.2: no secrets; the panic-freedom analogue is that `verify` returns a boolean and reverts only on documented conditions, with gas invariant under every environment opcode |

### 6.2 The constant-time argument, written down

Timing and side-channel properties are the headline result of most external
ML-DSA verification work, and none of it applies here. The reason belongs on the
record.

1. **There are no secrets.** The verifier's entire input is the pk-blob address,
   the message and the signature. All of it is calldata or chain state, public by
   construction. No key, no nonce, no randomness.
2. **Data-dependent control flow exists and is fine.** SampleInBall's rejection
   loop branches on `c̃`, which is 32 bytes of the public signature. Gas is
   therefore a public function of public inputs, which is what the EVM guarantees
   anyway.
3. **Nothing branches on anything secret-ish.** The only conditionals are on
   decoded signature fields, the pk blob, and lengths. `SEC_purity.t.sol` pins
   that the verdict **and** the gas are identical under every environment
   cheatcode.
4. **The one non-vacuous caveat.** FIPS 204 §3.6.3 warns that a verifier's
   intermediates can reveal `M`, `σ` or `pk` where signatures are bearer tokens.
   On chain that is moot, because the transaction already publishes them. It
   stops being moot inside a ZK circuit or over a private message, and anyone
   doing that must re-open this section.

### 6.3 Gaps left open, and why

- **P40. The NTT is not proved to be the negacyclic transform.** It is proved
  sound and reference-equal. A full transform proof is a multi-week Lean or Coq
  project, not attempted.
- **Everything upstream of the blob (P1, P17, P24–P27, P39, P43, P47, P48).**
  These are real obligations that this verifier structurally cannot discharge,
  because caching the expanded key is the entire optimisation. They are collected
  as the registration validator's contract (`SAFETY.md` §3).
- **The verifier implements ML-DSA with an empty context only.** A non-empty
  context cannot be expressed, and a caller who "just folds ctx into the message"
  builds a non-FIPS construction. This is a *functional* narrowing, not a
  soundness hole, and it is stated in the interface docs.
- **Refinement gap.** §5.7.
