# `formal/` — the verification artifacts, and the checks on those checks

Everything in this directory is a tool you can re-run, not a claim you have to
take on trust. [`docs/FORMAL_VERIFICATION.md`](../docs/FORMAL_VERIFICATION.md)
is the narrative of what is proved versus what is tested. Its §0b glossary
defines the vocabulary. This file is the map.

The words below are used precisely.

* An **obligation** is one named thing the machine has to establish, carrying an
  ID such as `S8` or `C18`.
* A **conjunct** is one individual claim inside an obligation, reported and
  audited on its own line.
* To **pin** something is to write its value down in advance (an ID list, a
  hash, a source expression) so that a later change shows up as a mismatch, not
  as a smaller green number.
* A **discrimination control** is a pair of values placed either side of a
  check's true boundary: one the check must accept, one it must reject. A check
  quietly rewritten so that it always passes will accept the value it should
  reject, and fail.

## The map

```
formal/
├── run_checks.sh             Every fast check in one command; this is the CI
│                            entry point.  Check 0 re-derives the trust-anchor
│                            digests in a fresh `python -I -S`: once under an
│                            interpreter found outside this repository, once
│                            under $PY.  It refuses to let any check run until
│                            the two answers agree with the pinned anchors.
├── z3/
│   ├── verify_all.py        62 machine-checked obligations (794 conjuncts),
│   │                        including META-IDS and META-PINS.  Every conjunct
│   │                        is reported and audited separately.  Both ID sets
│   │                        are asserted and include their own entries, and
│   │                        every pinned obligation carries discrimination
│   │                        controls, so an obligation rewritten into a
│   │                        tautology fails.  Its first ~90 lines are the
│   │                        trust anchor: it digests source_pins.py's code,
│   │                        `exec`s the bytes it digested instead of importing
│   │                        them, digests its own whole AST, and exits on any
│   │                        mismatch — before any statement of the suite runs.
│   ├── source_pins.py       META-PINS: AST-normalised source digests, with no
│   │                        exemptions, plus a byte digest of every file under
│   │                        formal/.  This is tamper-evidence, not
│   │                        tamper-proofing.  Regenerate with --write.
│   ├── kernel_obligations.py  O1 to O10: the optimized decode, UseHint and
│   │                        matvec kernels of src/Decode.sol.
│   └── vacuity_audit.py     Defects injected into the obligation suite itself,
│                            from a catalogue whose own ID set is pinned.  It
│                            answers, per conjunct, "would this fail if it were
│                            wrong?", and it reports blind-spot and crash
│                            categories.  VT01 to VT09 attack the pinning
│                            machinery itself.
├── lean/                    64 axiom-audited theorems, zero `sorry`, no mathlib
│   ├── README.md            What each module proves, theorem by theorem, plus
│   │                        the axiom and `sorry` policy the check enforces.
│   ├── check_axioms.py      The check.  `lake build` exits 0 with `sorry` in
│   │                        a headline theorem; this does not.  It pins every
│   │                        audited theorem's statement by digest as well as
│   │                        its name, and forces a full elaboration in a
│   │                        cache-free sandbox, because a warm `.lake` cache
│   │                        would replay traces the digests do not cover.
│   └── Mldsa/
│       ├── Barrett.lean     The lazy Barrett reduction and SWAR lane
│       │                    independence, under exact EVM 256-bit semantics.
│       ├── Encoding.lean    FIPS 204 Alg. 21 HintBitUnpack canonicality and
│       │                    injectivity; M' injectivity; pure and prehash
│       │                    domain separation.
│       ├── Decode.lean      A model of the shipped four-coefficients-per-word
│       │                    z decoder, in exact Nat arithmetic with EVM div/mod
│       │                    semantics.  The refinement gap between that model
│       │                    and the bytecode: FORMAL_VERIFICATION §5.7.
│       └── Audit.lean       `#print axioms` on every audited theorem, at build
│                            time.
├── mutation/
│   ├── mutants.py           Deliberate defects in the verifier and its
│   │                        kernels, with equivalence proofs written beside
│   │                        the few that cannot be killed.
│   ├── run_mutation.py      The driver.  One scratch workspace per parallel
│   │                        worker; occurrence-count assertions before
│   │                        patching; a FAIL that names no failing test is
│   │                        UNATTRIB rather than a kill; it never edits the
│   │                        repository.  It defaults to a seeded sample of
│   │                        8 of the 50 mutants.  `--full` is the campaign and
│   │                        the only scope that prints
│   │                        the published 45/45 kill rate.
│   │                        `--full` implies --no-fail-fast and
│   │                        stores complete killer lists, because
│   │                        hypotheses.py checks test/MUT_Gaps.t.sol's
│   │                        attributions against them.
│   └── run_halmos.py        Bytecode-level obligation driver: one process per
│                            function, with a verdict tag on every result.
├── acvp/
│   └── keygen_build.py      The 25 NIST ACVP ML-DSA-44 keyGen key pairs, as an
│                            on-chain fixture, with provenance and an oracle
│                            check.
└── hypotheses.py            docs/SAFETY.md hypothesis <-> enforcing check <->
                             evidence.
```

## Run everything

```bash
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh --full       # + vacuity audit + a sampled mutation run (8 of 50 mutants)
LAKE="$HOME/.elan/bin/lake" ./formal/run_checks.sh --extended   # + vacuity audit + the full 50-mutant campaign
```

`CHECK0_PY` is optional; check 0 already tries `/usr/bin/python3` and friends.
If you do set it, set it to a python3 that is **not** the one `pythonref/myenv`
was created from. Check 0 needs a second opinion from a *different executable*,
and `CHECK0_PY=$(command -v python3)` on an asdf or pyenv machine resolves to
the very interpreter the venv was built from. Check 0 refuses in that case, and
says so.

`--full` is the routine deep run. It samples the mutation catalogue, and it says
that it did. Only `--extended` runs the whole campaign, and only the campaign
establishes the published 45/45 kill rate. The campaign is 50 full via-IR
rebuilds: 12,348 s = 3.43 h of mutant time in `mutation_results_final.json`,
median 242 s each, and about 40 minutes of wall clock at `--jobs 6`.

Or run the pieces separately, with `PY=pythonref/myenv/bin/python`:

```bash
MLDSA_REPO=$PWD $PY formal/z3/verify_all.py   # 62/62 obligations, 794/794 conjuncts
$PY formal/z3/source_pins.py                  # region + file pins
$PY formal/lean/check_axioms.py               # 64 audited theorems + 64 statement digests
$PY formal/hypotheses.py                      # 68 enforced + 7 ASSUMED
$PY formal/z3/vacuity_audit.py --jobs 6       # every conjunct load-bearing
$PY formal/mutation/run_mutation.py           # sample: 8 of 50 mutants, parallel, seeded
$PY formal/mutation/run_mutation.py --full --jobs 6   # the campaign: every non-equivalent
                                              #   mutant killed (45/45)
```

`ENFORCED` and `ASSUMED` are the two status labels `hypotheses.py` prints for
each row: enforced by a pinned pattern in a named source file, or explicitly
assumed with a written reason.

`MLDSA_REPO` is only needed when `verify_all.py` runs from outside the
repository. Obligation **C16** reads the shipped NTT sources to check their
per-layer offset constants against the S5/S6/C9f/C9g induction. If the source
cannot be read, C16 **fails**. It is never a silent skip.

### Regenerating the pins after a deliberate change

`formal/z3/source_pins.py` holds the META-PINS tables. Three files pin each
other, so regeneration needs a fixpoint: the two tables and the six `ANCHOR_*`
lines of `run_checks.sh` are blanked wherever a file digests itself. After
reviewing the diff:

```bash
$PY formal/z3/source_pins.py --code-digest         # -> SOURCE_PINS_CODE_SHA256 in verify_all.py
$PY formal/z3/source_pins.py --check-script-digest # -> RUN_CHECKS_SH_SHA256 in verify_all.py
$PY formal/z3/source_pins.py --anchors             # -> the ANCHOR_* lines in run_checks.sh
$PY formal/z3/source_pins.py --write               # -> PINS + FILES, last (round-trip verified)
```

After a change to the emitted obligation set, regenerate the pinned ID lists
with `$PY formal/z3/verify_all.py --print-ids`, and the hypotheses row set with
`$PY formal/hypotheses.py --print-rows`. All of these are meant to be loud.

## What the CI checks defend against, and what they cannot

An obligation that cannot fail is not a proof. A green suite that cannot detect
a defect is not evidence. So:

* the obligation and conjunct ID sets are asserted, which means deleting a check
  fails the suite rather than shrinking a number;
* every pinned obligation states inputs its predicate must reject;
* every SMT claim must still be falsifiable once its premises are dropped;
* the source of the whole apparatus is digested and re-derived out of band
  before any check runs;
* the Lean check re-elaborates from source in a cache-free sandbox rather than
  trusting a build cache.

What this **cannot** see is stated precisely in
[`docs/FORMAL_VERIFICATION.md`](../docs/FORMAL_VERIFICATION.md) and in the
`[ASSUMED]` rows of `hypotheses.py`. The trust anchor cannot certify itself.
The interpreter, its standard library, the Z3 package and the Lean toolchain
are environment assumptions. Whoever controls the process that launches the
checks controls what those processes see.

Closing that last one means running the checks from a process the tree did not
start, on a checkout it did not create.
[`.github/workflows/ci.yml`](../.github/workflows/ci.yml) does both. Its
`formal` job checks the tree out onto a fresh runner, builds the venv and the
Lean toolchain from the pinned manifests, and runs `run_checks.sh` with
`GATE0_PY` pointed at the runner's own `/usr/bin/python3`.

**That workflow file lives in this repository**, so an attacker who can write
the tree can write it too. Removing that last step needs an organisation-level
required workflow, or a reusable workflow owned by a different repository.
This repository has neither.

FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE.
