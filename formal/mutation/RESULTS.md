# Mutation & bytecode-obligation results

FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE

## Mutation campaign

The catalogue (`mutants.py`) injects **50 deliberate defects** across seven
classes into the shipped verifier (`src/MLDSA44Verifier.sol`), the shipped
kernels (`src/Decode.sol`, `src/Ntt.sol`, `src/InvNtt.sol`), the reference
verifier and kernels (`test/ZZZ_E2ERef.sol`, `test/ZZZ_decode.t.sol`,
`test/ZZZ_decode2.t.sol`, `test/ZZZ_NttVariants.sol`, `test/ZZZ_InvNtt.sol`),
and the vendored oracle (`test/vendor/ZKNOX_dilithium_core.sol`):

| class     | n | what it attacks |
|-----------|---|-----------------|
| NORM      | 13 | the strict `‖z‖∞ < γ1 − β` check (FIPS 204 Alg. 3), on the reference verifier and the shipped `unpackZPacked`; includes single-site off-by-ones, both window edges as their own constants, the canonicalisation flag (`[u ≥ q]` vs `[u > q]`, i.e. z = 0 stored as q), and (because the shipped check is one expression per four-coefficient word) three mutants that blank or relax a SINGLE 64-bit LANE of a replicated constant, each leaving 256 of the 1024 coefficients unchecked or mis-decoded |
| HINT_ENC  | 13 | HintBitUnpack canonicality (FIPS 204 Alg. 21; the CVE-2026-24850 malleability class), on both decoder copies, including six mutants (M65–M70) on the SHIFT ARITHMETIC of the branchless padding check, the branch where a ONE-TOKEN change yields a SECOND valid signature for one (pk, message) |
| USEHINT   | 7 | UseHint + w1Encode (FIPS 204 Alg. 40/28), on both kernels, incl. the SWAR division and 2γ2 constants |
| NTT       | 7 | the two-step lane-local reduction: the coarse constant MU33 on the variant and shipped forward/inverse NTTs (congruence-preserving defects only lane bounds or end-to-end vectors can see), the SECOND step deleted from a shipped fused pass, and the 31-bit-per-lane quotient mask widened to 32 (cross-lane leak) |
| VERIFIER  | 7 | the assembled shipped verifier: exact sig length, the pk-contract size pin AND the CONSTANT it compares against (M72: the shape pin does not move when the constant does), mu domain byte, magic-c̃ backdoor shape, per-call helper codehash re-check, hint-weight check |
| REFERENCE | 1 | the vendored decoder used as the differential oracle (mutating the oracle must break the differential tests) |
| EQUIVALENT| 2 | provably semantics-preserving controls (must survive) |

**Result of the FULL campaign: 45 / 45 non-equivalent mutants KILLED = 100 %,
0 unattributed, and all 5 pinned equivalent mutants correctly SURVIVED**
(driver exit 0; every KILLED row carries at least one named killing test,
asserted by the driver).

> **That figure comes from a FULL campaign (`run_mutation.py --full`), the only
> mode that may print it.** Routine runs, including
> `formal/run_checks.sh --full`, execute a **seeded random SAMPLE of 8 of the
> 50 mutants**, because each mutant costs a full via-IR rebuild and the
> complete campaign is 3.4 h of measured mutant time (~40 min wall-clock at
> `--jobs 6`; the breakdown is below). A sampled run is labelled
> `SAMPLE n/50 (seed=S)` everywhere it reports, never prints the `45/45`
> headline, and never overwrites `mutation_results_final.json`.

The five expected survivors, with the argument for each (full text in
`mutants.py`):

* **M26.** The `s1 == 44` correction in the reference `useHintFast2` is dead
  code (the result is only used inside an unconditional `mod 44`, and
  44 ≡ 0 mod 44).
* **M28.** The shipped SWAR division constant `SW_MDIV + 1` is
  self-correcting: it changes the intermediate `Q0` on exactly 60 of the
  8,380,417 values of `r`, and the output on none of them. The evidence is
  **empirical over a complete differing set**, not exhaustive over the input
  space: all 60 differing `r` × 4 lane positions × 16 hint patterns × **13
  chosen critical neighbour-lane values** = 49,920 configurations, 0
  mismatches, re-checked on-chain. `mutants.py` labels it `EQUIVALENT
  (empirical, but over a COMPLETE differing set)` for exactly that reason.
* **M56.** The verifier-level `hWeight > 80` branch is unreachable:
  `unpackHFast` already enforces the ω bound at decode time.
* **E01**. The shipped norm check with its two `and` operands swapped,
  `and(add(o, Z_NLO), sub(Z_NHI, o))` → `and(sub(Z_NHI, o), add(o, Z_NLO))`.
  `AND` is commutative; no comparison is touched.
* **E02**. A comment-only change (harness control).

Only **M26, M28 and M56** are substantive equivalences: claims about the
kernels, each with its argument written beside it in `mutants.py`. **E01** and
**E02** are harness controls, an operand swap and a comment, and `mutants.py`
states their purpose plainly: a kill on either would mean some test pins gas or
bytecode where it means to pin behaviour, which would make every other kill in
the table suspect.

### Catalogue scope (mutants deliberately not included)

Four defect sites were probed and found **unkillable by construction** in the
current corpus, so they are not in the catalogue; each is documented inline in
`mutants.py`:

* the loose z-norm check of `test/ZZZ_decode2.t.sol::unpackZFast2` (2 sites).
  The loose window is deliberate and documented, and the flag is consumed only
  in agreement and memory-safety checks, never as a rejection surface;
* the ω-bound and cut-monotonicity checks of the TEST-SIDE decoder copy in
  `test/ZZZ_decode.t.sol` (2 sites). The FIPS-check battery asserts the
  SHIPPED decoder, and the differential tests do not generate encodings that
  reach these two checks of the test copy. Both checks are mutation-covered on
  the shipped copy (M44, M45), and the test-side checks that are differentially
  reachable stay covered (M20, M21, M24).

One direction choice is likewise recorded. Under a spread-Barrett reduction the
`−1` constant defect is end-to-end unobservable (erased by the final canonical
reduction); under the two-step lane-local reduction it is observable: `MU33 −
1` leaves step 2 about 1000× above 2q. Splitting the directions keeps both
meaningful under either reduction form: `−1` rides on the text-identical variant
copy (M30), where the lane-bound micro-tests see it directly, and `+1`, which
underflows a lane either way, is on the shipped copies (M49/M50, ACVP shards).

### Sampled runs vs the campaign

Each mutant is a full rebuild of the tree (`via_ir = true` at
`optimizer_runs = 10000`). The 50 records of `mutation_results_final.json` sum
to **12,348 s = 3.43 h** of mutant time, with min / median / max
**188.5 / 242.2 / 303.0 s** (3.1 / 4.0 / 5.1 min). Those per-mutant times come
from a **parallel** run (`--jobs 6`), so a serial run's wall-clock need not
equal their sum; at `--jobs 6` the campaign takes about **40 minutes**. Either
way it is a release-candidate cost, not an every-edit cost. The driver has two
scopes and keeps them visibly distinct:

| invocation | what it runs | may print `45/45`? | writes `mutation_results_final.json`? |
|---|---|---|---|
| `run_mutation.py` (default) | seeded, family-stratified **sample of 8** | no | no: a seed-named file in the temp dir |
| `run_mutation.py --sample N --seed S` | that exact sample, reproducibly | no | no |
| `run_mutation.py --ids M11,M26` | exactly those mutants | no | no |
| `run_mutation.py --full` | **all 50** | yes | yes |
| `formal/run_checks.sh --full` | vacuity audit + a **sampled** mutation run | no | no |
| `formal/run_checks.sh --extended` | vacuity audit + the **full** campaign | yes | yes |

* **`--jobs N`** (default `min(8, cpu_count − 2)`) runs N mutants at once, each
  in **its own workspace**. Mutants patch a file in place, so a shared
  workspace would be a correctness bug. Parallelism changes no verdict: the
  verdict classes, the `--fail-fast` retry and the exit rules are all per
  mutant, so `--full --jobs N` agrees with a serial run.
* **Sampling is stratified and reproducible.** The catalogue's seven families
  are each shuffled by `random.Random(seed)` and the sample is drawn
  **round-robin** across them, so a sample of 8 spans **all seven families** and
  always contains at least one pinned equivalent mutant, whose **SURVIVAL is
  the required outcome** (a selection consisting only of equivalents exits 0).
* **Reproducing a sampled failure.** The seed is printed at the top, in the
  summary banner, and on the last line; the replay command is printed
  verbatim. Given `SAMPLE 8/50 (seed=1487302113)`:

  ```bash
  $PY formal/mutation/run_mutation.py --sample 8 --seed 1487302113   # same 8 mutants
  $PY formal/mutation/run_mutation.py --ids M49                      # then narrow to one
  ```

* **Workspace hygiene is enforced.** Workspaces are `mldsa-mutws-*`
  directories under `$MUT_WS_ROOT`, registered as created and removed on every
  exit path (success, failure, exception, `atexit`, signal handlers that first
  kill the live `forge` children). Nothing without the `mldsa-mutws-` prefix
  is ever removed. `--keep-workspaces` opts out, loudly. Free space is checked
  **before** anything is built (~200 MB per worker plus a 512 MB reserve).

### Verdict integrity

The driver enforces:

* the mutant ID set and the equivalent set are **pinned in the driver**
  (`EXPECTED_MUTANTS`, 50 IDs; `EXPECTED_EQUIVALENT`, 5 IDs), and any run that
  draws from the catalogue, full **or sampled**, aborts if the catalogue is
  not exactly that set. Deleting hard-to-kill mutants cannot raise the score;
* only a `--full` run prints the campaign's kill rate, and only if every one
  of the 50 mutants produced a verdict (otherwise `INCOMPLETE`, and failure);
* every pattern's occurrence count is asserted before patching (a stale
  catalogue aborts instead of "surviving");
* a non-zero exit with **no named failing test** is scored `UNATTRIB`,
  excluded from the denominator, and fails the check, never a kill;
* a **non-equivalent survivor fails the check**, and so does a killed
  equivalent mutant (that would mean a test pins gas or bytecode where it
  means to pin behaviour).

## halmos obligation suites

`run_halmos.py` pins the per-contract obligation sets of the two symbolic
harnesses and aborts if the discovered `check_*` functions differ from the
pins (deleting an obligation cannot shrink the run silently):

| contract    | file                 | pinned obligations | expectation |
|-------------|----------------------|--------------------|-------------|
| FVKernels   | test/FV_Kernels.sol  | 18                 | every function PASS |
| FVCanaries  | test/FV_Kernels.sol  | 6                  | every function FAIL |
| FV2Barrett  | test/FV2_Barrett.sol | 15                 | every function PASS |
| FV2Canaries | test/FV2_Barrett.sol | 7                  | every function FAIL |

Canary contracts must report every function as FAIL; anything else invalidates
the corresponding proofs. If halmos is not installed the driver verifies the
pins against the harness sources and aborts with exit 3 before claiming
anything about the solver run.

> **Why the pins are generated, not hand-maintained:** a single stale
> identifier in the list makes every invocation exit 4 before the
> obligation-set check can mean anything, and a check that aborts on every run
> is worse than no check. To anyone not reading the exit code, that abort is
> indistinguishable from success. `--print-functions` regenerates the pins from
> the harness sources, so the driver reaches a verdict.

### Measured results

Both suites were re-run for this revision under **halmos 0.3.3** (Python 3.12,
default solver, `--loop 16`, `--solver-timeout-assertion 300000`, one process
per function, 330 s wall cap). The artefacts are `halmos_fv1.json` and
`halmos_fv2.json`.

| contract | result |
|---|---|
| FV2Barrett  | **13/15 PASS**; `w3_qhatFitsAndSecondMulNoWrap` and `w11b_swarIsLanewiseScalar` TIMEOUT at 300 s |
| FV2Canaries | **7/7 FAIL**, as required |
| FVKernels   | **9/18 PASS**; the nine Barrett/SWAR obligations `c1, c2, c1a, c1c, c1e, c3, c4, c6, c7` TIMEOUT at 300 s |
| FVCanaries  | **6/6 FAIL**, as required |

**The TIMEOUTs are the documented ones, and they are why `test/FV2_Barrett.sol`
exists.** Bit-blasting is the wrong engine for a linear-integer fact about a
floor division, across three solvers alike. A TIMEOUT is reported as TIMEOUT
and never as a pass. `halmos` prints a timeout as `0 passed; 1 failed`,
which is exactly the confusion this driver's verdict tags exist to prevent.

No claim in this repository rests on a halmos TIMEOUT. The lazy-Barrett bound
is proved by the Lean theorems (`Mldsa.Barrett.*`, exact EVM 256-bit semantics)
and by Z3 obligations S1-S4/S7/S13/C11a-d/E9a-b; halmos contributes the
BYTECODE-level link for the obligations it discharges.

## Result files

| file | what it records |
|---|---|
| `mutation_results_final.json` | the FULL campaign against the current corpus: **45 / 45 non-equivalent killed (100 %)**, 5 equivalent survivors, 0 unattributed, and a COMPLETE per-mutant killer list for each. Written **only** by `run_mutation.py --full`. Shape: `{"_meta": {…}, "results": [...]}`. `_meta` names the mode, whether `--fail-fast` was in force, and the SHA-256 of the two files the attribution is *about* (`mutants.py`, `test/MUT_Gaps.t.sol`). |
| `halmos_fv2.json` | `test/FV2_Barrett.sol` under halmos 0.3.3: FV2Barrett **13/15 PASS** (`w3`, `w11b` TIMEOUT), FV2Canaries **7/7 FAIL** as required. (These numbers postdate the two-step lane-local reduction, which re-cut the whole harness; a copy of this file recording 14/14 is stale by definition.) |
| `halmos_fv1.json` | `test/FV_Kernels.sol` under the same configuration: FVKernels **9/18 PASS** (nine Barrett/SWAR TIMEOUTs), FVCanaries **6/6 FAIL** as required. |

Regenerate either halmos file with `HALMOS=$(which halmos) $PY
formal/mutation/run_halmos.py --contracts FVKernels,FVCanaries --out
formal/mutation/halmos_fv1.json` (or `FV2Barrett,FV2Canaries` for the other).
Both are byte-pinned by `FILES` in `formal/z3/source_pins.py`, so regenerating
them moves a pin and is visible in a diff.

### What still detects nothing here, stated rather than implied

`FILES` pins these artefacts' OWN bytes. It does **not** bind them to the
sources they describe, and a byte pin over a results file is satisfied by a
file that is entirely stale:

* `mutation_results_final.json`. **Closed.** `_meta.source_sha256` carries
  the digest of `mutants.py` and `test/MUT_Gaps.t.sol`, and
  `formal/hypotheses.py::mut_attribution_problems()` refuses the artefact when
  either has moved, so a campaign that predates the current catalogue fails a
  check instead of being quoted.
* `halmos_fv1.json` / `halmos_fv2.json`. **OPEN, deliberately.** Neither
  carries a digest of the harness it describes, and `run_halmos.py` is invoked
  by neither `run_checks.sh` nor CI, so nothing notices the files going stale.
  That is exactly how a `halmos_fv2.json` can come to record `14/14`
  for a re-cut harness. The limit on the damage (a limit, not a fix): the
  driver aborts when the discovered `check_*` set differs from its pins, so a
  RENAMED or DELETED obligation is caught on the next run. A CHANGED BODY is
  not. Wiring halmos into CI means a hard dependency on a solver whose
  measured behaviour here is nine TIMEOUTs, which is why it is not wired in.
  These two files are a **dated measurement**, not a check, and no claim in
  this repository rests on them.

  **PARTIALLY CLOSED for `test/FV2_Barrett.sol`**,
  because `FORMAL_VERIFICATION.md` §5.7 marked the Barrett refinement gap
  *Closed* while citing exactly that file: a file `forge test` compiled and
  never ran (22 `check_*`, 0 `test*`), that no test imported, and that no
  digest covered. Its kernel copies are now tied to `src/Ntt.sol::lazyBarrett`
  and `src/InvNtt.sol::invLazyBarrett` by a fuzz test
  (`FV_Kernels.t.sol::testFuzz_FV2_barrett_kernels_are_the_shipped_reductions`)
  and the whole file sits under C18's residual digest with its check census,
  so a CHANGED BODY does move a check now. `halmos_fv2.json` itself is still a
  dated measurement, and `test/FV_Kernels.sol` is still covered by no digest.

### The killer lists are complete; the ATTRIBUTION they support is co-occurrence

`mut_attribution_problems()` requires a test named `test_MUT_M<nn>_*` to appear
in `M<nn>`'s killer list. That is a real check, and for a mutant with a small
killer set a strong one. **23 of the 45 non-equivalent mutants are killed
by 24 or more tests each** (`M64` by 66), and for those the same check would
accept almost any test name in the corpus. The wording published in
`test/MUT_Gaps.t.sol` is accurate about what is checked; the impression it
leaves is stronger than the check.

Where a killer set has exactly ONE member, co-occurrence **is** causation, and
those attributions are pinned by value in
`formal/hypotheses.py::SOLE_KILLER_PINS` and checked in both directions. As
measured by the current full campaign:

| mutant | its sole killer in the whole corpus |
|---|---|
| `M20`, `M21` | `test_hint_decoder_is_identical_across_builds` |
| `M25` | `test_kernel_21_useHintSwar_boundaries` |
| `M39`, `M44` | `test_MUT_M44_hint_weight_omega_bound` |

`M39` has no test named after it, so the attribution check never examined it,
and it shares its single killer with `M44`, so weakening that one test silently
un-kills **two** catalogued mutants. A genuinely causal check for the rest
(re-run the corpus with one test removed, per candidate) costs a full campaign
per candidate and is **not** implemented; the limitation is stated here and in
`FORMAL_VERIFICATION.md` §2e instead.

## Reproduce

```bash
PY=pythonref/myenv/bin/python           # or any python3
$PY formal/mutation/mutants.py          # catalogue summary
$PY formal/mutation/run_mutation.py     # ROUTINE: sample of 8, parallel (minutes)
$PY formal/mutation/run_mutation.py --full --jobs 6   # THE CAMPAIGN (all 50)
$PY formal/mutation/run_mutation.py --sample 8 --seed 1487302113   # replay a sample
HALMOS=$(which halmos) $PY formal/mutation/run_halmos.py
```

The published `45/45` figure is the `--full` line. The bare invocation is a
**sample** and says so in its own output; quoting a sampled run as the campaign
is the mistake this labelling exists to prevent.

The campaign never edits the repository: each worker builds a disposable
`mldsa-mutws-*` workspace and patches only the copies. Workspace 0 is built,
seeded from the repository's `out/`/`cache/`, and baselined; the other workers
are copy-on-write clones of that baselined tree, so every worker starts from
the same certified state and arrives warm. All are removed when the run ends,
however it ends.
