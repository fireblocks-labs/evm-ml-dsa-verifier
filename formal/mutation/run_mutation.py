#!/usr/bin/env python3
# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
"""
Mutation-testing driver for the ML-DSA-44 EVM verifier corpus.

    python3 run_mutation.py                       # SAMPLE of 8 of the 50 mutants (routine)
    python3 run_mutation.py --full                # the FULL 50-mutant campaign
    python3 run_mutation.py --ids M11,M26         # exactly these mutants
    python3 run_mutation.py --sample 12 --seed 7  # a reproducible 12-mutant sample

    common: [--jobs N] [--seed S] [--workspace-root DIR] [--keep-workspaces]
            [--no-fail-fast] [--no-warm-start] [--out FILE] [--list]

SCOPE — A SAMPLE IS NOT THE CAMPAIGN
------------------------------------
Each mutant costs a full `forge test` rebuild (via-IR at optimizer_runs=10000).
The 50 records of `mutation_results_final.json` sum to 12,348 s = 3.43 h of
mutant time (median 242 s, range 189-303 s); those times come from a `--jobs 6`
run, so a serial wall-clock may differ, and at `--jobs 6` the whole campaign
takes about 40 minutes.  That is a release-candidate cost, not an every-edit
cost, so the DEFAULT is a seeded random SAMPLE of 8 and the complete campaign
is `--full`.

The published number — 45/45 non-equivalent mutants KILLED — is a claim about a
FULL campaign, and only a `--full` run is allowed to print it.  A sampled run
prints `SAMPLE n/50 (seed=S)`, labels every statistic "sampled", names the seed
that reproduces the exact selection, and points at `--full` for the published
figure.  The sampled runs also never write `mutation_results_final.json`: that
artefact stays a full-campaign artefact (a sample writes a seed-named file under
the system temp directory instead).

SAMPLING is stratified and deterministic under `--seed`: the mutants are grouped
into families by `cls` (NORM, HINT_ENC, USEHINT, NTT, VERIFIER, REFERENCE,
EQUIVALENT) in catalogue order, each family is shuffled by a `random.Random(seed)`
seeded with the printed seed, and the sample is drawn ROUND-ROBIN across the
families.  A sample of 8 therefore spans all seven families rather than
concentrating in one, and it always contains at least one of the pinned
equivalent mutants — whose SURVIVAL is the correct outcome and is scored as such.

PARALLELISM
-----------
Mutants are independent, so `--jobs N` (default `min(8, cpu_count - 2)`) runs N
at a time.  Each worker gets ITS OWN WORKSPACE: mutants patch a file in place,
so sharing one workspace between workers would be a correctness bug, not merely
a speed issue.  Parallelism is an execution detail — every verdict class, the
`--fail-fast` retry logic and the exit-code rules below are per mutant and
unchanged, so a `--full --jobs N` run produces the same verdicts as a serial one.

WORKSPACES
----------
The driver never edits the repository.  It materialises a WORKSPACE that mirrors
the foundry root (repository root) with real copies of `foundry.toml`, `src/`,
`test/*.sol` and `test/vendor/` (so mutations touch only the copy) and symlinks
for the heavy read-only trees (`lib`, `pythonref`, `tools`, `helpers`,
`prepare`, `test/fixtures`, `test/vectors`, and the `formal/` tree the ACVP
key-generation harness invokes).  Mutations are applied inside the workspace
only.

Workspace hygiene is enforced, not hoped for: a run that leaks its workspaces
can exhaust the disk.  Every workspace this process creates is registered,
carries the distinctive `mldsa-mutws-` prefix, and is removed on success, on
failure, on exception, on `SIGINT`/`SIGTERM` (a handler that first kills the
live `forge` children, then removes the trees, then `_exit`s) and from an
`atexit` hook as a last resort.  `--keep-workspaces` opts out for debugging and
says so loudly.  Free space is checked BEFORE anything is built and the run
refuses with a number rather than filling the disk.

Verdicts
  KILLED    at least one NAMED test failed    -> the suite detects this defect
  SURVIVED  the whole suite still passed      -> a concrete, named test gap
            (for a pinned EQUIVALENT mutant this is the REQUIRED outcome)
  BUILD     the mutant does not compile       -> not a valid mutant, reported
  UNATTRIB  the run exited non-zero but named no failing test -> a harness
            error, NOT a kill.  Excluded from the kill rate and reported.
  STALE     the pattern no longer occurs the expected number of times ->
            the catalogue is out of date; the run ABORTS rather than reporting
            a meaningless score

Every mutant records WHICH tests failed, so a kill can be traced to the test
that earned it (and so a kill by an unrelated gas-snapshot test is visible).

A non-zero exit with no identifiable [FAIL] line is not a kill: it is a
transient (an FFI hiccup, a concurrent fixture rebuild).  Counting those as
kills inflates the score, so such a run is re-run once without --fail-fast and
scored UNATTRIB (excluded from the denominator) if it still names nothing.

THE KILLER LIST IS AN ATTRIBUTION, SO IT MUST BE COMPLETE -- A CAPPED OR
FAIL-FAST-TRUNCATED LIST IS NOT ONE
--------------------------------------------------------------------------
`test/MUT_Gaps.t.sol` publishes, in its header, that "every test names the
mutant id it kills, so the link between a test and the defect it detects is
reproducible rather than asserted", and `formal/hypotheses.py` CHECKS that
claim against the `killers` lists in `mutation_results_final.json`.  Two
failure modes would make those lists unusable as ground truth; both are barred:

  * a CAP.  With `killers[:12]` a full list is indistinguishable from a
    sample, and M11 alone reaches 12 names from a single suite.
  * FAIL-FAST.  Under the default `--fail-fast`, `forge --fail-fast`
    cancels the run, so the reported [FAIL] set is an ORDER-DEPENDENT PREFIX
    rather than the set of tests that detect the defect.  MEASURED on this tree:
    with --fail-fast M39 listed seven MUT_Gaps tests; with --no-fail-fast its
    killer set is exactly one, `test_MUT_M44_hint_weight_omega_bound`, and the
    test named after it kills it not at all.

So there is no cap, `--full` implies --no-fail-fast (pass `--fail-fast` to
override, and the choice is recorded), and the artefact carries a `_meta` block
naming the mode, the fail-fast setting, and the SHA-256 of the two files the
attribution is ABOUT -- `mutants.py` and `test/MUT_Gaps.t.sol` -- so a check can
refuse a stale artefact instead of quoting one.
"""
import argparse, atexit, hashlib, json, os, queue, random, re, shutil, signal
import subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
FORGE = os.path.expanduser("~/.foundry/bin/forge")
if not os.path.exists(FORGE):
    FORGE = shutil.which("forge") or "forge"

sys.path.insert(0, HERE)
from mutants import MUTANTS  # noqa: E402

# ---------------------------------------------------------------------------
# THE CATALOGUE IS AN ASSERTION
# ---------------------------------------------------------------------------
# The kill rate is printed as `killed/{len(real)}`, so the DENOMINATOR comes
# from whatever `mutants.py` happens to contain: deleting the mutants a weak
# corpus fails to kill would RAISE the advertised score instead of failing the
# check.  The mutant ID set is pinned here, in the DRIVER rather than in the
# catalogue it checks, and any run that DRAWS from the catalogue (a full run or
# a sample) aborts if the catalogue is not exactly this set.  `--ids` names its
# subset explicitly and is exempt, as it always was.
EXPECTED_MUTANTS = [
    'M11', 'M12', 'M13', 'M40', 'M40b', 'M41', 'M42', 'M60', 'M61', 'M62',
    'M63', 'M64', 'M20', 'M21', 'M24', 'M43', 'M44', 'M45', 'M46', 'M65',
    'M66', 'M67', 'M68', 'M69', 'M70', 'M25', 'M26', 'M27', 'M28', 'M47',
    'M71', 'M48', 'M29', 'M30', 'M49', 'M50', 'M57', 'M58', 'M59', 'M51',
    'M52', 'M72', 'M73', 'M53', 'M54', 'M55', 'M56', 'M39', 'E01', 'E02'
]
# The mutants that are PROVABLY semantics-preserving, hence expected to survive.
# Pinned for the same reason: "this survivor is fine" must be a claim made in
# advance, not a verdict read off the run.
EXPECTED_EQUIVALENT = ['M26', 'M28', 'M56', 'E01', 'E02']

# The published, quotable figure.  Only a --full run may print it.
FULL_NON_EQUIVALENT = len(EXPECTED_MUTANTS) - len(EXPECTED_EQUIVALENT)   # 45

# The files the ATTRIBUTION is about: the catalogue that defines the mutants and
# the suite whose test NAMES claim to kill them.  Their digests go into the
# artefact's `_meta` so `formal/hypotheses.py::mut_attribution_problems` can
# refuse an artefact produced from a different pair of files rather than quote
# it.  Nothing else in this repository binds a results JSON to its sources.
ATTRIBUTION_SOURCES = ("formal/mutation/mutants.py", "test/MUT_Gaps.t.sol")


def source_digests():
    """{repository-relative path: sha256} of the files the attribution is about."""
    out = {}
    for rel in sorted(ATTRIBUTION_SOURCES):
        with open(os.path.join(REPO, rel), "rb") as fh:
            out[rel] = hashlib.sha256(fh.read()).hexdigest()
    return out

# Read-only trees symlinked into the workspace from the foundry root.
# test/vendor is NOT symlinked: the REFERENCE class mutates a file inside it,
# and a symlinked directory would let the patch write through to the repo.
SYMLINK_DIRS = ["lib", "pythonref", "tools", "helpers", "prepare"]
SYMLINK_TEST = ["fixtures", "vectors"]

# Nothing outside a directory carrying this prefix is ever removed by this
# driver.  Distinctive on purpose: it must not collide with a hand-made
# workspace (e.g. an older /tmp/mldsa-mutation-ws) that this process does not
# own and must not delete.
WS_PREFIX = "mldsa-mutws-"

MB = 1 << 20
# Per-workspace disk estimate: the foundry `out/` tree with room for the
# rebuild, floored so a cold repository (no out/ yet) still reserves sensibly.
WS_BYTES_FLOOR = 200 * MB
# Headroom left free after the workspaces, so a full disk is refused up front
# rather than discovered by a compiler halfway through.
WS_BYTES_RESERVE = 512 * MB

# ---------------------------------------------------------------------------
# WORKSPACE + CHILD-PROCESS LIFETIME
# ---------------------------------------------------------------------------
_LOCK = threading.Lock()
_WORKSPACES = set()          # every workspace THIS process created
_PROCS = set()               # every live forge child
_KEEP_WORKSPACES = False
_ABORT = threading.Event()   # set by a signal handler or a fatal worker error


def _safe_rmtree(path):
    """Remove a workspace, refusing anything this driver did not create."""
    base = os.path.basename(os.path.normpath(path))
    if not base.startswith(WS_PREFIX):
        print(f"  !! REFUSING to remove {path}: not a {WS_PREFIX}* workspace",
              file=sys.stderr)
        return
    shutil.rmtree(path, ignore_errors=True)


def _kill_children():
    with _LOCK:
        procs = list(_PROCS)
    for p in procs:
        try:
            p.terminate()
        except Exception:
            pass
    deadline = time.time() + 5
    for p in procs:
        try:
            p.wait(timeout=max(0.1, deadline - time.time()))
        except Exception:
            try:
                p.kill()
            except Exception:
                pass


def cleanup_workspaces(kill=False):
    """Remove every workspace this process created.  Safe to call twice."""
    if kill:
        _kill_children()
    with _LOCK:
        paths = list(_WORKSPACES)
        _WORKSPACES.clear()
    if _KEEP_WORKSPACES:
        for p in paths:
            print(f"  (kept workspace: {p})")
        return
    for p in paths:
        _safe_rmtree(p)


def _on_signal(signum, _frame):
    _ABORT.set()
    sys.stderr.write(f"\n!! signal {signum}: killing builds and removing "
                     f"{len(_WORKSPACES)} workspace(s)\n")
    sys.stderr.flush()
    cleanup_workspaces(kill=True)
    os._exit(128 + signum)


def install_signal_handlers():
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        try:
            signal.signal(sig, _on_signal)
        except (ValueError, OSError):        # not the main thread / not supported
            pass
    atexit.register(cleanup_workspaces)      # last resort, e.g. an uncaught raise


def dir_bytes(path):
    total = 0
    for dirpath, _dirs, files in os.walk(path):
        for f in files:
            try:
                total += os.lstat(os.path.join(dirpath, f)).st_size
            except OSError:
                pass
    return total


def check_disk(root, jobs):
    """Refuse BEFORE building if `jobs` workspaces would not fit.

    A run that leaks its workspaces can exhaust the volume, so the space every
    workspace will need is checked here, before anything is built.  The estimate
    is deliberately conservative: it assumes a full copy even though the clone
    below is copy-on-write where the filesystem supports it.
    """
    out = os.path.join(REPO, "out")
    per = max(WS_BYTES_FLOOR, 2 * dir_bytes(out)) if os.path.isdir(out) \
        else WS_BYTES_FLOOR
    need = jobs * per + WS_BYTES_RESERVE
    free = shutil.disk_usage(root).free
    print(f"disk: {free / MB:.0f} MB free at {root}; need ~{need / MB:.0f} MB "
          f"({jobs} workspace(s) x ~{per / MB:.0f} MB + {WS_BYTES_RESERVE / MB:.0f} MB reserve)")
    if free < need:
        print(f"ABORT: insufficient disk space at {root}: {free / MB:.0f} MB free, "
              f"~{need / MB:.0f} MB needed for {jobs} workspace(s).\n"
              f"       Lower --jobs (each is ~{per / MB:.0f} MB), free space, or point "
              f"--workspace-root at a larger volume.", file=sys.stderr)
        return False
    return True


def build_workspace(ws):
    """Materialise a mutable mirror of the foundry root in the empty dir `ws`."""
    os.makedirs(os.path.join(ws, "test"), exist_ok=True)
    shutil.copy2(os.path.join(REPO, "foundry.toml"), os.path.join(ws, "foundry.toml"))
    shutil.copytree(os.path.join(REPO, "src"), os.path.join(ws, "src"))
    shutil.copytree(os.path.join(REPO, "test", "vendor"), os.path.join(ws, "test", "vendor"))
    for f in os.listdir(os.path.join(REPO, "test")):
        if f.endswith(".sol"):
            shutil.copy2(os.path.join(REPO, "test", f), os.path.join(ws, "test", f))
    for d in SYMLINK_DIRS:
        os.symlink(os.path.join(REPO, d), os.path.join(ws, d))
    for d in SYMLINK_TEST:
        os.symlink(os.path.join(REPO, "test", d), os.path.join(ws, "test", d))
    # test/FV2_AcvpKeyGen.t.sol runs `formal/acvp/keygen_build.py` through
    # vm.ffi with cwd = the foundry root, so `formal/` must resolve from the
    # workspace too.  It is symlinked read-only (the builder writes only under
    # formal/acvp/data/, which is cached and shared with the repository).
    os.symlink(os.path.join(REPO, "formal"), os.path.join(ws, "formal"))
    return ws


def new_workspace(root):
    """An empty, registered, uniquely-named workspace directory."""
    os.makedirs(root, exist_ok=True)
    ws = tempfile.mkdtemp(prefix=WS_PREFIX, dir=root)
    with _LOCK:
        _WORKSPACES.add(ws)
    return ws


def copy_tree(src, dst):
    """Copy `src` onto `dst`, preferring the filesystem's copy-on-write clone.

    `cp -Rc` is APFS clonefile: the 8 workspaces then cost almost no extra disk
    and are created in milliseconds.  `-R` copies symlinks AS symlinks, which is
    what the workspace's read-only trees need.  Any failure falls back to a
    plain recursive copy, so the semantics never depend on the filesystem.
    """
    for cmd in (["cp", "-Rc", src + "/.", dst], ["cp", "-R", src + "/.", dst]):
        try:
            if subprocess.run(cmd, capture_output=True).returncode == 0:
                return dst
        except OSError:
            pass
    shutil.copytree(src, dst, symlinks=True, dirs_exist_ok=True)
    return dst


def warm_start(ws):
    """Seed a workspace with the repository's existing build artefacts.

    foundry's cache is keyed on paths RELATIVE to the foundry root and on the
    CONTENT HASH of each source, so artefacts carry across workspaces and a
    changed (mutated) file is always recompiled — the seeding is a speed-up that
    cannot make a mutant test stale bytecode.  `--no-warm-start` disables it.
    """
    for name in ("out", "cache"):
        src = os.path.join(REPO, name)
        if os.path.isdir(src):
            dst = os.path.join(ws, name)
            os.makedirs(dst, exist_ok=True)
            copy_tree(src, dst)


def nth_replace(text, old, new, occ):
    """Replace occurrences of `old`; `occ` is None (all) or a list of 0-based indices."""
    out, pos, n = [], 0, 0
    while True:
        k = text.find(old, pos)
        if k < 0:
            out.append(text[pos:])
            break
        out.append(text[pos:k])
        out.append(new if (occ is None or n in occ) else old)
        pos = k + len(old)
        n += 1
    return "".join(out), n


def run_suite(ws, fail_fast=True, timeout=1800):
    cmd = [FORGE, "test"]
    if fail_fast:
        cmd.append("--fail-fast")
    t0 = time.time()
    proc = subprocess.Popen(cmd, cwd=ws, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True)
    with _LOCK:
        _PROCS.add(proc)
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        proc.kill()
        proc.communicate()
        return "TIMEOUT", [], time.time() - t0, ""
    finally:
        with _LOCK:
            _PROCS.discard(proc)
    out = stdout + stderr
    dt = time.time() - t0
    if "Compiler run failed" in out or "Error (" in out or "ParserError" in out:
        return "BUILD", [], dt, out[-4000:]
    failed = sorted(set(re.findall(r"\[FAIL[^\]]*\]\s+(\S+?)\s*\(", out)))
    if rc == 0 and not failed:
        return "PASS", [], dt, ""
    return "FAIL", failed, dt, out[-2000:]


# ---------------------------------------------------------------------------
# SELECTION
# ---------------------------------------------------------------------------
def families(mutants):
    """{class: [mutants]} plus the class order they first appear in."""
    order, by = [], {}
    for m in mutants:
        if m["cls"] not in by:
            by[m["cls"]] = []
            order.append(m["cls"])
        by[m["cls"]].append(m)
    return by, order


def stratified_sample(mutants, n, seed):
    """`n` mutants spanning as many families as possible, deterministic in `seed`.

    Each family's members are shuffled by `random.Random(seed)` in catalogue
    class order, then the sample is taken ROUND-ROBIN across families.  So a
    sample of 8 over the seven families takes one from each and one extra,
    rather than eight from whichever family happens to be largest, and the same
    seed always yields the same selection (that is what makes a failing sampled
    run replayable).
    """
    by, order = families(mutants)
    rng = random.Random(seed)
    pools = {}
    for cls in order:                        # shuffle in a FIXED class order
        pools[cls] = list(by[cls])
        rng.shuffle(pools[cls])
    picked = []
    while len(picked) < n:
        took = False
        for cls in order:
            if len(picked) >= n:
                break
            if pools[cls]:
                picked.append(pools[cls].pop())
                took = True
        if not took:                          # every family exhausted
            break
    rank = {m["id"]: i for i, m in enumerate(mutants)}
    return sorted(picked, key=lambda m: rank[m["id"]])


def catalogue_problems():
    """Why `mutants.py` is not the pinned catalogue, as a list of strings."""
    got_ids = [m["id"] for m in MUTANTS]
    got_eq = [m["id"] for m in MUTANTS if m.get("equivalent")]
    bad = []
    if got_ids != EXPECTED_MUTANTS:
        bad.append(f"catalogue is {len(got_ids)} mutants, pinned "
                   f"{len(EXPECTED_MUTANTS)}; missing "
                   f"{sorted(set(EXPECTED_MUTANTS) - set(got_ids))}, unpinned "
                   f"{sorted(set(got_ids) - set(EXPECTED_MUTANTS))}")
    if sorted(got_eq) != sorted(EXPECTED_EQUIVALENT):
        bad.append(f"equivalent-mutant set is {sorted(got_eq)}, pinned "
                   f"{sorted(EXPECTED_EQUIVALENT)}")
    return bad


# ---------------------------------------------------------------------------
# ONE MUTANT
# ---------------------------------------------------------------------------
def run_mutant(m, ws, fail_fast, timeout):
    """Patch, run, restore.  Returns (verdict, failed_tests, seconds, flaky)."""
    path = os.path.join(ws, m["file"])
    with open(path) as fh:
        pristine = fh.read()
    patched, n = nth_replace(pristine, m["old"], m["new"], m.get("occ"))
    if n != m["count"]:
        return "STALE", [], 0.0, False
    flaky = False
    try:
        with open(path, "w") as fh:
            fh.write(patched)
        v, failed, dt, _tail = run_suite(ws, fail_fast=fail_fast, timeout=timeout)
        # A non-zero exit with no identifiable [FAIL] line is not a kill: it
        # is a transient (an FFI hiccup, or a concurrent fixture rebuild).
        # Counting those as kills inflates the score, so re-run once without
        # --fail-fast and DEMAND A NAMED FAILING TEST.
        if v == "FAIL" and not failed:
            v2, failed2, dt2, _t2 = run_suite(ws, fail_fast=False, timeout=timeout)
            flaky = True
            v, failed, dt = v2, failed2, dt + dt2
    finally:
        with open(path, "w") as fh:
            fh.write(pristine)
    if v == "FAIL" and failed:
        verdict = "KILLED"
    elif v == "FAIL":
        # the re-run still named nothing.  This is a harness error, not
        # evidence about the test corpus, so it is not scored KILLED.
        verdict = "UNATTRIB"
    elif v == "PASS":
        verdict = "SURVIVED"
    else:
        verdict = v
    return verdict, failed, dt, flaky


def main():
    ap = argparse.ArgumentParser(
        description="mutation campaign for the ML-DSA-44 EVM verifier corpus")
    sel = ap.add_mutually_exclusive_group()
    sel.add_argument("--full", action="store_true",
                     help=f"run the COMPLETE {len(EXPECTED_MUTANTS)}-mutant campaign "
                          "(release candidates; the only mode allowed to print the "
                          "published kill rate)")
    sel.add_argument("--sample", type=int, default=8, metavar="N",
                     help="run a seeded, family-stratified random sample of N "
                          "mutants (default: 8)")
    sel.add_argument("--ids", default="", metavar="M11,M26",
                     help="run exactly these mutant ids")
    ap.add_argument("--seed", type=int, default=None,
                    help="RNG seed for --sample (default: random, always printed)")
    ap.add_argument("--jobs", type=int, default=None, metavar="N",
                    help="mutants to run at once, each in its OWN workspace "
                         "(default: min(8, cpu_count - 2))")
    ap.add_argument("--workspace-root", default=os.environ.get("MUT_WS_ROOT"),
                    help="parent directory for the per-worker workspaces "
                         "(default: $MUT_WS_ROOT or the system temp dir)")
    ap.add_argument("--keep-workspaces", action="store_true",
                    help="do NOT remove the workspaces (debugging; they are large)")
    ap.add_argument("--no-warm-start", action="store_true",
                    help="do not seed the workspace from the repository's out/ and "
                         "cache/ (slower; forge re-validates by content hash either way)")
    ap.add_argument("--out", default=None,
                    help="results JSON (default: mutation_results_final.json for "
                         "--full, a seed-named file under the temp dir otherwise)")
    ap.add_argument("--no-fail-fast", action="store_true",
                    help="do not pass --fail-fast to forge, so EVERY failing test is "
                         "named (implied by --full: the campaign artefact is an "
                         "attribution and a fail-fast prefix is not one)")
    ap.add_argument("--fail-fast", dest="force_fail_fast", action="store_true",
                    help="force --fail-fast even under --full (faster, but the killer "
                         "lists become an order-dependent prefix)")
    ap.add_argument("--list", action="store_true", help="print the catalogue and exit")
    args = ap.parse_args()

    if args.list:
        for m in MUTANTS:
            tag = " [equivalent]" if m.get("equivalent") else ""
            print(f"{m['id']:<5} {m['cls']:<10} {m['file']}{tag}\n        {m['desc']}")
        return 0

    global _KEEP_WORKSPACES
    _KEEP_WORKSPACES = args.keep_workspaces

    # ---- selection ---------------------------------------------------------
    ids = [x.strip() for x in args.ids.split(",") if x.strip()]
    seed = args.seed if args.seed is not None else random.SystemRandom().randrange(1, 2 ** 31)
    if ids:
        mode = "IDS"
        known = {m["id"] for m in MUTANTS}
        unknown = [i for i in ids if i not in known]
        if unknown:
            print(f"ABORT: unknown mutant id(s): {unknown}", file=sys.stderr)
            return 4
        todo = [m for m in MUTANTS if m["id"] in set(ids)]
    else:
        # Both a full run and a sample DRAW FROM the catalogue, so both assert
        # that the catalogue is the pinned one: a sampled denominator taken from
        # an unknown catalogue is exactly as meaningless as a full one.
        bad = catalogue_problems()
        if bad:
            for b in bad:
                print(f"ABORT: {b}", file=sys.stderr)
            return 4
        if args.full:
            mode, todo = "FULL", list(MUTANTS)
        else:
            mode = "SAMPLE"
            n = args.sample
            if n < 1:
                print("ABORT: --sample must be >= 1", file=sys.stderr)
                return 4
            n = min(n, len(MUTANTS))
            todo = stratified_sample(MUTANTS, n, seed)

    if args.out:
        out_path = args.out
    elif mode == "FULL":
        out_path = os.path.join(HERE, "mutation_results_final.json")
    else:
        # A SAMPLE NEVER OVERWRITES THE FULL-CAMPAIGN ARTEFACT.  Keeping
        # mutation_results_final.json a full-campaign file is half of what stops
        # a sample being quoted as the campaign (the other half is the summary
        # wording below).
        out_path = os.path.join(tempfile.gettempdir(),
                                f"mldsa-mutation-{mode.lower()}-{seed}.json")

    # A FULL run produces the artefact the attribution check reads, so it must
    # name EVERY failing test: `forge --fail-fast` cancels the run and turns the
    # [FAIL] set into an order-dependent prefix.  `--fail-fast` overrides, and
    # whichever way it lands is recorded in `_meta`.
    fail_fast = args.force_fail_fast or not (args.no_fail_fast or mode == "FULL")

    cpus = os.cpu_count() or 2
    jobs = args.jobs if args.jobs else min(8, max(1, cpus - 2))
    jobs = max(1, min(jobs, len(todo)))

    ws_root = args.workspace_root or tempfile.gettempdir()

    banner = {"FULL": f"FULL CAMPAIGN — all {len(MUTANTS)} catalogued mutants",
              "SAMPLE": f"SAMPLE {len(todo)}/{len(MUTANTS)} (seed={seed}) — "
                        "NOT the full campaign",
              "IDS": f"SELECTED {len(todo)}/{len(MUTANTS)} by --ids — "
                     "NOT the full campaign"}[mode]
    print("=" * 70)
    print(banner)
    if mode == "SAMPLE":
        print(f"seed: {seed}   (replay this exact selection with --sample "
              f"{len(todo)} --seed {seed})")
    print(f"mutants: {', '.join(m['id'] for m in todo)}")
    print(f"jobs: {jobs} (of {cpus} cpus)   workspaces: {ws_root}/{WS_PREFIX}*"
          + ("   [KEPT]" if _KEEP_WORKSPACES else ""))
    print(f"fail-fast: {'ON — killer lists are an ORDER-DEPENDENT PREFIX' if fail_fast else 'off — killer lists are COMPLETE'}")
    print(f"results: {out_path}")
    print("=" * 70, flush=True)

    if not check_disk(ws_root, jobs):
        return 5

    # The artefact's self-description.  A results file that does not say WHICH
    # mode produced it, whether the killer lists are complete, and WHICH
    # catalogue and which naming suite it is an attribution OF, cannot be used
    # as ground truth for anything: a truncated, fail-fast-pruned file looks
    # exactly like a complete one, so `_meta` makes the difference legible to
    # the check that reads it.
    def meta(n_done):
        return dict(mode=mode, fail_fast=fail_fast,
                    complete=(mode == "FULL" and n_done == len(MUTANTS)),
                    mutants_selected=[m["id"] for m in todo],
                    catalogue_size=len(MUTANTS),
                    expected_equivalent=list(EXPECTED_EQUIVALENT),
                    source_sha256=source_digests())

    install_signal_handlers()
    # Contention between `jobs` concurrent builds stretches wall clock, so the
    # per-suite safety net scales with it: a TIMEOUT must mean "wedged", never
    # "busy", or a parallel run would not agree with a serial one.
    timeout = 1800 + 900 * (jobs - 1)

    results_by_id, flaky, t_start = {}, [], time.time()
    try:
        # ---- workspace 0: built, warmed, baselined ------------------------
        ws0 = new_workspace(ws_root)
        build_workspace(ws0)
        if not args.no_warm_start:
            warm_start(ws0)
        print(f"workspace: {ws0}", flush=True)

        # THE CATALOGUE MUST STILL FIT THE SOURCE.  Checked for every selected
        # mutant BEFORE anything is built, so a stale catalogue aborts the run
        # deterministically instead of after an hour of compiling.
        for m in todo:
            with open(os.path.join(ws0, m["file"])) as fh:
                _p, n = nth_replace(fh.read(), m["old"], m["new"], m.get("occ"))
            if n != m["count"]:
                print(f"ABORT: {m['id']} pattern occurs {n}x, catalogue says "
                      f"{m['count']}x in {m['file']}", file=sys.stderr)
                return 3

        # baseline must be green, else every "kill" is meaningless
        print("== baseline ==", flush=True)
        v, failed, dt, _ = run_suite(ws0, fail_fast=False, timeout=timeout)
        print(f"baseline: {v} ({dt:.0f}s)", flush=True)
        if v != "PASS":
            print(f"ABORT: baseline is not green: {failed}", file=sys.stderr)
            return 2

        # ---- the other workspaces: clones of the baselined tree -----------
        # Cloning the tree that JUST PASSED the baseline (rather than rebuilding
        # each from the repository) makes every worker's starting point
        # byte-identical to the one the baseline certified, and it arrives warm.
        pool = queue.Queue()
        pool.put(ws0)
        for _ in range(jobs - 1):
            ws = new_workspace(ws_root)
            copy_tree(ws0, ws)
            pool.put(ws)
        if jobs > 1:
            print(f"cloned {jobs - 1} further workspace(s) from the baselined tree",
                  flush=True)

        done = threading.Lock()

        def work(m):
            if _ABORT.is_set():
                return None
            ws = pool.get()
            try:
                verdict, killers, dt, was_flaky = run_mutant(
                    m, ws, fail_fast=fail_fast, timeout=timeout)
            finally:
                pool.put(ws)
            eq = m.get("equivalent", False)
            good = (verdict == "SURVIVED") if eq else (verdict == "KILLED")
            # KILLERS ARE STORED WHOLE.  A cap like `killers[:12]` turns every
            # list of 12 into a SAMPLE that reads like a set, and the
            # attribution check in formal/hypotheses.py needs the whole set.
            rec = dict(id=m["id"], cls=m["cls"], file=m["file"], desc=m["desc"],
                       equivalent=eq, verdict=verdict, seconds=round(dt, 1),
                       killers=killers, expected_ok=good)
            with done:
                results_by_id[m["id"]] = rec
                if was_flaky:
                    flaky.append(m["id"])
                print(f"{m['id']:<5} {m['cls']:<10} {verdict:<9} {dt:6.0f}s  "
                      f"{'ok ' if good else '!! '} {m['desc']}", flush=True)
                if killers:
                    print(f"        killed by: {', '.join(killers[:6])}"
                          + (" ..." if len(killers) > 6 else ""), flush=True)
                ordered = [results_by_id[x["id"]] for x in todo
                           if x["id"] in results_by_id]
                with open(out_path, "w") as fh:
                    json.dump({"_meta": meta(len(ordered)), "results": ordered},
                              fh, indent=1)
            return rec

        with ThreadPoolExecutor(max_workers=jobs) as ex:
            list(ex.map(work, todo))
    finally:
        cleanup_workspaces()

    results = [results_by_id[m["id"]] for m in todo if m["id"] in results_by_id]
    stale = [r for r in results if r["verdict"] == "STALE"]
    if stale:                                   # the pre-flight check missed it
        for r in stale:
            print(f"ABORT: {r['id']} pattern count changed under the run "
                  f"({r['file']})", file=sys.stderr)
        return 3

    # An UNATTRIB row is not evidence in either direction, so it is excluded
    # from the denominator instead of being counted as a kill.  Any KILLED row
    # must carry at least one named killer -- assert it.
    inflated = [r for r in results if r["verdict"] == "KILLED" and not r["killers"]]
    real = [r for r in results if not r["equivalent"] and r["verdict"] != "UNATTRIB"]
    killed = sum(1 for r in real if r["verdict"] == "KILLED")
    eq_ok = [r for r in results if r["equivalent"] and r["verdict"] == "SURVIVED"]
    unat = [r for r in results if r["verdict"] == "UNATTRIB"]
    surv = [r for r in real if r["verdict"] != "KILLED"]
    bad_eq = [r for r in results if r["equivalent"] and r["verdict"] == "KILLED"]
    wall = time.time() - t_start

    # A FULL run that did not actually reach every catalogued mutant is not a
    # full campaign, and must not print the campaign's headline.
    incomplete = mode == "FULL" and len(results) != len(MUTANTS)

    print("\n" + "=" * 70)
    print(banner)
    if incomplete:
        print(f"  !! INCOMPLETE: {len(results)} of {len(MUTANTS)} mutants produced a "
              "verdict; this is NOT a full campaign")
    if mode == "FULL":
        if not incomplete:
            print(f"kill rate: {killed}/{len(real)} = "
                  f"{100.0 * killed / max(1, len(real)):.1f}%"
                  f"   (non-equivalent mutants with an attributable verdict)")
        print(f"mutants: {len(results)} total, {len(results) - len(real)} excluded "
              f"({sum(1 for r in results if r['equivalent'] and r['verdict'] != 'UNATTRIB')} "
              f"equivalent + {len(unat)} unattributed)")
    else:
        # Deliberately NOT in the shape of the published figure: every number is
        # labelled "sampled"/"selected", and the campaign's own verdict is
        # pointed at rather than approximated.
        lab = "sampled" if mode == "SAMPLE" else "selected"
        if real:
            print(f"{lab} kill rate: {killed}/{len(real)} {lab} non-equivalent "
                  f"mutants killed ({100.0 * killed / len(real):.1f}% OF THIS "
                  f"{lab.upper()} SET ONLY)")
        else:
            print(f"{lab} kill rate: n/a — every mutant in this selection is a "
                  "pinned EQUIVALENT, whose SURVIVAL is the required outcome")
        print(f"{lab}: {len(results)} of {len(MUTANTS)} catalogued mutants "
              f"({len(eq_ok)} pinned equivalent survived as required, "
              f"{len(unat)} unattributed)")
        cls_hit = sorted({r["cls"] for r in results})
        print(f"families: {', '.join(cls_hit)} ({len(cls_hit)} of "
              f"{len(families(MUTANTS)[1])})")
        print(f"THIS IS NOT THE CAMPAIGN.  The published figure "
              f"({FULL_NON_EQUIVALENT}/{FULL_NON_EQUIVALENT} non-equivalent mutants "
              f"KILLED) comes from a full run:")
        print("    formal/mutation/run_mutation.py --full --jobs 6")
        if mode == "SAMPLE":
            print("replay THIS sample exactly:")
            print(f"    formal/mutation/run_mutation.py --sample {len(todo)} "
                  f"--seed {seed}")
    for r in surv:
        print(f"  SURVIVOR {r['id']} [{r['cls']}] {r['desc']}")
    for r in unat:
        print(f"  !! UNATTRIBUTED {r['id']} [{r['cls']}] {r['desc']}")
        print(f"     the suite exited non-zero but named no failing test; this is a "
              f"harness error and is NOT counted as a kill")
    if inflated:
        for r in inflated:
            print(f"  !! INTERNAL ERROR: {r['id']} scored KILLED with no named killer")
    if flaky:
        print(f"  (re-ran without --fail-fast after an unattributed failure: "
              f"{', '.join(sorted(flaky))})")
    for r in bad_eq:
        print(f"  !! EQUIVALENT MUTANT KILLED (over-specified test): {r['id']} {r['desc']}")
    print(f"wall clock: {wall / 60:.1f} min at --jobs {jobs}; results: {out_path}")
    if mode == "SAMPLE":
        print(f"seed: {seed}")
    print("=" * 70)
    # A NON-EQUIVALENT SURVIVOR is a named test gap, so it fails the check
    # instead of being printed and shrugged at.  A pinned EQUIVALENT mutant that
    # survives is the REQUIRED outcome and never fails the check -- including
    # when a sample happens to contain nothing else.  If a new non-equivalent
    # survivor appears, either the corpus regressed or the mutant belongs in
    # EXPECTED_EQUIVALENT with a written reason.
    return 1 if (inflated or unat or surv or bad_eq or incomplete) else 0


if __name__ == "__main__":
    sys.exit(main())
