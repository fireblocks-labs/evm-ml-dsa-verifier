#!/usr/bin/env python3
"""
Machine-checked verification suite for the ML-DSA-44 EVM verifier.

Two kinds of obligation, both mechanical (no human "review" step):
  [SMT]  Z3 proves a universally-quantified statement over an unbounded domain by
         showing the negation is UNSAT.  A PASS here is a proof.
  [EXH]  the domain is small enough to enumerate completely; a PASS is a proof by
         exhaustion (every input checked against the FIPS reference formula).
  [CALC] a closed-form numeric fact, computed exactly in Python integers.

Run:  python3 verify_all.py            (z3-solver is REQUIRED, not optional)
Exit code 0 iff every obligation PASSes; a missing z3 records a FAIL, exit 1.

Obligation IDs are cited by FORMAL_VERIFICATION.md and by the source comments of
the kernels they cover.
"""
import ast, copy, hashlib, os, re, sys, time, traceback, types

# ===========================================================================
# TRUST ANCHOR
# ===========================================================================
# Reporting the source-digest tripwire THROUGH `record`, or reaching the pin
# tables with `import source_pins`, are both fatal.  Two attack shapes make
# that concrete:
#
#   * a module-level `PINS = exec("<rebind record>", globals())` inside this
#     file rebinds `record` to a function that returns True and forces every
#     conjunct True.  META-PINS's own FAIL rows are then laundered by the very
#     function it reports through, and the suite prints a full green tally,
#     exit 0, over a tree with a wrong shipped `Q4_128`.  A digest reported
#     through a hijackable channel is not a tripwire.
#   * `formal/z3/__pycache__/source_pins.cpython-310.pyc`, covered by no
#     manifest in the repository, replaces `compute()` with
#     `return dict(PINS)`.  CPython prefers that .pyc over the .py an
#     auditor reads, so the thing verified is not the thing executed.
#
# So the FIRST executable statements of this file are an anchor that runs before
# anything else in the file can, does not use `record`, does not use `import` for
# any repo module, and EXITS rather than reporting:
#
#   1. `sys.dont_write_bytecode` + PYTHONDONTWRITEBYTECODE, so no .pyc is ever
#      created for a module under formal/;
#   2. REFUSE to run if a `.pyc` exists anywhere that could shadow a module this
#      file loads (the .pyc-shadowing vector) -- not merely ignore it;
#   3. read `source_pins.py` as BYTES, digest its CODE (its AST with the two
#      pinned tables blanked) and compare against SOURCE_PINS_CODE_SHA256 below;
#      REFUSE on mismatch;
#   4. `exec` the very text that was digested -- no import machinery, no .pyc,
#      so the thing verified IS the thing executed;
#   5. digest THIS file's whole AST and compare against the pinned
#      `verify_all::@@file` region; REFUSE on mismatch.  That region has no
#      per-statement structure, so nothing in this file can be exempt from it --
#      which is what a rebinding statement inserted here would need.
#
# WHAT THE ANCHOR PROVES, AND WHERE THE BOOTSTRAP ENDS.  The anchor is code, so
# it cannot certify itself.  Its guarantee is exactly:
#
#     IF the ~90 lines of this block are the reviewed ones AND the interpreter
#     and its standard library are the reviewed ones, THEN every other byte of
#     the formal apparatus that this process executes, and every file under
#     formal/, is the byte that was pinned.
#
# An attacker with write access to the repository can still edit this block (or
# insert statements above it, e.g. rebinding `hashlib.sha256`).  Nothing in-band
# can stop that.  What is bought is that the attack surface is a fixed, tiny,
# human-auditable prefix of ONE file instead of 140 KB spread over eight, and
# that defeating it requires editing THREE files that pin each other:
# `verify_all.py` (this constant), `formal/z3/source_pins.py` (the tables) and
# `formal/run_checks.sh` (check 0, which re-derives both digests in a fresh
# `python -I -S` before any check runs).  See FORMAL_VERIFICATION.md §2f.
sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

# The CODE digest of formal/z3/source_pins.py: its AST with the module-level
# `PINS = {...}` and `FILES = {...}` assignments blanked.  Blanking them is what
# makes the two files' mutual pins terminate -- regenerating the tables cannot
# move this constant, and moving this constant cannot invalidate the tables.
# Regenerate with:  formal/z3/source_pins.py --code-digest
#
# BLANKING IS ONLY SOUND FOR INERT DATA.
# A dict display is executable code -- Python evaluates every value expression
# and a duplicate key is simply overwritten -- so a blanked region can be
# arbitrary code covered by nothing.  ONE line inside `PINS = {...}`,
#     'kernel_obligations::@@file': exec("<builtins.open shim>") or '<real hash>',
# is line-count-neutral, leaves the table's value byte-identical, and yields
# `anchor OK` with all four digests unchanged and ALL CHECKS PASS
# over a tree with a real defect in the shipped Ntt.sol.  `_anchor_code_digest`
# therefore REFUSES unless both tables are dict displays whose every key and
# value is a string CONSTANT, at column 0, alone on their first and last line.
SOURCE_PINS_CODE_SHA256 = "6d25f56d8eed4e1e87312829bc9b0b7e"

# The BYTE digest of formal/run_checks.sh with its six `ANCHOR_*=` lines blanked.
# Regenerate with:  formal/z3/source_pins.py --check-script-digest
#
# THE SECOND zero-anchor route.  `run_checks.sh` is the DRIVER, and a single
# row of `FILES` -- inside the blanked table -- is not enough to pin it.
# Replacing check 1's invocation with one that injects an `open()` shim, plus
# that one row, is TWO files, ONE hash literal, and no anchor movement: check 0
# still prints `anchor OK` verbatim and the tally is still fully green.
# The driver is pinned instead by a constant that is NOT in a blanked region, and
# this file checks it BEFORE the suite runs -- so running check 1 on its own
# (`MLDSA_REPO=$PWD python3 formal/z3/verify_all.py`) detects a tampered driver.
# The ANCHOR_* lines must be blanked (they hold digests OF this file, so
# digesting them would be a cycle) and they are held to the same inertness rule:
# each must be exactly `ANCHOR_NAME="<hex/version>"` and there must be six.
# RESIDUAL, stated plainly: whoever controls the driver controls every process
# the driver launches, including this one, so a driver payload that ALSO shims
# this file's reads of run_checks.sh still passes.  What this buys is that the
# cheapest such attack is no longer a hash swap in a table documented as inert;
# it is an interpreter shim visible in the driver's own diff.  See
# FORMAL_VERIFICATION.md §2f and the §FV.6 row of formal/hypotheses.py.
RUN_CHECKS_SH_SHA256 = "4fcc3e2f82f80c44082afd4769488a3d"

_ANCHOR_DIR = os.path.dirname(os.path.abspath(__file__))
_ANCHOR_TABLES = ("PINS", "FILES")
# formal/run_checks.sh, relative to _ANCHOR_DIR, and the shape of a blanked line
_ANCHOR_CHECK_SCRIPT = os.path.join(_ANCHOR_DIR, "..", "run_checks.sh")
_ANCHOR_CHECK_RE = re.compile(r'^ANCHOR_[A-Z0-9_]+="[0-9a-f. ]*"$')
_ANCHOR_CHECK_LINES = 6
# every module this file LOADS and executes, in load order
_ANCHOR_MODULES = ("source_pins", "kernel_obligations")
# {label: {"path":..., "sha256":..., "ast":..., "text":...}} for every module
# whose bytes this process executed, INCLUDING this file.  META-PINS asserts the
# registry against the pinned tables, so "verified" and "executed" cannot drift.
LOADED_MODULES = {}


def _anchor_digest(text):
    """The same whole-AST digest source_pins.ast_digest computes, standalone.

    Deliberately duplicated: the anchor must not call into the file it is about
    to verify.  Keep in step with source_pins.ast_digest / _digest.
    """
    return hashlib.sha256(ast.unparse(ast.parse(text)).encode("utf-8")
                          + b"\0").hexdigest()[:32]


def _anchor_refuse(why):
    """Fail closed and LOUD.  Never a FAIL row -- the reporting channel is
    itself hijackable, so the anchor does not use it."""
    bar = "!" * 78
    for stream in (sys.stdout, sys.stderr):
        print(bar, file=stream)
        print("REFUSING TO RUN — formal/z3/verify_all.py TRUST ANCHOR", file=stream)
        print(f"  {why}", file=stream)
        print("  The suite verifies its own source before it verifies anything "
              "else.  Nothing was proved.", file=stream)
        print("  If this change was deliberate: review the diff, then "
              "`formal/z3/source_pins.py --write`", file=stream)
        print("  and update SOURCE_PINS_CODE_SHA256 / formal/run_checks.sh check 0 "
              "from `--code-digest`.", file=stream)
        print(bar, file=stream)
        stream.flush()
    raise SystemExit(2)


def raw_bytes(path):
    """`path`'s bytes, read through RAW FILE DESCRIPTORS.

    A `builtins.open` shim that serves forged text to the checker defeats any
    read that goes through the ordinary file API -- both the inert-data table
    payload and the driver route rest on exactly that.  Every read
    that decides whether something is the reviewed artefact goes through
    `os.open`/`os.read` here instead, so replacing `builtins.open` (or `io.open`,
    or the `open` global of this module) is not enough.  This is
    defence-in-depth and NOT a boundary: a shim that also patches `os.read`
    defeats it, and nothing in-band can stop that.  It is the reason the
    remaining driver attack has to be a visibly hostile diff -- see the §FV.6
    row of formal/hypotheses.py.
    """
    fd = os.open(path, os.O_RDONLY)
    try:
        chunks = []
        while True:
            b = os.read(fd, 1 << 20)
            if not b:
                return b"".join(chunks)
            chunks.append(b)
    finally:
        os.close(fd)


def _anchor_read(path):
    """(bytes, text) — bytes are what is digested, text is what is executed.

    A PEP-263 encoding declaration other than utf-8 would make CPython compile
    something other than what these bytes decode to, so it is refused here.
    """
    try:
        raw = raw_bytes(path)
    except OSError as exc:
        _anchor_refuse(f"cannot read a module it must verify: {path}: {exc!r}")
    for line in raw.split(b"\n", 2)[:2]:
        m = re.match(rb"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)", line)
        if m and m.group(1).lower().replace(b"_", b"-") not in (b"utf-8", b"utf8"):
            _anchor_refuse(f"{path} declares source encoding {m.group(1)!r}; the "
                           "digest reads utf-8 bytes, so the compiled text could "
                           "differ from the digested text")
    return raw, raw.decode("utf-8")


def _anchor_no_shadowing_bytecode(name):
    """REFUSE if any `.pyc` could shadow module `name` and be executed instead.

    Checked on the module's own directory and on every `sys.path` entry, for both
    the PEP-3147 cache layout and a legacy sibling `.pyc`.
    """
    tag = sys.implementation.cache_tag
    for d in [_ANCHOR_DIR] + [p for p in sys.path if p]:
        for cand in (os.path.join(d, "__pycache__", f"{name}.{tag}.pyc"),
                     os.path.join(d, "__pycache__", f"{name}.pyc"),
                     os.path.join(d, f"{name}.pyc")):
            if os.path.exists(cand):
                _anchor_refuse(f"bytecode that can shadow {name}.py exists: {cand} "
                               "— delete it (a .pyc can shadow the .py an auditor reads)")


def _anchor_code_digest(text):
    """`text`'s AST digest with source_pins' two pinned tables blanked.

    More than one module-level assignment to either table name is REFUSED: a
    decoy table would otherwise be blanked here and then shadow the real one at
    runtime (Python keeps the last module-level binding).

    THE INERT-DATA RULE: what is blanked must be provably INERT DATA.  A dict
    display is executable code, so every key and every value must be a string
    CONSTANT; and because the version-independent counterpart of this digest
    blanks whole LINES, the assignment must start at column 0 with nothing else
    on its first or last line.
    """
    tree = ast.parse(text)
    lines = text.split("\n")
    seen, bad = {}, []
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in _ANCHOR_TABLES:
            nm = node.targets[0].id
            seen[nm] = seen.get(nm, 0) + 1
            val = node.value
            if not isinstance(val, ast.Dict):
                bad.append(f"{nm} is {type(val).__name__}, not a dict display")
            else:
                for item in list(val.keys) + list(val.values):
                    if item is None:
                        bad.append(f"{nm}: `**` unpacking in the table")
                    elif not (isinstance(item, ast.Constant)
                              and isinstance(item.value, str)):
                        bad.append(f"{nm}: line {getattr(item, 'lineno', 0)}: "
                                   f"{type(item).__name__} where a string literal "
                                   "is required")
            if node.col_offset != 0 \
                    or lines[node.end_lineno - 1][node.end_col_offset:].strip():
                bad.append(f"{nm}: other code shares the table's first or last line")
            node.value = ast.Dict(keys=[], values=[])
    if bad:
        _anchor_refuse("source_pins.py's BLANKED tables are not inert data — "
                       + "; ".join(bad[:3]) + " — a dict display is EXECUTABLE "
                       "code and the blanked region is covered by no "
                       "digest")
    if sorted(seen) != sorted(_ANCHOR_TABLES) or set(seen.values()) != {1}:
        _anchor_refuse(f"source_pins.py assigns its pinned tables {seen} times at "
                       f"module level; expected exactly one each of "
                       f"{list(_ANCHOR_TABLES)} — a duplicate would shadow the real "
                       "table at runtime")
    return hashlib.sha256(ast.unparse(ast.fix_missing_locations(tree))
                          .encode("utf-8") + b"\0").hexdigest()[:32]


def _anchor_check_script():
    """REFUSE if formal/run_checks.sh is not the pinned driver.

    Absent is NOT a failure here: `vacuity_audit.py` copies the three z3 modules
    into a temp directory that has no driver at all, and there a driver cannot
    be the attack.  In the repository, a deleted or renamed `run_checks.sh` is a
    FAIL of META-PINS.every_pinned_file_present, which is a `FILES` row.
    """
    path = os.path.abspath(_ANCHOR_CHECK_SCRIPT)
    if not os.path.isfile(path):
        return "absent (not a repository tree — see META-PINS)"
    raw, text = _anchor_read(path)
    lines, n, bad = text.split("\n"), 0, []
    for i, line in enumerate(lines):
        if not line.startswith("ANCHOR_"):
            continue
        n += 1
        if not _ANCHOR_CHECK_RE.match(line):
            bad.append(f"line {i + 1}: {line[:56]!r} is not a plain "
                       "hex/version string assignment")
        lines[i] = "@@ANCHOR BLANKED@@"
    if n != _ANCHOR_CHECK_LINES:
        bad.append(f"{n} ANCHOR_* lines, expected {_ANCHOR_CHECK_LINES}")
    if bad:
        _anchor_refuse("run_checks.sh's BLANKED anchor lines are not inert data — "
                       + "; ".join(bad[:3]))
    got = hashlib.sha256("\n".join(lines).encode("utf-8") + b"\0").hexdigest()[:32]
    if got != RUN_CHECKS_SH_SHA256:
        _anchor_refuse(f"run_checks.sh digest {got} != pinned {RUN_CHECKS_SH_SHA256} "
                       "— the CHECK SCRIPT that drives every check is not the "
                       "reviewed one (this closes the second zero-anchor "
                       "route: the driver is otherwise pinned only by a row of the BLANKED "
                       "FILES table).  Regenerate with "
                       "`formal/z3/source_pins.py --check-script-digest`.")
    return got


def _anchor_exec(name, raw, text):
    """Execute exactly the text that was digested, with no import machinery."""
    path = os.path.join(_ANCHOR_DIR, name + ".py")
    mod = types.ModuleType(name)
    mod.__file__ = path
    sys.modules[name] = mod
    try:
        exec(compile(text, path, "exec"), mod.__dict__)
    except Exception as exc:
        _anchor_refuse(f"{name}.py failed to execute: {exc!r}")
    LOADED_MODULES[name] = dict(path=path, text=text, ast=_anchor_digest(text),
                               sha256=hashlib.sha256(raw).hexdigest()[:32])
    return mod


def _anchor():
    """Verify, then load, then verify this file.  Returns the source_pins module."""
    if not __debug__:
        _anchor_refuse("running with -O: `assert` statements are stripped and "
                       "several checks in this apparatus are asserts")
    for name in _ANCHOR_MODULES:
        _anchor_no_shadowing_bytecode(name)
    LOADED_MODULES["run_checks.sh"] = dict(path=os.path.abspath(_ANCHOR_CHECK_SCRIPT),
                                          digest=_anchor_check_script())
    sp_raw, sp_text = _anchor_read(os.path.join(_ANCHOR_DIR, "source_pins.py"))
    got = _anchor_code_digest(sp_text)
    if got != SOURCE_PINS_CODE_SHA256:
        _anchor_refuse(f"source_pins.py CODE digest {got} != pinned "
                       f"{SOURCE_PINS_CODE_SHA256} — the digesting machinery "
                       "itself has been edited")
    sp = _anchor_exec("source_pins", sp_raw, sp_text)
    LOADED_MODULES["source_pins"]["code"] = got
    self_raw, self_text = _anchor_read(os.path.abspath(__file__))
    self_ast = _anchor_digest(self_text)
    pinned_self = getattr(sp, "PINS", {}).get("verify_all::@@file")
    if self_ast != pinned_self:
        _anchor_refuse(f"verify_all.py whole-file AST digest {self_ast} != pinned "
                       f"{pinned_self} — this file is not the file that was "
                       "reviewed (nothing here is exempt from its own AST digest)")
    LOADED_MODULES["verify_all"] = dict(path=os.path.abspath(__file__),
                                       text=self_text, ast=self_ast,
                                       sha256=hashlib.sha256(self_raw).hexdigest()[:32])
    ko_raw, ko_text = _anchor_read(os.path.join(_ANCHOR_DIR, "kernel_obligations.py"))
    ko_ast = _anchor_digest(ko_text)
    pinned_ko = getattr(sp, "PINS", {}).get("kernel_obligations::@@file")
    if ko_ast != pinned_ko:
        _anchor_refuse(f"kernel_obligations.py whole-file AST digest {ko_ast} != "
                       f"pinned {pinned_ko}")
    _anchor_exec("kernel_obligations", ko_raw, ko_text)
    return sp


SOURCE_PINS = _anchor()
# ===========================================================================
# end of the trust anchor
# ===========================================================================

# Repo root, for the obligations that cross-check the SHIPPED Solidity/Yul (C16).
# Overridable so the suite can be copied elsewhere (the vacuity audit does exactly
# that); if the source cannot be read the obligation FAILS -- never a silent skip.
REPO_ROOT = os.environ.get("MLDSA_REPO") or os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))

# Per-solver-call budget.  Every proof in this suite is discharged in a few
# milliseconds (each obligation prints its slowest call), so this is three orders
# of magnitude of headroom; it exists so that a MUTATED suite -- the vacuity audit
# runs 232 of them -- cannot sit for two minutes per falsified conjunct.  A
# `timeout`/`unknown` verdict is treated as a FAILED conjunct, never as a proof.
SMT_TIMEOUT_MS = int(os.environ.get("MLDSA_SMT_TIMEOUT_MS", "20000"))

Q = 8380417                  # ML-DSA modulus
N = 256                      # ring degree
L_DIM = 4                    # k = l = 4
GAMMA1 = 1 << 17
GAMMA2 = 95232
BETA = 78
TAU = 39
D_SHIFT = 13
OMEGA = 80
# The two-step LANE-LOCAL Barrett of src/Ntt.sol / src/InvNtt.sol.  Step 1 is a
# coarse Barrett whose product fits a 64-bit SWAR lane (which is the whole point:
# no spreading, no repack); step 2 is the same Barrett step with mu = 1, which is
# floor(2^23/Q) because Q = 2^23 - 2^13 + 1, so its multiply is elided.
MU33 = 1025                  # floor(2^33 / Q), forward+inverse coarse constant
SH1 = 33                     # step 1's shift
MU23 = 1                     # floor(2^23 / Q), step 2's (elided) constant
SH2 = 23                     # step 2's shift

# ---------------------------------------------------------------------------
# THE PK-CANONICALITY PREMISE, MADE EXPLICIT
# ---------------------------------------------------------------------------
# Every lane bound downstream of the matrix-vector product was written with a
# literal `Q - 1` standing for "the largest pk coefficient", so the premise
# "the cached Ahat/t1hat coefficients are CANONICAL (< q)" was carried inside an
# arithmetic expression instead of being stated.  It is not a free premise: the
# coefficient fields are 32 bits and q < 2^32, so a congruent-but-LIFTED blob
# (t1hat[i] += 4q, Ahat[i] += 128q, ...) passes every structural check the chain
# can apply, and MEASURED on the deployed artefact it makes a VALID signature
# REJECT -- the inverse transform's entry fold `sub(add(u0, ACCQ30), u1)` is
# correct at ACCQ30 = q*2^30 and silently wrong one unit past it while still
# emitting canonical-looking lanes, so nothing downstream can notice.  The
# headroom is 1.28x and it exists ONLY because a < q.
#
# `PK_AMAX` is therefore a PARAMETER of the accumulator ceiling, used by C9g,
# S14 and (through the same shape) O7/O8, and C9g carries a discrimination
# control asserting that the domination FAILS at PK_AMAX = 2q.  docs/SAFETY.md
# section 3 states the same fact as a SOUNDNESS PRECONDITION on the registrar.
PK_AMAX = Q                  # pk coefficients (Ahat, t1hat) are canonical: < q


def acc_entry(amax):
    """matvecRow's accumulator lane ceiling when pk coefficients are < `amax`.

    4 products of (pk coefficient < amax) x (LAZY forward-NTT lane <= 17q-1),
    plus the KQ28 = q*2^28 borrow-prevention offset (O8).
    """
    return 4 * (amax - 1) * (17 * Q - 1) + (Q << 28)


def entry_offset_dominates(amax):
    """S14's no-borrow premise at a pk-coefficient ceiling of `amax`.

    True at amax = q (1.28x of headroom) and FALSE at 2q: past the offset the
    EVM subtraction wraps out of the residue class and the entry fold is wrong
    WITHOUT being detectable downstream (FV6 measures exactly that cliff).
    """
    e = acc_entry(amax)
    return e <= (Q << 30) and 2 * e <= (Q << 31)

# ---------------------------------------------------------------------------
# The obligation and conjunct ID sets are ASSERTED, not merely printed.
# `python3 verify_all.py --print-ids` regenerates these two lists.
# ---------------------------------------------------------------------------
# The two sets are SELF-INCLUSIVE: META-IDS's own rows are members of both.
# Were they excluded, the assertion would sit outside the set it guards (`main`).
EXPECTED_OBLIGATIONS = [
    'C1',
    'C1b',
    'C9a',
    'C9b',
    'C9c',
    'C9d',
    'C9e',
    'C9h',
    'C11a',
    'C11b',
    'C11c',
    'C11d',
    'C9f',
    'C9g',
    'C16',
    'C18',
    'E15',
    'C10',
    'C10b',
    'C15b',
    'C15c',
    'C17',
    'S1',
    'S2',
    'S3',
    'S4',
    'S5',
    'S6',
    'S6b',
    'S7',
    'S8',
    'S8b',
    'S11',
    'S11b',
    'S13',
    'S14',
    'E1',
    'E2',
    'E3',
    'E4',
    'E5',
    'E6',
    'E3b',
    'E4b',
    'E5b',
    'E12',
    'E13',
    'E14',
    'E9a',
    'E9b',
    'O1',
    'O2',
    'O3',
    'O4',
    'O5',
    'O6',
    'O7',
    'O8',
    'O9',
    'O10',
    'META-PINS',
    'META-IDS',
]
EXPECTED_CONJUNCTS = [
    'C1.ctl_accepts_0',
    'C1.ctl_rejects_0',
    'C1.ctl_rejects_1',
    'C1.ctl_rejects_2',
    'C1.ctl_rejects_3',
    'C1b.q_is_2p23_minus_2p13_plus_1',
    'C1b.two_p23_minus_q_is_8191',
    'C1b.ctl_accepts_0',
    'C1b.ctl_rejects_0',
    'C1b.ctl_rejects_1',
    'C1b.ctl_rejects_2',
    'C9a.ctl_accepts_0',
    'C9a.ctl_accepts_1',
    'C9a.ctl_rejects_0',
    'C9a.ctl_rejects_1',
    'C9b.ctl_accepts_0',
    'C9b.ctl_accepts_1',
    'C9b.ctl_rejects_0',
    'C9b.ctl_rejects_1',
    'C9c.ctl_accepts_0',
    'C9c.ctl_accepts_1',
    'C9c.ctl_rejects_0',
    'C9c.ctl_rejects_1',
    'C9d.ctl_accepts_0',
    'C9d.ctl_accepts_1',
    'C9d.ctl_rejects_0',
    'C9d.ctl_rejects_1',
    'C9e.ctl_accepts_0',
    'C9e.ctl_accepts_1',
    'C9e.ctl_rejects_0',
    'C9e.ctl_rejects_1',
    'C9h.max_qhat_lt_2p31',
    'C9h.mask_width_is_64_minus_shift',
    'C9h.qhat_bound_iff_lane_local',
    'C9h.step2_quotient_fits_mask',
    'C9h.step2_neighbour_above_mask',
    'C9h.ctl_accepts_0',
    'C9h.ctl_rejects_0',
    'C9h.ctl_rejects_1',
    'C9h.ctl_rejects_2',
    'C11a.fails_at',
    'C11a.ok_below',
    'C11a.ctl_accepts_0',
    'C11a.ctl_accepts_1',
    'C11a.ctl_accepts_2',
    'C11a.ctl_accepts_3',
    'C11a.ctl_accepts_4',
    'C11a.ctl_rejects_0',
    'C11b.ctl_accepts_0',
    'C11b.ctl_accepts_1',
    'C11b.ctl_rejects_0',
    'C11b.ctl_rejects_1',
    'C11c.ctl_accepts_0',
    'C11c.ctl_accepts_1',
    'C11c.ctl_rejects_0',
    'C11c.ctl_rejects_1',
    'C11d.overflows_at',
    'C11d.fits_below',
    'C11d.inv_worst_is_lane_local',
    'C11d.ctl_accepts_0',
    'C11d.ctl_accepts_1',
    'C11d.ctl_rejects_0',
    'C11d.ctl_rejects_1',
    'C11d.ctl_rejects_2',
    'C9f.premise_LB_le_15q_every_layer',
    'C9f.max_barrett_input_is_15q_qm1',
    'C9f.barrett_input_inside_S1_domain',
    'C9f.barrett_input_below_first_fail',
    'C9f.final_lane_is_17q',
    'C9f.final_lane_lt_2p28',
    'C9f.ctl_rejects_0',
    'C9f.ctl_rejects_1',
    'C9f.ctl_rejects_2',
    'C9f.ctl_rejects_3',
    'C9f.ctl_rejects_4',
    'C9g.entry_is_O8_lane_max',
    'C9g.pk_coefficient_ceiling_is_q',
    'C9g.l1_offset_dominates_entry',
    'C9g.l2_offset_dominates_sum_lane',
    'C9g.l1l2_exit_meets_l3_premise',
    'C9g.max_barrett_input_is_128q_qm1',
    'C9g.barrett_input_inside_S2_domain',
    'C9g.barrett_input_below_first_fail',
    'C9g.max_sum_lane_is_256q',
    'C9g.max_sum_lane_lt_2p31',
    'C9g.layer8_lane_product_lt_2p64',
    'C9g.ctl_pk_canonical_premise_accepts_0',
    'C9g.ctl_pk_canonical_premise_accepts_1',
    'C9g.ctl_pk_canonical_premise_accepts_2',
    'C9g.ctl_pk_canonical_premise_rejects_0',
    'C9g.ctl_pk_canonical_premise_rejects_1',
    'C9g.ctl_pk_canonical_premise_rejects_2',
    'C9g.ctl_rejects_0',
    'C9g.ctl_rejects_1',
    'C9g.ctl_rejects_2',
    'C9g.ctl_rejects_3',
    'C9g.ctl_rejects_4',
    'C9g.ctl_rejects_5',
    'C16.fwd_MU33',
    'C16.inv_MU33',
    'C16.fwd_QHATM31_is_2p31m1_per_lane',
    'C16.inv_QHATM31_is_2p31m1_per_lane',
    'C16.fwd_constants_are_exactly_the_derived_set',
    'C16.inv_constants_are_exactly_the_derived_set',
    'C16.fwd_TWOQ4_is_2q_per_lane',
    'C16.fwd_TWOQ_is_2q',
    'C16.fwd_every_butterfly_offsets_by_2q',
    'C16.inv_ACCQ30_is_q_shl_30',
    'C16.inv_ACCQ31_is_q_shl_31',
    'C16.inv_TWOQ_is_2q',
    'C16.inv_TWOQ4_is_2q_per_lane',
    'C16.inv_Q4_4_is_4q_per_lane',
    'C16.inv_Q4_8_is_8q_per_lane',
    'C16.inv_Q4_16_is_16q_per_lane',
    'C16.inv_Q4_32_is_32q_per_lane',
    'C16.inv_Q4_64_is_64q_per_lane',
    'C16.inv_Q4_128_is_128q_per_lane',
    'C16.inv_layer8_canonicalises_with_mod',
    'C16.inv_layer8_no_extra_mod_elsewhere',
    'C16.fwd_schedule_extracted_is_plus_2q_x8',
    'C16.inv_schedule_extracted_is_K_2powL',
    'C16.fwd_every_reduction_has_both_steps',
    'C16.inv_every_reduction_has_both_steps',
    'C16.fwd_head_and_tail_are_inert',
    'C16.inv_head_and_tail_are_inert',
    'C16.fwd_every_plain_block_offsets_every_butterfly',
    'C16.inv_every_plain_block_offsets_every_butterfly',
    'C16.fwd_region_summary_is_the_pinned_one',
    'C16.inv_region_summary_is_the_pinned_one',
    'C16.fwd_body_digest_is_the_pinned_one',
    'C16.inv_body_digest_is_the_pinned_one',
    'C16.all_shipped_fwd_copies_agree',
    'C16.all_shipped_inv_copies_agree',
    'C16.fwd_shipped_sources_are_the_pinned_bytes',
    'C16.inv_shipped_sources_are_the_pinned_bytes',
    'C16.ctl_fwd_nine_layers_rejects_0',
    'C16.ctl_fwd_layer_offset_4q_rejects_0',
    'C16.ctl_fwd_extra_mod_layer_rejects_0',
    'C16.ctl_fwd_tail_canonicalises_again_rejects_0',
    'C16.ctl_fwd_unpaired_diff_store_rejects_0',
    'C16.ctl_fwd_one_tail_mulmod_dropped_rejects_0',
    'C16.ctl_fwd_barrett_back_in_the_tail_rejects_0',
    'C16.ctl_fwd_one_second_step_dropped_rejects_0',
    'C16.ctl_fwd_one_octet_butterfly_dropped_rejects_0',
    'C16.ctl_fwd_octet_block_is_only_radix4_rejects_0',
    'C16.ctl_inv_seven_blocks_rejects_0',
    'C16.ctl_inv_layer7_K_doubled_rejects_0',
    'C16.ctl_inv_barrett_at_layer8_rejects_0',
    'C16.ctl_inv_mod_in_a_barrett_block_rejects_0',
    'C16.ctl_inv_layer8_not_canonicalised_rejects_0',
    'C16.ctl_inv_one_second_step_dropped_rejects_0',
    'C16.ctl_inv_entry_fold_dropped_rejects_0',
    'C16.ctl_inv_one_entry_mulmod_dropped_rejects_0',
    'C16.ctl_fwd_payload_before_first_marker_rejects_0',
    'C16.ctl_fwd_payload_after_last_marker_rejects_0',
    'C16.ctl_fwd_one_offset_dropped_in_a_block_rejects_0',
    'C16.ctl_inv_payload_before_first_marker_rejects_0',
    'C16.ctl_inv_payload_after_last_marker_rejects_0',
    'C16.ctl_inv_one_offset_dropped_in_a_block_rejects_0',
    'C16.ctl_fwd_accepts_the_shipped_shape_accepts_0',
    'C16.ctl_inv_accepts_the_shipped_shape_accepts_0',
    'C18.dec_MLDSA_Q_is_q',
    'C18.dec_Z_M18_is_the_18_bit_field_mask_per_lane',
    'C18.dec_Z_UOFF_is_q_plus_gamma1_per_lane',
    'C18.dec_Z_QB32_is_2p32_minus_q_per_lane',
    'C18.dec_Z_BIT32_is_the_flag_bit_per_lane',
    'C18.dec_Z_NLO_is_the_low_window_edge_per_lane',
    'C18.dec_Z_NHI_is_the_high_window_edge_per_lane',
    'C18.dec_Z_P2_is_2p62_plus_2p16',
    'C18.dec_Z_P4_is_2p124_plus_2p78',
    'C18.dec_Z_P6_is_2p186_plus_2p140',
    'C18.dec_SW_REP1_is_one_per_lane',
    'C18.dec_SW_REP6_is_the_6_bit_mask_per_lane',
    'C18.dec_SW_K32G2_is_the_gamma2_comparator_per_lane',
    'C18.dec_SW_K321_is_the_nonzero_comparator_per_lane',
    'C18.dec_SW_GATHERK_is_the_four_gather_powers',
    'C18.dec_SW_MDIV_is_ceil_2p39_over_two_gamma2',
    'C18.dec_SW_D_is_two_gamma2',
    'C18.dec_SW_M44_is_ceil_2p12_over_44',
    'C18.dec_MV_M32_is_the_32_bit_coefficient_field_mask',
    'C18.dec_MV_L0_is_lane_0_of_the_pre_shifted_lane_mask',
    'C18.dec_MV_L1_is_lane_1_of_the_pre_shifted_lane_mask',
    'C18.dec_MV_L2_is_lane_2_of_the_pre_shifted_lane_mask',
    'C18.dec_MV_L3_is_lane_3_of_the_pre_shifted_lane_mask',
    'C18.dec_MV_KQ28REP_is_q_times_2p28_per_lane',
    'C18.ver_PK_SIZE_is_the_C15b_blob_width',
    'C18.ver_PK_T1_OFF_is_t1hat_after_the_64_byte_tr',
    'C18.ver_PK_A_OFF_is_Ahat_after_t1hat',
    'C18.kec__M64_170_is_the_64_bit_lane_mask',
    'C18.dec_no_dead_constants_remain',
    'C18.ver_no_dead_constants_remain',
    'C18.dec_constant_set_is_exactly_the_modelled_set',
    'C18.dec_every_constant_is_read_outside_its_declaration',
    'C18.ver_constant_set_is_exactly_the_modelled_set',
    'C18.ver_every_constant_is_read_outside_its_declaration',
    'C18.kec_constant_set_is_exactly_the_modelled_set',
    'C18.kec_every_constant_is_read_outside_its_declaration',
    'C18.dec_z_norm_gate_sites_is_4',
    'C18.dec_z_canonicalisation_sites_is_4',
    'C18.dec_z_quad_loop_trip_is_16',
    'C18.dec_z_driver_runs_all_4_polynomials',
    'C18.dec_z_slice_is_the_encoding_width',
    'C18.dec_z_gate_is_four_lanes_wide',
    'C18.dec_z_verdict_word_is_read_once',
    'C18.dec_z_gates_cover_all_1024_coefficients',
    'C18.dec_h_omega_gate_is_80',
    'C18.dec_h_scan_clamp_is_80',
    'C18.dec_h_counter_word_is_the_last_32_bytes',
    'C18.dec_h_pad_s1_threshold_is_the_w1_boundary',
    'C18.dec_h_pad_s2_threshold_is_the_w2_boundary',
    'C18.dec_h_pad_w1_covers_index_bytes_32_63',
    'C18.dec_h_pad_w2_covers_index_bytes_64_79',
    'C18.dec_h_pad_word_boundaries_are_the_shift_thresholds',
    'C18.dec_h_strict_increase_gate_present',
    'C18.dec_h_monotone_counter_gate_present',
    'C18.dec_h_padding_gate_present',
    'C18.dec_mod44_magic_shift_is_12',
    'C18.dec_mod44_subtrahend_is_44',
    'C18.dec_mod44_magic_is_ceil_2pow_shift_over_44',
    'C18.dec_swar_magic_shift_is_39',
    'C18.dec_swar_magic_is_ceil_2pow_shift_over_two_gamma2',
    'C18.ver_signature_length_is_2420',
    'C18.ver_hint_weight_bound_is_omega',
    'C18.ver_mu_preimage_is_66_plus_message',
    'C18.ver_tr_is_64_bytes_at_code_offset_1',
    'C18.ver_pk_size_gate_is_exact',
    'C18.ver_helper_is_pinned_at_construction_and_per_call',
    'C18.ver_pk_size_gate_constant_is_the_proved_width',
    'C18.ver_implements_the_pinned_interface',
    'C18.kec_domain_pad_byte_is_the_shake_0x1f',
    'C18.kec_final_pad_bit_is_0x80_in_the_last_word_of_the_rate_block',
    'C18.kec_sponge_rate_is_136_at_every_site',
    'C18.kec_squeeze_block_count_rounds_up_by_the_rate',
    'C18.kec_raw_permutation_is_800_bytes_in_and_out',
    'C18.kec_raw_permutation_gate_is_returndatasize_800',
    'C18.kec_batched_sponge_gate_is_returndatasize_136',
    'C18.kec_batched_outlen_gate_is_one_rate_block',
    'C18.kec_batched_path_refuses_the_800_byte_dispatch_collision',
    'C18.kec_raw_output_buffer_is_rounded_up_to_a_whole_word',
    'C18.kec_lane16_windows_end_flush_with_the_rate_block',
    'C18.ifc_declares_exactly_the_external_view_verify_entry_point',
    'C18.dec_shipped_source_is_the_pinned_bytes',
    'C18.ver_shipped_source_is_the_pinned_bytes',
    'C18.kec_shipped_source_is_the_pinned_bytes',
    'C18.ifc_shipped_source_is_the_pinned_bytes',
    'C18.fv2_declares_the_pinned_check_census',
    'C18.fv2_carries_the_shipped_scalar_two_step_kernel',
    'C18.fv2_carries_the_shipped_packed_two_step_kernel',
    'C18.fv2_refinement_harness_is_the_pinned_bytes',
    'C18.ctl_extracted_value_is_the_proved_value_accepts_0',
    'C18.ctl_extracted_value_is_the_proved_value_accepts_1',
    'C18.ctl_extracted_value_is_the_proved_value_accepts_2',
    'C18.ctl_extracted_value_is_the_proved_value_rejects_0',
    'C18.ctl_extracted_value_is_the_proved_value_rejects_1',
    'C18.ctl_extracted_value_is_the_proved_value_rejects_2',
    'C18.ctl_extracted_value_is_the_proved_value_rejects_3',
    'E15.canonical_weight_zero_accepted',
    'E15.grid_reaches_the_second_word_boundary',
    'E15.scan_clamp_keeps_the_index_scan_inside_the_index_array',
    'E15.ctl_scan_clamp_accepts_0',
    'E15.ctl_scan_clamp_accepts_1',
    'E15.ctl_scan_clamp_rejects_0',
    'E15.ctl_scan_clamp_rejects_1',
    'E15.ctl_scan_clamp_rejects_2',
    'E15.ctl_accepts_0',
    'E15.ctl_rejects_0',
    'E15.ctl_rejects_1',
    'E15.ctl_rejects_2',
    'E15.ctl_rejects_3',
    'E15.ctl_rejects_4',
    'E15.ctl_rejects_5',
    'E15.ctl_rejects_6',
    'E15.ctl_rejects_7',
    'E15.ctl_rejects_8',
    'E15.ctl_rejects_9',
    'C10.dp_is_proper',
    'C10.tail_lt_2^-200',
    'C10.ctl_accepts_0',
    'C10.ctl_accepts_1',
    'C10.ctl_accepts_2',
    'C10.ctl_rejects_0',
    'C10.ctl_rejects_1',
    'C10.ctl_rejects_2',
    'C10.ctl_rejects_3',
    'C10b.ge_tau',
    'C10b.lt_64',
    'C10b.ctl_accepts_0',
    'C10b.ctl_accepts_1',
    'C10b.ctl_accepts_2',
    'C10b.ctl_rejects_0',
    'C10b.ctl_rejects_1',
    'C10b.ctl_rejects_2',
    'C10b.ctl_rejects_3',
    'C10b.ctl_rejects_4',
    'C15b.shipped_PK_SIZE_is_this_width',
    'C15b.shipped_PK_T1_OFF_is_after_tr',
    'C15b.shipped_PK_A_OFF_is_after_t1hat',
    'C15b.ctl_accepts_0',
    'C15b.ctl_rejects_0',
    'C15b.ctl_rejects_1',
    'C15b.ctl_rejects_2',
    'C15c.ctl_accepts_0',
    'C15c.ctl_rejects_0',
    'C15c.ctl_rejects_1',
    'C15c.ctl_rejects_2',
    'C17.exact_on_every_reachable_T',
    'C17.magic_is_ceil_2pow12_over_44',
    'C17.reachable_T_max_is_87',
    'C17.lane_product_lt_2p64',
    'C17.quotient_fits_the_rep1_mask',
    'C17.folding_the_two_reductions_is_exact',
    'C17.ctl_accepts_0',
    'C17.ctl_accepts_1',
    'C17.ctl_accepts_2',
    'C17.ctl_rejects_0',
    'C17.ctl_rejects_1',
    'C17.ctl_rejects_2',
    'C17.ctl_rejects_3',
    'S1.premises_sat',
    'S1.lane_product_lt_2p64',
    'S1.qhat_lt_2p31',
    'S1.step1_nonneg',
    'S1.step1_lt_2p33',
    'S1.r_nonneg',
    'S1.r_lt_2q',
    'S1.claims_discriminate',
    'S2.premises_sat',
    'S2.lane_product_lt_2p64',
    'S2.qhat_lt_2p31',
    'S2.step1_nonneg',
    'S2.step1_lt_2p33',
    'S2.r_nonneg',
    'S2.r_lt_2q',
    'S2.claims_discriminate',
    'S3.premises_sat',
    'S3.unique_rep_below_2q',
    'S3.claims_discriminate',
    'S4.premises_sat',
    'S4.unique_rep_below_2q',
    'S4.claims_discriminate',
    'S5.premises_sat',
    'S5.product_in_barrett_domain',
    'S5.product_is_lane_local',
    'S5.V_nonneg',
    'S5.V_lt_2q',
    'S5.sum_lane_lt_LB_plus_2q',
    'S5.diff_lane_nonneg',
    'S5.diff_lane_lt_LB_plus_2q',
    'S5.claims_discriminate',
    'S6.premises_sat',
    'S6.diff_lane_positive',
    'S6.diff_lane_lt_2Kq',
    'S6.product_in_verified_domain',
    'S6.product_is_lane_local',
    'S6.barrett_r_nonneg',
    'S6.barrett_r_lt_2q',
    'S6.sum_lane_lt_2Kq',
    'S6.claims_discriminate',
    'S6b.premises_sat',
    'S6b.sum_diff_positive',
    'S6b.sum_lane_product_fits_64',
    'S6b.diff_lane_product_fits_64',
    'S6b.d_diff_positive',
    'S6b.d_lane_products_fit_64',
    'S6b.d_diff_product_fits_64',
    'S6b.claims_discriminate',
    'S7.premises_sat',
    'S7.mul_no_2p256_overflow',
    'S7.step1_shift_is_the_lane_quotients',
    'S7.step2_shift_is_the_lane_quotients',
    'S7.lane0_qhat_is_the_shift',
    'S7.lane0_product_no_carry',
    'S7.lane0_qhat_lt_2p31',
    'S7.lane0_step1_no_borrow',
    'S7.lane0_step1_lt_2p33',
    'S7.lane0_step2_quotient_lt_2p31',
    'S7.lane0_no_borrow',
    'S7.lane0_fits_its_lane',
    'S7.lane0_step1_field_is_the_quotient',
    'S7.lane0_step2_field_is_the_quotient',
    'S7.lane0_recovered',
    'S7.lane1_qhat_is_the_shift',
    'S7.lane1_product_no_carry',
    'S7.lane1_qhat_lt_2p31',
    'S7.lane1_step1_no_borrow',
    'S7.lane1_step1_lt_2p33',
    'S7.lane1_step2_quotient_lt_2p31',
    'S7.lane1_no_borrow',
    'S7.lane1_fits_its_lane',
    'S7.lane1_step1_shift_exposes_the_field',
    'S7.lane1_step1_field_is_the_quotient',
    'S7.lane1_step2_shift_exposes_the_field',
    'S7.lane1_step2_field_is_the_quotient',
    'S7.lane1_shift_exposes_the_result',
    'S7.lane1_recovered',
    'S7.lane2_qhat_is_the_shift',
    'S7.lane2_product_no_carry',
    'S7.lane2_qhat_lt_2p31',
    'S7.lane2_step1_no_borrow',
    'S7.lane2_step1_lt_2p33',
    'S7.lane2_step2_quotient_lt_2p31',
    'S7.lane2_no_borrow',
    'S7.lane2_fits_its_lane',
    'S7.lane2_step1_shift_exposes_the_field',
    'S7.lane2_step1_field_is_the_quotient',
    'S7.lane2_step2_shift_exposes_the_field',
    'S7.lane2_step2_field_is_the_quotient',
    'S7.lane2_shift_exposes_the_result',
    'S7.lane2_recovered',
    'S7.lane3_qhat_is_the_shift',
    'S7.lane3_product_no_carry',
    'S7.lane3_qhat_lt_2p31',
    'S7.lane3_step1_no_borrow',
    'S7.lane3_step1_lt_2p33',
    'S7.lane3_step2_quotient_lt_2p31',
    'S7.lane3_no_borrow',
    'S7.lane3_fits_its_lane',
    'S7.lane3_step1_shift_exposes_the_field',
    'S7.lane3_step1_field_is_the_quotient',
    'S7.lane3_step2_shift_exposes_the_field',
    'S7.lane3_step2_field_is_the_quotient',
    'S7.lane3_shift_exposes_the_result',
    'S7.lane3_recovered',
    'S7.claims_discriminate',
    'S8.premises_sat',
    'S8.kernel_iff_fips',
    'S8.claims_discriminate',
    'S8b.premises_sat',
    'S8b.lane0_u_no_borrow',
    'S8b.lane0_u_lt_2q',
    'S8b.lane0_flag_word_no_carry',
    'S8b.lane0_flag_is_a_bit',
    'S8b.lane0_mask_exposes_the_flag',
    'S8b.lane0_flag_iff_u_ge_q',
    'S8b.lane0_correction_is_lane_local',
    'S8b.lane0_o_no_borrow',
    'S8b.lane0_o_canonical',
    'S8b.lane0_o_is_the_centered_map',
    'S8b.lane0_stored_lane_recovered',
    'S8b.lane0_low_edge_no_carry',
    'S8b.lane0_high_edge_no_borrow',
    'S8b.lane0_high_edge_no_carry',
    'S8b.lane0_low_edge_bit_is_a_bit',
    'S8b.lane0_high_edge_bit_is_a_bit',
    'S8b.lane0_low_edge_mask_exposes_the_flag',
    'S8b.lane0_high_edge_mask_exposes_the_flag',
    'S8b.lane0_low_edge_iff_o_ge_bound',
    'S8b.lane0_high_edge_iff_o_le_bound',
    'S8b.lane0_reject_iff_fips',
    'S8b.lane1_u_no_borrow',
    'S8b.lane1_u_lt_2q',
    'S8b.lane1_flag_word_no_carry',
    'S8b.lane1_flag_is_a_bit',
    'S8b.lane1_mask_exposes_the_flag',
    'S8b.lane1_flag_iff_u_ge_q',
    'S8b.lane1_correction_is_lane_local',
    'S8b.lane1_o_no_borrow',
    'S8b.lane1_o_canonical',
    'S8b.lane1_o_is_the_centered_map',
    'S8b.lane1_stored_lane_recovered',
    'S8b.lane1_low_edge_no_carry',
    'S8b.lane1_high_edge_no_borrow',
    'S8b.lane1_high_edge_no_carry',
    'S8b.lane1_low_edge_bit_is_a_bit',
    'S8b.lane1_high_edge_bit_is_a_bit',
    'S8b.lane1_low_edge_mask_exposes_the_flag',
    'S8b.lane1_high_edge_mask_exposes_the_flag',
    'S8b.lane1_low_edge_iff_o_ge_bound',
    'S8b.lane1_high_edge_iff_o_le_bound',
    'S8b.lane1_reject_iff_fips',
    'S8b.lane1_flag_shift_exposes_the_lane',
    'S8b.lane1_shift_exposes_the_stored_lane',
    'S8b.lane1_low_edge_shift_exposes_the_lane',
    'S8b.lane1_high_edge_shift_exposes_the_lane',
    'S8b.lane2_u_no_borrow',
    'S8b.lane2_u_lt_2q',
    'S8b.lane2_flag_word_no_carry',
    'S8b.lane2_flag_is_a_bit',
    'S8b.lane2_mask_exposes_the_flag',
    'S8b.lane2_flag_iff_u_ge_q',
    'S8b.lane2_correction_is_lane_local',
    'S8b.lane2_o_no_borrow',
    'S8b.lane2_o_canonical',
    'S8b.lane2_o_is_the_centered_map',
    'S8b.lane2_stored_lane_recovered',
    'S8b.lane2_low_edge_no_carry',
    'S8b.lane2_high_edge_no_borrow',
    'S8b.lane2_high_edge_no_carry',
    'S8b.lane2_low_edge_bit_is_a_bit',
    'S8b.lane2_high_edge_bit_is_a_bit',
    'S8b.lane2_low_edge_mask_exposes_the_flag',
    'S8b.lane2_high_edge_mask_exposes_the_flag',
    'S8b.lane2_low_edge_iff_o_ge_bound',
    'S8b.lane2_high_edge_iff_o_le_bound',
    'S8b.lane2_reject_iff_fips',
    'S8b.lane2_flag_shift_exposes_the_lane',
    'S8b.lane2_shift_exposes_the_stored_lane',
    'S8b.lane2_low_edge_shift_exposes_the_lane',
    'S8b.lane2_high_edge_shift_exposes_the_lane',
    'S8b.lane3_u_no_borrow',
    'S8b.lane3_u_lt_2q',
    'S8b.lane3_flag_word_no_carry',
    'S8b.lane3_flag_is_a_bit',
    'S8b.lane3_mask_exposes_the_flag',
    'S8b.lane3_flag_iff_u_ge_q',
    'S8b.lane3_correction_is_lane_local',
    'S8b.lane3_o_no_borrow',
    'S8b.lane3_o_canonical',
    'S8b.lane3_o_is_the_centered_map',
    'S8b.lane3_stored_lane_recovered',
    'S8b.lane3_low_edge_no_carry',
    'S8b.lane3_high_edge_no_borrow',
    'S8b.lane3_high_edge_no_carry',
    'S8b.lane3_low_edge_bit_is_a_bit',
    'S8b.lane3_high_edge_bit_is_a_bit',
    'S8b.lane3_low_edge_mask_exposes_the_flag',
    'S8b.lane3_high_edge_mask_exposes_the_flag',
    'S8b.lane3_low_edge_iff_o_ge_bound',
    'S8b.lane3_high_edge_iff_o_le_bound',
    'S8b.lane3_reject_iff_fips',
    'S8b.lane3_flag_shift_exposes_the_lane',
    'S8b.lane3_shift_exposes_the_stored_lane',
    'S8b.lane3_low_edge_shift_exposes_the_lane',
    'S8b.lane3_high_edge_shift_exposes_the_lane',
    'S8b.claims_discriminate',
    'S11.premises_sat',
    'S11.q0_nonneg',
    'S11.q0_le_44',
    'S11.r0_nonneg',
    'S11.r0_lt_2gamma2',
    'S11.claims_discriminate',
    'S11b.premises_sat',
    'S11b.only_at_q_minus_1',
    'S11b.claims_discriminate',
    'S13.premises_sat',
    'S13.no_earlier_failure',
    'S13.lane_local_below_the_cliff',
    'S13.claims_discriminate',
    'S14.premises_sat',
    'S14.l1_diff_no_borrow',
    'S14.l1_operand_no_evm_wrap',
    'S14.l1_diff_congruent',
    'S14.l1_sum_lane_le_2acc',
    'S14.l2_diff_no_borrow',
    'S14.l2_operand_no_evm_wrap',
    'S14.l2_diff_congruent',
    'S14.exit_diff_sum_lane_lt_2q',
    'S14.exit_lanes_meet_l3_premise',
    'S14.claims_discriminate',
    'E1.ctl_eq_rejects_0',
    'E1.ctl_eq_rejects_1',
    'E2.output_in_0_44',
    'E2.sweep_ran_to_completion',
    'E2.ctl_range_accepts_0',
    'E2.ctl_range_rejects_0',
    'E2.ctl_range_rejects_1',
    'E3.ctl_rejects_0',
    'E3.ctl_rejects_1',
    'E3.ctl_rejects_2',
    'E4.ctl_rejects_0',
    'E4.ctl_rejects_1',
    'E4.ctl_rejects_2',
    'E4.ctl_rejects_3',
    'E5.boundary_rejected',
    'E5.just_inside_accepted',
    'E6.ctl_accepts_0',
    'E6.ctl_accepts_1',
    'E6.ctl_rejects_0',
    'E6.ctl_rejects_1',
    'E6.ctl_rejects_2',
    'E6.ctl_rejects_3',
    'E6.ctl_rejects_4',
    'E3b.z_zero_field_canonicalises_to_zero',
    'E3b.every_output_canonical',
    'E3b.ctl_accepts_0',
    'E3b.ctl_rejects_0',
    'E3b.ctl_rejects_1',
    'E3b.ctl_rejects_2',
    'E3b.ctl_rejects_3',
    'E4b.ctl_rejects_0',
    'E4b.ctl_rejects_1',
    'E4b.ctl_rejects_2',
    'E4b.ctl_rejects_3',
    'E4b.ctl_rejects_4',
    'E4b.ctl_rejects_5',
    'E5b.low_tail_boundary_rejected',
    'E5b.low_tail_just_inside_accepted',
    'E5b.high_tail_boundary_rejected',
    'E5b.high_tail_just_inside_accepted',
    'E5b.probes_straddle_the_bound_in_fips',
    'E12.ctl_rejects_0',
    'E12.ctl_rejects_1',
    'E13.ctl_rejects_0',
    'E13.ctl_rejects_1',
    'E13.ctl_rejects_2',
    'E14.pure_domain_injective',
    'E14.both_domains_nonempty',
    'E14.pure_prehash_disjoint',
    'E14.ctl_rejects_0',
    'E14.ctl_rejects_1',
    'E14.ctl_rejects_2',
    'E9a.congruent',
    'E9a.lane_local',
    'E9a.qhat_lt_2p31',
    'E9a.r_lt_2q',
    'E9a.r_nonneg',
    'E9a.ctl_rejects_0',
    'E9a.ctl_rejects_1',
    'E9a.ctl_rejects_2',
    'E9a.ctl_rejects_3',
    'E9a.ctl_rejects_4',
    'E9a.ctl_rejects_5',
    'E9b.congruent',
    'E9b.lane_local',
    'E9b.qhat_lt_2p31',
    'E9b.r_lt_2q',
    'E9b.r_nonneg',
    'E9b.ctl_rejects_0',
    'E9b.ctl_rejects_1',
    'E9b.ctl_rejects_2',
    'E9b.ctl_rejects_3',
    'E9b.ctl_rejects_4',
    'E9b.ctl_rejects_5',
    'O1.ctl_rejects_0',
    'O1.ctl_rejects_1',
    'O1.ctl_rejects_2',
    'O1.ctl_rejects_3',
    'O2.div_product_fits_lane',
    'O2.quotient_product_fits_lane',
    'O2.comparator_addends_fit_lane',
    'O2.top_lane_fits_word',
    'O2.ctl_lane64_accepts_0',
    'O2.ctl_lane64_accepts_1',
    'O2.ctl_lane64_rejects_0',
    'O2.ctl_lane64_rejects_1',
    'O2.ctl_word256_accepts_0',
    'O2.ctl_word256_accepts_1',
    'O2.ctl_word256_rejects_0',
    'O2.ctl_word256_rejects_1',
    'O3.K95233_premises_sat',
    'O3.K95233_comparator_iff',
    'O3.K95233_ctl_wrong_bit_is_refutable',
    'O3.K1_premises_sat',
    'O3.K1_comparator_iff',
    'O3.K1_ctl_wrong_bit_is_refutable',
    'O4.premises_sat',
    'O4.magic_division_is_mod44',
    'O4.quotient_fits_the_rep1_mask',
    'O4.ctl_wrong_magic_is_refutable',
    'O4.ctl_wrong_shift_is_refutable',
    'O4.ctl_wrong_subtrahend_is_refutable',
    'O4.ctl_bound_premise_is_load_bearing',
    'O5.ctl_rejects_0',
    'O5.ctl_rejects_1',
    'O5.ctl_rejects_2',
    'O5.ctl_rejects_3',
    'O5.ctl_rejects_4',
    'O6.uniform_lanes',
    'O6.mixed_lanes',
    'O6.ctl_uniform_rejects_0',
    'O6.ctl_uniform_rejects_1',
    'O6.ctl_uniform_rejects_2',
    'O6.ctl_mixed_rejects_0',
    'O6.ctl_mixed_rejects_1',
    'O6.ctl_mixed_rejects_2',
    'O7.premises_sat',
    'O7.pk_coefficient_ceiling_is_q',
    'O7.lane0_no_spill',
    'O7.lane0_ctl_premise_is_load_bearing',
    'O7.lane0_ctl_lane_locality_needs_a_ceiling',
    'O7.lane1_no_spill',
    'O7.lane1_ctl_premise_is_load_bearing',
    'O7.lane1_ctl_lane_locality_needs_a_ceiling',
    'O7.lane2_no_spill',
    'O7.lane2_ctl_premise_is_load_bearing',
    'O7.lane2_ctl_lane_locality_needs_a_ceiling',
    'O7.lane3_no_spill',
    'O7.lane3_ctl_premise_is_load_bearing',
    'O7.lane3_ctl_lane_locality_needs_a_ceiling',
    'O7.top_lane_fits_word',
    'O7.ctl_word256_accepts_0',
    'O7.ctl_word256_accepts_1',
    'O7.ctl_word256_rejects_0',
    'O7.ctl_word256_rejects_1',
    'O8.offset_prevents_borrow',
    'O8.lane_bound',
    'O8.offset_preserves_residue',
    'O8.replicated_constant_exact',
    'O8.entry_offset_dominates_lane_max',
    'O8.ctl_lane53_accepts_0',
    'O8.ctl_lane53_accepts_1',
    'O8.ctl_lane53_rejects_0',
    'O8.ctl_lane53_rejects_1',
    'O8.ctl_residue_accepts_0',
    'O8.ctl_residue_accepts_1',
    'O8.ctl_residue_accepts_2',
    'O8.ctl_residue_accepts_3',
    'O8.ctl_residue_rejects_0',
    'O8.ctl_residue_rejects_1',
    'O8.ctl_residue_rejects_2',
    'O8.ctl_borrow_accepts_0',
    'O8.ctl_borrow_accepts_1',
    'O8.ctl_borrow_rejects_0',
    'O8.ctl_borrow_rejects_1',
    'O8.ctl_borrow_rejects_2',
    'O8.ctl_rep_accepts_0',
    'O8.ctl_rep_rejects_0',
    'O8.ctl_rep_rejects_1',
    'O8.ctl_rep_rejects_2',
    'O8.ctl_entry_accepts_0',
    'O8.ctl_entry_accepts_1',
    'O8.ctl_entry_rejects_0',
    'O8.ctl_entry_rejects_1',
    'O8.pk_coefficient_ceiling_is_q',
    'O8.ctl_amax_accepts_0',
    'O8.ctl_amax_accepts_1',
    'O8.ctl_amax_accepts_2',
    'O8.ctl_amax_rejects_0',
    'O8.ctl_amax_rejects_1',
    'O8.ctl_amax_rejects_2',
    'O9.all_fields_canonical',
    'O9.lane_roundtrip_exact',
    'O9.canonical_lane_fits_23_bits',
    'O9.ctl_canon_accepts_0',
    'O9.ctl_canon_accepts_1',
    'O9.ctl_canon_accepts_2',
    'O9.ctl_canon_rejects_0',
    'O9.ctl_canon_rejects_1',
    'O9.ctl_canon_rejects_2',
    'O9.ctl_canon_rejects_3',
    'O9.ctl_23bit_accepts_0',
    'O9.ctl_23bit_accepts_1',
    'O9.ctl_23bit_rejects_0',
    'O9.ctl_23bit_rejects_1',
    'O9.ctl_stride_accepts_0',
    'O9.ctl_stride_accepts_1',
    'O9.ctl_stride_accepts_2',
    'O9.ctl_stride_rejects_0',
    'O9.ctl_stride_rejects_1',
    'O9.ctl_stride_rejects_2',
    'O9.ctl_stride_rejects_3',
    'O10.terms_pairwise_disjoint',
    'O10.terms_inside_the_word',
    'O10.mask_is_four_18_bit_lanes',
    'O10.coordinate_sweep_exact',
    'O10.shipped_map_is_bytewise_additive',
    'O10.fips_map_is_bytewise_additive',
    'O10.fused_constants_are_the_two_powers',
    'O10.fused_multiply_is_the_two_terms',
    'O10.mul_pairs_are_the_doubled_terms',
    'O10.ctl_disjoint_accepts_0',
    'O10.ctl_disjoint_accepts_1',
    'O10.ctl_disjoint_rejects_0',
    'O10.ctl_disjoint_rejects_1',
    'O10.ctl_disjoint_rejects_2',
    'O10.ctl_disjoint_rejects_3',
    'O10.ctl_mask_accepts_0',
    'O10.ctl_mask_rejects_0',
    'O10.ctl_mask_rejects_1',
    'O10.ctl_mask_rejects_2',
    'O10.ctl_mask_rejects_3',
    'O10.ctl_mask_rejects_4',
    'O10.ctl_sweep_accepts_0',
    'O10.ctl_sweep_rejects_0',
    'O10.ctl_sweep_rejects_1',
    'O10.ctl_sweep_rejects_2',
    'O10.ctl_sweep_rejects_3',
    'O10.ctl_fused_mul_accepts_0',
    'O10.ctl_fused_mul_rejects_0',
    'O10.ctl_fused_mul_rejects_1',
    'O10.ctl_fused_mul_rejects_2',
    'O10.ctl_fused_const_accepts_0',
    'O10.ctl_fused_const_rejects_0',
    'O10.ctl_fused_const_rejects_1',
    'O10.ctl_fused_pairs_accepts_0',
    'O10.ctl_fused_pairs_rejects_0',
    'O10.ctl_fused_pairs_rejects_1',
    'O10.ctl_fused_pairs_rejects_2',
    'META-PINS.all_regions_pinned',
    'META-PINS.no_unpinned_regions',
    'META-PINS.every_region_digest_matches',
    'META-PINS.every_formal_file_pinned',
    'META-PINS.every_pinned_file_present',
    'META-PINS.every_formal_file_digest_matches',
    'META-PINS.no_bytecode_cache_under_formal',
    'META-PINS.executing_modules_are_the_pinned_bytes',
    'META-PINS.no_alternate_source_encoding',
    'META-PINS.blanked_regions_are_inert_data',
    'META-IDS.no_duplicate_obligations',
    'META-IDS.no_duplicate_conjuncts',
    'META-IDS.obligations_exact',
    'META-IDS.conjuncts_exact',
    'META-IDS.obligation_count',
    'META-IDS.conjunct_count',
]

results = []          # one row per OBLIGATION
conjuncts = []        # one row per CONJUNCT of an obligation

def _truth(x):
    """The canonical truth value of a claim.  NOT `bool`.

    A `record` that PRINTS `pok` but TALLIES `bool(pok)` is defeatable:
    `bool` is an ordinary global NAME, so
        def record(..., parts=None, bool=lambda _x: True)
    makes every conjunct tally True while the same row prints `[FAIL]` --
    a green conjunct tally with a visible failure on screen.  `_truth` is a
    module-level function whose `def` line and body are both pinned regions,
    and `record` prints THE VALUE IT STORED rather than a second evaluation of
    the same expression, so the printed and tallied verdicts cannot differ.
    """
    return True if x else False


def record(oid, kind, desc, ok, detail="", parts=None):
    """Record one obligation, and each of its CONJUNCTS separately.

    CONJUNCT AUDIT.  Most obligations are conjunctions of several
    independent claims.  A vacuity audit that aggregates per obligation ID
    lets a conjunct no mutation targets be DELETED outright while both
    `verify_all.py` and `vacuity_audit.py` stay green -- eight such deletions
    across E14/O7/O2/O8 are enough to slip past both tools.

    `parts` is an ordered list of `(conjunct_name, bool)`.  Every conjunct gets
    its own `[PASS]/[FAIL] <oid>.<name>` line, so
      * `vacuity_audit.py` can aggregate killers PER CONJUNCT, and
      * deleting a conjunct removes an ID from the emitted set, which
        `EXPECTED_OBLIGATIONS`/`EXPECTED_CONJUNCTS` below turn into a FAILURE
        rather than a smaller number.
    An obligation with no `parts` is its own single conjunct.
    """
    parts = list(parts or ())
    results.append((oid, kind, desc,
                    _truth(ok) and all(_truth(p[1]) for p in parts), detail))
    print(f"[{'PASS' if results[-1][3] else 'FAIL'}] {oid:<7} {kind:<6} {desc}"
          + (f"  — {detail}" if detail else ""))
    for name, pok in parts:
        conjuncts.append((f"{oid}.{name}", _truth(pok)))
        print(f"[{'PASS' if conjuncts[-1][1] else 'FAIL'}] {conjuncts[-1][0]}")
    return results[-1][3]

# ---------------------------------------------------------------------------
# SEMANTIC PINNING
# ---------------------------------------------------------------------------
# Asserting WHICH obligations and conjuncts exist is not the same as asserting
# they still MEAN anything: rewriting a CALC predicate to a tautology of the
# shape `X <= X`, leaving every ID, description and evidence string alone,
# produces a byte-identical green report (exit 0) while proving nothing.  The
# pinned ID sets cannot see that edit, so something else has to, and the
# mechanism below is what does.
#
# The answer is DISCRIMINATION CONTROLS.  An obligation of the shape "the
# quantity X satisfies the predicate p" is recorded as the predicate `p` (a
# unary callable) applied to the subject `X`, TOGETHER WITH control points that
# straddle p's true boundary:
#
#     accept = values p MUST return True  on   (positive controls)
#     reject = values p MUST return False on   (negative controls)
#
# The control points are written as their own literal expressions, so a textual
# edit to the predicate does not move them.  A predicate rewritten to a
# tautology accepts its negative controls and FAILS; a predicate whose threshold
# drifts stops discriminating at the boundary and FAILS; a flipped comparison
# operator fails one side or the other.
#
# WHAT THIS CANNOT DETECT — stated precisely, because a perfect version is
# impossible (an obligation is code, and code can be rewritten):
#   (a) SUBJECT SUBSTITUTION.  The controls pin `p`, not the argument.  Feeding
#       `p` a different, trivially-satisfying subject (`pred(0)` instead of
#       `pred(MU52)`) leaves both claim and controls green.  This is what the
#       source-digest tripwire (META-PINS, formal/z3/source_pins.py) is for: it
#       makes any edit to the obligation's own expression loud.
#   (b) A COORDINATED REWRITE of the predicate AND its control points in the
#       same edit.  Nothing in-band can stop that either; META-PINS makes it
#       visible, and the vacuity audit's tautology mutations (VT01/VT02) prove
#       the controls bite when only the predicate moves.
#   (c) An obligation whose SUBJECT is itself computed wrongly upstream — the
#       controls say the predicate discriminates, not that the model is right.
#       That is what the vacuity audit's kernel mutations are for.
def controls(pred, accept=(), reject=(), label="ctl"):
    """Positive/negative controls for a claim stated as a unary predicate.

    `label` keeps conjunct IDs distinct when one obligation pins two predicates.
    """
    rows = []
    for i, x in enumerate(accept):
        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))
    for i, x in enumerate(reject):
        rows.append((f"{label}_rejects_{i}", not _truth(pred(x))))
    return rows


def pinned(oid, kind, desc, pred, subject, detail="", accept=(), reject=(), parts=()):
    """record() for an obligation whose claim is `pred(subject)`.

    Emits the claim plus one conjunct per control point.  See the block comment
    above for what this pins and what it provably cannot.
    """
    return record(oid, kind, desc, _truth(pred(subject)), detail,
                  parts=list(parts) + controls(pred, accept, reject))


try:
    from z3 import Int, If, Solver, And, Or, Not, Implies, unsat, sat, ForAll
    HAVE_Z3 = True
except Exception as e:                                              # pragma: no cover
    HAVE_Z3 = False
    print(f"!! z3 unavailable ({e}); SMT obligations will FAIL", file=sys.stderr)


# ---------------------------------------------------------------- primality
def _mr_witness(n, a):
    """Miller-Rabin: True if `a` witnesses that n is composite."""
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    x = pow(a, d, n)
    if x in (1, n - 1):
        return False
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1:
            return False
    return True


def _jacobi(a, n):
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


def _strong_lucas_prp(n):
    """Strong Lucas probable-prime test, Selfridge (method A) parameters."""
    if n % 2 == 0:
        return n == 2
    # a perfect square is never a Lucas PRP and would loop forever below
    r = int(n ** 0.5)
    for c in (r - 2, r - 1, r, r + 1, r + 2):
        if c >= 0 and c * c == n:
            return False
    D = 5
    while True:
        j = _jacobi(D, n)
        if j == -1:
            break
        if j == 0 and abs(D) != n:
            return False
        D = -(D + 2) if D > 0 else -(D - 2)
    Q = (1 - D) // 4
    d, s = n + 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    U, V, Qk = 0, 2, 1
    for bit in bin(d)[2:]:
        U, V = U * V % n, (V * V - 2 * Qk) % n
        Qk = Qk * Qk % n
        if bit == "1":
            U, V = (U + V), (D * U + V)
            U = (U * (n + 1) // 2 if U % 2 == 0 else (U + n) * (n + 1) // 2) % n \
                if False else (U * pow(2, n - 2, n)) % n
            V = (V * pow(2, n - 2, n)) % n
            Qk = Qk * Q % n
    if U == 0 or V == 0:
        return True
    for _ in range(s - 1):
        V = (V * V - 2 * Qk) % n
        if V == 0:
            return True
        Qk = Qk * Qk % n
    return False


def _is_prime_bpsw(n, mr_rounds=64):
    """BPSW (MR base 2 + strong Lucas) plus `mr_rounds` deterministic extra bases.

    Self-contained -- no sympy, no network.  BPSW has no known counterexample
    and none below 2^64; the extra Miller-Rabin rounds give an unconditional
    error bound of 4^-64 for the composite direction.
    """
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    if _mr_witness(n, 2):
        return False
    if not _strong_lucas_prp(n):
        return False
    import random as _r
    rng = _r.Random(0xB5D)  # fixed seed: the suite must be deterministic
    for _ in range(mr_rounds):
        if _mr_witness(n, rng.randrange(2, n - 1)):
            return False
    return True


# ---------------------------------------------------------------- reference impls
def ref_reduce_mod_pm(x, n):
    x = x % n
    return x - n if x > (n >> 1) else x

def ref_decompose(r):
    """FIPS 204 Decompose (alpha = 2*GAMMA2), mirroring pythonref utils.decompose."""
    rp = r % Q
    r0 = ref_reduce_mod_pm(rp, 2 * GAMMA2)
    if rp - r0 == Q - 1:
        return 0, r0 - 1
    return (rp - r0) // (2 * GAMMA2), r0

def ref_use_hint(h, r):
    m = (Q - 1) // (2 * GAMMA2)          # 44
    r1, r0 = ref_decompose(r)
    if h == 1:
        return (r1 + 1) % m if r0 > 0 else (r1 - 1) % m
    return r1

def ref_z_centered(v):
    """FIPS 204 BitUnpack for z (18-bit field) -> canonical [0,Q)."""
    return (GAMMA1 - v) % Q

def ref_z_norm_ok(v):
    """FIPS 204 acceptance: ||z||_inf < GAMMA1 - BETA, computed on the signed value."""
    signed = GAMMA1 - v                  # in (-2^17, 2^17]
    return abs(signed) < GAMMA1 - BETA


# ---------------------------------------------------------------- kernel models
def kern_barrett(e, mu=MU33, shift=SH1, shift2=SH2):
    """The two-step lane-local Barrett as implemented in Yul (ZZZ_NttVariants/
    ZZZ_InvNtt, and the shipped src/Ntt.sol / src/InvNtt.sol they mirror):

        x1 := sub(x,  mul(and(shr(33, mul(x,  MU33)), QHATM31), Q))
        r  := sub(x1, mul(and(shr(23, x1),            QHATM31), Q))

    Returned unmasked, i.e. as the SCALAR kernel `lazyBarrett` computes it; the
    31-bit-per-lane mask is what makes the PACKED form agree with four copies of
    this, and that is obligation S7 (and Lean `swar_lane_independent`).
    `qhat` is step 1's quotient — the one the mask has to hold."""
    qhat = (e * mu) >> shift
    x1 = e - Q * qhat
    return x1 - Q * (x1 >> shift2 if x1 >= 0 else 0), qhat

def kern_z_centered_strict(v):
    """unpackZStrict model: zc = mod(Q + GAMMA1 - v, Q) with v < 2^18."""
    return (Q + GAMMA1 - v) % Q

def kern_z_norm_flag(v):
    """Branchless strict-FIPS norm test on the raw 18-bit field (single range test).

    Models the EVM exactly: `sub` wraps mod 2^256 and `lt` is UNSIGNED, so for
    v < 79 the subtraction underflows to a huge value and the comparison fails,
    which is precisely how one comparison covers both tails.  (Modelling this with
    Python's unbounded ints instead was a harness bug that this suite caught.)
    """
    lhs = (v - (BETA + 1)) % (1 << 256)          # EVM sub
    return not (lhs < 2 * GAMMA1 - 2 * BETA - 1)  # EVM lt (unsigned)

# --- the SHIPPED packed decoder (src/Decode.sol _unpackZPoly), one lane ------
# The shipped kernel does the centered map, the canonicalisation and the strict
# norm check FOUR LANES AT A TIME.  S8b states the four-lane word arithmetic
# symbolically at EVM semantics; the two models below are its ONE-LANE
# projection, which is what the exhaustive sweeps E3b/E4b/E5b quantify over.
Z_UOFF_LANE = Q + GAMMA1                       # 8511489
Z_QB32_LANE = (1 << 32) - Q                    # 4286586879
Z_NLO_LANE = (1 << 32) - (GAMMA1 - BETA)       # 2^32 - 130994
Z_NHI_LANE = (1 << 32) + Q - (GAMMA1 - BETA)   # 2^32 + 8249423

def kern_z_canon_swar(v):
    """Canonicalisation as the shipped Yul does it, projected on one lane:

        u := sub(Z_UOFF, V)                              q + gamma1 - v
        o := sub(u, mul(shr(32, and(add(u, Z_QB32), Z_BIT32)), Q))

    `u + (2^32 - q)` is below 2^33 for every 18-bit field, so its bit 32 IS the
    predicate [u >= q] and the whole expression is ONE conditional subtraction.
    The `>=` (not `>`) is what canonicalises the z = 0 field (v = GAMMA1, where
    u == q exactly) to 0 rather than to q -- the SOTA hazard of EXPLAINER 10.
    """
    u = Z_UOFF_LANE - v
    return u - Q * (((u + Z_QB32_LANE) >> 32) & 1)

def kern_z_norm_flag_packed(v, nlo=Z_NLO_LANE, nhi=Z_NHI_LANE):
    """The STRICT norm check as the shipped Yul does it, projected on one lane:

        bad := and(add(o, Z_NLO), sub(Z_NHI, o))        bit 32 = reject

    Both lane values stay in [0, 2^33), so bit 32 of the first is [o >= 130994]
    and bit 32 of the second is [o <= 8249423]; their AND is "the stored
    coefficient is at distance >= gamma1 - beta from 0 modulo q", i.e. exactly
    the FIPS 204 rejection ||z||inf >= gamma1 - beta, boundary INCLUDED.
    `nlo`/`nhi` are parameters so that the discrimination controls can move the
    two window edges independently, in both directions.
    """
    o = kern_z_canon_swar(v)
    lo = ((o + nlo) >> 32) & 1
    hi = ((nhi - o) >> 32) & 1
    return bool(lo & hi)

def kern_use_hint(h, rv):
    """useHintFast2 branchless model."""
    q0 = rv // (2 * GAMMA2)
    r0 = rv - q0 * (2 * GAMMA2)
    c = 1 if r0 > GAMMA2 else 0
    s1 = q0 + c
    r1 = s1 * (0 if s1 == 44 else 1)
    return (r1 + h * (1 + 42 * (1 if (r0 == 0 or c) else 0))) % 44

# ================================================================ CALC obligations
def calc_obligations():
    import math
    ok = True
    # C1: the coarse Barrett constant of step 1
    ok &= pinned("C1", "CALC", "MU33 == floor(2^33/Q)",
                 lambda mu: mu == (1 << 33) // Q, MU33, str(MU33),
                 accept=[1025], reject=[1026, 1024, 0x200801C0, 0])
    # C1b: step 2 is the SAME Barrett step with mu = floor(2^23/Q), which is 1
    # only because Q = 2^23 - 2^13 + 1 -- i.e. the elided multiply is a fact
    # about this modulus, not a coincidence, and 2^23 - Q = 2^13 - 1 = 8191 is
    # the factor by which step 2 shrinks its input's high part.
    ok &= pinned("C1b", "CALC", "MU23 == floor(2^23/Q) == 1 (step 2's multiply is elided)",
                 lambda mu: mu == (1 << 23) // Q and mu == 1, MU23, str(MU23),
                 accept=[1], reject=[0, 2, 1025],
                 parts=[("q_is_2p23_minus_2p13_plus_1", Q == (1 << 23) - (1 << 13) + 1),
                        ("two_p23_minus_q_is_8191", (1 << 23) - Q == (1 << 13) - 1)])

    # C9: NTT forward lane ceiling and product ceiling
    ok &= pinned("C9a", "CALC", "forward: 17Q < 2^28 (final lane bound)",
                 lambda x: x < (1 << 28), 17 * Q, "",
                 accept=[0, (1 << 28) - 1], reject=[1 << 28, 1 << 29])
    ok &= pinned("C9b", "CALC", "forward: 15Q(Q-1) < 2^50 (max Barrett input)",
                 lambda x: x < (1 << 50), 15 * Q * (Q - 1), "",
                 accept=[0, (1 << 50) - 1], reject=[1 << 50, 1 << 51])
    ok &= pinned("C9c", "CALC", "inverse: 256Q < 2^31 (max sum lane)",
                 lambda x: x < (1 << 31), 256 * Q, "",
                 accept=[0, (1 << 31) - 1], reject=[1 << 31, 1 << 32])
    ok &= pinned("C9d", "CALC", "inverse: 128Q(Q-1) < 2^53 (max Barrett input)",
                 lambda x: x < (1 << 53), 128 * Q * (Q - 1), "",
                 accept=[0, (1 << 53) - 1], reject=[1 << 53, 1 << 54])
    # LANE-LOCALITY.  This is the fact the whole no-spreading design rests on:
    # step 1's product fits a 64-bit SWAR lane, so a packed word's four lanes
    # multiply INDEPENDENTLY and nothing has to be spread to 128-bit spacing.
    # The old spread form needed only 2^128 here and paid two masks, a shift and
    # a repack for it.
    ok &= pinned("C9e", "CALC", "packed lanes: max_e * MU33 < 2^64 (no cross-lane carry)",
                 lambda x: x < (1 << 64), (128 * Q * (Q - 1)) * MU33,
                 f"2^{math.log2((128*Q*(Q-1))*MU33):.1f} < 2^64",
                 accept=[0, (1 << 64) - 1], reject=[1 << 64, 1 << 65])
    # ... and the 31-bit mask is exactly the right width for it: qhat < 2^31
    # holds EXACTLY when the lane product is < 2^64, and after `shr(33, .)` the
    # NEXT lane's bits begin at bit 31 -- so one mask both extracts the quotient
    # and blocks the neighbour.  A 32-bit mask would let one neighbour bit in.
    ok &= pinned("C9h", "CALC", "QHATM31: qhat < 2^31 over the domain, and 64-33 == 31",
                 lambda w: w == 31, 64 - SH1, "mask width 31 == 64 - 33",
                 accept=[31], reject=[30, 32, 52],
                 parts=[("max_qhat_lt_2p31", ((128 * Q * (Q - 1)) * MU33) >> SH1 < (1 << 31)),
                        ("mask_width_is_64_minus_shift", 64 - SH1 == 31),
                        ("qhat_bound_iff_lane_local",
                         (((1 << 64) - 1) >> SH1) == (1 << 31) - 1),
                        # step 2 reuses the same mask: its quotient is < 2^31 and
                        # after shr(23,.) the neighbour's bits start at bit 41
                        ("step2_quotient_fits_mask",
                         (Q - 1 + ((128 * Q * (Q - 1)) * ((1 << SH1) - MU33 * Q) >> SH1)) >> SH2
                         < (1 << 31)),
                         ("step2_neighbour_above_mask", 64 - SH2 == 41 and 41 >= 31)])

    # C11: reduction SAFETY MARGIN (symbolic-execution finding). The smallest input for
    # which the two-step reduction violates r < 2q is exactly BARRETT_FIRST_FAIL
    # (there r == 2q on the nose). The inverse NTT's worst product sits only 1.144x below
    # it -- so ONE additional unreduced layer (which doubles lane growth) would BREAK the
    # reduction. This is the regression guard for that: if anyone raises the lane bound,
    # C11c fails loudly instead of silently producing wrong field arithmetic.
    # NOTE the margin is THINNER than the spread form's 1.335x: step 1's quotient
    # is coarse by construction (mu = 1025, defect d33 = 2^33 - MU33*q = 7167),
    # so step 2 has 10 bits of shrinkage to spend and the whole reduction fails
    # once step 1's output can reach 2^33 - d33.  The 2x doubling guard still
    # bites (C11c), and the LANE-locality cliff -- the first x whose product
    # leaves its 64-bit lane, 17,996,823,486,545,905 -- sits ABOVE this one, so
    # this is the binding constraint of the two.
    BARRETT_FIRST_FAIL = 10285325456994078
    LANE_FIRST_OVERFLOW = -(-(1 << 64) // MU33)
    r_at, _ = kern_barrett(BARRETT_FIRST_FAIL)
    r_below, _ = kern_barrett(BARRETT_FIRST_FAIL - 1)
    # The predicate here is "this input is inside the safe Barrett
    # domain".  Its controls are the cliff itself and a spread of points below it,
    # so a `kern_barrett` or a comparison rewritten to always-safe fails.
    ok &= pinned("C11a", "CALC", "first reduction failure is exactly at the known input (r == 2q)",
                 lambda x: kern_barrett(x)[0] < 2 * Q, BARRETT_FIRST_FAIL - 1,
                 f"x = {BARRETT_FIRST_FAIL}",
                 accept=[0, 1, 8380417, 16760834, 10285325456994077],
                 reject=[10285325456994078],
                 parts=[("fails_at", r_at == 2 * Q), ("ok_below", r_below < 2 * Q)])
    inv_worst = 128 * Q * (Q - 1)
    ok &= pinned("C11b", "CALC", "inverse-NTT worst product is inside the safe domain",
                 lambda x: x < 10285325456994078, inv_worst,
                 f"margin = {BARRETT_FIRST_FAIL / inv_worst:.4f}x",
                 accept=[0, 10285325456994077],
                 reject=[10285325456994078, 10285325456994079])
    ok &= pinned("C11c", "CALC", "GUARD: doubling lane growth (one extra unreduced layer) WOULD break it",
                 lambda x: x >= 10285325456994078, 2 * inv_worst,
                 "do not add unreduced layers without re-deriving MU/shift",
                 accept=[10285325456994078, 10285325456994079],
                 reject=[0, 10285325456994077])
    # C11d: the OTHER cliff -- the first input whose step-1 product leaves its
    # 64-bit lane, which is what the no-spreading design would lose first.  It
    # is checked, and reported, so that "the binding constraint is r < 2q" is a
    # derived fact rather than a claim: LANE_FIRST_OVERFLOW > BARRETT_FIRST_FAIL.
    ok &= pinned("C11d", "CALC", "the lane-locality cliff sits ABOVE the r<2q cliff",
                 lambda x: x > BARRETT_FIRST_FAIL, LANE_FIRST_OVERFLOW,
                 f"lane overflow at {LANE_FIRST_OVERFLOW} = ceil(2^64/MU33)",
                 accept=[BARRETT_FIRST_FAIL + 1, 1 << 62],
                 reject=[BARRETT_FIRST_FAIL, BARRETT_FIRST_FAIL - 1, 0],
                 parts=[("overflows_at", LANE_FIRST_OVERFLOW * MU33 >= (1 << 64)),
                        ("fits_below", (LANE_FIRST_OVERFLOW - 1) * MU33 < (1 << 64)),
                        ("inv_worst_is_lane_local", inv_worst * MU33 < (1 << 64))])

    # ---------------------------------------------------------------- C9f / C9g
    # S5/S6 prove ONE layer's step.  Without something to compose those steps
    # into a statement about the whole 8-layer transform, the per-layer bound
    # and the whole-transform constants (C9a-C9d) are related only by prose --
    # which is how an S5 proving `+4Q` coexists with consumers assuming `+2Q`.
    # These two obligations run the induction explicitly, mirroring the layer
    # structure of the emitted Yul, and pin the maxima the rest of the suite uses.
    #
    # forward (ZZZ_NttVariants.sol :: nttFwV3): every layer stores u+V and u+2q-V
    # with V < 2q (layers 1..7: V = Barrett(W[pv]*S); the fused layer 8: V =
    # mulmod(., ., q) < q < 2q — C16 pins which is which), so
    # LB_{L+1} = LB_L + 2q, LB_1 = q.  The final lanes are NOT canonicalised:
    # the transform exits < 17q (C9a), exactly the domain O7/O8's matvec admits.
    #
    # The induction is a PREDICATE OVER THE SCHEDULE
    # (entry lane bound, per-layer increment, layer count) rather than a straight
    # line of `all(...)` calls, and the obligation carries NEGATIVE CONTROLS: a
    # +4q schedule, a non-canonical entry, a ninth
    # layer and a seventh must each be REJECTED by the same predicate.  Without
    # them, rewriting any of the six conjuncts to `True` is a silent green PASS
    # -- and the schedule itself is the residual `[ASSUMED]` row in
    # formal/hypotheses.py, so the predicate that consumes it has to discriminate.
    def fwd_schedule(lb0, inc, layers):
        lb, bin_ = [lb0], []
        for _L in range(layers):
            bin_.append(lb[-1] * (Q - 1))          # multiplied operand < LB_L
            lb.append(lb[-1] + inc)
        return lb, bin_

    def fwd_induction_closes(sched):
        lb0, inc, layers = sched
        lb, bin_ = fwd_schedule(lb0, inc, layers)
        return (all(b <= 15 * Q for b in lb[:layers])
                and max(bin_) == 15 * Q * (Q - 1)
                and max(bin_) < BARRETT_FIRST_FAIL
                and lb[layers] == 17 * Q
                and lb[layers] < (1 << 28))

    fwd_lb, fwd_barrett_in = fwd_schedule(Q, 2 * Q, 8)
    ok &= pinned("C9f", "CALC",
                 "forward NTT: the 8-layer +2q induction closes (S5 step -> C9a/C9b constants)",
                 fwd_induction_closes, (Q, 2 * Q, 8),
                 f"lane bounds {[b // Q for b in fwd_lb]}q; max Barrett input "
                 f"{max(fwd_barrett_in) // (Q * (Q - 1))}q(q-1)",
                 reject=[(Q, 4 * Q, 8),            # a +4q schedule: LB leaves 15q at L5
                         (3 * Q, 2 * Q, 8),        # entered with non-canonical lanes
                         (Q, 2 * Q, 9),            # a NINTH layer: 17q(q-1) input, 19q lane
                         (Q, 2 * Q, 7),            # a SEVENTH: 13q(q-1) input, 15q lane
                         (Q, Q, 8)],               # +1q: max input 8q(q-1)
                 parts=[
                     ("premise_LB_le_15q_every_layer", all(b <= 15 * Q for b in fwd_lb[:8])),
                     ("max_barrett_input_is_15q_qm1", max(fwd_barrett_in) == 15 * Q * (Q - 1)),
                     ("barrett_input_inside_S1_domain", max(fwd_barrett_in) <= 15 * Q * (Q - 1)),
                     ("barrett_input_below_first_fail", max(fwd_barrett_in) < BARRETT_FIRST_FAIL),
                     ("final_lane_is_17q", fwd_lb[8] == 17 * Q),
                     ("final_lane_lt_2p28", fwd_lb[8] < (1 << 28)),
                 ])
    # inverse (ZZZ_InvNtt.sol :: nttInvV3): the verifier feeds the RAW matvec
    # accumulator straight into the fused L1+L2 block — lanes <= ACC_ENTRY =
    # 4(q-1)(17q-1) + q*2^28, which is EXACTLY O8's lane ceiling (the z/c
    # lanes are the LAZY forward NTT's, < 17q).  That block reduces with the
    # EVM's native mulmod/addmod against multiple-of-q offsets
    # ACCQ30 = q*2^30 >= ACC_ENTRY and ACCQ31 = q*2^31 >= 2*ACC_ENTRY
    # (the per-step proof is S14) and exits every lane < 2q — inside the < 4q
    # entry bound the L3..L8 over-approximation below assumes.  From there,
    # entering layer L every lane is < K_L*q with K_L = 2^(L-1); the
    # multiplied operand is (u + K_L q - v) < 2 K_L q, and the sum lane
    # doubles.  Layers 3..7 Barrett-reduce; layer 8 uses `mod` (S6b).
    # The accumulator ceiling is a FUNCTION of the pk-coefficient ceiling
    # `PK_AMAX` (module scope, with the argument for why that premise is not
    # free); the control at the end of this obligation is what makes it
    # falsifiable rather than assumed.
    ACC_ENTRY = acc_entry(PK_AMAX)                  # == O8's lane_max
    inv_exit_bound = 2 * Q                          # every L1+L2 exit lane (S14)

    def inv_barrett_inputs(n_barrett_layers):
        return [2 * (1 << (L - 1)) * Q * (Q - 1) for L in range(3, n_barrett_layers + 1)]

    def inv_induction_closes(sched):
        entry, exitb, n_barrett, sum_lane, l8_op = sched
        bin_ = inv_barrett_inputs(n_barrett)
        return (entry == acc_entry(PK_AMAX)
                and entry <= (Q << 30)              # the L1 offset dominates a lane
                and 2 * entry <= (Q << 31)          # the L2 offset dominates a sum lane
                and exitb <= 4 * Q                  # the block exit meets L3's premise
                and max(bin_) == 128 * Q * (Q - 1)
                and max(bin_) <= 128 * Q * (Q - 1)
                and max(bin_) < BARRETT_FIRST_FAIL
                and sum_lane == 256 * Q
                and sum_lane < (1 << 31)
                and l8_op * (Q - 1) < (1 << 64))

    inv_barrett_in = inv_barrett_inputs(7)
    inv_sum_lane = 256 * Q                          # after the L8 sums, before mod
    l8_operand = 2 * 128 * Q                        # sAB + 128q - sCD < 256q
    ok &= pinned("C9g", "CALC",
                 "inverse NTT: raw-accumulator entry fold (S14), layers 3-7 Barrett, "
                 "layer 8 mod (S6/S6b steps -> C9c/C9d constants)",
                 inv_induction_closes, (ACC_ENTRY, inv_exit_bound, 7, 256 * Q, 2 * 128 * Q),
                 f"entry {ACC_ENTRY} <= q*2^30; max Barrett input "
                 f"{max(inv_barrett_in) // (Q * (Q - 1))}q(q-1) at L7; "
                 f"max sum lane {inv_sum_lane // Q}q",
                 reject=[((Q << 30) + 1, inv_exit_bound, 7, 256 * Q, 2 * 128 * Q),  # entry past the L1 offset
                         (ACC_ENTRY, 8 * Q, 7, 256 * Q, 2 * 128 * Q),      # block exit busts L3's premise
                         (ACC_ENTRY, inv_exit_bound, 8, 256 * Q, 2 * 128 * Q),      # L8 Barrett-reduced too
                         (ACC_ENTRY, inv_exit_bound, 6, 256 * Q, 2 * 128 * Q),      # only six Barrett layers
                         (ACC_ENTRY, inv_exit_bound, 7, 512 * Q, 2 * 128 * Q),      # the sum lane doubles again
                         (ACC_ENTRY, inv_exit_bound, 7, 256 * Q, 2 * 128 * Q * (1 << 12))],  # L8 operand overflows
                 parts=[
                     ("entry_is_O8_lane_max", ACC_ENTRY == acc_entry(PK_AMAX)),
                     # the premise the two dominations rest on, stated rather
                     # than carried inside the `Q - 1` above
                     ("pk_coefficient_ceiling_is_q", PK_AMAX == Q),
                     ("l1_offset_dominates_entry", ACC_ENTRY <= (Q << 30)),
                     ("l2_offset_dominates_sum_lane", 2 * ACC_ENTRY <= (Q << 31)),
                     ("l1l2_exit_meets_l3_premise", inv_exit_bound <= 4 * Q),
                     ("max_barrett_input_is_128q_qm1", max(inv_barrett_in) == 128 * Q * (Q - 1)),
                     ("barrett_input_inside_S2_domain", max(inv_barrett_in) <= 128 * Q * (Q - 1)),
                     ("barrett_input_below_first_fail", max(inv_barrett_in) < BARRETT_FIRST_FAIL),
                     ("max_sum_lane_is_256q", inv_sum_lane == 256 * Q),
                     ("max_sum_lane_lt_2p31", inv_sum_lane < (1 << 31)),
                     ("layer8_lane_product_lt_2p64", l8_operand * (Q - 1) < (1 << 64)),
                 ]
                 # THE DISCRIMINATION CONTROL for the canonicality premise: the
                 # entry-fold domination must ACCEPT amax = q and REJECT amax =
                 # 2q (and anything larger).  Without this the `Q - 1` above is
                 # an assumption nothing can falsify; with it, a reviewer who
                 # doubts "canonical coefficients" can see the exact ceiling at
                 # which the fold stops being proved.
                 + controls(entry_offset_dominates,
                            label="ctl_pk_canonical_premise",
                            accept=[Q, Q - 1, 1],
                            reject=[2 * Q, 4 * Q, 1 << 32]))

    # ---------------------------------------------------------------------- C16
    # SOURCE LINKAGE.  C9f/C9g and S5/S6/S6b are statements about a layer
    # structure with per-layer offsets K*q.  This obligation reads the SHIPPED Yul
    # and checks that the constants and the butterfly shape are the ones the
    # induction assumes.  If the transform is re-tuned, this FAILS instead of the
    # proof silently describing a different program.
    #
    # FOUR WAYS A CHECK LIKE THIS GOES HOLLOW, and what closes each here:
    #  (i)   slicing the layer-8 region on a COMMENT --
    #            l78 = inv_body[inv_body.index("Layers 7+8 fused"):]
    #        lets anyone move that comment to the top of nttInvV3 and turn
    #        `inv_layer8_no_extra_mod_elsewhere` into `n == n`;
    #  (ii)  counting `mod(` as a RAW SUBSTRING of text that still contains
    #        comments and string literals counts a `mod(` inside either;
    #  (iii) a flat dict comprehension over the whole file lets the LAST
    #        declaration of a name win, so a shadowing redeclaration is
    #        invisible;
    #  (iv)  reading only the test-tree copy says nothing about the SHIPPED
    #        src/{Ntt,InvNtt}.sol.
    # So: the text is comment- and string-stripped before any counting; regions
    # are delimited by the `mstore(add(PR, 0x..), gas())` PROFILING MARKERS, which
    # are code and cannot be moved by editing a comment; a duplicate file-scope
    # constant is an error; and all three shipped copies of each transform are
    # read and required to agree byte-for-byte on the extracted shape.
    #
    # It also EXTRACTS the per-layer offset schedule from the source instead of
    # assuming it -- see the `[ASSUMED]` NTT-schedule row in formal/hypotheses.py.
    def _sol(rel):
        # RAW FILE DESCRIPTORS.  C16 is the whole link between the
        # proofs and the SHIPPED artefact, and an inert-data payload can install
        # a `builtins.open` shim that serves a pristine `Ntt.sol` to exactly this
        # call while the file on disk has lost a lane group's `+2q`.
        return raw_bytes(os.path.join(REPO_ROOT, rel)).decode("utf-8")

    def _strip_sol(text):
        """Drop `//` and `/* */` comments from Solidity/Yul, and replace every
        string literal by a DIGEST of its contents.

        Counting a token in raw source counts it in comments and strings too;
        that is defect (ii) above.  Replacing each literal by `""` instead would
        exempt the CONTENT of every string in the six shipped
        sources from `_C16_FILE_DIGEST` — the same class as an inert-data table, a
        region that is (in Yul, where a string literal is a 32-byte VALUE)
        semantically live and covered by no digest.  Substituting a hex digest
        keeps the counting property — a hex digest matches none of `mstore(`,
        `mload(`, `mul(`, `mod(`, `shr(52, mul(` or any `_K_OF` name — while
        making the content itself move `_fdigest`.  Measured: the only string
        literals in all six sources are the 22 + 8
        `assembly ("memory-safe")` annotations, so no live path exists; the
        exemption is closed rather than argued about.
        """
        out, i, n = [], 0, len(text)
        while i < n:
            if text.startswith("//", i):
                j = text.find("\n", i)
                i = n if j < 0 else j
                continue
            if text.startswith("/*", i):
                j = text.find("*/", i + 2)
                i = n if j < 0 else j + 2
                out.append(" ")
                continue
            c = text[i]
            if c in "\"'":
                q, i, lit = c, i + 1, []
                while i < n:
                    if text[i] == "\\":
                        lit.append(text[i:i + 2])
                        i += 2
                        continue
                    if text[i] == q:
                        i += 1
                        break
                    lit.append(text[i])
                    i += 1
                out.append(' "%s" ' % hashlib.sha256("".join(lit).encode("utf-8"))
                           .hexdigest()[:16])
                continue
            out.append(c)
            i += 1
        return "".join(out)

    _CONST_RE = re.compile(r"^\s*uint256 constant (\w+) = (0x[0-9a-fA-F]+|\d+);", re.M)
    # Every constant DECLARATION, of every type and at every scope -- the set
    # `_CONST_RE` cannot see.  `immutable` is
    # deliberately NOT matched: it is a constructor-time variable, not a
    # compile-time constant, and C18 extracts values.
    _DECL_CONST_RE = re.compile(
        r"^\s*[A-Za-z_][A-Za-z0-9_]*\s+(?:(?:public|private|internal)\s+)?constant\s+(\w+)\s*=",
        re.M)
    _MARK_RE = re.compile(
        r"mstore\(\s*(?:PR|add\(\s*PR\s*,\s*0x[0-9a-fA-F]+\s*\))\s*,\s*gas\(\)\s*\)")
    # The two-step lane-local Barrett, counted ONE STEP AT A TIME.  Counting only
    # the first step would leave the second unmodelled, and the second is not
    # decoration: step 1 alone lands at < 2^33, three orders of magnitude above
    # the 2q every lane bound in C9f/C9g/S5/S6 assumes.  So both are extracted
    # and `*_every_reduction_has_both_steps` requires them to agree region by
    # region -- a deleted `shr(23, ...)` line is then a FAILURE, not a smaller
    # number.  (A single `shr(52, mul(` regex over a SPREAD Barrett counts TWO per
    # reduction site, one for each spread half; these count one each.)
    _BARRETT_RE = re.compile(r"shr\(33, mul\(")
    _RED2_RE = re.compile(r"shr\(23, ")
    # `mod(` / `mul(` counted as OPCODES, not as substrings: `mulmod(` and
    # `addmod(` both contain `mod(` (and `mulmod(` contains `mul(`), and the
    # inverse entry block now reduces with mulmod/addmod — a raw substring
    # count would smear those into the `mod`-only-at-layer-8 conjuncts.  The
    # native-modmul opcodes get occurrence counts of their own below.
    _PLAINMOD_RE = re.compile(r"(?<![A-Za-z])mod\(")
    _PLAINMUL_RE = re.compile(r"(?<![A-Za-z])mul\(")
    # every per-layer offset constant, with the K it encodes (K*q)
    _K_OF = {"ACCQ30": 1 << 30, "ACCQ31": 1 << 31, "TWOQ": 2, "TWOQ4": 2,
             "Q4_4": 4, "Q4_8": 8, "Q4_16": 16, "Q4_32": 32, "Q4_64": 64,
             "Q4_128": 128}
    _OFFSET_RE = {o: re.compile(r"\b" + o + r"\b") for o in _K_OF}
    # The forward butterfly's PAIRED stores, in the RADIX-8 fused form: every
    # Barrett result t0 is consumed exactly twice, once as a sum `add(X, t0)`
    # and once as an offset difference `sub(add(X, TWOQ4), t0)`, where X is the
    # octet's loaded word (u0..u3) at the first fused layer, that layer's output
    # (a0/a1/b0/b1) at the second and the second's output (c0/c2/c4/c6) at the
    # third -- twelve minuend names, one per butterfly of an octet, and the
    # enumeration is CLOSED (a butterfly whose minuend is named anything else is
    # not counted, so it cannot hide inside these totals).  Counting the WHOLE
    # difference expression -- not just `add(u, TWOQ4)`, as the pre-fusion
    # revision did -- also pins the SUBTRACTION direction, so
    # `add(add(X, TWOQ4), t0)`, which would grow the lane by 4q instead of 2q,
    # no longer counts as a difference store.
    _SUM_RE = re.compile(r"add\((?:u[0-3]|a[01]|b[01]|c[0246]), t0\)")
    _DIFF_RE = re.compile(r"sub\(add\((?:u[0-3]|a[01]|b[01]|c[0246]), TWOQ4\), t0\)")

    def _consts(code):
        """File-scope `uint256 constant NAME = <literal>;`, duplicates rejected."""
        d = {}
        for m in _CONST_RE.finditer(code):
            if m.group(1) in d:
                raise ValueError(f"constant {m.group(1)} declared more than once")
            d[m.group(1)] = int(m.group(2), 0)
        return d

    def _declared_consts(code):
        """EVERY constant DECLARATION in the file: any type, any scope.

        `_CONST_RE` above sees only `uint256 constant`, at file scope, with a
        numeric literal.  That is the extraction C18 models BY VALUE -- and it
        is not the set a completeness check needs, because a constant of another
        type (`bytes32 private constant F1600_CODEHASH`) or an added alias is
        invisible to it.  This is the DECLARED set, compared against the
        modelled set below; a name that appears here and nowhere in the tables
        is a FAILURE -- that is the rename-alias route, closed.
        """
        names = [m.group(1) for m in _DECL_CONST_RE.finditer(code)]
        dup = sorted({n for n in names if names.count(n) > 1})
        if dup:
            raise ValueError(f"constant(s) declared more than once: {dup}")
        return sorted(names)

    def _consts_never_read(code, names):
        """Declared constants that occur ONLY in their own declaration.

        The rename-alias attack leaves the old constant DECLARED and correct
        (so the value conjunct still passes) while every USE SITE moves to a new
        one.  Requiring at least one occurrence outside the declaration is what
        makes the decoy half visible.
        """
        return sorted(n for n in names
                      if len(re.findall(r"\b" + re.escape(n) + r"\b", code)) < 2)

    def _norm(text):
        """Comment- and string-stripped source, whitespace-normalised.

        Reformatting and re-commenting do not move it; every token does.
        """
        return " ".join(text.split())

    def _fdigest(text):
        return hashlib.sha256(_norm(text).encode("utf-8")).hexdigest()[:32]

    def _region_summary(text):
        """The MULTISET summary of one region.

        Summarising a block by the SET of offset constants it mentions is not
        enough: deleting one lane group's `add(u, Q4_16)`
        while three others in the same block still name `Q4_16` moves nothing --
        `K_per_block` stays `[[1,2],[4],[8],[16],[32],[2,64,128]]` and the
        suite prints `[PASS] C16`.  Counting occurrences, not names, is what
        makes a dropped offset visible; `mstore`/`mload`/`mul` are counted for
        the same reason -- a butterfly that loses its offset keeps its stores.
        """
        return dict(
            K=tuple((o, len(_OFFSET_RE[o].findall(text))) for o in sorted(_K_OF)
                    if _OFFSET_RE[o].search(text)),
            barrett=len(_BARRETT_RE.findall(text)),
            red2=len(_RED2_RE.findall(text)),
            mod=len(_PLAINMOD_RE.findall(text)),
            mstore=text.count("mstore("),
            mload=text.count("mload("),
            mul=len(_PLAINMUL_RE.findall(text)),
            mulmod=text.count("mulmod("),
            addmod=text.count("addmod("),
        )

    def _shape(code, fn, end_fn):
        """The CODE-anchored structural summary of one transform.

        THE DEFECT THIS SIGNATURE EXISTS TO CLOSE.  Slicing the body as
        `body[marks[k].end():marks[k+1].start()]` for
        k < len(marks)-1 covers only the INTERIOR of the marker sequence.  Code
        before the first marker and code after the last marker then
        belongs to no block and is summarised by NOTHING.  Both are live:

          * a ninth, entirely unreduced inverse layer appended after
            `mstore(add(PR, 0xc0), gas())` leaves such a shape
            byte-identical and the suite prints `ALL CHECKS PASS`;
          * a loop inserted before `mstore(PR, gas())` that adds 128q to every
            input lane -- which falsifies S6/C9g's "entered canonical" premise
            outright -- does the same.

        The partition below is TOTAL: region 0 is the head (function entry to
        the first marker), regions 1..n-1 are the marker-delimited blocks, and
        region n is the tail (last marker to the end of the function).  Every
        byte of the body is in exactly one region or inside a marker, and
        `_fwd_shape_ok`/`_inv_shape_ok` require the head and the tail to be
        INERT.  `body_digest` is the residual catch-all: it moves on any change
        to the function that the summary above does not model (a re-tuned
        twiddle literal in the head's `psirev` table, for instance).
        """
        body = code[code.index("function " + fn):code.index("function " + end_fn)]
        marks = list(_MARK_RE.finditer(body))
        if len(marks) < 2:
            raise ValueError(f"{fn}: {len(marks)} profiling markers, expected >= 2")
        cuts = ([(0, marks[0].start())]
                + [(marks[k].end(), marks[k + 1].start()) for k in range(len(marks) - 1)]
                + [(marks[-1].end(), len(body))])
        regions = [body[a:b] for a, b in cuts]
        blks = regions[1:-1]
        return dict(
            n_blocks=len(blks),
            mod_total=len(_PLAINMOD_RE.findall(body)),
            mod_per_block=[len(_PLAINMOD_RE.findall(b)) for b in blks],
            barrett_per_block=[len(_BARRETT_RE.findall(b)) for b in blks],
            red2_per_block=[len(_RED2_RE.findall(b)) for b in blks],
            # the SCHEDULE, extracted: the K of every offset constant used in
            # each marker-delimited layer block
            K_per_block=[sorted({_K_OF[o] for o in _K_OF
                                 if _OFFSET_RE[o].search(b)}) for b in blks],
            # the TOTAL partition -- head, blocks, tail -- with
            # occurrence COUNTS rather than a set of names
            region_summary=[_region_summary(r) for r in regions],
            sum_stores=len(_SUM_RE.findall(body)),
            diff_stores=len(_DIFF_RE.findall(body)),
            body_digest=_fdigest(body),
        )

    def _inert(r):
        """A region that is not a layer: no per-layer offset constant, no
        reduction, no memory traffic, no multiply.

        The head and the tail of both transforms must be inert.  That, and
        nothing weaker, is what makes "the marker-delimited blocks" a COMPLETE
        account of the function rather than a sample of it."""
        return (r["K"] == () and r["barrett"] == 0 and r["red2"] == 0
                and r["mod"] == 0
                and r["mstore"] == 0 and r["mload"] == 0 and r["mul"] == 0
                and r["mulmod"] == 0 and r["addmod"] == 0)

    def _offsets_every_butterfly(r, layers):
        """In a RADIX-2^L FUSED layer block (L layers, ONE tuple of 2^L words
        loaded once and stored once) there are L * 2^(L-1) butterflies and 2^L
        stores -- every intermediate layer's results stay on the stack -- so the
        number of per-layer offset-constant OCCURRENCES is exactly L/2 times the
        store count.  Dropping one lane group's `+K q` breaks this even though
        the constant's NAME survives.  The forward transform's two word-aligned
        blocks are radix-8 (L = 3: twelve offsets, eight stores) and the
        inverse's are radix-4 (L = 2: four offsets, four stores); an UNFUSED
        block holds one layer, i.e. the same
        offsets-per-butterfly invariant at L = 1."""
        return r["mstore"] > 0 and 2 * sum(c for _o, c in r["K"]) == layers * r["mstore"]

    def _mutate_region(sh, idx, **kw):
        """`sh` with one region's summary overridden — for the negative controls."""
        rs = [dict(r) for r in sh["region_summary"]]
        rs[idx] = dict(rs[idx], **kw)
        return dict(sh, region_summary=rs)

    def _rep(val, lanes, width):
        return sum(val << (width * k) for k in range(lanes))

    # every shipped copy of each transform; they must all agree
    C16_FWD = ["test/ZZZ_NttVariants.sol",
               "src/Ntt.sol"]
    C16_INV = ["test/ZZZ_InvNtt.sol",
               "src/InvNtt.sol"]

    # ---------------------------------------------------------------------
    # THE PINNED SHIPPED SHAPE
    # ---------------------------------------------------------------------
    # Every region of both transforms, head and tail included, with occurrence
    # counts.  The OBSERVED region summaries and digests are printed in C16's
    # detail line on every run, so regenerating these after a deliberate re-tune
    # is a copy from that output — never a silent recompute inside the check.
    # A re-tuned transform must move these, and that is the point: C16 exists so
    # that a schedule change FAILS instead of the proof silently describing a
    # different program.
    # NOTE ON THE FUSED PASS STRUCTURE.  Both transforms now run their
    # word-aligned layers as RADIX-4 FUSED passes: one quad of four words is
    # loaded once, TWO layers run on the stack, and the quad is stored once.
    # That is a SCHEDULING change only -- the per-layer offsets, the Barrett
    # domain and the lane-growth budget are exactly as before (a fused block's
    # second layer consumes the first layer's outputs, which satisfy that
    # layer's entry bound by construction).  What it does change is the number
    # of marker-delimited blocks: forward 7 -> 4 (L1+L2, L3+L4, L5+L6, L7+L8),
    # inverse 6 -> 4 (entry fold + L1+L2, L3+L4, L5+L6, L7+L8), which is why
    # every count below moved.
    # NOTE ON THE TWO-STEP REDUCTION.  `barrett` counts step 1 (`shr(33, mul(`)
    # and `red2` counts step 2 (`shr(23, `), one each per reduction SITE -- the
    # old spread form's single regex counted two per site, one per spread half,
    # which is why every `barrett` count below halved.  `mul` fell with it: a
    # site is now 3 multiplies (x*MU33, qhat*q, b*q) where the spread form
    # needed 4 (two halves x two multiplies) plus the spread/repack masks.
    _FWD_REGIONS = [
        dict(K=(), barrett=0, red2=0, mod=0, mstore=0, mload=0, mul=0,
             mulmod=0, addmod=0),                                               # head
        dict(K=(("TWOQ4", 12),), barrett=12, red2=12, mod=0, mstore=8, mload=8, mul=48,
             mulmod=0, addmod=0),                                               # L1+L2+L3 fused (radix-8)
        dict(K=(("TWOQ4", 12),), barrett=12, red2=12, mod=0, mstore=8, mload=11, mul=48,
             mulmod=0, addmod=0),                                               # L4+L5+L6 fused (radix-8)
        dict(K=(("TWOQ", 16),), barrett=0, red2=0, mod=0, mstore=4, mload=6, mul=0,
             mulmod=16, addmod=0),                                              # L7+L8 (lazy exit, 4 words/iter)
        dict(K=(), barrett=0, red2=0, mod=0, mstore=0, mload=0, mul=0,
             mulmod=0, addmod=0),                                               # tail
    ]
    _INV_REGIONS = [
        dict(K=(), barrett=0, red2=0, mod=0, mstore=0, mload=0, mul=0,
             mulmod=0, addmod=0),                                               # head
        dict(K=(("ACCQ30", 8), ("ACCQ31", 4), ("TWOQ", 4)),
             barrett=0, red2=0, mod=0, mstore=4, mload=6, mul=0,
             mulmod=16, addmod=4),                                              # entry fold + L1+L2 (4 words/iter)
        dict(K=(("Q4_4", 2), ("Q4_8", 2)), barrett=4, red2=4, mod=0, mstore=4, mload=6,
             mul=16, mulmod=0, addmod=0),                                       # L3+L4 fused
        dict(K=(("Q4_16", 2), ("Q4_32", 2)), barrett=4, red2=4, mod=0, mstore=4, mload=5,
             mul=16, mulmod=0, addmod=0),                                       # L5+L6 fused
        dict(K=(("Q4_128", 1), ("Q4_64", 2), ("TWOQ4", 1)),
             barrett=2, red2=2, mod=16, mstore=4, mload=4, mul=12,
             mulmod=0, addmod=0),                                               # L7+L8
        dict(K=(), barrett=0, red2=0, mod=0, mstore=0, mload=0, mul=0,
             mulmod=0, addmod=0),                                               # tail
    ]
    # the residual digests: the whole normalised function body, and the whole
    # normalised FILE (so a payload in `ipackCoeffs`, in the constant block or in
    # the `psirev` twiddle table is visible too -- none of those is inside
    # `nttInvV3`, and the body digest alone cannot reach them)
    # These four cover the shipped sources' string literals too: `_strip_sol`
    # substitutes a DIGEST of each literal rather than erasing its contents,
    # which is what brings those literals inside `_fdigest`'s coverage.
    # THE TWIDDLE TABLES LIVE OUTSIDE THE TRANSFORMS, so the FILE digest is
    # the only thing covering them and it is load-bearing rather than belt-and-
    # braces.  They are `nttFwTable()` / `nttInvTable()`, called ONCE per
    # verify() and handed to each transform as a raw memory pointer rather than
    # sitting as an array literal in the transform's own head (-10,321 gas,
    # -201 bytes).  That is a HAND-OFF only -- the twiddle words are the same
    # words in the same order at the same offsets, `add(psirev, 0x20*k)` inside
    # each transform is unchanged to the character, and every structural
    # conjunct above (region summaries, head/tail inertness, offset counts,
    # store pairing, reduction counts, copies-agree) is blind to the hand-off;
    # only these four residual digests see it -- the contract they carry.
    _C16_BODY_DIGEST = {"fwd": "8719fdd28e9a6a676b3e134a5dd2fe9f",
                        "inv": "d50c74870791865c2d13504d1733ae08"}
    _C16_FILE_DIGEST = {"fwd": "88f75ee9baa21a9c87aa42024c450ebc",
                        "inv": "95de939acb7a1b2a2a07b0e4fb5b7f41"}

    # ---------------------------------------------------------------------
    # THE FILE-SCOPE CONSTANT BLOCK, BY DERIVATION AND CLOSED
    # ---------------------------------------------------------------------
    # A three-NAME allowlist -- "no constant whose name
    # contains SPREAD, QHATM or MU52 may remain" -- only
    # catches the dead artefact somebody already thought of.  Others would
    # walk straight through it in BOTH shipped forward copies: a `LO128`
    # 128-bit lane mask, or a `TWOQ2` holding 2q at 128-bit spacing -- the
    # working set of a SPREAD Barrett, read by nothing, describing a
    # reduction the transform does not perform.
    #
    # So the check here is by VALUE, by DERIVATION, and CLOSED: each shipped
    # transform's file-scope constants must be EXACTLY this map, so an extra
    # declaration FAILS whatever it is called and a re-tuned one FAILS whatever
    # it is named.  Nothing here is a copied literal -- every value is computed
    # from q (and from FIPS 204's zeta = 1753 for the folded L8 twiddle), so a
    # constant that agrees with the pin agrees with the arithmetic.
    def _inv_mod(a, m):
        """a^-1 mod m, or None when it does not exist.

        MUST NOT RAISE.  Vacuity mutation V29f rewrites `Q` ITSELF, and 256 is
        not invertible modulo every integer; an uncaught ValueError here would
        CRASH the whole obligation suite instead of failing C16's conjunct --
        the "crash instead of a verdict" category the vacuity audit refuses,
        and it would take C1b's two modulus conjuncts (whose only killer is
        V29f) down with it.  None propagates into the expected map below, no
        shipped integer equals None, and the conjunct FAILS, which is the
        verdict a mutated modulus should produce.
        """
        try:
            return pow(a, -1, m)
        except ValueError:
            return None

    _NINV = _inv_mod(1 << 8, Q)                   # n^-1 mod q, n = 256
    _ZETA_INV = _inv_mod(1753, Q)                 # zeta^-1; zeta = 1753 (FIPS 204)
    _C16_FWD_CONSTS = {
        "Q": Q,
        "MU33": (1 << 33) // Q,                   # the coarse Barrett constant
        "QHATM31": _rep((1 << 31) - 1, 4, 64),    # 64 - 33 == 31 bits per lane
        "LANE": (1 << 64) - 1,
        "TWOQ4": _rep(2 * Q, 4, 64),
        "TWOQ": 2 * Q,
    }
    _C16_INV_CONSTS = dict(
        _C16_FWD_CONSTS,
        NINV=_NINV,
        # the folded layer-8 twiddle: psirev_inv[1] * n^-1 mod q, and
        # psirev_inv[1] = zeta^-brv8(1) = zeta^-128
        S8P=(None if _NINV is None or _ZETA_INV is None
             else (pow(_ZETA_INV, 128, Q) * _NINV) % Q),
        ACCQ30=Q << 30,
        ACCQ31=Q << 31,
        **{f"Q4_{K}": _rep(K * Q, 4, 64) for K in (4, 8, 16, 32, 64, 128)},
    )

    def _fwd_shape_ok(sh):
        """The forward schedule C9f/S5 assume: 8 layers in 3 fused marker blocks
        — two RADIX-8 blocks (L1+L2+L3 and L4+L5+L6, each loading one octet of
        eight words once, running three layers on the stack and storing once)
        and the in-word L7+L8 — every layer offset by 2q, and the fused final
        block — whose two layers are IN-WORD, so their lanes are extracted to
        scalars anyway — reduces ALL FOUR of its twiddle products per data word
        with the EVM's native mulmod (16 for the four words it unrolls: L7's
        two, which share S7, and L8's two).  Every one of them is therefore
        CANONICAL (< q, tighter than the < 2q a Barrett leaves), so the +2q
        growth envelope still holds; consequently the block carries NO Barrett
        at all (`barrett_per_block[2] == 0`, which is what a Barrett smuggled
        back into the tail would break) and no `mul` outside a mulmod.  The
        block still emits LAZY lanes — no `mod` canonicalisation anywhere, no
        mulmod/addmod outside that block — and there is NOTHING outside those
        blocks (the head and the tail are regions too, and must be inert).
        Each of the two word-aligned fused blocks carries 12 butterflies, 8
        stores and 12 TWOQ4 offsets per octet, and the whole body pairs 24 sum
        stores with 24 offset-difference stores: that pairing IS the
        +2q-per-layer budget.  RADIX-8 FUSION IS A SCHEDULING CHANGE ONLY —
        every layer's operands are the previous layer's outputs, exactly as
        before, so no lane bound, offset constant or Barrett domain in C9a/C9f/
        S5 moves; what moves is the block partition extracted here."""
        try:
            rs = sh["region_summary"]
            return (sh["n_blocks"] == 3
                    and len(rs) == 5
                    and _inert(rs[0]) and _inert(rs[-1])
                    and all(_offsets_every_butterfly(r, 3) for r in rs[1:3])
                    and sh["K_per_block"] == [[2], [2], [2]]
                    and sh["barrett_per_block"] == [12, 12, 0]
                    and sh["red2_per_block"] == sh["barrett_per_block"]
                    and sh["mod_per_block"] == [0, 0, 0]
                    and sh["mod_total"] == 0
                    and rs[3]["mulmod"] == 16     # (2 L7 + 2 L8 products) x 4 words/iter
                    and rs[3]["addmod"] == 0
                    and sum(r["mulmod"] for r in rs) == 16
                    and sum(r["addmod"] for r in rs) == 0
                    and sh["sum_stores"] == sh["diff_stores"] == 24)
        except Exception:
            return False

    def _inv_shape_ok(sh):
        """The inverse schedule C9g/S6/S6b/S14 assume: the entry block folds the
        accumulator reduction in with EXACTLY 4 mulmod + 1 addmod per data word
        (16 + 4 for the four words it unrolls) against the ACCQ30/ACCQ31
        offsets; layers 3..8 use K = 2^(L-1) over the remaining 3 radix-4 fused
        marker blocks (L3+L4, L5+L6, L7+L8), Barrett at L3..L7 and plain `mod`
        ONLY in the final block (16 = 4 stores x 4 lanes) — and NOTHING outside
        those blocks (the head and the tail are regions too, and must be
        inert).  Fusing two layers into one block does not merge their offsets:
        each fused block still names BOTH of its layers' K*q constants, twice
        each, one per butterfly."""
        try:
            rs = sh["region_summary"]
            return (sh["n_blocks"] == 4
                    and len(rs) == 6
                    and _inert(rs[0]) and _inert(rs[-1])
                    and all(_offsets_every_butterfly(r, 2) for r in rs[2:4])
                    and sh["K_per_block"] == [[2, 1 << 30, 1 << 31],
                                              [4, 8], [16, 32], [2, 64, 128]]
                    and sh["barrett_per_block"] == [0, 4, 4, 2]
                    and sh["red2_per_block"] == sh["barrett_per_block"]
                    and sh["mod_per_block"] == [0, 0, 0, 16]
                    and sh["mod_total"] == 16
                    and rs[1]["mulmod"] == 16     # (2 L1 + 2 L2 diffs) x 4 words/iter
                    and rs[1]["addmod"] == 4      # the L2 sum-sum lane x 4 words/iter
                    and sum(r["mulmod"] for r in rs) == 16
                    and sum(r["addmod"] for r in rs) == 4)
        except Exception:
            return False

    try:
        fwd_codes = [_strip_sol(_sol(p)) for p in C16_FWD]
        inv_codes = [_strip_sol(_sol(p)) for p in C16_INV]
        fwd_norms = [_fdigest(c) for c in fwd_codes]
        inv_norms = [_fdigest(c) for c in inv_codes]
        fwd_shapes = [_shape(c, "nttFwV3", "lazyBarrett") for c in fwd_codes]
        inv_shapes = [_shape(c, "nttInvV3", "invLazyBarrett") for c in inv_codes]
        fcs = [_consts(c) for c in fwd_codes]
        ics = [_consts(c) for c in inv_codes]
        fc, ic = fcs[0], ics[0]
        fwd_shape, inv_shape = fwd_shapes[0], inv_shapes[0]
        c16 = [
            ("fwd_MU33", fc["MU33"] == (1 << 33) // Q),
            ("inv_MU33", ic["MU33"] == (1 << 33) // Q),
            # the 31-bit-per-lane quotient mask: 64 - 33 == 31 is what makes ONE
            # mask both extract the quotient and block the neighbour lane (C9h)
            ("fwd_QHATM31_is_2p31m1_per_lane", fc["QHATM31"] == _rep((1 << 31) - 1, 4, 64)),
            ("inv_QHATM31_is_2p31m1_per_lane", ic["QHATM31"] == _rep((1 << 31) - 1, 4, 64)),
            # ... and the WHOLE constant block of each transform is exactly the
            # derived set above -- no extra declaration, whatever it is named
            # (stronger than a three-name "no SPREAD/QHATM/MU52" allowlist, which
            # `LO128` and `TWOQ2`, the spread Barrett's own working
            # set, walk straight through)
            ("fwd_constants_are_exactly_the_derived_set", fc == _C16_FWD_CONSTS),
            ("inv_constants_are_exactly_the_derived_set", ic == _C16_INV_CONSTS),
            ("fwd_TWOQ4_is_2q_per_lane", fc["TWOQ4"] == _rep(2 * Q, 4, 64)),
            ("fwd_TWOQ_is_2q", fc["TWOQ"] == 2 * Q),
            # every forward sum store `add(u, t0)` has a matching `add(u, TWOQ4)`
            # diff store: that pairing IS the +2q lane growth S5/C9f assume.
            ("fwd_every_butterfly_offsets_by_2q",
             fwd_shape["sum_stores"] == fwd_shape["diff_stores"] > 0),
            # the entry-fold offsets: multiples of q that dominate one / two raw
            # accumulator lanes (S14's no-borrow premise, C9g's linkage)
            ("inv_ACCQ30_is_q_shl_30", ic["ACCQ30"] == Q << 30),
            ("inv_ACCQ31_is_q_shl_31", ic["ACCQ31"] == Q << 31),
            ("inv_TWOQ_is_2q", ic["TWOQ"] == 2 * Q),
            ("inv_TWOQ4_is_2q_per_lane", ic["TWOQ4"] == _rep(2 * Q, 4, 64)),
        ]
        for K in (4, 8, 16, 32, 64, 128):
            c16.append((f"inv_Q4_{K}_is_{K}q_per_lane", ic[f"Q4_{K}"] == _rep(K * Q, 4, 64)))
        # layer 8 canonicalises with `mod`, not Barrett: 4 stores x 4 lanes, and
        # the count is over CODE, in the marker-delimited final block only.
        c16.append(("inv_layer8_canonicalises_with_mod", inv_shape["mod_per_block"][-1] == 16))
        c16.append(("inv_layer8_no_extra_mod_elsewhere",
                    sum(inv_shape["mod_per_block"][:-1]) == 0
                    and inv_shape["mod_total"] == inv_shape["mod_per_block"][-1]))
        # the SCHEDULE itself, extracted from the shipped code
        c16.append(("fwd_schedule_extracted_is_plus_2q_x8", _fwd_shape_ok(fwd_shape)))
        c16.append(("inv_schedule_extracted_is_K_2powL", _inv_shape_ok(inv_shape)))
        # BOTH STEPS OF EVERY REDUCTION, region by region.  Step 1 alone lands
        # at < 2^33 -- three orders of magnitude above the < 2q every lane bound
        # in C9f/C9g/S5/S6 assumes -- so a reduction that lost its second line
        # must be a FAILURE and not a smaller number.  Stated separately from
        # the shape predicates so the audit can see it fail on its own.
        c16.append(("fwd_every_reduction_has_both_steps",
                    fwd_shape["red2_per_block"] == fwd_shape["barrett_per_block"]
                    and sum(fwd_shape["barrett_per_block"]) == 24))
        c16.append(("inv_every_reduction_has_both_steps",
                    inv_shape["red2_per_block"] == inv_shape["barrett_per_block"]
                    and sum(inv_shape["barrett_per_block"]) == 10))
        # The marker-delimited blocks must be the WHOLE transform.
        # Stated separately from the shape predicates so that the audit can see
        # these two facts fail on their own.
        c16.append(("fwd_head_and_tail_are_inert",
                    _inert(fwd_shape["region_summary"][0])
                    and _inert(fwd_shape["region_summary"][-1])
                    and len(fwd_shape["region_summary"]) == fwd_shape["n_blocks"] + 2))
        c16.append(("inv_head_and_tail_are_inert",
                    _inert(inv_shape["region_summary"][0])
                    and _inert(inv_shape["region_summary"][-1])
                    and len(inv_shape["region_summary"]) == inv_shape["n_blocks"] + 2))
        # ... and inside a plain layer block every butterfly carries its offset,
        # counted by OCCURRENCE (a dropped `+16q` keeps the name `Q4_16` alive)
        c16.append(("fwd_every_plain_block_offsets_every_butterfly",
                    all(_offsets_every_butterfly(r, 3)
                        for r in fwd_shape["region_summary"][1:3])))
        c16.append(("inv_every_plain_block_offsets_every_butterfly",
                    all(_offsets_every_butterfly(r, 2)
                        for r in inv_shape["region_summary"][2:4])))
        # ... and the whole region table is the pinned one, region by region
        c16.append(("fwd_region_summary_is_the_pinned_one",
                    fwd_shape["region_summary"] == _FWD_REGIONS))
        c16.append(("inv_region_summary_is_the_pinned_one",
                    inv_shape["region_summary"] == _INV_REGIONS))
        c16.append(("fwd_body_digest_is_the_pinned_one",
                    fwd_shape["body_digest"] == _C16_BODY_DIGEST["fwd"]))
        c16.append(("inv_body_digest_is_the_pinned_one",
                    inv_shape["body_digest"] == _C16_BODY_DIGEST["inv"]))
        # every shipped copy agrees, so the obligation is about the DEPLOYED code
        c16.append(("all_shipped_fwd_copies_agree",
                    len(fwd_shapes) == 2 and all(s == fwd_shape for s in fwd_shapes)
                    and all(c == fc for c in fcs)))
        c16.append(("all_shipped_inv_copies_agree",
                    len(inv_shapes) == 2 and all(s == inv_shape for s in inv_shapes)
                    and all(c == ic for c in ics)))
        # A structural summary is a summary: it models what it
        # was written to model.  These two conjuncts are the RESIDUAL -- the whole
        # normalised text of every shipped copy, digested -- so that a payload the
        # extraction does not model (another function in the same file, a re-tuned
        # twiddle literal, an altered constant block) is a FAILURE and not a blind
        # spot.  Every shipped copy must equal the SAME pinned digest, which is what
        # "byte-identical apart from comments" means for the shipped code.
        c16.append(("fwd_shipped_sources_are_the_pinned_bytes",
                    len(fwd_norms) == 2
                    and all(d == _C16_FILE_DIGEST["fwd"] for d in fwd_norms)))
        c16.append(("inv_shipped_sources_are_the_pinned_bytes",
                    len(inv_norms) == 2
                    and all(d == _C16_FILE_DIGEST["inv"] for d in inv_norms)))
        # CONTROLS: the shape predicates must REJECT a re-tuned schedule.
        # Without these, `_fwd_shape_ok`/`_inv_shape_ok` rewritten to `True`
        # would still report PASS.  They go through `controls()` like every
        # other control so that the catalogue's VT01/VT02 (which gut
        # `controls` itself) reach them; building them inline once left nine
        # of them unreachable by any mutation.
        for _n, _kw in (("nine_layers", dict(n_blocks=4)),
                        ("layer_offset_4q", dict(K_per_block=[[2], [2], [4]])),
                        ("extra_mod_layer", dict(mod_per_block=[0, 4, 0])),
                        ("tail_canonicalises_again", dict(mod_per_block=[0, 0, 4])),
                        ("unpaired_diff_store", dict(diff_stores=22))):
            c16 += controls(_fwd_shape_ok, label=f"ctl_fwd_{_n}",
                            reject=[dict(fwd_shape, **_kw)])
        # ... and the tail's mulmod reductions are load-bearing: a tail that
        # lost one (its product would exit unreduced at ~2^50 and the matvec's
        # lane locality O7 would be gone) must be rejected.
        c16 += controls(_fwd_shape_ok, label="ctl_fwd_one_tail_mulmod_dropped",
                        reject=[_mutate_region(fwd_shape, 3, mulmod=15)])
        # ... and a spread Barrett smuggled BACK into the fused tail (which
        # would leave its products < 2q instead of canonical, i.e. a different
        # growth envelope from the one C9f's induction is stated over) must be
        # rejected -- the mirror of ctl_inv_barrett_at_layer8 for the forward.
        c16 += controls(_fwd_shape_ok, label="ctl_fwd_barrett_back_in_the_tail",
                        reject=[dict(fwd_shape, barrett_per_block=[12, 12, 2],
                                     red2_per_block=[12, 12, 2])])
        # ... and the SECOND STEP of one reduction dropped: the site still looks
        # like a reduction to a step-1-only census, and its lane exits at < 2^33.
        c16 += controls(_fwd_shape_ok, label="ctl_fwd_one_second_step_dropped",
                        reject=[dict(fwd_shape, red2_per_block=[12, 11, 0])])
        # ... and a RADIX-8 block that lost one whole butterfly: the offsets, the
        # reductions and the paired stores all fall together, and each of the
        # three counts must be enough on its own to reject it.
        c16 += controls(_fwd_shape_ok, label="ctl_fwd_one_octet_butterfly_dropped",
                        reject=[dict(_mutate_region(fwd_shape, 1,
                                                    K=(("TWOQ4", 11),), barrett=11,
                                                    red2=11, mul=44),
                                     barrett_per_block=[11, 12, 0],
                                     red2_per_block=[11, 12, 0],
                                     sum_stores=23, diff_stores=23)])
        # ... and a radix-8 block re-cut as radix-4 WITHOUT re-cutting the rest:
        # eight stores against eight offsets is the radix-4 ratio, so the block
        # would be running two layers where the schedule states three.
        c16 += controls(_fwd_shape_ok, label="ctl_fwd_octet_block_is_only_radix4",
                        reject=[dict(_mutate_region(fwd_shape, 2,
                                                    K=(("TWOQ4", 8),), barrett=8,
                                                    red2=8, mul=32),
                                     barrett_per_block=[12, 8, 0],
                                     red2_per_block=[12, 8, 0],
                                     sum_stores=20, diff_stores=20)])
        for _n, _kw in (("seven_blocks", dict(n_blocks=5)),
                        ("layer7_K_doubled",
                         dict(K_per_block=[[2, 1 << 30, 1 << 31], [4, 8], [16, 32],
                                           [2, 128]])),
                        ("barrett_at_layer8",
                         dict(barrett_per_block=[0, 4, 4, 4], red2_per_block=[0, 4, 4, 4])),
                        ("mod_in_a_barrett_block", dict(mod_per_block=[0, 0, 16, 16])),
                        ("layer8_not_canonicalised", dict(mod_per_block=[0, 0, 0, 0])),
                        ("one_second_step_dropped", dict(red2_per_block=[0, 4, 4, 1]))):
            c16 += controls(_inv_shape_ok, label=f"ctl_inv_{_n}",
                            reject=[dict(inv_shape, **_kw)])
        # ... and the ENTRY FOLD's own rejected schedules: the pre-fold block
        # shape (no mulmod/addmod, Barrett back at L1/L2 — i.e. the entry
        # reduction dropped while the verifier feeds raw accumulators), and a
        # block that lost one of its mulmod reductions.
        c16 += controls(_inv_shape_ok, label="ctl_inv_entry_fold_dropped",
                        reject=[dict(_mutate_region(inv_shape, 1, mulmod=0, addmod=0),
                                     barrett_per_block=[2, 4, 4, 2],
                                     red2_per_block=[2, 4, 4, 2])])
        c16 += controls(_inv_shape_ok, label="ctl_inv_one_entry_mulmod_dropped",
                        reject=[_mutate_region(inv_shape, 1, mulmod=15)])
        # CONTROLS.  The three shapes a marker-INTERIOR extraction accepts
        # as byte-identical to the shipped one.  Each is reproducible
        # against the real tree; see FORMAL_VERIFICATION.md
        # §5 item 6.
        for _fn, _sh, _pred, _nb in (("fwd", fwd_shape, _fwd_shape_ok, 3),
                                     ("inv", inv_shape, _inv_shape_ok, 4)):
            # (a) a payload BEFORE the first marker -- e.g. a loop that adds 128q
            #     to every input lane, which destroys "entered canonical"
            c16 += controls(_pred, label=f"ctl_{_fn}_payload_before_first_marker",
                            reject=[_mutate_region(_sh, 0, mstore=64, mload=64,
                                                   mul=0, K=(("Q4_128", 64),))])
            # (b) a payload AFTER the last marker -- a ninth, unreduced layer
            c16 += controls(_pred, label=f"ctl_{_fn}_payload_after_last_marker",
                            reject=[_mutate_region(_sh, -1, mstore=64, mload=64,
                                                   mul=32, K=(("Q4_128", 32),))])
            # (c) one lane group's offset DROPPED inside a plain layer block:
            #     the constant's name survives, its occurrence count does not
            _plain = 2 if _fn == "inv" else 2
            _kept = tuple((o, c - 1) for o, c in _sh["region_summary"][_plain]["K"])
            c16 += controls(_pred, label=f"ctl_{_fn}_one_offset_dropped_in_a_block",
                            reject=[_mutate_region(_sh, _plain, K=_kept)])
        c16 += controls(_fwd_shape_ok, label="ctl_fwd_accepts_the_shipped_shape",
                        accept=[fwd_shape])
        c16 += controls(_inv_shape_ok, label="ctl_inv_accepts_the_shipped_shape",
                        accept=[inv_shape])
        c16_detail = (f"{len(c16)} constants/shapes/controls cross-checked against "
                      f"{len(C16_FWD) + len(C16_INV)} shipped Yul sources; "
                      f"regions fwd={len(fwd_shape['region_summary'])} "
                      f"inv={len(inv_shape['region_summary'])} (head+blocks+tail); "
                      f"observed digests body fwd={fwd_shape['body_digest']} "
                      f"inv={inv_shape['body_digest']} file fwd={fwd_norms[0]} "
                      f"inv={inv_norms[0]}")
    except Exception as exc:                       # never a silent skip -- fail loud
        c16 = [("source_readable", False)]
        c16_detail = f"CANNOT READ THE SHIPPED SOURCE: {exc!r} (set MLDSA_REPO)"
    ok &= record("C16", "EXH",
                 "the shipped NTT Yul uses exactly the per-layer offsets K*q the induction assumes",
                 True, c16_detail, parts=c16)

    # ---------------------------------------------------------------------- C18
    # SOURCE LINKAGE FOR THE FIPS VALIDITY CHECKS.
    #
    # C16 reads the two NTT files.  `src/Decode.sol` and
    # `src/MLDSA44Verifier.sol` carry EVERY FIPS 204
    # validity check the verifier applies, and 23 substring
    # counts in formal/hypotheses.py are all that would otherwise cover them,
    # which is not one coverage gap but a class of them.  Four mutations show
    # it, each leaving every obligation, every conjunct and every hypothesis
    # row GREEN:
    #   * `sub(c3, 64)` -> `sub(c3, 63)` in the hint padding check: for every
    #     hint weight in [64, 79] the FIRST padding byte stops being checked, so
    #     a SECOND distinct 2,420-byte signature verifies for one (pk, message).
    #     A strong-unforgeability break that every check passed AND that the whole
    #     305-test corpus passed.  (E15 below is the semantic answer to it.)
    #   * `PK_SIZE 20544 -> 20000`: the blob size check then admits zero-padded
    #     blobs.  hypotheses.py pinned the check's EXPRESSION TEXT -- which does
    #     not move when the constant does -- and C15b proved the width arithmetic
    #     in PYTHON, about a number the apparatus believed rather than the number
    #     the contract used.
    #   * `SW_M44 94 -> 93`: C17's magic-division proof was about a Python 94.
    #   * the z-decode driver's trip count 4 -> 3: 256 of 1024 coefficients
    #     silently undecoded and un-norm-checked.  hypotheses.py pinned the CALL
    #     SITE, not the number of times it runs.
    #
    # THE CLASS, stated so the fix can be checked against it: A PIN OVER
    # EXPRESSION TEXT IS NOT A PIN OVER THE CONSTANT VALUE, and a numeric fact
    # restated in Python is not a fact about the shipped code.  So every number
    # below is EXTRACTED FROM THE SOURCE and compared against the arithmetic the
    # obligations prove; `ctl_extracted_value_is_the_proved_value` is the
    # discrimination control that fails when the two disagree.  The whole-file
    # normalised digests are the residual, exactly as C16's are: a payload the
    # extraction does not model is a FAILURE, not a blind spot.
    #
    # COMPLETENESS OVER `src/`.  `src/FastKeccak170.sol` and
    # `src/IMLDSAVerifier.sol` would otherwise be the only files in `src/`
    # covered by NEITHER C16's digests NOR C18's -- the same uncovered-file
    # shape, on the same kind of file, as `src/Decode.sol`.  FastKeccak170.sol
    # is live on every call and carries FIPS 202's `0x1f` domain byte and `0x80`
    # final bit, the 136-byte rate at every site that spends it, the 800-byte
    # raw-permutation protocol, BOTH `returndatasize()` fail-closed checks, the
    # `input.length != 800` dispatch guard and a RAW (non-zero-filled) output
    # buffer; two substring rows in formal/hypotheses.py, both about the two
    # `104` offsets of section 4.1, are not coverage of any of that.
    # Both files are DIGESTED here on the same terms as the other two, and
    # FastKeccak170.sol's numbers are extracted BY VALUE like Decode.sol's;
    # the interface file has no numbers, so it contributes its digest and the
    # shape of the one entry point it declares.
    #
    # THE CONTROLS MUST COVER THE CONJUNCTS THEY CLAIM TO.  If every
    # substantive conjunct below spelled its comparison INLINE, `_agrees` -- the
    # predicate the seven `ctl_extracted_value_is_the_proved_value` controls pin
    # -- would be referenced by nothing but its own `controls()` call.  The
    # controls would then be a control over a helper no conjunct uses: rewriting
    # any conjunct leaves all seven green, and the only thing protecting the
    # conjuncts is META-PINS plus the vacuity mutations, a DIFFERENT mechanism
    # from the one `controls()` advertises (FORMAL_VERIFICATION.md section 2).
    # Every "extracted == proved" comparison therefore goes THROUGH `_agrees`:
    # `_agrees` rewritten in any direction moves both the controls and the
    # conjuncts they are supposed to protect.
    C18_DEC = "src/Decode.sol"
    C18_VER = "src/MLDSA44Verifier.sol"
    C18_KEC = "src/FastKeccak170.sol"
    C18_IFC = "src/IMLDSAVerifier.sol"
    # `test/FV2_Barrett.sol` is what
    # FORMAL_VERIFICATION.md section 5.7 cites when it marks the Lean<->bytecode
    # refinement gap for the Barrett family CLOSED, and by default it sits under
    # NO digest -- `source_pins` covers `formal/` only, C16 the NTT pair, C18
    # the four `src/` files.  It declares `check_*` and no `test*` functions, so
    # `forge test` compiles it and runs nothing, and no test imports it.  A
    # COMMENT claiming character-identity with `src/Ntt.sol::lazyBarrett` is not
    # a tie to the shipped kernel.  Both halves are closed: the identity is a
    # fuzz test (`FV_Kernels.t.sol::testFuzz_FV2_barrett_kernels_are_the_shipped
    # _reductions`), and the file carries a residual digest here on the same
    # terms as the four shipped sources, so an edit to a `check_*` BODY -- the
    # gap section 5.8 records for the halmos artefacts -- is a FAILED obligation.
    C18_FV2 = "test/FV2_Barrett.sol"
    ZB = GAMMA1 - BETA                      # the strict norm bound, gamma1 - beta

    # name -> (the arithmetic the constant must BE, what it is for).  Read from
    # the source; `_rep(v, 4, 64)` is the four-lane SWAR replication, so a
    # blanked or off-by-one lane moves the conjunct (mutants M40/M60/M61/M63).
    _C18_DEC_CONSTS = [
        ("MLDSA_Q", Q, "q"),
        ("Z_M18", _rep((1 << 18) - 1, 4, 64), "the 18 bit field mask per lane"),
        ("Z_UOFF", _rep(Q + GAMMA1, 4, 64), "q plus gamma1 per lane"),
        ("Z_QB32", _rep((1 << 32) - Q, 4, 64), "2p32 minus q per lane"),
        ("Z_BIT32", _rep(1 << 32, 4, 64), "the flag bit per lane"),
        ("Z_NLO", _rep((1 << 32) - ZB, 4, 64), "the low window edge per lane"),
        ("Z_NHI", _rep((1 << 32) + Q - ZB, 4, 64), "the high window edge per lane"),
        ("Z_P2", (1 << 62) + (1 << 16), "2p62 plus 2p16"),
        ("Z_P4", (1 << 124) + (1 << 78), "2p124 plus 2p78"),
        ("Z_P6", (1 << 186) + (1 << 140), "2p186 plus 2p140"),
        ("SW_REP1", _rep(1, 4, 64), "one per lane"),
        ("SW_REP6", _rep((1 << 6) - 1, 4, 64), "the 6 bit mask per lane"),
        ("SW_K32G2", _rep((1 << 32) - (GAMMA2 + 1), 4, 64), "the gamma2 comparator per lane"),
        ("SW_K321", _rep((1 << 32) - 1, 4, 64), "the nonzero comparator per lane"),
        ("SW_GATHERK", (1 << 174) + (1 << 116) + (1 << 58) + 1, "the four gather powers"),
        ("SW_MDIV", -((-1 << 39) // (2 * GAMMA2)), "ceil 2p39 over two gamma2"),
        ("SW_D", 2 * GAMMA2, "two gamma2"),
        ("SW_M44", -((-1 << 12) // 44), "ceil 2p12 over 44"),
        # C18 advertises itself as
        # "VALUE by VALUE" over the shipped sources, and `kernel_obligations.py`
        # says in as many words that "an edit to Decode.sol that moves one of
        # them fails there".  Decode.sol declares 24 file-scope constants, so a
        # table covering only 18 leaves the six matvec constants below -- the
        # pre-shifted 64-bit lane masks O7 models, the 32-bit coefficient field
        # mask, and the q*2^28 offset ACC_ENTRY is built from -- named by
        # NO conjunct.  MEASURED: replacing MV_KQ28REP by rep(Q << 29, 4, 64)
        # (still 0 mod q, still four equal lanes) fails EXACTLY ONE conjunct,
        # the whole-file digest, while all 77 value conjuncts, O7, O8, C9g, S14
        # and every hypothesis row stay green.  A digest says something moved;
        # these say WHAT.
        ("MV_M32", (1 << 32) - 1, "the 32 bit coefficient field mask"),
        ("MV_L0", ((1 << 64) - 1) << 0, "lane 0 of the pre shifted lane mask"),
        ("MV_L1", ((1 << 64) - 1) << 64, "lane 1 of the pre shifted lane mask"),
        ("MV_L2", ((1 << 64) - 1) << 128, "lane 2 of the pre shifted lane mask"),
        ("MV_L3", ((1 << 64) - 1) << 192, "lane 3 of the pre shifted lane mask"),
        ("MV_KQ28REP", _rep(Q << 28, 4, 64), "q times 2p28 per lane"),
    ]
    _C18_VER_CONSTS = [
        ("PK_SIZE", 64 + 4 * N * 4 + 16 * N * 4, "the C15b blob width"),
        ("PK_T1_OFF", 64, "t1hat after the 64 byte tr"),
        ("PK_A_OFF", 64 + 4 * N * 4, "Ahat after t1hat"),
    ]
    # src/FastKeccak170.sol's one file-scope constant: the lane mask every
    # absorb/squeeze extract ANDs with.  A short mask silently truncates a lane.
    _C18_KEC_CONSTS = [
        ("_M64_170", (1 << 64) - 1, "the 64 bit lane mask"),
    ]
    # constants that must be GONE.  SW_REP42/SW_REP44 would be declared and
    # never read (the kernel multiplies by the literals 42 and 44); SW_K3244
    # would be the second-reduction constant of a useHintSwar that does not
    # exist, and a model can easily outlive the constant it models; MU52 and
    # the SPREAD masks belong to the superseded SPREAD Barrett form.
    #
    # A FIVE-NAME BLACKLIST IS NOT A
    # COMPLETENESS CHECK, and C18's value extraction is defeatable by a
    # RENAME-ALIAS: keep `MV_KQ28REP` declared and correct, add
    # `MV_KQ28REP2 = rep(q * 2^29, 4, 64)` and point all six USE SITES at it.
    # `dec_MV_KQ28REP_is_q_times_2p28_per_lane` still passes -- it reads the
    # still-correct DECLARATION and never the constant the code USES -- so
    # exactly one conjunct moves, the whole-file digest, and the obligation that
    # advertises itself as "VALUE by VALUE" says nothing about the value the
    # kernel actually multiplies by.  Adding a brand-new file-scope constant
    # behaves the same way.  `src/Ntt.sol`/`InvNtt.sol` do not have it,
    # because C16 asserts `*_constants_are_exactly_the_derived_set`, a dict
    # EQUALITY over the whole block.
    #
    # The two conjuncts per file below are the same discipline for C18:
    #   *_constant_set_is_exactly_the_modelled_set   the DECLARED names are
    #       exactly the names modelled above -- an added constant, whatever it
    #       is called, is a FAILURE and not a blind spot.  This subsumes the
    #       blacklist, which is kept because it names WHICH five were deleted.
    #   *_every_constant_is_read_outside_its_declaration   a declared constant
    #       that no other line mentions is dead weight at best and, under a
    #       rename-alias, the decoy half of the attack.
    # `_declared_consts` reads EVERY constant declaration, of every type and at
    # every scope, so `bytes32 private constant F1600_CODEHASH` -- which the
    # `uint256 constant` regex cannot see -- is inside the set equality too and
    # is listed by name below rather than being invisible.
    _C18_DEAD = ("SW_REP42", "SW_REP44", "SW_K3244", "MU52", "SW_SPREAD")
    # Declared constants that are NOT modelled by value above, with the reason.
    # `F1600_CODEHASH` is a `bytes32` whose value is the keccak256 of
    # `helpers/f1600_170.hex`; recomputing keccak here would import a hash this
    # apparatus does not otherwise depend on, and the constant is already pinned
    # three other ways -- `formal/hypotheses.py`'s `!= F1600_CODEHASH) revert
    # BadHelper();` row (count 2), the whole-file `ver` digest below, and
    # `test/SEC_helper.t.sol`, which reverts the constructor on any other helper.
    # What was missing was not a value check but VISIBILITY: it is now a named
    # member of the declared set, so deleting it or adding a sibling MOVES a
    # conjunct.
    _C18_UNMODELLED = {"dec": (), "ver": ("F1600_CODEHASH",), "kec": ()}

    def _lane_count(word, lane_value):
        """How many of the four 64-bit lanes of `word` carry `lane_value`."""
        return sum(1 for k in range(4)
                   if (word >> (64 * k)) & ((1 << 64) - 1) == lane_value)

    def _one_num(code, rx, what):
        """The ONE number (or tuple of numbers) this pattern names in the source.

        More than one match, or none, raises -> the obligation FAILS loudly.
        This is the primitive the whole "pin the VALUE, not the expression text"
        correction is built on.
        """
        hits = re.findall(rx, code)
        if len(hits) != 1:
            raise ValueError(f"{what}: {len(hits)} matches of {rx!r}, expected 1")
        return tuple(int(g, 0) for g in hits[0]) if isinstance(hits[0], tuple) \
            else int(hits[0], 0)

    def _all_same_num(code, rx, what, want_n):
        """`want_n` occurrences of a pattern, all naming the SAME number."""
        hits = [int(h, 0) for h in re.findall(rx, code)]
        if len(hits) != want_n or len(set(hits)) != 1:
            raise ValueError(f"{what}: {hits!r}, expected {want_n} equal values")
        return hits[0]

    def _agrees(pair):
        """The value EXTRACTED from the shipped source IS the value proved."""
        return pair[0] == pair[1]

    # The pinned residual digests: the whole normalised text of each shipped
    # check file.  Regenerate from C18's own detail line after a REVIEWED edit;
    # a comment-only change does not move them (comments are stripped first).
    # The "ver" digest is what covers the twiddle-table hand-off: the tables sit
    # outside the two transforms as `nttFwTable()` / `nttInvTable()`, called
    # ONCE in `_wPrimeRows` and handed to `nttFwV3`/`nttInvV3` as a raw memory
    # pointer (-10,321 gas, -201 bytes), so MLDSA44Verifier.sol carries
    # two imports, two locals and three call arguments for it.  None of C18's
    # other 60 conjuncts -- every extracted constant, every check shape, every
    # control -- can see that hand-off, which is the contract this residual
    # digest carries: it moves for edits the value extraction cannot see.
    # "kec" and "ifc" are here because src/FastKeccak170.sol and
    # src/IMLDSAVerifier.sol are otherwise the two files of src/ that no digest
    # anywhere in the repository covers.
    _C18_FILE_DIGEST = {"dec": "8b9fb8dbc8fcebc64c122063c64e6b5b",
                        "ver": "79223e8482d012223df501e498a4c2d9",
                        "kec": "bee72ebc57e8a1f95d73dd5f69d281af",
                        "ifc": "0f50c68aab1ffdda8412fc89779e9070",
                        "fv2": "12d662de11e4edd03b0b230e01e93e73"}

    # The extracted constant tables outlive the try block: C15b and C17 below
    # state their arithmetic ABOUT THE SHIPPED VALUE, so an unreadable source
    # leaves them empty and those obligations fail rather than proving a fact
    # about a number only this file believes.
    dc, vc, kc, shp = {}, {}, {}, {}
    _hint_prm = None
    _hint_clamp = None
    try:
        dec_code = _strip_sol(_sol(C18_DEC))
        ver_code = _strip_sol(_sol(C18_VER))
        kec_code = _strip_sol(_sol(C18_KEC))
        ifc_code = _strip_sol(_sol(C18_IFC))
        fv2_code = _strip_sol(_sol(C18_FV2))
        dec_n, ver_n = _norm(dec_code), _norm(ver_code)
        kec_n, ifc_n = _norm(kec_code), _norm(ifc_code)
        fv2_n = _norm(fv2_code)
        dec_dig, ver_dig = _fdigest(dec_code), _fdigest(ver_code)
        kec_dig, ifc_dig = _fdigest(kec_code), _fdigest(ifc_code)
        fv2_dig = _fdigest(fv2_code)
        dc, vc = _consts(dec_code), _consts(ver_code)
        kc = _consts(kec_code)
        c18 = []
        for _nm, _want, _why in _C18_DEC_CONSTS:
            c18.append((f"dec_{_nm}_is_{_why.replace(' ', '_')}",
                        _agrees((dc.get(_nm), _want))))
        for _nm, _want, _why in _C18_VER_CONSTS:
            c18.append((f"ver_{_nm}_is_{_why.replace(' ', '_')}",
                        _agrees((vc.get(_nm), _want))))
        for _nm, _want, _why in _C18_KEC_CONSTS:
            c18.append((f"kec_{_nm}_is_{_why.replace(' ', '_')}",
                        _agrees((kc.get(_nm), _want))))
        c18.append(("dec_no_dead_constants_remain",
                    _agrees(([n for n in _C18_DEAD if n in dc], []))))
        c18.append(("ver_no_dead_constants_remain",
                    _agrees(([n for n in _C18_DEAD if n in vc], []))))

        # ---- COMPLETENESS, not a blacklist ---------------------------------
        # The DECLARED set of each shipped check file must be exactly the set
        # modelled above (plus the named, reasoned exemptions), and every
        # declared constant must be READ somewhere other than its own
        # declaration.  Together these close the rename-alias route: adding
        # `MV_KQ28REP2` and moving all six use sites to it now fails
        # `dec_constant_set_is_exactly_the_modelled_set`, and leaving
        # `MV_KQ28REP` behind as a correct-but-unused decoy additionally fails
        # `dec_every_constant_is_read_outside_its_declaration`.
        _mod = {"dec": [n for n, _w, _y in _C18_DEC_CONSTS],
                "ver": [n for n, _w, _y in _C18_VER_CONSTS],
                "kec": [n for n, _w, _y in _C18_KEC_CONSTS]}
        for _tag, _code in (("dec", dec_code), ("ver", ver_code), ("kec", kec_code)):
            _declared = _declared_consts(_code)
            _want = sorted(_mod[_tag] + list(_C18_UNMODELLED[_tag]))
            c18.append((f"{_tag}_constant_set_is_exactly_the_modelled_set",
                        _agrees((_declared, _want))))
            c18.append((f"{_tag}_every_constant_is_read_outside_its_declaration",
                        _agrees((_consts_never_read(_norm(_code), _declared), []))))

        # ---- the z decoder: sites x iterations x lanes x polynomials = 1024 --
        # A SITE COUNT alone never covered "every coefficient is checked"; nor did
        # a pin on the CALL SITE of the per-polynomial driver.  All four factors
        # are extracted, and their product must be the 1024 coefficients of z.
        z_sites = dec_n.count("mstore(0, or(mload(0), and(add(o, Z_NLO), sub(Z_NHI, o))))")
        z_canon = dec_n.count(
            "let o := sub(u, mul(shr(32, and(add(u, Z_QB32), Z_BIT32)), MLDSA_Q))")
        z_trip = _one_num(dec_n, r"for \{ let b := 0 \} lt\(b, (\d+)\)", "z quad loop")
        z_polys = _one_num(dec_n, r"for \(uint256 p = 0; p < (\d+); \+\+p\)", "z driver")
        z_slice = _one_num(dec_n, r"_unpackZPoly\(src \+ (\d+) \* p, dst\)", "z slice")
        z_lanes = _lane_count(dc.get("Z_NLO", 0), (1 << 32) - ZB)
        z_lanes_hi = _lane_count(dc.get("Z_NHI", 0), (1 << 32) + Q - ZB)
        z_verdict = dec_n.count("fail := and(mload(0), Z_BIT32)")
        c18 += [
            ("dec_z_norm_gate_sites_is_4", _agrees((z_sites, 4))),
            ("dec_z_canonicalisation_sites_is_4", _agrees((z_canon, 4))),
            ("dec_z_quad_loop_trip_is_16", _agrees((z_trip, 16))),
            ("dec_z_driver_runs_all_4_polynomials", _agrees((z_polys, L_DIM))),
            ("dec_z_slice_is_the_encoding_width",
             _agrees((z_slice * z_polys, (4 * N * 18) // 8))),
            ("dec_z_gate_is_four_lanes_wide", _agrees(((z_lanes, z_lanes_hi), (4, 4)))),
            ("dec_z_verdict_word_is_read_once", _agrees((z_verdict, 1))),
            ("dec_z_gates_cover_all_1024_coefficients",
             _agrees((z_sites * z_trip * z_lanes * z_polys, L_DIM * N))),
        ]

        # ---- the hint decoder: FIPS 204 Alg. 21's four checks, by VALUE -------
        h_omega = _one_num(dec_n, r"bad := or\(bad, gt\(c3, (\d+)\)\)", "omega check")
        # THE SCAN CLAMP, BOTH OPERANDS.  A pattern that captures the
        # SUBTRAHEND and leaves the `gt` THRESHOLD uncaptured is exactly the
        # asymmetry `h_s1`/`h_s2` exist to refuse.  The
        # verdict does not depend on which of the two moves -- `cut > 80 -> bad`
        # already implies the clamp can only matter on encodings that are
        # rejected anyway -- but the clamp is not there for the verdict: it is
        # there so that the index scan of a REJECTED encoding stays inside the
        # 80-byte index array of an 84-byte object, inside a block annotated
        # `memory-safe`.  That property is a function of the THRESHOLD operand:
        # at `gt(cut, 255)` the scan runs to cut = 255 and
        # reads ~171 bytes past the object.  Both operands are captured here and
        # required to be the same bound; E15 states the memory-safety
        # consequence semantically, over the extracted pair.
        h_clamp = _one_num(dec_n,
                           r"cut := sub\(cut, mul\(sub\(cut, (\d+)\), gt\(cut, (\d+)\)\)\)",
                           "scan clamp")
        h_cw = _one_num(dec_n, r"let cw := mload\(add\(d, (\d+)\)\)", "counter word")
        h_s1 = _one_num(dec_n, r"let s1 := mul\(gt\(c3, (\d+)\), sub\(c3, (\d+)\)\)", "s1")
        h_s2 = _one_num(dec_n, r"let s2 := mul\(gt\(c3, (\d+)\), sub\(c3, (\d+)\)\)", "s2")
        h_w1 = _one_num(dec_n, r"let w1 := mload\(add\(d, (\d+)\)\)", "w1")
        h_w2 = _one_num(dec_n, r"let w2 := shl\((\d+), mload\(add\(d, (\d+)\)\)\)", "w2")
        h_prev = dec_n.count("prevP := add(idx, 1)")
        h_mono = dec_n.count("bad := or(bad, or(or(gt(c0, c1), gt(c1, c2)), gt(c2, c3)))")
        h_strict = dec_n.count("bad := or(bad, lt(idx, prevP))")
        h_pad = dec_n.count("bad := or(bad, iszero(iszero(pad)))")
        _hint_clamp = (h_clamp[0], h_clamp[1])     # (subtrahend, gt threshold)
        _hint_prm = (h_s1[0], h_s1[1], h_s2[0], h_s2[1],
                     h_w2[0], h_w2[1], h_w1, h_cw, h_omega,
                     _hint_clamp[0], _hint_clamp[1])
        c18 += [
            ("dec_h_omega_gate_is_80", _agrees((h_omega, OMEGA))),
            # BOTH operands of the clamp, and they must be the SAME bound
            ("dec_h_scan_clamp_is_80", _agrees((h_clamp, (OMEGA, OMEGA)))),
            ("dec_h_counter_word_is_the_last_32_bytes",
             _agrees((h_cw + 32, OMEGA + L_DIM))),
            # the padding check's SHIFT ARITHMETIC, by value: the two operands of
            # each `mul(gt(c3, G), sub(c3, A))` must be the SAME word boundary,
            # or a padding byte goes unchecked -- that is exactly mutation A.
            ("dec_h_pad_s1_threshold_is_the_w1_boundary", _agrees((h_s1, (32, 32)))),
            ("dec_h_pad_s2_threshold_is_the_w2_boundary", _agrees((h_s2, (64, 64)))),
            ("dec_h_pad_w1_covers_index_bytes_32_63", _agrees((h_w1, 32))),
            ("dec_h_pad_w2_covers_index_bytes_64_79",
             _agrees(((h_w2, h_w2[1] + 32, h_w2[0]),
                      ((128, 48), OMEGA, 8 * (32 - 16))))),
            ("dec_h_pad_word_boundaries_are_the_shift_thresholds",
             _agrees(((h_s1[0], h_s2[0], h_s1[0], h_s2[0]),
                      (h_w1, h_w1 + 32, h_s1[1], h_s2[1])))),
            ("dec_h_strict_increase_gate_present", _agrees(((h_strict, h_prev), (1, 1)))),
            ("dec_h_monotone_counter_gate_present", _agrees((h_mono, 1))),
            ("dec_h_padding_gate_present", _agrees((h_pad, 1))),
        ]

        # ---- the useHint SWAR reduction, by VALUE ---------------------------
        m44_shift = _all_same_num(dec_n, r"shr\((\d+), mul\(S, SW_M44\)\)",
                                  "mod-44 magic shift", 8)
        m44_sub = _all_same_num(
            dec_n, r"mul\(and\(shr\(\d+, mul\(S, SW_M44\)\), SW_REP1\), (\d+)\)",
            "mod-44 subtrahend", 8)
        # ... and the OTHER magic division, `S1 = (W * SW_MDIV) >> 39`, whose
        # SHIFT is easy to leave unextracted: SW_MDIV's value can be pinned
        # against 2^39 in Python while the source's own `shr(39, ...)` is
        # pinned by nothing but the whole-file digest.  Both the constant and
        # the shift it is derived from are read out of the source here.
        sw_shift = _all_same_num(
            dec_n, r"and\(shr\((\d+), mul\(W, SW_MDIV\)\), SW_REP6\)",
            "swar magic-division shift", 8)
        c18 += [
            ("dec_mod44_magic_shift_is_12", _agrees((m44_shift, 12))),
            ("dec_mod44_subtrahend_is_44", _agrees((m44_sub, 44))),
            ("dec_mod44_magic_is_ceil_2pow_shift_over_44",
             _agrees((dc.get("SW_M44"), -((-1 << m44_shift) // 44)))),
            ("dec_swar_magic_shift_is_39", _agrees((sw_shift, 39))),
            ("dec_swar_magic_is_ceil_2pow_shift_over_two_gamma2",
             _agrees((dc.get("SW_MDIV"), -((-1 << sw_shift) // (2 * GAMMA2))))),
        ]
        shp["m44_shift"] = m44_shift

        # ---- the assembled verifier's own checks, by VALUE --------------------
        v_siglen = _one_num(ver_n, r"if \(sig\.length != (\d+)\) return false;",
                            "sig length")
        v_weight = _one_num(ver_n, r"if \(!hOk \|\| hWeight > (\d+)\) return false;",
                            "hint weight")
        v_mu = _one_num(ver_n, r"new bytes\((\d+) \+ message\.length\)", "mu preimage")
        v_tr = _one_num(ver_n, r"extcodecopy\(pkPtr, d, (\d+), (\d+)\)", "tr read")
        v_size_gate = ver_n.count("if eq(extcodesize(pkPtr), add(PK_SIZE, 1))")
        v_codehash = ver_n.count("!= F1600_CODEHASH) revert BadHelper();")
        v_iface = ver_n.count("contract MLDSA44Verifier is IMLDSAVerifier {")
        v_entry = ver_n.count("function verify(address pkBlob, bytes calldata message, "
                              "bytes calldata signature) external view returns (bool)")
        c18 += [
            ("ver_signature_length_is_2420",
             _agrees((v_siglen, 32 + (4 * N * 18) // 8 + (OMEGA + L_DIM)))),
            ("ver_hint_weight_bound_is_omega", _agrees((v_weight, OMEGA))),
            ("ver_mu_preimage_is_66_plus_message", _agrees((v_mu, 64 + 2))),
            ("ver_tr_is_64_bytes_at_code_offset_1", _agrees((v_tr, (1, 64)))),
            ("ver_pk_size_gate_is_exact", _agrees((v_size_gate, 1))),
            ("ver_helper_is_pinned_at_construction_and_per_call",
             _agrees((v_codehash, 2))),
            # ... and the check's CONSTANT is the width C15b proves, which is the
            # half `pat="if eq(extcodesize(pkPtr), add(PK_SIZE, 1))"` never saw
            ("ver_pk_size_gate_constant_is_the_proved_width",
             _agrees(((v_size_gate, vc.get("PK_SIZE")),
                      (1, 64 + 4 * N * 4 + 16 * N * 4)))),
            # the entry point is the PINNED INTERFACE's, and it is `view`: the
            # SAFETY.md claim "safe to call via STATICCALL" is a property of that
            # mutability keyword and of nothing else in the file
            ("ver_implements_the_pinned_interface", _agrees(((v_iface, v_entry), (1, 1)))),
        ]

        # ---- src/FastKeccak170.sol: FIPS 202's padding and the sponge rate ---
        # Every number the sponge is made of
        # is read out of the shipped file and compared against the protocol, not
        # restated: the domain byte, the final bit and the word it lands in, the
        # rate at every site that uses it, the 800-byte raw-permutation protocol
        # on BOTH sides of the staticcall, both fail-closed `returndatasize()`
        # checks, the batched path's two guards, and the round-up mask of the RAW
        # (deliberately non-zero-filled) return buffer.
        k_dom = _one_num(kec_n, r"mstore8\(add\(dst, rem\), (0x[0-9a-fA-F]+)\)",
                         "SHAKE domain byte")
        k_fin = _one_num(kec_n,
                         r"mstore\(add\(dst, (\d+)\), xor\(mload\(add\(dst, (\d+)\)\), "
                         r"(0x[0-9a-fA-F]+)\)\)", "final pad bit")
        k_rate = _all_same_num(
            kec_n,
            r"(?:len / |nFull \* |ptr \+= |new bytes\(|nOut \* |done \+= )(\d+)",
            "the sponge rate", 6)
        k_ceil = _one_num(kec_n, r"\(outLen \+ (\d+)\) / (\d+)", "squeeze block count")
        k_perm = _one_num(kec_n,
                          r"ok := staticcall\(gas\(\), helper, st, (\d+), st, (\d+)\) "
                          r"ok := and\(ok, eq\(returndatasize\(\), (\d+)\)\)",
                          "raw permutation call and its check")
        k_batch = _one_num(kec_n,
                           r"add\(output, 32\), outLen\) ok := and\(ok, "
                           r"eq\(returndatasize\(\), (\d+)\)\)",
                           "batched sponge check")
        k_out_gate = _one_num(kec_n, r"require\(outLen <= (\d+),", "batched outLen check")
        k_len_guard = _one_num(kec_n, r"require\(input\.length != (\d+),",
                               "batched length guard")
        k_alloc = _one_num(kec_n, r"and\(add\(outLen, (\d+)\), not\((\d+)\)\)",
                           "raw output buffer round-up")
        k_absorb16 = _one_num(kec_n,
                              r"v := grev\(mload\(add\(ptr, (\d+)\)\)\) mstore\(add\(st, 512\)",
                              "absorb lane-16 window")
        k_squeeze16 = _one_num(kec_n,
                               r"mstore\( add\(outPtr, (\d+)\), grev\( or\( or\(or\("
                               r"shl\(192, mload\(add\(st, 416\)\)\)",
                               "squeeze lane-16 window")
        c18 += [
            ("kec_domain_pad_byte_is_the_shake_0x1f", _agrees((k_dom, 0x1F))),
            ("kec_final_pad_bit_is_0x80_in_the_last_word_of_the_rate_block",
             _agrees(((k_fin, k_fin[0] + 32), ((104, 104, 0x80), k_rate)))),
            ("kec_sponge_rate_is_136_at_every_site", _agrees((k_rate, 136))),
            ("kec_squeeze_block_count_rounds_up_by_the_rate",
             _agrees((k_ceil, (k_rate - 1, k_rate)))),
            ("kec_raw_permutation_is_800_bytes_in_and_out",
             _agrees((k_perm[:2], (25 * 32, 25 * 32)))),
            ("kec_raw_permutation_gate_is_returndatasize_800",
             _agrees((k_perm[2], 25 * 32))),
            ("kec_batched_sponge_gate_is_returndatasize_136",
             _agrees((k_batch, k_rate))),
            ("kec_batched_outlen_gate_is_one_rate_block", _agrees((k_out_gate, k_rate))),
            ("kec_batched_path_refuses_the_800_byte_dispatch_collision",
             _agrees((k_len_guard, k_perm[0]))),
            ("kec_raw_output_buffer_is_rounded_up_to_a_whole_word",
             _agrees((k_alloc, (31, 31)))),
            ("kec_lane16_windows_end_flush_with_the_rate_block",
             _agrees(((k_absorb16 + 32, k_squeeze16 + 32), (k_rate, k_rate)))),
        ]

        # ---- src/IMLDSAVerifier.sol: the external ABI the deployment is -------
        i_iface = ifc_n.count("interface IMLDSAVerifier {")
        i_entry = ifc_n.count("function verify(address pkBlob, bytes calldata message, "
                              "bytes calldata signature) external view returns "
                              "(bool accepted);")
        c18 += [
            ("ifc_declares_exactly_the_external_view_verify_entry_point",
             _agrees(((i_iface, i_entry), (1, 1)))),
        ]

        # ---- FV2_Barrett.sol: the harness section 5.7's "Closed" rests on ----
        # Its three shipped-kernel copies must be present and its own `check_*`
        # census must be the one section 5.7 and RESULTS.md describe.  The
        # SEMANTICS of those copies -- that they equal `src/Ntt.sol::lazyBarrett`
        # -- is a forge fuzz test, deliberately, because that is the check a
        # solver-free CI can actually run.
        # 22 `check_*` (15 obligations + 7 canaries) -- exactly the row count of
        # formal/mutation/halmos_fv2.json -- and ZERO `test*`: the file
        # contributes no forge test of its own, which is precisely WHY the
        # shipped-kernel identity has to be asserted from FV_Kernels.t.sol.
        fv2_checks = len(re.findall(r"function check_\w+\(", fv2_n))
        fv2_tests = len(re.findall(r"function test\w*\(", fv2_n))
        fv2_scalar = fv2_n.count(
            "r := sub(x, mul(shr(33, mul(x, MU33)), Q)) r := sub(r, mul(shr(23, r), Q))")
        fv2_swar = fv2_n.count(
            "t0 := sub(t0, mul(and(shr(33, mul(t0, MU33)), QHATM31), Q)) "
            "t0 := sub(t0, mul(and(shr(23, t0), QHATM31), Q))")
        c18 += [
            ("fv2_declares_the_pinned_check_census",
             _agrees(((fv2_checks, fv2_tests), (22, 0)))),
            ("fv2_carries_the_shipped_scalar_two_step_kernel", _agrees((fv2_scalar, 1))),
            ("fv2_carries_the_shipped_packed_two_step_kernel", _agrees((fv2_swar, 1))),
        ]

        # ---- the residual: the whole normalised file, all five of them -------
        c18 += [
            ("dec_shipped_source_is_the_pinned_bytes",
             _agrees((dec_dig, _C18_FILE_DIGEST["dec"]))),
            ("ver_shipped_source_is_the_pinned_bytes",
             _agrees((ver_dig, _C18_FILE_DIGEST["ver"]))),
            ("kec_shipped_source_is_the_pinned_bytes",
             _agrees((kec_dig, _C18_FILE_DIGEST["kec"]))),
            ("ifc_shipped_source_is_the_pinned_bytes",
             _agrees((ifc_dig, _C18_FILE_DIGEST["ifc"]))),
            ("fv2_refinement_harness_is_the_pinned_bytes",
             _agrees((fv2_dig, _C18_FILE_DIGEST["fv2"]))),
        ]
        # THE DISCRIMINATION CONTROL for the whole "extracted == proved" method.
        # Every substantive conjunct above routes its comparison through
        # `_agrees`, so these seven rows are a control OVER THOSE CONJUNCTS and
        # not merely over a helper nothing calls:
        # `_agrees` rewritten to a tautology fails the four rejects, and
        # `_agrees` rewritten to a contradiction fails the three accepts AND
        # every conjunct it is supposed to protect.
        c18 += controls(_agrees, label="ctl_extracted_value_is_the_proved_value",
                        accept=[(20544, 20544), (94, 94), (4, 4)],
                        reject=[(20000, 20544), (20545, 20544), (93, 94), (3, 4)])
        c18_detail = (f"{len(c18)} extracted values/shapes/controls cross-checked "
                      f"against 4 shipped sources + the FV2 refinement harness; "
                      f"observed file digests dec={dec_dig} ver={ver_dig} "
                      f"kec={kec_dig} ifc={ifc_dig} fv2={fv2_dig}")
    except Exception as exc:                       # never a silent skip -- fail loud
        c18 = [("source_readable", False)]
        c18_detail = f"CANNOT READ THE SHIPPED CHECK SOURCE: {exc!r} (set MLDSA_REPO)"
    ok &= record("C18", "EXH",
                 "the shipped sources (Decode.sol, MLDSA44Verifier.sol, "
                 "FastKeccak170.sol, IMLDSAVerifier.sol) and the FV2 refinement "
                 "harness are the pinned artefact, VALUE by VALUE",
                 True, c18_detail, parts=c18)

    # ---------------------------------------------------------------------- E15
    # THE HINT PADDING CHECK, SEMANTICALLY.
    #
    # A digest tells you something changed; a test tells you what broke.  FIPS
    # 204 Algorithm 21 lines 16-18 require every UNUSED index byte to be zero,
    # and the shipped decoder discharges that branchlessly over three
    # 32/32/16-byte words -- so its correctness is a claim about SHIFT
    # ARITHMETIC at the two word boundaries c3 = 32 and c3 = 64.  No test,
    # mutant or obligation reached the c3 >= 64 branch, and a one-token edit
    # there is a strong-unforgeability break: a SECOND distinct 2,420-byte
    # signature verifying for one (pk, message), with hint weight >= 64 common
    # enough to hit on the second signature generated.
    #
    # This enumerates the COMPLETE reachable grid -- every total weight
    # c3 in [0, omega] x every dirty padding position p in [c3, 80) -- against a
    # model of the shipped Yul at EVM semantics whose parameters are EXTRACTED
    # FROM THE SOURCE (C18's `_hint_prm`), never restated here.  81 canonical
    # encodings must be ACCEPTED and 3,240 dirty ones REJECTED; the reject
    # controls are the mutations that survive every other check in the tree.
    # test/SEC3_HintPaddingGrid.t.sol runs the same grid ON CHAIN against
    # the shipped `unpackHFast`, so the model and the artefact are checked apart.
    _M256 = (1 << 256) - 1

    def _evm_shl(n, x):
        return 0 if n >= 256 else (x << n) & _M256

    def _scan_stays_inside_the_index_array(clamp):
        """MEMORY SAFETY of `unpackHFast`'s index scan, stated as a function
        of BOTH operands of the shipped clamp
        `cut := sub(cut, mul(sub(cut, A), gt(cut, G)))`.

        `cut` is a byte lifted out of the counter word, so its domain is the
        WHOLE of [0, 255] -- the omega check sets `bad`, it does not stop the
        scan.  The clamped value is the EXCLUSIVE end of `for j in [k, cut)`,
        which indexes the 80-byte index array of an 84-byte object inside a
        block annotated `memory-safe`.  So the requirement is that the clamp
        maps every byte to at most OMEGA.  It is a claim about the pair: at
        `A = 80, G = 255` the clamp never fires and the scan runs to 255; at
        `A = 255, G = 80` it fires and RAISES cut to 255.  Stated over the whole
        byte domain rather than over the grid, because the grid's counters are
        all <= OMEGA and can therefore never exhibit the defect (a conjunct
        quantified below its own counterexample is the failure mode this
        apparatus refuses).
        """
        a, g = clamp
        hi = 0
        for c in range(256):
            cut = (c - ((c - a) & _M256) * (1 if c > g else 0)) & _M256
            hi = max(hi, cut)
        return hi <= OMEGA

    def _hint_gate_accepts(region, prm):
        """`unpackHFast`'s validity verdict at EVM semantics for one 84-byte
        region, with the padding check's numbers taken as parameters."""
        g1, a1, g2, a2, wsh, woff, w1off, cwoff, omega, csub, cgt = prm
        mem = bytes(region) + bytes(64)        # memory past the object reads 0 here
        w0 = int.from_bytes(mem[0:32], "big")
        w1 = int.from_bytes(mem[w1off:w1off + 32], "big")
        w2 = _evm_shl(wsh, int.from_bytes(mem[woff:woff + 32], "big"))
        cw = mem[cwoff:cwoff + 32]
        c = (cw[28], cw[29], cw[30], cw[31])
        bad = c[0] > c[1] or c[1] > c[2] or c[2] > c[3] or c[3] > omega
        s1 = ((1 if c[3] > g1 else 0) * ((c[3] - a1) & _M256)) & _M256
        s2 = ((1 if c[3] > g2 else 0) * ((c[3] - a2) & _M256)) & _M256
        pad = (_evm_shl((c[3] * 8) & _M256, w0)
               | _evm_shl((s1 * 8) & _M256, w1)
               | _evm_shl((s2 * 8) & _M256, w2))
        bad = bad or pad != 0
        k = 0
        for i in range(4):
            cut = c[i]
            # the shipped clamp, at EVM semantics, with BOTH operands taken from
            # the source (restating the `gt` threshold here as OMEGA, rather
            # than reading it, would hide a threshold that moved)
            cut = (cut - ((cut - csub) & _M256) * (1 if cut > cgt else 0)) & _M256
            prev = 0
            for j in range(k, cut):
                idx = mem[j]
                bad = bad or idx < prev
                prev = idx + 1
            k = cut
        return not bad

    def _hint_padding_grid_ok(prm):
        """Every canonical encoding ACCEPTED, every dirty-padding one REJECTED."""
        for c3 in range(OMEGA + 1):
            clean = bytearray(OMEGA + L_DIM)
            for j in range(c3):
                clean[j] = j                   # strictly increasing, all in row 0
            for i in range(L_DIM):
                clean[OMEGA + i] = c3          # all four cut counters at the weight
            if not _hint_gate_accepts(clean, prm):
                return False                   # a canonical encoding was REJECTED
            for p in range(c3, OMEGA):
                dirty = bytearray(clean)
                dirty[p] = 0xFF
                if _hint_gate_accepts(dirty, prm):
                    return False               # dirty padding was ACCEPTED
        return True

    if _hint_prm is None:
        ok &= record("E15", "EXH",
                     "the shipped hint padding check accepts exactly the canonical "
                     "encodings (complete weight x dirty-position grid)",
                     False,
                     "CANNOT READ src/Decode.sol — the check's parameters are "
                     "extracted from it, never restated here",
                     parts=[("source_readable", False)])
    else:
        _n_rej = sum(OMEGA - c3 for c3 in range(OMEGA + 1))
        (_g1, _a1, _g2, _a2, _wsh, _woff, _w1off, _cwoff, _om,
         _csub, _cgt) = _hint_prm
        _cl = (_csub, _cgt)
        ok &= pinned(
            "E15", "EXH",
            "the shipped hint padding check accepts exactly the canonical encodings "
            "(complete weight x dirty-position grid, parameters read from the source)",
            _hint_padding_grid_ok, _hint_prm,
            f"{OMEGA + 1} canonical acceptances + {_n_rej} rejections at EVM "
            f"semantics; parameters s1=(gt {_g1}, sub {_a1}) s2=(gt {_g2}, sub {_a2}) "
            f"w2=shl({_wsh}, mload(d+{_woff})) clamp=(sub {_csub}, gt {_cgt})",
            accept=[_hint_prm],
            # the one-token defect and its neighbours, every one of which
            # survives the forge corpus, every obligation and hypothesis row.
            # NOTE what is deliberately NOT here: a variation of the scan clamp.
            # Every counter in this grid is <= OMEGA, so the clamp never fires
            # and NO clamp parameterisation changes a verdict on it -- a reject
            # control over the clamp would be a control that cannot come out
            # false.  The clamp's own property is MEMORY SAFETY, not the
            # verdict, and it is stated over the whole byte domain by
            # `scan_clamp_keeps_the_index_scan_inside_the_index_array` below,
            # over the whole [0, 255] domain of a counter byte.
            reject=[(_g1, _a1, 63, 63, _wsh, _woff, _w1off, _cwoff, _om, *_cl),   # weights 64-79 malleable
                    (_g1, _a1, _g2, 63, _wsh, _woff, _w1off, _cwoff, _om, *_cl),  # weights 65-79 malleable
                    (_g1, _a1, 65, 65, _wsh, _woff, _w1off, _cwoff, _om, *_cl),   # weight 65 falsely rejected
                    (31, 31, _g2, _a2, _wsh, _woff, _w1off, _cwoff, _om, *_cl),   # weights 32-63 malleable
                    (_g1, 31, _g2, _a2, _wsh, _woff, _w1off, _cwoff, _om, *_cl),  # ditto, sub only
                    (33, 33, _g2, _a2, _wsh, _woff, _w1off, _cwoff, _om, *_cl),   # weight 33 falsely rejected
                    (_g1, _a1, _g2, _a2, _wsh, 47, _w1off, _cwoff, _om, *_cl),    # index byte 79 uncovered
                    (_g1, _a1, _g2, _a2, 120, _woff, _w1off, _cwoff, _om, *_cl),  # w2 window slid by a byte
                    (_g1, _a1, _g2, _a2, _wsh, _woff, _w1off + 1, _cwoff, _om, *_cl),  # w1 window slid
                    (_g1, _a1, _g2, _a2, _wsh, _woff, _w1off, _cwoff + 1, _om, *_cl)],  # counters misread
            parts=[("canonical_weight_zero_accepted",
                    _hint_gate_accepts(bytearray(OMEGA + L_DIM), _hint_prm)),
                   ("grid_reaches_the_second_word_boundary", OMEGA > 64),
                   # the clamp's MEMORY-SAFETY property, over the extracted pair
                   ("scan_clamp_keeps_the_index_scan_inside_the_index_array",
                    _scan_stays_inside_the_index_array(_hint_clamp))]
                  + controls(_scan_stays_inside_the_index_array,
                             label="ctl_scan_clamp",
                             # the shipped pair, and the one neighbour that is
                             # still safe -- so the control is not simply a
                             # restatement of the subject
                             accept=[(OMEGA, OMEGA), (OMEGA, OMEGA - 1)],
                             # the two one-operand defects and the off-by-one
                             reject=[(OMEGA, 255), (255, OMEGA),
                                     (OMEGA + 1, OMEGA + 1)]))

    # C10: SampleInBall rejection-loop tail — EXACT, by dynamic programming over
    # integers.  "The per-draw reject probability is < 0.16" is a DIFFERENT
    # quantity from the one SAFETY.md §5 quotes, and not a substitute for it.
    #   FIPS 204 Alg. 29: 8 sign bytes are consumed first, then tau = 39 rejection
    #   draws; draw i (i = 256-tau .. 255) accepts a byte j iff j <= i, i.e. with
    #   probability (i+1)/256.  One SHAKE256 rate block is 136 bytes, so a SECOND
    #   permutation is needed iff the 39 draws consume more than 136 - 8 = 128 bytes.
    BUDGET = 136 - 8
    # w[n] = integer weight of consuming exactly n bytes (probability = w[n]/256^n)
    w = [0] * (BUDGET + 1); w[0] = 1
    for i in range(256 - TAU, 256):
        acc_i, rej_i = i + 1, 255 - i
        nw = [0] * (BUDGET + 1)
        for n, wn in enumerate(w):
            if not wn:
                continue
            # g >= 1 rejections-then-accept costs g bytes
            for g in range(1, BUDGET - n + 1):
                nw[n + g] += wn * pow(rej_i, g - 1) * acc_i
        w = nw
    num = sum(w[n] * pow(256, BUDGET - n) for n in range(BUDGET + 1))
    den = pow(256, BUDGET)
    p_second = (den - num) / den                       # exact rational -> float
    import math as _m
    # Compute the detail DEFENSIVELY.  A failing obligation must still
    # report: a mutation that makes `num > den` would otherwise crash the whole
    # suite here (log2 of a non-positive number).  A run that
    # produces no verdict is a hole in the audit, not evidence about the suite.
    _lg = f"2^{_m.log2(p_second):.1f}" if p_second > 0 else "not a probability"
    ok &= pinned("C10", "CALC",
                 "SampleInBall: exact P(a 2nd Keccak permutation is needed)",
                 lambda p: p < 2.0 ** -200, p_second,
                 f"= {p_second:.3e} = {_lg} (exact DP, tau={TAU}, budget={BUDGET}B)",
                 accept=[0.0, 2.0 ** -201, 2.0 ** -1000],
                 reject=[2.0 ** -200, 2.0 ** -199, 2.0 ** -60, 1.0],
                 parts=[("dp_is_proper", den > num), ("tail_lt_2^-200", p_second < 2.0 ** -200)])

    # C10b: expected number of rejection bytes (the SAFETY.md §5 figure)
    exp_bytes = sum(256 / (i + 1) for i in range(256 - TAU, 256))
    ok &= pinned("C10b", "CALC", "SampleInBall: expected rejection bytes consumed",
                 lambda e: 39 <= e < 64, exp_bytes,
                 f"E[bytes] = {exp_bytes:.2f} (>= tau = {TAU})",
                 accept=[39.0, 40.0, 63.999], reject=[38.999, 0.0, 64.0, 64.001, 1e9],
                 parts=[("ge_tau", TAU <= exp_bytes), ("lt_64", exp_bytes < 64)])

    # C15: the deployed wire widths are exactly the widths the layout comments
    # and the pk-blob reader assume.
    # Proving the width arithmetic in PYTHON and stopping there is not enough:
    # `PK_SIZE 20544 -> 20000` in
    # the shipped verifier leaves such a proof green -- the arithmetic is about
    # a number the apparatus believes, not the number the contract uses.  The
    # width is computed here AND the linkage conjunct compares it against the
    # value C18 EXTRACTED from src/MLDSA44Verifier.sol.
    ok &= pinned("C15b", "CALC", "pk blob widths: 64 + 4*256*4 + 16*256*4 == 20544",
                 lambda w: w == 20544, 64 + 4 * N * 4 + 16 * N * 4, "tr | t1hat | Ahat",
                 accept=[20544], reject=[20543, 20545, 0],
                 parts=[("shipped_PK_SIZE_is_this_width",
                         vc.get("PK_SIZE") == 64 + 4 * N * 4 + 16 * N * 4),
                        ("shipped_PK_T1_OFF_is_after_tr", vc.get("PK_T1_OFF") == 64),
                        ("shipped_PK_A_OFF_is_after_t1hat",
                         vc.get("PK_A_OFF") == 64 + 4 * N * 4)])
    ok &= pinned("C15c", "CALC", "sigma widths: 32 + 4*256*18/8 + (80+4) == 2420",
                 lambda w: w == 2420, 32 + (4 * N * 18) // 8 + (OMEGA + L_DIM), "c~ | z | h",
                 accept=[2420], reject=[2419, 2421, 0])

    # C17: the SWAR mod-44 reduction of useHintSwar (src/Decode.sol).  The
    # kernel folds FIPS 204's two reductions into ONE, on the grounds that
    # (S1 mod 44 + ADJ) mod 44 == (S1 + ADJ) mod 44, and evaluates the single
    # `mod 44` with a magic-number division: OUT = T - 44*((T*94) >> 12) with
    # T = S1 + ADJ.  Two things have to hold and both are enumerated COMPLETELY:
    # the identity (T*94)>>12 == floor(T/44) on the whole REACHABLE range of T,
    # and the reachability bound itself (S1 <= 44 because q0 == 44 forces
    # r0 == 0 hence c == 0 -- S11/S11b -- and ADJ <= 43).  The claim is stated
    # as "the FIRST T at which the magic division is wrong lies strictly above
    # the reachable maximum", so a widened T, a re-tuned magic constant or a
    # re-tuned shift all falsify it rather than shrinking a margin silently.
    # The magic constant and its
    # shift are READ FROM THE SHIPPED SOURCE.  Restated in Python they are only
    # a fact about a number this file believes: `SW_M44 94 -> 93` in Decode.sol
    # leaves C17 green while the mod-44 division becomes wrong for every
    # reachable T >= 44.  If the source is unreadable, `dc` is empty and the
    # fallback -1 makes the claim FAIL rather than proving the wrong number.
    SW_M44 = dc.get("SW_M44", -1)
    SW_M44_SHIFT = shp.get("m44_shift", 0)
    T_MAX = 44 + 43                                  # max S1 + max ADJ
    m44_first_bad = next(t_ for t_ in range(1 << 20)
                         if (t_ * SW_M44 >> SW_M44_SHIFT) != t_ // 44)
    ok &= pinned("C17", "CALC",
                 "useHintSwar: ONE mod-44 reduction — (T*94)>>12 == floor(T/44) "
                 "for every reachable T",
                 lambda first_bad: first_bad > T_MAX, m44_first_bad,
                 f"exact for every T < {m44_first_bad}; reachable max T = {T_MAX} "
                 f"= 44 + 43 (margin {m44_first_bad - T_MAX})",
                 accept=[T_MAX + 1, 131, 1 << 20],
                 reject=[T_MAX, T_MAX - 1, 44, 0],
                 # NOTE the range here is the REACHABLE one, not [0, first_bad):
                 # `first_bad` is by construction the first counterexample, so a
                 # conjunct quantified below it would be a tautology and the
                 # vacuity audit would (rightly) report it as never-killable.
                 parts=[("exact_on_every_reachable_T",
                         all((t_ * SW_M44 >> SW_M44_SHIFT) == t_ // 44
                             for t_ in range(T_MAX + 1))),
                        ("magic_is_ceil_2pow12_over_44",
                         SW_M44 == -((-1 << SW_M44_SHIFT) // 44)),
                        ("reachable_T_max_is_87", T_MAX == 87),
                        # the lane product must not carry into the next 64-bit
                        # SWAR lane, and the quotient must fit the REP1 mask
                        ("lane_product_lt_2p64", T_MAX * SW_M44 < (1 << 64)),
                        ("quotient_fits_the_rep1_mask",
                         all((t_ * SW_M44 >> SW_M44_SHIFT) <= 1
                             for t_ in range(T_MAX + 1))),
                        # ... and the algebraic step that made one reduction
                        # enough: reducing S1 first cannot change the result
                        ("folding_the_two_reductions_is_exact",
                         all(((s1 % 44) + adj) % 44 == (s1 + adj) % 44
                             for s1 in range(45) for adj in (0, 1, 43)))])
    return ok


# ================================================================ EXH obligations
def exh_obligations():
    ok = True
    # Every enumeration below is a DETECTOR PARAMETERISED
    # OVER THE KERNEL, and each obligation carries a negative control: the same
    # detector, run against a deliberately broken kernel, must report a
    # counterexample.  Without them, `bad == 0` rewritten to `True` (or a sweep
    # whose loop body stops comparing) is a silent green PASS.  The controls
    # cost microseconds because a broken kernel fails on the first few inputs.
    #
    # E1: UseHint over the COMPLETE domain [0,Q) x {0,1}
    # E2 is folded into the same sweep so that the output-range claim is also
    # COMPLETE: a stride-7 sample of the same domain would not be a proof.
    def usehint_sweep(kern, limit=Q):
        """(equality_ok, range_ok) over [0,limit) x {0,1}, breaking on the first
        counterexample.  The RANGE test must precede the equality break,
        otherwise an out-of-range output is masked by the equality mismatch it
        also causes and E2's conjunct can never be falsified."""
        for rv in range(limit):
            k0, k1 = kern(0, rv), kern(1, rv)
            if not (0 <= k0 < 44 and 0 <= k1 < 44):
                return True, False
            if k0 != ref_use_hint(0, rv) % 44 or k1 != ref_use_hint(1, rv) % 44:
                return False, True
        return True, True

    def usehint_equals_fips(kern):
        return usehint_sweep(kern)[0]

    def usehint_output_in_range(kern):
        return usehint_sweep(kern)[1]

    t0 = time.time()
    e1_eq, e1_rng = usehint_sweep(kern_use_hint)
    ok &= record("E1", "EXH", f"UseHint == FIPS reference on all {Q} x 2 inputs",
                 usehint_equals_fips(kern_use_hint), f"{time.time()-t0:.1f}s",
                 parts=controls(usehint_equals_fips, label="ctl_eq",
                                reject=[lambda h, rv: (kern_use_hint(h, rv) + 1) % 44,
                                        lambda h, rv: kern_use_hint(0, rv)]))
    ok &= record("E2", "EXH", "UseHint output in [0,44) on the COMPLETE domain (6-bit packing)",
                 True, "full sweep, no stride",
                 parts=[("output_in_0_44", usehint_output_in_range(kern_use_hint)),
                        ("sweep_ran_to_completion", e1_eq)]
                 + controls(usehint_output_in_range, label="ctl_range",
                            accept=[kern_use_hint],
                            reject=[lambda h, rv: kern_use_hint(h, rv) + 44,
                                    lambda h, rv: -1]))

    # E3: z centered map over the COMPLETE 18-bit field domain
    def zmap_agrees(kern):
        return not [v for v in range(1 << 18) if kern(v) != ref_z_centered(v)]
    ok &= pinned("E3", "EXH", "z centered map == FIPS BitUnpack on all 2^18 fields",
                 zmap_agrees, kern_z_centered_strict, f"checked {1<<18}",
                 reject=[lambda v: (kern_z_centered_strict(v) + 1) % Q,
                         lambda v: (GAMMA1 - v) % (Q + 1),
                         lambda v: 0])

    # E4: strict norm test equivalence over the COMPLETE domain
    def normflag_agrees(kern):
        return not [v for v in range(1 << 18) if kern(v) != (not ref_z_norm_ok(v))]
    ok &= pinned("E4", "EXH", "branchless norm test == strict FIPS ||z||<G1-B on all 2^18",
                 normflag_agrees, kern_z_norm_flag,
                 f"boundary: v={BETA} rejected, v={BETA+1} accepted",
                 reject=[lambda v: not (((v - BETA) % (1 << 256)) < 2 * GAMMA1 - 2 * BETA - 1),
                         lambda v: not (((v - (BETA + 1)) % (1 << 256)) < 2 * GAMMA1 - 2 * BETA),
                         lambda v: False, lambda v: True])

    # E5: the boundary itself (regression against the SOTA off-by-one)
    b_rej = kern_z_norm_flag(BETA)            # |z| = GAMMA1 - BETA  -> must reject
    b_acc = not kern_z_norm_flag(BETA + 1)    # |z| = GAMMA1 - BETA - 1 -> must accept
    ok &= record("E5", "EXH", "norm boundary: |z|=G1-B rejected, G1-B-1 accepted",
                 True, parts=[("boundary_rejected", b_rej), ("just_inside_accepted", b_acc)])

    # E6: z=0 canonicalization (the q-vs-0 hazard)
    ok &= pinned("E6", "EXH", "z=0 field (v=GAMMA1) canonicalizes to 0, not Q",
                 lambda v: kern_z_centered_strict(v) == 0, GAMMA1, "",
                 accept=[GAMMA1, GAMMA1 + Q], reject=[0, 1, GAMMA1 - 1, GAMMA1 + 1, Q])

    # ---- the SHIPPED PACKED decoder (src/Decode.sol _unpackZPoly) ----------
    # E3/E4/E5/E6 above are about the per-coefficient form, which the REFERENCE
    # decoder (test/ZZZ_E2ERef.sol) still carries and which is therefore still
    # the differential oracle.  The shipped kernel evaluates the same two
    # functions FOUR LANES AT A TIME with carry/borrow flags instead of `mod`
    # and `lt`, so its one-lane projection gets its own complete sweep here and
    # its four-lane word arithmetic gets S8b.
    def canon_swar_agrees(kern):
        return not [v for v in range(1 << 18) if kern(v) != ref_z_centered(v)]
    ok &= pinned("E3b", "EXH",
                 "SWAR conditional subtract == FIPS BitUnpack centered map on all 2^18 fields",
                 canon_swar_agrees, kern_z_canon_swar, f"checked {1<<18}",
                 parts=[("z_zero_field_canonicalises_to_zero",
                         kern_z_canon_swar(GAMMA1) == 0),
                        ("every_output_canonical",
                         all(0 <= kern_z_canon_swar(v) < Q for v in range(1 << 18)))],
                 accept=[kern_z_centered_strict],
                 # the flag taken STRICTLY (`u > q`) leaves v = GAMMA1 at q --
                 # the exact SOTA defect of EXPLAINER 10 -- and a flag read one
                 # bit off, or dropped, leaves a non-canonical lane
                 reject=[lambda v: (Z_UOFF_LANE - v) - Q * (1 if Z_UOFF_LANE - v > Q else 0),
                         lambda v: (Z_UOFF_LANE - v) - Q * ((((Z_UOFF_LANE - v) + Z_QB32_LANE) >> 31) & 1),
                         lambda v: Z_UOFF_LANE - v,
                         lambda v: (kern_z_canon_swar(v) + 1) % Q])

    # E4b: the packed check's predicate, over the COMPLETE domain, in BOTH
    # directions.  The two window edges are separate CONSTANTS here (they were
    # one comparison in the per-coefficient form), so each is moved on its own.
    def normflag_packed_agrees(kern):
        return not [v for v in range(1 << 18) if kern(v) != (not ref_z_norm_ok(v))]
    ok &= pinned("E4b", "EXH",
                 "packed bit-32 norm check == strict FIPS ||z||<G1-B on all 2^18",
                 normflag_packed_agrees, kern_z_norm_flag_packed,
                 f"reject window [{GAMMA1 - BETA}, {Q - (GAMMA1 - BETA)}] on the STORED lane",
                 reject=[  # low edge relaxed by one: accepts |z| == gamma1-beta
                         lambda v: kern_z_norm_flag_packed(v, nlo=Z_NLO_LANE - 1),
                         # high edge relaxed by one: accepts z == -(gamma1-beta)
                         lambda v: kern_z_norm_flag_packed(v, nhi=Z_NHI_LANE + 1),
                         # low edge tightened by one: rejects a legal coefficient
                         lambda v: kern_z_norm_flag_packed(v, nlo=Z_NLO_LANE + 1),
                         # high edge tightened by one
                         lambda v: kern_z_norm_flag_packed(v, nhi=Z_NHI_LANE - 1),
                         lambda v: False, lambda v: True])

    # E5b: the boundary of the packed check, BOTH directions.  E5 pins the low
    # tail (v = BETA); the packed check reaches the high tail through a DIFFERENT
    # constant (Z_NHI, and a `sub` rather than an `add`), so the high tail is a
    # genuinely separate claim and not a symmetry of the low one.
    ok &= record("E5b", "EXH",
                 "packed check boundary: |z| = G1-B rejected and G1-B-1 accepted, on BOTH tails",
                 True,
                 f"v in {{{BETA}, {BETA+1}, {2*GAMMA1-BETA}, {2*GAMMA1-BETA-1}}}",
                 parts=[("low_tail_boundary_rejected", kern_z_norm_flag_packed(BETA)),
                        ("low_tail_just_inside_accepted", not kern_z_norm_flag_packed(BETA + 1)),
                        ("high_tail_boundary_rejected", kern_z_norm_flag_packed(2 * GAMMA1 - BETA)),
                        ("high_tail_just_inside_accepted",
                         not kern_z_norm_flag_packed(2 * GAMMA1 - BETA - 1)),
                        # ... and the four probes really are the two boundaries:
                        # the FIPS reference must straddle at exactly these
                        # fields, or the four claims above are about the wrong
                        # points and prove nothing about the bound.
                        ("probes_straddle_the_bound_in_fips",
                         not ref_z_norm_ok(BETA) and not ref_z_norm_ok(2 * GAMMA1 - BETA)
                         and ref_z_norm_ok(BETA + 1) and ref_z_norm_ok(2 * GAMMA1 - BETA - 1))])

    # E12: HINT-ENCODING CANONICALITY (the classic Dilithium malleability bug class).
    # FIPS 204 Alg. 21 HintBitUnpack must accept EXACTLY ONE byte string per hint
    # set: indices strictly increasing inside each polynomial, cut positions
    # non-decreasing and <= omega, and every trailing index byte zero.  Enumerated
    # COMPLETELY on a scaled model (k = 2 polynomials, omega = 4, index alphabet
    # 0..7), i.e. all 8^6 = 262,144 encodings.  The full-parameter statement
    # (k = 4, omega = 80, 84 bytes) is the Lean theorem
    # Mldsa.Encoding.hint_decode_canonical / hint_decode_injective.
    # The two CHECKS are switches, so the negative controls below are the
    # same decoder with one check disabled rather than a second transcription that
    # could drift out of step with this one.
    def decode_small(y, k=2, om=4, nmax=8, strict_inc=True, pad_gate=True):
        """Faithful transcription of FIPS 204 Alg. 21 at reduced parameters."""
        hs = [[] for _ in range(k)]
        idx = 0
        for i in range(k):
            cut = y[om + i]
            if cut < idx or cut > om:
                return None
            first = idx
            while idx < cut:
                if strict_inc and idx > first and y[idx - 1] >= y[idx]:
                    return None
                if y[idx] >= nmax:
                    return None
                hs[i].append(y[idx])
                idx += 1
        if pad_gate:
            for j in range(idx, om):
                if y[j] != 0:
                    return None
        return tuple(tuple(r) for r in hs)
    # WHY THE KEY IS A SET.  `decode_small` returns the indices of each row in
    # the order they were READ, so keying E12's collision map on that ordered
    # tuple would make two encodings differing only by a permutation decode to
    # two DIFFERENT keys, which can never collide — E12 would then pass
    # unchanged with the strict-increase check deleted, which is precisely the
    # CVE-2026-24850 / Hamburg-2024 defect it is named after (and exactly what
    # formal/z3/vacuity_audit.py mutation V35 probes for).
    # The FIPS object is a hint SET (a bit vector), so the key is the set.
    def hint_set(d):
        return tuple(frozenset(row) for row in d)

    def canonicality_sweep(dec):
        """(seen, dupes, total, first_collision) over ALL 8^6 encodings."""
        seen, dupes, total, coll = {}, 0, 0, None
        for code in range(8 ** 6):
            y = [(code >> (3 * t)) & 7 for t in range(6)]
            d = dec(y)
            if d is None:
                continue
            total += 1
            key = hint_set(d)
            if key in seen:
                dupes += 1
                if coll is None:
                    coll = (seen[key], tuple(y))
            else:
                seen[key] = tuple(y)
        return seen, dupes, total, coll

    # CONTROLS: the SAME sweep, run against the decoder with the
    # strict-increase check or the trailing-zero padding check switched off, must
    # FIND a collision.  That is mutations V35/V36 brought in-band, and it is
    # what makes `dupes == 0` evidence rather than an empty search.
    def decode_no_strictinc(y):
        return decode_small(y, strict_inc=False)

    def decode_no_padding_gate(y):
        return decode_small(y, pad_gate=False)

    seen, dupes, total, coll = canonicality_sweep(decode_small)
    ok &= pinned("E12", "EXH",
                 "HintBitUnpack (scaled k=2,omega=4): accepted encoding is UNIQUE per hint SET",
                 lambda dec: canonicality_sweep(dec)[1] == 0, decode_small,
                 f"all 8^6 = 262144 strings; {total} accepted, {len(seen)} distinct hint sets, "
                 f"{dupes} collisions"
                 + (f"; first collision {coll[0]} vs {coll[1]}" if coll else ""),
                 reject=[decode_no_strictinc, decode_no_padding_gate])

    # E13: and the decoder is exactly the FIPS predicate on that scaled model —
    # every accepted string round-trips through the canonical ENCODER, which
    # emits each row's indices in strictly increasing order.
    def encode_small(hs, k=2, om=4):
        flat = [v for row in hs for v in sorted(row)]
        if len(flat) > om:
            return None
        cuts, run = [], 0
        for row in hs:
            run += len(row)
            cuts.append(run)
        return flat + [0] * (om - len(flat)) + cuts
    def encode_desc(hs, k=2, om=4):
        """The same encoder emitting each row DESCENDING -- the non-canonical
        order the strict-increase check exists to reject."""
        flat = [v for row in hs for v in sorted(row, reverse=True)]
        if len(flat) > om:
            return None
        cuts, run = [], 0
        for row in hs:
            run += len(row)
            cuts.append(run)
        return flat + [0] * (om - len(flat)) + cuts

    def roundtrip_ok(enc):
        return not [h for h, y in seen.items() if enc(h) != list(y)]
    rt_bad = [h for h, y in seen.items() if encode_small(h) != list(y)]
    ok &= pinned("E13", "EXH", "every accepted encoding equals the canonical encoder's output",
                 roundtrip_ok, encode_small,
                 f"{len(seen)} hint sets round-tripped, 0 non-canonical",
                 reject=[encode_desc, lambda hs: None,
                         lambda hs: list(encode_small(hs) or []) + [0]])

    # E14: FIPS 204 §5.2 message-representative injectivity, COMPLETE on a small
    # alphabet.  M' = 0x00 || len(ctx) || ctx || M with |ctx| <= 255 must be
    # injective in (ctx, M) -- otherwise a signature made for one context could be
    # replayed in another.  Also checks the pure/HashML-DSA separation byte.
    # A "00/01 domains disjoint" conjunct of the shape
    #     sep_ok = all(not mp.startswith(b"\x01") for mp in coll)
    # over a `coll` every element of which is built as b"\x00" + ... is a
    # TAUTOLOGY: it cannot be false for any input, and deleting it changes
    # nothing in either verify_all.py or the vacuity audit.  The claim is
    # therefore made against the OTHER domain, which is actually built:
    # HashML-DSA's M' = 0x01 || len(ctx) || ctx || OID || H(M).
    OID = bytes(range(11))                       # any fixed-width prehash OID

    def mprime_sweep(pure, prehash):
        """(collisions, pure_images, prehash_images) for a pair of encoders."""
        coll, hash_coll, bad = {}, {}, 0
        for clen in range(0, 4):
            for cbits in range(2 ** clen):
                ctx = bytes((cbits >> t) & 1 for t in range(clen))
                for mlen in range(0, 5):
                    for mbits in range(2 ** mlen):
                        m = bytes((mbits >> t) & 1 for t in range(mlen))
                        mp = pure(clen, ctx, m)
                        if mp in coll and coll[mp] != (ctx, m):
                            bad += 1
                        coll[mp] = (ctx, m)
                        hash_coll[prehash(clen, ctx, m)] = (ctx, m)
        return bad, coll, hash_coll

    def mprime_injective_and_separated(encs):
        pure, prehash = encs
        bad, c, h = mprime_sweep(pure, prehash)
        return bad == 0 and bool(c) and bool(h) and not (set(c) & set(h))

    _pure = lambda clen, ctx, m: b"\x00" + bytes([clen]) + ctx + m
    _prehash = lambda clen, ctx, m: b"\x01" + bytes([clen]) + ctx + OID + m
    bad14, coll, hash_coll = mprime_sweep(_pure, _prehash)
    # the pure and prehash images can never collide: they differ in byte 0
    sep_ok = not (set(coll) & set(hash_coll))
    both_built = bool(coll) and bool(hash_coll)
    ok &= pinned("E14", "EXH", "M' = 00||len(ctx)||ctx||M injective in (ctx, M); 00/01 domains disjoint",
                 mprime_injective_and_separated, (_pure, _prehash),
                 f"{len(coll)} pure + {len(hash_coll)} prehash representatives, 0 collisions",
                 reject=[  # no ctx length byte -> ("a","b") and ("ab","") collide
                     (lambda clen, ctx, m: b"\x00" + ctx + m, _prehash),
                     # prehash reusing the pure domain byte -> the domains meet
                     (_pure, lambda clen, ctx, m: b"\x00" + bytes([clen]) + ctx + m),
                     # a constant representative: maximally non-injective
                     (lambda clen, ctx, m: b"\x00", _prehash)],
                 parts=[("pure_domain_injective", bad14 == 0),
                        ("both_domains_nonempty", both_built),
                        ("pure_prehash_disjoint", sep_ok)])

    # E9: Barrett over a dense sweep of its full input domain (SMT proves the rest)
    emax_f, emax_i = 15 * Q * (Q - 1), 128 * Q * (Q - 1)
    def sweep(emax, n=200000, kern=None):
        """Return one flag per CHECKED PROPERTY, so each is separately auditable."""
        kern = kern or kern_barrett
        good = dict(r_nonneg=True, r_lt_2q=True, congruent=True, qhat_lt_2p31=True,
                    lane_local=True)
        step = max(1, emax // n)
        pts = list(range(0, emax + 1, step)) + [0, 1, Q - 1, Q, Q + 1, 2 * Q, emax - 1, emax]
        for e in pts:
            r, qh = kern(e)
            if r < 0: good["r_nonneg"] = False
            if r >= 2 * Q: good["r_lt_2q"] = False
            if r % Q != e % Q: good["congruent"] = False
            if qh >= (1 << 31): good["qhat_lt_2p31"] = False
            if e * MU33 >= (1 << 64): good["lane_local"] = False
        return good
    # CONTROLS: the sweep must NOTICE a broken Barrett.  Each control uses
    # a small point count -- a wrong shift fails within the first handful of
    # points -- so the four extra sweeps per obligation cost milliseconds.
    for oid, emax, tag in (("E9a", emax_f, "forward"), ("E9b", emax_i, "inverse")):
        g = sweep(emax)
        ok &= pinned(oid, "EXH",
                     f"{tag} two-step Barrett dense sweep (0<=r<2Q, r=e mod Q, qhat<2^31, lane-local)",
                     lambda k, _e=emax: all(sweep(_e, 2000, k).values()), kern_barrett,
                     "200k points + edges",
                     reject=[lambda e: kern_barrett(e, shift=30),      # qhat too large
                             lambda e: kern_barrett(e, shift=36),      # qhat too small
                             lambda e: kern_barrett(e, shift2=26),     # step 2 shift wrong
                             lambda e: (kern_barrett(e)[0] + 1, kern_barrett(e)[1]),
                             lambda e: (e - Q * ((e * MU33) >> SH1), (e * MU33) >> SH1),
                             lambda e: (e, 0)],                        # no reduction at all
                     parts=sorted(g.items()))
    return ok


# ================================================================ SMT obligations
def _syntactically_trivial(claim):
    """`True`, or `e == e` / `e <-> e` with structurally identical sides.

    These are exactly what a gutted obligation looks like,
    and Z3 discharges them for free.  Checked structurally so that even a claim
    that is legitimately valid without premises cannot be replaced by one.
    """
    try:
        from z3 import is_true, is_eq, is_bool
        if is_true(claim):
            return True
        if is_eq(claim) and claim.num_args() == 2 and claim.arg(0).eq(claim.arg(1)):
            return True
        if is_bool(claim) and claim.decl().name() in ("=", "iff") \
                and claim.num_args() == 2 and claim.arg(0).eq(claim.arg(1)):
            return True
    except Exception:
        return False
    return False


def smt_obligations():
    if not HAVE_Z3:
        record("S*", "SMT", "z3 unavailable", False, "install z3-solver")
        return False
    ok = True

    def prove(oid, desc, build, detail="", theory_valid=()):
        """Discharge one obligation CONJUNCT BY CONJUNCT.

        `build()` returns `(premises, [(conjunct_name, claim), ...])`.

        Every conjunct is proved on its own (premises + Not(claim)
        must be UNSAT) and reported on its own line, so a deleted conjunct
        changes the emitted ID set (caught by EXPECTED_CONJUNCTS) and a
        conjunct no mutation can break is visible to `vacuity_audit.py`.

        In addition the PREMISE SET ALONE must be SAT.  An `unsat` derived from
        contradictory premises is free and proves nothing; that is the classical
        notion of vacuity, and a *mutation* audit cannot detect it.  Every SMT
        obligation therefore carries a `premises_sat` conjunct.

        `claims_discriminate` is the DUAL of that guard.  An
        `unsat` is equally free when `Not(claim)` is unsatisfiable ON ITS OWN --
        i.e. when the claim is a theorem of Z3's background theory and the
        premises contribute nothing.  That is exactly what a conjunct gutted to
        `x == x`, `r < r + 1` or `True` looks like, and without the dual it is
        invisible: the report prints `unsat (proved)` either way.  Each claim is
        checked for FALSIFIABILITY with the premises dropped; the conjuncts that
        are legitimately theory-valid (a pure algebraic identity between two
        differently-written expressions, with no domain hypothesis) must be named
        in `theory_valid=` at the call site, which makes that list the complete,
        reviewable set of conjuncts this guard cannot cover.
        """
        prem, claims = build()
        worst = 0.0
        s0 = Solver(); s0.set("timeout", SMT_TIMEOUT_MS)
        for p in prem:
            s0.add(p)
        t = time.time(); prem_ok = s0.check() == sat; worst = max(worst, time.time() - t)
        parts = [("premises_sat", prem_ok)]
        bad = []
        trivial = []
        declared_valid = []
        for name, claim in claims:
            s = Solver(); s.set("timeout", SMT_TIMEOUT_MS)
            for p in prem:
                s.add(p)
            s.add(Not(claim))
            t = time.time(); res = s.check(); worst = max(worst, time.time() - t)
            good = res == unsat
            if not good:
                bad.append(f"{name}={res}" + (f" {s.model()}" if res == sat else ""))
            parts.append((name, good))
            # ... and the premise-free falsifiability check.  A claim that is
            # SYNTACTICALLY trivial (`True`, or `e == e` for structurally equal
            # sides) is rejected even when it is declared theory-valid: that is
            # the literal shape of a gutted obligation.
            if _syntactically_trivial(claim):
                trivial.append(name + " (syntactically trivial)")
                continue
            st = Solver(); st.set("timeout", SMT_TIMEOUT_MS)
            st.add(Not(claim))
            t = time.time(); rt = st.check(); worst = max(worst, time.time() - t)
            if rt != sat:                       # unsat or unknown: not falsifiable
                (declared_valid if name in theory_valid else trivial).append(name)
        # every name declared theory-valid must ACTUALLY be theory-valid, so the
        # exemption list cannot quietly grow to cover conjuncts that do have
        # content (or rot once a conjunct is strengthened).
        stale = sorted(set(theory_valid) - set(declared_valid))
        parts.append(("claims_discriminate", not trivial and not stale))
        nonlocal ok
        d = detail or (f"unsat (proved) for each of {len(claims)} conjuncts; "
                       f"slowest solver call {worst*1000:.0f} ms of {SMT_TIMEOUT_MS} ms budget")
        if bad:
            d = "COUNTEREXAMPLE " + "; ".join(bad)[:500]
        elif trivial or stale:
            d = (f"VACUOUS: claim(s) valid without premises {trivial}; "
                 f"stale theory_valid entries {stale}")
        ok &= record(oid, "SMT", desc, True, d, parts=parts)

    # S1/S2: two-step Barrett correctness over the ENTIRE input domain (both
    # variants).  Every conjunct the PACKED form depends on is here: the lane
    # product must fit a 64-bit lane (else neighbouring lanes interfere), step
    # 1's quotient must fit the 31-bit mask field, step 1's OUTPUT must stay
    # under 2^33 (which is what lets step 2 reuse the same mask), and only then
    # the classical 0 <= r < 2Q.
    for oid, emax, tag in (("S1", 15 * Q * (Q - 1), "forward"), ("S2", 128 * Q * (Q - 1), "inverse")):
        def build(emax=emax):
            e = Int('e')
            qhat = (e * MU33) / (1 << SH1)         # z3 Int division = floor for e >= 0
            x1 = e - Q * qhat
            r = x1 - Q * (x1 / (1 << SH2))
            return ([e >= 0, e <= emax],
                    [("lane_product_lt_2p64", e * MU33 < (1 << 64)),
                     ("qhat_lt_2p31", qhat < (1 << 31)),
                     ("step1_nonneg", x1 >= 0),
                     ("step1_lt_2p33", x1 < (1 << 33)),
                     ("r_nonneg", r >= 0),
                     ("r_lt_2q", r < 2 * Q)])
        prove(oid, f"{tag} two-step Barrett: forall e<=max, lane-local, qhat<2^31, 0<=r<2Q", build)

    # S3/S4: congruence r == e (mod Q) over the entire domain.  BOTH steps
    # subtract a multiple of Q, so the claim is about the composition.
    for oid, emax, tag in (("S3", 15 * Q * (Q - 1), "forward"), ("S4", 128 * Q * (Q - 1), "inverse")):
        def build(emax=emax):
            e = Int('e')
            qhat = (e * MU33) / (1 << SH1)
            x1 = e - Q * qhat
            r = x1 - Q * (x1 / (1 << SH2))
            # r = e - Q*(qhat + b) is congruent by construction; prove r is the
            # *unique* representative < 2Q
            return ([e >= 0, e <= emax],
                    [("unique_rep_below_2q", Or(r == e % Q, r == (e % Q) + Q))])
        prove(oid, f"{tag} two-step Barrett: r in {{e mod Q, e mod Q + Q}}", build)

    # ----------------------------------------------------------------- S5
    # THE SOUNDNESS GAP THIS CLOSES.  An S5 that concludes
    # `lane + 2Q + r < LB + 4Q` while its name, its own comment and
    # FORMAL_VERIFICATION.md all say "+2q per layer" matches neither the
    # expression nor the bound of the emitted Yul:
    #
    #   test/ZZZ_NttVariants.sol :: nttFwV3, every layer
    #       t0 := mul(mload(pv), S)          <- the MULTIPLIED operand is W[pv]
    #       ...spread Barrett -> V < 2q...
    #       mstore(pu, add(u, t0))           <- W[pu] = u + V
    #       mstore(pv, sub(add(u, TWOQ4), t0))  <- W[pv] = u + 2q - V
    #
    # so the two new lanes are `u + V` and `u + 2q - V`, NOT `u + 2q + V`.  The
    # `+2Q` form of the `u + 2q + V` expression is SAT, i.e. it is not a
    # theorem, and the `+4Q` that would make it one does not close the
    # induction: 8 layers of +4q give 33q > 2^28 and violate the obligation's own
    # `LB <= 15Q` premise from layer 5 on.  The correct expressions DO prove +2q
    # (this obligation), and the CALC obligation C9f closes the induction with it.
    def build_s5():
        u, x, Sc, LB = Int('u'), Int('x'), Int('S'), Int('LB')
        prem = [LB >= Q, LB <= 15 * Q,        # lane bound entering this layer
                u >= 0, u < LB,               # W[pu]
                x >= 0, x < LB,               # W[pv], the multiplied operand
                Sc >= 0, Sc < Q]              # twiddle
        prod = x * Sc
        V1 = prod - Q * ((prod * MU33) / (1 << SH1))
        V = V1 - Q * (V1 / (1 << SH2))
        return prem, [
            ("product_in_barrett_domain", prod <= 15 * Q * (Q - 1)),
            ("product_is_lane_local", prod * MU33 < (1 << 64)),
            ("V_nonneg", V >= 0),
            ("V_lt_2q", V < 2 * Q),
            ("sum_lane_lt_LB_plus_2q", u + V < LB + 2 * Q),
            ("diff_lane_nonneg", u + 2 * Q - V >= 0),
            ("diff_lane_lt_LB_plus_2q", u + 2 * Q - V < LB + 2 * Q),
        ]
    prove("S5", "forward NTT (nttFwV3) butterfly: both new lanes < LB + 2q, product in Barrett domain",
          build_s5)

    # S6: inverse Gentleman-Sande step, over the layers that USE Barrett.
    # THE DOMAIN LINKAGE THIS CLOSES.  An S6 that
    # quantifies over K <= 128 concludes `product <= 256*Q*(Q-1)`.  That
    # bound is (i) above 2^53, which C9d denies, and (ii) above
    # BARRETT_FIRST_FAIL, i.e. outside the domain S1-S4/E9b verify Barrett over,
    # so nothing would link S6 to the reduction it feeds.  K = 128 is layer 8, and
    # ZZZ_InvNtt.sol canonicalises layer 8 with a per-lane `mod`, NOT
    # with Barrett -- see S6b.  The Barrett layers are L3..L7 (the fused entry
    # block reduces with mulmod/addmod instead — see S14); the step below is
    # proved for K = 2^(L-1) over L = 1..7, a SUPERSET of the instantiated
    # K = 4..64, and the product is <= 128*Q*(Q-1), exactly C9d's bound.
    def build_s6():
        U, V, K, Sc = Int('U'), Int('V'), Int('K'), Int('S')
        prem = [Or(*[K == (1 << i) for i in range(7)]),   # K = 2^(L-1), L = 1..7
                U >= 0, U < K * Q, V >= 0, V < K * Q,
                Sc >= 0, Sc < Q]
        diff = U + K * Q - V                     # Yul: sub(add(u, Q4_K), v)
        prod = diff * Sc
        r1 = prod - Q * ((prod * MU33) / (1 << SH1))
        r = r1 - Q * (r1 / (1 << SH2))
        return prem, [
            ("diff_lane_positive", diff > 0),
            ("diff_lane_lt_2Kq", diff < 2 * K * Q),
            ("product_in_verified_domain", prod <= 128 * Q * (Q - 1)),
            ("product_is_lane_local", prod * MU33 < (1 << 64)),
            ("barrett_r_nonneg", r >= 0),
            ("barrett_r_lt_2q", r < 2 * Q),
            ("sum_lane_lt_2Kq", U + V < 2 * K * Q),
        ]
    prove("S6", "inverse NTT (nttInvV3) Barrett layers L3..L7 (proved for K <= 64): "
          "product <= 128q(q-1) (= C9d/S2/S4/E9b domain)",
          build_s6)

    # S6b: inverse layer 8 is NOT a Barrett layer.  ZZZ_InvNtt.sol:374-407 folds
    # the n^-1 scaling in and canonicalises every lane with `mod(., Q)`.  What
    # must hold there is only that each 64-bit SWAR lane holds its product
    # without overlapping its neighbour.
    def build_s6b():
        sAB, sCD, dAB, dCD, Sc = Int('sAB'), Int('sCD'), Int('dAB'), Int('dCD'), Int('S')
        prem = [sAB >= 0, sAB < 128 * Q, sCD >= 0, sCD < 128 * Q,   # L7 sum lanes
                dAB >= 0, dAB < 2 * Q, dCD >= 0, dCD < 2 * Q,       # L7 Barrett outputs
                Sc >= 0, Sc < Q]
        return prem, [
            ("sum_diff_positive", sAB + 128 * Q - sCD > 0),
            ("sum_lane_product_fits_64", (sAB + sCD) * Sc < (1 << 64)),
            ("diff_lane_product_fits_64", (sAB + 128 * Q - sCD) * Sc < (1 << 64)),
            ("d_diff_positive", dAB + 2 * Q - dCD > 0),
            ("d_lane_products_fit_64", (dAB + dCD) * Sc < (1 << 64)),
            ("d_diff_product_fits_64", (dAB + 2 * Q - dCD) * Sc < (1 << 64)),
        ]
    prove("S6b", "inverse NTT layer 8 (mod-canonicalised, not Barrett): every lane product < 2^64",
          build_s6b)

    # S7: PACKED-LANE independence, all FOUR lanes, no spreading.
    # A second conjunct of the shape
    # `packed*MU == a*MU + b*MU*2^128` is DISTRIBUTIVITY over unbounded Int --
    # a tautology of Z3's integer theory that says nothing about the EVM.  What
    # is modelled here is what the Yul actually does to the packed word, and the
    # statement is about the word the transform really holds (four 64-bit
    # lanes) rather than about the two-lane SPREAD intermediate a spread form
    # would need:
    #     w  := sub(w, mul(and(shr(33, mul(w, MU33)), QHATM31), Q))    step 1
    #     w  := sub(w, mul(and(shr(23, w),            QHATM31), Q))    step 2
    # Having no spread/repack removes those two intermediates AND makes the
    # obligation stronger: nothing separates the lanes except the
    # arithmetic, so every lane's non-interference has to be proved outright.
    #
    # ENCODING NOTE.  Asking Z3 for `((w*MU33)/2^33 masked)/2^{64k} % 2^64` directly
    # is three nested divisions over a 256-bit form and returns `unknown` (measured:
    # 14 of 28 conjuncts, 20 s each).  The Euclidean WITNESSES below remove the
    # nesting without weakening anything: `l*MU33 == q*2^33 + s, 0 <= s < 2^33`
    # determines q uniquely, and `qhat_is_the_shift` ASSERTS that this q is the
    # value the kernel's own `shr` produces, so the witness is checked and not
    # assumed.  Everything after that is one division of an EXPLICIT linear form.
    def build_s7():
        L = [Int('l%d' % k) for k in range(4)]
        QH = [Int('q%d' % k) for k in range(4)]      # step-1 quotients (witnessed)
        SS = [Int('s%d' % k) for k in range(4)]      # step-1 remainders
        BB = [Int('b%d' % k) for k in range(4)]      # step-2 quotients (witnessed)
        TT = [Int('t%d' % k) for k in range(4)]      # step-2 remainders
        emax = 128 * Q * (Q - 1)
        X1 = [L[k] - Q * QH[k] for k in range(4)]    # step-1 lane outputs
        prem = []
        for k in range(4):
            prem += [L[k] >= 0, L[k] <= emax,
                     SS[k] >= 0, SS[k] < (1 << SH1),
                     L[k] * MU33 == QH[k] * (1 << SH1) + SS[k],
                     TT[k] >= 0, TT[k] < (1 << SH2),
                     X1[k] == BB[k] * (1 << SH2) + TT[k]]
        w = sum(L[k] * (1 << (64 * k)) for k in range(4))
        A = sum(QH[k] * (1 << (64 * k)) for k in range(4))
        B2 = sum(BB[k] * (1 << (64 * k)) for k in range(4))
        R = [X1[k] - Q * BB[k] for k in range(4)]
        # what `shr(33, mul(w, MU33))` holds: the four quotients in their lanes,
        # with each lane's REMAINDER sitting below the next lane's quotient --
        # which is exactly why the mask is 31 bits and not 32
        Y1 = A + sum(SS[k] * (1 << (64 * k - SH1)) for k in range(1, 4))
        Y2 = B2 + sum(TT[k] * (1 << (64 * k - SH2)) for k in range(1, 4))
        w1 = w - A * Q                               # the word after step 1
        r = w1 - B2 * Q                              # the word after step 2

        def _above(k, terms):
            """the part of an explicit lane sum at or above bit 64k"""
            return sum(c * (1 << (sh - 64 * k)) for c, sh in terms if sh >= 64 * k)
        y1t = ([(QH[j], 64 * j) for j in range(4)]
               + [(SS[j], 64 * j - SH1) for j in range(1, 4)])
        y2t = ([(BB[j], 64 * j) for j in range(4)]
               + [(TT[j], 64 * j - SH2) for j in range(1, 4)])
        rt = [(R[j], 64 * j) for j in range(4)]
        claims = [
            ("mul_no_2p256_overflow", w * MU33 < (1 << 256)),
            ("step1_shift_is_the_lane_quotients", (w * MU33) / (1 << SH1) == Y1),
            ("step2_shift_is_the_lane_quotients", w1 / (1 << SH2) == Y2),
        ]
        for k in range(4):
            claims += [
                (f"lane{k}_qhat_is_the_shift", QH[k] == (L[k] * MU33) / (1 << SH1)),
                (f"lane{k}_product_no_carry", L[k] * MU33 < (1 << 64)),
                (f"lane{k}_qhat_lt_2p31", QH[k] < (1 << 31)),
                (f"lane{k}_step1_no_borrow", X1[k] >= 0),
                (f"lane{k}_step1_lt_2p33", X1[k] < (1 << SH1)),
                (f"lane{k}_step2_quotient_lt_2p31", BB[k] < (1 << 31)),
                (f"lane{k}_no_borrow", R[k] >= 0),
                (f"lane{k}_fits_its_lane", R[k] < 2 * Q),
            ]
            # The MASK, lane by lane.  Asking for `(Y/2^{64k}) % 2^31 == q_k` in
            # one query returns `unknown` at k = 2 (measured, 120 s): the nested
            # div/mod over a four-term 256-bit form is past Z3's reach.  Split at
            # the shift, it is two SUBSTITUTABLE equalities -- `Y/2^{64k} == U`
            # and `U % 2^31 == q_k`, both decided in milliseconds -- whose
            # conjunction IS the extraction fact by substituting the first into
            # the second.  Lane 0's shift is by 2^0, so its `div` half is an
            # identity and only the `mod` half is stated.
            if k == 0:
                claims += [
                    ("lane0_step1_field_is_the_quotient", Y1 % (1 << 31) == QH[0]),
                    ("lane0_step2_field_is_the_quotient", Y2 % (1 << 31) == BB[0]),
                    ("lane0_recovered", r % (1 << 64) == R[0]),
                ]
            else:
                claims += [
                    (f"lane{k}_step1_shift_exposes_the_field",
                     Y1 / (1 << (64 * k)) == _above(k, y1t)),
                    (f"lane{k}_step1_field_is_the_quotient",
                     _above(k, y1t) % (1 << 31) == QH[k]),
                    (f"lane{k}_step2_shift_exposes_the_field",
                     Y2 / (1 << (64 * k)) == _above(k, y2t)),
                    (f"lane{k}_step2_field_is_the_quotient",
                     _above(k, y2t) % (1 << 31) == BB[k]),
                    (f"lane{k}_shift_exposes_the_result",
                     r / (1 << (64 * k)) == _above(k, rt)),
                    (f"lane{k}_recovered", _above(k, rt) % (1 << 64) == R[k]),
                ]
        return prem, claims
    prove("S7", "packed two-step Barrett: ALL FOUR 64-bit lanes reduce in place "
          "(no carry, no borrow, no spreading)", build_s7)

    # S8: strict norm predicate equivalence, symbolically over all 18-bit fields.
    # EVM semantics: wrapped `sub` + UNSIGNED `lt`.  Encode the wrap explicitly.
    def build_s8():
        v = Int('v')
        wrapped = If(v >= BETA + 1, v - (BETA + 1), v - (BETA + 1) + (1 << 256))
        flag = Not(wrapped < 2 * GAMMA1 - 2 * BETA - 1)          # kernel: reject?
        # FIPS: reject iff |z| >= GAMMA1 - BETA, where z = GAMMA1 - v (signed)
        fips_reject = Or(GAMMA1 - v >= GAMMA1 - BETA, v - GAMMA1 >= GAMMA1 - BETA)
        return ([v >= 0, v < (1 << 18)], [("kernel_iff_fips", flag == fips_reject)])
    prove("S8", "norm flag (EVM wrap/unsigned-lt) == strict FIPS reject, all 18-bit v", build_s8)

    # S8b: the SHIPPED decoder's PACKED form -- four coefficients, one word, one
    # check -- symbolically, at EVM semantics, for arbitrary 18-bit fields.
    #
    # This is S8's obligation for a kernel that no longer evaluates a predicate
    # per coefficient.  What has to be proved is not just "the predicate is the
    # FIPS one" but that the word arithmetic IS four independent copies of it:
    # every lane's `sub` must not borrow from its neighbour, every lane's `add`
    # must not carry into it, and the single flag bit each comparison leaves at
    # bit 32 must be the one the mask picks up.  Every one of those is a
    # conjunct below, per lane, and the whole apparatus is what makes ONE
    # `and(add(o, Z_NLO), sub(Z_NHI, o))` a four-coefficient norm check.
    #
    # ENCODING NOTE (same as S7): the three quotients are Euclidean WITNESSES
    # (`t == F*2^32 + rt, 0 <= rt < 2^32` determines F uniquely) rather than
    # nested `div` over a 256-bit form, and each witness is CHECKED against the
    # shift the kernel actually performs rather than assumed.
    def build_s8b():
        NLO = (1 << 32) - (GAMMA1 - BETA)          # Z_NLO, per lane
        NHI = (1 << 32) + Q - (GAMMA1 - BETA)      # Z_NHI, per lane
        QB32 = (1 << 32) - Q                       # Z_QB32, per lane
        UOFF = Q + GAMMA1                          # Z_UOFF, per lane
        V = [Int('v%d' % k) for k in range(4)]
        F = [Int('f%d' % k) for k in range(4)]     # mod flags   (witnessed)
        RF = [Int('rf%d' % k) for k in range(4)]
        XB = [Int('xb%d' % k) for k in range(4)]   # low-edge flags  (witnessed)
        RX = [Int('rx%d' % k) for k in range(4)]
        YB = [Int('yb%d' % k) for k in range(4)]   # high-edge flags (witnessed)
        RY = [Int('ry%d' % k) for k in range(4)]
        U = [UOFF - V[k] for k in range(4)]
        T = [U[k] + QB32 for k in range(4)]
        O = [U[k] - Q * F[k] for k in range(4)]
        X = [O[k] + NLO for k in range(4)]
        Y = [NHI - O[k] for k in range(4)]
        prem = []
        for k in range(4):
            prem += [V[k] >= 0, V[k] < (1 << 18),
                     RF[k] >= 0, RF[k] < (1 << 32), T[k] == F[k] * (1 << 32) + RF[k],
                     RX[k] >= 0, RX[k] < (1 << 32), X[k] == XB[k] * (1 << 32) + RX[k],
                     RY[k] >= 0, RY[k] < (1 << 32), Y[k] == YB[k] * (1 << 32) + RY[k]]
        # the words the kernel actually holds
        Tw = sum(T[k] * (1 << (64 * k)) for k in range(4))
        Ow = sum(O[k] * (1 << (64 * k)) for k in range(4))
        Xw = sum(X[k] * (1 << (64 * k)) for k in range(4))
        Yw = sum(Y[k] * (1 << (64 * k)) for k in range(4))

        def _above(k, terms):
            """the part of an explicit lane sum at or above bit 64k"""
            return sum(c * (1 << (sh - 64 * k)) for c, sh in terms if sh >= 64 * k)
        ot = [(O[j], 64 * j) for j in range(4)]
        tt = [(T[j], 64 * j) for j in range(4)]
        xt = [(X[j], 64 * j) for j in range(4)]
        yt = [(Y[j], 64 * j) for j in range(4)]
        claims = []
        for k in range(4):
            # FIPS 204: reject iff |z| >= gamma1 - beta with z = gamma1 - v signed
            fips_reject = Or(GAMMA1 - V[k] >= GAMMA1 - BETA,
                             V[k] - GAMMA1 >= GAMMA1 - BETA)
            claims += [
                # --- the centered value, and the ONE conditional subtraction --
                (f"lane{k}_u_no_borrow", U[k] > 0),
                (f"lane{k}_u_lt_2q", U[k] < 2 * Q),
                (f"lane{k}_flag_word_no_carry", T[k] < (1 << 33)),
                (f"lane{k}_flag_is_a_bit", And(F[k] >= 0, F[k] <= 1)),
                (f"lane{k}_mask_exposes_the_flag",
                 ((_above(k, tt) % (1 << 64)) / (1 << 32)) % 2 == F[k]),
                (f"lane{k}_flag_iff_u_ge_q", (F[k] == 1) == (U[k] >= Q)),
                (f"lane{k}_correction_is_lane_local", Q * F[k] < (1 << 64)),
                (f"lane{k}_o_no_borrow", O[k] >= 0),
                (f"lane{k}_o_canonical", O[k] < Q),
                (f"lane{k}_o_is_the_centered_map",
                 Or(O[k] == GAMMA1 - V[k], O[k] == GAMMA1 - V[k] + Q)),
                (f"lane{k}_stored_lane_recovered", _above(k, ot) % (1 << 64) == O[k]),
                # --- the two edges of the strict norm window ------------------
                (f"lane{k}_low_edge_no_carry", X[k] < (1 << 33)),
                (f"lane{k}_high_edge_no_borrow", Y[k] > 0),
                (f"lane{k}_high_edge_no_carry", Y[k] < (1 << 33)),
                (f"lane{k}_low_edge_bit_is_a_bit", And(XB[k] >= 0, XB[k] <= 1)),
                (f"lane{k}_high_edge_bit_is_a_bit", And(YB[k] >= 0, YB[k] <= 1)),
                (f"lane{k}_low_edge_mask_exposes_the_flag",
                 ((_above(k, xt) % (1 << 64)) / (1 << 32)) % 2 == XB[k]),
                (f"lane{k}_high_edge_mask_exposes_the_flag",
                 ((_above(k, yt) % (1 << 64)) / (1 << 32)) % 2 == YB[k]),
                (f"lane{k}_low_edge_iff_o_ge_bound", (XB[k] == 1) == (O[k] >= GAMMA1 - BETA)),
                (f"lane{k}_high_edge_iff_o_le_bound",
                 (YB[k] == 1) == (O[k] <= Q - (GAMMA1 - BETA))),
                # --- and the AND of the two bits IS the FIPS verdict ----------
                (f"lane{k}_reject_iff_fips", (XB[k] * YB[k] == 1) == fips_reject),
            ]
            # The four words are read at bit 64k.  For k = 0 that shift is by
            # 2^0, i.e. an identity of Z3's integer theory that would be `sat`
            # with the premises dropped (the `claims_discriminate` guard), so
            # the exposure claim is stated exactly for the lanes whose shift is
            # real -- the same split S7 makes for the same reason.
            if k > 0:
                claims += [
                    (f"lane{k}_flag_shift_exposes_the_lane",
                     Tw / (1 << (64 * k)) == _above(k, tt)),
                    (f"lane{k}_shift_exposes_the_stored_lane",
                     Ow / (1 << (64 * k)) == _above(k, ot)),
                    (f"lane{k}_low_edge_shift_exposes_the_lane",
                     Xw / (1 << (64 * k)) == _above(k, xt)),
                    (f"lane{k}_high_edge_shift_exposes_the_lane",
                     Yw / (1 << (64 * k)) == _above(k, yt)),
                ]
        return prem, claims
    prove("S8b", "packed z decode: ALL FOUR lanes canonicalise and check in place "
          "(no borrow, no carry, one bit-32 flag each) == strict FIPS reject", build_s8b)

    # S11: UseHint intermediate ranges, symbolically (complements exhaustive equality).
    # NOTE q0 reaches 44 exactly at rv = Q-1 = 44*2*GAMMA2 (the FIPS edge case); the
    # kernel's `mul(s1, iszero(eq(s1,44)))` maps that to 0.  Asserting q0<=43 here was
    # a harness bug this suite caught.
    def build_s11():
        rv = Int('rv')
        q0 = rv / (2 * GAMMA2)
        r0 = rv - q0 * (2 * GAMMA2)
        return ([rv >= 0, rv < Q],
                [("q0_nonneg", q0 >= 0), ("q0_le_44", q0 <= 44),
                 ("r0_nonneg", r0 >= 0), ("r0_lt_2gamma2", r0 < 2 * GAMMA2)])
    # NOTE `r0_nonneg`/`r0_lt_2gamma2` ARE valid without the premises -- z3's
    # Int division is Euclidean, so `rv - (rv/k)*k` lies in [0,k) for every rv.
    # They still model the kernel's two-instruction remainder, and the premises
    # are load-bearing for `q0_le_44`, so they are declared rather than deleted.
    prove("S11", "UseHint: q0 in [0,44] (44 only at Q-1) and r0 in [0,2*GAMMA2)", build_s11,
          theory_valid=("r0_nonneg", "r0_lt_2gamma2"))

    # S11b: the edge case is reachable ONLY at rv = Q-1 (so the correction is exact)
    def build_s11b():
        rv = Int('rv')
        return ([rv >= 0, rv < Q, rv / (2 * GAMMA2) == 44],
                [("only_at_q_minus_1", rv == Q - 1)])
    prove("S11b", "q0 == 44 implies rv == Q-1 (edge-case correction is exact)", build_s11b)

    # S13: MINIMALITY of the Barrett failure point — no smaller input violates r < 2q.
    # Together with C11a (failure exactly at that input) this pins the safe domain
    # precisely, which is what makes the C11b/C11c margin numbers meaningful.
    def build_s13():
        e = Int('e')
        qhat = (e * MU33) / (1 << SH1)
        x1 = e - Q * qhat
        r = x1 - Q * (x1 / (1 << SH2))
        return ([e >= 0, e <= 10285325456994078 - 1],
                [("no_earlier_failure", r < 2 * Q),
                 ("lane_local_below_the_cliff", e * MU33 < (1 << 64))])
    prove("S13", "two-step Barrett: no input below the known failure point violates r < 2q",
          build_s13)

    # S14: the inverse NTT's ENTRY FOLD (ZZZ_InvNtt.sol :: nttInvV3, fused
    # L1+L2 block with the matvec-accumulator reduction folded in).  The
    # verifier feeds RAW accumulator lanes (<= ACC_ENTRY = 4(q-1)(17q-1) +
    # q*2^28, exactly O8's lane ceiling — the z/c lanes are the LAZY forward
    # NTT's, < 17q) straight into the block.  What has to hold at EVM
    # semantics, and what the premises buy, is that the multiple-of-q
    # offsets ACCQ30 = q*2^30 / ACCQ31 = q*2^31 DOMINATE the raw lanes, so the
    # 256-bit subtraction never wraps (a wrap shifts the operand by 2^256,
    # which is NOT a multiple of q — FV6 demonstrates the broken residue
    # class); mulmod/addmod themselves are exact for every operand.  The two
    # `*_congruent` conjuncts are offset-cancellation identities over
    # unbounded Int (declared theory-valid); the no-borrow, no-wrap and
    # exit-bound conjuncts are the domain facts the premises are FOR.
    # Exit lanes: both mulmod lanes and the addmod lane are canonical, the
    # diff-sum lane d01+d23 < 2q — all inside layer 3's < 4q premise (C9g).
    def build_s14():
        u0, u1 = Int('u0'), Int('u1')
        s01, s23 = Int('s01'), Int('s23')
        d01, d23 = Int('d01'), Int('d23')
        Sa, Sc = Int('Sa'), Int('Sc')
        ACC = acc_entry(PK_AMAX)      # the CANONICAL-pk ceiling, stated (B/3.1)
        prem = [u0 >= 0, u0 <= ACC, u1 >= 0, u1 <= ACC,              # raw lanes (O8)
                s01 >= 0, s01 <= 2 * ACC, s23 >= 0, s23 <= 2 * ACC,  # L1 sum lanes
                d01 >= 0, d01 < Q, d23 >= 0, d23 < Q,                # L1 mulmod outputs
                Sa >= 0, Sa < Q, Sc >= 0, Sc < Q]                    # twiddles
        l1_op = u0 + (Q << 30) - u1
        l2_op = s01 + (Q << 31) - s23
        return prem, [
            ("l1_diff_no_borrow", l1_op >= 0),
            ("l1_operand_no_evm_wrap", u0 + (Q << 30) < (1 << 256)),
            ("l1_diff_congruent", (l1_op * Sa) % Q == (((u0 - u1) % Q) * Sa) % Q),
            ("l1_sum_lane_le_2acc", u0 + u1 <= 2 * ACC),
            ("l2_diff_no_borrow", l2_op >= 0),
            ("l2_operand_no_evm_wrap", s01 + (Q << 31) < (1 << 256)),
            ("l2_diff_congruent", (l2_op * Sc) % Q == (((s01 - s23) % Q) * Sc) % Q),
            ("exit_diff_sum_lane_lt_2q", d01 + d23 < 2 * Q),
            ("exit_lanes_meet_l3_premise", d01 + d23 < 4 * Q),
        ]
    prove("S14", "inverse NTT entry fold: offsets dominate raw accumulator lanes, exits < 2q",
          build_s14, theory_valid=("l1_diff_congruent", "l2_diff_congruent"))

    return ok


def kernel_obligations():
    """O1-O10: the arithmetic introduced by the optimized decode/UseHint/matvec kernels.

    Lives in a companion module because it was produced by a separate work
    stream; it is run here so there is exactly ONE obligation count for the
    project.  Its `record` is rebound to ours so its results land in the same
    list and a failure there fails the whole suite.

    The module is NOT imported here.  The trust anchor already read it,
    digested its bytes against the pinned `kernel_obligations::@@file` region and
    `exec`ed the text it digested, so `import` (which prefers a `.pyc`, and would
    thus run something other than what was digested) is never used.
    """
    ko = sys.modules["kernel_obligations"]
    ko.record = record
    fns = [ko.o1_division_constant, ko.o2_no_cross_lane_carry, ko.o3_ge_comparator,
           ko.o4_mod44, ko.o5_multiply_gather, ko.o6_usehint_equivalence,
           ko.o7_preshifted_lane_product, ko.o8_accumulator_bounds,
           ko.o9_packed_store_disjoint, ko.o10_packed_field_extraction]
    ok = True
    for fn in fns:
        ok &= bool(fn())
    return ok


def source_pin_obligation(rec):
    """META-PINS: the source-digest obligation (formal/z3/source_pins.py).

    The HARD part of this check already ran, in the trust anchor at the top of
    this file, before any statement of the suite: this row is the REPORTED part,
    and it covers the things the anchor cannot decide on its own -- the per-region
    attribution, the whole formal/ file manifest, bytecode anywhere under formal/,
    and the executed-bytes registry.

    Never a silent skip -- if the module or the tables cannot be read the
    obligation FAILS, exactly like C16's unreadable-source path.
    """
    try:
        return SOURCE_PINS.check(rec, os.path.abspath(__file__), LOADED_MODULES)
    except Exception as exc:
        parts = [(c, False) for c in
                 ("all_regions_pinned", "no_unpinned_regions",
                  "every_region_digest_matches", "every_formal_file_pinned",
                  "every_pinned_file_present", "every_formal_file_digest_matches",
                  "no_bytecode_cache_under_formal",
                  "executing_modules_are_the_pinned_bytes",
                  "no_alternate_source_encoding")]
        return rec("META-PINS", "CALC",
                   "every source region, file and executed byte of the formal "
                   "apparatus matches its pinned digest",
                   False, f"CANNOT RUN formal/z3/source_pins.py: {exc!r}",
                   parts=parts)


def _abort_with_fail_rows(exc):
    """A CRASH must not leave the operator staring at a wall of green.

    This is the remedy for the gap FORMAL_VERIFICATION.md §5 item 9 records.
    Without this, a single `ZeroDivisionError` in
    `ref_decompose` would abort the suite at the first affected obligation
    after emitting a long run of `[PASS]` rows and **0 `[FAIL]` rows** — and
    then die.  Nothing is silently starved (`vacuity_audit.py` raises CRASH,
    and NEVER-KILLED for anything the crashing mutation alone killed), but an
    operator triaging the crash line scrolls up into an unbroken green report,
    which is exactly the wrong signal.

    Wrapping all 62 obligation BODIES is the wrong shape of fix — 62 wrappers
    is 62 places to get the `try` boundary wrong, and it
    would convert a crash into a per-obligation FAIL while letting the run
    CONTINUE, so the suite would go on proving things on top of a kernel that
    just raised.  This does the useful half at one site: every obligation that
    never produced a verdict gets an explicit `[FAIL] <id>` row naming the
    crash, so the emitted set is complete and the last thing on screen says the
    PASS rows above are void.  The run still stops, which is the correct
    response to an exception inside a proof.
    """
    ran = {r[0] for r in results}
    missing = [o for o in EXPECTED_OBLIGATIONS if o not in ran]
    print("")
    for oid in missing:
        print(f"[FAIL] {oid:<7} CRASH  never ran — the suite aborted: "
              f"{type(exc).__name__}: {exc}")
    print("\n" + "!" * 78)
    print("SUITE ABORTED BY AN EXCEPTION — NOTHING ABOVE IS A VERDICT")
    print(f"  {type(exc).__name__}: {exc}")
    print(f"  {len(results)} of {len(EXPECTED_OBLIGATIONS)} obligations reached a "
          f"verdict; the other {len(missing)} are FAIL rows above, not silence.")
    print("  The green rows printed before the exception were computed by a suite "
          "that then raised;")
    print("  treat the whole run as VOID and fix the exception before reading any "
          "of them.")
    print("!" * 78)
    traceback.print_exc()
    return 3


def main():
    print("=" * 78)
    print("ML-DSA-44 EVM verifier — machine-checked obligation suite")
    print("=" * 78)
    t0 = time.time()
    ok = True
    try:
        print("\n-- CALC (exact integer facts) " + "-" * 46)
        ok &= calc_obligations()
        print("\n-- SMT (Z3 proofs over unbounded/large domains) " + "-" * 28)
        ok &= smt_obligations()
        print("\n-- EXH (complete-domain enumeration) " + "-" * 39)
        ok &= exh_obligations()
        print("\n-- O (optimized kernels, src/Decode.sol) " + "-" * 34)
        ok &= kernel_obligations()
        # ---- META-PINS: the source-digest tripwire -------------------------
        ok &= source_pin_obligation(record)
    except BaseException as exc:                   # noqa: BLE001 — deliberate
        return _abort_with_fail_rows(exc)

    # ---- the tally is an ASSERTION, not prose -----------------------------------
    # Printing `len(results)` would let a deleted obligation produce a green
    # "81/81".  The expected ID sets are pinned here instead;
    # a missing, renamed or duplicated obligation OR CONJUNCT is a FAILURE.
    #
    # Two ways that assertion goes hollow:
    #  (a) META-IDS's own rows not being members of the pinned sets: were
    #      `got_obl`/`got_conj` snapshotted BEFORE the `record("META-IDS",
    #      ...)` call that appends them, the assertion would sit outside the
    #      set it guards -- the pinned lists would be short by exactly
    #      META-IDS's own rows, and the two counts would never disagree.
    #  (b) nothing reconciling the pinned lengths with the HEADLINE tally, so
    #      the two numbers drift apart silently.
    # So the ID sets INCLUDE META-IDS's own rows (predicted exactly, since
    # `record` appends them deterministically), and `main` asserts the printed
    # totals against `len(EXPECTED_*)` after every row has been recorded.
    meta_parts = ["no_duplicate_obligations", "no_duplicate_conjuncts",
                  "obligations_exact", "conjuncts_exact",
                  "obligation_count", "conjunct_count"]
    got_obl = [r[0] for r in results] + ["META-IDS"]
    got_conj = [c[0] for c in conjuncts] + [f"META-IDS.{p}" for p in meta_parts]
    ok &= record("META-IDS", "CALC",
                 "the emitted obligation/conjunct ID sets are exactly the expected ones",
                 True,
                 f"{len(got_obl)} obligations, {len(got_conj)} conjunct rows "
                 f"(inclusive of META-IDS itself)",
                 parts=[
                     ("no_duplicate_obligations", len(set(got_obl)) == len(got_obl)),
                     ("no_duplicate_conjuncts", len(set(got_conj)) == len(got_conj)),
                     ("obligations_exact", sorted(set(got_obl)) == sorted(EXPECTED_OBLIGATIONS)),
                     ("conjuncts_exact", sorted(set(got_conj)) == sorted(EXPECTED_CONJUNCTS)),
                     ("obligation_count", len(got_obl) == len(EXPECTED_OBLIGATIONS)),
                     ("conjunct_count", len(got_conj) == len(EXPECTED_CONJUNCTS)),
                 ])
    missing_o = sorted(set(EXPECTED_OBLIGATIONS) - set(got_obl))
    extra_o = sorted(set(got_obl) - set(EXPECTED_OBLIGATIONS))
    missing_c = sorted(set(EXPECTED_CONJUNCTS) - set(got_conj))
    extra_c = sorted(set(got_conj) - set(EXPECTED_CONJUNCTS))
    if missing_o or extra_o or missing_c or extra_c:
        print(f"!! obligation IDs missing: {missing_o}")
        print(f"!! obligation IDs unexpected: {extra_o}")
        print(f"!! conjunct IDs missing: {missing_c}")
        print(f"!! conjunct IDs unexpected: {extra_c}")

    n = len(results); npass = sum(1 for r in results if r[3])
    nc = len(conjuncts); ncpass = sum(1 for c in conjuncts if c[1])
    # The HEADLINE numbers are reconciled against the pinned sets, and
    # against META-IDS's own prediction of what it was about to append.  This is
    # the assertion that terminates the self-reference: whatever META-IDS
    # concludes, the two printed totals must equal len(EXPECTED_*) exactly.
    tally_ok = (n == len(EXPECTED_OBLIGATIONS) and nc == len(EXPECTED_CONJUNCTS)
                and [r[0] for r in results] == got_obl
                and [c[0] for c in conjuncts] == got_conj)
    if not tally_ok:
        print(f"!! TALLY MISMATCH: reported {n} obligations / {nc} conjuncts, "
              f"pinned {len(EXPECTED_OBLIGATIONS)} / {len(EXPECTED_CONJUNCTS)}; "
              f"META-IDS predicted {len(got_obl)} / {len(got_conj)}")
        ok = False
    print("\n" + "=" * 78)
    print(f"{npass}/{n} obligations PASS in {time.time()-t0:.1f}s")
    print(f"{ncpass}/{nc} conjuncts PASS "
          f"(every conjunct of every obligation is reported and audited separately)")
    print(f"tally reconciled against the pinned ID sets: "
          f"{'YES' if tally_ok else 'NO — MISMATCH'}")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    rc = main()
    if "--print-ids" in sys.argv:
        print("\nEXPECTED_OBLIGATIONS = [")
        for r in results:
            print(f"    {r[0]!r},")
        print("]\nEXPECTED_CONJUNCTS = [")
        for c in conjuncts:
            print(f"    {c[0]!r},")
        print("]")
    sys.exit(rc)
