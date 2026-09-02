#!/usr/bin/env python3
# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
"""
META-PINS — source digests for the whole formal apparatus.

WHY.  A predicate rewritten to a tautology -- C6's to `MASK191 <= MASK191`, or
C7's to `eps < 2.0 ** -0` -- leaves every ID, description and evidence string
untouched, and the suite then reports a full green tally with exit 0 while
proving nothing.  Such a rewrite is invisible to any check that reads only the
suite's output.  The primary answer is DISCRIMINATION CONTROLS in
`verify_all.py`; this module is the second, syntactic layer: it digests the
source of the apparatus and asserts the digests against pinned tables.

THE THREAT CLASS.  A digesting scheme like this one is defeatable in several
independent ways, each of which turns on the same mistake -- *something the
apparatus executes, or something a check counts, is exempt from digesting*.  The
four gaps this design must close, and what each would otherwise permit:

  1.  A `_SKIP_MODULE_NAMES = ("EXPECTED_OBLIGATIONS", "EXPECTED_CONJUNCTS",
      "PINS")` list makes `regions()` `continue` on a module-level assignment to
      any of those names.  A single statement
          PINS = exec("<rebind record to always return True>", globals())
      inside the pinned file is then digested by nothing at all: 0 FAIL rows, a
      full green tally, `META-PINS ... every region digested against its pin`,
      exit 0, over a tree whose shipped `Q4_128` constant is wrong.
  2.  If `regions()` unparses the statements of a `FunctionDef.body` and never
      the `def` line, every module-level function's parameter list, defaults and
      decorators are unpinned.  `def record(..., bool=lambda _x: True)` then
      gives `all regions, 0 changed` and a green tally while a row prints [FAIL]
      (`record` prints `pok` but tallies `bool(pok)`).
  3.  If META-PINS is reached by an `import`, CPython runs
      `formal/z3/__pycache__/source_pins.cpython-310.pyc`, which no manifest
      need cover.  A `.pyc` whose payload is
      `def compute(paths): return dict(PINS)` makes every digest agree with
      itself, so a C6 gutted by SUBJECT SUBSTITUTION prints [PASS].
  4.  A check that prints `All {len(checks)} numeric claims agree` with no
      expected-name set is only as strong as the digest over its source: were
      such a file left unpinned, deleting nine `chk(...)` lines would still
      print `All 24 numeric claims agree` and exit 0 over the deleted checks.

WHAT THIS FILE NOW DOES.

1. NO EXEMPT REGION.  `_SKIP_MODULE_NAMES` is gone.  Every module-level
   statement of a pinned module is digested, including assignments to
   `EXPECTED_OBLIGATIONS` / `EXPECTED_CONJUNCTS` / `PINS`, and every function
   contributes a `::@@def` region holding its decorators and its `def` line.
2. WHOLE-FILE AST DIGEST.  Each pinned module also gets one `<label>::@@file`
   region: `sha256(ast.unparse(ast.parse(source)))`.  This has no per-statement
   structure to be exempt from, so any executable change to the file moves it,
   whatever shape the change takes.  It is what the TRUST ANCHOR in
   `verify_all.py` checks, hard, before the suite runs.
3. WHOLE-TREE FILE MANIFEST.  `FILES` byte-digests EVERY file under `formal/`
   except the four generated result files named in `GENERATED` -- checks,
   catalogues, Lean sources, docs.  The check is an ENUMERATION: a new file is a
   FAIL (`unpinned`), a deleted file is a FAIL (`missing`), a changed byte is a
   FAIL (`changed`).  That ensures no file under formal/ is covered by no digest.
4. NO BYTECODE MAY SHADOW SOURCE.  Any `*.pyc` anywhere under `formal/` is a
   violation, and `verify_all.py`'s anchor refuses to run at all if one exists
   for a module it loads.  Every entry point under `formal/` sets
   `sys.dont_write_bytecode` and exports `PYTHONDONTWRITEBYTECODE=1`, so none is
   ever created in normal operation.
5. THE THING VERIFIED IS THE THING EXECUTED.  `verify_all.py` does not `import`
   `source_pins` or `kernel_obligations`; it reads their bytes, digests those
   bytes, and `exec`s the text it digested.  `check()` is handed that registry
   and asserts, per module, that the executed bytes are the pinned bytes.

No EXEMPT region remains except the two the apparatus BLANKS on
purpose, and both of those are live -- each is arbitrary code covered by
nothing unless the inertness rule below is enforced:

  THE INERT-DATA ATTACK: the two pinned tables are blanked from the CODE and
         BYTES anchors so that `--write` cannot move them.  But a dict display
         is EXECUTABLE code -- Python evaluates every value expression and a
         duplicate key is simply overwritten -- so an unguarded blanked region
         is arbitrary code covered by NOTHING: not the four `ANCHOR_*` literals,
         not `SOURCE_PINS_CODE_SHA256`, not `FILES` (this file is
         SELF_UNPINNABLE), and by NOTHING else in the repository.  ONE line,
             'kernel_obligations::@@file': exec("<builtins.open shim>")
                                        or '6c4881578c83b0ca333dc7c6f671e694',
         is line-count-neutral (so the LINE-RANGE digest does not move) and
         leaves the table's value byte-identical, so it yields `anchor OK`
         with all four digests unchanged and ALL CHECKS PASS over a
         tree carrying a real defect in the shipped `Ntt.sol`.  ONE file,
         ONE line, ZERO hash literals, ZERO anchor movement -- against a
         documented floor of three files and four hash literals.
  THE DRIVER  Absent item 7 below, `formal/run_checks.sh` is pinned by exactly
         one row of that same blanked `FILES` table.  Rewriting check 1's
         invocation to inject an `open()` shim, plus that row, is TWO files, ONE
         hash literal and zero anchor movement -- and yields `ALL CHECKS PASS`.

6. WHAT IS BLANKED MUST BE PROVABLY INERT DATA.  `table_problems` refuses unless
   each table is a dict display whose every key and value is a string CONSTANT,
   assigned at column 0 with nothing else on its first or last line; the same
   rule, in `blank_check_script`, holds `run_checks.sh`'s six `ANCHOR_*=` lines to
   being nothing but hex/version string assignments.  All three independent
   blankers (here, `verify_all.py`'s anchor, `run_checks.sh` check 0) enforce it,
   and `META-PINS.blanked_regions_are_inert_data` reports it every run.
7. THE DRIVER IS PINNED OUTSIDE EVERY BLANKED REGION.  `check_script_digest()` is
   held as `RUN_CHECKS_SH_SHA256` in `verify_all.py` and as `ANCHOR_RUN_CHECKS_SH`
   in `run_checks.sh` itself.  The residue is stated in `hypotheses.py` §FV.6:
   whoever controls the driver controls the processes it launches, so the
   remaining attack is an interpreter shim visible in the driver's own diff, and
   running check 1 on its own (`python3 formal/z3/verify_all.py`) detects it.

WHAT IT STILL DOES NOT DO, precisely:
  * It is tamper-EVIDENCE, not tamper-proofing, and the bootstrap is finite.
    See `verify_all.py`'s TRUST ANCHOR block, FORMAL_VERIFICATION.md §2 ("What
    a pin actually pins") and §2f for the exact statement of what an attacker
    with write access to the repository can still do.
  * It says nothing about whether the code is CORRECT -- only that it is the
    code that was reviewed.  Correctness is the job of the obligations, their
    controls, and `vacuity_audit.py`.

Regenerate after a deliberate change:

    formal/z3/source_pins.py --print > /tmp/pins     (review, then hand-edit)
    formal/z3/source_pins.py --write                 (rewrites both tables)

`--write` locates the tables through the AST and REFUSES if either name is
assigned more than once at module level, then re-reads and re-parses what it
wrote and checks it round-trips.  Partitioning the source text on the first
literal `"PINS = {\\n"` would let a decoy table earlier in the file be
rewritten instead of the real one -- see `_rewrite_tables`.
"""
import argparse
import ast
import copy
import hashlib
import os
import posixpath
import re
import sys

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

HERE = os.path.dirname(os.path.abspath(__file__))


def _formal_root():
    """The `formal/` tree that `FILES` pins.

    PRIMARY: the parent of the directory this module is EXECUTING from, because
    that is the tree the running apparatus belongs to -- "the thing verified is
    the thing executed" applies to the manifest root as much as to the modules.
    FALLBACK: `$MLDSA_REPO/formal`, for the one case where the primary is wrong --
    `vacuity_audit.py` copies these three modules into a temp directory and tells
    them where the repository is, exactly as verify_all.py's REPO_ROOT does.
    Blindly using the parent there walked /var/folders/.../T and tripped over a
    unix socket; blindly using MLDSA_REPO makes the manifest follow an env var,
    which is the wrong default for a tamper check.
    """
    cand = os.path.abspath(os.path.join(HERE, ".."))
    if os.path.isfile(os.path.join(cand, "run_checks.sh")) \
            and os.path.isdir(os.path.join(cand, "lean")) \
            and os.path.isdir(os.path.join(cand, "z3")):
        return cand
    repo = os.environ.get("MLDSA_REPO")
    return os.path.join(os.path.abspath(repo), "formal") if repo else cand


FORMAL = _formal_root()

# A string constant that names an obligation: C1, C2a, C4[...], S6b, E11a, O9.
_OID_RE = re.compile(r"^(?:C|S|E|O)\d+[a-z]?(?:\[.*\])?$")
# Calls whose first argument is an obligation ID.
_RECORDERS = ("record", "pinned", "prove")
# PEP 263: a source encoding declaration other than utf-8 would make the bytes we
# digest decode differently from the text CPython compiles.
_COOKIE_RE = re.compile(rb"^[ \t\f]*#.*?coding[:=][ \t]*([-\w.]+)")

# The names whose module-level assignment in THIS file is the pinned table.  The
# trust anchor in verify_all.py blanks exactly these when it digests this file's
# CODE, so that regenerating the tables does not move the anchor constant (and so
# that the two files' digests have a fixpoint instead of an infinite regress).
TABLE_NAMES = ("PINS", "FILES")

# The check script, which `verify_all.py`'s anchor byte-pins with the six
# ANCHOR_* lines blanked -- the shell counterpart of the two tables above, and
# for the same fixpoint reason (those lines HOLD digests of verify_all.py).
CHECK_SCRIPT = "run_checks.sh"
CHECK_SCRIPT_BLANK = "@@ANCHOR BLANKED@@"
# A blanked line must be a hex/version STRING ASSIGNMENT and nothing else.  Same
# rule as `_inert_table_problems` below: what is exempt from a digest must be
# provably inert.
CHECK_ANCHOR_RE = re.compile(r'^ANCHOR_[A-Z0-9_]+="[0-9a-f. ]*"$')
CHECK_ANCHOR_COUNT = 6


# ---------------------------------------------------------------------------
# INERT-DATA CHECK  (inert-data hardening)
# ---------------------------------------------------------------------------
# THE INERT-DATA ATTACK: the two pinned tables are BLANKED before this file's CODE digest is
# taken -- deliberately, so that `--write` cannot move the anchor.  But a dict
# display is EXECUTABLE CODE: Python evaluates every value expression, and a
# duplicate key is simply overwritten.  ONE line
#
#     'kernel_obligations::@@file': exec("<install a builtins.open shim>") or
#                                '6c4881578c83b0ca333dc7c6f671e694',
#
# is line-count-neutral (so the LINE-RANGE digest does not move), leaves the
# table's final value byte-identical, and executes arbitrary code that no digest
# in this repository covers: not the four run_checks.sh anchors, not
# `SOURCE_PINS_CODE_SHA256`, not `FILES` (this file is SELF_UNPINNABLE), and
# by NOTHING else in the repository.
# The effect: `anchor OK`, all four digests unchanged, ALL CHECKS PASS, over a tree
# with a live defect in `Ntt.sol` -- ONE file, ONE line, ZERO hash literals.
#
# THE CLASS, stated so the fix can be checked against it: A PINNED FILE MUST
# HAVE NO REGION THAT IS BOTH EXECUTABLE AND EXEMPT FROM THE PIN.  Blanking a
# source region is only sound if that region is provably INERT DATA.  So the
# tables are no longer merely blanked -- they are first PROVED to be dict
# displays every one of whose keys and values is a string CONSTANT (no call, no
# f-string, no BoolOp, no comprehension, no `**`, no concatenation), starting at
# column 0 with nothing else on their first or last line.  Anything else is
# refused, by all three independent implementations of the blanker
# (`self_code_digest`/`self_code_bytes_digest` here, `_anchor_code_digest` in
# verify_all.py, `blank_tables_*` in run_checks.sh check 0).
def _inert_dict_problems(name, node, lines):
    """Why `name = {...}` is not provably inert data, as a list of strings."""
    bad = []
    value = node.value
    if not isinstance(value, ast.Dict):
        return [f"{name}: value is {type(value).__name__}, not a dict display"]
    for kind, items in (("key", value.keys), ("value", value.values)):
        for item in items:
            if item is None:                       # `**other` inside the display
                bad.append(f"{name}: `**` unpacking in the table")
                continue
            if not (isinstance(item, ast.Constant) and isinstance(item.value, str)):
                bad.append(f"{name}: line {getattr(item, 'lineno', node.lineno)}: "
                           f"{kind} is {type(item).__name__}, not a string literal "
                           "— the blanked region must be INERT DATA")
    if node.col_offset != 0:
        bad.append(f"{name}: assignment starts at column {node.col_offset}, not 0")
    head = lines[node.lineno - 1][:node.col_offset]
    tail = lines[node.end_lineno - 1][node.end_col_offset:]
    for where, frag in (("first", head), ("last", tail)):
        if frag.strip():
            bad.append(f"{name}: other code shares the table's {where} line "
                       f"({frag.strip()[:48]!r}) — the LINE-RANGE digest blanks "
                       "whole lines, so it would be exempt too")
    return bad


def table_problems(text, tree=None):
    """Everything wrong with this file's two pinned tables, as a list.

    Empty list == both tables are assigned exactly once at module level and are
    provably inert data whose blanking cannot hide code.
    """
    tree = tree or ast.parse(text)
    lines = text.split("\n")
    bad, seen = [], {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in TABLE_NAMES:
            nm = node.targets[0].id
            seen[nm] = seen.get(nm, 0) + 1
            bad += _inert_dict_problems(nm, node, lines)
    if sorted(seen) != sorted(TABLE_NAMES) or set(seen.values()) != {1}:
        bad.append(f"module-level table assignments {seen}; expected exactly one "
                   f"each of {list(TABLE_NAMES)}")
    return bad


def blank_check_script(text):
    """`formal/run_checks.sh` with its ANCHOR_* lines blanked, or raise.

    WHY THE DRIVER IS PINNED SEPARATELY.  `run_checks.sh` is the DRIVER, and a
    lone `FILES` row -- inside the blanked table -- is not enough to pin it:
    editing the driver and that one row is two files, one hash literal, and no
    anchor movement, and check 0 still prints `anchor OK` verbatim.
    `verify_all.py` therefore byte-pins the driver, so the driver is covered by
    a constant that is NOT in a blanked region.
    The ANCHOR_* lines themselves must be blanked -- they hold digests OF
    verify_all.py, so digesting them would be a cycle -- and they are held to the
    same inertness rule as the tables: each must be exactly a hex/version string
    assignment, and there must be exactly CHECK_ANCHOR_COUNT of them.
    """
    lines = text.split("\n")
    bad, n = [], 0
    for i, line in enumerate(lines):
        if not line.startswith("ANCHOR_"):
            continue
        n += 1
        if not CHECK_ANCHOR_RE.match(line):
            bad.append(f"{CHECK_SCRIPT} line {i + 1}: {line[:60]!r} is not a plain "
                       "hex/version string assignment — a blanked line must be "
                       "INERT DATA")
        lines[i] = CHECK_SCRIPT_BLANK
    if n != CHECK_ANCHOR_COUNT:
        bad.append(f"{CHECK_SCRIPT}: {n} ANCHOR_* lines, expected {CHECK_ANCHOR_COUNT}")
    if bad:
        raise SystemExit("\n".join("!! " + b for b in bad))
    return "\n".join(lines)


def check_script_digest(path=None):
    """The digest `verify_all.py`'s RUN_CHECKS_SH_SHA256 holds."""
    p = path or os.path.join(FORMAL, CHECK_SCRIPT)
    return _digest_bytes(blank_check_script(read_text(p)[1]).encode("utf-8"))

# The ONE build directory under formal/ that holds no source, given as a PATH
# RELATIVE TO formal/ and not as a bare name.  NOTE that `__pycache__` is
# deliberately NOT here: it is walked, so that every `*.pyc` in it is REPORTED
# (a payload can otherwise hide in exactly such a file) and so
# that any other file dropped into it is pinned like any other.
#
# WHY THE SKIP IS A PATH, NOT A NAME.  A `SKIP_DIRS = (".lake",)` matched
# against the bare directory NAME at ANY depth leaves
# `formal/z3/.lake/payload.py` -- a directory the Lean build never creates and
# that `check_axioms.py`'s throwaway-sandbox discipline says nothing about --
# invisible to `every_formal_file_pinned`.  The skip is therefore anchored to the
# exact relative path of the Lean package's build tree; a `.lake` anywhere else
# is walked and therefore FAILS as an unpinned file, which is the correct
# verdict for a build directory that has no build in it.
SKIP_REL_DIRS = ("lean/.lake",)
# The ONLY files under formal/ that `FILES` does not pin, because the checks
# themselves write them: their content is a RESULT, not an input.  They are
# reproduced by `run_checks.sh --full`.  Everything else under formal/ is pinned.
GENERATED = (
    "z3/vacuity_results.json",
    "mutation/mutation_results_final.json",
    "mutation/mutation_results_before.json",
    "mutation/halmos_results.json",
)
# THIS file cannot byte-pin itself: the pin is stored in the file, so writing it
# changes the bytes it claims to digest -- there is no fixpoint.  It is pinned
# instead by its CODE digest (this file's AST with `PINS` and `FILES` blanked),
# which IS a fixpoint and which is held in two other files:
#   * `SOURCE_PINS_CODE_SHA256` in formal/z3/verify_all.py (the trust anchor), and
#   * check 0 of formal/run_checks.sh, re-derived in a fresh `python -I -S`.
# Every statement of this file except the two table literals is therefore covered.
# What is NOT covered is the table CONTENT: an attacker who edits a pinned file
# can also edit its pin here.  That is the tamper-EVIDENCE boundary, and it is
# why the pins live in a second file and the anchor constants in a third.
SELF_UNPINNABLE = ("z3/source_pins.py",)
# The modules verify_all.py loads and executes; `check()` asserts that the bytes
# it executed are the bytes pinned here.
EXECUTED_MODULES = ("verify_all", "kernel_obligations", "source_pins")


def _ids_in(node):
    """Obligation IDs named by this statement, as a sorted tuple.

    Both `record("C6", ...)` (a literal first argument) and the loop forms
    `for oid, emax, tag in (("S1", ...), ("S2", ...)): prove(oid, ...)` are
    covered, the latter because the IDs still appear as string constants inside
    the statement.  An f-string ID (`f"C4[{name}]"`) contributes its literal
    prefix, so the five C4 instances share one region.
    """
    ids = set()
    for n in ast.walk(node):
        if isinstance(n, ast.Constant) and isinstance(n.value, str) \
                and _OID_RE.match(n.value):
            ids.add(n.value)
        elif isinstance(n, ast.Call) and isinstance(n.func, ast.Name) \
                and n.func.id in _RECORDERS and n.args:
            a0 = n.args[0]
            if isinstance(a0, ast.JoinedStr) and a0.values \
                    and isinstance(a0.values[0], ast.Constant):
                pref = a0.values[0].value
                if pref:
                    ids.add(pref)
    return tuple(sorted(ids))


def _digest(chunks):
    h = hashlib.sha256()
    for c in chunks:
        h.update(c.encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()[:32]


def ast_digest(text):
    """The digest of a module's ENTIRE executable content.

    Formatting, comments and quote style do not move it; every statement,
    signature, default and decorator does.  There is no per-statement bucket to
    be exempt from -- that is the point (exemptions 1 and 2 in the header).
    """
    return _digest([ast.unparse(ast.parse(text))])


def def_header(node):
    """`ast.unparse` of a function's decorators and `def` line, body elided.

    Digesting only `FunctionDef.body` leaves the signature unpinned, so that
    `def record(..., bool=lambda _x: True)` moves no digest (exemption 2 above).
    """
    clone = copy.deepcopy(node)
    clone.body = [ast.Pass()]
    return ast.unparse(ast.fix_missing_locations(clone))


def encoding_of(raw):
    """The PEP-263 source encoding declared in the first two lines, or None."""
    for line in raw.split(b"\n", 2)[:2]:
        m = _COOKIE_RE.match(line)
        if m:
            return m.group(1).decode("ascii", "replace").lower()
    return None


def raw_bytes(path):
    """`path`'s bytes, read through RAW FILE DESCRIPTORS, never `open`.

    Both the inert-data payload and the driver route work by installing a
    `builtins.open` shim and serving forged text to the checker.  Every read
    that decides whether something is the reviewed artefact goes through
    `os.open`/`os.read`, so replacing `builtins.open` is not enough.  It is
    defence-in-depth, not a boundary: a shim that also patches `os.read` wins,
    and no in-band check can stop that (hypotheses §FV.6).  Kept identical to
    `verify_all.raw_bytes`, deliberately duplicated -- neither file may depend
    on the other to read the bytes it is verifying.
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


def read_text(path):
    """(bytes, text) read exactly the way the digests and the loader read it."""
    raw = raw_bytes(path)
    return raw, raw.decode("utf-8")


def regions(label, text):
    """{region_key: digest} for one module's source `text`.

    Keys:
      `<label>::@@file`             the whole module's AST  (no exemptions)
      `<label>::<fn>::@@def`        a function's decorators + `def` line
      `<label>::<fn>::<ids>`        body statements naming those obligation IDs
      `<label>::<fn>::_rest`        the rest of that function's body
      `<label>::@class <name>`      a whole module-level class
      `<label>::@<name>`            a module-level assignment to one Name
      `<label>::@_module`           every other module-level statement
    """
    tree = ast.parse(text)
    buckets = {f"{label}::@@file": [ast.unparse(tree)]}

    def add(key, src):
        buckets.setdefault(key, []).append(src)

    for top in tree.body:
        if isinstance(top, (ast.FunctionDef, ast.AsyncFunctionDef)):
            fn = top.name
            add(f"{label}::{fn}::@@def", def_header(top))
            for stmt in top.body:
                ids = _ids_in(stmt)
                key = f"{label}::{fn}::" + ("+".join(ids) if ids else "_rest")
                add(key, ast.unparse(stmt))
        elif isinstance(top, ast.ClassDef):
            add(f"{label}::@class {top.name}", ast.unparse(top))
        elif isinstance(top, ast.Assign) and len(top.targets) == 1 \
                and isinstance(top.targets[0], ast.Name):
            add(f"{label}::@{top.targets[0].id}", ast.unparse(top))
        else:
            add(f"{label}::@_module", ast.unparse(top))
    return {k: _digest(v) for k, v in buckets.items()}


def compute(paths, texts=None):
    """{region_key: digest} over every pinned module.

    `texts` maps label -> the source text ACTUALLY EXECUTED for that label; when
    a label is present there, its text is digested instead of re-reading the
    file, so the digest is of the bytes that ran (exemption 3 in the header).
    """
    out = {}
    for label, path in paths:
        text = (texts or {}).get(label)
        if text is None:
            text = read_text(path)[1]
        out.update(regions(label, text))
    return out


def default_paths(verify_all_path=None):
    v = verify_all_path or os.path.join(HERE, "verify_all.py")
    d = os.path.dirname(os.path.abspath(v))
    return [("verify_all", os.path.abspath(v)),
            ("kernel_obligations", os.path.join(d, "kernel_obligations.py"))]


# ---------------------------------------------------------------------------
# The whole-tree file manifest
# ---------------------------------------------------------------------------
def walk_formal(root=None):
    """(pinned_files, pyc_files) under formal/.

    `pinned_files` maps a POSIX path relative to formal/ -> sha256 of the bytes.
    `pyc_files` is every `*.pyc` found, INCLUDING inside `__pycache__`: bytecode
    that shadows a pinned source is exemption 3 in the header, so it is reported rather
    than skipped.
    """
    root = os.path.abspath(root or FORMAL)
    if not os.path.isdir(root):                    # never a silent empty manifest
        raise OSError(f"the formal tree is not a directory: {root} "
                      "(set MLDSA_REPO if this copy is running outside the repo)")
    files, pycs = {}, []
    for dirpath, dirnames, filenames in os.walk(root):
        # Skip by RELATIVE PATH, not by bare name at any depth.
        here = os.path.relpath(dirpath, root)
        here = "" if here == "." else posixpath.join(*here.split(os.sep))
        dirnames[:] = [d for d in sorted(dirnames)
                       if (posixpath.join(here, d) if here else d) not in SKIP_REL_DIRS]
        for name in sorted(filenames):
            full = os.path.join(dirpath, name)
            rel = posixpath.join(*os.path.relpath(full, root).split(os.sep))
            if name.endswith((".pyc", ".pyo")):
                pycs.append(rel)
                continue
            if rel in GENERATED or rel in SELF_UNPINNABLE:
                continue
            if not os.path.isfile(full):           # sockets, fifos, dangling links
                raise OSError(f"not a regular file under formal/: {rel}")
            files[rel] = hashlib.sha256(raw_bytes(full)).hexdigest()[:32]
    return files, pycs


def encoding_problems(paths):
    """Pinned .py files whose PEP-263 cookie is not utf-8.

    The digests read bytes and decode utf-8; a different declared encoding would
    make CPython compile something else from the same bytes.
    """
    bad = []
    for label, path in paths:
        try:
            enc = encoding_of(read_text(path)[0])
        except OSError as exc:
            bad.append(f"{label}: {exc!r}")
            continue
        if enc is not None and enc.replace("_", "-") not in ("utf-8", "utf8"):
            bad.append(f"{label}: declared source encoding {enc!r}")
    return bad


CONJUNCTS = ("all_regions_pinned", "no_unpinned_regions",
             "every_region_digest_matches", "every_formal_file_pinned",
             "every_pinned_file_present", "every_formal_file_digest_matches",
             "no_bytecode_cache_under_formal",
             "executing_modules_are_the_pinned_bytes",
             "no_alternate_source_encoding",
             "blanked_regions_are_inert_data")
DESC = ("every source region, file and executed byte of the formal apparatus "
        "matches its pinned digest")


def failed_parts(reason):
    """The all-FAIL conjunct list, so a load or read error is never a silent skip."""
    return [(c, False) for c in CONJUNCTS], reason


def blanked_region_problems(self_path=None):
    """Everything that is BLANKED before a digest and is not provably inert.

    HARDENING NOTE.  The anchor in verify_all.py and check 0 both REFUSE on
    these, before anything runs; this conjunct exists so the same fact is also
    REPORTED, per run, in the tally an auditor reads.
    """
    p = self_path or os.path.abspath(__file__)
    bad = list(table_problems(read_text(p)[1]))
    gs = os.path.join(FORMAL, CHECK_SCRIPT)
    if os.path.isfile(gs):
        try:
            blank_check_script(read_text(gs)[1])
        except SystemExit as exc:
            bad.append(str(exc))
    return bad


def check(record, verify_all_path=None, loaded=None):
    """Record the META-PINS obligation.  Exactly ten conjuncts, always.

    `loaded` is verify_all.py's registry of the modules it EXECUTED:
        {label: {"path": ..., "sha256": ..., "ast": ..., "text": ...}}
    """
    loaded = loaded or {}
    try:
        paths = default_paths(verify_all_path)
        texts = {k: v["text"] for k, v in loaded.items() if "text" in v}
        got = compute(paths, texts)
        files, pycs = walk_formal()
        enc_bad = encoding_problems(paths)
        inert_bad = blanked_region_problems(
            (loaded.get("source_pins") or {}).get("path"))
    except Exception as exc:                       # never a silent skip
        parts, why = failed_parts(f"CANNOT DIGEST THE FORMAL TREE: {exc!r}")
        return record("META-PINS", "CALC", DESC, False, why, parts=parts)

    missing = sorted(set(PINS) - set(got))
    extra = sorted(set(got) - set(PINS))
    changed = sorted(k for k in set(got) & set(PINS) if got[k] != PINS[k])
    f_missing = sorted(set(FILES) - set(files))
    f_extra = sorted(set(files) - set(FILES))
    f_changed = sorted(k for k in set(files) & set(FILES) if files[k] != FILES[k])

    # the modules that ran must BE the pinned files, by byte digest and by AST
    exec_bad = []
    for label in EXECUTED_MODULES:
        info = loaded.get(label)
        if not info:
            exec_bad.append(f"{label}: not registered by the trust anchor")
            continue
        rel = posixpath.join("z3", label + ".py")
        if rel in SELF_UNPINNABLE:
            # this module has no FILES row (see SELF_UNPINNABLE); what CAN be
            # checked here is that nobody swapped the file between the anchor's
            # read and now, and that its CODE digest still equals the one the
            # anchor compared against its pinned constant.
            try:
                now = hashlib.sha256(read_text(info["path"])[0]).hexdigest()[:32]
            except OSError as exc:
                exec_bad.append(f"{label}: unreadable now: {exc!r}")
                continue
            if now != info.get("sha256"):
                exec_bad.append(f"{label}: file changed under the running process "
                                f"({info.get('sha256')} -> {now})")
            if info.get("code") != self_code_digest(info["path"]):
                exec_bad.append(f"{label}: CODE digest moved since the anchor "
                                f"checked it ({info.get('code')})")
            continue
        if FILES.get(rel) != info.get("sha256"):
            exec_bad.append(f"{label}: executed bytes {info.get('sha256')} "
                            f"!= pinned {FILES.get(rel)}")
        key = f"{label}::@@file"
        if PINS.get(key) != info.get("ast"):
            exec_bad.append(f"{label}: executed AST {info.get('ast')} "
                            f"!= pinned {PINS.get(key)}")

    parts = [
        ("all_regions_pinned", not missing),
        ("no_unpinned_regions", not extra),
        ("every_region_digest_matches", not changed),
        ("every_formal_file_pinned", not f_extra),
        ("every_pinned_file_present", not f_missing),
        ("every_formal_file_digest_matches", not f_changed),
        ("no_bytecode_cache_under_formal", not pycs),
        ("executing_modules_are_the_pinned_bytes", not exec_bad),
        ("no_alternate_source_encoding", not enc_bad),
        ("blanked_regions_are_inert_data", not inert_bad),
    ]
    assert [p[0] for p in parts] == list(CONJUNCTS)     # the ten, in order
    detail = (f"{len(got)} source regions / {len(files)} formal files digested "
              f"against {len(PINS)} region pins and {len(FILES)} file pins; "
              f"{len(GENERATED)} generated files excluded by name; the 2 blanked "
              f"tables and the {CHECK_ANCHOR_COUNT} blanked ANCHOR_* lines are "
              "inert data")
    if missing or extra or changed or f_missing or f_extra or f_changed \
            or pycs or exec_bad or enc_bad or inert_bad:
        detail = ("DIGEST MISMATCH — "
                  f"regions: missing {missing[:4]}, unpinned {extra[:4]}, "
                  f"CHANGED {changed[:4]}; files: missing {f_missing[:4]}, "
                  f"unpinned {f_extra[:4]}, CHANGED {f_changed[:4]}; "
                  f"bytecode {pycs[:4]}; executed {exec_bad[:3]}; "
                  f"encoding {enc_bad[:2]}; NOT INERT {inert_bad[:2]} "
                  "(regenerate with formal/z3/source_pins.py --write AFTER review)")
    return record("META-PINS", "CALC", DESC, True, detail, parts=parts)


# ---------------------------------------------------------------------------
# regeneration
# ---------------------------------------------------------------------------
def _table_span(src, name):
    """(lineno, end_lineno) of the ONE module-level `name = ...` assignment.

    Using `src.partition("PINS = {\\n")` would let the FIRST literal match win,
    so a decoy table earlier in the file would be rewritten while the real one
    went stale.  The span therefore comes from the AST, and more than one
    module-level assignment to `name` is an error rather than a silent choice.
    """
    hits = [n for n in ast.parse(src).body
            if isinstance(n, ast.Assign) and len(n.targets) == 1
            and isinstance(n.targets[0], ast.Name) and n.targets[0].id == name]
    if len(hits) != 1:
        raise SystemExit(f"source_pins.py: {len(hits)} module-level assignments to "
                         f"{name} (expected exactly 1) — refusing to rewrite")
    return hits[0].lineno, hits[0].end_lineno


def _render(name, table):
    return (f"{name} = {{\n"
            + "".join(f"    {k!r}: {table[k]!r},\n" for k in sorted(table))
            + "}\n")


def _rewrite_tables():
    self_path = os.path.abspath(__file__)
    want = {"PINS": compute(default_paths()), "FILES": walk_formal()[0]}
    # rewrite the LATER table first so the earlier one's line span stays valid
    src = read_text(self_path)[1]
    spans = sorted(((_table_span(src, n)), n) for n in TABLE_NAMES)
    for (lo, hi), name in reversed(spans):
        lines = src.splitlines(keepends=True)
        src = "".join(lines[:lo - 1]) + _render(name, want[name]) + "".join(lines[hi:])
    with open(self_path, "w", encoding="utf-8") as fh:
        fh.write(src)
    # HARDENING NOTE: round-trip.  Re-read, re-parse, and CHECK that the tables we meant
    # to write are the tables the file now defines -- a decoy or a mis-sliced span
    # shows up here rather than as a stale pin that still passes.
    back = read_text(self_path)[1]
    tree = ast.parse(back)
    for name in TABLE_NAMES:
        node = [n for n in tree.body
                if isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == name]
        if len(node) != 1:
            raise SystemExit(f"source_pins.py: --write produced {len(node)} "
                             f"assignments to {name}; ABORTING (file may be corrupt)")
        if ast.literal_eval(node[0].value) != want[name]:
            raise SystemExit(f"source_pins.py: --write did NOT round-trip for {name}; "
                             "ABORTING (file may be corrupt)")
    print(f"source_pins.py: rewrote {len(want['PINS'])} region pins and "
          f"{len(want['FILES'])} file pins (round-trip verified)")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--print", action="store_true", dest="do_print")
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--code-digest", action="store_true",
                    help="print this file's CODE digest (tables blanked) — the "
                         "constant verify_all.py's trust anchor holds")
    ap.add_argument("--anchors", action="store_true",
                    help="print every anchor constant for formal/run_checks.sh check 0")
    ap.add_argument("--check-script-digest", action="store_true",
                    help="print run_checks.sh's digest (ANCHOR_* lines blanked) — "
                         "the constant verify_all.py's RUN_CHECKS_SH_SHA256 holds")
    args = ap.parse_args()
    if args.code_digest:
        print(self_code_digest())
        return 0
    if args.anchors:
        va = os.path.join(HERE, "verify_all.py")
        print(f"ANCHOR_VERIFY_ALL_AST={ast_digest(read_text(va)[1])}")
        print(f"ANCHOR_SOURCE_PINS_CODE={self_code_digest()}")
        print(f"ANCHOR_VERIFY_ALL_BYTES={_digest_bytes(read_text(va)[0])}")
        print(f"ANCHOR_SOURCE_PINS_BYTES={self_code_bytes_digest()}")
        print(f"ANCHOR_RUN_CHECKS_SH={check_script_digest()}")
        return 0
    if args.check_script_digest:
        print(check_script_digest())
        return 0
    if args.write:
        _rewrite_tables()
        return 0
    got = compute(default_paths())
    files, pycs = walk_formal()
    if args.do_print:
        sys.stdout.write(_render("PINS", got))
        sys.stdout.write(_render("FILES", files))
        return 0
    rc = 0
    for label, table, pinned in (("region", got, PINS), ("file", files, FILES)):
        for k in sorted(set(pinned) - set(table)):
            print(f"!! {label} disappeared: {k}"); rc = 1
        for k in sorted(set(table) - set(pinned)):
            print(f"!! {label} not pinned:  {k}"); rc = 1
        for k in sorted(set(table) & set(pinned)):
            if table[k] != pinned[k]:
                print(f"!! {label} CHANGED:     {k}"); rc = 1
    for p in pycs:
        print(f"!! BYTECODE under formal/ (may shadow a pinned source): {p}"); rc = 1
    for e in encoding_problems(default_paths()):
        print(f"!! {e}"); rc = 1
    for e in blanked_region_problems():
        print(f"!! NOT INERT: {e}"); rc = 1
    print(f"{len(got)} regions / {len(files)} files digested against "
          f"{len(PINS)} region pins / {len(FILES)} file pins; "
          f"{len(pycs)} bytecode file(s) under formal/")
    print(f"code digest of this file (tables blanked): {self_code_digest()}")
    print(f"digest of {CHECK_SCRIPT} (ANCHOR_* lines blanked): {check_script_digest()}")
    return rc


def self_code_digest(path=None):
    """This file's AST digest with the pinned tables BLANKED.

    `verify_all.py`'s trust anchor holds this value as a literal, computes it
    itself from the bytes it is about to execute, and refuses to run on a
    mismatch.  Blanking the tables is what gives the two files' mutual pins a
    fixpoint: regenerating PINS/FILES cannot move this digest, so `--write` never
    invalidates the anchor and the anchor never invalidates `--write`.

    This function is a CONVENIENCE for `--code-digest`; the anchor does NOT call
    it (it must not trust this file to describe itself) -- it recomputes the same
    thing in ~12 self-contained lines.  Keep the two in step.
    """
    text = read_text(path or os.path.abspath(__file__))[1]
    tree = ast.parse(text)
    bad = table_problems(text, tree)                # blank only INERT DATA
    if bad:
        raise SystemExit("\n".join("!! " + b for b in bad))
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in TABLE_NAMES:
            node.value = ast.Dict(keys=[], values=[])
    return _digest([ast.unparse(ast.fix_missing_locations(tree))])


def _digest_bytes(raw):
    return hashlib.sha256(raw + b"\0").hexdigest()[:32]


def self_code_bytes_digest(path=None):
    """This file's RAW TEXT with the two tables' LINE RANGES blanked.

    HARDENING NOTE.  `ast.unparse`'s output is
    CPython-version-dependent: 3.9.6 and 3.10.4 agree on this repository's
    anchor, 3.11.15 does not.  Check 0 now re-derives the anchors under a
    BOOTSTRAP interpreter found outside the repository, whose version it does
    not get to choose, so it needs a digest that every version agrees on.
    `ast.parse` line numbers ARE stable across versions, so blanking the two
    table assignments by LINE RANGE and digesting the remaining raw text is the
    version-independent counterpart of `self_code_digest`.  Both are checked;
    the AST one only where the running version is in the anchored set.

    Keep this in step with `blank_tables_text` in run_checks.sh check 0, which
    recomputes the same thing in ~12 self-contained lines (the anchor must not
    trust this file to describe itself).
    """
    text = read_text(path or os.path.abspath(__file__))[1]
    tree = ast.parse(text)
    lines = text.split("\n")
    bad = table_problems(text, tree)                # blank only INERT DATA
    if bad:
        raise SystemExit("\n".join("!! " + b for b in bad))
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in TABLE_NAMES:
            for i in range(node.lineno - 1, node.end_lineno):
                lines[i] = "@@TABLE BLANKED@@"
    return _digest_bytes("\n".join(lines).encode("utf-8"))


# ---------------------------------------------------------------------------
# The pinned tables.  Regenerate with `--write` ONLY after reviewing the diff.
# Exactly one module-level assignment each: `--write` and the trust anchor both
# refuse if there are more (a decoy table would otherwise shadow the real one).
# ---------------------------------------------------------------------------
PINS = {
    'kernel_obligations::@@file': 'd77cd23da6bc360b30d4a56a1c7cfeff',
    'kernel_obligations::@D2G': 'e50846c5078a01b50ab11a43a6dd928f',
    'kernel_obligations::@GAMMA2': 'adca3d86d6523628d64ff94648654d7b',
    'kernel_obligations::@KQ28': '032bbee29c93d8595ec3d95bc992208f',
    'kernel_obligations::@M256': 'a733fbad0676303146627a91094aa5bf',
    'kernel_obligations::@M64': '506ea7b72ecce47fed1c46da7ba8d0b9',
    'kernel_obligations::@MV_KQ28REP': '2bab5a4aaba635afdacbcbbaf5d0f3f6',
    'kernel_obligations::@PK_AMAX': '065a3054e096241b20b532ea1f73a49d',
    'kernel_obligations::@Q': 'f81a02363242d1571ad6c864704172a6',
    'kernel_obligations::@SMT_TIMEOUT_MS': 'de4b3d501ce025bd94468e8497b596f9',
    'kernel_obligations::@SW_GATHERK': 'ca7ac6010081efc26a7b4b0e19a55057',
    'kernel_obligations::@SW_K321': 'c14811c6fbcd9be1ce972130f7736c7c',
    'kernel_obligations::@SW_K32G2': 'ff778dfbc2cc255ebd1728f2c9cd574e',
    'kernel_obligations::@SW_M44': '0ea94d3567330731fae24e849d35914b',
    'kernel_obligations::@SW_M44_SHIFT': 'ce6459ac7aa49aae079657b4c2b2b8d8',
    'kernel_obligations::@SW_MDIV': '3ea52dfda4276f714dd7457ed5494cc6',
    'kernel_obligations::@SW_REP1': 'fb11e1de04783d001b600dcab703e9d4',
    'kernel_obligations::@SW_REP6': '3008cde09e47f3c636eed2934ab3710f',
    'kernel_obligations::@SW_SHIFT': '0d23a63dadb314af38528f2df185846a',
    'kernel_obligations::@SW_T_MAX': 'b007c895f1a1529ad67bfdd3a4b264ec',
    'kernel_obligations::@ZMAX': '6bf26970f7c8d920b4fea45d4fd131fe',
    'kernel_obligations::@Z_M18_DEC': 'dab4d64985a6d4c4274dd8387e1df6f3',
    'kernel_obligations::@Z_MUL_PAIRS': '2c9885724f1e41c0d1fc6c2e0dfd08e5',
    'kernel_obligations::@Z_TERMS': '7025ca2b1bb6bac062388ea2a01134fd',
    'kernel_obligations::@_module': '1f46fe3999fbe1a4957c5c75a5d73a55',
    'kernel_obligations::@conjuncts': 'd372712e919417ec4c216192d92117fb',
    'kernel_obligations::@results': '4c264bdeaa919eefdfe2c7f3d8c29370',
    'kernel_obligations::_bytewise_additive::@@def': 'b2d843fd5a1ab6fbd3102afbc59cf2bd',
    'kernel_obligations::_bytewise_additive::_rest': 'd9067f6c719e5234aa7a64ec4afeaccf',
    'kernel_obligations::_extract_fips::@@def': 'd00e8f140ce8266b93f41e264e6e7779',
    'kernel_obligations::_extract_fips::_rest': 'f71ff818eaa717d230c41cc465344244',
    'kernel_obligations::_extract_shipped::@@def': '50aee5046a1f053db532103e78fa4f64',
    'kernel_obligations::_extract_shipped::_rest': '6f8f11b0132b5c4b556203707b382067',
    'kernel_obligations::_fused_constants_are_the_two_powers::@@def': '34a6e75253342de4a120cc1913cd357b',
    'kernel_obligations::_fused_constants_are_the_two_powers::_rest': '2bf74e1d661df678c28c854d039d1c0e',
    'kernel_obligations::_fused_multiply_is_the_two_terms::@@def': 'd9679ad570ad74dc497051bc0d0cd7d5',
    'kernel_obligations::_fused_multiply_is_the_two_terms::_rest': '44f193408b82456b6ec87017b518624c',
    'kernel_obligations::_lanes_roundtrip::@@def': '6e2c70483305b7b5abe47705e21365be',
    'kernel_obligations::_lanes_roundtrip::_rest': 'c220b2f008e7d608dffb742492b0b6bb',
    'kernel_obligations::_mul_pairs_are_the_doubled_terms::@@def': '9fba223898d0c1a66c8f95f9833b0253',
    'kernel_obligations::_mul_pairs_are_the_doubled_terms::_rest': '7b75427118baab6d5fd2f46b480d72f9',
    'kernel_obligations::_prem_sat::@@def': '1ac04e7e4a41484c0542be24fc7cd421',
    'kernel_obligations::_prem_sat::_rest': '89dedeeabe2d9dd7322ba978add2db97',
    'kernel_obligations::_refutable::@@def': 'b1c7d48334db9d0efa0cede930b5f7bf',
    'kernel_obligations::_refutable::_rest': 'bd214fbad02ee92208bda81dcc13c68a',
    'kernel_obligations::_solver::@@def': '70a92e39f3684646c1a0d8e663dca366',
    'kernel_obligations::_solver::_rest': 'a79ebae94f1cdcd5075b1bfc800c24bc',
    'kernel_obligations::_swar_div_exact::@@def': '043e4d926d14f92844523c33379f057b',
    'kernel_obligations::_swar_div_exact::_rest': '80ad5ffa5aa8aee7f609f10f149951ef',
    'kernel_obligations::_sweep_exact::@@def': '20fcc7a60c380ae5764a33acbbc7a4bc',
    'kernel_obligations::_sweep_exact::_rest': 'b0eb6f89d3a36c0d0c75e5ef75f1b3ee',
    'kernel_obligations::_terms_disjoint::@@def': '68938aff89c751276c99f86d894c39ea',
    'kernel_obligations::_terms_disjoint::_rest': '6f4eca050f0fba788f7e17336757fd13',
    'kernel_obligations::_terms_inside_the_word::@@def': '74a24e525de3fc384da88e18b3b3e25f',
    'kernel_obligations::_terms_inside_the_word::_rest': '30733af5f884c2ed4551c31677ff7731',
    'kernel_obligations::_truth::@@def': 'a501f2213426724c44a9abe965f8ea47',
    'kernel_obligations::_truth::_rest': 'ddffeec68f130b10fc4c26a9c5ae030f',
    'kernel_obligations::controls::@@def': '28583f79729f6d0077ec074d8ecafac4',
    'kernel_obligations::controls::_rest': '1e6975719afd050b7a0e183944b9b621',
    'kernel_obligations::decompose::@@def': '00f61d4c5b808ea906526878f82cb430',
    'kernel_obligations::decompose::_rest': 'b47083f0739cb40f91beaa6283d83be5',
    'kernel_obligations::main::@@def': 'ae338532d5fa14df45706c4e15dc5ec6',
    'kernel_obligations::main::_rest': '5c0473d4b560eaa465b35fdcbb23b94c',
    'kernel_obligations::o10_packed_field_extraction::@@def': 'f37a85cda7062152c431ffafb2431c7e',
    'kernel_obligations::o10_packed_field_extraction::O10': '60029bcfa8ce270a415ba1eff4d19493',
    'kernel_obligations::o10_packed_field_extraction::_rest': '678e1ec711405678632f544d12d89b1b',
    'kernel_obligations::o1_division_constant::@@def': 'beb172e95ef04df6083baccd7b32bbe4',
    'kernel_obligations::o1_division_constant::O1': 'e180f09599173ddb2610790e37a1e849',
    'kernel_obligations::o2_no_cross_lane_carry::@@def': 'caba33539444fa7265884cbbdb6e99de',
    'kernel_obligations::o2_no_cross_lane_carry::O2': '77e461b133e420c3f90307e9d14e2c65',
    'kernel_obligations::o2_no_cross_lane_carry::_rest': '2e37734bb0a8ee9a4d7c4345c6ab704e',
    'kernel_obligations::o3_ge_comparator::@@def': '5981be973278902beffa111d3d6088e3',
    'kernel_obligations::o3_ge_comparator::O3': '374979a911d7f4303c2c6865e7e03135',
    'kernel_obligations::o3_ge_comparator::_rest': '2e5b14098dd9c772a86d98edfb5d0964',
    'kernel_obligations::o4_mod44::@@def': '97999744e5bb55cf917139605ff55e79',
    'kernel_obligations::o4_mod44::O4': '4162c473060059abbb7c27c057863dde',
    'kernel_obligations::o4_mod44::_rest': 'b1d705a748abc3af655d20fe61cdf1d2',
    'kernel_obligations::o5_multiply_gather::@@def': 'cae2810261eeceb94c7499da2cfeafa2',
    'kernel_obligations::o5_multiply_gather::O5': '41fd64830e4b93a2fb3fa7f6d4de5ade',
    'kernel_obligations::o5_multiply_gather::_rest': '3568f532e0ba2856411a08b9a589235f',
    'kernel_obligations::o6_usehint_equivalence::@@def': '0433b50fd5cfae9ea9587674de089dee',
    'kernel_obligations::o6_usehint_equivalence::O6': '119d9e6970aac7595733f2e1ea745b21',
    'kernel_obligations::o6_usehint_equivalence::_rest': '4d831c0910347edebf8962ee4da8f30b',
    'kernel_obligations::o7_preshifted_lane_product::@@def': '04a72b62a80225f3a8c697e585daa888',
    'kernel_obligations::o7_preshifted_lane_product::O7': 'c4bb9993df70f0989978e92c3a880c37',
    'kernel_obligations::o7_preshifted_lane_product::_rest': 'aa892e93d0b174dd9c8a73e637e8a201',
    'kernel_obligations::o8_accumulator_bounds::@@def': '94765ee1f04466f7d504c05df7d968a0',
    'kernel_obligations::o8_accumulator_bounds::O8': '010ea3755e07c9be3835c6323d2f63d3',
    'kernel_obligations::o8_accumulator_bounds::_rest': '37e96d9cfefd8e9825e2859d457ad35b',
    'kernel_obligations::o9_packed_store_disjoint::@@def': 'c361bd926e087aa82735005b02cfb9e6',
    'kernel_obligations::o9_packed_store_disjoint::O9': '1e35b9f0869026bede72bf12dd4de165',
    'kernel_obligations::o9_packed_store_disjoint::_rest': 'a2334991024ddebfc6f93baeac6a4b44',
    'kernel_obligations::pinned::@@def': '388ce8d6fa0029dff494591518658d3b',
    'kernel_obligations::pinned::_rest': '0829a3fa82f24cd63e2774f0182c2cb4',
    'kernel_obligations::record::@@def': '4263a229dbc55cd6081624a23299b5cc',
    'kernel_obligations::record::_rest': '75b2f506945dd665e95e91442a41315f',
    'kernel_obligations::swar_word::@@def': '7fb3a72cd1127966e78fec8b9b7fa106',
    'kernel_obligations::swar_word::_rest': '7626edbc628d00758b4ea492f0ff651b',
    'kernel_obligations::use_hint::@@def': '747de1d7cf959b0977e3ea22b753e51f',
    'kernel_obligations::use_hint::_rest': '4e6b64a9812a0989cf59da6f1998c37e',
    'verify_all::@@file': 'b6a32774ab13a4b8f86c90b264060e12',
    'verify_all::@BETA': 'e9fb47b6f47fe7f2d7fbe8289e2181e4',
    'verify_all::@D_SHIFT': 'ad3523b916bccd8f59fa2c8506abf700',
    'verify_all::@EXPECTED_CONJUNCTS': 'ddd102378d9e765399f737132ec97129',
    'verify_all::@EXPECTED_OBLIGATIONS': '7857dabea289b0ba990a1897c2d72580',
    'verify_all::@GAMMA1': '322d19097b1229b5e5d6899ba35227ba',
    'verify_all::@GAMMA2': 'adca3d86d6523628d64ff94648654d7b',
    'verify_all::@LOADED_MODULES': '13d9c50ca4a355b8ff6c5405cf29332b',
    'verify_all::@L_DIM': '86058045905df342b1ef38b6bca29c75',
    'verify_all::@MU23': '8fffe669d7e2f1f259b06d888f05e1ba',
    'verify_all::@MU33': '39063ee6124862c24a3ffc85f8a53256',
    'verify_all::@N': '2f5c9ea07964289d1d6aae698c3a1e8e',
    'verify_all::@OMEGA': '0cc7db6051005464e74400a035234614',
    'verify_all::@PK_AMAX': '065a3054e096241b20b532ea1f73a49d',
    'verify_all::@Q': 'f81a02363242d1571ad6c864704172a6',
    'verify_all::@REPO_ROOT': 'dd47882bf5d2f6fb8e08c1a0cfeec58e',
    'verify_all::@RUN_CHECKS_SH_SHA256': 'e436717a327b65af6f9195f08b72079d',
    'verify_all::@SH1': '9731ff3ebe1276e67d0c2aa69d38196e',
    'verify_all::@SH2': '49d3a59cb316e3de923f4d8a73670d0c',
    'verify_all::@SMT_TIMEOUT_MS': 'de4b3d501ce025bd94468e8497b596f9',
    'verify_all::@SOURCE_PINS': 'a478ef02de31506c51a7a0516711bdf3',
    'verify_all::@SOURCE_PINS_CODE_SHA256': '02209ef3d455e5c40f16ed21d8771cbb',
    'verify_all::@TAU': '07c0940d167eb255f0c3b65e83ba7b11',
    'verify_all::@Z_NHI_LANE': '0b4889905f0a5b47ddfb16641a2d11bc',
    'verify_all::@Z_NLO_LANE': '992aa3a9699d86da3aa3a9a1f3819a21',
    'verify_all::@Z_QB32_LANE': '5474247a61b1b49fbba064548b2aa68e',
    'verify_all::@Z_UOFF_LANE': 'f13ff9941af5c723524f3f787758d48b',
    'verify_all::@_ANCHOR_CHECK_LINES': '8fbda70cdeb5695b44fc64ed980ed48e',
    'verify_all::@_ANCHOR_CHECK_RE': '5b55813a6a624640aa8ae82dfd2a4c4c',
    'verify_all::@_ANCHOR_CHECK_SCRIPT': 'f77b4a2b86d9916b0903922b441396b2',
    'verify_all::@_ANCHOR_DIR': 'dbd0603ef0d5eb515456a76385d31c3f',
    'verify_all::@_ANCHOR_MODULES': 'a1ea6ac5ecf003fea0a0b7a6e2b072c9',
    'verify_all::@_ANCHOR_TABLES': '8c460fad2cadda7590e1d4ff6ed65499',
    'verify_all::@_module': 'ced8f7c24e413a6e13f99b5bf50a9364',
    'verify_all::@conjuncts': 'd372712e919417ec4c216192d92117fb',
    'verify_all::@results': '4c264bdeaa919eefdfe2c7f3d8c29370',
    'verify_all::_abort_with_fail_rows::@@def': '818624a22039a7403aaff97a66d853cd',
    'verify_all::_abort_with_fail_rows::_rest': '42a76cc2762b76bc41f4cc298f06e965',
    'verify_all::_anchor::@@def': 'c56c08c7c20feaf360d2bcc57ffa2986',
    'verify_all::_anchor::_rest': 'ffb83cfbfe3dec58deccc2c4549066ba',
    'verify_all::_anchor_check_script::@@def': 'bf8d44ab7e9c71667dafe614daf987f3',
    'verify_all::_anchor_check_script::_rest': '1744e46750195a3debf19a32c64d3e2b',
    'verify_all::_anchor_code_digest::@@def': '95a216f90e0f35459dff24b4b813766b',
    'verify_all::_anchor_code_digest::_rest': 'ff9f79285c4d53dc4d3979e14b3861de',
    'verify_all::_anchor_digest::@@def': 'a12d262cd709a755bd0afee1e62cca87',
    'verify_all::_anchor_digest::_rest': '4f68138e56e30adf53a00c1e17f32a30',
    'verify_all::_anchor_exec::@@def': '3900a23a996d7dc443935e33ae6d2aff',
    'verify_all::_anchor_exec::_rest': 'adba390dcc6db5ac273e2367641f553e',
    'verify_all::_anchor_no_shadowing_bytecode::@@def': '9a85b9130d1006c0547dc5357b1303c6',
    'verify_all::_anchor_no_shadowing_bytecode::_rest': 'db9acf5db7633c797940ffa19f5f93a2',
    'verify_all::_anchor_read::@@def': '020e88593c1197b96a6826f6d39df2a0',
    'verify_all::_anchor_read::_rest': 'c63b20db2002197c1db66169d928282b',
    'verify_all::_anchor_refuse::@@def': '33e9af931c138777f3f6e7557548b4d8',
    'verify_all::_anchor_refuse::_rest': '9358dccd9c72131f4e19787e7ece4916',
    'verify_all::_is_prime_bpsw::@@def': '37f18a350e307f4daea3e84fa6ea509f',
    'verify_all::_is_prime_bpsw::_rest': '8bfad1deb6018b9b9dcb1f05de090851',
    'verify_all::_jacobi::@@def': '3ce8d19ac30f76c7aa58fa7d61d312b0',
    'verify_all::_jacobi::_rest': 'ba44b3579cafaa7b4eb5b510066b04d8',
    'verify_all::_mr_witness::@@def': '92d5bff679d524ee06082002c580e7d3',
    'verify_all::_mr_witness::_rest': 'ff17723493a8e9ced9e9091e37a3c4fa',
    'verify_all::_strong_lucas_prp::@@def': 'ef745a4b43557143914dc67210f85230',
    'verify_all::_strong_lucas_prp::_rest': 'f61ebd832232361fff3f2bc49d86381a',
    'verify_all::_syntactically_trivial::@@def': 'be997388425ac6e44f1276385cd3d893',
    'verify_all::_syntactically_trivial::_rest': '15dc34c29c9999684aad875df96f16be',
    'verify_all::_truth::@@def': 'a501f2213426724c44a9abe965f8ea47',
    'verify_all::_truth::_rest': '4f124b8e1a8c217261609e0a30d9fac5',
    'verify_all::acc_entry::@@def': '1ec761c9beeb63cac31ef77c7ed1709d',
    'verify_all::acc_entry::_rest': 'fcff6afbeb14fb09eed1311ac36b3a05',
    'verify_all::calc_obligations::@@def': '6cc742ea4a6330f9588867f394b4885f',
    'verify_all::calc_obligations::C1': 'f092b49f4a4fa09482b21e60d779b6cf',
    'verify_all::calc_obligations::C10': 'ab2da76ef6e56b21a4d3f957ce5e6fcf',
    'verify_all::calc_obligations::C10b': '1fcd16acc78fc8efb65cea3c09c90650',
    'verify_all::calc_obligations::C11a': 'e9c51279b1bf62bc97aa9e76ab786e7b',
    'verify_all::calc_obligations::C11b': 'bb6ce5c9058114ba8e1b9701857608a6',
    'verify_all::calc_obligations::C11c': 'e08f0865f68d75cc4e559e84bb9f36eb',
    'verify_all::calc_obligations::C11d': '35c5ef6d28af1c40d591ced282bf9ab1',
    'verify_all::calc_obligations::C15b': '50a6f7ef8447c951598991cfda6318f9',
    'verify_all::calc_obligations::C15c': 'd557ce8f16954fe6519409b1d4f23c5c',
    'verify_all::calc_obligations::C16': 'c1cfddb10694e1318565e62da2601e65',
    'verify_all::calc_obligations::C17': '8802150c97fdc3646b73e508dfd790f1',
    'verify_all::calc_obligations::C18': '5a38d129a9117e946bc7c4039be20ec3',
    'verify_all::calc_obligations::C1b': '987ed86bc1803b1e0247906d2b000edf',
    'verify_all::calc_obligations::C9a': 'd418d24f3708331d37756cd1f6d5beaf',
    'verify_all::calc_obligations::C9b': '7be04ad28d75545216a615ca35a2dad1',
    'verify_all::calc_obligations::C9c': '8fa79002a3e8fb214d91e425af011a9e',
    'verify_all::calc_obligations::C9d': '1442a2e8446279cd4324dba4ea290922',
    'verify_all::calc_obligations::C9e': 'e1cb01ac25228adff2af08783f6774a8',
    'verify_all::calc_obligations::C9f': 'fe5260d1ded92fa5b6314a95434d37f0',
    'verify_all::calc_obligations::C9g': '87c79d72efa08ef66ebdcf0de31d5587',
    'verify_all::calc_obligations::C9h': '08a70cb4defcc14e5980249e67950bc4',
    'verify_all::calc_obligations::E15': '5e2675003c526b62b1aafb114befd997',
    'verify_all::calc_obligations::_rest': '87ddd6b5d47692c9a2c378416963c6d0',
    'verify_all::controls::@@def': '28583f79729f6d0077ec074d8ecafac4',
    'verify_all::controls::_rest': 'a9e84aa4abf4cd0592c2eccb769c563c',
    'verify_all::entry_offset_dominates::@@def': 'f1dc1a2fc493cec780edc3ebcc2e5f57',
    'verify_all::entry_offset_dominates::_rest': 'edba7cf6437bf78aa23ccf181bc69ea7',
    'verify_all::exh_obligations::@@def': 'b1d55d04d2fe019ccc8b473f4000259d',
    'verify_all::exh_obligations::E1': 'dcedf686dff3f053584fa685e8e63592',
    'verify_all::exh_obligations::E12': 'f5d42c9f6b488a44fe6a59089dcf2ca5',
    'verify_all::exh_obligations::E13': '1c28f0893825b3e719ef70585d942298',
    'verify_all::exh_obligations::E14': '4045fff23dff6e6db1218698e35cddc2',
    'verify_all::exh_obligations::E2': '46f763dfce17a9f3414dba8ca8469051',
    'verify_all::exh_obligations::E3': '243edf0f00e6ba85a4c4927b25203e02',
    'verify_all::exh_obligations::E3b': '37b9338a12138480ac34a5c0d98b3ffa',
    'verify_all::exh_obligations::E4': '613ff410a75ff158b541ced5ac66401c',
    'verify_all::exh_obligations::E4b': '08afbc5435ec84196bf2ea25cda8a2c3',
    'verify_all::exh_obligations::E5': 'f3d0681860a6a11249b88c11c8a51ee6',
    'verify_all::exh_obligations::E5b': 'f809710abe875b8953b0f9a2ec7bbc2f',
    'verify_all::exh_obligations::E6': '5fb073ad1d95fccb7a1e6f1b1a48277d',
    'verify_all::exh_obligations::E9a+E9b': '170eed1b7b427729fcdded20fc29f954',
    'verify_all::exh_obligations::_rest': '34bd32d900e2a8970dd3f71bd698d891',
    'verify_all::kern_barrett::@@def': '44d8b719ea8554389dcba9260b62e39e',
    'verify_all::kern_barrett::_rest': 'a6e5d5105c6497368addd72fc787a02b',
    'verify_all::kern_use_hint::@@def': 'ada863dd2c0e9a97ab90afbe94375a84',
    'verify_all::kern_use_hint::_rest': '7917c0d3f0cee6f9b083fe9a68d0dfa3',
    'verify_all::kern_z_canon_swar::@@def': '2f82c96752e318c94a6f835ae1a60950',
    'verify_all::kern_z_canon_swar::_rest': 'de3e4705745e54268be4fe534407019e',
    'verify_all::kern_z_centered_strict::@@def': 'dd447fbd518dd32ae6761e026fcf5f9e',
    'verify_all::kern_z_centered_strict::_rest': '96d6b51e2f2159cff3ad61685a13a1e3',
    'verify_all::kern_z_norm_flag::@@def': 'd29ce4581cc41379b5887652a25b7cf2',
    'verify_all::kern_z_norm_flag::_rest': '7a5e0e93d28d18be885a86831628bdc7',
    'verify_all::kern_z_norm_flag_packed::@@def': '245e1cab8c94f6d4a1b2c8d74ae3cddd',
    'verify_all::kern_z_norm_flag_packed::_rest': '5fb4108e462e60af7fdf29b706437fb2',
    'verify_all::kernel_obligations::@@def': '3cafbbb4baffd58b105872938263365d',
    'verify_all::kernel_obligations::_rest': 'bb1682f7e55ba7960cae7a3fde95f109',
    'verify_all::main::@@def': 'ae338532d5fa14df45706c4e15dc5ec6',
    'verify_all::main::_rest': 'e1a0aaddce9a9b11e77b3d2081a4d72a',
    'verify_all::pinned::@@def': '388ce8d6fa0029dff494591518658d3b',
    'verify_all::pinned::_rest': '84b103ff5aec407e3ea426dc1713caaa',
    'verify_all::raw_bytes::@@def': '9abc97863f37a37fef672107c34b521e',
    'verify_all::raw_bytes::_rest': 'ef2e7ed371fb240eb5fd9de7ed6efd34',
    'verify_all::record::@@def': '4263a229dbc55cd6081624a23299b5cc',
    'verify_all::record::_rest': '7d1a3a5f4899a0f5c15ad044a8a0c9cc',
    'verify_all::ref_decompose::@@def': '6b8957eb9802643757e123c2f3c280d6',
    'verify_all::ref_decompose::_rest': '7887e1f996a3039c0b91bc1531eced3c',
    'verify_all::ref_reduce_mod_pm::@@def': 'a0d8ee3d02ffed15c01d702d740ee754',
    'verify_all::ref_reduce_mod_pm::_rest': '13b659e22ca237f8afb50ba853ab8270',
    'verify_all::ref_use_hint::@@def': 'c18276d431b8589d035ce774116f482f',
    'verify_all::ref_use_hint::_rest': 'f54218beb1e2db30364dd8932df07819',
    'verify_all::ref_z_centered::@@def': 'bc37beaee71605d71cf8f3f5f49b8dde',
    'verify_all::ref_z_centered::_rest': '4946543d7bad580bca1379e165a965ce',
    'verify_all::ref_z_norm_ok::@@def': 'eba78e3c56257da4dcf521d9075d22e0',
    'verify_all::ref_z_norm_ok::_rest': '11cfe72efe300fb1c9e31a7e4572c046',
    'verify_all::smt_obligations::@@def': '4957668f2bdff5cb0d86acf87520ee39',
    'verify_all::smt_obligations::S1+S2': '2e36c6e4f14206210c44005210de6df3',
    'verify_all::smt_obligations::S11': '3d37963190190ddee67242e132c7871c',
    'verify_all::smt_obligations::S11b': '34e36e7b06a1e15494f5ed893b9412de',
    'verify_all::smt_obligations::S13': 'cdec3799a497a2fa7a8183e2ac038021',
    'verify_all::smt_obligations::S14': '5c1c81fd20aef03f308b5fb24ad14dc2',
    'verify_all::smt_obligations::S3+S4': '1da0d082b05c374978735d39cd0cd3be',
    'verify_all::smt_obligations::S5': '75562c6dd54735e3184c117c192cafda',
    'verify_all::smt_obligations::S6': '594dfae7a2cd1c82e4ab039ba23dbe6d',
    'verify_all::smt_obligations::S6b': 'acc96f2580a7a2cea7c2a9527d990107',
    'verify_all::smt_obligations::S7': '9c80a428f5503e2d8b8889b1732ee55f',
    'verify_all::smt_obligations::S8': '7f60d5b2076f809ab824c9477ff6a3b7',
    'verify_all::smt_obligations::S8b': '5f35f2a1d227edb85cb9e6e0b4b2114e',
    'verify_all::smt_obligations::_rest': 'a5f999f77b32d561f69d578df09d65ed',
    'verify_all::source_pin_obligation::@@def': '397a4b56103891042b17330979b58723',
    'verify_all::source_pin_obligation::_rest': '004d23be3452ae9c62c34536694dc5d1',
}
FILES = {
    'README.md': '097be8e5518e8b36c6765d079ad913a6',
    'acvp/data/mldsa_keygen.json': 'e67ee6540d40e11506c3c4e3b1f79fc1',
    'acvp/data/provenance.json': '2f5a8c202f978b622b8029a04ccfa724',
    'acvp/keygen_build.py': '6706b0bc91edc00ae87fddb51765f558',
    'hypotheses.py': '0416c3273f4ed6e6506a23c983e59c75',
    'lean/Mldsa.lean': '3c148079764ccff70d6f9a6696ddfaa9',
    'lean/Mldsa/Audit.lean': 'fbc77ba53df0b338cd042a9905656ef1',
    'lean/Mldsa/Barrett.lean': 'fd8b7e52048ff12dd5f73f26f04be0cd',
    'lean/Mldsa/Decode.lean': 'b7916cf3d5e463117b17f9b377957521',
    'lean/Mldsa/Encoding.lean': '3d1d7f4926244e6976019aabfe89f35a',
    'lean/README.md': '61f61aaee32465a6b6bb3ba6cbba1ac3',
    'lean/check_axioms.py': '33adc4fd957711e52ed64b08739d23b4',
    'lean/lake-manifest.json': 'b4eb4e6013cb31743957e8323d0f2f2d',
    'lean/lakefile.toml': 'e1bf836c8b5f6aa99f3142a2c08b8990',
    'lean/lean-toolchain': '62c2d9c0fc1ec4c67e151c11eff41ca0',
    'mutation/RESULTS.md': 'd4714bc4e542ba709738d950b8867e63',
    'mutation/halmos_fv1.json': '3366b85c650fa2a9a4f2d83981fe0caa',
    'mutation/halmos_fv2.json': '55093daaf1d92e76764e84e01ab42140',
    'mutation/mutants.py': 'b43f57f32ef5996dc316866efe261cf9',
    'mutation/run_halmos.py': 'a362a32487ed516c77fe3e5716c001b5',
    'mutation/run_mutation.py': '34d645503e6e84f9e8752b9cad7020a8',
    'run_checks.sh': '7c3988a697367101130dd6e9acfbbd81',
    'z3/kernel_obligations.py': '3e30c169057428a154a43518504c21db',
    'z3/vacuity_audit.py': 'ecc9854912ec6b40ae01fab95406b7b6',
    'z3/verify_all.py': 'a41a1c08212904b7e6c562f8299a0f83',
}


if __name__ == "__main__":
    sys.exit(main())
