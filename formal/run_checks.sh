#!/usr/bin/env bash
#
# The formal-verification CHECKS, in one place, all of them FAILING on regression.
#
# Several of these were once "a human reads the output": `lake build` exits 0
# with `sorry` planted in a headline theorem, and a suite that prints
# `len(results)` produces a smaller green number when an obligation is deleted.
# Every check below therefore ASSERTS rather than reports: the obligation and
# conjunct ID sets are pinned, every pinned obligation carries discrimination
# controls, and check 1 carries the META-PINS source-digest tripwire; check 2
# pins every audited Lean theorem's STATEMENT, not just its name.  See
# docs/FORMAL_VERIFICATION.md for what those mechanisms provably cannot detect.
#
#   ./formal/run_checks.sh              # the fast checks (~2 min)
#   ./formal/run_checks.sh --full       # + vacuity audit + a SAMPLED mutation run
#   ./formal/run_checks.sh --extended   # + vacuity audit + the FULL 50-mutant campaign
#
# MUTATION SCOPE — A SAMPLE IS NOT THE CAMPAIGN.  Every mutant costs a full
# via-IR rebuild at optimizer_runs=10000; the 50 records of
# mutation_results_final.json sum to 12,348 s = 3.43 h of mutant time (median
# 242 s, range 189-303 s, from a --jobs 6 run, so a serial wall-clock may
# differ).  At --jobs 6 the campaign takes about 40 minutes: a
# release-candidate cost, not an every-edit cost.  `--full`
# therefore runs a seeded, family-stratified SAMPLE of 8 mutants in parallel
# (minutes), and `--extended` (or MUTATION_EXTENDED=1) runs the whole campaign.
# The two are labelled differently everywhere they are reported: the published
# `45/45 non-equivalent mutants KILLED` figure is a claim about a FULL campaign,
# and only `--extended` can produce it.  A sampled run prints its SEED, so a
# sampled failure is replayed exactly with
# `run_mutation.py --sample 8 --seed <printed seed>`.
#
# CI WIRING: `.github/workflows/ci.yml`.  Its `formal` job checks the tree
# out onto a fresh runner, builds the venv and the pinned Lean toolchain, and
# runs THIS SCRIPT with CHECK0_PY pointed at the runner's own /usr/bin/python3 --
# which is what check 0's two-interpreter agreement check needs, and what the
# §FV.6 hypothesis row means by "a process this tree did not start".  Its
# `forge-test` job runs the EVM corpus and checks MLDSA44Verifier against
# EIP-170.  The per-conjunct vacuity audit and the FULL mutation campaign are
# the `vacuity-and-mutation` job, which invokes them directly rather than
# through this script, because every mutant is a full via-IR rebuild.  Two things that workflow does NOT buy, stated here so a green badge
# is not over-read: it lives IN this repository, so it is in the same trust
# domain as the tree (see hypotheses §FV.6); and a green FAST-check run still
# covers neither the vacuity audit nor the campaign, exactly as before -- do not
# read a green SAMPLED run as covering the campaign.
#
# CHECK 0 exists because asserting an obligation is PRESENT is not asserting it
# still MEANS anything, and because the pinning mechanism itself is the
# cheapest thing to attack.  The attack is to find something the apparatus
# EXECUTES that it does not
# DIGEST: an unpinned module-level slot, an unpinned `def` line, a shadowing
# `__pycache__/*.pyc`, an interpreter owned by the repository, and executable
# code hidden in a BLANKED region.  Check 0 is the outermost layer of the
# answer: it re-derives, in a FRESH `python -I -S` that ignores site-packages,
# PYTHON* env vars and sitecustomize — once under an interpreter found OUTSIDE
# this repository, once under $PY — the digests that anchor everything else,
# proves the blanked regions are inert data, and refuses to let any check run
# until the two independent answers match the anchors.  For what this bootstrap
# does and does not buy, see the "Trust anchor" entry in the glossary (§0b) of
# docs/FORMAL_VERIFICATION.md and §2f, which record that the anchor cannot
# certify itself and that the interpreter and the toolchain are assumptions.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PY="${PY:-$ROOT/pythonref/myenv/bin/python}"
LAKE="${LAKE:-$HOME/.elan/bin/lake}"
# FULL     = the fast checks + the vacuity audit + a SAMPLED mutation run
# EXTENDED = the same, with the COMPLETE 50-mutant campaign instead of a sample.
# An unrecognised option is refused rather than ignored: a typo'd `--extendd`
# that silently ran a SAMPLE would be a sample reported as the campaign.
FULL=0
EXTENDED=0
while [ $# -gt 0 ]; do
  case "$1" in
    --full)     FULL=1;;
    --extended) FULL=1; EXTENDED=1;;
    *) echo "usage: $0 [--full | --extended]   (see the header of this file)" >&2
       exit 64;;
  esac
  shift
done
if [ "${MUTATION_EXTENDED:-0}" = "1" ]; then FULL=1; EXTENDED=1; fi
MUT_SAMPLE="${MUT_SAMPLE:-8}"
MUT_JOBS="${MUT_JOBS:-${JOBS:-6}}"

# No .pyc may ever be created for a module under formal/ (a shadowing .pyc
# once carried a payload).  Both the flag and the env var: subprocesses
# inherit the latter.
export PYTHONDONTWRITEBYTECODE=1

# ---------------------------------------------------------------------------
# THE ANCHOR CONSTANTS.  Regenerate with:  formal/z3/source_pins.py --anchors
# ---------------------------------------------------------------------------
# ANCHOR_VERIFY_ALL_AST     sha256(ast.unparse(ast.parse(verify_all.py)))[:32]
# ANCHOR_SOURCE_PINS_CODE   the same over source_pins.py with its two pinned
#                           tables blanked (so regenerating pins cannot move it)
# ANCHOR_VERIFY_ALL_BYTES   sha256 of verify_all.py's RAW BYTES
# ANCHOR_SOURCE_PINS_BYTES  sha256 of source_pins.py's raw text with the LINE
#                           RANGES of the two table assignments blanked
# ANCHOR_RUN_CHECKS_SH       sha256 of THIS file's raw text with the six
#                           ANCHOR_* lines blanked (they hold digests of
#                           verify_all.py, so digesting them would be a cycle)
#
# These are the THIRD copy of the anchor.  `verify_all.py` holds the second
# (SOURCE_PINS_CODE_SHA256, RUN_CHECKS_SH_SHA256) and `source_pins.py` holds the
# first (the `verify_all::@@file` region).
#
# WHAT IS BLANKED MUST BE PROVABLY INERT DATA, or blanking hands the attacker a
# region covered by nothing.  Two such regions exist here, and both are
# realisable:
#   THE TABLES.  A dict display is EXECUTABLE code, so ONE line inside
#          `PINS = {...}` -- `'k': exec("<open() shim>") or '<hash>'`,
#          line-count-neutral, value byte-identical -- gave `anchor OK` with all
#          digests unchanged and ALL CHECKS PASS over a tree with a real defect
#          in the shipped Ntt.sol.  ONE file, ONE line, ZERO hash literals.
#          Closed: all three blankers now REFUSE unless every key and value is
#          a string constant at column 0 with nothing else on the first or
#          last line.
#   THIS FILE.  The driver was pinned only by one row of that same blanked
#          `FILES` table, so rewriting check 1's invocation to inject an
#          `open()` shim plus that one row was TWO files, ONE hash literal and
#          zero anchor movement.  Closed as far as in-band checking can: the
#          driver is now anchored here AND in verify_all.py, outside every
#          blanked region.  The residue -- a driver payload that also shims the
#          suite's own reads -- is a bigger, self-evidently hostile diff, and it
#          is caught by running check 1 on its own.  See hypotheses §FV.6.
#
# THE BYTES ANCHORS: the two BYTES anchors exist because
# `ast.unparse` output is CPython-version-dependent -- 3.9.6 and 3.10.4 agree on
# 24c5536d…, 3.11.15 does not -- and check 0 must now run under an interpreter it
# did not get from this repository, whose version it cannot choose.  The BYTES
# digests are computed with `hashlib` and `str.split` only, so they are the same
# on every version; the AST digests are checked in addition wherever the running
# interpreter's (major, minor) is in ANCHOR_AST_PYVERS.
ANCHOR_VERIFY_ALL_AST="b6a32774ab13a4b8f86c90b264060e12"
ANCHOR_SOURCE_PINS_CODE="6d25f56d8eed4e1e87312829bc9b0b7e"
ANCHOR_VERIFY_ALL_BYTES="b118ceb39f0b646b268ccef93cd69c7f"
ANCHOR_SOURCE_PINS_BYTES="a8dfcd6407634dbb60e7a7da14eb7b6f"
ANCHOR_RUN_CHECKS_SH="4fcc3e2f82f80c44082afd4769488a3d"
ANCHOR_AST_PYVERS="3.9 3.10"

# ---------------------------------------------------------------------------
# THE BOOTSTRAP INTERPRETER
# ---------------------------------------------------------------------------
# A check 0 that ran `"$PY" -I -S` would still take $PY from A PATH INSIDE THIS
# REPOSITORY (`pythonref/myenv/bin/python`, a 7-byte symlink).
# "Out of band" would therefore be a claim about FLAGS, not about PROVENANCE: an
# attacker who can write the repository can write the interpreter.  Replacing
# that symlink with a wrapper script that serves the reviewed bytes of
# `verify_all.py` to every `open()`, plus ONE payload edit in `verify_all.py`
# (deleting C16's extracted-schedule conjunct and all five of its discrimination
# controls, together with their pinned IDs), is a TWO-file defeat that prints
# the original `anchor OK` line, a full green obligation tally and ALL CHECKS
# PASS -- i.e. cheaper than the several coordinated edits that would otherwise
# be the floor, and with the anchor line UNCHANGED rather than moved.
#
# So check 0 now:
#   (a) runs under BOOT_PY, an interpreter whose own realpath is OUTSIDE $ROOT
#       and which was not found through any repository path.  If none exists the
#       check FAILS -- it never silently falls back to $PY;
#   (b) re-derives the anchors under BOOT_PY (version-independent BYTES digests
#       always; AST digests additionally when BOOT_PY's version is anchored);
#   (c) re-derives the same digests under $PY and requires the two independent
#       answers to AGREE.  A lying $PY must report the anchored values to pass
#       (b)'s comparison in its own run, and then disagrees with BOOT_PY, which
#       reports what is actually on disk;
#   (d) requires realpath($PY) to be outside $ROOT, which is the direct
#       statement of "no check runs under a repository-owned executable".
# What this does NOT buy is stated in FORMAL_VERIFICATION.md §2f and in the
# §FV.2 row of formal/hypotheses.py: BOOT_PY itself is an environment
# assumption, not a verified object.
find_boot_py() {
  local c rp
  for c in "${CHECK0_PY:-}" /usr/bin/python3 /usr/local/bin/python3 \
           /opt/homebrew/bin/python3 "$(command -v python3 2>/dev/null || true)" \
           "$(command -v python3.10 2>/dev/null || true)"; do
    [ -n "$c" ] && [ -x "$c" ] || continue
    case "$c" in "$ROOT"/*) continue;; esac
    rp="$("$c" -I -S -c 'import os,sys; print(os.path.realpath(sys.executable))' 2>/dev/null)" || continue
    [ -n "$rp" ] || continue
    case "$rp" in "$ROOT"/*) continue;; esac
    printf '%s\n' "$c"
    return 0
  done
  return 1
}
BOOT_PY="$(find_boot_py || true)"

# The digest kernel, run twice: once under BOOT_PY, once under $PY.  It imports
# `ast`, `hashlib` and `os` from the standard library and NOTHING from this
# repository, prints one machine-readable RESULT line, and exits 1 on any
# mismatch with the anchors it is given.
CHECK0_SRC=$(cat <<'PYEOF'
import ast, hashlib, os, re, sys

(formal, want_va_ast, want_sp_ast, want_va_b, want_sp_b, want_rg_b,
 ast_vers) = sys.argv[1:8]
z3 = os.path.join(formal, "z3")
ver = "%d.%d" % sys.version_info[:2]
check_ast = ver in ast_vers.split()
bad, got = [], {}


def read(path):
    with open(path, "rb") as fh:
        raw = fh.read()
    for line in raw.split(b"\n", 2)[:2]:
        if b"coding" in line and line.lstrip().startswith(b"#") \
                and b"utf-8" not in line and b"utf8" not in line:
            bad.append(f"{path}: suspicious PEP-263 encoding line: {line!r}")
    return raw, raw.decode("utf-8")


def sha(b):
    return hashlib.sha256(b + b"\0").hexdigest()[:32]


def table_nodes(text):
    """The module-level `PINS = {...}` / `FILES = {...}` assignments, CHECKED.

    THE INERT-DATA RULE.  Blanking a source region before
    digesting it is only sound if that region is provably INERT DATA, and a
    dict display is NOT: Python evaluates every value expression, and a
    duplicate key is simply overwritten.  ONE line inside `PINS = {...}`,
        'kernel_obligations::@@file': exec("<builtins.open shim>") or '<real hash>',
    is line-count-neutral, leaves the table's value byte-identical, and printed
    `anchor OK` with all four digests unchanged, ALL CHECKS PASS
    over a tree with a real defect in the shipped Ntt.sol.  So: every key and
    every value must be a string CONSTANT, the assignment must start at column 0,
    and nothing else may share its first or last line (the LINE-RANGE blanker
    below would blank that too).
    """
    tree = ast.parse(text)
    lines = text.split("\n")
    seen, nodes = {}, []
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                and isinstance(node.targets[0], ast.Name) \
                and node.targets[0].id in ("PINS", "FILES"):
            nm = node.targets[0].id
            seen[nm] = seen.get(nm, 0) + 1
            nodes.append(node)
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
                                   "is required — the BLANKED table is not inert "
                                   "data")
            if node.col_offset != 0 \
                    or lines[node.end_lineno - 1][node.end_col_offset:].strip():
                bad.append(f"{nm}: other code shares the table's first or last "
                           "line, which the LINE-RANGE digest blanks too")
    if sorted(seen) != ["FILES", "PINS"] or set(seen.values()) != {1}:
        bad.append(f"source_pins.py assigns its pinned tables {seen} times at "
                   "module level; expected exactly one each")
    return tree, lines, nodes


def blank_tables_text(text):
    """source_pins.py's text with the two pinned tables' LINE RANGES blanked.

    Line numbers are stable across CPython versions; `ast.unparse` output is
    not.  This is the version-independent counterpart of the CODE digest.
    """
    _tree, lines, nodes = table_nodes(text)
    for node in nodes:
        for i in range(node.lineno - 1, node.end_lineno):
            lines[i] = "@@TABLE BLANKED@@"
    return "\n".join(lines)


def blank_tables_ast(text):
    tree, _lines, nodes = table_nodes(text)
    for node in nodes:
        node.value = ast.Dict(keys=[], values=[])
    return ast.unparse(ast.fix_missing_locations(tree))


def blank_gate_anchors(text):
    """run_checks.sh with its six `ANCHOR_*=` lines blanked.

    THE SECOND zero-anchor route.  This file is the DRIVER, and the
    only thing that pinned it was one row of the (blanked) `FILES` table:
    rewriting check 1's invocation to inject an `open()` shim, plus that one row,
    is TWO files, ONE hash literal and no anchor movement -- reproduced, with
    this very line printing `anchor OK`.  `verify_all.py` now holds
    RUN_CHECKS_SH_SHA256 and checks it before the suite runs; check 0 re-derives
    the same value under both interpreters.  The ANCHOR_* lines are blanked
    because they hold digests OF verify_all.py (digesting them would be a
    cycle), and they are held to the same inertness rule as the tables.
    """
    lines, n = text.split("\n"), 0
    for i, line in enumerate(lines):
        if not line.startswith("ANCHOR_"):
            continue
        n += 1
        if not re.match(r'^ANCHOR_[A-Z0-9_]+="[0-9a-f. ]*"$', line):
            bad.append(f"run_checks.sh line {i + 1}: {line[:56]!r} is not a plain "
                       "hex/version string assignment — a blanked line must be "
                       "INERT DATA")
        lines[i] = "@@ANCHOR BLANKED@@"
    if n != 6:
        bad.append(f"run_checks.sh: {n} ANCHOR_* lines, expected 6")
    return "\n".join(lines)


# (a) verify_all.py
try:
    raw, text = read(os.path.join(z3, "verify_all.py"))
    got["va_bytes"] = sha(raw)
    got["va_ast"] = sha(ast.unparse(ast.parse(text)).encode("utf-8")) if check_ast else "skipped"
except Exception as exc:
    bad.append(f"verify_all.py: {exc!r}")

# (b) source_pins.py, code only (its two pinned tables blanked)
try:
    raw, text = read(os.path.join(z3, "source_pins.py"))
    got["sp_bytes"] = sha(blank_tables_text(text).encode("utf-8"))
    got["sp_ast"] = sha(blank_tables_ast(text).encode("utf-8")) if check_ast else "skipped"
except Exception as exc:
    bad.append(f"source_pins.py: {exc!r}")

# (c) run_checks.sh itself -- the DRIVER -- with its six ANCHOR_* lines blanked.
#     verify_all.py holds the same constant as RUN_CHECKS_SH_SHA256, in a region
#     that is NOT blanked, and refuses before the suite runs.
try:
    _raw, text = read(os.path.join(formal, "run_checks.sh"))
    got["rg_bytes"] = sha(blank_gate_anchors(text).encode("utf-8"))
except Exception as exc:
    bad.append(f"run_checks.sh: {exc!r}")

# (d) nothing under formal/ may be compiled bytecode that shadows a source file
pycs = [os.path.relpath(os.path.join(d, f), formal)
        for d, _sub, fs in os.walk(formal) for f in fs
        if f.endswith((".pyc", ".pyo"))]
for p in sorted(pycs):
    bad.append(f"bytecode under formal/ (may shadow a pinned source): {p}")

for key, want in (("va_bytes", want_va_b), ("sp_bytes", want_sp_b),
                  ("rg_bytes", want_rg_b),
                  ("va_ast", want_va_ast), ("sp_ast", want_sp_ast)):
    have = got.get(key, "MISSING")
    if have == "skipped":
        continue
    if have != want:
        bad.append(f"{key}: {have} != anchored {want}")

print("RESULT python=%s va_bytes=%s sp_bytes=%s rg_bytes=%s va_ast=%s sp_ast=%s "
      "pycs=%d"
      % (ver, got.get("va_bytes", "MISSING"), got.get("sp_bytes", "MISSING"),
         got.get("rg_bytes", "MISSING"),
         got.get("va_ast", "MISSING"), got.get("sp_ast", "MISSING"), len(pycs)))
for b in bad:
    print(f"  !! {b}")
if bad:
    print("ANCHOR MISMATCH — the formal apparatus is not the reviewed one, or a "
          ".pyc can shadow it.")
    print("If deliberate: review the diff, then `formal/z3/source_pins.py --write` "
          "and paste `--anchors` here and into verify_all.py.")
    sys.exit(1)
PYEOF
)

rc=0
run() {
  local name="$1"; shift
  echo "=============================================================================="
  echo "CHECK: $name"
  echo "=============================================================================="
  if "$@"; then
    echo "-- $name: PASS"
  else
    echo "-- $name: FAIL (exit $?)"
    rc=1
  fi
  echo
}

# 0. the trust anchor, re-derived out of band -- under an interpreter this
#    repository does not own, and cross-checked against $PY's own answer.
#    `-I` (isolated: no PYTHON* env vars, no user site) `-S` (no site.py, so no
#    sitecustomize/.pth) so that this check depends on the interpreter and its
#    standard library and on nothing else in the environment.  It reads only
#    `ast`, `hashlib` and `os.walk`; it imports nothing from this repository.
check0() {
  local args=( "$ROOT/formal" "$ANCHOR_VERIFY_ALL_AST" "$ANCHOR_SOURCE_PINS_CODE"
               "$ANCHOR_VERIFY_ALL_BYTES" "$ANCHOR_SOURCE_PINS_BYTES"
               "$ANCHOR_RUN_CHECKS_SH" "$ANCHOR_AST_PYVERS" )
  local ok=0
  # `ident` is tracked SEPARATELY from `ok` because the two failures mean
  # opposite things and the old code conflated them: a documented reproduce line
  # (`CHECK0_PY=$(command -v python3)`) makes the bootstrap and check
  # interpreters the SAME executable on any machine whose venv was built from
  # that same python3 -- asdf/pyenv shims, i.e. most developer laptops -- and
  # check 0 then printed `ANCHOR MISMATCH — the formal apparatus is not the
  # reviewed one`.
  # That reads like a tamper alarm; the cause is a shell substitution one line
  # above it.  Refusal is still correct (step (d) would be one interpreter
  # agreeing with itself), but the message must LEAD with why.
  local ident=0

  # (a) an interpreter that is not this repository's
  if [ -z "$BOOT_PY" ]; then
    echo "  !! no bootstrap interpreter found OUTSIDE $ROOT."
    echo "     check 0 refuses to re-derive the trust anchor with an interpreter"
    echo "     the attacker could have written."
    echo "     Point CHECK0_PY at a python3 outside this repository and re-run."
    return 1
  fi
  local boot_rp py_rp
  boot_rp="$("$BOOT_PY" -I -S -c 'import os,sys;print(os.path.realpath(sys.executable))')"
  echo "  bootstrap interpreter:  $BOOT_PY -> $boot_rp"

  # (b) $PY, the interpreter every OTHER check runs under, must not be a
  #     repository-owned executable either.
  if ! py_rp="$("$PY" -c 'import os,sys;print(os.path.realpath(sys.executable))' 2>/dev/null)"; then
    echo "  !! \$PY ($PY) did not run"
    return 1
  fi
  echo "  check interpreter:      $PY -> $py_rp"
  case "$py_rp" in
    "$ROOT"/*)
      echo "  !! \$PY resolves INSIDE the repository ($py_rp)."
      echo "     A repository-owned interpreter is a repository-owned check: it can"
      echo "     serve the reviewed bytes to every open() while executing others"
      echo "     A venv whose bin/python is a SYMLINK to an interpreter"
      echo "     outside the tree is fine; a regular file there is not."
      ok=1;;
  esac
  # (b2) The check above reads `sys.executable`, and for a WRAPPER
  #      SCRIPT that `exec`s an outside interpreter, `sys.executable` is the
  #      OUTSIDE one -- so a regular file at $PY inside $ROOT passed (b) while
  #      the message above claimed it would not.  Found by re-running the
  #      wrapper attack: a two-line `#!/bin/sh\nexec <outside python>`
  #      at pythonref/myenv/bin/python printed
  #      `-- trust anchor ...: PASS`.  The documented intent is about the PATH,
  #      so resolve the PATH -- with BOOT_PY, never with $PY itself.
  py_link="$("$BOOT_PY" -I -S -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$PY" 2>/dev/null || echo "$PY")"
  echo "  check interpreter path: $PY -> $py_link"
  case "$py_link" in
    "$ROOT"/*)
      echo "  !! \$PY is a repository-owned EXECUTABLE FILE ($py_link)."
      echo "     A wrapper script that execs an interpreter outside the tree keeps"
      echo "     sys.executable outside \$ROOT while still choosing the flags, the"
      echo "     environment and the -c prologue every check runs under."
      ok=1;;
  esac
  if [ "$boot_rp" = "$py_rp" ]; then
    echo "  !! the bootstrap and check interpreters are the same executable;"
    echo "     step (d) below would not be an independent second opinion."
    ident=1
  fi

  # (c) the anchors, re-derived by the bootstrap interpreter
  local boot_out py_out
  boot_out="$("$BOOT_PY" -I -S -c "$CHECK0_SRC" "${args[@]}" 2>&1)" || ok=1
  echo "$boot_out" | sed 's/^/  boot: /'

  # (d) ... and again by $PY.  A $PY that lies must report the anchored values
  #      here and therefore disagree with the bootstrap interpreter, which
  #      reports what is actually on disk.
  py_out="$("$PY" -I -S -c "$CHECK0_SRC" "${args[@]}" 2>&1)" || ok=1
  echo "$py_out" | sed 's/^/  py:   /'

  local b p
  b="$(printf '%s\n' "$boot_out" | grep '^RESULT ' || true)"
  p="$(printf '%s\n' "$py_out"   | grep '^RESULT ' || true)"
  if [ -z "$b" ] || [ -z "$p" ]; then
    echo "  !! one of the two interpreters produced no RESULT line"
    ok=1
  else
    local f bv pv
    for f in va_bytes sp_bytes rg_bytes va_ast sp_ast pycs; do
      bv="$(printf '%s\n' "$b" | tr ' ' '\n' | sed -n "s/^$f=//p")"
      pv="$(printf '%s\n' "$p" | tr ' ' '\n' | sed -n "s/^$f=//p")"
      [ "$bv" = "skipped" ] || [ "$pv" = "skipped" ] && continue
      if [ "$bv" != "$pv" ]; then
        echo "  !! $f DISAGREES: bootstrap says $bv, \$PY says $pv —"
        echo "     one of the two interpreters is not reporting the bytes on disk."
        ok=1
      fi
    done
  fi

  # (e) PROVENANCE OF THE SOLVER, reported.  Re-examining the §FV.2 row after
  #     `z3` is imported by check 1 from wherever `$PY` resolves it, and in
  #     the default configuration that is INSIDE this repository
  #     (pythonref/myenv/lib/.../site-packages/z3).  A repository-
  #     owned solver is the same class of exposure as a repository-owned
  #     interpreter, and NO digest in this apparatus covers it.
  #     What does cover it, demonstrated rather than asserted (see §2, "What a
  #     pin actually pins", of FORMAL_VERIFICATION.md): a solver that answers
  #     `unsat` to everything fails every `S*.premises_sat` and
  #     `S*.claims_discriminate`; a
  #     context-sensitive one that answers `sat` to premise-only checks, `unsat`
  #     to premises+Not(claim) and `sat` to the premise-free probe is caught by
  #     the BIDIRECTIONAL `theory_valid` staleness check (S11/S14) and by
  #     `kernel_obligations`' `ctl_*_is_refutable` controls.  A bespoke replay shim
  #     defeats check 1 -- but only usefully in combination with an edit to
  #     `verify_all.py`, which (a)-(d) above catch.  This line exists so that the
  #     provenance is on the record in every run rather than in a document.
  local z3info
  z3info="$("$PY" -c 'import os,z3;print(os.path.dirname(os.path.abspath(z3.__file__)), z3.get_version_string())' 2>/dev/null || echo "NOT IMPORTABLE")"
  case "$z3info" in
    "$ROOT"/*) echo "  solver: $z3info  [INSIDE \$ROOT — not covered by any digest; see hypotheses §FV.2]";;
    *)         echo "  solver: $z3info  [outside \$ROOT]";;
  esac

  # THE IDENTITY CASE LEADS, and it does not print ANCHOR MISMATCH when it is
  # the only problem: nothing above disagreed about any byte.
  if [ "$ident" != "0" ]; then
    echo "CHECK 0 REFUSED — INTERPRETER IDENTITY.  This is NOT an anchor mismatch:"
    echo "no digest above disagreed with anything.  CHECK0_PY and \$PY resolve to"
    echo "the SAME executable ($boot_rp), so step (d) would be one interpreter"
    echo "agreeing with itself instead of a second opinion."
    echo "  CAUSE, nine times in ten: \`CHECK0_PY=\$(command -v python3)\` on a"
    echo "  machine where pythonref/myenv was created FROM that same python3"
    echo "  (asdf/pyenv shims).  The documented reproduce line warns against"
    echo "  exactly that."
    echo "  FIX: unset CHECK0_PY (check 0 tries /usr/bin/python3 and friends by"
    echo "  itself), or point it at a python3 that is NOT the one the venv was"
    echo "  created from -- e.g. CHECK0_PY=/usr/bin/python3."
  fi
  if [ "$ok" != "0" ]; then
    echo "ANCHOR MISMATCH — the formal apparatus is not the reviewed one, or the"
    echo "interpreter running the checks is not reporting the bytes on disk."
  fi
  if [ "$ident" != "0" ] || [ "$ok" != "0" ]; then
    return 1
  fi
  echo "anchor OK: verify_all.py=$ANCHOR_VERIFY_ALL_BYTES (bytes) / $ANCHOR_VERIFY_ALL_AST (ast)"
  echo "           source_pins.py(code)=$ANCHOR_SOURCE_PINS_BYTES (bytes) / $ANCHOR_SOURCE_PINS_CODE (ast)"
  echo "           run_checks.sh(this file, ANCHOR_* lines blanked)=$ANCHOR_RUN_CHECKS_SH"
  echo "           the 2 blanked tables and the 6 blanked ANCHOR_* lines are INERT DATA"
  echo "           0 bytecode files under formal/"
  echo "re-derived TWICE by \`python -I -S\` (no site-packages, no sitecustomize, no"
  echo "PYTHON* env vars, nothing imported from this repository) — once by an"
  echo "interpreter outside \$ROOT, once by the interpreter the checks run under,"
  echo "and the two answers agree."
}
run "trust anchor, out of band (formal/run_checks.sh check 0)" check0

# 1. the obligation suite -- the ID set is asserted, so a deleted obligation or
#    conjunct is a failure and not a smaller number
run "z3 obligation suite (formal/z3/verify_all.py)" \
    env MLDSA_REPO="$ROOT" "$PY" "$ROOT/formal/z3/verify_all.py"

# 2. the Lean axiom base -- `lake build` alone does NOT bite (see the script header)
run "Lean axiom check (formal/lean/check_axioms.py)" \
    env LAKE="$LAKE" "$PY" "$ROOT/formal/lean/check_axioms.py"

# 3. hypotheses <-> enforcing code
run "hypotheses (formal/hypotheses.py)" \
    "$PY" "$ROOT/formal/hypotheses.py"

if [ "$FULL" = "1" ]; then
  # 5. per-conjunct vacuity audit: every conjunct of every obligation must be
  #    load-bearing, every non-equivalent mutation must kill something
  run "per-conjunct vacuity audit (formal/z3/vacuity_audit.py)" \
      "$PY" "$ROOT/formal/z3/vacuity_audit.py" --jobs "${JOBS:-6}"

  # 6. mutation testing of the EVM corpus.  SAMPLED on the routine path; the
  #    complete campaign only under --extended, and the check NAME says which,
  #    so a scrollback of a sampled run cannot be read as the campaign.
  if [ "$EXTENDED" = "1" ]; then
    run "mutation campaign, FULL — all 50 catalogued mutants (formal/mutation/run_mutation.py --full)" \
        "$PY" "$ROOT/formal/mutation/run_mutation.py" --full --jobs "$MUT_JOBS"
  else
    run "mutation campaign, SAMPLED — $MUT_SAMPLE of 50 mutants, seeded, NOT the full campaign (formal/mutation/run_mutation.py --sample)" \
        "$PY" "$ROOT/formal/mutation/run_mutation.py" --sample "$MUT_SAMPLE" \
        --jobs "$MUT_JOBS"
  fi
fi

echo "=============================================================================="
# WHICH SCOPE RAN, stated in the summary an auditor quotes rather than left to
# be inferred from which checks happen to appear above.
if [ "$FULL" != "1" ]; then
  echo "scope: FAST CHECKS ONLY — no vacuity audit, no mutation testing."
  echo "       \`--full\` adds the vacuity audit + a SAMPLED mutation run;"
  echo "       \`--extended\` adds the complete 50-mutant mutation campaign."
elif [ "$EXTENDED" = "1" ]; then
  echo "scope: EXTENDED — vacuity audit + the FULL mutation campaign (all 50 mutants)."
else
  echo "scope: FULL — vacuity audit + a SAMPLED mutation run ($MUT_SAMPLE of 50 mutants, seeded)."
  echo "       THE MUTATION RESULT ABOVE IS A SAMPLE, NOT THE CAMPAIGN: it does not"
  echo "       establish the published 45/45 non-equivalent kill rate.  Run"
  echo "       \`./formal/run_checks.sh --extended\` for that; the sample's SEED is"
  echo "       printed above and replays its exact selection."
fi
echo "=============================================================================="
[ "$rc" = "0" ] && echo "ALL CHECKS PASS" || echo "AT LEAST ONE CHECK FAILED"
echo "=============================================================================="
exit "$rc"
