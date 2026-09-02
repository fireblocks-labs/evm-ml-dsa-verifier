#!/usr/bin/env python3
"""
HARD CHECK on the Lean development's axiom base.  Exit 0 iff:

  1. no source file contains a proof escape hatch (`sorry`, `admit`,
     `native_decide`, a user `axiom`, `unsafe`, `@[implemented_by]`, ...)
     outside a comment;
  2. `lake build` succeeds;
  3. the build emits an axiom-audit line for EVERY theorem `Mldsa/Audit.lean`
     asks about, and the audited theorem-name set is exactly EXPECTED_THEOREMS;
  4. no audited theorem depends on `sorryAx` (or on anything outside Lean's own
     three axioms `propext`, `Quot.sound`, `Classical.choice`);
  5. the string `sorryAx` does not appear anywhere in the build output.

WHY THIS EXISTS.  `#print axioms` is an `info:` message and `sorry` is a
*warning*; neither changes `lake build`'s exit code.  A planted `sorry`
therefore builds green: `sorryAx` is printed in the log and nothing fails, so
without a dedicated check the "0 sorry / 0 custom axioms" claim would be an
eyeball check, not a machine check.  This script is that machine check.

    formal/lean/check_axioms.py                    # build + audit
    formal/lean/check_axioms.py --print-theorems   # regenerate EXPECTED_THEOREMS
    formal/lean/check_axioms.py --print-statements # regenerate EXPECTED_STATEMENTS

CI: this must be a required job.  See formal/README.md "CI wiring".
"""
import os as _os_bootstrap, sys as _sys_bootstrap

_sys_bootstrap.dont_write_bytecode = True
_os_bootstrap.environ["PYTHONDONTWRITEBYTECODE"] = "1"

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
def _resolve_lake():
    """Resolve `lake` from $LAKE, PATH, or elan's default install location.

    A bare name -- `LAKE=lake`, the natural thing to write once elan is on
    $PATH -- must be resolved with a PATH lookup, not `os.path.exists`:
    otherwise the check exits 2 with "THE CHECK DID NOT RUN" on every CI run.
    Fail-closed, but a check that never runs protects nothing.
    """
    import shutil
    cand = os.environ.get("LAKE")
    if cand:
        if os.path.sep in cand:
            return cand                      # explicit path: use it verbatim
        return shutil.which(cand) or cand    # bare name: resolve on PATH
    return shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")


LAKE = _resolve_lake()

# Lean's own axioms.  Anything else -- above all `sorryAx` -- is a proof hole.
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

# Tokens that would let a proof through without the kernel checking it, or that
# would add a trust assumption outside ALLOWED_AXIOMS.
FORBIDDEN = [
    (r"\bsorry\b", "sorry (proof hole)"),
    (r"\bsorryAx\b", "sorryAx"),
    (r"\badmit\b", "admit"),
    (r"\bnative_decide\b", "native_decide (trusts the compiler, not the kernel)"),
    # `\baxiom\b`, deliberately NOT the line-anchored `^\s*axiom\s`: the anchored
    # form misses `private axiom`, `protected axiom`, `noncomputable axiom`,
    # `scoped axiom`, `local axiom` and `@[simp] axiom`.  `\baxiom\b` catches
    # every modifier ordering; it does not match `axioms` (the `#print axioms`
    # directives) because of the trailing word boundary, and the corpus is
    # comment-stripped first, so prose occurrences are not false positives.
    (r"\baxiom\b", "a user-declared axiom"),
    (r"\bLean\.ofReduceBool\b", "Lean.ofReduceBool (the native_decide axiom)"),
    (r"\bLean\.trustCompiler\b", "Lean.trustCompiler"),
    (r"\bunsafe\s+(def|theorem|instance)\b", "unsafe declaration"),
    (r"@\[implemented_by", "@[implemented_by] (replaces a proof-carrying def)"),
    (r"@\[extern", "@[extern] (foreign implementation)"),
    # (`set_option maxRecDepth` is NOT listed: it bounds elaboration recursion and
    #  has no effect on what the kernel accepts.)
    (r"set_option\s+debug\.skipKernelTC\s+true", "kernel type-checking disabled"),
    (r"set_option\s+maxHeartbeats\s+0\b", "elaboration heartbeats disabled"),
]

# The audited theorem set, pinned.  Deleting a `#print axioms` line is a
# FAILURE, not a shorter list.  Regenerate with --print-theorems.
EXPECTED_THEOREMS = [
    'Mldsa.Barrett.mu_is_floor',
    'Mldsa.Barrett.mu_q_add_d',
    'Mldsa.Barrett.unit_step_is_floor',
    'Mldsa.Barrett.q_sparse_form',
    'Mldsa.Barrett.no_borrow',
    'Mldsa.Barrett.second_no_borrow',
    'Mldsa.Barrett.barrettNat_lt_two_q',
    'Mldsa.Barrett.step1_lt_two_pow_33',
    'Mldsa.Barrett.barrettEVM_eq_nat',
    'Mldsa.Barrett.barrettEVM_lt_two_q',
    'Mldsa.Barrett.barrettNat_congr',
    'Mldsa.Barrett.lane_product_lt_two_pow_63',
    'Mldsa.Barrett.qhat_lt_two_pow_31',
    'Mldsa.Barrett.barrett_forward',
    'Mldsa.Barrett.barrett_inverse',
    'Mldsa.Barrett.barrett_inverse_congr',
    'Mldsa.Barrett.firstFail_breaks',
    'Mldsa.Barrett.firstFail_pred_ok',
    'Mldsa.Barrett.invMax_lt_firstFail',
    'Mldsa.Barrett.margin_guard',
    'Mldsa.Barrett.margin_guard_hmg',
    'Mldsa.Barrett.lane_cliff_above_firstFail',
    'Mldsa.Barrett.lane_cliff_breaks',
    'Mldsa.Barrett.step1_alone_is_not_enough',
    'Mldsa.Barrett.swar_step1_lane_independent',
    'Mldsa.Barrett.swar_lane_independent',
    'Mldsa.Barrett.swar_lane_fits',
    'Mldsa.Decode.u_bounds',
    'Mldsa.Decode.u_lt_two_q',
    'Mldsa.Decode.flag_no_carry',
    'Mldsa.Decode.flag_is_a_bit',
    'Mldsa.Decode.flag_iff_u_ge_q',
    'Mldsa.Decode.canon_lt_q',
    'Mldsa.Decode.canon_closed_form',
    'Mldsa.Decode.canon_zero_field',
    'Mldsa.Decode.lo_no_carry',
    'Mldsa.Decode.hi_no_borrow',
    'Mldsa.Decode.lo_iff',
    'Mldsa.Decode.hi_iff',
    'Mldsa.Decode.reject_iff_fips',
    'Mldsa.Decode.boundary_low_rejected',
    'Mldsa.Decode.boundary_low_inside_accepted',
    'Mldsa.Decode.boundary_high_rejected',
    'Mldsa.Decode.boundary_high_inside_accepted',
    'Mldsa.Decode.addSplit4',
    'Mldsa.Decode.subFromRep4',
    'Mldsa.Decode.swar_z_lane_independent',
    'Mldsa.Decode.flag_word_lane_fits',
    'Mldsa.Decode.fused_split',
    'Mldsa.Decode.fused_disjoint',
    'Mldsa.Decode.zp2_is_two_powers',
    'Mldsa.Decode.zp4_is_two_powers',
    'Mldsa.Decode.zp6_is_two_powers',
    'Mldsa.Encoding.all_zero_replicate',
    'Mldsa.Encoding.decRows_canonical',
    'Mldsa.Encoding.hint_decode_canonical',
    'Mldsa.Encoding.hint_decode_injective',
    'Mldsa.Encoding.hint_weight_le_omega',
    'Mldsa.Encoding.strictInc_rejects_permutation',
    'Mldsa.Encoding.strictInc_rejects_repeat',
    'Mldsa.Encoding.padding_gate_rejects_nonzero',
    'Mldsa.Encoding.mprime_injective',
    'Mldsa.Encoding.ctx_len_gate_is_load_bearing',
    'Mldsa.Encoding.pure_prehash_disjoint',
]


AUDIT_RE = re.compile(
    r"'([A-Za-z0-9_.']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")

# ---------------------------------------------------------------------------
# The audited theorem STATEMENTS, pinned.
#
# Names and axiom lists alone are not enough: a theorem could be weakened to
# `True`, or to a statement about different constants, and stay sorry-free with
# an unchanged name and an unchanged axiom list, and every other check in the
# repository would stay green.
#
# EXPECTED_STATEMENTS pins a digest of each audited theorem's STATEMENT -- the
# text between `theorem <name>` and the top-level `:=`, comment-stripped and
# whitespace-normalised, so reformatting and re-commenting do not churn it while
# any change to a binder, a hypothesis or a conclusion does.
#
# What this cannot do: it is tamper-EVIDENCE, not a semantic check.  It says the
# statement is the one that was PINNED, not that the statement is the right
# one.  Regenerate deliberately with --print-statements.
DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z0-9_.']+)")
NS_RE = re.compile(r"(?m)^\s*namespace\s+([A-Za-z0-9_.']+)|^\s*end\s+([A-Za-z0-9_.']+)")


def theorem_statements(files):
    """{fully-qualified name: normalised statement} for every theorem/lemma."""
    out = {}
    for path in files:
        src = strip_comments(open(path, encoding="utf-8").read())
        events = [(m.start(), m.group(1), m.group(2)) for m in NS_RE.finditer(src)]
        for m in DECL_RE.finditer(src):
            stack = []
            for pos, op, cl in events:
                if pos > m.start():
                    break
                if op:
                    stack.append(op)
                elif cl and stack and stack[-1] == cl:
                    stack.pop()
            name = ".".join(stack + [m.group(1)])
            i, n, depth = m.end(), len(src), 0
            while i < n - 1:
                c = src[i]
                if c in "([{⟨":
                    depth += 1
                elif c in ")]}⟩":
                    depth -= 1
                elif depth == 0 and src.startswith(":=", i):
                    break
                i += 1
            out[name] = " ".join(src[m.end():i].split())
    return out


def statement_digest(stmt):
    return hashlib.sha256(stmt.encode("utf-8")).hexdigest()[:32]


EXPECTED_STATEMENTS = {
    'Mldsa.Barrett.mu_is_floor': '09218c60b6494a2844bf27103e6d41f0',
    'Mldsa.Barrett.mu_q_add_d': '2255a371880d4aeeb5e076cd06e5ec5f',
    'Mldsa.Barrett.unit_step_is_floor': 'cca515eaddc7746af14c86e5d78228be',
    'Mldsa.Barrett.q_sparse_form': '953b831b69927bcb0e0293c7b66425b6',
    'Mldsa.Barrett.no_borrow': '6aa7e03b292fe86e678c18daac9474aa',
    'Mldsa.Barrett.second_no_borrow': '2a51aa0c3d26f928568b1ecc0085d084',
    'Mldsa.Barrett.barrettNat_lt_two_q': '60c90e865d6716376ea1f4f758148ed1',
    'Mldsa.Barrett.step1_lt_two_pow_33': '7ce7b3820dad24ba210f73543da2b9e3',
    'Mldsa.Barrett.barrettEVM_eq_nat': 'be3b32c16bf05c201dc7af73773aaa9e',
    'Mldsa.Barrett.barrettEVM_lt_two_q': '466fdc2da9034fedd507944bd3ff2340',
    'Mldsa.Barrett.barrettNat_congr': 'b5d5cb54ae56c4384e1c227fc256de0c',
    'Mldsa.Barrett.lane_product_lt_two_pow_63': 'b3d7d565b1a4cb64c1e55e28e7dbc69d',
    'Mldsa.Barrett.qhat_lt_two_pow_31': 'c93ed1f459b9941ba72a0dc419ab4081',
    'Mldsa.Barrett.barrett_forward': 'a52cbfa43d1f73cb47750e90def8f900',
    'Mldsa.Barrett.barrett_inverse': '79d664e78a275cb3b69412055b946c10',
    'Mldsa.Barrett.barrett_inverse_congr': 'a1defb55a30a2718621af386288f52c3',
    'Mldsa.Barrett.firstFail_breaks': 'e7ed8704a3342d035d30f68aad02fbdd',
    'Mldsa.Barrett.firstFail_pred_ok': 'e134aa457f4d0800439302fbe0d83304',
    'Mldsa.Barrett.invMax_lt_firstFail': 'e17984a655d1d2ac27c3b03fc7ff8f29',
    'Mldsa.Barrett.margin_guard': 'c74f05559eb06acbc22d22e619ac5d45',
    'Mldsa.Barrett.margin_guard_hmg': 'e38ae0d2e7149d1ce2086699ab7aae2e',
    'Mldsa.Barrett.lane_cliff_above_firstFail': 'd2d2847e1e727d9444e6068051504935',
    'Mldsa.Barrett.lane_cliff_breaks': '128d4176d17d63af762540c0cb0cec4c',
    'Mldsa.Barrett.step1_alone_is_not_enough': 'f69f799762651640a5d320652074593a',
    'Mldsa.Barrett.swar_step1_lane_independent': '5a536524fb490ac03d2e807b8d70fc8d',
    'Mldsa.Barrett.swar_lane_independent': 'ff66529ad6c570016c14dd22be0cc836',
    'Mldsa.Barrett.swar_lane_fits': 'dcb9b593800465a41b49f95b17a25834',
    'Mldsa.Decode.u_bounds': 'b533853024a5b68a04d8b2eb62f77961',
    'Mldsa.Decode.u_lt_two_q': '82ec8d455dcd53dbc1bdfc5591d4708a',
    'Mldsa.Decode.flag_no_carry': 'a6a17351b079d545b2e8922f8733b36b',
    'Mldsa.Decode.flag_is_a_bit': '7e4ea06bc732a5281b8584b8eac6c750',
    'Mldsa.Decode.flag_iff_u_ge_q': '020bb9b5ac73402406ef897641f29920',
    'Mldsa.Decode.canon_lt_q': '65557bb9b6b585c92417165b67d0e033',
    'Mldsa.Decode.canon_closed_form': 'cbd9916313597e0673e6998eb75eaddb',
    'Mldsa.Decode.canon_zero_field': 'eab3ded7fc9e679314f47c76201fddb0',
    'Mldsa.Decode.lo_no_carry': '6b44ffee822e962a553e9cbbf9a6247c',
    'Mldsa.Decode.hi_no_borrow': '333504e726653dc83226af731dafb434',
    'Mldsa.Decode.lo_iff': '46bf684f656e630f9fda560964dd8072',
    'Mldsa.Decode.hi_iff': '5fb528d93061ab0528ebf40595200ada',
    'Mldsa.Decode.reject_iff_fips': '23e6046e8f5ba8825416e9961c129d83',
    'Mldsa.Decode.boundary_low_rejected': '11bc6026413b0b60bc76d48e5f9f2def',
    'Mldsa.Decode.boundary_low_inside_accepted': '28a55643f1c4093c41f254e6dd6f0b23',
    'Mldsa.Decode.boundary_high_rejected': 'eabc1edef91fd5e39cd92a0d11c72dda',
    'Mldsa.Decode.boundary_high_inside_accepted': 'cfa54ac3afcdab4d9185ef00c93e40c3',
    'Mldsa.Decode.addSplit4': 'a8a4c072d2e99ce311ba2a422f484b32',
    'Mldsa.Decode.subFromRep4': 'd7e316c10ebd2191f4e029bbc60653f0',
    'Mldsa.Decode.swar_z_lane_independent': '2c5391fe07461680b11efd20152bee53',
    'Mldsa.Decode.flag_word_lane_fits': '0d7718c81975acab22e6e8187c0e0e48',
    'Mldsa.Decode.fused_split': '2ed6a1ee378dab46ef98b3e04b694c04',
    'Mldsa.Decode.fused_disjoint': '898d2b4fd2aedf69c116ca3f4130d38e',
    'Mldsa.Decode.zp2_is_two_powers': '0751cf70cd06d57cf0b0d03158ba79f2',
    'Mldsa.Decode.zp4_is_two_powers': '428d781d99905ffdca421b377e365ee2',
    'Mldsa.Decode.zp6_is_two_powers': 'b25718d5bf7811b45f0dbfc7324cead6',
    'Mldsa.Encoding.all_zero_replicate': 'a700fa76a5ebce4b2086e900058c9e4f',
    'Mldsa.Encoding.decRows_canonical': '961ffc61062f6850c2ef0d38ed5dfee2',
    'Mldsa.Encoding.hint_decode_canonical': 'cf8b6c0420bf1a0418556d59d9e59951',
    'Mldsa.Encoding.hint_decode_injective': '55708476f58b5b3dfa41a368e2c8a3bf',
    'Mldsa.Encoding.hint_weight_le_omega': '4b490d1bfce22fc82413f90b5ccd724c',
    'Mldsa.Encoding.strictInc_rejects_permutation': '58504f7c5a432ed39c439554607bfdf7',
    'Mldsa.Encoding.strictInc_rejects_repeat': '3cfb05b5f85f47416147a9b84d11dfa4',
    'Mldsa.Encoding.padding_gate_rejects_nonzero': '0afa35494dbb122ef82109d030ab8507',
    'Mldsa.Encoding.mprime_injective': 'd83a36f2d5565ff7f447ffe2426dfa01',
    'Mldsa.Encoding.ctx_len_gate_is_load_bearing': 'cf5481657e966b2079490b63eee414f0',
    'Mldsa.Encoding.pure_prehash_disjoint': '14736e27a42357abc0f0e3e123f2daf5',
}



def strip_comments(src):
    """Remove `--` line comments and `/- ... -/` block comments (nesting-aware)."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "".join(out)


def scan_sources():
    problems = []
    files = []
    for root, _dirs, names in os.walk(HERE):
        if ".lake" in root:
            continue
        for nm in sorted(names):
            if nm.endswith(".lean"):
                files.append(os.path.join(root, nm))
    for path in sorted(files):
        code = strip_comments(open(path, encoding="utf-8").read())
        for lineno, line in enumerate(code.splitlines(), 1):
            for pat, why in FORBIDDEN:
                if re.search(pat, line):
                    problems.append(f"{os.path.relpath(path, HERE)}:{lineno}: {why} -> {line.strip()[:100]}")
    return files, problems


# The files that make the Lean package a package.  Everything else the sandbox
# build sees is a `.lean` source found by `scan_sources`.
PACKAGE_FILES = ("lakefile.toml", "lean-toolchain", "lake-manifest.json")


def run_lake(files, keep=False):
    """Elaborate the WHOLE development FROM SOURCE, in a throwaway tree.

    Running `lake build` in the working tree is NOT a check: on a warm cache
    `lake build` does not elaborate anything, it REPLAYS the messages stored in
    `.lake/build/lib/lean/Mldsa/*.trace`, so every verdict would be a read of a
    build artefact.  `formal/z3/source_pins.py` pins every file under `formal/`
    EXCEPT `lean/.lake` (`SKIP_REL_DIRS`), so that artefact is covered by no manifest:
    replacing a single `.olean` under `.lake/` with one built from a source
    containing `sorry` would make a warm-cache check report a clean axiom base
    for a proof that is a hole.

    So the check does not read `.lake` at all.  It copies the package files and
    every `.lean` source into a fresh directory that HAS no build cache and
    elaborates there, from nothing.  Every `#print axioms` line the audit reads
    is then produced by this run's kernel, and no file under `formal/lean/.lake`
    can influence the verdict -- which is also what makes `SKIP_REL_DIRS =
    ("lean/.lake",)` in source_pins.py (anchored to that ONE path, not to
    `.lake` wherever it appears) safe rather than merely convenient.

    Cost: a few seconds to a few minutes (the development has no external
    dependencies).  There is no flag to skip it; a check with a fast path is a
    check with a bypass.
    """
    tmp = tempfile.mkdtemp(prefix="mldsa-lean-elab-")
    try:
        for rel in PACKAGE_FILES:
            src = os.path.join(HERE, rel)
            if os.path.exists(src):
                shutil.copy(src, os.path.join(tmp, rel))
        for path in files:
            dst = os.path.join(tmp, os.path.relpath(path, HERE))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy(path, dst)
        if os.path.exists(os.path.join(tmp, ".lake")):
            return 3, f"sandbox {tmp} already holds a build cache", tmp
        r = subprocess.run([LAKE, "build"], cwd=tmp, capture_output=True,
                           text=True, timeout=7200)
        return r.returncode, r.stdout + r.stderr, tmp
    finally:
        if not keep:
            shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep-sandbox", action="store_true",
                    help="do not delete the throwaway elaboration tree (debugging)")
    ap.add_argument("--print-theorems", action="store_true")
    ap.add_argument("--print-statements", action="store_true",
                    help="regenerate EXPECTED_STATEMENTS")
    args = ap.parse_args()

    print("=" * 78)
    print("Lean axiom check — `sorry` / custom-axiom hard check")
    print("=" * 78)
    fail = []

    # ---- 1. static scan ----------------------------------------------------
    files, problems = scan_sources()
    print(f"[1] scanned {len(files)} .lean files for proof escape hatches: "
          f"{'CLEAN' if not problems else str(len(problems)) + ' PROBLEM(S)'}")
    for p in problems:
        print(f"    !! {p}")
    fail += problems

    if not os.path.exists(LAKE):
        print(f"[2] !! lake not found at {LAKE} (set $LAKE) — THE CHECK DID NOT RUN")
        return 2

    # ---- 2. build ----------------------------------------------------------
    # FORCED ELABORATION.  A fresh tree with no `.lake`, so nothing can be
    # replayed from a cache; the digests below are of the exact bytes
    # elaborated, and `formal/z3/source_pins.py` pins the same files.
    t0 = time.time()
    rc, out, tmp = run_lake(files, keep=args.keep_sandbox)
    print(f"[2] FORCED FULL ELABORATION in a cache-free sandbox: "
          f"`lake build` exit={rc} in {time.time() - t0:.1f}s "
          f"({len(files)} .lean sources + {len(PACKAGE_FILES)} package files copied; "
          f"no .lake read){' [' + tmp + ']' if args.keep_sandbox else ''}")
    for path in sorted(files):
        digest = hashlib.sha256(open(path, "rb").read()).hexdigest()[:16]
        print(f"    elaborated {digest}  {os.path.relpath(path, HERE)}")
    if rc != 0:
        fail.append(f"lake build exited {rc}")
        print(out[-3000:])

    # ---- 3/4. the axiom audit ---------------------------------------------
    n_directives = open(os.path.join(HERE, "Mldsa", "Audit.lean"), encoding="utf-8") \
        .read().count("#print axioms ")
    audited = {}
    for m in AUDIT_RE.finditer(out):
        name = m.group(1)
        axl = m.group(2)
        audited[name] = sorted(a.strip() for a in axl.split(",")) if axl else []

    print(f"[3] axiom-audit lines: {len(audited)} for {n_directives} `#print axioms` directives")
    if len(audited) != n_directives:
        fail.append(f"only {len(audited)} of {n_directives} audited theorems reported")

    if args.print_theorems:
        print("\nEXPECTED_THEOREMS = [")
        for k in audited:
            print(f"    {k!r},")
        print("]")

    missing = [t for t in EXPECTED_THEOREMS if t not in audited]
    extra = [t for t in audited if t not in EXPECTED_THEOREMS]
    if missing:
        fail.append(f"audited theorem(s) MISSING from the build output: {missing}")
        print(f"    !! missing: {missing}")
    if extra:
        fail.append(f"unexpected audited theorem(s): {extra}")
        print(f"    !! unexpected: {extra}")

    bad_ax = {t: a for t, a in audited.items() if set(a) - ALLOWED_AXIOMS}
    print(f"[4] theorems depending on anything outside "
          f"{{propext, Quot.sound, Classical.choice}}: {len(bad_ax)}")
    for t, a in bad_ax.items():
        print(f"    !! {t} depends on {a}")
        fail.append(f"{t} depends on {a}")

    # ---- 5. belt and braces on the raw log --------------------------------
    hits = [ln.strip() for ln in out.splitlines()
            if "sorryAx" in ln or "declaration uses 'sorry'" in ln]
    print(f"[5] build output lines mentioning sorry/sorryAx: {len(hits)}")
    for h in hits[:20]:
        print(f"    !! {h[:160]}")
    fail += [f"build log: {h[:120]}" for h in hits]

    # ---- 6. the audited theorems' STATEMENTS, pinned ----------------------
    stmts = theorem_statements(files)
    if args.print_statements:
        print("\nEXPECTED_STATEMENTS = {")
        for t in EXPECTED_THEOREMS:
            if t in stmts:
                print(f"    {t!r}: {statement_digest(stmts[t])!r},")
        print("}")
    absent = [t for t in EXPECTED_THEOREMS if t not in stmts]
    unpinned = [t for t in EXPECTED_THEOREMS if t in stmts and t not in EXPECTED_STATEMENTS]
    moved = [t for t in EXPECTED_THEOREMS
             if t in stmts and t in EXPECTED_STATEMENTS
             and statement_digest(stmts[t]) != EXPECTED_STATEMENTS[t]]
    print(f"[6] audited theorem STATEMENTS pinned: "
          f"{len(EXPECTED_STATEMENTS)}/{len(EXPECTED_THEOREMS)}; "
          f"{len(absent)} not found in source, {len(unpinned)} unpinned, {len(moved)} CHANGED")
    for t in absent:
        print(f"    !! statement not found in any .lean source: {t}")
    for t in unpinned:
        print(f"    !! statement not pinned (regenerate with --print-statements): {t}")
    for t in moved:
        print(f"    !! STATEMENT CHANGED: {t}")
        print(f"       now: {stmts[t][:140]}")
    fail += [f"statement missing: {t}" for t in absent]
    fail += [f"statement unpinned: {t}" for t in unpinned]
    fail += [f"statement changed: {t}" for t in moved]

    print("=" * 78)
    if fail:
        print(f"FAIL — {len(fail)} problem(s); the Lean axiom base is NOT clean")
        print("=" * 78)
        return 1
    print(f"PASS — {len(audited)} theorems, 0 sorry, 0 custom axioms, "
          f"only Lean's own {sorted(ALLOWED_AXIOMS)}; "
          f"{len(EXPECTED_STATEMENTS)} theorem statements pinned; "
          f"every axiom line produced by THIS run's kernel from a cache-free "
          f"elaboration of the {len(files)} sources digested above")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
