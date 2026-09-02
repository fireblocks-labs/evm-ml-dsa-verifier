#!/usr/bin/env python3
# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
"""
halmos driver for the bytecode-level obligation suites.

    python3 run_halmos.py [--halmos PATH] [--cap SECONDS] [--contracts A,B,...]

Runs one function per process (halmos leaks state between functions otherwise),
at `--loop 16` — the default of 2 is a bounded unroll that silently produces
fast bogus PASSes — and reports the per-function verdict tag, because halmos
prints a TIMEOUT as "0 passed; 1 failed" in its summary line and it would be
easy to mistake a solver giving up for a broken property.

Contracts:
  FVKernels   / FVCanaries    test/FV_Kernels.sol
  FV2Barrett  / FV2Canaries   test/FV2_Barrett.sol

Canary contracts MUST report every function as FAIL; anything else invalidates
the corresponding proofs.
"""
import argparse, json, os, re, shutil, subprocess, sys, time

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

# repository root = the foundry root the harness contracts live under
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
SUITES = {
    "FVKernels": ("test/FV_Kernels.sol", "PASS"),
    "FVCanaries": ("test/FV_Kernels.sol", "FAIL"),
    "FV2Barrett": ("test/FV2_Barrett.sol", "PASS"),
    "FV2Canaries": ("test/FV2_Barrett.sol", "FAIL"),
}

# ---------------------------------------------------------------------------
# THE OBLIGATION SET IS AN ASSERTION
# ---------------------------------------------------------------------------
# `functions_of()` DISCOVERS `check_*` functions by regex, so deleting an
# obligation from the .sol file would shrink the run and still report every
# discovered function "as expected".  The names are pinned here, per contract,
# and a full run aborts unless the discovered set is exactly this one.
# Regenerate with `--print-functions` ONLY after reviewing the harness diff.
#
# WHY THESE ARE GENERATED, NOT HAND-MAINTAINED.  These names track the
# TWO-STEP LANE-LOCAL reduction.  A stale set here -- "spread"-form
# identifiers such as `check_c3_spreadBarrett2` or
# `check_w11_spreadIsTheComposition`, naming a kernel this tree does not
# contain -- aborts EVERY invocation of this driver with exit 4 before it
# reaches the solver, and a check that cannot run is not a check.  Regenerate
# from `--print-functions` and read the harness diff; do not hand-edit.
EXPECTED_FUNCTIONS = {
    "FVKernels": [
        "check_a1_centeredMapStrict", "check_a2_normTestStrict",
        "check_a3_normTestLoose", "check_a4_centeredMapLoose",
        "check_a5_bitExtract", "check_b1_useHint",
        "check_c1_lazyBarrettForward", "check_c2_lazyBarrettInverse",
        "check_c1a_barrettCongruenceOnly", "check_c1b_barrettQhatBound",
        "check_c1c_barrettLazyBound", "check_c1d_barrettLazyBoundNarrow",
        "check_c1e_barrettLazyBoundWitness", "check_c3_swarQhatMasksLanes",
        "check_c4_swarBarrett4", "check_c6_swarQhatMaskWitness",
        "check_c7_swarBarrettWitness", "check_f1_pack6",
    ],
    "FVCanaries": [
        "check_c0_toolDetectsFailures", "check_c1_vacuity_a1",
        "check_c2_vacuity_b1", "check_c4_useHintNeedsCanonicalInput",
        "check_c5_swarNeedsLaneBound", "check_c6_step2IsLoadBearing",
    ],
    "FV2Barrett": [
        "check_w0_domainConstants", "check_w1_firstMulIsLaneLocal",
        "check_w2_shrIsFloorDiv", "check_w3_qhatFitsAndSecondMulNoWrap",
        "check_w4_subIsExactWhenNoBorrow", "check_w5_kernelIsTheOpcodeChain",
        "check_w6_transfer", "check_w7_andQhatm31Model",
        "check_w8_step2MaskModel", "check_w8b_lanePackingIsLossless",
        "check_w9_packedMulIsLaneLocal", "check_w10_swarIsTheComposition",
        "check_w11_swarStepsAreMaskedScalarSteps",
        "check_w11b_swarIsLanewiseScalar", "check_w12_firstFailIsReal",
    ],
    "FV2Canaries": [
        "check_k0_toolBites", "check_k1_domainIsLoadBearing",
        "check_k2_w6NotVacuous", "check_k3_swarNeedsLaneBound",
        "check_k4_subNeedsNoBorrow", "check_k5_step2IsLoadBearing",
        "check_k6_qhatm31IsNotIdentity",
    ],
}


def functions_of(path, contract):
    src = open(os.path.join(ROOT, path)).read()
    start = src.index(f"\ncontract {contract} ")   # declaration, not a comment
    rest = src[start + 1:]
    nxt = rest.find("\ncontract ")
    body = rest if nxt < 0 else rest[:nxt]
    return re.findall(r"function (check_[A-Za-z0-9_]+)\(", body)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--halmos", default=os.environ.get("HALMOS", "halmos"))
    ap.add_argument("--cap", type=int, default=330)
    ap.add_argument("--assertion-timeout", type=int, default=300000)
    ap.add_argument("--contracts", default=",".join(SUITES))
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__), "halmos_results.json"))
    ap.add_argument("--print-functions", action="store_true",
                    help="regenerate EXPECTED_FUNCTIONS")
    args = ap.parse_args()

    if args.print_functions:
        print("EXPECTED_FUNCTIONS = {")
        for c, (p, _e) in SUITES.items():
            print(f"    {c!r}: {functions_of(p, c)!r},")
        print("}")
        return 0

    # the discovered obligation set must be the PINNED one, per contract
    bad = []
    for contract in sorted(SUITES):
        want = EXPECTED_FUNCTIONS[contract]
        got = functions_of(SUITES[contract][0], contract)
        if got != want:
            bad.append(f"{contract}: discovered {len(got)} obligations, pinned "
                       f"{len(want)}; missing {sorted(set(want) - set(got))}, "
                       f"unpinned {sorted(set(got) - set(want))}")
    if bad:
        for b in bad:
            print(f"ABORT: {b}", file=sys.stderr)
        return 4

    if shutil.which(args.halmos) is None:
        print(f"ABORT: halmos executable not found ({args.halmos!r}); the pinned "
              f"obligation sets above were verified against the harness, but no "
              f"solver run was performed", file=sys.stderr)
        return 3

    results = []
    for contract in args.contracts.split(","):
        contract = contract.strip()
        path, expect = SUITES[contract]
        fns = functions_of(path, contract)
        print(f"\n=== {contract} ({path}): {len(fns)}/{len(EXPECTED_FUNCTIONS[contract])} "
              f"pinned obligations, expect {expect} ===", flush=True)
        for fn in fns:
            cmd = [args.halmos, "--contract", contract, "--function", fn, "--loop", "16",
                   "--solver-timeout-assertion", str(args.assertion_timeout)]
            t0 = time.time()
            try:
                r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                                   timeout=args.cap)
                out = r.stdout
                if "[TIMEOUT]" in out:
                    v = "TIMEOUT"
                elif "[ERROR]" in out:
                    v = "ERROR"
                elif "[PASS]" in out:
                    v = "PASS"
                elif "[FAIL]" in out:
                    v = "FAIL"
                else:
                    v = "UNKNOWN"
            except subprocess.TimeoutExpired:
                v = "WALL-TIMEOUT"
            dt = time.time() - t0
            good = (v == expect)
            print(f"{contract}.{fn}: {v:<12} {dt:6.1f}s {'ok' if good else '!!'}", flush=True)
            results.append(dict(contract=contract, function=fn, verdict=v,
                                seconds=round(dt, 1), expected=expect, ok=good))
            json.dump(results, open(args.out, "w"), indent=1)

    print("\n" + "=" * 70)
    for contract in args.contracts.split(","):
        c = contract.strip()
        rs = [r for r in results if r["contract"] == c]
        okc = sum(1 for r in rs if r["ok"])
        print(f"{c:<14} {okc}/{len(rs)} as expected ({SUITES[c][1]})")
        for r in rs:
            if not r["ok"]:
                print(f"    !! {r['function']}: {r['verdict']}")
    print("=" * 70)
    return 0 if all(r["ok"] for r in results) else 1


if __name__ == "__main__":
    sys.exit(main())
