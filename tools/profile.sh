#!/usr/bin/env bash
# tools/profile.sh — gas-profiling workflow for the ML-DSA-44 EVM verifier.
#
# Produces, in ./profiles/ (untracked, see .gitignore):
#   e2e_gas.txt          canonical end-to-end number from test/E2E.t.sol
#                        (test_e2e_10: measured 1,226,311 on forge 1.4.2-nightly
#                        c808c4cd, solc 0.8.30, evm osaka)
#   flamegraph_verify.svg   flame GRAPH (sorted by cost) of ONE verify() call
#   flamechart_verify.svg   flame CHART (execution order) of the same call
#   flamegraph_stages.svg   flame graph of the staged pipeline, one frame per
#                           shipped kernel (PROFILE_E2ETest::_stage_*)
#   stages.txt           exact per-stage gasleft() brackets + per-pass NTT
#                        profile (the numbers; flamegraphs are the pictures)
#   gas_report.txt       forge --gas-report for the profile run
#   trace_verify.txt     full --decode-internal -vvvv trace of one verify()
#                        (shows all 9 F1600 helper STATICCALLs individually)
#   SUMMARY.txt          stage table extracted from stages.txt
#
# KNOWN LIMITS (why the staged view exists):
#   * foundry's --flamegraph/--decode-internal only labels CONTRACT MEMBER
#     functions. The verifier's kernels are file-level free functions
#     (nttFwV3, matvecRow, unpackZPacked, useHintSwar, shake256Fast170, ...)
#     and get NO frames of their own — test/PROFILE_E2E.t.sol wraps each in a
#     named member function and brackets it with gasleft(), so the stage
#     flamegraph + stages.txt recover that granularity.
#   * The Keccak-f[1600] helper is raw runtime bytecode (helpers/
#     f1600_170.hex) with no source: its 9 STATICCALLs are visible (41,373 gas
#     each incl. call overhead) but its interior cannot be decoded.
#   * Pass-level NTT granularity comes from the gas()-snapshot `prof` arrays
#     already plumbed through src/Ntt.sol / src/InvNtt.sol. The FORWARD runs
#     its eight layers as THREE fused passes (radix-8 L1+L2+L3, radix-8
#     L4+L5+L6, in-word L7+L8) and writes 4 snapshots delimiting 3 blocks; the
#     INVERSE runs FOUR and writes 5 -- the same blocks Z3 obligation C16
#     extracts from the shipped Yul.
#
# Prerequisites: pythonref/myenv virtualenv (see README.md); tests use vm.ffi.
set -euo pipefail
cd "$(dirname "$0")/.."

PROF_DIR=profiles
MC=(--match-contract 'PROFILE_E2ETest$')

if [ ! -x pythonref/myenv/bin/python ]; then
    echo "ERROR: pythonref/myenv virtualenv missing — see README.md" >&2
    exit 1
fi

mkdir -p "$PROF_DIR"
forge --version | tee "$PROF_DIR/forge_version.txt"

echo "== [1/6] canonical E2E gas (test/E2E.t.sol test_e2e_10) =="
forge test --match-contract 'E2ETest$' --match-test test_e2e_10 -vv \
    | tee "$PROF_DIR/e2e_gas.txt"

echo "== [2/6] flame graph + flame chart of one verify() call =="
forge test "${MC[@]}" --match-test 'test_profile_00_verify' --flamegraph
cp cache/flamegraph_PROFILE_E2ETest_test_profile_00_verify.svg "$PROF_DIR/flamegraph_verify.svg"
forge test "${MC[@]}" --match-test 'test_profile_00_verify' --flamechart
cp cache/flamechart_PROFILE_E2ETest_test_profile_00_verify.svg "$PROF_DIR/flamechart_verify.svg"

echo "== [3/6] flame graph of the staged pipeline (per-kernel frames) =="
forge test "${MC[@]}" --match-test 'test_profile_10_stages' --flamegraph
cp cache/flamegraph_PROFILE_E2ETest_test_profile_10_stages.svg "$PROF_DIR/flamegraph_stages.svg"

echo "== [4/6] per-stage brackets + NTT layer profile =="
forge test "${MC[@]}" -vv | tee "$PROF_DIR/stages.txt"

echo "== [5/6] gas report =="
forge test "${MC[@]}" --gas-report > "$PROF_DIR/gas_report.txt"

echo "== [6/6] decoded trace of one verify() =="
forge test "${MC[@]}" --match-test 'test_profile_00_verify' \
    --decode-internal -vvvv > "$PROF_DIR/trace_verify.txt"

# stage table for quick reading
{
    echo "forge: $(forge --version | head -1)"
    grep -E "E2E gas, MLDSA44Verifier" "$PROF_DIR/e2e_gas.txt" || true
    echo "--- per-stage brackets (gasleft), test_profile_10_stages ---"
    sed -n '/stage /p;/staged kernel sum/p;/external verify/p;/residual/p;/harness slice/p' "$PROF_DIR/stages.txt"
    echo "--- NTT pass profile (prof arrays), test_profile_20_ntt_layers ---"
    sed -n '/nttFwV3 total/,/inv pass 4/p' "$PROF_DIR/stages.txt"
    echo "--- F1600 helper staticcalls in one verify() ---"
    grep -oE "\[[0-9]+\] F1600_keccak_helper" "$PROF_DIR/trace_verify.txt" | sort | uniq -c
} > "$PROF_DIR/SUMMARY.txt"

echo
echo "Artifacts in $PROF_DIR/:"
ls -la "$PROF_DIR"
