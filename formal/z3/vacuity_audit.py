#!/usr/bin/env python3
# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
"""
Vacuity audit for the machine-checked obligation suite.

    python3 vacuity_audit.py [--jobs 4] [--ids V01,V07]

The question every obligation has to answer is not "does it pass?" but
**"would it fail if the thing it names were wrong?"**  Obligations can fail that
test in ways reading cannot see: a tautology, or a claim quantified over the
specification instead of the implementation.  Re-reading them is not a method.
This is: the audit MUTATES the obligation suite's own kernel models and records,
for every obligation ID, which mutations it detects.

    KILLED-BY >= 1   the obligation is sensitive to the implementation it names
    NEVER KILLED     the obligation passes no matter how the modelled kernel is
                     broken -> it is checking something else (or nothing)

THREE PROPERTIES THIS AUDIT MUST HAVE, and why none of them is automatic:

 1. PER-CONJUNCT, NOT PER-OBLIGATION.  Aggregating killers by obligation ID is
    not enough: the catalogue holds at most one mutation per obligation, so
    every conjunct that no mutation targets could be DELETED and the obligation
    would still be "sensitive to at least one injected defect".  Eight such
    deletions across E14/O7/O2/O8 pass both a per-obligation audit and the
    suite.  `verify_all.py` therefore emits one `[PASS]/[FAIL] <oid>.<conjunct>`
    line per conjunct, and this audit aggregates on those.  A conjunct no
    mutation can break is reported and FAILS the audit unless it is in
    CONJUNCT_EXEMPT with a written reason.

 2. A MUTATION THAT KILLS NOTHING IS A BLIND SPOT, so the audit has to say so.
    A row in `vacuity_results.json` with `failed: []` is an injected,
    non-equivalent defect that the entire suite failed to notice; a summary
    reporting only "obligations killed by nothing" hides it.  That category is
    printed first and fails the audit.

 3. A MUTATION THAT CRASHES THE SUITE must not read as "kills 0".  `run_one`
    computes `crashed` and `main()` treats it as a hard error.

Two verdicts are expected and are recorded as such rather than treated as
failures:
  * a mutation that is SEMANTICALLY EQUIVALENT must kill nothing (`equiv=True`);
    if it kills something, that obligation is over-specified.
  * an obligation that is a pure design fact (a width, a degree, a layout) is
    not a kernel model and is only killed by mutating its own claim; those
    mutations are in the catalogue too and are tagged `claim=True`.

Runtime: the suite is ~60 s, so a full audit is `#mutations x 60 s / jobs`.
Exit code 0 iff every obligation AND every conjunct is load-bearing, every
non-equivalent mutation kills something, and nothing crashed.
"""
import argparse, json, os, re, shutil, subprocess, sys, tempfile
from concurrent.futures import ProcessPoolExecutor

# No .pyc may ever exist under formal/: a bytecode cache is a payload that no
# source digest covers.  The env var matters as much as the flag -- the worker
# processes and the `verify_all.py` subprocesses inherit the env, not sys.flags.
sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", ".."))
PY = os.path.join(HERE, "..", "..", "pythonref", "myenv", "bin", "python")
V = "verify_all.py"
O = "kernel_obligations.py"
S = "source_pins.py"        # imported by verify_all.py for the META-PINS tripwire

# The suite is copied into a temp dir for each mutation; C16 reads the SHIPPED
# Solidity, so the copy has to be told where the repository is.
ENV = dict(os.environ, MLDSA_REPO=REPO)

# ---------------------------------------------------------------------------
# Conjuncts that no mutation in this catalogue can break, WITH A REASON.
# The audit fails on any never-killed conjunct that is not listed here, so this
# list is the complete, reviewable set of "checks we cannot check".
# ---------------------------------------------------------------------------
# There is NO wildcard and NO suffix rule here.  A rule of the form
#     if cid.endswith("premises_sat"): return CONJUNCT_EXEMPT["*.premises_sat"]
# would exempt an ADDED conjunct by name alone, which makes the exempt set
# unbounded.  Instead the premise-satisfiability guards are funnelled through
# ONE place per module (`prove()` in verify_all.py, `_prem_sat()` in
# kernel_obligations.py), so mutations VT06/VT07 falsify EVERY one of them at
# once and not one of them needs an exemption.  The exempt set is therefore
# only META-PINS's own conjuncts, each listed individually, by exact name, and
# for the structural reason spelled out below: the sandbox copy is not the repo
# file, so this one tripwire moves under every mutation in the catalogue.
CONJUNCT_EXEMPT = {
    # META-PINS digests the suite's own source and the whole formal/ tree, so
    # EVERY mutation moves it; its kills carry no information about any
    # obligation and are filtered out of the audit's accounting in `run_one`
    # (see the note there).  That it bites is not in question -- it bites on
    # every one of the mutations -- so exempting it from the "is this conjunct
    # load-bearing?" question is the correct reading, not a concession.
    # Every one of META-PINS's conjuncts is listed here individually, by name.
    "META-PINS.all_regions_pinned":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.no_unpinned_regions":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.every_region_digest_matches":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.every_formal_file_pinned":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.every_pinned_file_present":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.every_formal_file_digest_matches":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.no_bytecode_cache_under_formal":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.executing_modules_are_the_pinned_bytes":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.no_alternate_source_encoding":
        "source-digest tripwire; the sandbox copy is not the repo file, so this conjunct is moved by EVERY mutation and its kills carry no information about any obligation -- filtered from kill accounting in run_one",
    "META-PINS.blanked_regions_are_inert_data":
        "source-digest tripwire (the two BLANKED pin tables and the six BLANKED ANCHOR_* lines must be provably inert data); the sandbox has no run_checks.sh and its source_pins.py is regenerated, so this conjunct carries no information about any obligation -- filtered from kill accounting in run_one",
}


# The obligation row of the same tripwire, for the same reason.
OBLIGATION_EXEMPT = {
    "META-PINS": "source-digest tripwire; moved by every mutation, so filtered "
                 "from kill accounting (see run_one)",
}


def exempt_reason(cid):
    """Exact membership only -- no wildcards, no suffix rules."""
    return CONJUNCT_EXEMPT.get(cid) or OBLIGATION_EXEMPT.get(cid)

# ---------------------------------------------------------------------------
# Mutations.  `old` must occur exactly `count` times in `file`.
#   kind="kernel"  breaks a modelled KERNEL -> the obligations that model that
#                  kernel against the FIPS reference must FAIL
#   kind="claim"   breaks the CLAIM of a closed-form fact -> that fact must FAIL
#   equiv=True     provably semantics-preserving -> nothing may fail
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# THE CATALOGUE IS AN ASSERTION
# ---------------------------------------------------------------------------
# `mutations run: {len(results)}` is not enough on its own.  430 of the 641 rows
# have exactly one killer, so deleting one of those mutations is caught as a
# never-killed conjunct -- but 65 of the 166 mutations are the sole killer of
# nothing, and deleting one of THOSE would shrink the audit silently.  The
# catalogue ID set is pinned here and a full run (no `--ids`) aborts if it moves.
EXPECTED_MUTATIONS = [
    'V01',
    'V02',
    'V02b',
    'V03',
    'V04',
    'V05',
    'V06',
    'V07',
    'V08',
    'V24',
    'V25',
    'V29',
    'V29b',
    'V29c',
    'V29d',
    'V29e',
    'V29f',
    'V29g',
    'V29h',
    'V29i',
    'V29j',
    'V29k',
    'V29l',
    'V107b2',
    'V34',
    'V35',
    'V36',
    'V37',
    'V38',
    'V39',
    'V40',
    'V48',
    'V49',
    'V50',
    'V51',
    'V52',
    'V53',
    'V54',
    'V55',
    'V65',
    'V66',
    'V66b',
    'V66c',
    'V66d',
    'V67',
    'V67b',
    'V67c',
    'V67d',
    'V67e',
    'V67f',
    'V68',
    'V68b',
    'V68c',
    'V69',
    'V70',
    'V71',
    'V74',
    'V75',
    'V76',
    'V77',
    'V78',
    'V79',
    'V80',
    'V92',
    'V93',
    'V94',
    'V95',
    'V96',
    'V97',
    'V98',
    'V99',
    'V100',
    'V101',
    'V102',
    'V103',
    'V104',
    'V105',
    'V106',
    'V107b',
    'V107c',
    'V107d',
    'V107e',
    'V107f',
    'V107',
    'V108',
    'V109',
    'V107g',
    'V107h',
    'V110',
    'V111',
    'V112',
    'V113',
    'V114',
    'V115',
    'V116',
    'V117',
    'V118',
    'V119',
    'V90',
    'V01b',
    'V92b',
    'V94b',
    'V100b',
    'V124',
    'V125',
    'V127',
    'V128',
    'V129',
    'V136',
    'V137',
    'V138',
    'V78b',
    'V139',
    'V140',
    'V141',
    'V142',
    'V143',
    'VZ01',
    'VZ02',
    'VZ03',
    'VZ04',
    'VZ05',
    'VZ06',
    'VZ07',
    'VZ08',
    'VZ09',
    'VZ10',
    'VZ11',
    'VZ12',
    'VZ13',
    'VZ15',
    'VZ16',
    'VZ17',
    'VZ18',
    'VZ19',
    'VZ20',
    'VZ21',
    'VZ22',
    'VZ23',
    'VZ24',
    'VZ25',
    'VZ26',
    'VZ27',
    'VZ28',
    'VZ29',
    'VZ32',
    'VZ33',
    'VZ30',
    'VZ31',
    'V145',
    'V01c',
    'V92c',
    'VT01',
    'VT02',
    'VT03',
    'VT04',
    'VT05',
    'VT06',
    'VT07',
    'VT08',
    'VT09',
    'V148',
    'V149',
    'V150',
    'V151',
    'V152',
    'V153',
    'V154',
    'V155',
    'V156',
    'V157',
    'V158',
    'V162',
    'V163',
    'V164',
    'V165',
    'V166',
    'V167',
    'V168',
    'V169',
    'V170',
    'V171',
    'V172',
    'V173',
    'V174',
    'V175',
    'V176',
    'V177',
    'V178',
    'V179',
    'V180',
    'V181',
    'V182',
    'V183',
    'V184',
    'V185',
    'V186',
    'V187',
    'V190',
    'V191',
    'V192',
    'V193',
    'V194',
    'V195',
    'V196',
    'V197',
    'V198',
    'V199',
    'V200',
    'V201',
    'V202',
    'V203',
    'V204',
    'V205',
    'V206',
    'V207',
    'V208',
    'V209',
    'V210',
    'V211',
    'V212',
    'V213',
    'V214',
    'V215',
    'V216',
    'V217',
    'V218',
    'V219',
    'V220',
    'V221',
    'V222',
    'V223',
]

MUTS = [
    # ---- Barrett -----------------------------------------------------------
    dict(id="V01", file=V, kind="kernel", count=1,
         old="    qhat = (e * mu) >> shift",
         new="    qhat = (e * mu) >> (shift + 1)",
         desc="two-step Barrett kernel: wrong step-1 shift"),
    dict(id="V02", file=V, kind="kernel", count=1,
         old="    return x1 - Q * (x1 >> shift2 if x1 >= 0 else 0), qhat",
         new="    return x1 - Q * (x1 >> shift2 if x1 >= 0 else 0) + 1, qhat",
         desc="two-step Barrett kernel: off-by-one output"),
    dict(id="V02b", file=V, kind="kernel", count=1,
         old="    qhat = (e * mu) >> shift\n    x1 = e - Q * qhat\n",
         new="    qhat = (e * mu) >> shift\n    x1 = e - Q * qhat + 1\n",
         desc="two-step Barrett kernel: step 1 off by one"),
    # ---- z decode / norm ---------------------------------------------------
    dict(id="V03", file=V, kind="kernel", count=1,
         old="    return (Q + GAMMA1 - v) % Q",
         new="    return (Q + GAMMA1 - v + 1) % Q",
         desc="strict z centered map: off by one"),
    dict(id="V04", file=V, kind="kernel", count=1,
         old="    lhs = (v - (BETA + 1)) % (1 << 256)          # EVM sub",
         new="    lhs = (v - BETA) % (1 << 256)          # EVM sub",
         desc="norm kernel: window start off by one (the SOTA bug)"),
    dict(id="V05", file=V, kind="kernel", count=1,
         old="    return not (lhs < 2 * GAMMA1 - 2 * BETA - 1)  # EVM lt (unsigned)",
         new="    return not (lhs < 2 * GAMMA1 - 2 * BETA)  # EVM lt (unsigned)",
         desc="norm kernel: window width off by one"),
    # ---- UseHint -----------------------------------------------------------
    dict(id="V06", file=V, kind="kernel", count=1,
         old="    c = 1 if r0 > GAMMA2 else 0",
         new="    c = 1 if r0 >= GAMMA2 else 0",
         desc="UseHint kernel: decompose threshold off by one"),
    dict(id="V07", file=V, kind="kernel", count=1, equiv=True,
         old="    r1 = s1 * (0 if s1 == 44 else 1)",
         new="    r1 = s1",
         desc="UseHint kernel: drop the s1==44 correction (EQUIVALENT: the "
              "unconditional mod 44 absorbs it; cross-checks Solidity mutant M26)"),
    dict(id="V08", file=V, kind="kernel", count=1,
         old="    q0 = rv // (2 * GAMMA2)",
         new="    q0 = rv // (2 * GAMMA2 + 1)",
         desc="UseHint kernel: wrong divisor"),
    # ---- range checks -------------------------------------------------------
    # ---- offset-binary decode ---------------------------------------------
    # ---- stored-q z convention --------------------------------------------
    # ---- SMT-inline kernel models -----------------------------------------
    # ---- claims about the design ------------------------------------------
    dict(id="V24", file=V, kind="claim", count=1,
         old='("q0_le_44", q0 <= 44)',
         new='("q0_le_44", q0 <= 43)',
         desc="S11 claim: q0 <= 43 (an off-by-one harness bound) must FAIL"),
    dict(id="V25", file=V, kind="claim", count=1,
         old="        return ([e >= 0, e <= 10285325456994078 - 1],",
         new="        return ([e >= 0, e <= 10285325456994078],",
         desc="S13 claim: the failure point is minimal — including it must FAIL"),
    dict(id="V29", file=V, kind="claim", count=1,
         old="MU33 = 1025                  # floor(2^33 / Q), forward+inverse coarse constant",
         new="MU33 = 1026                  # floor(2^33 / Q), forward+inverse coarse constant",
         desc="the coarse Barrett constant itself"),
    dict(id="V29b", file=V, kind="claim", count=1,
         old="SH2 = 23                     # step 2's shift",
         new="SH2 = 24                     # step 2's shift",
         desc="step 2's shift: the reduction stops landing under 2q"),
    dict(id="V29c", file=V, kind="claim", count=1,
         old="MU33 = 1025                  # floor(2^33 / Q), forward+inverse coarse constant",
         new="MU33 = 3000                  # floor(2^33 / Q), forward+inverse coarse constant",
         desc="the coarse constant grown until the LANE-LOCALITY facts fail "
              "(C9e/C9h/C11d/S1/S2/E9: max*MU33 no longer fits 2^64 and qhat "
              "leaves the 31-bit mask field)"),
    dict(id="V29d", file=V, kind="claim", count=1,
         old="SH1 = 33                     # step 1's shift",
         new="SH1 = 34                     # step 1's shift",
         desc="step 1's shift: the 31-bit mask is exactly 64 - SH1 wide, so "
              "moving SH1 falsifies C9h's mask-width conjuncts"),
    dict(id="V29e", file=V, kind="claim", count=1,
         old="    LANE_FIRST_OVERFLOW = -(-(1 << 64) // MU33)",
         new="    LANE_FIRST_OVERFLOW = -(-(1 << 63) // MU33)",
         desc="C11d: the lane-overflow cliff is where the product reaches 2^64, "
              "not 2^63"),
    dict(id="V29f", file=V, kind="claim", count=1,
         old="Q = 8380417                  # ML-DSA modulus",
         new="Q = 8380418                  # ML-DSA modulus",
         desc="the modulus itself: C1b's `q == 2^23 - 2^13 + 1` and "
              "`2^23 - q == 8191` are what make step 2's multiply elidable"),
    dict(id="V29g", file=V, kind="claim", count=1,
         old="    LANE_FIRST_OVERFLOW = -(-(1 << 64) // MU33)",
         new="    LANE_FIRST_OVERFLOW = -(-(1 << 65) // MU33)",
         desc="C11d: the input one below the lane cliff must still FIT the lane "
              "(a cliff placed a bit too high does not)"),
    dict(id="V29h", file=V, kind="claim", count=1,
         old='                         (Q - 1 + ((128 * Q * (Q - 1)) * ((1 << SH1) - MU33 * Q) >> SH1)) >> SH2\n'
             '                         < (1 << 31)),',
         new='                         (Q - 1 + ((128 * Q * (Q - 1)) * ((1 << SH1) - MU33 * Q) >> SH1)) >> SH2\n'
             '                         < (1 << 9)),',
         desc="C9h: step 2's quotient bound (895) is checked against the mask "
              "width, and the conjunct must be present to check it"),
    dict(id="V29i", file=V, kind="claim", count=1,
         old="            if e * MU33 >= (1 << 64): good[\"lane_local\"] = False",
         new="            if e * MU33 >= (1 << 50): good[\"lane_local\"] = False",
         desc="E9a/E9b: the sweep's lane-locality check is against 2^64, and the "
              "FORWARD domain's products (1.08e18) exceed 2^50"),
    dict(id="V29j", file=V, kind="claim", count=1,
         old='                    [("lane_product_lt_2p64", e * MU33 < (1 << 64)),',
         new='                    [("lane_product_lt_2p64", e * MU33 < (1 << 59)),',
         desc="S1/S2: the forward domain's lane product is 1.08e18, above 2^59 -- "
              "so the 2^64 bound is REACHED, not decorative"),
    dict(id="V29k", file=V, kind="claim", count=1,
         old='            ("product_in_barrett_domain", prod <= 15 * Q * (Q - 1)),\n'
             '            ("product_is_lane_local", prod * MU33 < (1 << 64)),',
         new='            ("product_in_barrett_domain", prod <= 15 * Q * (Q - 1)),\n'
             '            ("product_is_lane_local", prod * MU33 < (1 << 59)),',
         desc="S5: the forward butterfly's product is lane-local with 5 bits to "
              "spare, not 10"),
    dict(id="V29l", file=V, kind="claim", count=1,
         old="                     L[k] * MU33 == QH[k] * (1 << SH1) + SS[k],",
         new="                     L[k] * MU33 == QH[k] * (1 << (SH1 + 1)) + SS[k],",
         desc="S7: the Euclidean WITNESS must be the kernel's own quotient -- "
              "`lane{k}_qhat_is_the_shift` is what checks it, and a witness taken "
              "at the wrong shift falsifies it"),
    dict(id="V107b2", file=V, kind="claim", count=1,
         old='            ("inv_QHATM31_is_2p31m1_per_lane", ic["QHATM31"] == _rep((1 << 31) - 1, 4, 64)),',
         new='            ("inv_QHATM31_is_2p31m1_per_lane", ic["QHATM31"] == _rep((1 << 32) - 1, 4, 64)),',
         desc="C16: the INVERSE file's quotient mask is 31 bits per lane too"),
    dict(id="V34", file=V, kind="claim", count=1,
         old="    BUDGET = 136 - 8",
         new="    BUDGET = 48",
         desc="C10: the SampleInBall rejection budget drives P(2nd permutation)"),
    # ---- encoding canonicality --------------------------------------------
    dict(id="V35", file=V, kind="kernel", count=1,
         old='                if strict_inc and idx > first and y[idx - 1] >= y[idx]:',
         new='                if False and idx > first and y[idx - 1] >= y[idx]:',
         desc="E12/E13: the strict-increase check (CVE-2026-24850 shape)"),
    dict(id="V36", file=V, kind="kernel", count=1,
         old='        if pad_gate:\n            for j in range(idx, om):',
         new='        if False:\n            for j in range(idx, om):',
         desc="E12/E13: the trailing-zero padding check"),
    dict(id="V37", file=V, kind="kernel", count=1,
         old='    _pure = lambda clen, ctx, m: b"\\x00" + bytes([clen]) + ctx + m',
         new='    _pure = lambda clen, ctx, m: b"\\x00" + ctx + m',
         desc="E14: the ctx length byte is what makes M' injective"),
    # ---- opcode-sweep kernels ---------------------------------------------
    dict(id="V38", file=O, kind="kernel", count=1,
         old="SW_MDIV = 2886403",
         new="SW_MDIV = 2886404",
         desc="O1: SWAR division constant (intermediate only; see Solidity M28)"),
    dict(id="V39", file=O, kind="kernel", count=1,
         old="SW_GATHERK = 0x0000000000000000000040000000000000100000000000000400000000000001",
         new="SW_GATHERK = 0x0000000000000000000040000000000000100000000000000400000000000002",
         desc="O5: the multiply-gather constant"),
    dict(id="V40", file=O, kind="kernel", count=1,
         old="    Q0 = (((W * SW_MDIV) & M256) >> SW_SHIFT) & SW_REP6",
         new="    Q0 = (((W * SW_MDIV) & M256) >> (SW_SHIFT + 1)) & SW_REP6",
         desc="O6: SWAR UseHint quotient shift"),
]


# ---------------------------------------------------------------------------
# CLAIM MUTATIONS, for every obligation the kernel mutations above leave
# untouched.  A closed-form CALC fact is not a kernel model, so the only
# meaningful mutation is of its own claim: weaken the asserted bound and
# confirm the obligation notices.  An obligation that survives the
# weakening of its own claim is not checking anything.
# ---------------------------------------------------------------------------
MUTS += [
    dict(id="V48", file=V, kind="claim", count=1,
         old='                 lambda x: x < (1 << 28), 17 * Q, "",',
         new='                 lambda x: x < (1 << 20), 17 * Q, "",',
         desc='C9a: forward final lane bound'),
    dict(id="V49", file=V, kind="claim", count=1,
         old='                 lambda x: x < (1 << 50), 15 * Q * (Q - 1), "",',
         new='                 lambda x: x < (1 << 40), 15 * Q * (Q - 1), "",',
         desc='C9b: forward Barrett input bound'),
    dict(id="V50", file=V, kind="claim", count=1,
         old='                 lambda x: x < (1 << 31), 256 * Q, "",',
         new='                 lambda x: x < (1 << 21), 256 * Q, "",',
         desc='C9c: inverse sum lane bound'),
    dict(id="V51", file=V, kind="claim", count=1,
         old='                 lambda x: x < (1 << 53), 128 * Q * (Q - 1), "",',
         new='                 lambda x: x < (1 << 43), 128 * Q * (Q - 1), "",',
         desc='C9d: inverse Barrett input bound'),
    dict(id="V52", file=V, kind="claim", count=1,
         old='                 lambda x: x < (1 << 64), (128 * Q * (Q - 1)) * MU33,',
         new='                 lambda x: x < (1 << 78), (128 * Q * (Q - 1)) * MU33,',
         desc='C9e: spread-lane no-carry margin'),
    dict(id="V53", file=V, kind="claim", count=1,
         old='                 lambda x: x < 10285325456994078, inv_worst,',
         new='                 lambda x: x < 1000, inv_worst,',
         desc='C11b: inverse worst product inside the safe domain'),
    dict(id="V54", file=V, kind="claim", count=1,
         old='                 lambda x: x >= 10285325456994078, 2 * inv_worst,',
         new='                 lambda x: x >= 102853254569940780, 2 * inv_worst,',
         desc='C11c: the one-extra-layer guard'),
    dict(id="V55", file=V, kind="claim", count=1,
         old='("lt_64", exp_bytes < 64)',
         new='("lt_64", exp_bytes < 42)',
         desc='C10b: expected rejection bytes'),
    dict(id="V65", file=V, kind="claim", count=1,
         old='                 lambda w: w == 2420, 32 + (4 * N * 18) // 8 + (OMEGA + L_DIM), "c~ | z | h",',
         new='                 lambda w: w == 2419, 32 + (4 * N * 18) // 8 + (OMEGA + L_DIM), "c~ | z | h",',
         desc='C15c: sigma width'),
]


MUTS += [
    dict(id="V66", file=V, kind="claim", count=1,
         old='("sum_lane_lt_LB_plus_2q", u + V < LB + 2 * Q),',
         new='("sum_lane_lt_LB_plus_2q", u + V < LB + 1 * Q),',
         desc='S5: the forward +2q increment is EXACT (tightening to +q must FAIL)'),
    dict(id="V66b", file=V, kind="claim", count=1,
         old='("diff_lane_lt_LB_plus_2q", u + 2 * Q - V < LB + 2 * Q),',
         new='("diff_lane_lt_LB_plus_2q", u + 2 * Q - V < LB + 1 * Q),',
         desc='S5: the +2q increment binds on the DIFFERENCE lane too'),
    dict(id="V66c", file=V, kind="claim", count=1,
         old='("product_in_barrett_domain", prod <= 15 * Q * (Q - 1)),',
         new='("product_in_barrett_domain", prod <= 14 * Q * (Q - 1)),',
         desc='S5: 15q(q-1) is the exact forward Barrett domain (C9b)'),
    dict(id="V66d", file=V, kind="claim", count=1,
         old='        prem = [LB >= Q, LB <= 15 * Q,        # lane bound entering this layer',
         new='        prem = [LB >= Q, LB <= 17 * Q,        # lane bound entering this layer',
         desc='S5: the LB <= 15q premise is what keeps the product in the domain'),
    dict(id="V67", file=V, kind="claim", count=1,
         old='("product_in_verified_domain", prod <= 128 * Q * (Q - 1)),',
         new='("product_in_verified_domain", prod <= 64 * Q * (Q - 1)),',
         desc='S6: 128q(q-1) is the EXACT inverse Barrett domain (C9d/S2/S4/E9b)'),
    dict(id="V67b", file=V, kind="claim", count=1,
         old='        prem = [Or(*[K == (1 << i) for i in range(7)]),   # K = 2^(L-1), L = 1..7',
         new='        prem = [Or(*[K == (1 << i) for i in range(8)]),   # K = 2^(L-1), L = 1..7',
         desc='S6: layer 8 (K=128) is NOT a Barrett layer -- admitting it must FAIL'),
    dict(id="V67c", file=V, kind="claim", count=1,
         old='("barrett_r_lt_2q", r < 2 * Q),',
         new='("barrett_r_lt_2q", r < 1 * Q),',
         desc='S6: the inverse Barrett postcondition is r < 2q, not r < q'),
    dict(id="V67d", file=V, kind="claim", count=1,
         old='("sum_lane_lt_2Kq", U + V < 2 * K * Q),',
         new='("sum_lane_lt_2Kq", U + V < 1 * K * Q),',
         desc='S6: the sum lane DOUBLES (2Kq is exact)'),
    dict(id="V67e", file=V, kind="claim", count=1,
         old='            ("sum_lane_product_fits_64", (sAB + sCD) * Sc < (1 << 64)),',
         new='            ("sum_lane_product_fits_64", (sAB + sCD) * Sc < (1 << 53)),',
         desc='S6b: the layer-8 lane budget is 64 bits and is nearly full'),
    dict(id="V67f", file=V, kind="claim", count=1,
         old='        prem = [sAB >= 0, sAB < 128 * Q, sCD >= 0, sCD < 128 * Q,   # L7 sum lanes',
         new='        prem = [sAB >= 0, sAB < (1 << 20) * Q, sCD >= 0, sCD < (1 << 20) * Q,  # L7 sum lanes',
         desc='S6b: layer-8 inputs are < 128q; one more doubling overflows the lane'),
    dict(id="V68", file=V, kind="claim", count=1,
         old='                (f"lane{k}_product_no_carry", L[k] * MU33 < (1 << 64)),',
         new='                (f"lane{k}_product_no_carry", L[k] * MU33 < (1 << 62)),',
         desc='S7: LANE-LOCALITY is a REACHED bound -- the worst lane product is 9.21e18, so 2^62 is false and 2^64 is not'),
    dict(id="V68b", file=V, kind="kernel", count=1,
         old='        w = sum(L[k] * (1 << (64 * k)) for k in range(4))',
         new='        w = sum(L[k] * (1 << (56 * k)) for k in range(4))',
         desc='S7: narrowing the lane spacing to 56 bits DOES make the lanes interfere'),
    dict(id="V68c", file=V, kind="kernel", count=1,
         old='                     _above(k, y1t) % (1 << 31) == QH[k]),',
         new='                     _above(k, y1t) % (1 << 29) == QH[k]),',
         desc="S7: the QHATM field must be wide enough for qhat (max 1072693247 = 2^29.999; "
              "31- and 30-bit masks are EQUIVALENT here -- the field has 2 bits of slack)"),
    dict(id="V69", file=V, kind="kernel", count=1,
         old='        wrapped = If(v >= BETA + 1, v - (BETA + 1), v - (BETA + 1) + (1 << 256))',
         new='        wrapped = If(v >= BETA, v - BETA, v - BETA + (1 << 256))',
         desc='S8: the inline EVM-wrap norm model (window start)'),
    dict(id="V70", file=V, kind="kernel", count=1,
         old='        flag = Not(wrapped < 2 * GAMMA1 - 2 * BETA - 1)          # kernel: reject?',
         new='        flag = Not(wrapped < 2 * GAMMA1 - 2 * BETA)          # kernel: reject?',
         desc='S8: the inline EVM-wrap norm model (window width)'),
    dict(id="V71", file=V, kind="claim", count=1,
         old='        return ([rv >= 0, rv < Q, rv / (2 * GAMMA2) == 44],',
         new='        return ([rv >= 0, rv < Q, rv / (2 * GAMMA2) == 43],',
         desc='S11b: q0 == 44 is reachable ONLY at rv = q-1'),
    dict(id="V74", file=V, kind="kernel", count=1,
         old='        flat = [v for row in hs for v in sorted(row)]',
         new='        flat = [v for row in hs for v in sorted(row, reverse=True)]',
         desc='E13: the canonical encoder emits INCREASING indices'),
    dict(id="V75", file=O, kind="claim", count=1,
         old='    ok1 = fits_lane(maxprod)',
         new='    ok1 = maxprod < (1 << 40)',
         desc='O2: the SWAR lane budget'),
    dict(id="V76", file=O, kind="kernel", count=1,
         old='        bit32 = (v / (1 << 32)) % 2',
         new='        bit32 = (v / (1 << 31)) % 2',
         desc="O3: the add/shift comparator's bit position"),
    dict(id="V77", file=O, kind="kernel", count=1,
         old='    sol = _solver(prem, Not(magic == s % 44))',
         new='    sol = _solver(prem, Not(magic + 1 == s % 44))',
         desc='O4: the ONE magic-division reduction == mod 44 (the kernel folds '
              'FIPS 204\'s two reductions into one and evaluates it by magic division, '
              'not by a conditional subtract)'),
    dict(id="V78", file=O, kind="claim", count=1,
         old='    parts.append(("top_lane_fits_word", fits_word((PK_AMAX - 1) * ZMAX * (1 << 192))))',
         new='    parts.append(("top_lane_fits_word", (Q - 1) * (Q - 1) * (1 << 192) < (1 << 237)))',
         desc='O7: the top-lane product bound'),
    dict(id="V79", file=O, kind="claim", count=1,
         old='    ok_bound = lane_fits_53(lane_max)',
         new='    ok_bound = lane_max < (1 << 40)',
         desc='O8: the matvecRow lazy-accumulator lane bound'),
    dict(id="V80", file=O, kind="kernel", count=1,
         old='    canon = all(is_canonical((8511489 - v) % Q) for v in range(1 << 18))',
         new='    canon = all(is_canonical((8511489 - v) % (Q + 1)) for v in range(1 << 18))',
         desc="O9: unpackZPacked's canonical lane map"),
]

# ---------------------------------------------------------------------------
# PER-CONJUNCT EXTENSION: one mutation for each CONJUNCT the mutations above
# cannot reach.  A per-obligation criterion would let an obligation with four
# claims get by on one mutation; the criterion is per conjunct, so each claim
# needs its own.  Everything below is either a `kernel` mutation of an inline
# model or a `claim` mutation that TIGHTENS the conjunct by one step -- if the
# conjunct is at its true boundary, tightening it must make the suite FAIL.
# ---------------------------------------------------------------------------
MUTS += [
    # ---- S1/S2 (inline Barrett model) --------------------------------------
    dict(id="V92", file=V, kind="kernel", count=1,
         old="            qhat = (e * MU33) / (1 << SH1)         # z3 Int division = floor for e >= 0",
         new="            qhat = (e * MU33) / (1 << 30)         # z3 Int division = floor for e >= 0",
         desc="S1/S2 inline Barrett: quotient 8x too large (r < 0, r >= 2q, qhat >= 2^32)"),
    # ---- S3/S4 (congruence) -------------------------------------------------
    dict(id="V93", file=V, kind="kernel", count=1,
         old="            r = x1 - Q * (x1 / (1 << SH2))\n            # r = e - Q*(qhat + b) is congruent by construction",
         new="            r = x1 - Q * (x1 / (1 << SH2)) + 1\n            # r = e - Q*(qhat + b) is congruent by construction",
         desc="S3/S4: the reduced value must stay congruent to e mod q"),
    # ---- S5 (inline Barrett inside the butterfly) ---------------------------
    dict(id="V94", file=V, kind="kernel", count=1,
         old="        V1 = prod - Q * ((prod * MU33) / (1 << SH1))",
         new="        V1 = prod - Q * ((prod * MU33) / (1 << 30))",
         desc="S5: the butterfly's Barrett quotient 8x too large"),
    # ---- S6 (the offset that keeps the difference lane non-negative) --------
    dict(id="V95", file=V, kind="claim", count=1,
         old="        diff = U + K * Q - V                     # Yul: sub(add(u, Q4_K), v)",
         new="        diff = U - V                             # Yul: sub(add(u, Q4_K), v)",
         desc="S6: dropping the +Kq offset DOES make the difference lane negative"),
    dict(id="V96", file=V, kind="claim", count=1,
         old="        diff = U + K * Q - V                     # Yul: sub(add(u, Q4_K), v)",
         new="        diff = U + 3 * K * Q - V                 # Yul: sub(add(u, Q4_K), v)",
         desc="S6: the offset is exactly Kq (3Kq breaks the 2Kq lane bound)"),
    # ---- S6b (layer 8: the difference lanes) --------------------------------
    dict(id="V97", file=V, kind="claim", count=1,
         old="                dAB >= 0, dAB < 2 * Q, dCD >= 0, dCD < 2 * Q,       # L7 Barrett outputs",
         new="                dAB >= 0, dAB < (1 << 20) * Q, dCD >= 0, dCD < (1 << 20) * Q,  # L7 Barrett outputs",
         desc="S6b: layer 7 MUST reduce to < 2q or layer 8's lanes overflow"),
    # ---- S7 (the 256-bit product budget) ------------------------------------
    dict(id="V98", file=V, kind="claim", count=1,
         old="        emax = 128 * Q * (Q - 1)",
         new="        emax = 128 * Q * (Q - 1) * (1 << 130)",
         desc="S7: the spread word's Barrett product does not fit 2^256 for larger lanes"),
    # ---- S11 (the inline decompose model) -----------------------------------
    dict(id="V99", file=V, kind="kernel", count=1,
         old="        q0 = rv / (2 * GAMMA2)\n        r0 = rv - q0 * (2 * GAMMA2)",
         new="        q0 = (rv - Q) / (2 * GAMMA2)\n        r0 = rv - q0 * (2 * GAMMA2)",
         desc="S11: a negative quotient / out-of-range remainder must be caught"),
    dict(id="V100", file=V, kind="kernel", count=1,
         old="        q0 = rv / (2 * GAMMA2)\n        r0 = rv - q0 * (2 * GAMMA2)",
         new="        q0 = rv / (2 * GAMMA2)\n        r0 = rv - q0 * GAMMA2",
         desc="S11: the remainder is rv - q0*2*gamma2, not rv - q0*gamma2"),
    # ---- C9f: the forward induction ----------------------------------------
    dict(id="V101", file=V, kind="claim", count=1,
         old='                 fwd_induction_closes, (Q, 2 * Q, 8),',
         new='                 fwd_induction_closes, (Q, 4 * Q, 8),',
         desc="C9f: a +4q/layer schedule breaks the induction"),
    dict(id="V102", file=V, kind="claim", count=1,
         old='    fwd_lb, fwd_barrett_in = fwd_schedule(Q, 2 * Q, 8)',
         new='    fwd_lb, fwd_barrett_in = fwd_schedule(3 * Q, 2 * Q, 8)',
         desc="C9f: the transform must be entered with CANONICAL lanes (< q)"),
    # ---- C9g: the inverse induction ----------------------------------------
    dict(id="V103", file=V, kind="claim", count=1,
         old='                 inv_induction_closes, (ACC_ENTRY, inv_exit_bound, 7, 256 * Q, 2 * 128 * Q),',
         new='                 inv_induction_closes, (ACC_ENTRY, inv_exit_bound, 8, 256 * Q, 2 * 128 * Q),',
         desc="C9g: including layer 8 as a Barrett layer leaves the verified domain"),
    dict(id="V104", file=V, kind="claim", count=1,
         old="    inv_sum_lane = 256 * Q                          # after the L8 sums, before mod",
         new="    inv_sum_lane = 512 * Q                          # after the L8 sums, before mod",
         desc="C9g: the maximum inverse sum lane is 256q (C9c)"),
    dict(id="V105", file=V, kind="claim", count=1,
         old="    l8_operand = 2 * 128 * Q                        # sAB + 128q - sCD < 256q",
         new="    l8_operand = 2 * 128 * Q * (1 << 12)            # sAB + 128q - sCD < 256q",
         desc="C9g: layer 8's lane products fit 64 bits only at this operand size"),
    # ---- C16: the shipped-Yul cross-check ----------------------------------
    dict(id="V106", file=V, kind="claim", count=1,
         old='            ("fwd_MU33", fc["MU33"] == (1 << 33) // Q),',
         new='            ("fwd_MU33", fc["MU33"] == (1 << 32) // Q),',
         desc="C16: the forward file's Barrett constant"),
    dict(id="V107b", file=V, kind="claim", count=1,
         old='            ("fwd_QHATM31_is_2p31m1_per_lane", fc["QHATM31"] == _rep((1 << 31) - 1, 4, 64)),',
         new='            ("fwd_QHATM31_is_2p31m1_per_lane", fc["QHATM31"] == _rep((1 << 32) - 1, 4, 64)),',
         desc="C16: the shipped quotient mask is 31 bits per lane, not 32 -- the "
              "extra bit is the neighbour lane's"),
    # C16's constant check is not a name allowlist ("no constant called SPREAD,
    # QHATM or MU52") but a CLOSED, derived equality: each shipped transform's
    # file-scope constant block must be EXACTLY the map computed from q.  This
    # mutation tests that the conjunct can SEE which constants are actually
    # declared, by adding a PHANTOM expected constant (the spread Barrett's
    # MU52, which nothing ships) to the derived table.  Neither shipped copy
    # declares it, so BOTH the fwd and the inv equality must go false; one
    # mutation, two conjuncts.  A conjunct rewritten to ignore extra or missing
    # declarations would survive it, which is what makes it worth running.
    dict(id="V107c", file=V, kind="claim", count=1,
         old='        "TWOQ": 2 * Q,',
         new='        "TWOQ": 2 * Q, "MU52": (1 << 52) // Q,',
         desc="C16: the derived constant block is CLOSED -- an expected constant "
              "that no shipped copy declares must falsify both equalities (the "
              "conjunct must be able to SEE which constants are there)"),
    dict(id="V107d", file=V, kind="claim", count=1,
         old='                    and sum(fwd_shape["barrett_per_block"]) == 24))',
         new='                    and sum(fwd_shape["barrett_per_block"]) == 23))',
         desc="C16: the forward transform has exactly 24 reduction sites, both "
              "steps each"),
    dict(id="V107e", file=V, kind="claim", count=1,
         old='                    and sum(inv_shape["barrett_per_block"]) == 10))',
         new='                    and sum(inv_shape["barrett_per_block"]) == 9))',
         desc="C16: the inverse transform has exactly 10 reduction sites, both "
              "steps each"),
    dict(id="V107f", file=V, kind="claim", count=1,
         old='                    and sh["red2_per_block"] == sh["barrett_per_block"]\n'
             '                    and sh["mod_per_block"] == [0, 0, 0]',
         new='                    and sh["mod_per_block"] == [0, 0, 0]',
         desc="C16: _fwd_shape_ok must REJECT a forward transform one of whose "
              "reductions lost its second step (ctl_fwd_one_second_step_dropped)"),
    dict(id="V107", file=V, kind="claim", count=1,
         old='            ("inv_MU33", ic["MU33"] == (1 << 33) // Q),',
         new='            ("inv_MU33", ic["MU33"] == (1 << 32) // Q),',
         desc="C16: the inverse file's Barrett constant"),
    dict(id="V108", file=V, kind="claim", count=1,
         old='            ("fwd_TWOQ4_is_2q_per_lane", fc["TWOQ4"] == _rep(2 * Q, 4, 64)),',
         new='            ("fwd_TWOQ4_is_2q_per_lane", fc["TWOQ4"] == _rep(3 * Q, 4, 64)),',
         desc="C16: the forward butterfly's +2q offset constant"),
    dict(id="V109", file=V, kind="claim", count=1,
         old='            ("fwd_TWOQ_is_2q", fc["TWOQ"] == 2 * Q),',
         new='            ("fwd_TWOQ_is_2q", fc["TWOQ"] == 3 * Q),',
         desc="C16: the forward L7/L8 scalar 2q offset"),
    dict(id="V107g", file=V, kind="claim", count=1,
         old='        return r["mstore"] > 0 and 2 * sum(c for _o, c in r["K"]) == layers * r["mstore"]',
         new='        return r["mstore"] > 0 and 2 * sum(c for _o, c in r["K"]) <= layers * r["mstore"]',
         desc="C16: the offsets-per-butterfly ratio is an EQUALITY -- relaxed to <=, a "
              "block that has DROPPED one butterfly's offset passes "
              "(ctl_fwd_one_offset_dropped_in_a_block stops rejecting)"),
    dict(id="V107h", file=V, kind="claim", count=1,
         old='                    and sh["barrett_per_block"] == [12, 12, 0]',
         new='                    and sh["barrett_per_block"] == [12, 12, 12]',
         desc="C16: the forward per-block reduction census is load-bearing (the two "
              "radix-8 blocks carry twelve reductions each and the in-word tail none, "
              "because its four products per word go through mulmod)"),
    dict(id="V110", file=V, kind="claim", count=1,
         old='             fwd_shape["sum_stores"] == fwd_shape["diff_stores"] > 0),',
         new='             fwd_shape["sum_stores"] == fwd_shape["barrett_per_block"][0] > 0),',
         desc="C16: every forward sum store is paired with a +2q difference store"),
    dict(id="V111", file=V, kind="claim", count=1,
         old='            ("inv_ACCQ30_is_q_shl_30", ic["ACCQ30"] == Q << 30),',
         new='            ("inv_ACCQ30_is_q_shl_30", ic["ACCQ30"] == Q << 29),',
         desc="C16: the entry-fold L1 offset is exactly q*2^30 (a multiple of q "
              "that dominates one raw accumulator lane)"),
    dict(id="V112", file=V, kind="claim", count=1,
         old='            ("inv_TWOQ_is_2q", ic["TWOQ"] == 2 * Q),',
         new='            ("inv_TWOQ_is_2q", ic["TWOQ"] == 4 * Q),',
         desc="C16: the inverse L2 scalar 2q offset"),
    dict(id="V113", file=V, kind="claim", count=1,
         old='            ("inv_TWOQ4_is_2q_per_lane", ic["TWOQ4"] == _rep(2 * Q, 4, 64)),',
         new='            ("inv_TWOQ4_is_2q_per_lane", ic["TWOQ4"] == _rep(4 * Q, 4, 64)),',
         desc="C16: the inverse L8 difference offset constant"),
    dict(id="V114", file=V, kind="claim", count=1,
         old='            c16.append((f"inv_Q4_{K}_is_{K}q_per_lane", ic[f"Q4_{K}"] == _rep(K * Q, 4, 64)))',
         new='            c16.append((f"inv_Q4_{K}_is_{K}q_per_lane", ic[f"Q4_{K}"] == _rep(K * Q + 1, 4, 64)))',
         desc="C16: every per-layer offset constant Q4_K is exactly K*q per lane"),
    dict(id="V115", file=V, kind="claim", count=1,
         old='        c16.append(("inv_layer8_canonicalises_with_mod", inv_shape["mod_per_block"][-1] == 16))',
         new='        c16.append(("inv_layer8_canonicalises_with_mod", inv_shape["mod_per_block"][-1] == 15))',
         desc="C16: layer 8 canonicalises all 4x4 lanes with mod"),
    dict(id="V116", file=V, kind="claim", count=1,
         old='                    sum(inv_shape["mod_per_block"][:-1]) == 0\n                    and inv_shape["mod_total"] == inv_shape["mod_per_block"][-1]))',
         new='                    sum(inv_shape["mod_per_block"][:-1]) == 0\n                    and inv_shape["mod_total"] == inv_shape["mod_per_block"][-1] + 1))',
         desc="C16: no OTHER inverse layer uses a modular reduction"),
    dict(id="V117", file=V, kind="claim", count=1,
         old='    C16_FWD = ["test/ZZZ_NttVariants.sol",',
         new='    C16_FWD = ["test/DOES_NOT_EXIST.sol",',
         desc="C16: an unreadable source FAILS (it is never a silent skip)"),
    # ---- E14: the two message-representative domains ------------------------
    dict(id="V118", file=V, kind="kernel", count=1,
         old='    _prehash = lambda clen, ctx, m: b"\\x01" + bytes([clen]) + ctx + OID + m',
         new='    _prehash = lambda clen, ctx, m: b"\\x00" + bytes([clen]) + ctx + m',
         desc="E14: reusing the pure domain byte for HashML-DSA DOES collide"),
    dict(id="V119", file=V, kind="kernel", count=1,
         old='        for clen in range(0, 4):\n            for cbits in range(2 ** clen):',
         new='        for clen in range(0, 0):\n            for cbits in range(2 ** clen):',
         desc="E14: an empty representative set makes the injectivity claim vacuous"),
    # ---- the classical-vacuity guard itself ---------------------------------
    # These two demonstrate that `<oid>.premises_sat` bites; that is why every
    # other `premises_sat` conjunct is listed in CONJUNCT_EXEMPT.
    dict(id="V90", file=V, kind="claim", count=1,
         old="        return ([v >= 0, v < (1 << 18)], [(\"kernel_iff_fips\", flag == fips_reject)])",
         new="        return ([v >= 0, v < (1 << 18), v > (1 << 18)], [(\"kernel_iff_fips\", flag == fips_reject)])",
         desc="S8: contradictory premises make the proof free -> premises_sat must FAIL"),
]

# ---------------------------------------------------------------------------
# SECOND PER-CONJUNCT PASS.  A per-conjunct run over the catalogue above leaves
# 40 conjuncts that no mutation can break; each mutation below closes exactly
# one of them.  A conjunct with no killer is not evidence, so the alternative
# was to delete those conjuncts -- but every one of them is a real property of
# the emitted code, so they are kept and the catalogue is extended instead.
# ---------------------------------------------------------------------------
MUTS += [
    # ---- S14: the modular-complement offset removal ------------------------
    # ---- Barrett: the quotient can be too SMALL as well as too large -------
    dict(id="V01b", file=V, kind="kernel", count=1,
         old="    qhat = (e * mu) >> shift",
         new="    qhat = (e * mu) >> (shift - 4)",
         desc="Barrett kernel: quotient 16x too large (qhat leaves 2^32, r goes negative)"),
    dict(id="V92b", file=V, kind="kernel", count=1,
         old="            qhat = (e * MU33) / (1 << SH1)         # z3 Int division = floor for e >= 0",
         new="            qhat = (e * MU33) / (1 << 36)         # z3 Int division = floor for e >= 0",
         desc="S1/S2 inline Barrett: quotient 8x too small (r >= 2q)"),
    dict(id="V94b", file=V, kind="kernel", count=1,
         old="        V = V1 - Q * (V1 / (1 << SH2))",
         new="        V = V1 - Q * (V1 / (1 << 26))",
         desc="S5: an under-reduced V leaves [0,2q) and the difference lane underflows"),
    # ---- S11: the remainder must be non-negative ---------------------------
    dict(id="V100b", file=V, kind="kernel", count=1,
         old="        q0 = rv / (2 * GAMMA2)\n        r0 = rv - q0 * (2 * GAMMA2)",
         new="        q0 = rv / (2 * GAMMA2)\n        r0 = rv - (q0 + 1) * (2 * GAMMA2)",
         desc="S11: an over-subtracted remainder goes negative"),
    # ---- C10 / C10b --------------------------------------------------------
    dict(id="V124", file=V, kind="claim", count=1,
         old="    num = sum(w[n] * pow(256, BUDGET - n) for n in range(BUDGET + 1))",
         new="    num = 2 * sum(w[n] * pow(256, BUDGET - n) for n in range(BUDGET + 1))",
         desc="C10: the DP weights must be a proper sub-distribution (num <= den)"),
    dict(id="V125", file=V, kind="claim", count=1,
         old="    exp_bytes = sum(256 / (i + 1) for i in range(256 - TAU, 256))",
         new="    exp_bytes = sum(256 / (i + 1) for i in range(256 - TAU, 256)) / 4",
         desc="C10b: E[rejection bytes] is at least tau (one accepted byte per draw)"),
    # ---- the Barrett cliff constant ---------------------------------------
    dict(id="V127", file=V, kind="claim", count=1,
         old="    BARRETT_FIRST_FAIL = 10285325456994078",
         new="    BARRETT_FIRST_FAIL = 1000",
         desc="C11a/C11b/C9f/C9g: the Barrett cliff constant itself"),
    # ---- E2: the 6-bit packing depends on the FINAL mod 44 -----------------
    dict(id="V128", file=V, kind="kernel", count=1,
         old="    return (r1 + h * (1 + 42 * (1 if (r0 == 0 or c) else 0))) % 44",
         new="    return (r1 + h * (1 + 42 * (1 if (r0 == 0 or c) else 0))) % 45",
         desc="E2: UseHint's final mod 44 is what keeps the output 6-bit packable"),
    # ---- E5: the accepted side of the norm boundary ------------------------
    dict(id="V129", file=V, kind="kernel", count=1,
         old="    lhs = (v - (BETA + 1)) % (1 << 256)          # EVM sub",
         new="    lhs = (v - (BETA + 2)) % (1 << 256)          # EVM sub",
         desc="E5: |z| = gamma1-beta-1 must be ACCEPTED (over-rejection is a defect too)"),
    # ---- E8: each check, each direction, each end of the wire ---------------
    # ---- O2: the three lane budgets besides the division product -----------
    dict(id="V136", file=O, kind="claim", count=1,
         old='    ok2 = fits_lane(63 * D2G)',
         new='    ok2 = 63 * D2G < (1 << 20)',
         desc="O2: the masked quotient times 2*gamma2 stays in its lane"),
    dict(id="V137", file=O, kind="claim", count=1,
         old='    ok3 = (fits_lane((D2G - 1) + (1 << 32))',
         new='    ok3 = (((D2G - 1) + (1 << 32) < (1 << 32))',
         desc="O2: the add/shift comparator addends stay in their lane"),
    dict(id="V138", file=O, kind="claim", count=1,
         old='    ok4 = fits_word(M64 << 192)',
         new='    ok4 = (M64 << 192) < (1 << 200)',
         desc="O2: the top lane's hint mask stays inside the 256-bit word"),
    # ---- O7: the lane products must not spill --------------------------------
    dict(id="V78b", file=O, kind="claim", count=1,
         old="    prem = [a >= 0, a < PK_AMAX, z >= 0, z <= ZMAX]",
         new="    prem = [a >= 0, a < PK_AMAX * (1 << 20), z >= 0, z < Q]",
         desc="O7: canonical inputs are what keep each lane product inside 64 bits"),
    # ---- O8: the three matvec accumulator facts besides the lane bound ------
    dict(id="V139", file=O, kind="claim", count=1,
         old='    ok_nonneg = offset_exceeds((KQ28, prod))',
         new='    ok_nonneg = offset_exceeds((KQ28, prod * (1 << 20)))',
         desc="O8: the K*q offset is what prevents a borrow between lanes"),
    dict(id="V140", file=O, kind="claim", count=1,
         old='    ok_mod = is_multiple_of_q(KQ28)',
         new='    ok_mod = is_multiple_of_q(KQ28 + 1)',
         desc="O8: the offset must be a multiple of q (residue class preserved)"),
    dict(id="V141", file=O, kind="claim", count=1,
         old='    ok_rep = rep_is_four_lanes(MV_KQ28REP)',
         new='    ok_rep = MV_KQ28REP == sum(KQ28 << (64 * k) for k in range(3))',
         desc="O8: the replicated offset constant covers all FOUR lanes"),
    # ---- O9 ----------------------------------------------------------------
    dict(id="V142", file=O, kind="claim", count=1,
         old='        return x < (1 << 23)',
         new='        return x < (1 << 22)',
         desc="O9: a canonical coefficient is 23 bits, which is what makes 4/word fit"),
    dict(id="V143", file=O, kind="kernel", count=1,
         old='            w |= combo[k] << (stride * k)',
         new='            w |= combo[k] << (60 * k)',
         desc="O9: the packing stride is 64 bits; a narrower stride overlaps"),
    # =======================================================================
    # THE SHIPPED PACKED z DECODER (S8b, E3b, E4b, E5b, O10).
    # The kernel does not evaluate a predicate per coefficient, so what has to
    # be load-bearing is FOUR-LANE arithmetic: every mutation below breaks one
    # named ingredient of it -- an offset, a window edge, a lane spacing, a
    # carry budget, a witness -- and each must falsify at least one conjunct.
    # Every one of these BREAKS its target (leaves it false); a mutation that
    # merely relaxed a bound would leave the conjunct true and prove nothing,
    # which is the easiest way for a catalogue entry to be worthless.
    # =======================================================================
    # ---- S8b: the centered offset, the canonicalisation flag, the two edges --
    dict(id="VZ01", file=V, kind="kernel", count=1,
         old="        UOFF = Q + GAMMA1                          # Z_UOFF, per lane",
         new="        UOFF = Q + GAMMA1 + 1                      # Z_UOFF, per lane",
         desc="S8b: Z_UOFF is q + gamma1 exactly (the centered map and the verdict "
              "both move if it is off by one)"),
    dict(id="VZ02", file=V, kind="kernel", count=1,
         old="        QB32 = (1 << 32) - Q                       # Z_QB32, per lane",
         new="        QB32 = (1 << 32) - Q - 1                   # Z_QB32, per lane",
         desc="S8b: the canonicalisation flag is [u >= q]; taken strictly, the z = 0 "
              "field stores q (the ZKNox defect) and the lane stops being canonical"),
    dict(id="VZ03", file=V, kind="kernel", count=1,
         old="        NLO = (1 << 32) - (GAMMA1 - BETA)          # Z_NLO, per lane",
         new="        NLO = (1 << 32) - (GAMMA1 - BETA) + 1      # Z_NLO, per lane",
         desc="S8b: the LOW window edge (bit 32 of o + Z_NLO)"),
    dict(id="VZ04", file=V, kind="kernel", count=1,
         old="        NHI = (1 << 32) + Q - (GAMMA1 - BETA)      # Z_NHI, per lane",
         new="        NHI = (1 << 32) + Q - (GAMMA1 - BETA) - 1  # Z_NHI, per lane",
         desc="S8b: the HIGH window edge (bit 32 of Z_NHI - o)"),
    # ---- S8b: the three carry/borrow budgets --------------------------------
    dict(id="VZ05", file=V, kind="kernel", count=1,
         old="        T = [U[k] + QB32 for k in range(4)]",
         new="        T = [U[k] + QB32 * 4 for k in range(4)]",
         desc="S8b: the flag word must stay under 2^33, or its carry leaves bit 32"),
    dict(id="VZ06", file=V, kind="kernel", count=1,
         old="        X = [O[k] + NLO for k in range(4)]",
         new="        X = [O[k] + NLO * 2 for k in range(4)]",
         desc="S8b: the low-edge word must stay under 2^33"),
    dict(id="VZ07", file=V, kind="kernel", count=1,
         old="        Y = [NHI - O[k] for k in range(4)]",
         new="        Y = [NHI - O[k] * 1024 for k in range(4)]",
         desc="S8b: the high-edge word is a SUBTRACTION and must not borrow"),
    dict(id="VZ08", file=V, kind="kernel", count=1,
         old="                     RF[k] >= 0, RF[k] < (1 << 32), T[k] == F[k] * (1 << 32) + RF[k],",
         new="                     RF[k] >= 0, RF[k] < (1 << 33), T[k] == F[k] * (1 << 32) + RF[k],",
         desc="S8b: the Euclidean witness pins the flag ONLY if its remainder is "
              "below the divisor"),
    # ---- S8b: the four lane spacings ---------------------------------------
    dict(id="VZ09", file=V, kind="kernel", count=1,
         old="        tt = [(T[j], 64 * j) for j in range(4)]",
         new="        tt = [(T[j], 56 * j) for j in range(4)]",
         desc="S8b: the flag word's lanes are 64 bits apart"),
    dict(id="VZ10", file=V, kind="kernel", count=1,
         old="        ot = [(O[j], 64 * j) for j in range(4)]",
         new="        ot = [(O[j], 56 * j) for j in range(4)]",
         desc="S8b: the STORED word's lanes are 64 bits apart"),
    dict(id="VZ11", file=V, kind="kernel", count=1,
         old="        xt = [(X[j], 64 * j) for j in range(4)]",
         new="        xt = [(X[j], 56 * j) for j in range(4)]",
         desc="S8b: the low-edge word's lanes are 64 bits apart"),
    dict(id="VZ12", file=V, kind="kernel", count=1,
         old="        yt = [(Y[j], 64 * j) for j in range(4)]",
         new="        yt = [(Y[j], 56 * j) for j in range(4)]",
         desc="S8b: the high-edge word's lanes are 64 bits apart"),
    # ---- S8b: the SPEC side of the equivalence ------------------------------
    dict(id="VZ13", file=V, kind="kernel", count=1,
         old="            fips_reject = Or(GAMMA1 - V[k] >= GAMMA1 - BETA,",
         new="            fips_reject = Or(GAMMA1 - V[k] > GAMMA1 - BETA,",
         desc="S8b: FIPS 204 rejects the boundary ||z|| == gamma1-beta (the bound is "
              "STRICT); transcribing it loosely must break the equivalence"),
    # ---- S8b: the four claims no kernel mutation reaches -------------------
    dict(id="VZ15", file=V, kind="claim", count=1,
         old='                (f"lane{k}_u_no_borrow", U[k] > 0),',
         new='                (f"lane{k}_u_no_borrow", U[k] > 8249346),',
         desc="S8b: u bottoms out at exactly 8249346 (v = 2^18 - 1)"),
    dict(id="VZ16", file=V, kind="claim", count=1,
         old='                (f"lane{k}_u_lt_2q", U[k] < 2 * Q),',
         new='                (f"lane{k}_u_lt_2q", U[k] < Q),',
         desc="S8b: u reaches q + gamma1 > q, which is WHY a conditional subtract is needed"),
    dict(id="VZ17", file=V, kind="claim", count=1,
         old='                (f"lane{k}_correction_is_lane_local", Q * F[k] < (1 << 64)),',
         new='                (f"lane{k}_correction_is_lane_local", Q * F[k] < Q),',
         desc="S8b: the correction q*flag is a real q when the flag is set"),
    dict(id="VZ18", file=V, kind="claim", count=1,
         old='                (f"lane{k}_o_no_borrow", O[k] >= 0),',
         new='                (f"lane{k}_o_no_borrow", O[k] > 0),',
         desc="S8b: o REACHES 0 (the z = 0 field), so the bound is >= and not >"),
    dict(id="VZ19", file=V, kind="claim", count=1,
         old='                (f"lane{k}_high_edge_no_carry", Y[k] < (1 << 33)),',
         new='                (f"lane{k}_high_edge_no_carry", Y[k] < (1 << 32)),',
         desc="S8b: the high-edge word DOES reach past 2^32 -- that is its flag bit"),
    # ---- E3b/E4b/E5b: the one-lane projection the sweeps quantify over ------
    dict(id="VZ20", file=V, kind="kernel", count=1,
         old="    return u - Q * (((u + Z_QB32_LANE) >> 32) & 1)",
         new="    return u - Q * (((u + Z_QB32_LANE) >> 31) & 1)",
         desc="E3b: the canonicalisation flag is bit 32 of the biased lane"),
    dict(id="VZ21", file=V, kind="kernel", count=1,
         old="Z_QB32_LANE = (1 << 32) - Q                    # 4286586879",
         new="Z_QB32_LANE = (1 << 32) - Q - 1                # 4286586879",
         desc="E3b: [u >= q], not [u > q] -- the z = 0 field must canonicalise to 0"),
    dict(id="VZ22", file=V, kind="kernel", count=1,
         old="Z_NLO_LANE = (1 << 32) - (GAMMA1 - BETA)       # 2^32 - 130994",
         new="Z_NLO_LANE = (1 << 32) - (GAMMA1 - BETA) + 1   # 2^32 - 130994",
         desc="E4b/E5b: the low tail of the STRICT bound (the published off-by-one)"),
    dict(id="VZ23", file=V, kind="kernel", count=1,
         old="Z_NLO_LANE = (1 << 32) - (GAMMA1 - BETA)       # 2^32 - 130994",
         new="Z_NLO_LANE = (1 << 32) - (GAMMA1 - BETA) - 1   # 2^32 - 130994",
         desc="E5b: ... and over-rejection on the low tail is a defect too"),
    dict(id="VZ24", file=V, kind="kernel", count=1,
         old="Z_NHI_LANE = (1 << 32) + Q - (GAMMA1 - BETA)   # 2^32 + 8249423",
         new="Z_NHI_LANE = (1 << 32) + Q - (GAMMA1 - BETA) - 1  # 2^32 + 8249423",
         desc="E4b/E5b: the HIGH tail of the same bound, reached by a different constant"),
    dict(id="VZ25", file=V, kind="kernel", count=1,
         old="Z_NHI_LANE = (1 << 32) + Q - (GAMMA1 - BETA)   # 2^32 + 8249423",
         new="Z_NHI_LANE = (1 << 32) + Q - (GAMMA1 - BETA) + 1  # 2^32 + 8249423",
         desc="E5b: ... and over-rejection on the high tail"),
    dict(id="VZ26", file=V, kind="kernel", count=1,
         old="    return abs(signed) < GAMMA1 - BETA",
         new="    return abs(signed) <= GAMMA1 - BETA",
         desc="E5b: the FIPS reference itself must put the boundary OUTSIDE the "
              "accepted set, or the four boundary claims probe the wrong points"),
    # ---- O10: the extraction (terms, mask, additivity) ----------------------
    dict(id="VZ27", file=O, kind="kernel", count=1,
         old="Z_TERMS = ((0, 0), (1, 8), (2, 16), (2, 62), (3, 70), (4, 78),",
         new="Z_TERMS = ((0, 0), (1, 8), (2, 16), (2, 20), (3, 70), (4, 78),",
         desc="O10: the twelve byte terms must be pairwise DISJOINT (b2's second copy "
              "moved on top of its first)"),
    dict(id="VZ28", file=O, kind="kernel", count=1,
         old="           (4, 124), (5, 132), (6, 140), (6, 186), (7, 194), (8, 202))",
         new="           (4, 124), (5, 132), (6, 140), (6, 186), (7, 194), (8, 250))",
         desc="O10: no term may reach past bit 255"),
    dict(id="VZ29", file=O, kind="kernel", count=1,
         old="Z_M18_DEC = 0x000000000003ffff000000000003ffff000000000003ffff000000000003ffff",
         new="Z_M18_DEC = 0x000000000001ffff000000000003ffff000000000003ffff000000000003ffff",
         desc="O10: the field mask is 18 bits in ALL FOUR lanes (lane 3 narrowed)"),
    # ---- O10: the three FUSED byte placements ------------------------------
    # These two conjuncts are about the DATA (`Z_MUL_PAIRS`), so the mutations
    # that show they are live have to break the data, not the predicate: a
    # constant that is not `2^s + 2^t`, and a pair whose shifts are not the two
    # positions the twelve-term model gives that byte.
    dict(id="VZ32", file=O, kind="kernel", count=1,
         old="Z_MUL_PAIRS = ((2, 16, 62, 0x4000000000010000),",
         new="Z_MUL_PAIRS = ((2, 16, 62, 0x4000000000010001),",
         desc="O10: a fused constant that is not exactly 2^s + 2^t -- the multiply "
              "stops being the OR of the two shifted byte copies"),
    dict(id="VZ33", file=O, kind="kernel", count=1,
         old="               (6, 140, 186, 0x40000000000100000000000000000000000000000000000))",
         new="               (6, 140, 187, 0x40000000000100000000000000000000000000000000000))",
         desc="O10: a fused pair whose SHIFTS are not the two positions Z_TERMS "
              "gives that byte (the constant is then the wrong two powers, and "
              "the pair no longer matches the doubled terms)"),
    dict(id="VZ30", file=O, kind="kernel", count=1,
         old="    v = d & mask",
         new="    v = (d | 1) & mask",
         desc="O10: the shipped extraction is bytewise additive (a constant term "
              "breaks both the additivity and the sweep)"),
    dict(id="VZ31", file=O, kind="kernel", count=1,
         old="        bits |= b[i] << (8 * i)",
         new="        bits += b[i] << (7 * i)",
         desc="O10: the FIPS side is an LSB-first bitstream at BYTE spacing; overlap "
              "makes it non-additive and the coordinate sweep unsound"),

    # ---- META-IDS: the assertion that the suite is still all there ---------
    dict(id="V145", file=V, kind="claim", count=1,
         old='                        ("pure_prehash_disjoint", sep_ok)])',
         new='                        ])',
         desc="META-IDS: deleting a CONJUNCT must fail the suite"),
    # ---- the last three conjuncts no mutation above can break --------------
    # The forward Barrett domain is 15q(q-1), where qhat only reaches
    # 125,706,239 = 2^26.9, so the x8 quotient of V92 is not enough to leave the
    # 2^32 field; x64 is.  (The inverse domain's qhat is 2^29.999, which is why
    # V92 already kills S2's.)
    dict(id="V01c", file=V, kind="kernel", count=1,
         old="    qhat = (e * mu) >> shift",
         new="    qhat = (e * mu) >> (shift - 6)",
         desc="E9a/E9b: qhat must stay inside the 32-bit QHATM field (x64 leaves it)"),
    dict(id="V92c", file=V, kind="kernel", count=1,
         old="            qhat = (e * MU33) / (1 << SH1)         # z3 Int division = floor for e >= 0",
         new="            qhat = (e * MU33) / (1 << 27)         # z3 Int division = floor for e >= 0",
         desc="S1/S2: qhat must stay inside the 32-bit QHATM field (x64 leaves it)"),
]

# ---------------------------------------------------------------------------
# MUTATIONS OF THE SEMANTIC-PINNING MECHANISM ITSELF.
#
# The catalogue above breaks one modelled kernel or one claim at a time.  These
# break the machinery that is supposed to notice, universally -- they are the
# "rewrite the predicate, keep the ID and the description" attack, applied to
# every pinned obligation at once.  Each must kill the whole class of conjunct
# it targets; if it does not, that class of conjunct is decoration.
# ---------------------------------------------------------------------------
MUTS += [
    dict(id="VT01", file=V, kind="claim", count=1,
         old="    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         new="    pred = lambda _x: True\n"
             "    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         desc="EVERY discrimination predicate rewritten to a TAUTOLOGY -- must "
              "falsify every ctl_rejects_* conjunct in verify_all.py"),
    dict(id="VT02", file=V, kind="claim", count=1,
         old="    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         new="    pred = lambda _x: False\n"
             "    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         desc="EVERY discrimination predicate rewritten to a CONTRADICTION -- "
              "must falsify every ctl_accepts_* conjunct in verify_all.py"),
    dict(id="VT03", file=O, kind="claim", count=1,
         old="    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         new="    pred = lambda _x: True\n"
             "    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         desc="the same tautology rewrite in kernel_obligations.py -- must falsify "
              "every O*.ctl_*_rejects_* conjunct"),
    dict(id="VT04", file=O, kind="claim", count=1,
         old="    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         new="    pred = lambda _x: False\n"
             "    rows = []\n    for i, x in enumerate(accept):\n"
             '        rows.append((f"{label}_accepts_{i}", _truth(pred(x))))',
         desc="the same contradiction rewrite in kernel_obligations.py -- must "
              "falsify every O*.ctl_*_accepts_* conjunct"),
    dict(id="VT05", file=V, kind="claim", count=1,
         old="        for name, claim in claims:\n"
             "            s = Solver(); s.set(\"timeout\", SMT_TIMEOUT_MS)",
         new="        claims = [(nm, cl == cl) for nm, cl in claims]\n"
             "        for name, claim in claims:\n"
             "            s = Solver(); s.set(\"timeout\", SMT_TIMEOUT_MS)",
         desc="EVERY SMT conjunct rewritten to `x == x` -- must falsify every "
              "S*.claims_discriminate (an unguarded suite proves all of them)"),
    dict(id="VT06", file=V, kind="claim", count=1,
         old="        prem, claims = build()\n        worst = 0.0",
         new="        prem, claims = build()\n"
             "        prem = list(prem) + [Int('_vac') > 0, Int('_vac') < 0]\n"
             "        worst = 0.0",
         desc="contradictory premises in EVERY SMT obligation -- must falsify "
              "every S*.premises_sat (this is what retires their exemptions)"),
    dict(id="VT07", file=O, kind="claim", count=1,
         old="    return _solver(prem).check() == sat",
         new="    return _solver(prem + [Int('_vac') > 0, Int('_vac') < 0]).check() == sat",
         desc="contradictory premises in every O-series obligation -- must falsify "
              "O3/O4/O7's premises_sat conjuncts"),
    dict(id="VT08", file=V, kind="claim", count=1,
         old="    got_obl = [r[0] for r in results] + [\"META-IDS\"]",
         new="    got_obl = [r[0] for r in results]",
         desc="META-IDS excluded from its own pinned set (the self-exclusion "
              "defect) -- the tally reconciliation must now catch it"),
    dict(id="VT09", file=O, kind="claim", count=1,
         old="    return _solver(prem, negated_claim).check() == sat",
         new="    return _solver(prem + [Int('_vac') > 0, Int('_vac') < 0],"
             " negated_claim).check() == sat",
         desc="contradictory premises in every O-series refutability CONTROL -- must "
              "falsify O3/O4/O7's nine ctl_* conjuncts at once"),
    # ---- the C16/C9f/C9g conjuncts the mutations above cannot reach ---------
    dict(id="V148", file=V, kind="claim", count=1,
         old='                    len(fwd_shapes) == 2 and all(s == fwd_shape for s in fwd_shapes)',
         new='                    len(fwd_shapes) == 3 and all(s == fwd_shape for s in fwd_shapes)',
         desc="C16: ALL THREE shipped copies of the forward transform are read "
              "(reads every shipped copy)"),
    dict(id="V149", file=V, kind="claim", count=1,
         old='                    len(inv_shapes) == 2 and all(s == inv_shape for s in inv_shapes)',
         new='                    len(inv_shapes) == 3 and all(s == inv_shape for s in inv_shapes)',
         desc="C16: ALL THREE shipped copies of the inverse transform are read"),
    dict(id="V150", file=V, kind="claim", count=1,
         old='                    and sh["K_per_block"] == [[2], [2], [2]]',
         new='                    and sh["K_per_block"] == [[2], [2], [4]]',
         desc="C16: the EXTRACTED forward schedule is +2q at every one of the "
              "three fused marker-delimited blocks"),
    dict(id="V151", file=V, kind="claim", count=1,
         old='                    and sh["K_per_block"] == [[2, 1 << 30, 1 << 31],\n'
             '                                              [4, 8], [16, 32], [2, 64, 128]]',
         new='                    and sh["K_per_block"] == [[2, 1 << 30, 1 << 31],\n'
             '                                              [4, 8], [16, 32], [2, 64]]',
         desc="C16: the EXTRACTED inverse schedule is K = 2^(L-1) for L = 1..8"),
    dict(id="V152", file=V, kind="claim", count=1,
         old='                     ("final_lane_lt_2p28", fwd_lb[8] < (1 << 28)),',
         new='                     ("final_lane_lt_2p28", fwd_lb[8] < (1 << 27)),',
         desc="C9f: 17q < 2^28 is the exact forward final-lane headroom (2^27 "
              "does not fit)"),
    dict(id="V153", file=V, kind="claim", count=1,
         old="    inv_barrett_in = inv_barrett_inputs(7)",
         new="    inv_barrett_in = inv_barrett_inputs(8)",
         desc="C9g: the Barrett layers are L1..L7; admitting L8 takes the max "
              "input to 256q(q-1), outside C9d/S2/S4/E9b's verified domain"),
]

# ---------------------------------------------------------------------------
# THE TOTAL REGION PARTITION.
#
# A C16 that sliced only the INTERIOR of the profiling-marker sequence, and
# summarised each block by the SET of offset-constant names it mentions, would
# leave the function's head and tail in no block at all, and a deleted
# `add(u, Q4_16)` would keep the name alive.  Three one-file, no-trace edits to
# the shipped Yul then leave the extracted shape byte-identical and the suite at
# ALL CHECKS PASS.  V162 is the direct regression mutation -- it reinstates that
# interior-only slicing and MUST kill -- and V154..V161 make each conjunct and
# each discrimination control of the partition individually load-bearing.
# ---------------------------------------------------------------------------
MUTS += [
    dict(id="V154", file=V, kind="claim", count=1,
         old='        return (r["K"] == () and r["barrett"] == 0 and r["red2"] == 0\n'
             '                and r["mod"] == 0\n'
             '                and r["mstore"] == 0 and r["mload"] == 0 and r["mul"] == 0\n'
             '                and r["mulmod"] == 0 and r["addmod"] == 0)',
         new='        return (r["K"] != () or r["barrett"] != 0 or r["red2"] != 0\n'
             '                or r["mod"] != 0\n'
             '                or r["mstore"] != 0 or r["mload"] != 0 or r["mul"] != 0\n'
             '                or r["mulmod"] != 0 or r["addmod"] != 0)',
         desc="C16: `_inert` inverted -- the head/tail inertness conjuncts and the "
              "shape predicates that use them must FAIL"),
    dict(id="V155", file=V, kind="claim", count=1,
         old='        return (r["K"] == () and r["barrett"] == 0 and r["red2"] == 0\n'
             '                and r["mod"] == 0\n'
             '                and r["mstore"] == 0 and r["mload"] == 0 and r["mul"] == 0\n'
             '                and r["mulmod"] == 0 and r["addmod"] == 0)',
         new='        return (r["K"] == r["K"] and r["barrett"] >= 0 and r["red2"] >= 0\n'
             '                and r["mod"] >= 0\n'
             '                and r["mstore"] >= 0 and r["mload"] >= 0 and r["mul"] >= 0\n'
             '                and r["mulmod"] >= 0 and r["addmod"] >= 0)',
         desc="C16: `_inert` weakened to a tautology -- the payload-before-the-first-"
              "marker and payload-after-the-last-marker CONTROLS must FAIL (this is "
              "out-of-partition payload becoming invisible again)"),
    dict(id="V156", file=V, kind="claim", count=1,
         old='        return r["mstore"] > 0 and 2 * sum(c for _o, c in r["K"]) == layers * r["mstore"]',
         new='        return r["mstore"] > 0 and 2 * sum(c for _o, c in r["K"]) == layers * r["mstore"] + 2',
         desc="C16: in a radix-2^L fused block the offset-occurrence count is "
              "L/2 times the store count (one offset per butterfly, one store "
              "per output word)"),
    dict(id="V157", file=V, kind="claim", count=1,
         old='        return r["mstore"] > 0 and 2 * sum(c for _o, c in r["K"]) == layers * r["mstore"]',
         new='        return sum(c for _o, c in r["K"]) >= 0',
         desc="C16: `_offsets_every_butterfly` weakened to a tautology -- the "
              "one-offset-dropped CONTROL must FAIL (a dropped butterfly offset)"),
    dict(id="V158", file=V, kind="claim", count=1,
         old='            mul=len(_PLAINMUL_RE.findall(text)),',
         new='            mul=len(_PLAINMUL_RE.findall(text)) + 1,',
         desc="C16: the per-region occurrence counts are the pinned ones"),
    dict(id="V162", file=V, kind="claim", count=1,
         old="        cuts = ([(0, marks[0].start())]\n"
             "                + [(marks[k].end(), marks[k + 1].start()) for k in range(len(marks) - 1)]\n"
             "                + [(marks[-1].end(), len(body))])",
         new="        cuts = [(marks[k].end(), marks[k + 1].start())\n"
             "                for k in range(len(marks) - 1)]",
         desc="C16: THE PARTITION DEFECT ITSELF -- interior-only slicing, "
              "under which a ninth unreduced layer after the last marker and a "
              "lane-corrupting loop before the first one were both invisible"),

    # ---- S14: the inverse NTT's entry fold (raw-accumulator mulmod/addmod) --
    # Without the five mutations below, S14's five conjuncts have no killer at
    # all; per the rule above the catalogue is extended rather than
    # the conjuncts deleted -- each one is a real property of the emitted code.
    dict(id="V163", file=V, kind="claim", count=1,
         old='            ("l1_operand_no_evm_wrap", u0 + (Q << 30) < (1 << 256)),',
         new='            ("l1_operand_no_evm_wrap", u0 + (Q << 30) < (1 << 50)),',
         desc="S14: the L1 mulmod operand really needs the full 256-bit headroom "
              "claim -- a 2^50 bound is false over the premise domain"),
    dict(id="V164", file=V, kind="claim", count=1,
         old='            ("l1_sum_lane_le_2acc", u0 + u1 <= 2 * ACC),',
         new='            ("l1_sum_lane_le_2acc", u0 + u1 <= ACC),',
         desc="S14: the raw L1 sum lane reaches 2*ACC_ENTRY, not ACC_ENTRY -- "
              "this is the bound the ACCQ31 offset is sized for"),
    dict(id="V165", file=V, kind="claim", count=1,
         old="        l2_op = s01 + (Q << 31) - s23",
         new="        l2_op = s01 + (Q << 21) - s23",
         desc="S14: an L2 offset too small for a raw sum lane borrows -- "
              "l2_diff_no_borrow must FAIL (the congruence conjunct alone cannot "
              "see it: q*2^21 is still a multiple of q)"),
    dict(id="V166", file=V, kind="claim", count=1,
         old="        l2_op = s01 + (Q << 31) - s23",
         new="        l2_op = s01 + (Q << 31) + 1 - s23",
         desc="S14: an L2 offset that is NOT a multiple of q shifts the residue "
              "class -- l2_diff_congruent must FAIL (no_borrow alone cannot see it)"),
    dict(id="V167", file=V, kind="claim", count=1,
         old='            ("l2_operand_no_evm_wrap", s01 + (Q << 31) < (1 << 256)),',
         new='            ("l2_operand_no_evm_wrap", s01 + (Q << 31) < (1 << 51)),',
         desc="S14: the L2 mulmod operand really needs the full 256-bit headroom "
              "claim -- a 2^51 bound is false over the premise domain"),
    dict(id="V168", file=V, kind="claim", count=1,
         old='    _C16_BODY_DIGEST = {"fwd": "8719fdd28e9a6a676b3e134a5dd2fe9f",',
         new='    _C16_BODY_DIGEST = {"fwd": "8719fdd28e9a6a676b3e134a5dd2fe90",',
         desc="C16: the pinned FORWARD body digest is load-bearing -- a moved pin "
              "must fail fwd_body_digest_is_the_pinned_one"),
    dict(id="V169", file=V, kind="claim", count=1,
         old='                        "inv": "d50c74870791865c2d13504d1733ae08"}\n'
             '    _C16_FILE_DIGEST',
         new='                        "inv": "d50c74870791865c2d13504d1733ae00"}\n'
             '    _C16_FILE_DIGEST',
         desc="C16: the pinned INVERSE body digest is load-bearing"),
    dict(id="V170", file=V, kind="claim", count=1,
         old='    _C16_FILE_DIGEST = {"fwd": "88f75ee9baa21a9c87aa42024c450ebc",',
         new='    _C16_FILE_DIGEST = {"fwd": "88f75ee9baa21a9c87aa42024c450eb0",',
         desc="C16: the pinned FORWARD file digest is load-bearing -- a moved pin "
              "must fail fwd_shipped_sources_are_the_pinned_bytes"),
    dict(id="V171", file=V, kind="claim", count=1,
         old='                        "inv": "95de939acb7a1b2a2a07b0e4fb5b7f41"}',
         new='                        "inv": "95de939acb7a1b2a2a07b0e4fb5b7f40"}',
         desc="C16: the pinned INVERSE file digest is load-bearing"),
    dict(id="V172", file=V, kind="claim", count=1,
         old="    ACC_ENTRY = acc_entry(PK_AMAX)                  # == O8's lane_max",
         new="    ACC_ENTRY = acc_entry(PK_AMAX) - 1              # == O8's lane_max",
         desc="C9g: the entry ceiling must be EXACTLY O8's lane_max -- "
              "entry_is_O8_lane_max must FAIL on a drifted value"),
    dict(id="V173", file=V, kind="claim", count=1,
         old='                     ("l1_offset_dominates_entry", ACC_ENTRY <= (Q << 30)),',
         new='                     ("l1_offset_dominates_entry", ACC_ENTRY <= (Q << 22)),',
         desc="C9g: the L1 entry offset really has to dominate ACC_ENTRY -- "
              "a q*2^22 offset does not"),
    dict(id="V174", file=V, kind="claim", count=1,
         old='                     ("l2_offset_dominates_sum_lane", 2 * ACC_ENTRY <= (Q << 31)),',
         new='                     ("l2_offset_dominates_sum_lane", 2 * ACC_ENTRY <= (Q << 23)),',
         desc="C9g: the L2 entry offset really has to dominate 2*ACC_ENTRY"),
    dict(id="V175", file=V, kind="claim", count=1,
         old="    inv_exit_bound = 2 * Q                          # every L1+L2 exit lane (S14)",
         new="    inv_exit_bound = 8 * Q                          # every L1+L2 exit lane (S14)",
         desc="C9g: an entry block that exits above 4q busts layer 3's premise -- "
              "l1l2_exit_meets_l3_premise must FAIL"),
    dict(id="V176", file=O, kind="claim", count=1,
         old="    ok_entry = dominated_by_entry_offset((lane_max, Q << 30))",
         new="    ok_entry = dominated_by_entry_offset((lane_max, Q << 20))",
         desc="O8: the producer/consumer linkage -- the matvec lane ceiling must be "
              "dominated by the inverse NTT's S14 entry offset"),
    dict(id="V177", file=V, kind="claim", count=1,
         old='            ("inv_ACCQ31_is_q_shl_31", ic["ACCQ31"] == Q << 31),',
         new='            ("inv_ACCQ31_is_q_shl_31", ic["ACCQ31"] == Q << 30),',
         desc="C16: the entry-fold L2 offset is exactly q*2^31 (a multiple of q "
              "that dominates two raw accumulator lanes)"),
    dict(id="V178", file=V, kind="claim", count=1,
         old="        l1_op = u0 + (Q << 30) - u1",
         new="        l1_op = u0 + (Q << 20) - u1",
         desc="S14: an L1 offset too small for a raw lane borrows -- "
              "l1_diff_no_borrow must FAIL (q*2^20 is still a multiple of q, so "
              "the congruence conjunct alone cannot see it)"),
    dict(id="V179", file=V, kind="claim", count=1,
         old="        l1_op = u0 + (Q << 30) - u1",
         new="        l1_op = u0 + (Q << 30) + 1 - u1",
         desc="S14: an L1 offset that is NOT a multiple of q shifts the residue "
              "class -- l1_diff_congruent must FAIL (no_borrow alone cannot see it)"),
    dict(id="V180", file=V, kind="claim", count=1,
         old='            ("exit_diff_sum_lane_lt_2q", d01 + d23 < 2 * Q),',
         new='            ("exit_diff_sum_lane_lt_2q", d01 + d23 < Q),',
         desc="S14: the diff-sum exit lane genuinely reaches [q, 2q) -- a < q "
              "claim is false over the premise domain"),
    dict(id="V181", file=V, kind="claim", count=1,
         old='            ("exit_lanes_meet_l3_premise", d01 + d23 < 4 * Q),',
         new='            ("exit_lanes_meet_l3_premise", d01 + d23 < Q),',
         desc="S14: the exit-meets-L3-premise conjunct is a real bound, not "
              "decoration"),
    dict(id="V182", file=V, kind="claim", count=1,
         old='                [("no_earlier_failure", r < 2 * Q),',
         new='                [("no_earlier_failure", r < 2 * Q),\n'
             '                 ("no_earlier_failure", r < 2 * Q),',
         desc="META-IDS: a DUPLICATED conjunct row must fail "
              "no_duplicate_conjuncts (the tally would otherwise double-count)"),
    dict(id="V183", file=V, kind="claim", count=1,
         old='    ok &= pinned("C1", "CALC", "MU33 == floor(2^33/Q)",\n'
             '                 lambda mu: mu == (1 << 33) // Q, MU33, str(MU33),\n'
             '                 accept=[1025], reject=[1026, 1024, 0x200801C0, 0])',
         new='    ok &= pinned("C1", "CALC", "MU33 == floor(2^33/Q)",\n'
             '                 lambda mu: mu == (1 << 33) // Q, MU33, str(MU33),\n'
             '                 accept=[1025], reject=[1026, 1024, 0x200801C0, 0])\n'
             '    ok &= pinned("C1", "CALC", "MU33 == floor(2^33/Q)",\n'
             '                 lambda mu: mu == (1 << 33) // Q, MU33, str(MU33),\n'
             '                 accept=[1025], reject=[1026, 1024, 0x200801C0, 0])',
         desc="META-IDS: a DUPLICATED obligation row must fail "
              "no_duplicate_obligations"),
    # ---- C17: the SWAR mod-44 magic division of useHintSwar -----------------
    # C17 covers useHintSwar's fold of two mod-44 reductions into one; these
    # four mutations are its discrimination controls.  Without them the audit
    # reports C17 and all six of its conjuncts as never-killed, which is
    # exactly what the audit is for.
    dict(id="V184", file=V, kind="claim", count=1,
         old='    SW_M44 = dc.get("SW_M44", -1)',
         new='    SW_M44 = dc.get("SW_M44", -1) - 1',
         desc="C17: the magic constant must be ceil(2^12/44); 93 makes the "
              "division wrong from T = 44 (i.e. below the reachable maximum)"),
    dict(id="V185", file=V, kind="claim", count=1,
         old="    T_MAX = 44 + 43                                  # max S1 + max ADJ",
         new="    T_MAX = 44 + 430                                 # max S1 + max ADJ",
         desc="C17: the reachable bound on T is load-bearing -- widen it past "
              "the magic division's exact range and the quotient stops fitting "
              "the REP1 mask"),
    dict(id="V186", file=V, kind="claim", count=1,
         old='    SW_M44 = dc.get("SW_M44", -1)\n',
         new='    SW_M44 = dc.get("SW_M44", -1) << 60\n',
         desc="C17: the SWAR lane budget -- a magic constant this large makes "
              "the lane product T*M exceed 2^64 and carry into the next lane"),
    dict(id="V187", file=V, kind="claim", count=1,
         old="                         all(((s1 % 44) + adj) % 44 == (s1 + adj) % 44",
         new="                         all(((s1 % 43) + adj) % 44 == (s1 + adj) % 44",
         desc="C17: folding the two reductions is exact only because the "
              "INTERMEDIATE modulus is 44 as well"),
]


# ---------------------------------------------------------------------------
# C18 / E15 AND THE PK-CANONICALITY PREMISE.
# ---------------------------------------------------------------------------
# C18 exists because without it NOTHING under formal/ reads src/Decode.sol or
# src/MLDSA44Verifier.sol -- the two files that carry every FIPS 204 validity
# check -- and four demonstrated mutations leave the whole apparatus green.  An
# obligation is only evidence if it can FAIL, so each group of its conjuncts
# gets a mutation here.  The mutations are chosen to break the SHARED path
# wherever one exists (the extraction helpers, the two constant tables), so that
# a group of conjuncts falls together rather than needing one mutation each.
MUTS += [
    # ---- C18: the extracted constant tables --------------------------------
    dict(id="V190", file=V, kind="kernel", count=1,
         old="        dc, vc = _consts(dec_code), _consts(ver_code)",
         new="        dc, vc = {k: v + 1 for k, v in _consts(dec_code).items()}, _consts(ver_code)",
         desc="C18: every Decode.sol constant is compared against the ARITHMETIC it "
              "must be; a drifted extraction must falsify all of them (and C17, whose "
              "magic constant is read from the same table)"),
    dict(id="V191", file=V, kind="kernel", count=1,
         old="        dc, vc = _consts(dec_code), _consts(ver_code)",
         new="        dc, vc = _consts(dec_code), {k: v + 1 for k, v in _consts(ver_code).items()}",
         desc="C18/C15b: the verifier's PK_SIZE / PK_T1_OFF / PK_A_OFF are compared "
              "against C15b's width arithmetic -- the linkage that `PK_SIZE = 20000` "
              "walked straight through"),
    dict(id="V192", file=V, kind="claim", count=1,
         old='    _C18_FILE_DIGEST = {"dec": "8b9fb8dbc8fcebc64c122063c64e6b5b",\n'
             '                        "ver": "79223e8482d012223df501e498a4c2d9",',
         new='    _C18_FILE_DIGEST = {"dec": "00000000000000000000000000000000",\n'
             '                        "ver": "00000000000000000000000000000000",',
         desc="C18: the two check files' whole-file residual digests -- the catch-all "
              "for any payload the extraction does not model"),
    dict(id="V193", file=V, kind="claim", count=1,
         old='    _C18_DEAD = ("SW_REP42", "SW_REP44", "SW_K3244", "MU52", "SW_SPREAD")',
         new='    _C18_DEAD = ("SW_REP1", "PK_SIZE")',
         desc="C18: a constant declared and never read is unpinned surface; the "
              "dead-constant conjuncts must FAIL when a LIVE name is listed"),
    # ---- C18: the two extraction helpers -----------------------------------
    dict(id="V194", file=V, kind="kernel", count=1,
         old="        return tuple(int(g, 0) for g in hits[0]) if isinstance(hits[0], tuple) \\\n"
             "            else int(hits[0], 0)",
         new="        return tuple(int(g, 0) + 1 for g in hits[0]) if isinstance(hits[0], tuple) \\\n"
             "            else int(hits[0], 0) + 1",
         desc="C18: every VALUE read out of the shipped source -- trip counts, slice "
              "widths, the omega check, both padding-shift boundaries, the signature "
              "length, the tr offset -- must move when the extraction does"),
    dict(id="V195", file=V, kind="kernel", count=1,
         old="        if len(hits) != want_n or len(set(hits)) != 1:\n"
             "            raise ValueError(f\"{what}: {hits!r}, expected {want_n} equal values\")\n"
             "        return hits[0]",
         new="        if len(hits) != want_n or len(set(hits)) != 1:\n"
             "            raise ValueError(f\"{what}: {hits!r}, expected {want_n} equal values\")\n"
             "        return hits[0] + 1",
         desc="C18: the mod-44 magic shift and subtrahend, read from all eight "
              "unrolled sites and required to agree"),
    dict(id="V196", file=V, kind="kernel", count=1,
         old="        return sum(1 for k in range(4)\n"
             "                   if (word >> (64 * k)) & ((1 << 64) - 1) == lane_value)",
         new="        return 3",
         desc="C18: the z check is FOUR lanes wide because the window constants are "
              "replicated four times; a blanked lane must be visible (mutant M60)"),
    # ---- C18: the counted check sites ---------------------------------------
    dict(id="V197", file=V, kind="claim", count=1,
         old='            ("dec_z_norm_gate_sites_is_4", _agrees((z_sites, 4))),',
         new='            ("dec_z_norm_gate_sites_is_4", _agrees((z_sites, 5))),',
         desc="C18: the four norm-check sites of the shipped z decoder"),
    dict(id="V198", file=V, kind="claim", count=1,
         old='            ("dec_z_canonicalisation_sites_is_4", _agrees((z_canon, 4))),',
         new='            ("dec_z_canonicalisation_sites_is_4", _agrees((z_canon, 5))),',
         desc="C18: the four canonicalisation sites (one conditional subtract each)"),
    dict(id="V199", file=V, kind="claim", count=1,
         old='            ("dec_z_verdict_word_is_read_once", _agrees((z_verdict, 1))),',
         new='            ("dec_z_verdict_word_is_read_once", _agrees((z_verdict, 2))),',
         desc="C18: a check whose verdict word is never read is not a check"),
    dict(id="V200", file=V, kind="claim", count=1,
         old='            ("dec_h_strict_increase_gate_present", _agrees(((h_strict, h_prev), (1, 1)))),',
         new='            ("dec_h_strict_increase_gate_present", _agrees(((h_strict, h_prev), (2, 2)))),',
         desc="C18: Alg. 21 line 12, the strict-increase check and its prevP seed"),
    dict(id="V201", file=V, kind="claim", count=1,
         old='            ("dec_h_monotone_counter_gate_present", _agrees((h_mono, 1))),',
         new='            ("dec_h_monotone_counter_gate_present", _agrees((h_mono, 2))),',
         desc="C18: Alg. 21 line 4, first disjunct (non-decreasing cut counters)"),
    dict(id="V202", file=V, kind="claim", count=1,
         old='            ("dec_h_padding_gate_present", _agrees((h_pad, 1))),',
         new='            ("dec_h_padding_gate_present", _agrees((h_pad, 2))),',
         desc="C18: Alg. 21 lines 16-18, the padding check's verdict"),
    dict(id="V203", file=V, kind="claim", count=1,
         old='            ("ver_pk_size_gate_is_exact", _agrees((v_size_gate, 1))),',
         new='            ("ver_pk_size_gate_is_exact", _agrees((v_size_gate, 2))),',
         desc="C18: the pk data-contract size check, present exactly once"),
    dict(id="V204", file=V, kind="claim", count=1,
         old='            ("ver_helper_is_pinned_at_construction_and_per_call",\n'
             '             _agrees((v_codehash, 2))),',
         new='            ("ver_helper_is_pinned_at_construction_and_per_call",\n'
             '             _agrees((v_codehash, 3))),',
         desc="C18: the Keccak helper codehash check, at construction AND per call"),
    # ---- E15: the padding-check grid ----------------------------------------
    dict(id="V205", file=V, kind="kernel", count=1,
         old="        pad = (_evm_shl((c[3] * 8) & _M256, w0)\n"
             "               | _evm_shl((s1 * 8) & _M256, w1)\n"
             "               | _evm_shl((s2 * 8) & _M256, w2))",
         new="        pad = (_evm_shl((c[3] * 8) & _M256, w0)\n"
             "               | _evm_shl((s1 * 8) & _M256, w1))",
         desc="E15: the THIRD padding word dropped -- index bytes 64..79 stop being "
              "checked, which is the shape of the demonstrated malleability break"),
    dict(id="V206", file=V, kind="claim", count=1,
         old='                   ("grid_reaches_the_second_word_boundary", OMEGA > 64),',
         new='                   ("grid_reaches_the_second_word_boundary", OMEGA > 80),',
         desc="E15: the grid must actually REACH the c3 >= 64 branch -- the branch no "
              "test, mutant or obligation reached before"),
    dict(id="V207", file=V, kind="kernel", count=1,
         old='            parts=[("canonical_weight_zero_accepted",\n'
             '                    _hint_gate_accepts(bytearray(OMEGA + L_DIM), _hint_prm)),',
         new='            parts=[("canonical_weight_zero_accepted",\n'
             '                    _hint_gate_accepts(bytearray(b"\\xff" * (OMEGA + L_DIM)), _hint_prm)),',
         desc="E15: the all-zero encoding is the one canonical encoding of the empty "
              "hint set and must be ACCEPTED"),
    # ---- the pk-canonicality premise, in all three places ------------------
    dict(id="V208", file=V, kind="claim", count=1,
         old='                     ("pk_coefficient_ceiling_is_q", PK_AMAX == Q),',
         new='                     ("pk_coefficient_ceiling_is_q", PK_AMAX == 2 * Q),',
         desc="C9g: the accumulator ceiling is a function of the pk-coefficient "
              "ceiling, and that premise is stated rather than carried in a `Q - 1`"),
    dict(id="V209", file=O, kind="claim", count=2,
         old='("pk_coefficient_ceiling_is_q", PK_AMAX == Q)',
         new='("pk_coefficient_ceiling_is_q", PK_AMAX == 2 * Q)',
         desc="O7/O8: the same premise, in the two obligations whose products are "
              "taken over a CACHED pk coefficient"),
    dict(id="V210", file=O, kind="claim", count=1,
         old="    def entry_offset_dominates(amax):\n"
             "        return 4 * (amax - 1) * ZMAX + KQ28 <= (Q << 30)",
         new="    def entry_offset_dominates(amax):\n"
             "        return 4 * (amax - 1) * ZMAX + KQ28 <= (Q << 40)",
         desc="O8: the discrimination control for the canonicality premise -- the "
              "entry-fold domination must FAIL at 2q, or `pk coefficients are "
              "canonical` is an assumption nothing can falsify"),
    # ---- O4, restated over the shipped magic division ----------------------
    dict(id="V211", file=O, kind="claim", count=1,
         old="               (\"quotient_fits_the_rep1_mask\",\n"
             "                all(((t * SW_M44) >> SW_M44_SHIFT) <= 1 for t in range(SW_T_MAX + 1))),",
         new="               (\"quotient_fits_the_rep1_mask\",\n"
             "                all(((t * SW_M44) >> SW_M44_SHIFT) <= 0 for t in range(SW_T_MAX + 1))),",
         desc="O4: the magic division's quotient must fit the REP1 mask the kernel "
              "ANDs it with, or the subtrahend spills into the next SWAR lane"),
    # This conjunct is a RELATIVE claim -- "the threshold and the subtrahend of
    # each padding shift are the SAME word boundary" -- so it is invariant under
    # V194's uniform +1 on every extracted value, and without the mutation
    # below it is the one never-killed conjunct in the tree.  It needs a
    # mutation that breaks the AGREEMENT rather than the magnitudes, which is
    # also exactly the shape of the defect it exists to catch (`gt(c3, 64)` with
    # `sub(c3, 63)`).
    dict(id="V212", file=V, kind="claim", count=1,
         old='            ("dec_h_pad_word_boundaries_are_the_shift_thresholds",\n'
             '             _agrees(((h_s1[0], h_s2[0], h_s1[0], h_s2[0]),\n'
             '                      (h_w1, h_w1 + 32, h_s1[1], h_s2[1])))),',
         new='            ("dec_h_pad_word_boundaries_are_the_shift_thresholds",\n'
             '             _agrees(((h_s1[0], h_s2[0], h_s1[0], h_s2[0]),\n'
             '                      (h_w1 + 1, h_w1 + 32, h_s1[1], h_s2[1])))),',
         desc="C18: each padding shift's THRESHOLD and its SUBTRAHEND must be the "
              "same word boundary -- the agreement, not the magnitudes, is what "
              "makes the shift cover exactly the padding"),
]


# ---------------------------------------------------------------------------
# THE TWO UNDIGESTED src/ FILES, THE SCAN CLAMP, AND THE CONTROL THAT DOES
# NOT CONTROL.
# ---------------------------------------------------------------------------
# Three structural holes of the same class as a check file that nothing reads,
# each of them made visible by the mutations below:
#
#  * `src/FastKeccak170.sol` and `src/IMLDSAVerifier.sol` are shipped files it
#    is easy to leave covered by NO digest and NO value extraction anywhere in
#    the repository -- exactly the shape that lets a payload hide in `src/`.
#  * C18's seven `ctl_extracted_value_is_the_proved_value` controls are only
#    controls if the substantive conjuncts route their comparison through
#    `_agrees`.  A conjunct that spells its comparison inline is not protected
#    by a control over a helper nothing calls, so all of them route through it.
#  * the scan clamp needs BOTH operands captured.  A regex that captures the
#    SUBTRAHEND and leaves the `gt` THRESHOLD uncaptured pins nothing about the
#    operand deciding whether the index scan stays inside its 84-byte object.
#
# V217 is the `_agrees` mutation and it is deliberately BROAD: with the
# comparisons routed, inverting `_agrees` falsifies every conjunct the controls
# are supposed to protect AND all seven control rows -- which is the point.  The
# same edit against a suite whose conjuncts compare inline fails the seven
# controls and NOTHING else, leaving every substantive C18 conjunct PASS;
# against this one it fails EVERY one of C18's 85 rows -- a count that includes
# the six MV_* lane/offset constants and the two SWAR magic-division rows.
MUTS += [
    dict(id="V213", file=V, kind="claim", count=1,
         old='            ("dec_h_scan_clamp_is_80", _agrees((h_clamp, (OMEGA, OMEGA)))),',
         new='            ("dec_h_scan_clamp_is_80", _agrees((h_clamp, (OMEGA, 255)))),',
         desc="C18: the scan clamp's GT THRESHOLD, which the old pattern did not "
              "capture -- naming 255 there is exactly the defect, and it can only be "
              "named at all because both operands are now read"),
    dict(id="V214", file=V, kind="kernel", count=1,
         old="        return hi <= OMEGA",
         new="        return hi <= 255",
         desc="E15: the scan-clamp memory-safety bound RELAXED to the whole byte "
              "domain -- the three reject controls must catch that the clamp is what "
              "keeps the index scan inside the 80-byte index array"),
    dict(id="V215", file=V, kind="claim", count=1,
         old="        _hint_clamp = (h_clamp[0], h_clamp[1])",
         new="        _hint_clamp = (h_clamp[0], 255)",
         desc="E15: ONLY the clamp's gt threshold moved (the verdict-equivalent "
              "edit): at gt(cut,255) the scan reads ~171 bytes past the 84-byte "
              "object, inside a block annotated memory-safe"),
    dict(id="V216", file=V, kind="kernel", count=1,
         old="        return hi <= OMEGA",
         new="        return hi < OMEGA",
         desc="E15: the same bound TIGHTENED past the shipped clamp -- the accept "
              "controls must catch a memory-safety claim that rejects the artefact"),
    dict(id="V217", file=V, kind="kernel", count=1,
         old="    def _agrees(pair):\n"
             '        """The value EXTRACTED from the shipped source IS the value proved."""\n'
             "        return pair[0] == pair[1]",
         new="    def _agrees(pair):\n"
             '        """The value EXTRACTED from the shipped source IS the value proved."""\n'
             "        return pair[0] != pair[1]",
         desc="C18: the extracted-vs-proved comparison itself -- with every "
              "conjunct routed through it, the seven discrimination controls are a "
              "control over those conjuncts and not over a helper nobody calls"),
    dict(id="V218", file=V, kind="kernel", count=1,
         old="        kc = _consts(kec_code)",
         new="        kc = {k: v + 1 for k, v in _consts(kec_code).items()}",
         desc="C18: src/FastKeccak170.sol's file-scope lane mask, which no digest "
              "and no extraction in the repository covered before"),
    dict(id="V219", file=V, kind="claim", count=1,
         old='                        "kec": "bee72ebc57e8a1f95d73dd5f69d281af",\n'
             '                        "ifc": "0f50c68aab1ffdda8412fc89779e9070",',
         new='                        "kec": "00000000000000000000000000000000",\n'
             '                        "ifc": "00000000000000000000000000000000",',
         desc="C18: the two NEW whole-file residual digests -- src/FastKeccak170.sol "
              "and src/IMLDSAVerifier.sol were shipped files covered by nothing"),
    # ---- the FV2 refinement harness, and C18's completeness ----------------
    dict(id="V220", file=V, kind="claim", count=1,
         old='                        "fv2": "12d662de11e4edd03b0b230e01e93e73"}',
         new='                        "fv2": "00000000000000000000000000000000"}',
         desc="C18: the residual digest over test/FV2_Barrett.sol -- the harness "
              "FORMAL_VERIFICATION.md 5.7 cites as CLOSING the Barrett refinement gap, "
              "which was imported by no test and covered by no digest at all"),
    dict(id="V221", file=V, kind="kernel", count=1,
         old='    _DECL_CONST_RE = re.compile(\n'
             '        r"^\\s*[A-Za-z_][A-Za-z0-9_]*\\s+(?:(?:public|private|internal)\\s+)?constant\\s+(\\w+)\\s*=",\n'
             '        re.M)',
         new='    _DECL_CONST_RE = re.compile(\n'
             '        r"^\\s*uint256\\s+constant\\s+(\\w+)\\s*=",\n'
             '        re.M)',
         desc="C18: the DECLARED-constant scan must see every type at every scope. "
              "Narrowed back to `uint256 constant` it loses `bytes32 private constant "
              "F1600_CODEHASH`, which is exactly the constant the set equality exists "
              "to make visible"),
    dict(id="V222", file=V, kind="kernel", count=1,
         old='        return sorted(n for n in names\n'
             '                      if len(re.findall(r"\\b" + re.escape(n) + r"\\b", code)) < 2)',
         new='        return sorted(n for n in names\n'
             '                      if len(re.findall(r"\\b" + re.escape(n) + r"\\b", code)) >= 2)',
         desc="C18: the rename-alias DECOY check -- a constant occurring only in its "
              "own declaration must be a failure; inverting the predicate must falsify "
              "all three files' `every_constant_is_read_outside_its_declaration`"),
    dict(id="V223", file=V, kind="kernel", count=1,
         old='        names = [m.group(1) for m in _DECL_CONST_RE.finditer(code)]',
         new='        names = [m.group(1) for m in _DECL_CONST_RE.finditer(code)][1:]',
         desc="C18: the completeness check must be over the WHOLE declared block -- a "
              "dropped name is precisely where a rename-alias hides (MV_KQ28REP2 kept "
              "the correct declaration and moved all six use sites)"),
]


# ROW PARSING.  `re.findall(r"^\[PASS\] (\S+)")` would stop at the first space,
# and five obligation IDs contain spaces -- `C4[s (2^52 raw)]` and its siblings.
# Their CONJUNCT rows would then parse as the bare token `C4[s`, which has no
# `.` in it, so a dot-based split classifies them as OBLIGATIONS and merges them
# with the obligation row of the same name: 25 conjuncts (every C4 control) go
# unaudited individually and inherit the obligation's killers.  Obligation rows
# are distinguishable structurally -- they carry a KIND column -- so split on
# that instead of on the presence of a dot.
ROW_RE = re.compile(r"^\[(PASS|FAIL)\] (.+?)\s*$", re.M)
KIND_RE = re.compile(r"^(.*?)\s+(CALC|SMT|EXH)\s{2,}")


def split_rows(out, verdict=None):
    """(obligation_ids, conjunct_ids) from one suite run."""
    obl, conj = [], []
    for m in ROW_RE.finditer(out):
        if verdict and m.group(1) != verdict:
            continue
        row = m.group(2)
        km = KIND_RE.match(row)
        (obl if km else conj).append((km.group(1).strip() if km else row.strip()))
    return obl, conj


def all_rows(out, verdict=None):
    o, c = split_rows(out, verdict)
    return o + c


def run_one(m):
    tmp = tempfile.mkdtemp(prefix="vac-")
    try:
        for f in (V, O, S):
            shutil.copy(os.path.join(HERE, f), os.path.join(tmp, f))
        p = os.path.join(tmp, m["file"])
        src = open(p).read()
        n = src.count(m["old"])
        if n != m["count"]:
            return dict(id=m["id"], error=f"pattern occurs {n}x, expected {m['count']}x")
        open(p, "w").write(src.replace(m["old"], m["new"]))
        # `verify_all.py` REFUSES to run (exit 2, no obligations) if its own
        # whole-file AST digest is not the pinned `verify_all::@@file` region --
        # a hard, pre-suite anchor against a swapped-out suite file.  Every
        # mutation moves that digest, so the sandbox regenerates the pin tables
        # for the MUTATED copy before running it: the mutation under test stays
        # the only variable, and the audit measures obligations rather than the
        # tripwire.  This is a regeneration IN THE SANDBOX, not a bypass in the
        # suite -- `verify_all.py` still refuses in every other context, and
        # META-PINS still FAILS here (the sandbox copy is not the repo file), so
        # its ten conjuncts stay in CONJUNCT_EXEMPT with that reason.
        w = subprocess.run([PY, "source_pins.py", "--write"], cwd=tmp,
                           capture_output=True, text=True, timeout=600, env=ENV)
        if w.returncode != 0:
            return dict(id=m["id"],
                        error=f"source_pins.py --write failed in the sandbox: "
                              f"{(w.stderr or w.stdout)[-400:]}")
        r = subprocess.run([PY, "verify_all.py"], cwd=tmp, capture_output=True,
                           text=True, timeout=1800, env=ENV)
        out = r.stdout
        failed = all_rows(out, "FAIL")
        passed = all_rows(out, "PASS")
        # META-PINS digests the suite's own source, so it fires on EVERY
        # mutation by construction.  Counting those as kills would mean no mutation
        # could ever be reported as a BLIND SPOT -- the audit's main signal -- so
        # its rows are removed from the accounting here and its ten conjuncts are
        # listed in CONJUNCT_EXEMPT with that reason.  This is a filter in the
        # AUDIT, not an env-var bypass in the suite: `verify_all.py` still fails
        # closed on a digest mismatch in every other context.
        failed = [x for x in failed if not x.startswith("META-PINS")]
        passed = [x for x in passed if not x.startswith("META-PINS")]
        # A mutant that never reaches the tally line produced no verdict at all,
        # which is not the same as "kills 0" and must not be read as a statement
        # about the obligations.  Detect it on the tally, not on empty lists.
        crashed = ("obligations PASS" not in out)
        return dict(id=m["id"], desc=m["desc"], kind=m["kind"],
                    equiv=bool(m.get("equiv")), failed=failed,
                    n_pass=len(passed), crashed=crashed, rc=r.returncode,
                    stderr=(r.stderr[-900:] if crashed else ""))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--ids", default="")
    ap.add_argument("--out", default=os.path.join(HERE, "vacuity_results.json"))
    args = ap.parse_args()

    sel = set(x.strip() for x in args.ids.split(",") if x.strip())
    todo = [m for m in MUTS if not sel or m["id"] in sel]

    got_ids = [m["id"] for m in MUTS]
    if not sel and got_ids != EXPECTED_MUTATIONS:
        print(f"ABORT: catalogue is {len(got_ids)} mutations, pinned "
              f"{len(EXPECTED_MUTATIONS)}; missing "
              f"{sorted(set(EXPECTED_MUTATIONS) - set(got_ids))}, unpinned "
              f"{sorted(set(got_ids) - set(EXPECTED_MUTATIONS))}", file=sys.stderr)
        return 4

    # baseline: the unmutated suite, for the full obligation + conjunct ID list
    r = subprocess.run([PY, os.path.join(HERE, "verify_all.py")], cwd=HERE,
                       capture_output=True, text=True, env=ENV)
    # META-PINS IS kept in the baseline ID list on purpose: it must show up in
    # the audit table as an exempt, never-killed conjunct WITH ITS REASON rather
    # than disappear from the accounting altogether.
    obl_ids, conj_ids = split_rows(r.stdout, "PASS")
    all_ids = obl_ids + conj_ids
    base_fail = all_rows(r.stdout, "FAIL")
    obl_set = set(obl_ids)
    print(f"baseline: {len(all_ids)} PASS ({len(obl_ids)} obligations, "
          f"{len(conj_ids)} conjuncts), {len(base_fail)} FAIL")
    if base_fail:
        print(f"ABORT: baseline is not green: {base_fail}", file=sys.stderr)
        return 2

    results = []
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        for res in ex.map(run_one, todo):
            results.append(res)
            if res.get("error"):
                print(f"{res['id']}: CATALOGUE ERROR {res['error']}")
                continue
            tag = "EQUIV" if res["equiv"] else res["kind"].upper()
            kf = [x for x in res["failed"] if x in obl_set]
            kc = [x for x in res["failed"] if x not in obl_set]
            print(f"{res['id']:<5} {tag:<7} kills {len(kf):>3} obl / {len(kc):>3} conj: "
                  f"{','.join(kf[:6])}{' ...' if len(kf) > 6 else ''}"
                  f"{'  CRASHED' if res.get('crashed') else ''}"
                  f"   [{res['desc'][:50]}]", flush=True)
            json.dump(results, open(args.out, "w"), indent=1)

    if any(x.get("error") for x in results):
        print("\nABORT: catalogue is stale", file=sys.stderr)
        return 3

    # ---- the audit table --------------------------------------------------
    killers = {oid: [] for oid in all_ids}
    for res in results:
        if res["equiv"] or res.get("crashed"):
            continue
        for oid in res["failed"]:
            killers.setdefault(oid, []).append(res["id"])
    never_o_all = sorted(o for o in obl_ids if not killers.get(o))
    never_o = [o for o in never_o_all if not exempt_reason(o)]
    never_c_all = sorted(c for c in conj_ids if not killers.get(c))
    never_c = [c for c in never_c_all if not exempt_reason(c)]
    exempted = [x for x in never_o_all + never_c_all if exempt_reason(x)]

    # Category 1: a non-equivalent mutation that killed NOTHING is a hole in the
    # SUITE, not a property of any obligation, so it is reported on its own.
    blind = [rr for rr in results
             if not rr.get("error") and not rr["equiv"]
             and not rr.get("crashed") and not rr["failed"]]
    crashed = [rr for rr in results if rr.get("crashed")]
    bad_equiv = [(rr["id"], rr["failed"]) for rr in results if rr["equiv"] and rr["failed"]]

    print("\n" + "=" * 78)
    print(f"mutations run: {len(results)}   obligations: {len(obl_ids)}   "
          f"conjuncts: {len(conj_ids)}")
    print(f"BLIND SPOTS — non-equivalent mutations that killed NOTHING: {len(blind)}")
    for rr in blind:
        print(f"    !! {rr['id']} [{rr['kind']}] {rr['desc']}")
        print(f"       no obligation and no conjunct in the suite notices this defect")
    print(f"CRASHES — mutations whose run produced no verdict at all: {len(crashed)}")
    for rr in crashed:
        print(f"    !! {rr['id']} rc={rr.get('rc')} {rr['desc']}")
        print(f"       {rr.get('stderr', '')[-300:]}")
    print(f"obligations sensitive to >= 1 injected defect: "
          f"{len(obl_ids) - len(never_o_all)}/{len(obl_ids)}")
    for oid in never_o:
        print(f"    !! NEVER-KILLED OBLIGATION {oid}")
    print(f"conjuncts sensitive to >= 1 injected defect: "
          f"{len(conj_ids) - len(never_c_all)}/{len(conj_ids)}"
          f"  (+{len(exempted)} exempt in total, {len(never_c)} unexplained)")
    for cid in never_c:
        print(f"    !! NEVER-KILLED CONJUNCT {cid}")
    if exempted:
        print(f"  exempt rows ({len(exempted)}), each with a written reason:")
        for cid in exempted:
            print(f"    -- {cid}: {exempt_reason(cid)}")
    for mid, f in bad_equiv:
        print(f"  !! EQUIVALENT mutation {mid} killed {f} — that obligation is "
              f"over-specified (it pins an intermediate, not a behaviour)")
    # A `--ids` run cannot judge coverage: the never-killed lists are then just
    # "everything the selected mutations happen not to touch".  Blind spots,
    # crashes and over-specified equivalent mutations ARE still judgeable.
    partial = bool(sel)
    if partial:
        print("\n  NOTE: --ids restricts the catalogue, so the never-killed lists above are\n"
              "        an artefact of the restriction and are NOT counted in the verdict.")
    bad = bool(blind or crashed or bad_equiv or (not partial and (never_o or never_c)))
    print(f"\nVERDICT: {'FAIL' if bad else 'PASS'}"
          + ("  (partial run: coverage not judged)" if partial else ""))
    print("=" * 78)
    json.dump(dict(mutations=results, killers=killers,
                   never_killed=never_o, never_killed_conjuncts=never_c,
                   exempt_conjuncts={c: exempt_reason(c) for c in exempted},
                   blind_spots=[b["id"] for b in blind],
                   crashed=[c["id"] for c in crashed],
                   all_ids=all_ids, obligation_ids=obl_ids, conjunct_ids=conj_ids),
              open(args.out, "w"), indent=1)
    return 4 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
