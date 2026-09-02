#!/usr/bin/env python3
# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
"""
kernel_obligations.py — machine-checked obligations for the arithmetic in the
optimized kernels in src/Decode.sol.

formal/z3/verify_all.py covers every invariant the SHIPPED kernels rely on;
three pieces of kernel-specific arithmetic each get their own obligation here
rather than being assumed:

  O1..O6  useHintSwar   — SWAR UseHint + w1Encode (division-by-multiplication,
                          the add/shift comparators, the multiply-gather, and
                          the end-to-end equivalence with FIPS 204 UseHint)
  O7..O8  matvecRow     — pre-shifted lane masks and the lazy accumulator
                          bound, restated for this expression form
  O9      unpackZPacked — the packed store is a disjoint OR of canonical lanes
  O10     unpackZPacked — the 18-bit field extraction (twelve disjoint byte terms
                          and one mask) is FIPS 204 BitUnpack

Same conventions as formal/z3/verify_all.py:
  [SMT]  Z3 proves a universally quantified statement (negation UNSAT)
  [EXH]  complete enumeration of a finite domain
  [CALC] a closed-form numeric fact in exact Python integers

Run through formal/z3/verify_all.py (the suite executes this module).
Exit code 0 iff every obligation PASSes.
"""
import os
import sys
import time

sys.dont_write_bytecode = True
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"

Q = 8380417
GAMMA2 = 95232
D2G = 190464  # 2 * gamma2
KQ28 = Q << 28
ZMAX = 17 * Q - 1          # LAZY forward-NTT lane ceiling (C9a/C9f)
M64 = (1 << 64) - 1
M256 = (1 << 256) - 1

# --- kernel constants, copied from src/Decode.sol --------------------------
# THE MODELLING HAZARD.  A model of `useHintSwar` can silently describe a kernel
# THAT NO LONGER EXISTS.  An older shape of this kernel reduced TWICE (an
# intermediate `R1 = S1 mod 44`, then `S = (R1 + ADJ) mod 44`), both times
# through a conditional subtract selected by bit 32 of `x + SW_K3244`.  The
# shipped kernel instead folds the two into ONE reduction and evaluates it with
# a MAGIC DIVISION -- `S - 44*((S*SW_M44) >> 12)`.  Modelling the old shape
# leaves `SW_K3244` occurring nowhere in the repository except here, makes three
# O3 conjuncts (the K = 44 comparator) prove something the kernel does not do,
# and puts O2/O4's `s <= 86` premise one short of the shipped reachable maximum
# T = S1 + ADJ = 87.  The model below is the shipped one, opcode for opcode; O6
# re-checks it against the FIPS 204 reference over the COMPLETE domain, which is
# what makes a modelling error a FAILURE rather than a different green number.
# The VALUES themselves are cross-checked against the shipped source by
# obligation C18, so an edit to Decode.sol that moves one of them fails there
# rather than silently re-basing this model.
#
# THE EXTRACTION GAP.  A whole-file digest is not a NAMED conjunct, and the
# difference matters.  src/Decode.sol declares 24 file-scope constants; a C18
# table naming only 18 leaves `MV_M32`, `MV_L0..MV_L3` and `MV_KQ28REP` -- the
# pre-shifted lane masks O7 models and the q*2^28 offset O8's `ACC_ENTRY` is
# built from -- named by NO conjunct, and leaves the `shr(39, ...)` of the magic
# division below unnamed as well.  With that gap open,
# `MV_KQ28REP := rep(Q << 29, 4, 64)` (still 0 mod q, still four equal lanes)
# fails EXACTLY ONE conjunct, C18's whole-file digest, while every value
# conjunct, O7, O8, C9g, S14 and every hypotheses.py row stays green.  All seven
# are therefore extracted (`C18.dec_MV_*`,
# `C18.dec_swar_magic_shift_is_39`), so a moved value fails a NAMED conjunct and
# not only a digest.
#
# WHAT C18 STILL DOES NOT COVER, so the boundary is on the record: `SW_T_MAX`
# below is not a source constant at all -- it is the reachable maximum of
# T = S1 + ADJ, a fact about the kernel's DYNAMICS, discharged by O2/O4/O6 over
# the complete domain rather than by extraction.  The end-to-end behaviour of
# the matvec constants is covered semantically by
# `test/Kernels.t.sol::test_kernel_51_matvecRow_worstcase`, which runs the
# shipped `matvecRow` against a per-lane reference at O8's worst admissible
# input and is what caught the `MV_KQ28REP` mutation by name.
SW_MDIV = 2886403
SW_SHIFT = 39
SW_M44 = 94                # ceil(2^12 / 44) -- the magic multiplier
SW_M44_SHIFT = 12          # ... and its shift
SW_T_MAX = 87              # max reachable T = S1 (<= 44) + ADJ (<= 43)
SW_REP1 = 0x0000000000000001000000000000000100000000000000010000000000000001
SW_REP6 = 0x000000000000003F000000000000003F000000000000003F000000000000003F
SW_K32G2 = 0x00000000FFFE8BFF00000000FFFE8BFF00000000FFFE8BFF00000000FFFE8BFF
SW_K321 = 0x00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF
SW_GATHERK = 0x0000000000000000000040000000000000100000000000000400000000000001
MV_KQ28REP = 0x0007FE00100000000007FE00100000000007FE00100000000007FE0010000000

# The pk-coefficient ceiling, made an EXPLICIT parameter rather than an implicit
# literal.  O7/O8 are stated over products of a CACHED pk coefficient and
# a lazy forward-NTT lane; "the cached coefficient is canonical" was carried
# inside a literal `Q - 1` rather than stated, and it is not free -- a
# congruent-but-lifted blob passes every on-chain check and lands outside every
# bound proved here.  `ctl_amax_*` is the discrimination control.
PK_AMAX = Q

results = []
conjuncts = []


def _truth(x):
    """The canonical truth value of a claim.  NOT `bool` — see verify_all._truth.

    `bool` is an ordinary global NAME and a parameter default on a recorder's
    own `def` line can shadow it, making a row print [FAIL] while the tally
    counts it as a PASS.
    """
    return True if x else False


def record(oid, kind, desc, ok, detail="", parts=None):
    """Same contract as formal/z3/verify_all.py:record (which rebinds this).

    HARDENING NOTE: `parts` carries the obligation's individual conjuncts so the vacuity
    audit can aggregate PER CONJUNCT instead of per obligation ID.
    HARDENING NOTE: the printed verdict IS the stored verdict, and truth goes through
    `_truth` rather than the shadowable builtin name `bool`.
    """
    parts = list(parts or ())
    results.append((oid, kind, desc,
                    _truth(ok) and all(_truth(p[1]) for p in parts), detail))
    print(f"[{'PASS' if results[-1][3] else 'FAIL'}] {oid:<5} {kind:<5} {desc}"
          + (f"  — {detail}" if detail else ""))
    for name, pok in parts:
        conjuncts.append((f"{oid}.{name}", _truth(pok)))
        print(f"[{'PASS' if conjuncts[-1][1] else 'FAIL'}] {conjuncts[-1][0]}")
    return results[-1][3]


def controls(pred, accept=(), reject=(), label="ctl"):
    """Positive/negative controls for a claim stated as a unary predicate.

    Identical contract to formal/z3/verify_all.py:controls.
    An obligation rewritten to a tautology accepts its negative controls and
    fails; one rewritten to a contradiction rejects its positive controls.
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

    Same contract as formal/z3/verify_all.py:pinned.  Routing the VERDICT and the
    CONTROLS through one callable is the whole point: controls attached to a
    predicate the obligation does not actually evaluate prove nothing about it.
    """
    return record(oid, kind, desc, _truth(pred(subject)), detail,
                  parts=list(parts) + controls(pred, accept, reject))


try:
    from z3 import Int, If, Solver, And, Or, Not, Implies, sat, unsat, ForAll  # noqa: F401

    HAVE_Z3 = True
except Exception:
    HAVE_Z3 = False
    print("!! z3 not importable — SMT obligations will be SKIPPED")

# PER-SOLVER-CALL BUDGET, and `unknown` is NOT a proof.  A `_prem_sat` or
# `_refutable` that returns `s.check() != unsat` lets a solver that timed out or
# gave up -- `unknown` -- score as a PASS on the two guards whose whole job is
# to say "this proof is not free".  And with no timeout set, a mutated suite can
# sit indefinitely instead of reporting, which is a hang rather than a verdict.
# Both therefore demand `== sat`, and every call carries the same budget
# verify_all.py's `prove()` uses.  Three orders of magnitude of headroom: every
# call here discharges in milliseconds.
SMT_TIMEOUT_MS = int(os.environ.get("MLDSA_SMT_TIMEOUT_MS", "20000"))


def _solver(prem, extra=None):
    """A budgeted solver over `prem` (+ `extra`).  Never unbounded."""
    s = Solver()
    s.set("timeout", SMT_TIMEOUT_MS)
    for p in prem:
        s.add(p)
    if extra is not None:
        s.add(extra)
    return s


def _prem_sat(prem):
    """The classical vacuity guard, in ONE place for all of O3/O4/O7.

    Open-coding it three times would mean no single mutation can falsify
    every `premises_sat` conjunct, so all 24 of them across the suite would
    have to be EXEMPTED from the vacuity audit by a suffix rule -- which would
    also make any NEW conjunct whose name ends in `premises_sat` exempt by name
    alone.  With the check funnelled through one helper here and through
    `prove()` in verify_all.py, mutation V148 (contradictory premises
    everywhere) falsifies all of them at once and the exemption list is empty.

    The verdict is `== sat`: `!= unsat` would count `unknown`
    -- a solver that gave up -- as evidence that the premises are satisfiable.
    """
    return _solver(prem).check() == sat


def _refutable(prem, negated_claim):
    """The DUAL guard: `prem + negated_claim` must be SAT.

    A control of the form "the same encoding at the wrong constant is still
    refutable" is only evidence if it can come out false, so all of O3/O4/O7's
    controls go through this one helper -- mutation VT09 makes its premise set
    contradictory and falsifies every one of them at once.  Built inline, it
    would instead leave nine such conjuncts unreachable by any mutation in the
    catalogue.

    `== sat`, and budgeted, for the same reason as above.
    """
    return _solver(prem, negated_claim).check() == sat


# ---------------------------------------------------------------- reference
def decompose(r):
    """FIPS 204 Algorithm 36 Decompose, gamma2 = 95232."""
    rp = r % Q
    r0 = rp % D2G
    if r0 > GAMMA2:
        r0 -= D2G
    if rp - r0 == Q - 1:
        return 0, r0 - 1
    return (rp - r0) // D2G, r0


def use_hint(h, r):
    """FIPS 204 Algorithm 40 UseHint."""
    r1, r0 = decompose(r)
    if h == 1:
        return (r1 + 1) % 44 if r0 > 0 else (r1 - 1) % 44
    return r1


# ------------------------------------------------- the kernel, bit-for-bit
def swar_word(rs, hs):
    """Exact 256-bit model of the SHIPPED useHintSwar inner loop body.

    Opcode for opcode with src/Decode.sol:

        Q0  := and(shr(39, mul(W, SW_MDIV)), SW_REP6)
        R0  := sub(W, mul(Q0, SW_D))
        C   := and(shr(32, add(R0, SW_K32G2)), SW_REP1)
        NEG := or(and(not(shr(32, add(R0, SW_K321))), SW_REP1), C)
        ADJ := and(add(SW_REP1, mul(NEG, 42)), tbl[h & 15])
        S   := add(add(Q0, C), ADJ)                       -- T, <= 87
        S   := sub(S, mul(and(shr(12, mul(S, SW_M44)), SW_REP1), 44))
        L   := and(shr(174, mul(S, SW_GATHERK)), 0xffffff)

    ONE reduction, by magic division -- not the two conditional subtracts of the
    older kernel shape (see the modelling hazard above).
    """
    W = rs[0] | (rs[1] << 64) | (rs[2] << 128) | (rs[3] << 192)
    HB = 0
    for k in range(4):
        if hs[k]:
            HB |= M64 << (64 * k)
    Q0 = (((W * SW_MDIV) & M256) >> SW_SHIFT) & SW_REP6
    R0 = (W - ((Q0 * D2G) & M256)) & M256
    C = ((((R0 + SW_K32G2) & M256) >> 32) & SW_REP1)
    NZ = (~((((R0 + SW_K321) & M256) >> 32))) & M256          # EVM `not`
    NEG = (NZ & SW_REP1) | C
    ADJ = ((SW_REP1 + ((NEG * 42) & M256)) & M256) & HB
    S = (Q0 + C + ADJ) & M256
    S = (S - (((((S * SW_M44) & M256) >> SW_M44_SHIFT) & SW_REP1) * 44)) & M256
    return (((S * SW_GATHERK) & M256) >> 174) & 0xFFFFFF


# =========================================================== O1 .. O6 (SWAR)
def _swar_div_exact(param):
    """(mdiv, shift) reproduces floor(r / 2*gamma2) on the whole domain."""
    mdiv, shift = param
    for r in range(Q):
        if (r * mdiv) >> shift != r // D2G:
            return False
    return True


def o1_division_constant():
    # The VERDICT and the CONTROLS must be the same callable, or the controls are
    # decoration: computing the verdict with an inline loop while pinning
    # `_swar_div_exact` separately means rewriting the verdict to `True` fails no
    # control at all.  Both therefore go through `pinned`, so a rewritten verdict
    # is a rewritten control and the controls cannot come out free.
    return pinned(
        "O1", "EXH",
        "SWAR div: (r*2886403)>>39 == floor(r/2*gamma2) for EVERY r < q",
        _swar_div_exact, (SW_MDIV, SW_SHIFT),
        "checked all 8380417 values",
        reject=[(SW_MDIV + 1, SW_SHIFT), (SW_MDIV - 1, SW_SHIFT),
                (SW_MDIV, SW_SHIFT + 1), (SW_MDIV, SW_SHIFT - 1)],
    )


def o2_no_cross_lane_carry():
    # HARDENING NOTE: ONE predicate per bound, used both for the conjunct and for its
    # controls, so a widened bound fails a control instead of passing quietly.
    def fits_lane(x):
        return x < (1 << 64)

    def fits_word(x):
        return x < (1 << 256)

    maxprod = (Q - 1) * SW_MDIV
    ok1 = fits_lane(maxprod)
    # Q0*D2G: Q0 is masked to 6 bits, so <= 63
    ok2 = fits_lane(63 * D2G)
    # the comparator addends never leave the lane.  NOTE: `86 + 2^32` is the
    # reachable maximum of a kernel that reduces TWICE; the shipped kernel
    # reduces ONCE and its T reaches 87.  The magic-division product T*94 is the
    # other lane-local quantity here.
    ok3 = (fits_lane((D2G - 1) + (1 << 32))
           and fits_lane(SW_T_MAX + (1 << 32))
           and fits_lane(SW_T_MAX * SW_M44))
    # HB * lane mask: the top lane's contribution stays inside 256 bits
    ok4 = fits_word(M64 << 192)
    return record(
        "O2", "CALC",
        "useHintSwar: no lane can carry into its neighbour",
        True,
        f"max lane product r*MDIV = {maxprod} = 2^{maxprod.bit_length() - 1}.x < 2^64; "
        f"mod-44 magic product T*{SW_M44} <= {SW_T_MAX * SW_M44} < 2^64",
        parts=[("div_product_fits_lane", ok1), ("quotient_product_fits_lane", ok2),
               ("comparator_addends_fit_lane", ok3), ("top_lane_fits_word", ok4)]
        + controls(fits_lane, label="ctl_lane64",
                   accept=[0, (1 << 64) - 1], reject=[1 << 64, (1 << 64) + 1])
        + controls(fits_word, label="ctl_word256",
                   accept=[0, (1 << 256) - 1], reject=[1 << 256, (1 << 256) + 1]),
    )


def o3_ge_comparator():
    if not HAVE_Z3:
        return record("O3", "SMT", "SWAR >= comparator", False, "z3 unavailable — install z3-solver")
    parts = []
    # A K = 44 instance here would be DEAD: it models the conditional subtract
    # of a useHintSwar that reduces twice, whereas the shipped kernel reduces
    # once, by magic division (O4).  The two comparators the shipped kernel
    # really evaluates are K = gamma2 + 1 (the `C` flag, `add(R0, SW_K32G2)`)
    # and K = 1 (the `NEG` flag's [R0 != 0] half, `add(R0, SW_K321)`), both on
    # an 18-bit R0.
    for width, K in ((18, GAMMA2 + 1), (18, 1)):
        x = Int("x")
        prem = [x >= 0, x < (1 << width)]
        # bit 32 of (x + 2^32 - K) is set  <=>  x >= K
        v = x + (1 << 32) - K
        bit32 = (v / (1 << 32)) % 2
        s = _solver(prem, Not(bit32 == If(x >= K, 1, 0)))
        parts.append((f"K{K}_premises_sat", _prem_sat(prem)))
        parts.append((f"K{K}_comparator_iff", s.check() == unsat))
        # HARDENING NOTE: control: the comparator claim must be FALSIFIABLE at the wrong
        # bit position, so `s.check() == unsat` cannot be a free unsat.
        parts.append((f"K{K}_ctl_wrong_bit_is_refutable",
                      _refutable(prem, Not((x + (1 << 32) - K) / (1 << 31) % 2
                                           == If(x >= K, 1, 0)))))
    return record(
        "O3", "SMT",
        "add/shift comparator: bit32(x + 2^32 - K) == [x >= K] for every in-range x",
        True,
        "unsat (proved) for K in {gamma2+1, 1} — the two comparators the SHIPPED "
        "kernel evaluates (the K = 44 instance modelled a reduction that is gone)",
        parts=parts,
    )


def o4_mod44():
    if not HAVE_Z3:
        return record("O4", "SMT", "SWAR mod 44", False, "z3 unavailable — install z3-solver")
    # Modelling a CONDITIONAL SUBTRACT (`s - 44*[s >= 44]`) selected by bit 32
    # of `s + SW_K3244`, over `s <= 86`, would describe a kernel the shipped one
    # is not: the shipped kernel folds FIPS 204's two reductions into ONE and
    # evaluates it by MAGIC DIVISION, `S - 44*((S*SW_M44) >> 12)`, over
    # T = S1 + ADJ <= 87.  With both the operation and the bound wrong here,
    # `SW_M44 94 -> 93` in Decode.sol would leave this obligation green.  It
    # is therefore stated over the shipped form; the shipped CONSTANTS are
    # cross-checked against the source by C18 and the magic division's exactness
    # by C17.
    s = Int("s")
    prem = [s >= 0, s <= SW_T_MAX]      # S1 <= 44 and ADJ <= 43
    magic = s - 44 * ((s * SW_M44) / (1 << SW_M44_SHIFT))
    sol = _solver(prem, Not(magic == s % 44))
    return record(
        "O4", "SMT",
        "the ONE magic-division reduction == mod 44 for every reachable T "
        "(T = S1 + ADJ <= 87)",
        True, "unsat (proved)",
        parts=[("premises_sat", _prem_sat(prem)),
               ("magic_division_is_mod44", sol.check() == unsat),
               # the quotient must fit the REP1 mask the kernel ANDs it with,
               # or the subtrahend spills into the next SWAR lane
               ("quotient_fits_the_rep1_mask",
                all(((t * SW_M44) >> SW_M44_SHIFT) <= 1 for t in range(SW_T_MAX + 1))),
               # HARDENING NOTE: controls: the SAME encoding at the wrong magic
               # constant, at the wrong shift and at the wrong subtrahend must
               # each be SAT, so the unsat above is not a theorem of the
               # background theory; and the premise T <= 87 is what makes ONE
               # reduction enough (the magic division first fails at T = 131).
               ("ctl_wrong_magic_is_refutable",
                _refutable(prem, Not(s - 44 * ((s * (SW_M44 - 1)) / (1 << SW_M44_SHIFT))
                                     == s % 44))),
               ("ctl_wrong_shift_is_refutable",
                _refutable(prem, Not(s - 44 * ((s * SW_M44) / (1 << (SW_M44_SHIFT - 1)))
                                     == s % 44))),
               ("ctl_wrong_subtrahend_is_refutable",
                _refutable(prem, Not(s - 43 * ((s * SW_M44) / (1 << SW_M44_SHIFT))
                                     == s % 44))),
               ("ctl_bound_premise_is_load_bearing",
                _refutable([s >= 0], Not(magic == s % 44)))],
    )


def o5_multiply_gather():
    """One MUL replaces 4 extracts + 3 SHL + 3 OR. Complete enumeration over the
    reachable domain: each lane is a UseHint output, so 0 <= a_k < 44; the 6-bit
    field width is checked over the full 0..63 range as well."""
    # HARDENING NOTE: the COMPLETE sweep is a function of the gather constant, so the
    # verdict and the controls are the same callable (see O1).  A wrong K fails
    # within the first few tuples, so the four controls cost nothing.
    def gather_packs_four_fields(K):
        rng = list(range(64))
        for a0 in rng:
            for a1 in rng:
                for a2 in rng:
                    for a3 in rng:
                        R = a0 | (a1 << 64) | (a2 << 128) | (a3 << 192)
                        if (((R * K) & M256) >> 174) & 0xFFFFFF != \
                                (a0 | (a1 << 6) | (a2 << 12) | (a3 << 18)):
                            return False
        return True

    return pinned(
        "O5", "EXH",
        "multiply-gather: (lanes * K)>>174 packs four 6-bit fields, K = 2^174+2^116+2^58+1",
        gather_packs_four_fields, SW_GATHERK,
        "all 64^4 = 16,777,216 lane tuples",
        reject=[SW_GATHERK + 1, SW_GATHERK - 1, 0, 1, SW_GATHERK << 1],
    )


def o6_usehint_equivalence():
    # HARDENING NOTE: both sweeps are functions of the SWAR kernel, so the verdicts and
    # the controls are the same callables (see O1).  A broken kernel mismatches
    # within the first few r, so the three controls cost nothing.
    import itertools
    import random

    corner = [0, 1, GAMMA2, GAMMA2 + 1, D2G - 1, D2G, 8285184, 8285185, Q - 2, Q - 1]

    def uniform_lanes_match_fips(kern):
        for r in range(Q):
            for h in (0, 1):
                w = use_hint(h, r)
                if kern([r, r, r, r], [h, h, h, h]) != (w | (w << 6) | (w << 12) | (w << 18)):
                    return False
        return True

    def mixed_lanes_match_fips(kern):
        for rs in itertools.product(corner, repeat=4):
            for hp in range(16):
                hs = [(hp >> k) & 1 for k in range(4)]
                want = 0
                for k in range(4):
                    want |= use_hint(hs[k], rs[k]) << (6 * k)
                if kern(list(rs), hs) != want:
                    return False
        rng = random.Random(20260809)
        for _ in range(200000):
            rs = [rng.randrange(Q) for _ in range(4)]
            hs = [rng.randrange(2) for _ in range(4)]
            want = 0
            for k in range(4):
                want |= use_hint(hs[k], rs[k]) << (6 * k)
            if kern(rs, hs) != want:
                return False
        return True

    broken = [lambda rs, hs: (swar_word(rs, hs) + 1) & 0xFFFFFF,
              lambda rs, hs: swar_word(rs, [0, 0, 0, 0]),
              lambda rs, hs: 0]
    ok_uniform = uniform_lanes_match_fips(swar_word)
    ok_mixed = mixed_lanes_match_fips(swar_word)
    return record(
        "O6", "EXH",
        "useHintSwar == FIPS 204 UseHint+w1Encode on the COMPLETE r domain",
        True,
        f"{2 * Q} uniform-lane cases + {10 ** 4 * 16 + 200000} mixed-lane cases, "
        f"{'0 mismatches' if ok_uniform and ok_mixed else 'MISMATCHES'}",
        parts=[("uniform_lanes", ok_uniform), ("mixed_lanes", ok_mixed)]
        + controls(uniform_lanes_match_fips, label="ctl_uniform", reject=broken)
        + controls(mixed_lanes_match_fips, label="ctl_mixed", reject=broken),
    )


# ============================================================ O7 .. O8 (matvec)
def o7_preshifted_lane_product():
    if not HAVE_Z3:
        return record("O7", "SMT", "pre-shifted lane product", False, "z3 unavailable — install z3-solver")
    a = Int("a")
    z = Int("z")
    # `a` is a canonical pk coefficient (Ahat / t1hat, < q); `z` is a LAZY
    # forward-NTT lane (zHat / cHat), <= ZMAX = 17q-1 (C9a/C9f) — the forward
    # transform no longer canonicalises its output.
    prem = [a >= 0, a < PK_AMAX, z >= 0, z <= ZMAX]
    parts = [("premises_sat", _prem_sat(prem)),
             # the premise itself, STATED rather than left implicit:
             # `a < q` is a property of a CANONICAL pk blob, not of every blob
             # the on-chain checks accept
             ("pk_coefficient_ceiling_is_q", PK_AMAX == Q)]
    # HARDENING NOTE: `a * (z * 2^(64k)) == (a*z) * 2^(64k)` is associativity over
    # unbounded Int -- a tautology, and so is dividing it back out.  What the
    # kernel needs is that the lane-k product occupies EXACTLY bits
    # [64k, 64k+64): it must not spill into lane k+1, and the top lane must not
    # leave the 256-bit word.
    for k in range(4):
        s = _solver(prem,
                    Not(And(a * z < (1 << 64),                              # fits one lane
                            (a * z) * (1 << (64 * k)) < (1 << (64 * (k + 1))),  # no spill up
                            (a * z) * (1 << (64 * k)) < (1 << 256))))       # inside the word
        parts.append((f"lane{k}_no_spill", s.check() == unsat))
        # HARDENING NOTE: control: with the canonicality premise on `a` dropped the same
        # claim is SAT, so the unsat above is not free.
        parts.append((f"lane{k}_ctl_premise_is_load_bearing",
                      _refutable([a >= 0, z >= 0, z <= ZMAX],
                                 Not(And(a * z < (1 << 64),
                                         (a * z) * (1 << (64 * k)) < (1 << (64 * (k + 1))),
                                         (a * z) * (1 << (64 * k)) < (1 << 256))))))
        # ... and the DISCRIMINATION CONTROL that names O7's OWN cliff.  Lane
        # locality here survives a lifted pk by a wide margin -- a*z leaves a
        # 64-bit lane only past a ~ 2^64/ZMAX ~ 15,455q -- so this control is
        # stated at 2^40, where the claim really is refutable.  The ceiling that
        # a lifted blob DOES break is the entry fold's, at 2q, and it is
        # asserted where it belongs: O8.ctl_amax_rejects_* and
        # C9g.ctl_pk_canonical_premise_rejects_*.  Naming the wrong cliff here
        # would be a control that cannot come out false, which is the failure
        # mode this whole apparatus exists to refuse.
        parts.append((f"lane{k}_ctl_lane_locality_needs_a_ceiling",
                      _refutable([a >= 0, a < (1 << 40), z >= 0, z <= ZMAX],
                                 Not(And(a * z < (1 << 64),
                                         (a * z) * (1 << (64 * k)) < (1 << (64 * (k + 1))),
                                         (a * z) * (1 << (64 * k)) < (1 << 256))))))
    # and the top lane never overflows the 256-bit word (HARDENING NOTE: one predicate
    # for the conjunct and its controls, see O1)
    def fits_word(x):
        return x < (1 << 256)
    parts.append(("top_lane_fits_word", fits_word((PK_AMAX - 1) * ZMAX * (1 << 192))))
    parts += controls(fits_word, label="ctl_word256",
                      accept=[0, (1 << 256) - 1], reject=[1 << 256, 1 << 300])
    return record(
        "O7", "SMT",
        "macCompactPre/matvecRow: mul(a_k, wz & L_k) is the lane-k product (z <= 17q-1), no overlap",
        True,
        f"unsat (proved); top-lane product < 2^{((Q - 1) * ZMAX << 192).bit_length()}  < 2^256",
        parts=parts,
    )


def o8_accumulator_bounds():
    # HARDENING NOTE: each conjunct and its controls share one predicate (see O1).
    # The z/c lanes are the LAZY forward-NTT outputs (<= ZMAX = 17q-1, C9a/C9f);
    # the lane ceiling 4(q-1)(17q-1) + q*2^28 is EXACTLY the ACC_ENTRY the
    # inverse NTT's entry fold is verified over (C9g/S14): O8 is the producer
    # side of that contract, C9g/S14 the consumer side.
    def lane_fits_53(x):
        return x < (1 << 53)

    def is_multiple_of_q(x):
        return x % Q == 0

    def offset_exceeds(pair):
        return pair[0] > pair[1]

    def rep_is_four_lanes(w):
        return w == sum((Q << 28) << (64 * k) for k in range(4))

    def dominated_by_entry_offset(pair):
        return pair[0] <= pair[1]

    # THE PK-COEFFICIENT CEILING, PARAMETERISED.  Writing `lane_max` with a
    # literal `Q - 1` carries "the cached pk coefficients are CANONICAL" inside
    # the arithmetic instead of stating it, which is why `PK_AMAX` is an
    # explicit parameter here.  The margin between `lane_max` and the inverse
    # NTT's ACCQ30 entry offset is 1.28x and it exists ONLY because a < q; past
    # the offset the entry fold's EVM subtraction wraps out of the residue class
    # while still emitting canonical-looking lanes, so a lifted blob makes a
    # VALID signature reject and nothing downstream can see why.
    def entry_offset_dominates(amax):
        return 4 * (amax - 1) * ZMAX + KQ28 <= (Q << 30)

    prod = (PK_AMAX - 1) * ZMAX
    lane_max = 4 * prod + KQ28
    # every (KQ28 - c*t1) lane stays non-negative -> no borrow
    ok_nonneg = offset_exceeds((KQ28, prod))
    ok_bound = lane_fits_53(lane_max)
    ok_mod = is_multiple_of_q(KQ28)  # the offset must not change the residue class
    ok_rep = rep_is_four_lanes(MV_KQ28REP)
    # ... and the ceiling is dominated by the inverse NTT's ACCQ30 entry offset
    ok_entry = dominated_by_entry_offset((lane_max, Q << 30))
    return record(
        "O8", "CALC",
        "matvecRow lazy accumulator: lanes < 2^53, KQ28 > (q-1)(17q-1), KQ28 == 0 mod q, "
        "lane_max <= ACCQ30 (the inverse NTT's S14 entry offset)",
        True,
        f"max lane = {lane_max} = 2^{lane_max.bit_length() - 1}.x, KQ28 = {KQ28}",
        parts=[("offset_prevents_borrow", ok_nonneg), ("lane_bound", ok_bound),
               ("offset_preserves_residue", ok_mod), ("replicated_constant_exact", ok_rep),
               ("entry_offset_dominates_lane_max", ok_entry)]
        + controls(lane_fits_53, label="ctl_lane53",
                   accept=[0, (1 << 53) - 1], reject=[1 << 53, 1 << 54])
        + controls(is_multiple_of_q, label="ctl_residue",
                   accept=[0, Q, 2 * Q, KQ28], reject=[1, Q - 1, Q + 1])
        + controls(offset_exceeds, label="ctl_borrow",
                   accept=[(2, 1), (KQ28, 0)], reject=[(1, 2), (1, 1), (0, KQ28)])
        + controls(rep_is_four_lanes,
                   label="ctl_rep", accept=[MV_KQ28REP],
                   reject=[0, MV_KQ28REP + 1,
                           sum((Q << 28) << (64 * k) for k in range(3))])
        + controls(dominated_by_entry_offset, label="ctl_entry",
                   accept=[(0, 1), (Q << 30, Q << 30)],
                   reject=[((Q << 30) + 1, Q << 30), (1, 0)])
        # THE DISCRIMINATION CONTROL for the canonicality premise: the entry
        # offset dominates at a < q and FAILS at a < 2q.  That converts "pk
        # coefficients are canonical" from an unstated assumption carried by a
        # `Q - 1` into a falsifiable conjunct, and names the exact ceiling.
        + [("pk_coefficient_ceiling_is_q", PK_AMAX == Q)]
        + controls(entry_offset_dominates, label="ctl_amax",
                   accept=[PK_AMAX, PK_AMAX - 1, 1],
                   reject=[2 * PK_AMAX, 4 * PK_AMAX, 1 << 32]),
    )


# ============================================================ O9 (unpackZ)
def _lanes_roundtrip(stride):
    """Four canonical lanes packed at `stride` bits round-trip through the OR.

    Control target: 64 must work, and every narrower stride must not --
    that is the whole content of `lane_roundtrip_exact`.
    """
    for combo in ((0, 0, 0, 0), (Q - 1, Q - 1, Q - 1, Q - 1), (0, Q - 1, 1, Q - 2)):
        w = 0
        for k in range(4):
            w |= combo[k] << (stride * k)
        for k in range(4):
            if (w >> (stride * k)) & M64 != combo[k]:
                return False
    return True


def o9_packed_store_disjoint():
    """unpackZPacked ORs four canonical coefficients into one word.  Every
    coefficient is mod(8511489 - v, q) < q < 2^23, so the four 64-bit lanes are
    disjoint and the OR equals the intended packing — exactly the layout
    packFromFlat produced.  Checked over the COMPLETE 18-bit field domain."""
    # HARDENING NOTE: each conjunct and its controls share one predicate (see O1).
    def is_canonical(c):
        return 0 <= c < Q

    def fits_23_bits(x):
        return x < (1 << 23)

    canon = all(is_canonical((8511489 - v) % Q) for v in range(1 << 18))
    rt = _lanes_roundtrip(64)
    return record(
        "O9", "EXH",
        "unpackZPacked: 4 canonical lanes (< q < 2^23) OR into one word without overlap",
        True,
        "all 2^18 field values map into [0,q); lane round-trip exact",
        parts=[("all_fields_canonical", canon), ("lane_roundtrip_exact", rt),
               ("canonical_lane_fits_23_bits", fits_23_bits(Q))]
        + controls(is_canonical, label="ctl_canon",
                   accept=[0, 1, Q - 1], reject=[-1, Q, Q + 1, 1 << 23])
        + controls(fits_23_bits, label="ctl_23bit",
                   accept=[0, (1 << 23) - 1], reject=[1 << 23, 1 << 24])
        + controls(_lanes_roundtrip, label="ctl_stride",
                   accept=[64, 65, 128], reject=[60, 63, 23, 22]),
    )


# ====================================================== O10 (unpackZ extract)
# The four 18-bit fields of a 9-byte group are assembled by TWELVE byte terms
# placed with pure LEFT shifts and ONE 18-bit-per-lane mask:
#
#   V := and(  byte(0,w)      | byte(1,w)<<8   | byte(2,w)<<16  | byte(2,w)<<62
#            | byte(3,w)<<70  | byte(4,w)<<78  | byte(4,w)<<124 | byte(5,w)<<132
#            | byte(6,w)<<140 | byte(6,w)<<186 | byte(7,w)<<194 | byte(8,w)<<202,
#            Z_M18)
#
# The three bytes that straddle a field boundary (2, 4, 6) appear TWICE, and the
# bits each copy contributes outside its lane's 18-bit field -- b2's low 2 bits
# at 62..63, b4's low 4 at 124..127, b6's low 6 at 186..191, and the high spill
# of the in-lane copies -- are discarded by the single mask.  That is what
# replaces the per-field `and(byte(k,w), 3|15|63)` + `shr` of the previous form.
Z_TERMS = ((0, 0), (1, 8), (2, 16), (2, 62), (3, 70), (4, 78),
           (4, 124), (5, 132), (6, 140), (6, 186), (7, 194), (8, 202))
Z_M18_DEC = 0x000000000003ffff000000000003ffff000000000003ffff000000000003ffff

# The three DOUBLED bytes are emitted by ONE multiply each instead of two shifts
# and an OR: for b < 2^8 the two shifted copies occupy disjoint bit ranges (the
# shifts are 46 apart, far more than the 8 bits a byte spans), so
#
#     b * (2^s + 2^t)  ==  or(shl(s, b), shl(t, b))       exactly, for all b < 256
#
# and the twelve-term model above is UNCHANGED -- the multiply is a different
# way to emit the same two terms, not a different term set.  The pairs, the
# constants and that identity are all pinned below; `_mul_pairs_are_the_doubled
# _terms` is what ties the constants back to Z_TERMS, so a constant that encoded
# some OTHER pair of shifts could not pass by agreeing with itself.
Z_MUL_PAIRS = ((2, 16, 62, 0x4000000000010000),
               (4, 78, 124, 0x10000000000040000000000000000000),
               (6, 140, 186, 0x40000000000100000000000000000000000000000000000))


def _terms_disjoint(terms):
    """the twelve byte terms occupy pairwise DISJOINT bit ranges.

    This is the whole content of "the OR is a sum": two terms sharing a bit
    would make the OR lose information (and an ADD carry into the next field).
    """
    occ = 0
    for _i, sh in terms:
        m = 0xFF << sh
        if occ & m:
            return False
        occ |= m
    return True


def _terms_inside_the_word(terms):
    """no term reaches bit 256 (the top one ends at bit 209)"""
    return all(sh + 8 <= 256 for _i, sh in terms)


def _fused_constants_are_the_two_powers(pairs):
    """each fused constant is EXACTLY 2^s + 2^t for its pair's two shifts"""
    return all(c == (1 << s) + (1 << t) for _i, s, t, c in pairs)


def _fused_multiply_is_the_two_terms(pairs):
    """EXHAUSTIVE over the byte domain: the multiply equals the OR of the two
    shifted copies for every one of the 256 values a byte can take."""
    for _i, s, t, c in pairs:
        for b in range(256):
            if b * c != ((b << s) | (b << t)):
                return False
    return True


def _mul_pairs_are_the_doubled_terms(pairs, terms=Z_TERMS):
    """the fused pairs are exactly the bytes that occur TWICE in Z_TERMS, with
    exactly those two shifts -- so the multiplies cannot cover a term set other
    than the one the sweep below proves equal to FIPS BitUnpack"""
    doubled = {}
    for i, sh in terms:
        doubled.setdefault(i, []).append(sh)
    twice = {i: sorted(v) for i, v in doubled.items() if len(v) == 2}
    return twice == {i: sorted((s, t)) for i, s, t, _c in pairs}


def _extract_shipped(b, terms=Z_TERMS, mask=Z_M18_DEC):
    """the shipped kernel's extraction, as four lane values"""
    d = 0
    for i, sh in terms:
        d |= b[i] << sh
    v = d & mask
    return [(v >> (64 * k)) & M64 for k in range(4)]


def _extract_fips(b):
    """FIPS 204 BitUnpack on the same 9 bytes: an LSB-first bitstream cut into
    four 18-bit fields.  Written from the SPEC, not transcribed from the Yul the
    kernel replaced, so this is an independent oracle rather than a restatement.
    """
    bits = 0
    for i in range(9):
        bits |= b[i] << (8 * i)
    return [(bits >> (18 * k)) & ((1 << 18) - 1) for k in range(4)]


def _sweep_exact(terms):
    """COORDINATE SWEEP: every byte, every value, the other eight zero.

    Complete BECAUSE both maps are bytewise additive (the two conjuncts below):
    a map of the form M(b) = sum_i g_i(b_i) is determined by its nine
    restrictions, so agreement on the axes IS agreement on the whole 2^72 domain.
    """
    for i in range(9):
        for x in range(256):
            b = [0] * 9
            b[i] = x
            if _extract_shipped(b, terms) != _extract_fips(b):
                return False
    return True


def _bytewise_additive(fn):
    """M(b) == sum over the nine axes of M(b restricted to one byte).

    Checked on a seeded pseudo-random sample of full 9-byte tuples; it is the
    hypothesis that makes `_sweep_exact` a complete argument, so it is stated
    and checked rather than assumed.
    """
    st = 0x243F6A8885A308D3
    for _ in range(4000):
        st = (st * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        b = [(st >> (7 * j)) & 0xFF for j in range(9)]
        whole = fn(b)
        axes = [0, 0, 0, 0]
        for i in range(9):
            e = [0] * 9
            e[i] = b[i]
            part = fn(e)
            for k in range(4):
                axes[k] += part[k]
        if whole != axes:
            return False
    return True


def o10_packed_field_extraction():
    """unpackZPacked builds the four 18-bit fields with twelve left-shifted byte
    terms and ONE mask.  The terms are pairwise disjoint, so the OR is a sum and
    the map is bytewise additive; a complete coordinate sweep then settles
    equality with FIPS 204 BitUnpack over the whole 2^72 domain."""
    # HARDENING NOTE: each conjunct and its controls share one predicate (see O1).
    def mask_is_four_18_bit_lanes(m):
        return m == sum(((1 << 18) - 1) << (64 * k) for k in range(4))

    ok_disjoint = _terms_disjoint(Z_TERMS)
    ok_inside = _terms_inside_the_word(Z_TERMS)
    ok_mask = mask_is_four_18_bit_lanes(Z_M18_DEC)
    ok_sweep = _sweep_exact(Z_TERMS)
    ok_add_new = _bytewise_additive(_extract_shipped)
    ok_add_ref = _bytewise_additive(_extract_fips)
    ok_mulc = _fused_constants_are_the_two_powers(Z_MUL_PAIRS)
    ok_mule = _fused_multiply_is_the_two_terms(Z_MUL_PAIRS)
    ok_mulp = _mul_pairs_are_the_doubled_terms(Z_MUL_PAIRS)
    # a fused constant with ONE bit moved: the multiply stops being the two
    # terms (it is still a multiply, which is exactly why this is checked
    # exhaustively rather than by inspection)
    bad_c_hi = tuple((i, s, t, c + (1 << (t + 1))) for i, s, t, c in Z_MUL_PAIRS)
    bad_c_lo = tuple((i, s, t, c - (1 << s)) for i, s, t, c in Z_MUL_PAIRS)
    bad_c_shift = tuple((i, s, t, (1 << s) + (1 << (t - 1))) for i, s, t, c in Z_MUL_PAIRS)
    # a shift moved by one must break the sweep, in both directions, and on a
    # doubled byte as well as a single one
    bad_low = tuple((i, sh - 1 if sh == 62 else sh) for i, sh in Z_TERMS)
    bad_high = tuple((i, sh + 1 if sh == 202 else sh) for i, sh in Z_TERMS)
    bad_mid = tuple((i, sh - 1 if sh == 132 else sh) for i, sh in Z_TERMS)
    dropped = tuple(t for t in Z_TERMS if t != (2, 62))
    return record(
        "O10", "EXH",
        "unpackZPacked field extraction: 12 disjoint byte terms (the three doubled "
        "ones emitted by ONE multiply each) + ONE 18-bit mask == FIPS 204 "
        "BitUnpack on the complete 9-byte domain",
        True,
        f"top bit {max(sh for _i, sh in Z_TERMS) + 7}; 9 x 256 coordinate sweep, "
        "bytewise-additive on both sides",
        parts=[("terms_pairwise_disjoint", ok_disjoint),
               ("terms_inside_the_word", ok_inside),
               ("mask_is_four_18_bit_lanes", ok_mask),
               ("coordinate_sweep_exact", ok_sweep),
               ("shipped_map_is_bytewise_additive", ok_add_new),
               ("fips_map_is_bytewise_additive", ok_add_ref),
               ("fused_constants_are_the_two_powers", ok_mulc),
               ("fused_multiply_is_the_two_terms", ok_mule),
               ("mul_pairs_are_the_doubled_terms", ok_mulp)]
        + controls(_terms_disjoint, label="ctl_disjoint",
                   accept=[Z_TERMS, ((0, 0), (1, 8))],
                   reject=[((0, 0), (1, 0)), ((2, 62), (3, 64)),
                           ((6, 140), (5, 136)), Z_TERMS + ((0, 16),)])
        + controls(mask_is_four_18_bit_lanes, label="ctl_mask",
                   accept=[Z_M18_DEC],
                   reject=[0, Z_M18_DEC + 1, (1 << 18) - 1,
                           sum(((1 << 18) - 1) << (64 * k) for k in range(3)),
                           sum(((1 << 17) - 1) << (64 * k) for k in range(4))])
        + controls(_sweep_exact, label="ctl_sweep",
                   accept=[Z_TERMS], reject=[bad_low, bad_high, bad_mid, dropped])
        + controls(_fused_multiply_is_the_two_terms, label="ctl_fused_mul",
                   accept=[Z_MUL_PAIRS],
                   reject=[bad_c_hi, bad_c_lo, bad_c_shift])
        + controls(_fused_constants_are_the_two_powers, label="ctl_fused_const",
                   accept=[Z_MUL_PAIRS], reject=[bad_c_hi, bad_c_lo])
        + controls(_mul_pairs_are_the_doubled_terms, label="ctl_fused_pairs",
                   accept=[Z_MUL_PAIRS],
                   reject=[Z_MUL_PAIRS[:2],
                           tuple((i, s, t + 1, c) for i, s, t, c in Z_MUL_PAIRS),
                           ((0, 0, 46, (1 << 46) + 1),)]),
    )


def main():
    t0 = time.time()
    print("=" * 78)
    print("O1-O10 kernel obligations (companion to formal/z3/verify_all.py)")
    print("=" * 78)
    o1_division_constant()
    o2_no_cross_lane_carry()
    o3_ge_comparator()
    o4_mod44()
    o5_multiply_gather()
    o6_usehint_equivalence()
    o7_preshifted_lane_product()
    o8_accumulator_bounds()
    o9_packed_store_disjoint()
    o10_packed_field_extraction()
    npass = sum(1 for r in results if r[3])
    print("=" * 78)
    print(f"{npass}/{len(results)} obligations PASS in {time.time() - t0:.1f}s")
    print("=" * 78)
    return 0 if npass == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
