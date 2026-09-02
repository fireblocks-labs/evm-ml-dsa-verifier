#!/usr/bin/env python3
"""
wycheproof_build.py — fixture-shard builder for test/SEC2_Wycheproof.t.sol.

  usage (this is what vm.ffi runs, cwd = repository root):
      pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py wp_0.hex
      pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py --build
      pythonref/myenv/bin/python tools/fixtures/wycheproof_build.py --audit

OUTPUT — hex text (no 0x, no newline) on stdout; shards are cached under
test/fixtures/ and rebuilt only when missing (same self-healing pattern as
tools/fixtures/acvp_build.py, via fx_common.serve/main).

SOURCE — test/vectors/wycheproof/mldsa_44_verify_test.json, vendored verbatim
from https://github.com/C2SP/wycheproof (testvectors_v1/).  URL, SHA-256,
retrieval date and the group/flag census are in the sibling provenance.txt,
and this script re-checks the SHA-256 on every build.

WHY WYCHEPROOF ON TOP OF ACVP.  The official NIST ACVP sigVer corpus that
test/ACVP_MLDSA44.t.sol replays contains no systematic coverage of malformed
HintBitPack encodings (the hEncode(h) region of the FIPS 204 signature).
Wycheproof does: tcId 15..19 and 137..139 are exactly that class (reverse
order, repeated index, non-zero padding, limit going backwards, limits that
read past the 84-byte hint section).  tcId 18, "signature with a repeated
hint", is the vector that reproduces the CVE-2026-24850 bug class in
RustCrypto `ml-dsa` — it passes ACVP and fails Wycheproof.

VERDICTS.  The expected verdict is ALWAYS Wycheproof's own `result` field; it
is never adjusted to whatever an implementation happens to do.  Every verdict
is nevertheless independently cross-checked against the pythonref dilithium_py
reference oracle, and a disagreement is reported loudly on stderr.  A
disagreement that is not in KNOWN_ORACLE_DIVERGENCE aborts the build, AND an
entry in KNOWN_ORACLE_DIVERGENCE that no longer corresponds to an observed
divergence -- or that now sits on a case with a different `comment` -- aborts it
too, so the corpus can never drift silently in either direction.
See KNOWN_ORACLE_DIVERGENCE below: the
python oracle itself has one.

`result: "acceptable"` — Wycheproof's third verdict, "a strict verifier may
reject this".  This file (v1, SHA above) contains ZERO acceptable cases
(77 valid / 103 invalid / 0 acceptable), so the policy is currently moot, but
it is implemented and enforced: ACCEPTABLE_IS_VALID = False, i.e. an
`acceptable` case would be treated as MUST-REJECT, which is the right stance
for a strict FIPS 204 verifier.  Both counts are printed by --audit.

REPRESENTABILITY.  Two structural limits of the on-chain designs:

  * ctx.  Both in-tree verifiers (test/ZZZ_E2ERef.sol and the shipped
    src/MLDSA44Verifier.sol) implement ML-DSA with an EMPTY context only
    (M' = 0x00 || 0x00 || M); they have no ctx parameter at all.  A Wycheproof
    case carrying a non-empty ctx therefore MUST NOT be accepted — that is
    real domain-separation coverage, not a skip, and those cases get the
    ":ctxbind" label suffix (same convention as acvp_build.py).

  * public-key length.  Both verifiers consume a FIXED-SIZE pre-expanded pk
    data contract (20,544-byte payload) built off-chain from a 1,312-byte pk.
    A 1,311- or 1,313-byte pk simply cannot be turned into one, so the four
    IncorrectPublicKeyLength cases are NOT verifier cases: they are
    REGISTRATION-layer cases.  They are segregated into their own shard
    (wpc_pklen.hex) which carries the raw malformed pk, so the Solidity side
    can assert (a) the registration layer must reject it on length, and
    (b) what the "helpful" canonicalisation an implementer might be tempted to
    do (truncate 1,313 -> 1,312, or zero-pad 1,311 -> 1,312) actually produces.
    For three of the four cases the canonical cache still rejects, because
    tr = H(pk) binds the exact byte string that was signed.  For tcId 65 it
    does NOT: the "long public key" is a genuine 1,312-byte key with a trailing
    0x00 appended and the signature was made over the real key, so the
    canonicalised cache ACCEPTS.  Truncating is therefore unsafe, and the
    registration layer MUST enforce len(pk) == 1312 exactly.  Nothing here
    pretends the verifier itself covers a wrong-length key.

SHARDS
  wp_0.hex .. wp_3.hex   Combo, round-robin over all 176 representable cases
  wpc_hints.hex          flag InvalidHintsEncoding        (8 cases)
  wpc_zeropk.hex         flag ZeroPublicKey               (35 cases)
  wpc_norm.hex           flag InfinityNormViolation       (42 cases)
  wpc_bound.hex          flag BoundaryCondition           (61 cases)
  wpc_many.hex           flag ManySteps                   (44 cases)
  wpc_siglen.hex         flag IncorrectSignatureLength    (3 cases)
  wpc_ctx.hex            every case carrying a `ctx`      (8 cases)
  wpc_pklen.hex          flag IncorrectPublicKeyLength    (4 cases, PkLenShard)

The class shards deliberately overlap wp_0..3 so a reviewer can find each
regression class by name in test/SEC2_Wycheproof.t.sol.

Deterministic, offline (the corpus is vendored), no randomness.
"""

import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import fx_common as F  # noqa: E402

# ---------------------------------------------------------------- provenance

VECTORS = F.FOUNDRY_ROOT / "test" / "vectors" / "wycheproof" / "mldsa_44_verify_test.json"
VECTORS_SHA256 = "5ec04790c240c443ca8b662b8fc871834602c7cce87fcd36a193110745b2b9ea"

# ------------------------------------------------------------------- policy

# Wycheproof's third verdict.  A strict FIPS 204 verifier should reject an
# "acceptable" case, so it counts as must-reject.  (This file has none.)
ACCEPTABLE_IS_VALID = False

# Disagreements between Wycheproof's `result` and the pythonref dilithium_py
# reference oracle that are EXPECTED, i.e. the oracle is the one that is
# wrong.
#
# THIS TABLE IS AN EQUALITY, NOT A FILTER.  Keyed by tcId alone and consulted
# only to SUPPRESS, an entry would mean "do not abort": nothing would assert
# that the divergence it describes still happens, and nothing would check that
# the case landing on that tcId is still the same case.
# Both halves fail OPEN, and they fail open exactly when the protection matters:
#
#   * re-pin the corpus and let the ids shift, and a DIFFERENT case arriving at
#     tcId 18 is silently exempted from the only oracle cross-check there is;
#   * fix `dilithium_py` (or have upstream drop the case) and the entry becomes a
#     standing licence to ignore whatever next lands there, with no signal at all
#     that it stopped describing anything.
#
# So the check below is two-directional and content-pinned:
#   (a) every observed divergence must be listed here          -> else ABORT
#   (b) every entry here must be OBSERVED                      -> else ABORT
#   (c) the observed case's `comment` must equal `comment` here -> else ABORT
# `comment` is Wycheproof's own per-test string, so (c) pins WHICH case this is
# independently of its numbering.
#
# tcId 18 — "signature with a repeated hint".  HintBitUnpack (FIPS 204
# Algorithm 21) requires the indices inside each polynomial's slice to be
# STRICTLY increasing; a repeated index makes the encoding non-canonical and
# the signature invalid.  dilithium_py's _unpack_h does not enforce it and
# ACCEPTS the signature, so a signature can be re-encoded into a second,
# distinct byte string that still verifies — signature malleability.  This is
# the same defect as CVE-2026-24850 in RustCrypto `ml-dsa`.  Wycheproof is
# right; the expectation stays "invalid" and both EVM verifiers must reject.
KNOWN_ORACLE_DIVERGENCE = {
    18: {
        # Wycheproof's own `comment` for this test, pinned verbatim.
        "comment": "signature with a repeated hint",
        "why": "dilithium_py accepts a non-canonical repeated hint index "
               "(FIPS 204 Alg. 21 requires strictly increasing indices) "
               "— CVE-2026-24850 class",
    },
}

NAMES = (
    [f"wp_{k}.hex" for k in range(4)]
    + ["wpc_hints.hex", "wpc_zeropk.hex", "wpc_norm.hex", "wpc_bound.hex",
       "wpc_many.hex", "wpc_siglen.hex", "wpc_ctx.hex"]
    + ["wpc_pklen.hex"]
)
N_MAIN_SHARDS = 4

# short tags used in the on-chain labels, so a console.log line identifies the
# regression class without the reviewer having to look up the tcId
SHORT = {
    "ValidSignature": "ok",
    "InvalidSignature": "bad",
    "ModifiedSignature": "mod",
    "InvalidHintsEncoding": "hints",
    "InfinityNormViolation": "norm",
    "ZeroPublicKey": "zeropk",
    "BoundaryCondition": "bnd",
    "ManySteps": "many",
    "InvalidContext": "ctx",
    "IncorrectSignatureLength": "siglen",
    "IncorrectPublicKeyLength": "pklen",
    "InvalidPrivateKey": "isk",
}

# --------------------------------------------------------------- shard types
#
# Field order MUST match the Solidity struct declarations in
# test/SEC2_Wycheproof.t.sol verbatim — abi.decode is positional.

COMBO_T = "(bytes[],uint256[],uint256[],bytes[],bytes[],bool[],string[])"
#          pkBlobs  pkIdx      tcIds      msgs    sigs    expect  labels

PKLEN_T = "(bytes[],bytes[],uint256[],bytes[],bytes[],bool[],string[])"
#          rawPk    pkBlobs  tcIds      msgs    sigs    canonAcc labels
#          rawPk    the malformed pk verbatim (1,311 / 1,313 B)
#          pkBlobs  payload built from the CANONICALISED 1,312-byte key
#          canonAcc the MEASURED oracle verdict for that canonical key —
#                   true for tcId 65, where the "long public key" is a real
#                   key plus a trailing 0x00 and the signature was made over
#                   the real key.  The on-chain verifier is *right* to accept
#                   it; what must reject the case is the registration layer's
#                   length check.  Never hardcoded; see build_corpus().


class Case:
    __slots__ = ("tc", "gi", "comment", "flags", "result", "pk", "msg", "sig",
                 "ctx", "exp", "label", "ctx_field")


def _log(*a):
    print(*a, file=sys.stderr)


def _load():
    raw = VECTORS.read_bytes()
    got = hashlib.sha256(raw).hexdigest()
    if got != VECTORS_SHA256:
        raise SystemExit(
            f"wycheproof_build: {VECTORS} SHA-256 mismatch\n"
            f"  expected {VECTORS_SHA256}\n  got      {got}\n"
            f"  (re-download per test/vectors/wycheproof/provenance.txt)"
        )
    d = json.loads(raw)
    if d.get("algorithm") != "ML-DSA-44":
        raise SystemExit(f"wycheproof_build: unexpected algorithm {d.get('algorithm')!r}")
    return d


def _label(tc, flags, suffix=""):
    tags = "+".join(SHORT.get(f, f) for f in flags) or "-"
    return f"WP{tc}[{tags}]{suffix}"


def _canonical_pk(pk):
    """The 1,312-byte key a naive registration layer would derive from a
    malformed-length pk: truncate if too long, zero-pad if too short."""
    if len(pk) > F.PK_LEN:
        return pk[: F.PK_LEN]
    return pk + b"\x00" * (F.PK_LEN - len(pk))


# ------------------------------------------------------------------- corpus


def build_corpus():
    """Return (std_cases, pklen_cases, stats).  Aborts on any unexplained
    disagreement between Wycheproof and the reference oracle."""
    d = _load()
    std, pklen = [], []
    divergences = []
    n_tests = 0
    counts = {"valid": 0, "invalid": 0, "acceptable": 0}
    flag_hist = {}

    for gi, g in enumerate(d["testGroups"]):
        if g.get("type") != "MlDsaVerify":
            raise SystemExit(f"wycheproof_build: unexpected group type {g.get('type')!r}")
        pk = bytes.fromhex(g["publicKey"])
        for t in g["tests"]:
            n_tests += 1
            tc = t["tcId"]
            res = t["result"]
            if res not in counts:
                raise SystemExit(f"wycheproof_build: tcId {tc}: unknown result {res!r}")
            counts[res] += 1
            flags = list(t.get("flags", []))
            for f in flags:
                flag_hist[f] = flag_hist.get(f, 0) + 1

            wp_valid = res == "valid" or (res == "acceptable" and ACCEPTABLE_IS_VALID)
            msg = bytes.fromhex(t["msg"])
            sig = bytes.fromhex(t["sig"])
            ctx = bytes.fromhex(t.get("ctx", ""))

            c = Case()
            c.tc, c.gi, c.comment, c.flags, c.result = tc, gi, t["comment"], flags, res
            c.pk, c.msg, c.sig, c.ctx = pk, msg, sig, ctx
            c.ctx_field = "ctx" in t  # the vector explicitly carried a context

            # ---- oracle cross-check (Wycheproof stays authoritative) ----
            oracle_ctx = F.verify_pure(pk, msg, sig, ctx)
            if oracle_ctx != wp_valid:
                divergences.append((tc, res, oracle_ctx, flags, t["comment"], gi))

            if len(pk) != F.PK_LEN:
                # registration-layer case; see module docstring
                if wp_valid:
                    raise SystemExit(f"wycheproof_build: tcId {tc}: wrong-length pk marked valid?")
                if ctx:
                    raise SystemExit(f"wycheproof_build: tcId {tc}: wrong-length pk with ctx is unsupported")
                # What a "helpful" registration layer that canonicalises the
                # length (truncate / zero-pad) would end up caching.  The
                # verdict is MEASURED with the reference oracle, never
                # assumed: for tcId 65 the 1,313-byte key is a genuine
                # 1,312-byte key plus a trailing 0x00 and the signature was
                # made over the real key, so the canonical cache ACCEPTS.
                # That is the whole point of the flag — the only thing standing
                # between a non-canonical pk encoding and a valid signature is
                # a strict length check at REGISTRATION time.
                canon = _canonical_pk(pk)
                c.exp = F.verify_pure(canon, msg, sig, b"")
                c.label = _label(tc, flags, ":reglayer")
                pklen.append(c)
                continue

            # both verifiers are empty-ctx only, so a non-empty ctx must fail
            c.exp = wp_valid and not ctx
            c.label = _label(tc, flags, ":ctxbind" if (ctx and wp_valid) else "")

            oracle_empty = F.verify_pure(pk, msg, sig, b"")
            if oracle_empty != c.exp:
                # RECORDED, never suppressed here: the allowlist is applied once,
                # below, where it is also checked for the reverse direction.
                divergences.append((tc, res, oracle_empty, flags, t["comment"] + " [empty-ctx replay]", gi))
            std.append(c)

    # -------------------------------------------------- loud divergence report
    # (a) observed but not adjudicated, (b) adjudicated but not observed,
    # (c) adjudicated and observed but describing a DIFFERENT case.
    observed = {x[0] for x in divergences}
    unexplained = [x for x in divergences if x[0] not in KNOWN_ORACLE_DIVERGENCE]
    vanished = sorted(set(KNOWN_ORACLE_DIVERGENCE) - observed)
    mismatched = []
    for tc, _res, _got, _flags, comment, _gi in divergences:
        entry = KNOWN_ORACLE_DIVERGENCE.get(tc)
        if entry is None:
            continue
        base = comment[: -len(" [empty-ctx replay]")] \
            if comment.endswith(" [empty-ctx replay]") else comment
        if base != entry["comment"]:
            mismatched.append((tc, entry["comment"], base))
    if divergences:
        _log("")
        _log("=" * 78)
        _log("!!  WYCHEPROOF vs pythonref dilithium_py REFERENCE ORACLE DISAGREE  !!")
        _log("=" * 78)
        for tc, res, got, flags, comment, gi in divergences:
            known = (KNOWN_ORACLE_DIVERGENCE.get(tc) or {}).get("why")
            _log(f"  tcId {tc} (group {gi})  wycheproof={res}  oracle={'valid' if got else 'invalid'}")
            _log(f"      flags   : {flags}")
            _log(f"      comment : {comment}")
            _log(f"      status  : {'KNOWN — ' + known if known else '*** UNEXPLAINED ***'}")
        _log("=" * 78)
        _log("  Expected verdicts below are WYCHEPROOF's, unchanged.  The EVM")
        _log("  verifiers are required to match Wycheproof, not the oracle.")
        _log("=" * 78)
        _log("")
    if unexplained:
        raise SystemExit(
            f"wycheproof_build: {len(unexplained)} UNEXPLAINED oracle divergence(s) "
            f"(tcIds {[x[0] for x in unexplained]}); refusing to build a corpus whose "
            f"expectations nobody has adjudicated"
        )
    if vanished:
        raise SystemExit(
            f"wycheproof_build: KNOWN_ORACLE_DIVERGENCE lists tcIds {vanished}, and "
            f"NO divergence was observed for them.  A suppression entry that no longer "
            f"describes anything is a standing exemption for whatever case next lands "
            f"on that id -- which is precisely when it is dangerous.  Either the oracle "
            f"was fixed (delete the entry and say so), or the corpus was re-pinned and "
            f"the ids moved (re-adjudicate)."
        )
    if mismatched:
        raise SystemExit(
            "wycheproof_build: KNOWN_ORACLE_DIVERGENCE is pinned to the wrong case(s): "
            + "; ".join(f"tcId {tc}: pinned {want!r}, corpus says {got!r}"
                        for tc, want, got in mismatched)
            + ".  The ids shifted under the allowlist; re-adjudicate rather than "
              "re-number."
        )
    _log(f"[wp] oracle divergences: observed {sorted(observed)} == "
         f"adjudicated {sorted(KNOWN_ORACLE_DIVERGENCE)}, comments pinned")

    stats = {
        "tests": n_tests,
        "groups": len(d["testGroups"]),
        "results": counts,
        "flags": flag_hist,
        "std": len(std),
        "pklen": len(pklen),
        "divergences": divergences,
    }
    if n_tests != d.get("numberOfTests"):
        raise SystemExit(f"wycheproof_build: parsed {n_tests} tests, header says {d.get('numberOfTests')}")
    return std, pklen, stats


# -------------------------------------------------------------------- blobs

_PK_CACHE = {}


def _pk(pk):
    if pk not in _PK_CACHE:
        _PK_CACHE[pk] = F.pk_blob(pk)
    return _PK_CACHE[pk]


def _combo(cases):
    """Pack a list of Case into the COMBO_T tuple, deduplicating pk blobs."""
    blobs, order, pkIdx = [], {}, []
    for c in cases:
        if c.pk not in order:
            order[c.pk] = len(blobs)
            blobs.append(_pk(c.pk))
        pkIdx.append(order[c.pk])
    return (
        blobs,
        pkIdx,
        [c.tc for c in cases],
        [c.msg for c in cases],
        [c.sig for c in cases],
        [c.exp for c in cases],
        [c.label for c in cases],
    )


def _has(c, flag):
    return flag in c.flags


def build_all():
    std, pklen, stats = build_corpus()

    # ---- main shards, round-robin so every class is present in every shard
    for k, idxs in enumerate(F.round_robin(len(std), N_MAIN_SHARDS)):
        F.write_shard(f"wp_{k}.hex", F.enc(COMBO_T, _combo([std[i] for i in idxs])))

    # ---- per-flag class shards (deliberately overlap the main shards)
    classes = {
        "wpc_hints.hex": lambda c: _has(c, "InvalidHintsEncoding"),
        "wpc_zeropk.hex": lambda c: _has(c, "ZeroPublicKey"),
        "wpc_norm.hex": lambda c: _has(c, "InfinityNormViolation"),
        "wpc_bound.hex": lambda c: _has(c, "BoundaryCondition"),
        "wpc_many.hex": lambda c: _has(c, "ManySteps"),
        "wpc_siglen.hex": lambda c: _has(c, "IncorrectSignatureLength"),
        # every vector that explicitly carries a `ctx` field, including tcId 2
        # (ctx = "") which is the positive control for the empty-ctx verifiers
        "wpc_ctx.hex": lambda c: c.ctx_field or _has(c, "InvalidContext"),
    }
    for name, pred in classes.items():
        sel = [c for c in std if pred(c)]
        if not sel:
            _log(f"[wp] WARNING: class shard {name} is EMPTY — no representable case carries that flag")
        F.write_shard(name, F.enc(COMBO_T, _combo(sel)))
        _log(f"[wp] {name}: {len(sel)} cases, tcIds {[c.tc for c in sel]}")

    # ---- registration-layer shard (wrong-length public keys)
    canon = [_canonical_pk(c.pk) for c in pklen]
    pk_shard = (
        [c.pk for c in pklen],
        [_pk(p) for p in canon],
        [c.tc for c in pklen],
        [c.msg for c in pklen],
        [c.sig for c in pklen],
        [c.exp for c in pklen],
        [c.label for c in pklen],
    )
    F.write_shard("wpc_pklen.hex", F.enc(PKLEN_T, pk_shard))
    _log(f"[wp] wpc_pklen.hex: {len(pklen)} registration-layer cases, tcIds {[c.tc for c in pklen]}")
    for c in pklen:
        _log(
            f"[wp]   tcId {c.tc}: len(pk)={len(c.pk)} -> canonicalised 1312 B "
            f"{'ACCEPTS (registration MUST reject on length!)' if c.exp else 'rejects'}"
        )

    return stats


# -------------------------------------------------------------------- audit


def audit():
    """Human-readable census; does not write shards."""
    std, pklen, st = build_corpus()
    print(f"vectors      {VECTORS}")
    print(f"sha256       {VECTORS_SHA256}")
    print(f"groups       {st['groups']}")
    print(f"tests        {st['tests']}")
    print(f"results      valid={st['results']['valid']} invalid={st['results']['invalid']} "
          f"acceptable={st['results']['acceptable']}  (policy: acceptable -> "
          f"{'ACCEPT' if ACCEPTABLE_IS_VALID else 'REJECT'})")
    print(f"representable {len(std)}   registration-layer-only (wrong pk length) {len(pklen)}")
    acc = sum(c.exp for c in std)
    print(f"verifier expectation   must-accept {acc}  must-reject {len(std) - acc}")
    ctxbind = [c.tc for c in std if c.label.endswith(":ctxbind")]
    print(f"ctxbind (valid-with-ctx, must be rejected by the empty-ctx verifiers): {ctxbind}")
    print("per-flag (representable cases only):")
    for f in sorted(SHORT):
        sel = [c for c in std if _has(c, f)]
        if not sel:
            print(f"    {f:26s} 0   (no representable case)")
            continue
        a = sum(c.exp for c in sel)
        print(f"    {f:26s} {len(sel):3d}   must-accept {a:3d}  must-reject {len(sel) - a:3d}")
    print(f"oracle divergences: {len(st['divergences'])}")
    for tc, res, got, flags, comment, gi in st["divergences"]:
        print(f"    tcId {tc}: wycheproof={res} oracle={'valid' if got else 'invalid'} | {comment}")


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "--audit":
        audit()
    else:
        F.main(sys.argv, build_all, NAMES)
