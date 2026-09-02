#!/usr/bin/env python3
"""
acvp_build.py — fixture-shard builder for test/ACVP_MLDSA44.t.sol.

  usage (this is what vm.ffi runs, cwd = repository root):
      pythonref/myenv/bin/python tools/fixtures/acvp_build.py ah_0.hex
      pythonref/myenv/bin/python tools/fixtures/acvp_build.py --build   # all

OUTPUT — hex text (no 0x, no newline) on stdout; the shards are cached under
test/fixtures/ and rebuilt only when missing.

  ah_0.hex .. ah_5.hex   Shard = (bytes[] pkBlobs, uint256[] pkIdx,
                                  bytes[] msgs, bytes[] sigs,
                                  bool[] expect, string[] labels)
                         6 shards over the same 165-case corpus.  Each case is
                         replayed against BOTH in-tree subjects: the reference
                         verifier test/ZZZ_E2ERef.sol and the shipped
                         src/MLDSA44Verifier.sol (both implement pure ML-DSA-44
                         with an empty context, so one verdict column serves
                         both).

  at_0.hex .. at_3.hex   the SAME tuple shape over the FIPS204-tr1 corpus:
                         120 ML-DSA-44 external-interface cases (60 pure +
                         60 preHash) on 120 official keys that appear NOWHERE
                         ELSE in this tree -- a disjoint second official key
                         population, not a re-cut of the corpus above.  See
                         `build_tr1_corpus`.

CORPUS — 165 cases, in this order (see README_shards.md for provenance):
  idx   0.. 14  SV  15  ACVP ML-DSA-sigVer-FIPS204, ML-DSA-44, external/pure
                       (tgId 1, tcId 1..15).  Verdict = ACVP `testPassed`.
  idx  15.. 44  SG  30  ACVP ML-DSA-sigGen-FIPS204, ML-DSA-44, external/pure
                       (deterministic + hedged groups).  Always valid.
  idx  45.. 89  PH  45  ACVP HashML-DSA (external/preHash): 15 from sigVer +
                       30 from sigGen.  Replayed as PURE ML-DSA, so all 45 are
                       must-reject (FIPS 204 pure/preHash domain separation);
                       each one is first confirmed to verify in its own preHash
                       domain (M' = 0x01||len(ctx)||ctx||OID||PH(M)).
  idx  90..104  DVv 15  the official sigVer (sk, message) re-signed with ctx=""
                       so both verifiers get true positives on official NIST
                       key material.  Always valid.
  idx 105..164  DVm 60  the four ACVP mutation classes (modified message /
                       modified signature - commitment / - z / - hint) applied
                       to each DVv signature.  Always must-reject.

Both verifiers implement ML-DSA with an EMPTY context only, so an official
case carrying a non-empty ctx must NOT be accepted; those get the ":ctxbind"
label suffix (domain-separation coverage).

VERDICTS are never invented: they come from ACVP `testPassed` where ACVP has
one, and EVERY expected verdict is independently reproduced with the pythonref
dilithium_py oracle before it is emitted.  A disagreement aborts the build.

TR1 CORPUS — 120 cases (`at_*`), from ML-DSA-sigGen-FIPS204-tr1:
  TP<tc>   60  external/pure.  5 carry an EMPTY context and are must-ACCEPT --
               the only official-answer must-accepts in this tree outside the
               keyGen shards.  The other 55 carry a non-empty context and are
               must-REJECT on context binding (":ctxbind").
  TH<tc>  60  external/preHash.  All must-REJECT as pure ML-DSA, each first
               confirmed to verify in its OWN preHash domain, exactly as the
               PH category above.
Every tr1 case is labelled with its `keyFormat` (`seed` / `expanded`), because
tr1 presents each group in both key presentations; both hand a verifier the
same 1,312-byte pk, so the label is documentation and not a branch.

SHARDING is round-robin (case i -> shard i % nshards).  This keeps every
category present in every shard and, in particular, puts sigVer tcId 14 — the
one official ML-DSA-44 key whose tr[0] is 0xEF — together with its DVv case in
shard ah_1, which test_acvp_eip3541_pk_prefix is built around.  THE ah_*
ASSIGNMENT IS THEREFORE LOAD-BEARING: the tr1 cases go into their own family
rather than being appended to the 165, so that adding them moves nothing.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import fx_common as F  # noqa: E402

NAMES = [f"ah_{k}.hex" for k in range(6)] + [f"at_{k}.hex" for k in range(4)]
N_SHARDS = 6
TR1_SHARDS = 4

# ABI tuple; field order MUST match struct Shard in test/ACVP_MLDSA44.t.sol.
SHARD_T = "(bytes[],uint256[],bytes[],bytes[],bool[],string[])"

# the four ACVP mutation classes, applied to the freshly re-signed DVv vectors
MUTATIONS = ("msg", "ctilde", "z", "hint")


def _flip(buf, lo, hi, tag):
    """Flip one deterministically chosen bit in buf[lo:hi]."""
    r = F.rnd(b"acvp/flip/" + tag, 8)
    off = lo + int.from_bytes(r[:4], "big") % (hi - lo)
    bit = r[4] & 7
    out = bytearray(buf)
    out[off] ^= 1 << bit
    return bytes(out)


def _mutate(kind, tc, msg, sig):
    """Return (message, signature) for one ACVP-style mutation class."""
    if kind == "msg":
        m = bytearray(msg) if msg else bytearray(b"\x00")
        m[0] ^= 0x01
        return bytes(m), sig
    if kind == "ctilde":
        return msg, _flip(sig, 0, 32, b"ct/%d" % tc)
    if kind == "z":
        return msg, _flip(sig, 32, 2336, b"z/%d" % tc)
    if kind == "hint":  # the hEncode(h) region of the FIPS 204 signature
        return msg, _flip(sig, 2336, 2416, b"h/%d" % tc)
    raise AssertionError(kind)


class Case:
    __slots__ = ("pk", "msg", "sig", "exp", "label")

    def __init__(self, pk, msg, sig, exp, label):
        self.pk, self.msg, self.sig = pk, msg, sig
        self.exp, self.label = exp, label


def build_corpus():
    ml, _ = F.acvp_data()
    cases = []

    def check(cond, what):
        if not cond:
            raise SystemExit(f"acvp_build: ORACLE DISAGREEMENT — {what}")

    # ---------------------------------------------------------------- SV (15)
    sv_pure = ml["sigVer"]["pure"]
    for t in sv_pure:
        pk = bytes.fromhex(t["pk"])
        msg = bytes.fromhex(t["message"])
        sig = bytes.fromhex(t["signature"])
        ctx = bytes.fromhex(t["context"])
        acvp = bool(t["testPassed"])
        # ACVP's own verdict, reproduced by the reference oracle
        check(F.verify_pure(pk, msg, sig, ctx) == acvp,
              f"sigVer tcId {t['tcId']} ({t.get('reason')}): oracle != ACVP testPassed")
        exp = acvp if not ctx else False
        check(F.verify_pure(pk, msg, sig, b"") == exp,
              f"sigVer tcId {t['tcId']}: empty-ctx oracle != expected verdict")
        lab = f"SV{t['tcId']}" + (":ctxbind" if ctx else "")
        cases.append(Case(pk, msg, sig, exp, lab))

    # ---------------------------------------------------------------- SG (30)
    for t in ml["sigGen"]["pure"]:
        pk = bytes.fromhex(t["pk"])
        msg = bytes.fromhex(t["message"])
        sig = bytes.fromhex(t["signature"])
        ctx = bytes.fromhex(t["context"])
        check(F.verify_pure(pk, msg, sig, ctx), f"sigGen tcId {t['tcId']}: official signature must verify")
        exp = not ctx
        check(F.verify_pure(pk, msg, sig, b"") == exp,
              f"sigGen tcId {t['tcId']}: empty-ctx oracle != expected verdict")
        lab = f"SG{t['tcId']}" + (":ctxbind" if ctx else "")
        cases.append(Case(pk, msg, sig, exp, lab))

    # ---------------------------------------------------------------- PH (45)
    for t in ml["sigVer"]["preHash"] + ml["sigGen"]["preHash"]:
        pk = bytes.fromhex(t["pk"])
        msg = bytes.fromhex(t["message"])
        sig = bytes.fromhex(t["signature"])
        ctx = bytes.fromhex(t["context"])
        want_ph = bool(t["testPassed"]) if "testPassed" in t else True
        # (i) the case behaves as ACVP says inside its OWN preHash domain ...
        check(F.verify_prehash(pk, msg, sig, ctx, t["hashAlg"]) == want_ph,
              f"preHash tcId {t['tcId']} ({t['hashAlg']}): oracle != ACVP verdict in preHash domain")
        # (ii) ... and can never verify as PURE ML-DSA, with or without ctx
        check(not F.verify_pure(pk, msg, sig, ctx), f"preHash tcId {t['tcId']}: verified as pure ML-DSA (ctx)")
        check(not F.verify_pure(pk, msg, sig, b""), f"preHash tcId {t['tcId']}: verified as pure ML-DSA (empty ctx)")
        cases.append(Case(pk, msg, sig, False, f"PH{t['tcId']}"))

    # --------------------------------------------------------------- DVv (15)
    dv = []
    for t in sv_pure:
        pk = bytes.fromhex(t["pk"])
        sk = bytes.fromhex(t["sk"])
        msg = bytes.fromhex(t["message"])
        sig = F.D.sign(sk, msg, ctx=b"", deterministic=True)
        check(F.verify_pure(pk, msg, sig, b""),
              f"DV{t['tcId']}: re-signed official key material must verify with empty ctx")
        cases.append(Case(pk, msg, sig, True, f"DV{t['tcId']}"))
        dv.append((t["tcId"], pk, msg, sig))

    # --------------------------------------------------------------- DVm (60)
    for tc, pk, msg, sig in dv:
        for kind in MUTATIONS:
            m2, s2 = _mutate(kind, tc, msg, sig)
            check(not F.verify_pure(pk, m2, s2, b""),
                  f"DV{tc}:{kind}: mutated signature must be rejected by the reference")
            cases.append(Case(pk, m2, s2, False, f"DV{tc}:{kind}"))

    assert len(cases) == 165, len(cases)
    return cases


def build_tr1_corpus():
    """The FIPS204-tr1 sigGen corpus: 120 ML-DSA-44 external-interface cases.

    A SECOND official key population, disjoint from everything else in this
    tree (asserted below), and the only place outside the keyGen shards where
    an official ACVP answer produces a MUST-ACCEPT at this interface: five of
    the sixty pure cases were generated with an empty context, which is exactly
    the interface both verifiers implement.  The other 55 pure cases and all 60
    preHash cases are must-reject, on context binding and on pure/preHash
    domain separation respectively — and each is confirmed to verify in the
    domain it was generated for before it is emitted as a rejection, so a
    "reject" here is a statement about domain separation and not about a
    corpus we failed to parse.
    """
    ml, _ = F.acvp_data()
    cases = []

    def check(cond, what):
        if not cond:
            raise SystemExit(f"acvp_build: ORACLE DISAGREEMENT — {what}")

    # ------------------------------------------------------------- TP (60)
    n_accept = 0
    for t in ml["tr1"]["pure"]:
        pk = bytes.fromhex(t["pk"])
        msg = bytes.fromhex(t["message"])
        sig = bytes.fromhex(t["signature"])
        ctx = bytes.fromhex(t["context"])
        kf = t.get("keyFormat", "?")
        # the official signature verifies in the domain it was generated for
        check(F.verify_pure(pk, msg, sig, ctx),
              f"tr1 pure tcId {t['tcId']} ({kf}): official signature must verify")
        exp = not ctx
        check(F.verify_pure(pk, msg, sig, b"") == exp,
              f"tr1 pure tcId {t['tcId']}: empty-ctx oracle != expected verdict")
        n_accept += exp
        lab = f"TP{t['tcId']}:{kf}" + ("" if exp else ":ctxbind")
        cases.append(Case(pk, msg, sig, exp, lab))

    # ------------------------------------------------------------- TH (60)
    for t in ml["tr1"]["preHash"]:
        pk = bytes.fromhex(t["pk"])
        msg = bytes.fromhex(t["message"])
        sig = bytes.fromhex(t["signature"])
        ctx = bytes.fromhex(t["context"])
        kf = t.get("keyFormat", "?")
        check(F.verify_prehash(pk, msg, sig, ctx, t["hashAlg"]),
              f"tr1 preHash tcId {t['tcId']} ({t['hashAlg']}): must verify in its own domain")
        check(not F.verify_pure(pk, msg, sig, ctx),
              f"tr1 preHash tcId {t['tcId']}: verified as pure ML-DSA (ctx)")
        check(not F.verify_pure(pk, msg, sig, b""),
              f"tr1 preHash tcId {t['tcId']}: verified as pure ML-DSA (empty ctx)")
        cases.append(Case(pk, msg, sig, False, f"TH{t['tcId']}:{kf}"))

    assert len(cases) == 120, len(cases)
    # THE POINT OF THIS CORPUS IS THAT ITS KEYS ARE NEW.  If a re-pin ever made
    # it overlap the corpus above, it would stop being breadth and start being
    # a second copy, so the disjointness is asserted rather than assumed.
    old_pks = {t["pk"] for b in ("sigVer", "sigGen") for k in ("pure", "preHash")
               for t in ml[b][k]}
    new_pks = {t["pk"] for k in ("pure", "preHash") for t in ml["tr1"][k]}
    if old_pks & new_pks:
        raise SystemExit(
            f"acvp_build: {len(old_pks & new_pks)} tr1 key(s) also appear in the "
            f"FIPS204 corpus; the at_* family is meant to be a DISJOINT key "
            f"population and is no longer one"
        )
    if n_accept != 5:
        raise SystemExit(
            f"acvp_build: tr1 pure must-accept count is {n_accept}, expected 5 "
            f"(the empty-context cases).  The corpus moved; re-adjudicate."
        )
    return cases


def _emit(prefix, cases, nshards):
    """Round-robin `cases` into `nshards` shards named `<prefix>k.hex`."""
    # deduplicated 20,544-byte pk payloads, memoised across shards
    pk_cache = {}
    for c in cases:
        if c.pk not in pk_cache:
            pk_cache[c.pk] = F.pk_blob(c.pk)

    for k, idxs in enumerate(F.round_robin(len(cases), nshards)):
        blobs, order, pkidx = [], {}, []
        for i in idxs:
            pk = cases[i].pk
            if pk not in order:
                order[pk] = len(blobs)
                blobs.append(pk_cache[pk])
            pkidx.append(order[pk])
        shard = (
            blobs,
            pkidx,
            [cases[i].msg for i in idxs],
            [cases[i].sig for i in idxs],
            [cases[i].exp for i in idxs],
            [cases[i].label for i in idxs],
        )
        F.write_shard(f"{prefix}{k}.hex", F.enc(SHARD_T, shard))


def build_all():
    _emit("ah_", build_corpus(), N_SHARDS)
    _emit("at_", build_tr1_corpus(), TR1_SHARDS)


if __name__ == "__main__":
    F.main(sys.argv, build_all, NAMES)
