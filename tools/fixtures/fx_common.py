"""
fx_common.py — shared plumbing for the in-repo fixture-shard builders
(acvp_build.py, fuzz_build.py, shake_build.py, wycheproof_build.py).

WHAT THIS MODULE PROVIDES
  * cached, distilled copies of the official NIST ACVP vector files
    (tools/fixtures/acvp_data/*.json, fetched once from usnistgov/ACVP-Server)
  * the on-chain public-key blob encoding used by the verifiers
      pk_blob(pk) -> 20,544 B  raw payload (prepare/prepare.py output minus its
                               leading 0x00 EIP-3541 prefix byte)
  * ABI encoding of the shard structs declared by the Solidity suites
  * an atomic, flock-serialised shard cache under test/fixtures/

The shards are pure functions of the inputs; every builder is deterministic.
"""

import errno
import fcntl
import hashlib
import importlib.util
import json
import os
import ssl
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path

# --------------------------------------------------------------------- paths

HERE = Path(__file__).resolve().parent  # tools/fixtures
FOUNDRY_ROOT = HERE.parents[1]  # repository root
FIXTURES = FOUNDRY_ROOT / "test" / "fixtures"
ACVP_DATA = HERE / "acvp_data"
PYTHONREF = FOUNDRY_ROOT / "pythonref"
PREPARE = FOUNDRY_ROOT / "prepare"

sys.path.insert(0, str(PYTHONREF))


def _load(name, path):
    """Import a module by absolute file path.

    Deliberately NOT `sys.path` based: the shard corpora must always be
    produced by the very module shipped in prepare/, never by a look-alike
    that happens to be first on sys.path.
    """
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


M = _load("mldsa_min", PREPARE / "mldsa_min.py")

from eth_abi import encode as abi_encode  # noqa: E402
from dilithium_py.dilithium.default_parameters import Dilithium2 as D  # noqa: E402
from dilithium_py.shake.shake_wrapper import shake128, shake256  # noqa: E402

Q = M.Q
GAMMA1 = M.GAMMA1
BETA = M.BETA
OMEGA = M.OMEGA
SIG_LEN = 2420
PK_LEN = 1312
PK_BLOB = 20544

# ------------------------------------------------------------ ACVP provenance
#
# The FIVE upstream files are the ones named verbatim in the headers of
# test/ACVP_MLDSA44.t.sol and test/FUZZ_Shake.t.sol.  They are fetched once,
# distilled down to the ML-DSA-44 / byte-aligned-SHAKE-256 subset the suites
# actually use, and the distilled JSON is kept in tools/fixtures/acvp_data/ so
# that regeneration is offline and reproducible afterwards.
#
# EACH ENTRY CARRIES ITS SHA-256, AND `_fetch` CHECKS IT.  A digest merely
# COMPUTED at fetch time and RECORDED in the distilled JSON's `_provenance`,
# with nothing ever comparing it to anything, would make "pinned" mean only
# "written down".  Every corpus in this repository that an auditor is asked to
# trust (Wycheproof, the ACVP keyGen set) verifies its digest BEFORE use, and
# this one does too: a re-fetch that returns different bytes is a hard
# error naming both digests, not a silently different corpus.
#
# THE COUNT IN THE SENTENCE ABOVE IS A CHECKED NUMBER, not prose: a stale
# "four" left behind by the addition of `ML-DSA-sigGen-FIPS204-tr1` would be
# the same class of drift as every other published count in this tree.
# `_ACVP_FILE_COUNT` is asserted against `len(ACVP_FILES)` in
# `acvp_data()`, so adding or removing a projection without updating the
# sentence is a hard error rather than a stale word.
_ACVP_FILE_COUNT = 5   # keep in step with "FIVE" above
ACVP_BASE = "https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/json-files"
ACVP_FILES = {
    "ML-DSA-sigVer-FIPS204": {
        "url": f"{ACVP_BASE}/ML-DSA-sigVer-FIPS204/internalProjection.json",
        "sha256": "47cdd6314c7f746d02421ffcba89d4dbc7bb875ac49e07a029fdfc26fba55437",
    },
    "ML-DSA-sigGen-FIPS204": {
        "url": f"{ACVP_BASE}/ML-DSA-sigGen-FIPS204/internalProjection.json",
        "sha256": "72dcaf5f69853ca267ccd16af9cb40949786aca0fcfbf05d1ebeba132b93af22",
    },
    # FIPS204-tr1: the technical-corrigendum-1 sigGen projection.  A SEPARATE
    # corpus, not a newer revision of the one above -- 120 ML-DSA-44
    # external-interface cases (60 pure + 60 preHash) on 120 keys that appear
    # nowhere else in this tree, in both `keyFormat` presentations (`seed` and
    # `expanded`).  See `_distill_mldsa`, which dispatches on the document's
    # own `revision` field rather than on this key.
    "ML-DSA-sigGen-FIPS204-tr1": {
        "url": f"{ACVP_BASE}/ML-DSA-sigGen-FIPS204-tr1/internalProjection.json",
        "sha256": "b61576c765b1eb0e6a667a67a68380df944592be8740f9c020c9ea5a89136f18",
    },
    "SHAKE-256-FIPS202": {
        "url": f"{ACVP_BASE}/SHAKE-256-FIPS202/internalProjection.json",
        "sha256": "a9348d17e009cad62a2baa70160353f5bca936a27116f60dd5811f39b91c6991",
    },
    "SHAKE-256-1.0": {
        "url": f"{ACVP_BASE}/SHAKE-256-1.0/internalProjection.json",
        "sha256": "94d0992ed2acbebe45f359cb1ffaceaf881a170339935ba9d2d36c8388005d26",
    },
}


def _log(*a):
    print(*a, file=sys.stderr)


def _fetch(name):
    """Fetch one upstream ACVP file over HTTPS with certificate verification ON.

    Some interpreters here ship without a CA bundle, which makes urllib raise
    SSLCertVerificationError; in that case we shell out to curl, which uses the
    system trust store.  TLS verification is never disabled (no -k / no
    ssl._create_unverified_context) — a failure to verify is a hard error.
    """
    url = ACVP_FILES[name]["url"]
    _log(f"[fx] fetching {url}")
    try:
        with urllib.request.urlopen(url, timeout=300) as r:  # noqa: S310 (fixed https URL)
            raw = r.read()
    except urllib.error.URLError as e:
        if not isinstance(getattr(e, "reason", None), ssl.SSLCertVerificationError):
            raise
        _log("[fx] urllib has no CA bundle; retrying with curl (verification on)")
        raw = subprocess.run(
            ["curl", "--fail", "--silent", "--show-error", "--location",
             "--proto", "=https", "--tlsv1.2", "--max-time", "300", url],
            check=True, stdout=subprocess.PIPE,
        ).stdout
    got = hashlib.sha256(raw).hexdigest()
    want = ACVP_FILES[name]["sha256"]
    if got != want:
        raise SystemExit(
            f"fx_common: {name}: upstream sha256 {got} != pinned {want} "
            f"({url}).  The ACVP projection moved.  Review the diff, then update "
            f"ACVP_FILES and delete tools/fixtures/acvp_data/*.json to re-distil; "
            f"refusing to build fixtures from an unreviewed corpus."
        )
    return raw, got


# The document revisions this distiller knows how to read.  `_distill_mldsa`
# dispatches on the projection's OWN `revision` field and REFUSES an unknown
# one, so a corpus that upstream re-cuts under a new revision cannot be
# distilled by rules written for the old one.
_MLDSA_REVISIONS = {"FIPS204", "FIPS204-tr1"}


def _distill_mldsa(raw_sigver, raw_siggen, raw_tr1):
    """Keep only the ML-DSA-44 external-interface groups (pure + preHash).

    Three projections, TWO revisions.  `FIPS204` is the original sigVer/sigGen
    pair.  `FIPS204-tr1` is the technical-corrigendum-1 sigGen projection: a
    separate corpus on its own keys, cut into four groups per preHash mode by
    `keyFormat` (`seed` / `expanded`) and `deterministic`.  `keyFormat` is a
    KEY-GENERATION presentation and does not change what a verifier sees --
    both formats hand us a 1,312-byte `pk` and a 2,420-byte `signature` -- so
    it is carried through as a label rather than branched on, and the tr1
    records are kept in their own bucket so no caller can mistake them for the
    corpus whose `testPassed` verdicts drive the sigVer expectations.
    """

    def grab(doc, iface, prehash, with_sk):
        out = []
        for g in doc["testGroups"]:
            if g["parameterSet"] != "ML-DSA-44":
                continue
            if g.get("signatureInterface") != iface or g.get("preHash") != prehash:
                continue
            for t in g["tests"]:
                rec = {
                    "tcId": int(t["tcId"]),
                    "tgId": int(g["tgId"]),
                    "pk": t["pk"],
                    "message": t["message"],
                    "signature": t["signature"],
                    "context": t.get("context", ""),
                    "hashAlg": t.get("hashAlg", "none"),
                }
                if "testPassed" in t:
                    rec["testPassed"] = bool(t["testPassed"])
                if "reason" in t:
                    rec["reason"] = t["reason"]
                # tr1 splits every (preHash, deterministic) pair by keyFormat;
                # record which presentation the case came from.
                if "keyFormat" in g:
                    rec["keyFormat"] = g["keyFormat"]
                if with_sk:
                    rec["sk"] = t["sk"]
                out.append(rec)
        return out

    def revision_of(doc, name):
        rev = doc.get("revision")
        if rev not in _MLDSA_REVISIONS:
            raise SystemExit(
                f"fx_common: {name}: revision {rev!r} is not one this distiller "
                f"knows ({sorted(_MLDSA_REVISIONS)}); the projection was re-cut "
                f"upstream and the distillation rules must be re-reviewed"
            )
        return rev

    sv = json.loads(raw_sigver)
    sg = json.loads(raw_siggen)
    tr = json.loads(raw_tr1)
    for doc, name, want in ((sv, "ML-DSA-sigVer-FIPS204", "FIPS204"),
                            (sg, "ML-DSA-sigGen-FIPS204", "FIPS204"),
                            (tr, "ML-DSA-sigGen-FIPS204-tr1", "FIPS204-tr1")):
        got = revision_of(doc, name)
        if got != want:
            raise SystemExit(f"fx_common: {name}: revision {got!r}, expected {want!r}")
    return {
        "sigVer": {
            # sk is kept only here: the DV category re-signs the official
            # sigVer key material with an empty context.
            "pure": grab(sv, "external", "pure", True),
            "preHash": grab(sv, "external", "preHash", False),
        },
        "sigGen": {
            "pure": grab(sg, "external", "pure", False),
            "preHash": grab(sg, "external", "preHash", False),
        },
        "tr1": {
            "pure": grab(tr, "external", "pure", False),
            "preHash": grab(tr, "external", "preHash", False),
        },
    }


def _distill_shake(raws):
    """Byte-aligned SHAKE-256 AFT/VOT cases only (the EVM XOF is byte-oriented).

    Bit-length cases (len % 8 or outLen % 8) are not expressible on-chain and
    are skipped; MCT groups are skipped (they are a chained self-test, not a
    KAT).  Every retained md is re-derived with hashlib before it is kept.
    """
    out = []
    skipped = 0
    for name, raw in raws:
        doc = json.loads(raw)
        for g in doc["testGroups"]:
            if g["testType"] == "MCT":
                continue
            for t in g["tests"]:
                nbits, obits = int(t["len"]), int(t["outLen"])
                if nbits % 8 or obits % 8:
                    skipped += 1
                    continue
                msg = b"" if nbits == 0 else bytes.fromhex(t["msg"])
                md = bytes.fromhex(t["md"])
                assert len(msg) * 8 == nbits and len(md) * 8 == obits, t["tcId"]
                assert hashlib.shake_256(msg).digest(len(md)) == md, (name, t["tcId"])
                out.append(
                    {
                        "src": f"{name}/{g['testType']}",
                        "tcId": int(t["tcId"]),
                        "msg": msg.hex(),
                        "outLen": len(md),
                        "md": md.hex(),
                    }
                )
    return {"skippedBitOriented": skipped, "vectors": out}


# ------------------------------------------------ the DISTILLED files' digests
#
# THE PINS ABOVE GUARD A PATH A NORMAL CHECKOUT NEVER TAKES.  `_fetch` is the
# only place an `ACVP_FILES` digest is compared, and `acvp_data()` returns the
# TRACKED distilled files whenever they exist -- which they always do in a
# checkout -- so on an ordinary run, and in CI, those pins alone would check no
# digest at all.  The residual would be small, because every builder
# re-derives its verdicts from an independent oracle and hard-asserts the corpus
# sizes; but what would go unpinned is PROVENANCE, that these bytes are NIST's
# rather than merely self-consistent, and that is exactly what "official NIST
# ACVP vectors pass on-chain" rests on.
#
# So the distilled files carry their own SHA-256 and it is verified BEFORE they
# are returned, on every build -- the same discipline
# `wycheproof_build._load()` applies to the file IT actually reads.  The digests
# are over the bytes on disk; regenerate by deleting
# tools/fixtures/acvp_data/*.json, re-running any builder with network access
# (which re-fetches, and THEN the `ACVP_FILES` pins bite), and pasting the new
# values printed below.
ACVP_DISTILLED_SHA256 = {
    "mldsa44.json": "5f1916a17955140869d4320fb5f47f2cca5a4225db786a3316eb7d8cdf1eb7ab",
    "shake256.json": "24fd077fbdb7fd9618cdf4f77513229f7634fd544f9fd93a0bda5838ee0fe9ff",
}


def _verify_distilled(path):
    """Refuse a distilled corpus whose bytes are not the pinned ones."""
    raw = path.read_bytes()
    got = hashlib.sha256(raw).hexdigest()
    want = ACVP_DISTILLED_SHA256[path.name]
    if got != want:
        raise SystemExit(
            f"fx_common: {path} SHA-256 mismatch\n"
            f"  expected {want}\n  got      {got}\n"
            f"  The distilled ACVP corpus is not the reviewed one.  Its provenance "
            f"is the whole basis of the 'official NIST ACVP vectors' claim, so this "
            f"is a hard error.  To re-derive: delete tools/fixtures/acvp_data/*.json "
            f"and re-run a builder with network access (the ACVP_FILES pins are "
            f"checked on the fetch), then update ACVP_DISTILLED_SHA256."
        )
    return raw


def acvp_data():
    """Return the distilled ACVP corpus, fetching + distilling on first use."""
    if len(ACVP_FILES) != _ACVP_FILE_COUNT:
        raise SystemExit(
            f"fx_common: ACVP_FILES holds {len(ACVP_FILES)} projections, but this "
            f"module's prose and _ACVP_FILE_COUNT say {_ACVP_FILE_COUNT}"
        )
    mldsa_p = ACVP_DATA / "mldsa44.json"
    shake_p = ACVP_DATA / "shake256.json"
    if mldsa_p.exists() and shake_p.exists():
        # PROVENANCE IS CHECKED ON THE PATH ACTUALLY TAKEN, not only on the
        # re-fetch path nobody runs.
        return (json.loads(_verify_distilled(mldsa_p)),
                json.loads(_verify_distilled(shake_p)))

    ACVP_DATA.mkdir(parents=True, exist_ok=True)
    prov = {}
    raws = {}
    for n in ACVP_FILES:
        raws[n], prov[n] = _fetch(n)

    mldsa = _distill_mldsa(raws["ML-DSA-sigVer-FIPS204"],
                           raws["ML-DSA-sigGen-FIPS204"],
                           raws["ML-DSA-sigGen-FIPS204-tr1"])
    shake = _distill_shake(
        [(n, raws[n]) for n in ("SHAKE-256-FIPS202", "SHAKE-256-1.0")]
    )
    mldsa["_provenance"] = {
        k: {"url": ACVP_FILES[k]["url"], "sha256": prov[k]}
        for k in ("ML-DSA-sigVer-FIPS204", "ML-DSA-sigGen-FIPS204",
                  "ML-DSA-sigGen-FIPS204-tr1")
    }
    shake["_provenance"] = {
        k: {"url": ACVP_FILES[k]["url"], "sha256": prov[k]}
        for k in ("SHAKE-256-FIPS202", "SHAKE-256-1.0")
    }
    _atomic_write(mldsa_p, json.dumps(mldsa, indent=1))
    _atomic_write(shake_p, json.dumps(shake, indent=1))
    return mldsa, shake


# ---------------------------------------------------------- pk / hint  blobs


def _compact32(coeffs):
    """32 words of 8 x 32-bit coefficient fields, big-endian serialised
    (identical to prepare/prepare.py::compact32)."""
    out = bytearray()
    for w in range(32):
        word = 0
        for s in range(8):
            word |= int(coeffs[8 * w + s]) << (32 * s)
        out += word.to_bytes(32, "big")
    return bytes(out)


def pk_blob(pk):
    """20,544-byte RAW pk payload (code == blob for test/ZZZ_E2ERef.sol).

    Identical to prepare/prepare.py minus its leading 0x00 byte (the shipped
    MLDSA44Verifier reads 0x00 || blob from a CREATEd data contract per
    EIP-3541; tests prepend the prefix where they deploy for it).
      [    0 ..    64)  tr = SHAKE256(pk, 64)
      [   64 ..  4160)  t1hat = NTT((t1 << 13) mod q), rows 0..3
      [ 4160 .. 20544)  Ahat  = ExpandA(rho), 16 polys row-major i*4+j
    """
    rho, t1 = M.pk_decode(pk)
    a_hat = M.expand_a(rho)
    t1_hat = [M.ntt([(c << M.D) % Q for c in row]) for row in t1]
    blob = bytearray(M.tr_of(pk))
    for i in range(4):
        blob += _compact32(t1_hat[i])
    for i in range(4):
        for j in range(4):
            blob += _compact32(a_hat[i][j])
    assert len(blob) == PK_BLOB, len(blob)
    return bytes(blob)


# ------------------------------------------------------------- oracle helpers


def verify_pure(pk, m, sig, ctx=b""):
    """FIPS 204 pure ML-DSA-44 verification through the pythonref oracle."""
    if len(sig) != SIG_LEN or len(pk) != PK_LEN or len(ctx) > 255:
        return False
    try:
        return bool(D.verify(pk, m, sig, ctx=ctx))
    except (ValueError, IndexError, AssertionError):
        return False


# FIPS 204 §5.4 pre-hash OIDs (DER, 11 bytes) and digest lengths.
PH_OID = {
    "SHA2-256": (bytes.fromhex("0609608648016503040201"), 32),
    "SHA2-384": (bytes.fromhex("0609608648016503040202"), 48),
    "SHA2-512": (bytes.fromhex("0609608648016503040203"), 64),
    "SHA2-224": (bytes.fromhex("0609608648016503040204"), 28),
    "SHA2-512/224": (bytes.fromhex("0609608648016503040205"), 28),
    "SHA2-512/256": (bytes.fromhex("0609608648016503040206"), 32),
    "SHA3-224": (bytes.fromhex("0609608648016503040207"), 28),
    "SHA3-256": (bytes.fromhex("0609608648016503040208"), 32),
    "SHA3-384": (bytes.fromhex("0609608648016503040209"), 48),
    "SHA3-512": (bytes.fromhex("060960864801650304020A"), 64),
    "SHAKE-128": (bytes.fromhex("060960864801650304020B"), 32),
    "SHAKE-256": (bytes.fromhex("060960864801650304020C"), 64),
}


def _ph_digest(alg, m):
    oid, n = PH_OID[alg]
    if alg == "SHAKE-128":
        return oid, hashlib.shake_128(m).digest(n)
    if alg == "SHAKE-256":
        return oid, hashlib.shake_256(m).digest(n)
    h = {
        "SHA2-224": "sha224",
        "SHA2-256": "sha256",
        "SHA2-384": "sha384",
        "SHA2-512": "sha512",
        "SHA2-512/224": "sha512_224",
        "SHA2-512/256": "sha512_256",
        "SHA3-224": "sha3_224",
        "SHA3-256": "sha3_256",
        "SHA3-384": "sha3_384",
        "SHA3-512": "sha3_512",
    }[alg]
    return oid, hashlib.new(h, m).digest()


def verify_prehash(pk, m, sig, ctx, alg):
    """HashML-DSA verification: M' = 0x01 || |ctx| || ctx || OID || PH(M)."""
    if len(sig) != SIG_LEN or len(ctx) > 255:
        return False
    oid, dg = _ph_digest(alg, m)
    mp = bytes([1, len(ctx)]) + ctx + oid + dg
    try:
        return bool(D._verify_internal(pk, mp, sig))
    except (ValueError, IndexError, AssertionError):
        return False


def rnd(tag, n):
    """Deterministic pseudorandom bytes (all fixture randomness comes from here)."""
    return hashlib.shake_256(b"evm-ml-dsa-verifier/fixtures/" + tag).digest(n)


# --------------------------------------------------------------- shard tuples
#
# Field order below MUST match the Solidity struct declarations verbatim —
# abi.decode is positional.

HON_SHARD_T = "(bytes[],uint256[],bytes[],bytes[],bool[],string[])"
FUZZ_SHARD_T = "(bytes[],bytes[],bytes[],uint256[],bytes[],bytes[],bytes[],bool[],bool[],string[])"
SHAKE_SHARD_T = "(bytes[],uint256[],bytes[],string[])"


def enc(type_str, value):
    return abi_encode([type_str], [value]).hex()


def split(n, k):
    """numpy.array_split-style contiguous split of range(n) into k chunks."""
    base, rem = divmod(n, k)
    out, i = [], 0
    for s in range(k):
        m = base + (1 if s < rem else 0)
        out.append(list(range(i, i + m)))
        i += m
    return out


def round_robin(n, k):
    """shard s := every index i with i % k == s (keeps every category evenly
    represented in every shard; sizes are identical to split())."""
    return [[i for i in range(n) if i % k == s] for s in range(k)]


# ------------------------------------------------------------- shard cache IO


def _atomic_write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + f".tmp{os.getpid()}")
    tmp.write_text(text)
    tmp.replace(path)


def write_shard(name, hexstr):
    _atomic_write(FIXTURES / name, hexstr)
    _log(f"[fx] wrote {name} ({len(hexstr) // 2} bytes)")


def serve(name, build_all, names):
    """Print the cached shard `name`, building the whole family on first use.

    A flock on test/fixtures/.build.lock serialises concurrent forge workers so
    the corpus is generated exactly once.
    """
    if name not in names:
        raise SystemExit(f"unknown shard {name!r}; known: {' '.join(names)}")
    target = FIXTURES / name
    if not target.exists():
        FIXTURES.mkdir(parents=True, exist_ok=True)
        lock = FIXTURES / ".build.lock"
        with open(lock, "a+") as fh:
            try:
                fcntl.flock(fh, fcntl.LOCK_EX)
            except OSError as e:  # pragma: no cover
                if e.errno != errno.ENOLCK:
                    raise
            if not target.exists():
                build_all()
    if not target.exists():
        raise SystemExit(f"builder did not produce {name}")
    sys.stdout.write(target.read_text())


def main(argv, build_all, names):
    """CLI: `<builder>.py <shard-name>` prints one shard (building on demand);
    `<builder>.py --build` (re)builds every shard of the family."""
    if len(argv) == 2 and argv[1] in ("--build", "-b"):
        build_all()
        return
    if len(argv) != 2:
        raise SystemExit(f"usage: {argv[0]} <shard-name>|--build   ({' '.join(names)})")
    serve(argv[1], build_all, names)
