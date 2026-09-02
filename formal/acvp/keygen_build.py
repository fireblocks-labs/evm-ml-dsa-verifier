#!/usr/bin/env python3
"""
keygen_build.py — on-chain fixture for the NIST ACVP **ML-DSA-keyGen** corpus.

    (run by vm.ffi, cwd = repository root)
    pythonref/myenv/bin/python formal/acvp/keygen_build.py kg_0

WHY THIS EXISTS
---------------
`test/ACVP_MLDSA44.t.sol` exercises the ACVP **sigVer** and **sigGen** corpora.
It does not touch **keyGen**, so the off-chain public-key transform (the pk
data contract: tr ‖ t1hat = NTT(2^d·t1) ‖ Ahat = ExpandA(rho)) had only ever
been built from the 15 distinct public keys that appear in sigVer.  The keyGen
corpus supplies **25 further official ML-DSA-44 key pairs**, each with the
seed, so every one can be re-signed and verified on chain: 25 more independent
exercises of ExpandA, the NTT, the t1 unpacking and the tr computation, on
NIST key material rather than on locally generated keys.

Exact counts (measured, not quoted) are printed by `--stats`:
  ML-DSA-44 keyGen AFT cases in the ACVP corpus : 25
  used here                                     : 25   (all of them)

OUTPUT — one hex blob (no 0x) on stdout per 5-case shard, ABI-encoded as

    (bytes[] pkBlobs, bytes[] msgs, bytes[] sigs, string[] labels)

so both in-tree subjects — the reference verifier test/ZZZ_E2ERef.sol and the
shipped src/MLDSA44Verifier.sol — can be driven from the same fixture (the
pkBlobs are the 20,544-byte payloads; the test prepends the 0x00 EIP-3541
prefix where it deploys for the shipped verifier).  Every case is first
checked against the `dilithium_py` reference oracle here; a disagreement
aborts the build rather than producing a fixture that encodes a wrong verdict.

PROVENANCE — the ACVP JSON is cached in `formal/acvp/data/mldsa_keygen.json`
with its SHA-256 recorded in `provenance.json` (both committed).  The cached
corpus is a trust root for 25 on-chain fixtures, so its digest is verified
against provenance.json on EVERY run; a mismatch refuses to build.  It is
fetched once over HTTPS if absent (TLS verification on).
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent  # formal/acvp
DATA = HERE / "data"
REPO = HERE.parents[1]  # repository root
FIXTOOLS = REPO / "tools" / "fixtures"
URL = ("https://raw.githubusercontent.com/usnistgov/ACVP-Server/master/gen-val/"
       "json-files/ML-DSA-keyGen-FIPS204/internalProjection.json")

sys.path.insert(0, str(FIXTOOLS))
sys.path.insert(0, str(REPO / "pythonref"))


N_KEYGEN_CASES = 25          # ML-DSA-44 keyGen AFT cases in the ACVP corpus


def _fetch():
    DATA.mkdir(parents=True, exist_ok=True)
    p = DATA / "mldsa_keygen.json"
    if p.exists():
        # The cached corpus is a TRUST ROOT for 25 on-chain fixtures: verify it
        # against the sha256 recorded in provenance.json, or refuse — a fixture
        # built from a doctored corpus encodes a wrong verdict everywhere it is
        # used.
        raw = p.read_bytes()
        prov = json.loads((DATA / "provenance.json").read_text())
        got = hashlib.sha256(raw).hexdigest()
        if got != prov["sha256"]:
            raise SystemExit(f"keygen_build: ACVP corpus digest {got} != recorded "
                             f"{prov['sha256']} in provenance.json — REFUSING to "
                             "build fixtures from an unverified corpus")
        return json.loads(raw)
    # one-time fetch; curl uses the system trust store (TLS verification ON,
    # https enforced) because the venv's Python ships without a CA bundle
    raw = subprocess.run(["curl", "--fail", "--silent", "--show-error", "--location",
                          "--proto", "=https", "--tlsv1.2", "--max-time", "300", URL],
                         capture_output=True, check=True).stdout
    doc = json.loads(raw)
    p.write_bytes(raw)
    (DATA / "provenance.json").write_text(json.dumps({
        "url": URL, "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
    }, indent=1))
    return doc


def cases():
    """Every ML-DSA-44 keyGen AFT case, in corpus order."""
    doc = _fetch()
    out = []
    for g in doc["testGroups"]:
        if g.get("parameterSet") != "ML-DSA-44":
            continue
        for t in g["tests"]:
            out.append(dict(tcId=int(t["tcId"]), tgId=int(g["tgId"]),
                            seed=bytes.fromhex(t["seed"]),
                            pk=bytes.fromhex(t["pk"]),
                            sk=bytes.fromhex(t["sk"])))
    # The case COUNT is an assertion, not a print: a corpus silently truncated
    # to one case would otherwise still produce a green fixture build and a
    # green on-chain suite over one key pair.
    if len(out) != N_KEYGEN_CASES:
        raise SystemExit(f"keygen_build: {len(out)} ML-DSA-44 keyGen AFT cases, "
                         f"expected exactly {N_KEYGEN_CASES}")
    return out


N_SHARDS = 5


def build(shard):
    import fx_common as F
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    cs = [c for i, c in enumerate(cases()) if i % N_SHARDS == shard]
    pkBlobs, msgs, sigs, labels = [], [], [], []
    for c in cs:
        # (a) the official (seed -> pk, sk) derivation must reproduce exactly
        pk, sk = F.D.key_derive(c["seed"], _xof=shake256, _xof2=shake128)
        if pk != c["pk"] or sk != c["sk"]:
            raise SystemExit(f"keygen_build: ORACLE DISAGREEMENT — tcId {c['tcId']}: "
                             "seed does not reproduce the official (pk, sk)")
        # (b) sign a fixed message with the official sk, empty context
        msg = hashlib.sha256(b"acvp-keygen/" + c["seed"]).digest()
        sig = F.D.sign(sk, msg, ctx=b"", deterministic=True,
                       _xof=shake256, _xof2=shake128)
        if not F.verify_pure(pk, msg, sig, b""):
            raise SystemExit(f"keygen_build: ORACLE DISAGREEMENT — tcId {c['tcId']}: "
                             "reference verify rejected its own signature")
        pkBlobs.append(F.pk_blob(pk))
        msgs.append(msg)
        sigs.append(sig)
        labels.append(f"KG{c['tcId']}")
    return F.enc("(bytes[],bytes[],bytes[],string[])", (pkBlobs, msgs, sigs, labels))


def main(argv):
    if len(argv) > 1 and argv[1] == "--stats":
        cs = cases()
        prov = json.loads((DATA / "provenance.json").read_text())
        print(f"ML-DSA-44 keyGen AFT cases: {len(cs)}/{N_KEYGEN_CASES} "
              f"(count asserted, corpus digest verified against provenance.json)")
        print(f"tcIds: {cs[0]['tcId']}..{cs[-1]['tcId']}")
        print(f"source: {prov['url']}\nsha256: {prov['sha256']}")
        return 0
    name = argv[1] if len(argv) > 1 else "kg_0"
    if not name.startswith("kg_"):
        raise SystemExit(f"unknown fixture {name!r}")
    shard = int(name[3:].removesuffix(".hex"))
    if not 0 <= shard < N_SHARDS:
        raise SystemExit(f"shard out of range: {shard}")
    import fx_common as F
    out = F.FIXTURES / f"kg_acvp_{shard}.hex"
    if out.exists():
        sys.stdout.write(out.read_text().strip())
        return 0
    hexstr = build(shard)
    F._atomic_write(out, hexstr)
    sys.stdout.write(hexstr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
