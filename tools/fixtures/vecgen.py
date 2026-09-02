# Invoked as: pythonref/myenv/bin/python tools/fixtures/vecgen.py ...
"""
vecgen.py — vm.ffi (signature, pk blob, message) vector generator for the
ML-DSA-44 test suites.

CLI
---
  vecgen.py seed <seed_hex_64_chars_no_0x> <msg_hex_with_0x_prefix>
      Derive the ML-DSA-44 key pair from `seed` exactly the way
      pythonref/sig_sol.py does in "NIST" mode
      (Dilithium2.key_derive(seed, _xof=shake256, _xof2=shake128)), sign the
      message deterministically (rnd = 0^32, ctx = b"") and emit the fixture.

  vecgen.py kat
      Reproduce, bit-exactly, the NIST KAT vector: provenance
      pythonref/dilithium_py/generate_KAT_example.py — AES-256-CTR-DRBG seeded
      with bytes(range(48)), 48-byte seed then a 33-byte message drawn from it,
      Dilithium2.set_drbg_seed(seed) + keygen() + sign(sk, msg) (NIST xofs,
      count 0 of pythonref/assets/PQCsignKAT_Dilithium2.rsp).

OUTPUT ABI (stdout, lower-case hex, no 0x prefix)
-------------------------------------------------
  abi.encode(bytes sig, bytes pkBlob, bytes msg)

    sig     2,420 bytes — standard FIPS 204 sigma = c~ || zEncode(z) || hEncode(h)
    pkBlob 20,544 bytes — raw pk payload, identical to prepare/prepare.py minus
            its leading 0x00 EIP-3541 prefix byte (tests deploying for the
            shipped MLDSA44Verifier prepend the prefix; the in-tree reference
            verifier consumes these bytes verbatim as contract code)
    msg     the raw message bytes (decoded from the hex argument)

Deterministic, offline, no network.
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))  # repository root
PYREF = os.path.join(_ROOT, "pythonref")

sys.path.insert(0, _HERE)
sys.path.insert(0, PYREF)

from eth_abi import encode as abi_encode  # noqa: E402

import e2e_pk  # noqa: E402  (shares the blob builder + mldsa_min loading)


def derive_keypair(seed):
    """pythonref/sig_sol.py "NIST" mode: Dilithium2.key_derive with SHAKE xofs."""
    from dilithium_py.dilithium.default_parameters import Dilithium2 as D
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    return D.key_derive(seed, _xof=shake256, _xof2=shake128)


def sign_nist(sk, msg):
    """pythonref/sig_sol.py "NIST" mode: deterministic FIPS 204 sign, ctx = b""."""
    from dilithium_py.dilithium.default_parameters import Dilithium2 as D
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    return D.sign(sk, msg, deterministic=True, _xof=shake256, _xof2=shake128)


def kat_vector():
    """Reproduce generate_KAT_example.py count 0 -> (pk, msg, sig)."""
    from dilithium_py.dilithium.default_parameters import Dilithium2 as D
    from dilithium_py.drbg.aes256_ctr_drbg import AES256_CTR_DRBG
    from dilithium_py.shake.shake_wrapper import shake256

    with open(os.path.join(PYREF, "assets", "PQCsignKAT_Dilithium2.rsp")) as fh:
        blocks = fh.read().split("\n\n")[1:-1]
    # "count = 0" block: count, seed, mlen, msg, pk, sk, smlen, sm
    fields = [line.split(" = ")[-1] for line in blocks[0].split("\n")]
    mlen = int(fields[2])

    drbg = AES256_CTR_DRBG(bytes(range(48)))
    seed = drbg.random_bytes(48)
    msg = drbg.random_bytes(mlen)

    D.set_drbg_seed(seed)
    pk, sk = D.keygen()
    sig = D.sign(sk, msg, _xof=shake256)
    if not D.verify(pk, msg, sig, _xof=shake256):
        raise SystemExit("vecgen: reproduced KAT vector does not verify")
    return pk, msg, sig


def emit(sig, pk_blob, msg):
    sys.stdout.write(
        abi_encode(["bytes", "bytes", "bytes"], [sig, pk_blob, msg]).hex()
    )


def main(argv):
    if len(argv) >= 2 and argv[1] == "kat":
        pk, msg, sig = kat_vector()
    elif len(argv) >= 4 and argv[1] == "seed":
        seed = bytes.fromhex(argv[2].removeprefix("0x"))
        msg = bytes.fromhex(argv[3].removeprefix("0x"))
        pk, sk = derive_keypair(seed)
        sig = sign_nist(sk, msg)
    else:
        raise SystemExit(
            "usage: vecgen.py seed <seed_hex> <0xmsg_hex>  |  vecgen.py kat"
        )

    if len(sig) != 2420:
        raise SystemExit(f"vecgen: signature must be 2420 bytes, got {len(sig)}")
    emit(sig, e2e_pk.build(pk), msg)


if __name__ == "__main__":
    main(sys.argv)
