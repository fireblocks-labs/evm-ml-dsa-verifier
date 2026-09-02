# Invoked as: pythonref/myenv/bin/python tools/fixtures/e2e_pk.py ...
"""
e2e_pk.py — vm.ffi public-key-blob generator for the ML-DSA-44 e2e tests.

CLI
---
  e2e_pk.py seed <seed_hex_64_chars_no_0x>
      Derive the key pair from `seed` exactly the way pythonref/sig_sol.py does
      in "NIST" mode (Dilithium2.key_derive(seed, _xof=shake256,
      _xof2=shake128)) and emit the blob for the resulting public key.

  e2e_pk.py pk <pk_hex_with_0x_prefix>
      Emit the blob for the given standard 1312-byte FIPS 204 ML-DSA-44 pk.

OUTPUT ABI (stdout, lower-case hex, no 0x prefix)
-------------------------------------------------
  the RAW 20,544-byte pk payload (NOT abi-encoded, and WITHOUT the leading
  0x00 byte that prepare/prepare.py prepends for EIP-3541 data-contract
  deployment — tests deploying for the shipped MLDSA44Verifier prepend it;
  tests for the in-tree reference verifier deploy these bytes verbatim and
  assert blob.length == E2E_PK_SIZE == 20544):

    [    0 ..    64)  tr    = SHAKE256(pk, 64)
    [   64 ..  4160)  t1hat = NTT((t1 << 13) mod q), 4 polys, 32 words each
    [ 4160 .. 20544)  Ahat  = ExpandA(rho) (NTT domain), 16 polys row-major
                              i*4 + j, 32 words each

  Word packing ("compact_256(32)"): word w of a poly holds coefficients
  8w..8w+7, coefficient (8w+s) at bit offset 32*s (LSB-first), serialised
  big-endian so a Solidity mload() of the word returns exactly that value.

Deterministic, offline, no network. The blob math is byte-identical to
prepare/prepare.py (which prepends the one 0x00 byte; this program does not).
"""
import importlib.util
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))  # repository root
PYREF = os.path.join(_ROOT, "pythonref")

sys.path.insert(0, PYREF)

_spec = importlib.util.spec_from_file_location(
    "mldsa_min", os.path.join(_ROOT, "prepare", "mldsa_min.py")
)
M = importlib.util.module_from_spec(_spec)
sys.modules["mldsa_min"] = M
_spec.loader.exec_module(M)

BLOB_SIZE = 20544  # 64 + 4*1024 + 16*1024, no 0x00 prefix


def compact32(coeffs):
    """32 words of 8 x 32-bit coefficient fields, big-endian serialised."""
    out = bytearray()
    for w in range(32):
        word = 0
        for s in range(8):
            word |= int(coeffs[8 * w + s]) << (32 * s)
        out += word.to_bytes(32, "big")
    return bytes(out)


def build(pk):
    rho, t1 = M.pk_decode(pk)
    a_hat = M.expand_a(rho)
    t1_hat = [M.ntt([(c << M.D) % M.Q for c in row]) for row in t1]

    blob = bytearray()
    blob += M.tr_of(pk)
    for i in range(4):
        blob += compact32(t1_hat[i])
    for i in range(4):
        for j in range(4):
            blob += compact32(a_hat[i][j])
    assert len(blob) == BLOB_SIZE, len(blob)
    return bytes(blob)


def derive_pk(seed):
    """pythonref/sig_sol.py "NIST" mode key derivation."""
    from dilithium_py.dilithium.default_parameters import Dilithium2 as D
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    pk, _sk = D.key_derive(seed, _xof=shake256, _xof2=shake128)
    return pk


def main(argv):
    if len(argv) >= 3 and argv[1] == "seed":
        pk = derive_pk(bytes.fromhex(argv[2].removeprefix("0x")))
    elif len(argv) >= 3 and argv[1] == "pk":
        pk = bytes.fromhex(argv[2].removeprefix("0x"))
    else:
        raise SystemExit(
            "usage: e2e_pk.py seed <seed_hex>  |  e2e_pk.py pk <0xpk_hex>"
        )
    if len(pk) != 1312:
        raise SystemExit(f"e2e_pk: pk must be 1312 bytes, got {len(pk)}")
    sys.stdout.write(build(pk).hex())


if __name__ == "__main__":
    main(sys.argv)
