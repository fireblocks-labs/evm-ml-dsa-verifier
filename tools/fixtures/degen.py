# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
# Invoked as: pythonref/myenv/bin/python tools/fixtures/degen.py ...
"""
degen.py — the DEGENERATE ML-DSA-44 public key t1 = 0 fixture, for which anybody
can forge a signature on any message with no secret key at all.

Consumed by test/SEC_pkcache.t.sol
(test_degenerate_key_cache_forgery_accepted_by_both_and_by_FIPS, and
test_proof_of_possession_does_not_reject_a_degenerate_key, which passes a
REGISTRAR-CHOSEN challenge as the message).

CLI
---
  degen.py <seed_hex_64_chars_no_0x> <msg_hex_with_0x_prefix>

OUTPUT ABI (stdout, lower-case hex, no 0x prefix)
-------------------------------------------------
  abi.encode(bytes pkBlob, bytes sig, bytes pk, bool fipsOk)

    pkBlob 20,544 bytes — the on-chain cache for the degenerate key, WITHOUT the
                          leading 0x00 EIP-3541 prefix (identical layout to
                          e2e_pk.py): tr = SHAKE256(pk, 64), t1hat = 0, and
                          Ahat = ExpandA(rho) the GENUINE, non-zero image. The
                          shipped verifier's deploying test prepends the 0x00
                          byte; the reference verifier consumes these bytes
                          verbatim as contract code.
    sig     2,420 bytes — the forged sigma (see WHY IT WORKS below).
    pk      1,312 bytes — the standard FIPS 204 pk = rho || pkEncode(t1 = 0).
    fipsOk       bool   — the ACTUAL verdict of the reference FIPS 204 verifier
                          (dilithium_py Dilithium2.verify) on (pk, msg, sig).
                          Measured, never hardcoded.

WHY IT WORKS (FIPS 204 Algorithm 3, ML-DSA.Verify)
--------------------------------------------------
With t1 = 0 the public key contributes nothing to w'_approx:

    w'_approx = A z - c * (t1 << d) = A z - 0 = A z

so choosing z = 0 (in range: ||z||inf = 0 < gamma1 - beta = 130994) gives
w'_approx = 0 regardless of A and c. With the hint vector h = 0 (84 zero bytes
is a VALID HintBitUnpack encoding: all counts 0, all padding 0),

    w1 = UseHint(h = 0, w'_approx = 0) = HighBits(0) = 0   =>   w1Encode(w1) = 0^768

is a FIXED value the forger knows, so the challenge can simply be COMPUTED:

    tr  = SHAKE256(pk, 64)
    mu  = SHAKE256(tr || 0x00 || 0x00 || M, 64)             (ctx = b"")
    c~  = SHAKE256(mu || w1Encode(0), 32)
    sigma = c~ || zEncode(z = 0) || hEncode(h = 0)

and the verifier's final comparison c~ == SHAKE256(mu || w1Encode(w1)) holds by
construction. zEncode of z = 0 puts the raw value gamma1 = 2^17 in every 18-bit
field.

This is ML-DSA's well-known lack of key-substitution / exclusive-ownership
robustness, NOT a bug in the verifiers: the reference FIPS 204 verifier accepts
the same sigma (that is what `fipsOk` reports). The consequence for this design
is that the required registration-time pk validator (docs/SAFETY.md section 3)
must not only re-derive the cache from a standard pk, it must also REJECT
degenerate keys, by an explicit criterion ON THE KEY.

PROOF-OF-POSSESSION IS NOT SUCH A CRITERION.  PoP asks the registrant to sign a
challenge under the key being registered; the whole point of the construction
above is that ANYONE can do that for this key, with no secret material, in one
shot, for a challenge somebody else picked.  Run this script with a registrar's
challenge string as `<msg_hex>` and the output IS a valid PoP response.  A
key-free-forgeable public key does not have NO owner -- it has EVERY owner.

Deterministic, offline, no network.
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

import e2e_pk  # noqa: E402  (shares the blob builder + mldsa_min loading)
from eth_abi import encode as abi_encode  # noqa: E402

M = e2e_pk.M
GAMMA1 = M.GAMMA1
PK_SIZE = 1312
SIG_SIZE = 2420
Z_BYTES = 2304  # 4 rows x 256 coeffs x 18 bits
H_BYTES = 84  # omega + k
W1_BYTES = 768  # 4 rows x 256 coeffs x 6 bits
A_OFF = 4160  # start of the Ahat block in the cache


def degenerate_pk(seed):
    """pk = rho || pkEncode(t1 = 0), with rho taken from an honest key."""
    honest_pk = e2e_pk.derive_pk(seed)
    rho = honest_pk[:32]
    pk = rho + bytes(PK_SIZE - 32)  # t1 = 0 -> 4 * 320 zero bytes
    assert len(pk) == PK_SIZE
    return pk


def encode_z_zero():
    """zEncode(z = 0): every 18-bit little-endian field carries gamma1."""
    bits = 0
    for i in range(1024):
        bits |= GAMMA1 << (18 * i)
    return bits.to_bytes(Z_BYTES, "little")


def forge(pk, msg, ctx=b""):
    """The universal forgery for t1 = 0 (see the module docstring)."""
    if len(ctx) > 255:
        raise SystemExit("degen: ctx must be at most 255 bytes")
    tr = M.shake256(pk, 64)
    m_prime = bytes([0]) + bytes([len(ctx)]) + ctx + msg
    mu = M.shake256(tr + m_prime, 64)
    c_tilde = M.shake256(mu + bytes(W1_BYTES), 32)  # w1 = UseHint(0, 0) = 0
    sig = c_tilde + encode_z_zero() + bytes(H_BYTES)
    assert len(sig) == SIG_SIZE, len(sig)
    return sig


def fips_verdict(pk, msg, sig, ctx=b""):
    """The REAL verdict of the reference FIPS 204 verifier (never hardcoded)."""
    from dilithium_py.dilithium.default_parameters import Dilithium2 as D
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    return bool(D.verify(pk, msg, sig, ctx, _xof=shake256, _xof2=shake128))


def main(argv):
    if len(argv) < 3:
        raise SystemExit("usage: degen.py <seed_hex> <0xmsg_hex>")
    seed = bytes.fromhex(argv[1].removeprefix("0x"))
    msg = bytes.fromhex(argv[2].removeprefix("0x"))

    pk = degenerate_pk(seed)
    sig = forge(pk, msg)
    pk_blob = e2e_pk.build(pk)
    fips_ok = fips_verdict(pk, msg, sig)

    if len(pk_blob) != 20544:
        raise SystemExit(f"degen: pk blob must be 20544 bytes, got {len(pk_blob)}")
    # sanity: A really is the genuine, non-zero ExpandA image (offset 4160..)
    if not any(pk_blob[A_OFF:]):
        raise SystemExit("degen: A block is all zero — cache is not honestly derived")

    sys.stdout.write(
        abi_encode(
            ["bytes", "bytes", "bytes", "bool"],
            [pk_blob, sig, pk, fips_ok],
        ).hex()
    )


if __name__ == "__main__":
    main(sys.argv)
