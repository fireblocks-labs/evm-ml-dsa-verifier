# FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE
# Invoked as: pythonref/myenv/bin/python tools/fixtures/degen2.py ...
"""
degen2.py — the three degenerate-key fixtures that pin docs/SAFETY.md section
3.1's degeneracy guidance.

`degen.py` (the sibling) covers the flagship `t1 = 0` key and the
proof-of-possession vacuity result.  This file covers three further gaps that
section 3.1's guidance has to close, and each one is consumed by a test in
test/SEC_pkcache.t.sol:

  witness   NO PROOF ABOUT THE SECRET KEY REJECTS DEGENERATE KEYS -- NOT EVEN
            A PROOF OF KNOWLEDGE OF (s1, s2).  Section 3.1 quotes it as "the
            complete answer, because it demands the one object a degenerate
            key does not have" and then refutes it.  A degenerate key HAS that
            object, and it is PUBLIC:

                t1 = 0    everywhere  <-  (s1, s2, t0) = ( 0,  0, 0)
                t1 = 1023 everywhere  <-  (s1, s2, t0) = ( 0, -1, 0)

            because Power2Round(0, 13) = (0, 0) and Power2Round(q-1, 13) =
            (1023, 0) -- q - 1 == 1023 * 2^13 EXACTLY -- and ||s2||inf = 1 <=
            eta = 2.  This mode BUILDS the FIPS 204 secret key from the witness
            and SIGNS with the reference signer, which genuinely uses s1 in
            z = y + c*s1, s2 in the r0 check and t0 in the hint.  So a rigorous
            exact-relation, norm-bounded proof of knowledge of (s1, s2) is
            answered under a degenerate key with no secret material at all.

  maxdegen  THE MAXIMAL DEGENERATE KEY.  t1 = 1023 in all 1,024 coefficients:
            maximal coefficient value, maximal Hamming weight, every pkEncode
            byte 0xff -- nothing that resembles the t1 = 0 fixture.  It is
            key-free forgeable by the IDENTICAL z = 0 / h = 0 construction,
            because lift(1023) = -1, so ||c (*) lift(t1)||inf <= tau = 39, far
            inside gamma2.  The CENTRED-LIFT criterion of section 3.1 refuses
            it; a "reject low-weight / near-zero t1" rule does not.

  fatsig    A DEGENERATE-KEY FORGERY THAT DOES NOT LOOK DEGENERATE.  The
            published fixture uses z = 0 and h = 0, the single most conspicuous
            signature in the space.  A registrar that "hardens" proof-of-
            possession by refusing conspicuous responses is not helped: the same
            key-free forgery closes with ||z||inf just under gamma1 - beta and
            60 real hint bits.

CLI
---
  degen2.py witness  <t1_value> <seed_hex_64_chars_no_0x> <msg_hex_with_0x>
      abi.encode(bytes pkBlob, bytes sig, bytes pk, bool fipsOk,
                 uint256 s1max, uint256 s2max, uint256 t0max, uint256 eta,
                 bool relationHolds)
      `t1_value` is 0 or 1023.  s1max/s2max/t0max are the MEASURED infinity
      norms of the witness; `relationHolds` is an INDEPENDENT re-derivation of
      Power2Round(A*s1 + s2, 13) == (t1, 0) over all 1,024 coefficients.

  degen2.py maxdegen <seed_hex> <msg_hex_with_0x>
      abi.encode(bytes pkBlob, bytes sig, bytes pk, bool fipsOk)

  degen2.py fatsig   <seed_hex> <msg_hex_with_0x>
      abi.encode(bytes pkBlob, bytes sig, bytes pk, bool fipsOk,
                 uint256 zmax, uint256 hweight)

Every verdict below is MEASURED (the reference FIPS 204 verifier's own answer),
never hardcoded.  Deterministic, offline, no network.
"""
import hashlib
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

import e2e_pk  # noqa: E402  (shares the blob builder + mldsa_min loading)
from eth_abi import encode as abi_encode  # noqa: E402

M = e2e_pk.M
Q = M.Q
D = M.D
GAMMA1 = M.GAMMA1
GAMMA2 = (Q - 1) // 88
TAU, OMEGA, BETA, ETA = 39, 80, 78, 2
PK_SIZE, SIG_SIZE = 1312, 2420
Z_BYTES, H_BYTES, W1_BYTES = 2304, 84, 768
A_OFF = 4160  # start of the Ahat block in the cache

# q - 1 == 1023 * 2^13 EXACTLY.  This is the whole reason the t1 = 1023 key is
# both degenerate AND has a norm-conforming witness: lift(1023) = -1.
assert (Q - 1) == 1023 * (1 << D), "q-1 must be exactly 1023 * 2^13"


# ------------------------------------------------------------------ key build


def pk_with_constant_t1(seed, v):
    """pk = rho || pkEncode(t1 = v everywhere), rho from an HONEST key.

    Identical construction to degen.py for v = 0, so the two fixtures register
    the same key for the same seed.
    """
    rho = e2e_pk.derive_pk(seed)[:32]
    body = bytearray()
    for _row in range(4):
        bits = 0
        for i in range(256):
            bits |= v << (10 * i)
        body += bits.to_bytes(320, "little")
    pk = rho + bytes(body)
    assert len(pk) == PK_SIZE
    _r, t1 = M.pk_decode(pk)  # round-trip through the reference decoder
    assert all(c == v for row in t1 for c in row), "t1 did not round-trip"
    return pk


# ------------------------------------------------------------------- encoders


def encode_z(z_rows):
    """zEncode: 18-bit little-endian fields of (gamma1 - z_i)."""
    bits, idx = 0, 0
    for row in z_rows:
        for c in row:
            bits |= ((GAMMA1 - c) % (1 << 18)) << (18 * idx)
            idx += 1
    return bits.to_bytes(Z_BYTES, "little")


def encode_h(h_rows):
    """HintBitUnpack's inverse: sorted indices per row + k cumulative counters."""
    packed, offsets = [], []
    for row in h_rows:
        packed.extend(sorted(i for i, b in enumerate(row) if b))
        offsets.append(len(packed))
    assert offsets[-1] <= OMEGA, offsets
    packed.extend([0] * (OMEGA - offsets[-1]))
    return bytes(packed + offsets)


def w1_encode(w1_rows):
    bits, idx = 0, 0
    for row in w1_rows:
        for c in row:
            bits |= c << (6 * idx)
            idx += 1
    return bits.to_bytes(W1_BYTES, "little")


# ------------------------------------------------------- FIPS 204 arithmetic


def decompose(r):
    """FIPS 204 Algorithm 36."""
    rp = r % Q
    r0 = rp % (2 * GAMMA2)
    if r0 > GAMMA2:
        r0 -= 2 * GAMMA2
    if rp - r0 == Q - 1:
        return 0, r0 - 1
    return (rp - r0) // (2 * GAMMA2), r0


def power2round(r):
    """FIPS 204 Algorithm 35, returned as (r1, r0)."""
    rp = r % Q
    r0 = rp % (1 << D)
    if r0 > (1 << (D - 1)):
        r0 -= 1 << D
    return (rp - r0) >> D, r0


def matvec(a_hat, z_rows):
    """A z, in the coefficient domain."""
    z_hat = [M.ntt(list(r)) for r in z_rows]
    out = []
    for i in range(4):
        acc = [0] * 256
        for j in range(4):
            p = M.pointwise(a_hat[i][j], z_hat[j])
            acc = [(x + y) % Q for x, y in zip(acc, p)]
        out.append(M.intt(acc))
    return out


def mu_of(pk, msg, ctx=b""):
    tr = M.shake256(pk, 64)
    return M.shake256(tr + bytes([0]) + bytes([len(ctx)]) + ctx + msg, 64)


# --------------------------------------------------------------- the forgery


def forge_zero(pk, msg):
    """The z = 0 / h = 0 forgery: works whenever HighBits(w') is 0 for every c."""
    c_tilde = M.shake256(mu_of(pk, msg) + bytes(W1_BYTES), 32)
    return c_tilde + encode_z([[0] * 256 for _ in range(4)]) + bytes(H_BYTES)


def forge_fat(pk, msg, rng_seed):
    """The same key-free forgery under t1 = 0, with an ORDINARY-LOOKING sigma.

    t1 = 0 => w'approx = A z for any z, independent of c.  Choose z uniformly in
    the legal window, choose a hint pattern h, and set
    c~ = H(mu || w1Encode(UseHint(h, A z))) -- no secret material, one shot, no
    grinding.  The forger controls w1; it does not have to match any signer's w.
    """
    rho, _t1 = M.pk_decode(pk)
    a_hat = M.expand_a(rho)

    lim = GAMMA1 - BETA
    stream = hashlib.shake_256(rng_seed).digest(4 * 256 * 4)
    z_rows = []
    for r in range(4):
        row = []
        for i in range(256):
            o = 4 * (256 * r + i)
            w = int.from_bytes(stream[o:o + 4], "little")
            row.append(w % (2 * lim - 1) - (lim - 1))
        z_rows.append(row)
    assert max(abs(c) for row in z_rows for c in row) < lim

    w = matvec(a_hat, z_rows)  # == w'approx, since t1 = 0

    # Real hint bits: h_ij = 1 means "move the high part by one" (FIPS 204
    # Alg. 40 UseHint), and w1 is simply what UseHint then produces.
    h_rows = [[0] * 256 for _ in range(4)]
    for r in range(4):
        for t in range(15):  # 60 bits total, under omega = 80
            h_rows[r][(t * 17 + 3 * r) % 256] = 1

    w1_rows = []
    for r in range(4):
        row = []
        for i in range(256):
            r1, r0 = decompose(w[r][i])
            if h_rows[r][i] == 1:
                row.append((r1 + 1) % 44 if r0 > 0 else (r1 - 1) % 44)
            else:
                row.append(r1)
        w1_rows.append(row)

    c_tilde = M.shake256(mu_of(pk, msg) + w1_encode(w1_rows), 32)
    sig = c_tilde + encode_z(z_rows) + encode_h(h_rows)
    assert len(sig) == SIG_SIZE, len(sig)
    return (sig,
            max(abs(c) for row in z_rows for c in row),
            sum(sum(row) for row in h_rows))


# ------------------------------------------- the PUBLIC secret-key witnesses


def sign_with_witness(pk, t1_val, msg):
    """Build the FIPS 204 secret key from the PUBLIC witness and SIGN with it.

    The reference signer uses every component of the witness for real: s1 in
    z = y + c*s1, s2 in the r0 check on w - c*s2, and t0 in the hint.  If it
    produces a signature the reference verifier accepts under `pk`, then the
    witness IS an ML-DSA secret key for `pk` in every sense a proof of knowledge
    could ask about.
    """
    from dilithium_py.dilithium.default_parameters import Dilithium2 as DD
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    s2_coeff = {0: 0, 1023: -1}[t1_val]
    s1_rows = [[0] * 256 for _ in range(DD.l)]
    s2_rows = [[s2_coeff] * 256 for _ in range(DD.k)]
    t0_rows = [[0] * 256 for _ in range(DD.k)]

    rho = pk[:32]
    # The key relation, re-derived INDEPENDENTLY of dilithium_py's packing:
    # Power2Round(A*s1 + s2) must be (t1_val, 0) in all 1,024 coefficients.
    a_hat = M.expand_a(rho)
    t = matvec(a_hat, s1_rows)
    relation = True
    for i in range(4):
        for j in range(256):
            r1, r0 = power2round(t[i][j] + s2_rows[i][j])
            if r1 != t1_val or r0 != 0:
                relation = False

    def vec(rows):
        return DD.M([[DD.R(r)] for r in rows])

    sk = DD._pack_sk(rho, bytes(32), DD._h(pk, 64, _xof=shake256),
                     vec(s1_rows), vec(s2_rows), vec(t0_rows))
    if len(sk) != DD._sk_size():
        raise SystemExit(f"degen2: packed sk is {len(sk)} bytes, expected {DD._sk_size()}")
    sig = DD.sign(sk, msg, b"", True, _xof=shake256, _xof2=shake128)
    norms = (max(abs(c) for r in s1_rows for c in r),
             max(abs(c) for r in s2_rows for c in r),
             max(abs(c) for r in t0_rows for c in r))
    return sig, norms, relation


# ------------------------------------------------------------------- verdict


def fips_verdict(pk, msg, sig, ctx=b""):
    """The REAL verdict of the reference FIPS 204 verifier (never hardcoded)."""
    from dilithium_py.dilithium.default_parameters import Dilithium2 as DD
    from dilithium_py.shake.shake_wrapper import shake128, shake256

    try:
        return bool(DD.verify(pk, msg, sig, ctx, _xof=shake256, _xof2=shake128))
    except (ValueError, IndexError, AssertionError):
        return False


def _blob(pk):
    blob = e2e_pk.build(pk)
    if len(blob) != e2e_pk.BLOB_SIZE:
        raise SystemExit(f"degen2: pk blob must be {e2e_pk.BLOB_SIZE} bytes, got {len(blob)}")
    if not any(blob[A_OFF:]):
        raise SystemExit("degen2: A block is all zero — cache is not honestly derived")
    return blob


def main(argv):
    if len(argv) < 2:
        raise SystemExit("usage: degen2.py witness|maxdegen|fatsig ...")
    mode = argv[1]

    if mode == "witness":
        if len(argv) != 5:
            raise SystemExit("usage: degen2.py witness <t1_value> <seed_hex> <0xmsg_hex>")
        t1_val = int(argv[2])
        if t1_val not in (0, 1023):
            raise SystemExit("degen2: witness is defined for t1 = 0 and t1 = 1023")
        seed = bytes.fromhex(argv[3].removeprefix("0x"))
        msg = bytes.fromhex(argv[4].removeprefix("0x"))
        pk = pk_with_constant_t1(seed, t1_val)
        sig, (n1, n2, n0), relation = sign_with_witness(pk, t1_val, msg)
        sys.stdout.write(abi_encode(
            ["bytes", "bytes", "bytes", "bool",
             "uint256", "uint256", "uint256", "uint256", "bool"],
            [_blob(pk), sig, pk, fips_verdict(pk, msg, sig),
             n1, n2, n0, ETA, relation]).hex())
        return

    if len(argv) != 4:
        raise SystemExit(f"usage: degen2.py {mode} <seed_hex> <0xmsg_hex>")
    seed = bytes.fromhex(argv[2].removeprefix("0x"))
    msg = bytes.fromhex(argv[3].removeprefix("0x"))

    if mode == "maxdegen":
        pk = pk_with_constant_t1(seed, 1023)
        sig = forge_zero(pk, msg)
        sys.stdout.write(abi_encode(
            ["bytes", "bytes", "bytes", "bool"],
            [_blob(pk), sig, pk, fips_verdict(pk, msg, sig)]).hex())
    elif mode == "fatsig":
        pk = pk_with_constant_t1(seed, 0)
        sig, zmax, hw = forge_fat(pk, msg, seed)
        sys.stdout.write(abi_encode(
            ["bytes", "bytes", "bytes", "bool", "uint256", "uint256"],
            [_blob(pk), sig, pk, fips_verdict(pk, msg, sig), zmax, hw]).hex())
    else:
        raise SystemExit("usage: degen2.py witness|maxdegen|fatsig ...")


if __name__ == "__main__":
    main(sys.argv)
