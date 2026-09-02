"""
mldsa_min.py — minimal, dependency-free FIPS 204 ML-DSA-44 *public-side* math.

Only what prepare.py needs: public-key decoding, ExpandA, the NTT/inverse NTT,
SampleInBall, signature decoding and the w'_approx computation. Standard
library only (hashlib) so the program is deterministic and offline on any
Python 3.8+.

Cross-validated against pythonref/ (dilithium_py): ExpandA, NTT/invNTT
coefficient order, SampleInBall and w'_approx all match bit-for-bit.

FIPS 204 references (the PUBLISHED standard's numbering, not the draft's):
Algorithm 41 (NTT), 42 (NTT^-1), 32 (ExpandA/RejNTTPoly), 29 (SampleInBall),
23 (pkDecode), 27 (sigDecode).  Citing 22 for pkDecode or 26 for sigDecode
would name the DRAFT's algorithms: in FIPS 204 as published, 22 is pkEncode and
26 is sigEncode -- the encoders, not the decoders this file implements.
"""

from hashlib import shake_128, shake_256

Q = 8380417
N = 256
D = 13
K = 4  # rows
L = 4  # cols
TAU = 39
GAMMA1 = 1 << 17
GAMMA2 = (Q - 1) // 88
BETA = 78
OMEGA = 80
ZETA = 1753  # 512th primitive root of unity mod q


def _brv8(i):
    return int(f"{i:08b}"[::-1], 2)


# zetas[i] = ZETA^brv8(i) mod q  (FIPS 204 Algorithm 41's constant table)
ZETAS = [pow(ZETA, _brv8(i), Q) for i in range(256)]


def shake128(data, n):
    return shake_128(data).digest(n)


def shake256(data, n):
    return shake_256(data).digest(n)


# ---------------------------------------------------------------- NTT / INTT


def ntt(a):
    """FIPS 204 Algorithm 41, in the standard coefficient order."""
    w = list(a)
    m = 0
    length = 128
    while length >= 1:
        start = 0
        while start < N:
            m += 1
            z = ZETAS[m]
            for j in range(start, start + length):
                t = (z * w[j + length]) % Q
                w[j + length] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
            start += 2 * length
        length //= 2
    return w


def intt(a):
    """FIPS 204 Algorithm 42 (inverse NTT), including the 256^-1 scaling."""
    w = list(a)
    m = 256
    length = 1
    while length < N:
        start = 0
        while start < N:
            m -= 1
            z = (-ZETAS[m]) % Q
            for j in range(start, start + length):
                t = w[j]
                w[j] = (t + w[j + length]) % Q
                w[j + length] = (z * (t - w[j + length])) % Q
            start += 2 * length
        length *= 2
    f = 8347681  # 256^-1 * ... = pow(256, -1, Q) folded constant of FIPS 204
    return [(f * x) % Q for x in w]


def pointwise(a, b):
    return [(x * y) % Q for x, y in zip(a, b)]


def polyadd(a, b):
    return [(x + y) % Q for x, y in zip(a, b)]


def polysub(a, b):
    return [(x - y) % Q for x, y in zip(a, b)]


# ------------------------------------------------------------------ ExpandA


def rej_ntt_poly(seed):
    """FIPS 204 Algorithm 30: rejection sampling in the NTT domain."""
    out = []
    want = 3 * N + 96
    while True:
        buf = shake128(seed, want)
        out = []
        i = 0
        while i + 3 <= len(buf) and len(out) < N:
            v = buf[i] | (buf[i + 1] << 8) | ((buf[i + 2] & 0x7F) << 16)
            i += 3
            if v < Q:
                out.append(v)
        if len(out) == N:
            return out
        want *= 2  # XOF prefix property keeps this deterministic


def expand_a(rho):
    """A_hat[i][j] = RejNTTPoly(rho || j || i) — NTT domain (FIPS 204 Alg. 32)."""
    return [[rej_ntt_poly(rho + bytes([j, i])) for j in range(L)] for i in range(K)]


# --------------------------------------------------------------- SampleInBall


def sample_in_ball(c_tilde):
    """FIPS 204 Algorithm 29 (tau = 39): coefficients in {0, 1, q-1}."""
    c = [0] * N
    stream = shake256(c_tilde, 136)
    signs = int.from_bytes(stream[:8], "little")
    pos = 8
    for i in range(N - TAU, N):
        while True:
            if pos >= len(stream):
                stream = shake256(c_tilde, 2 * len(stream))
            j = stream[pos]
            pos += 1
            if j <= i:
                break
        c[i] = c[j]
        c[j] = Q - 1 if (signs & 1) else 1
        signs >>= 1
    return c


# ------------------------------------------------------------------- decoding


def pk_decode(pk):
    """pkDecode: (rho, t1) with t1 coefficients in [0, 2^10)."""
    if len(pk) != 1312:
        raise ValueError(f"ML-DSA-44 pk must be 1312 bytes, got {len(pk)}")
    rho = pk[:32]
    t1 = []
    off = 32
    for _ in range(K):
        chunk = pk[off : off + 320]
        off += 320
        bits = int.from_bytes(chunk, "little")
        t1.append([(bits >> (10 * i)) & 0x3FF for i in range(N)])
    return rho, t1


def sig_decode(sig):
    """sigDecode: (c_tilde, z, h_indices). z centered in (-gamma1, gamma1]."""
    if len(sig) != 2420:
        raise ValueError(f"ML-DSA-44 signature must be 2420 bytes, got {len(sig)}")
    c_tilde = sig[:32]
    z = []
    off = 32
    for _ in range(L):
        chunk = sig[off : off + 576]
        off += 576
        bits = int.from_bytes(chunk, "little")
        z.append([GAMMA1 - ((bits >> (18 * i)) & 0x3FFFF) for i in range(N)])
    hb = sig[off : off + 84]
    h = [[] for _ in range(K)]
    idx = 0
    for i in range(K):
        end = hb[OMEGA + i]
        if end < idx or end > OMEGA:
            return c_tilde, z, None
        prev = -1
        for j in range(idx, end):
            if hb[j] <= prev and j > idx:
                return c_tilde, z, None
            prev = hb[j]
            h[i].append(hb[j])
        idx = end
    for j in range(idx, OMEGA):
        if hb[j] != 0:
            return c_tilde, z, None
    return c_tilde, z, h


# ---------------------------------------------------------------- verify math


def tr_of(pk):
    """tr = H(pk, 64) = SHAKE256(pk, 64)."""
    return shake256(pk, 64)
