#!/usr/bin/env python3
"""
fuzz_build.py — fixture-shard builder for test/FUZZ_MLDSA44.t.sol.

  usage (this is what vm.ffi runs, cwd = repository root):
      pythonref/myenv/bin/python tools/fixtures/fuzz_build.py fs_0.hex
      pythonref/myenv/bin/python tools/fixtures/fuzz_build.py --build   # all

OUTPUT — hex text (no 0x, no newline) on stdout; cached under test/fixtures/.

  fs_0.hex .. fs_12.hex   Shard, battery A   (800 cases: 62 x7, 61 x6)
  fm_0.hex .. fm_22.hex   Shard, battery B   (1380 cases: 60 each)

  Shard = (bytes[] pkBlobs, uint256[] pkIdx, bytes[] msgs, bytes[] sigs,
           bool[] expect, string[] labels)

2180 cases in total, each fed to BOTH in-tree subjects — the reference
verifier test/ZZZ_E2ERef.sol and the shipped src/MLDSA44Verifier.sol — for
4360 on-chain verifications.  Sharding is sized for the default per-test gas
ceiling (each on-chain verification pair costs several million gas), so a
shard never carries more than 62 cases.

EVERY case is oracle-checked against the pythonref FIPS-204 implementation
before it is emitted; a disagreement aborts the build.  Nothing here is
hand-asserted, so every on-chain assertion is a genuine differential test
(EVM verdict == python reference verdict).

BATTERY A — 800 must-ACCEPT cases: 40 deterministically derived keys x 20
  message lengths {0,1,2,31,32,33,63,64,65,69,70,71,135,136,137,206,272,342,
  500,8192}.  The lengths straddle the SHAKE256 rate (136 B) for the raw
  message and for the mu pre-image 66+|M| at exact block boundaries
  (|M| = 70 -> 136, 206 -> 272, 342 -> 408), plus the empty message and the
  8 KiB ACVP maximum.  Case ordering is key-major, so a contiguous shard only
  ever touches 3-4 public keys (which keeps the per-shard pk-blob overhead
  down).

BATTERY B — 1380 must-REJECT cases: 60 base signatures x 23 systematic
  sigma mutations (MUTATIONS below), covering the commitment, the z region,
  the hEncode(h) region (FIPS 204 HintBitUnpack validity), the signature
  length, and message/key substitution.

An h index >= 256 is deliberately absent from the h-region mutations:
FIPS 204 encodes hint positions as single bytes, so no decoder can ever see
one.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import fx_common as F  # noqa: E402

NAMES = [f"fs_{k}.hex" for k in range(13)] + [f"fm_{k}.hex" for k in range(23)]
N_KEYS = 40
N_BASES = 60
N_FS_SHARDS = 13
N_FM_SHARDS = 23

# ABI tuple; field order MUST match struct Shard in test/FUZZ_MLDSA44.t.sol.
SHARD_T = "(bytes[],uint256[],bytes[],bytes[],bool[],string[])"

MSG_LENS = [0, 1, 2, 31, 32, 33, 63, 64, 65, 69, 70, 71, 135, 136, 137, 206, 272, 342, 500, 8192]

MUTATIONS = (
    "flip.ctilde", "flip.z", "flip.h", "flip.multi3",
    "z.plus1", "z.boundary.g1mb", "z.inrange.g1mb1", "z.gamma1", "z.maxfield", "z.rowswap",
    "h.count.gt.omega", "h.nonmonotone.idx", "h.nonmonotone.cnt", "h.nonzero.pad", "h.allzero",
    "sig.trunc2419", "sig.ext2421", "sig.empty", "sig.random",
    "msg.swap", "pk.swap", "ctilde.zero", "ctilde.other",
)
assert len(MUTATIONS) == 23

Z_OFF, Z_ROW, H_OFF = 32, 576, 2336
GAMMA1 = F.GAMMA1  # 131072
FIELD_MAX = (1 << 18) - 1


# ------------------------------------------------------------ bit-level tools


def z_get(sig, row, c):
    off = Z_OFF + Z_ROW * row
    return (int.from_bytes(sig[off:off + Z_ROW], "little") >> (18 * c)) & FIELD_MAX


def z_set(sig, row, c, v):
    off = Z_OFF + Z_ROW * row
    chunk = int.from_bytes(sig[off:off + Z_ROW], "little")
    chunk = (chunk & ~(FIELD_MAX << (18 * c))) | ((v & FIELD_MAX) << (18 * c))
    return sig[:off] + chunk.to_bytes(Z_ROW, "little") + sig[off + Z_ROW:]


def z_force(sig, raw_value):
    """Set the first z coefficient whose raw field differs to `raw_value`.
    Returns a signature that is guaranteed to differ from the input."""
    for c in range(256):
        if z_get(sig, 0, c) != raw_value:
            return z_set(sig, 0, c, raw_value)
    raise AssertionError("degenerate z row")


def flip_bits(buf, lo, hi, tag, n=1):
    out = bytearray(buf)
    for k in range(n):
        r = F.rnd(b"fuzz/flip/%s/%d" % (tag, k), 8)
        off = lo + int.from_bytes(r[:4], "big") % (hi - lo)
        out[off] ^= 1 << (r[4] & 7)
    return bytes(out)


def h_bytes(sig):
    return bytearray(sig[H_OFF:H_OFF + 84])


def with_h(sig, hb):
    assert len(hb) == 84
    return sig[:H_OFF] + bytes(hb) + sig[H_OFF + 84:]


# ------------------------------------------------------------------ mutations


def mutate(kind, tag, pk_idx, msg, sig, other_msg, other_sig, other_pk_idx):
    """Return (pk_idx, message, signature) for one mutation class."""
    if kind == "flip.ctilde":
        return pk_idx, msg, flip_bits(sig, 0, 32, tag)
    if kind == "flip.z":
        return pk_idx, msg, flip_bits(sig, Z_OFF, H_OFF, tag)
    if kind == "flip.h":
        return pk_idx, msg, flip_bits(sig, H_OFF, H_OFF + 80, tag)
    if kind == "flip.multi3":
        return pk_idx, msg, flip_bits(sig, 0, 2420, tag, n=3)
    if kind == "z.plus1":
        for c in range(256):
            v = z_get(sig, 0, c)
            if v >= 1:  # z := z + 1 (raw field decreases by one)
                return pk_idx, msg, z_set(sig, 0, c, v - 1)
        raise AssertionError("degenerate z row")
    if kind == "z.boundary.g1mb":  # |z| = gamma1 - beta = 130994 -> strict FIPS reject
        return pk_idx, msg, z_force(sig, GAMMA1 - (GAMMA1 - F.BETA))
    if kind == "z.inrange.g1mb1":  # |z| = 130993, inside the bound
        return pk_idx, msg, z_force(sig, GAMMA1 - (GAMMA1 - F.BETA - 1))
    if kind == "z.gamma1":  # z = gamma1
        return pk_idx, msg, z_force(sig, 0)
    if kind == "z.maxfield":  # z = -(gamma1 - 1)
        return pk_idx, msg, z_force(sig, FIELD_MAX)
    if kind == "z.rowswap":
        a, b = Z_OFF, Z_OFF + Z_ROW
        return pk_idx, msg, sig[:a] + sig[b:b + Z_ROW] + sig[a:a + Z_ROW] + sig[b + Z_ROW:]
    if kind == "h.count.gt.omega":  # cumulative weight 81 > omega = 80
        hb = h_bytes(sig)
        hb[80:84] = bytes([81, 81, 81, 81])
        return pk_idx, msg, with_h(sig, hb)
    if kind == "h.nonmonotone.idx":  # decreasing indices inside one polynomial
        hb = bytearray(84)
        hb[0], hb[1] = 7, 3
        hb[80:84] = bytes([2, 2, 2, 2])
        return pk_idx, msg, with_h(sig, hb)
    if kind == "h.nonmonotone.cnt":  # decreasing cumulative counts
        hb = bytearray(84)
        hb[0:8] = bytes([1, 2, 3, 4, 5, 6, 7, 8])
        hb[80:84] = bytes([4, 2, 6, 8])
        return pk_idx, msg, with_h(sig, hb)
    if kind == "h.nonzero.pad":  # non-zero byte in the hint padding region
        hb = h_bytes(sig)
        if hb[83] >= 80:
            # weight is exactly omega, so there is no padding region: drop the
            # last hint position to create one (byte 79 becomes padding).
            hb[83] = 79
        hb[79] = 0xFF
        return pk_idx, msg, with_h(sig, hb)
    if kind == "h.allzero":  # structurally valid, empty hint vector
        return pk_idx, msg, with_h(sig, bytearray(84))
    if kind == "sig.trunc2419":
        return pk_idx, msg, sig[:2419]
    if kind == "sig.ext2421":
        return pk_idx, msg, sig + b"\x00"
    if kind == "sig.empty":
        return pk_idx, msg, b""
    if kind == "sig.random":
        return pk_idx, msg, F.rnd(b"fuzz/randsig/" + tag, 2420)
    if kind == "msg.swap":
        return pk_idx, other_msg, sig
    if kind == "pk.swap":
        return other_pk_idx, msg, sig
    if kind == "ctilde.zero":
        return pk_idx, msg, b"\x00" * 32 + sig[32:]
    if kind == "ctilde.other":
        return pk_idx, msg, other_sig[:32] + sig[32:]
    raise AssertionError(kind)


# --------------------------------------------------------------- corpus build


class Case:
    __slots__ = ("pk_idx", "msg", "sig", "exp", "label")

    def __init__(self, pk_idx, msg, sig, exp, label):
        self.pk_idx, self.msg, self.sig = pk_idx, msg, sig
        self.exp, self.label = exp, label


def keys():
    out = []
    for i in range(N_KEYS):
        pk, sk = F.D.key_derive(F.rnd(b"fuzz/key/%d" % i, 32))
        out.append((pk, sk))
    return out


def build_corpus(ks):
    def check(cond, what):
        if not cond:
            raise SystemExit(f"fuzz_build: ORACLE DISAGREEMENT — {what}")

    # ------------------------------------------------------- battery A (800)
    battery_a = []
    for i in range(N_KEYS):
        pk, sk = ks[i]
        for j, n in enumerate(MSG_LENS):
            msg = F.rnd(b"fuzz/A/%d/%d" % (i, j), n)
            sig = F.D.sign(sk, msg, ctx=b"", deterministic=True)
            check(F.verify_pure(pk, msg, sig), f"A:k{i}:len{n}: fresh signature must verify")
            battery_a.append(Case(i, msg, sig, True, f"A:k{i}:len{n}"))
    assert len(battery_a) == 800

    # ------------------------------------------------------ battery B (1380)
    bases = []
    for j in range(N_BASES):
        ki = j % N_KEYS
        pk, sk = ks[ki]
        msg = F.rnd(b"fuzz/B/msg/%d" % j, 64)
        sig = F.D.sign(sk, msg, ctx=b"", deterministic=True)
        check(F.verify_pure(pk, msg, sig), f"B:base{j}: base signature must verify")
        bases.append((ki, msg, sig))

    battery_b = []
    for j, (ki, msg, sig) in enumerate(bases):
        oki, omsg, osig = bases[(j + 1) % N_BASES]
        other_pk_idx = (ki + 1) % N_KEYS
        tag = b"%d" % j
        for kind in MUTATIONS:
            pi, m2, s2 = mutate(kind, tag + b"/" + kind.encode(), ki, msg, sig,
                                omsg, osig, other_pk_idx)
            check((pi, m2, s2) != (ki, msg, sig), f"B:base{j}:{kind}: mutation is a no-op")
            check(not F.verify_pure(ks[pi][0], m2, s2),
                  f"B:base{j}:{kind}: mutated vector must be rejected by the reference")
            battery_b.append(Case(pi, m2, s2, False, f"B:base{j}:{kind}"))
    assert len(battery_b) == N_BASES * 23 == 1380, len(battery_b)
    return battery_a, battery_b


def _emit(prefix, cases, nshards, pk_blobs):
    for k, idxs in enumerate(F.split(len(cases), nshards)):
        blobs, order, pkidx = [], {}, []
        for i in idxs:
            p = cases[i].pk_idx
            if p not in order:
                order[p] = len(blobs)
                blobs.append(pk_blobs[p])
            pkidx.append(order[p])
        shard = (
            blobs,
            pkidx,
            [cases[i].msg for i in idxs],
            [cases[i].sig for i in idxs],
            [cases[i].exp for i in idxs],
            [cases[i].label for i in idxs],
        )
        F.write_shard(f"{prefix}_{k}.hex", F.enc(SHARD_T, shard))


def build_all():
    ks = keys()
    battery_a, battery_b = build_corpus(ks)
    pk_blobs = [F.pk_blob(pk) for pk, _ in ks]
    _emit("fs", battery_a, N_FS_SHARDS, pk_blobs)
    _emit("fm", battery_b, N_FM_SHARDS, pk_blobs)


if __name__ == "__main__":
    F.main(sys.argv, build_all, NAMES)
