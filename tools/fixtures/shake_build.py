#!/usr/bin/env python3
"""
shake_build.py — fixture-shard builder for test/FUZZ_Shake.t.sol.

  usage (this is what vm.ffi runs, cwd = repository root):
      pythonref/myenv/bin/python tools/fixtures/shake_build.py sk_0.hex
      pythonref/myenv/bin/python tools/fixtures/shake_build.py --build   # all

OUTPUT — hex text (no 0x, no newline) on stdout; cached under test/fixtures/.

  sk_0.hex .. sk_3.hex   ShakeShard = (bytes[] inputs, uint256[] outLens,
                                       bytes[] digests, string[] labels)
                         the 251 OFFICIAL NIST ACVP SHAKE-256 known-answer
                         vectors (63/63/63/62).
  sr_0.hex .. sr_2.hex   same struct, the 405 randomized oracle vectors
                         (135/135/135).

OFFICIAL CORPUS (251) — every byte-aligned SHAKE-256 case of
    gen-val/json-files/SHAKE-256-FIPS202/internalProjection.json   (237 AFT)
    gen-val/json-files/SHAKE-256-1.0/internalProjection.json       (1148 AFT +
                                                                    512 VOT)
  = 41 + 143 + 67 = 251 vectors.  The 1646 remaining cases have a bit-oriented
  input or output length (len % 8 != 0 or outLen % 8 != 0), which a byte
  oriented EVM XOF cannot express, and the single MCT group is a chained
  self-test rather than a KAT; both are skipped.  Inputs run up to 8126 bytes
  and outputs up to 512 bytes.  Every `md` is re-derived with hashlib's
  FIPS-202 SHAKE-256 while the distilled corpus is built (tools/fixtures/
  fx_common.py::_distill_shake), so ACVP and the oracle agree on all 251.

RANDOM CORPUS (405) — hashlib-oracle vectors:
  * 19 x 15 = 285 grid of
      inLen  in {0,1,2,31,32,33,63,64,135,136,137,271,272,273,407,408,409,
                 544,1000}
      outLen in {1,31,32,33,64,135,136,137,271,272,273,1000,1088,1500,3000}
    (both sides straddle the 136-byte rate and the 3rd/4th block boundary,
     include the empty input and outputs past 1000 bytes)
  * 120 uniformly random pairs with inLen <= 4096 and outLen <= 2048.
  All inputs are deterministic SHAKE-256 expansions of a fixed domain string,
  so the corpus is reproducible bit-for-bit.
"""

import hashlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import fx_common as F  # noqa: E402

NAMES = [f"sk_{k}.hex" for k in range(4)] + [f"sr_{k}.hex" for k in range(3)]
N_KAT_SHARDS = 4
N_RND_SHARDS = 3

GRID_IN = [0, 1, 2, 31, 32, 33, 63, 64, 135, 136, 137, 271, 272, 273, 407, 408, 409, 544, 1000]
GRID_OUT = [1, 31, 32, 33, 64, 135, 136, 137, 271, 272, 273, 1000, 1088, 1500, 3000]
N_RANDOM = 120


def kat_cases():
    _, sk = F.acvp_data()
    out = []
    for v in sk["vectors"]:
        msg = bytes.fromhex(v["msg"])
        md = bytes.fromhex(v["md"])
        assert hashlib.shake_256(msg).digest(v["outLen"]) == md, v
        out.append((msg, v["outLen"], md, f"ACVP:{v['src']}:tc{v['tcId']}"))
    assert len(out) == 251, len(out)
    return out


def random_cases():
    out = []
    for ni in GRID_IN:
        msg = F.rnd(b"shake/grid/in/%d" % ni, ni)
        for no in GRID_OUT:
            out.append((msg, no, hashlib.shake_256(msg).digest(no), f"RND:grid:{ni}->{no}"))
    for i in range(N_RANDOM):
        r = F.rnd(b"shake/rnd/%d" % i, 8)
        ni = int.from_bytes(r[:4], "big") % 4097
        no = 1 + int.from_bytes(r[4:], "big") % 2048
        msg = F.rnd(b"shake/rnd/msg/%d" % i, ni)
        out.append((msg, no, hashlib.shake_256(msg).digest(no), f"RND:rand{i}:{ni}->{no}"))
    assert len(out) == len(GRID_IN) * len(GRID_OUT) + N_RANDOM == 405, len(out)
    return out


def _emit(prefix, cases, nshards):
    for k, idxs in enumerate(F.split(len(cases), nshards)):
        shard = (
            [cases[i][0] for i in idxs],
            [cases[i][1] for i in idxs],
            [cases[i][2] for i in idxs],
            [cases[i][3] for i in idxs],
        )
        F.write_shard(f"{prefix}_{k}.hex", F.enc(F.SHAKE_SHARD_T, shard))


def build_all():
    _emit("sk", kat_cases(), N_KAT_SHARDS)
    _emit("sr", random_cases(), N_RND_SHARDS)


if __name__ == "__main__":
    F.main(sys.argv, build_all, NAMES)
