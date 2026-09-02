#!/usr/bin/env python3
"""
build_f1600_batch.py — build helpers/f1600_170.hex from helpers/f1600_core.hex.

WHAT THIS BUILDS
  The shipped Keccak-f[1600] helper runtime. It wraps the original generated,
  fully-unrolled, straight-line 24-round permutation (helpers/f1600_core.hex,
  sha256 pinned below; see test/ZZZ_FastKeccak170.sol for that artifact's own
  provenance) with a two-entry-point dispatcher:

    * RAW PERMUTATION (calldatasize == 800): byte-compatible with the original
      helper protocol — 25 lanes in, 25 lanes out (800-byte state both ways).
      Used by SampleInBall's incremental squeeze (src/Decode.sol) and by the
      generic sponge in src/FastKeccak170.sol.

    * BATCHED SHAKE256 (any other calldatasize): calldata IS the raw message;
      the helper runs the whole sponge in one call — FIPS 202 padding
      (0x1f domain, 0x80 final bit), one absorb + permutation per 136-byte
      rate block, and returns the FIRST 136-byte squeeze block. Callers take
      the outLen <= 136 prefix they need (mu wants 64, the final c-tilde hash
      wants 32). A message of exactly 800 bytes cannot be expressed (it would
      be dispatched as a raw permutation); the Solidity wrapper
      (shake256Batch170) rejects that length, and ML-DSA-44 never produces it
      (mu preimage = 66 + |M|, final-hash preimage = 832).

  Why: the ML-DSA-44 final hash absorbs 7 rate blocks = 7 helper calls under
  the raw protocol. Batching turns 7 staticcalls into 1 and moves the
  XOR-absorb / byte-reversal glue into the helper where memory addresses are
  compile-time constants — the per-call marshaling (~200 gas/call), the
  caller-side sponge glue, and 6 redundant 50-word callee memory expansions
  are the prize; the permutation core itself is untouched.

Q-FORM: WHY THE PERMUTATION CARRIES NO MASKS
  The EVM has no rotate. A 64-bit lane rotation on a 64-bit-clean value costs
  `DUP1; PUSH a; SHR; SWAP1; PUSH b; SHL; OR` and then a MASK -- `DUPn(0xff..ff);
  AND` -- because the SHL half overflows past bit 63. Keccak-f[1600] does 29
  rotations per round (25 rho offsets, one of which is 0, plus theta's five
  rot1s), so the generated core paid 29 x (DUP + AND) = 58 opcodes = 174 gas
  per round, 4,176 per permutation, for masking alone.

  Q-form removes ALL of it. A lane v is held in a full 256-bit word as the
  4-FOLD REPLICATION rep4(v) = v | v<<64 | v<<128 | v<<192 == v * QK. Two
  facts make this exact:

    * the word IS the rotation ring. For a 64-periodic W,
        or(shl(r, W), shr(64-r, W)) == rep4(rotl64(v, r))
      with no mask: bit i of the shr term is v[(i-r) mod 64] for all
      i < 192+r, bit i of the shl term is v[(i-r) mod 64] for all i >= r, and
      the two ranges cover 0..255. The bits SHL pushes past bit 255 are
      exactly the bits SHR brings back. Note the core's existing shift
      amounts (r and 64-r) already work -- 64-r == 256-r modulo the period.
    * every other step is bitwise (theta XOR, chi's and/or/andnot, iota XOR,
      the lane complements) and therefore preserves 64-periodicity, so the
      invariant is closed under the whole round with no fixups anywhere.

  So Q-form is a pure DELETION on the core: the mask's `DUPn; AND` pairs go
  away. That deletion is stack-depth-neutral (DUP pushes one, AND pops two and
  pushes one), which is what makes it safe to do on the pinned bytecode --
  every other DUPn/SWAPn index in the core keeps its meaning. -4,176 gas per
  permutation, and -1,392 bytes of code.

  The cost is paid only at the representation boundary, and Q-form is
  RESIDENT in the callee's memory so the batch path pays it once per rate
  block rather than once per permutation:
    * batch absorb: each extracted 64-bit message lane is replicated with one
      MUL before it is XORed into the state word (17 x 8 = 136 gas/block);
    * batch squeeze: CHEAPER than before -- field k of a Q-form word already
      holds the lane, so an output lane is one AND against a pre-shifted mask
      instead of a shift+mask pair;
    * raw entry: 25 CALLDATALOAD+MUL lifts in, 25 ANDs out (~960 gas), on a
      protocol that is byte-identical to before -- callers still see clean
      64-bit lanes in and out and cannot observe Q-form at all.

MECHANICAL PATCHES APPLIED TO THE CORE (all verified by simulation below)
  1. Round-1 input relocation: the core's first round reads the 25-lane state
     from CALLDATA offsets 0x000..0x300; every CALLDATALOAD (50 sites, each
     directly preceded by its PUSH offset) becomes an MLOAD at offset+0x320.
     The state therefore lives IN MEMORY at 0x320..0x640, which is exactly
     where the core's final round writes it — the permutation becomes
     in-place on memory, hence loopable. The raw entry point fills those words
     straight from calldata (one CALLDATALOAD per lane, no CALLDATACOPY: every
     byte is read exactly once anyway).
  2. Round-constant patch: solc reconstructed five complemented iota
     constants as `PUSH1 a; PUSH1 1; PUSH1 s; SHL; SUB` (15 gas, 7 bytes);
     each becomes a single PUSH of the constant (3 gas). Same trick as the
     original build's 64-bit-mask patch, applied to the five sites that
     pass missed. -60 gas per permutation.
  3. The trailing `PUSH2 0x320; DUP1; RETURN` is removed; control falls
     through to the dispatcher's sponge loop (which RETURNs the state for the
     raw path, byte-for-byte as before).
  4. The top-level 64-bit lane-mask variable (`PUSH8 0xff..ff` at core
     instruction 0) becomes all-256-bits (`PUSH0; NOT`). Its only surviving
     consumers are the core's 22 `xor(v, mask)` lane complements, which must
     now complement all four copies -- so widening the variable is exactly the
     fixup they need, and it costs no opcode.
  5. Q-FORM: all 696 `DUPn(mask); AND` rotation fixups (29 per round x 24) are
     DELETED. See above. -4,176 gas per permutation.
  6. All 24 iota round constants (19 direct pushes + the five of patch 2) are
     replaced by their 4-fold replication, so the iota XOR hits every copy.

  Patches 4-6 are driven by `scan_core`, a symbolic-stack pass that PROVES the
  properties they rely on rather than assuming them: the lane mask is pushed
  exactly once, its only uses are those 696 ANDs and 22 XORs (any other use
  aborts the build), every shift amount is a literal (no dynamic shift could
  be Q-form-safe), each iota literal reaches its XOR from a PUSH used once,
  and the core is stack-neutral.

MEMORY MAP (callee frame)
  0x000..0x320  ping-pong round buffer (odd-round outputs); reused as the
                squeeze staging buffer after the last permutation
  0x320..0x640  the 25-lane state in Q-FORM: permutation input AND output
  0x660         remaining-rate-blocks counter (batch; 0 in raw mode)
  0x680         pointer to next rate block in the padded message (batch)
  0x6a0         mode flag: nonzero = batch (squeeze+return-136), 0 = raw
  0x6c0..       the padded message (batch only)

SELF-VERIFICATION (the script refuses to write on any failure)
  * core sha256 == pinned constant; core is straight-line (no JUMP/JUMPDEST),
    stack-neutral, max stack depth 16; scan_core's Q-form preconditions above,
    plus exact counts for every patch (50 relocations, 5+19 = 24 iota
    constants, 696 mask deletions);
  * every static jump in the assembled runtime lands on a JUMPDEST;
  * EIP-170 size, EIP-3541 first byte;
  * mini-EVM differential tests:
      - raw path: 20 random chained states vs a FIPS-202 Python Keccak-f[1600]
        AND vs the original core runtime executed under the same mini-EVM;
      - Q-FORM INVARIANT PROBE: on each of those 20 states, the 25 state words
        are read out of the mini-EVM's memory both after the entry lift and
        after the last round, and each must be EXACTLY rep4 of the FIPS-202
        model's lane. This checks the REPRESENTATION, not just the masked
        800-byte return value;
      - batch path: SHAKE256 of 14 message lengths (block-boundary cases
        0/135/136/137/271/272, the ML-DSA shapes 98 and 832, and others) vs
        hashlib.shake_256;
  * exact callee gas (straight-line + memory expansion) is printed for both
    paths.

OUTPUTS
  helpers/f1600_170.hex             the shipped runtime (hex, no newline)
  test/ZZZ_FastKeccak170.sol        the _F1600_CODE_170 constant is rewritten
                                    in place to match (deploy source of truth)
  stdout                            keccak256 (the F1600_CODEHASH pin), sha256,
                                    size, and measured gas for both entries

USAGE
  python3 tools/build_f1600_batch.py [--check]
    --check: verify helpers/f1600_170.hex is exactly what this script builds
             (byte-for-byte), without writing anything.
"""

import collections
import hashlib
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORE_PATH = os.path.join(ROOT, "helpers", "f1600_core.hex")
OUT_PATH = os.path.join(ROOT, "helpers", "f1600_170.hex")
SOL_PATH = os.path.join(ROOT, "test", "ZZZ_FastKeccak170.sol")

# sha256 of the pristine generated core (the pre-2026-08-11 shipped runtime).
CORE_SHA256 = "46fbc67c4040f22929be6abb43abb935a3f2ae6b03398729c09afe0c898764ee"

EIP170_LIMIT = 24576
M64 = (1 << 64) - 1
M256 = (1 << 256) - 1

# Q-FORM: a 64-bit Keccak lane v is held in a full 256-bit EVM word as the
# 4-fold replication  v | v<<64 | v<<128 | v<<192  ==  v * QK. Because the word
# is EXACTLY four copies, the 256-bit word is itself the rotation ring: for a
# 64-periodic W,  or(shl(r, W), shr(64-r, W)) == rep4(rotl64(v, r))  with no
# masking (bits shifted out of bit 255 are the bits shr brings back in). See
# the module docstring, patch 5.
QK = int("0000000000000001" * 4, 16)


def rep4(v):
    """4-fold replication of a 64-bit lane value into a 256-bit word."""
    if v >> 64:
        raise SystemExit(f"rep4: {v:#x} is not a 64-bit lane value")
    return v * QK

# ---------------------------------------------------------------------------
# tiny EVM opcode table (only what the runtime uses)
# ---------------------------------------------------------------------------
OP = {
    "STOP": 0x00, "ADD": 0x01, "MUL": 0x02, "SUB": 0x03, "DIV": 0x04,
    "LT": 0x10, "GT": 0x11, "EQ": 0x14, "ISZERO": 0x15,
    "AND": 0x16, "OR": 0x17, "XOR": 0x18, "NOT": 0x19,
    "SHL": 0x1B, "SHR": 0x1C,
    "CALLDATALOAD": 0x35, "CALLDATASIZE": 0x36, "CALLDATACOPY": 0x37,
    "POP": 0x50, "MLOAD": 0x51, "MSTORE": 0x52, "MSTORE8": 0x53,
    "JUMP": 0x56, "JUMPI": 0x57, "JUMPDEST": 0x5B, "PUSH0": 0x5F,
    "RETURN": 0xF3, "REVERT": 0xFD,
}
GAS = {
    0x00: 0, 0x01: 3, 0x02: 5, 0x03: 3, 0x04: 5, 0x10: 3, 0x11: 3, 0x14: 3,
    0x15: 3, 0x16: 3, 0x17: 3, 0x18: 3, 0x19: 3, 0x1B: 3, 0x1C: 3,
    0x35: 3, 0x36: 2, 0x50: 2, 0x51: 3, 0x52: 3, 0x53: 3,
    0x56: 8, 0x57: 10, 0x5B: 1, 0x5F: 2, 0xF3: 0, 0xFD: 0,
}


def disasm(code):
    """[(pc, opcode, immediate_bytes)] with PUSH immediates attached."""
    pc, out = 0, []
    while pc < len(code):
        op = code[pc]
        imm = b""
        if 0x60 <= op <= 0x7F:
            w = op - 0x5F
            imm = code[pc + 1: pc + 1 + w]
            if len(imm) != w:
                raise SystemExit("truncated PUSH at end of code")
            pc += w
        out.append((pc - len(imm), op, imm))
        pc += 1
    return out


def push(val, width=None):
    """Smallest PUSH encoding of val (or fixed width)."""
    if width is None:
        if val == 0:
            return bytes([OP["PUSH0"]])
        width = max(1, (val.bit_length() + 7) // 8)
    return bytes([0x5F + width]) + val.to_bytes(width, "big")


# ---------------------------------------------------------------------------
# FIPS-202 Keccak-f[1600] reference model (lane i = x + 5y, matching the
# helper's 25-word state layout)
# ---------------------------------------------------------------------------
_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]


def _rol(v, r):
    return ((v << r) | (v >> (64 - r))) & M64


def keccak_f1600(st):
    a = list(st)
    for rnd in range(24):
        c = [a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        a = [a[i] ^ d[i % 5] for i in range(25)]
        b = [0] * 25
        for x in range(5):
            for y in range(5):
                # rho offsets
                t = {(0, 0): 0, (1, 0): 1, (2, 0): 62, (3, 0): 28, (4, 0): 27,
                     (0, 1): 36, (1, 1): 44, (2, 1): 6, (3, 1): 55, (4, 1): 20,
                     (0, 2): 3, (1, 2): 10, (2, 2): 43, (3, 2): 25, (4, 2): 39,
                     (0, 3): 41, (1, 3): 45, (2, 3): 15, (3, 3): 21, (4, 3): 8,
                     (0, 4): 18, (1, 4): 2, (2, 4): 61, (3, 4): 56, (4, 4): 14}[(x, y)]
                b[y + 5 * ((2 * x + 3 * y) % 5)] = _rol(a[x + 5 * y], t)
        a = [b[i] ^ ((~b[(i % 5 + 1) % 5 + 5 * (i // 5)]) & b[(i % 5 + 2) % 5 + 5 * (i // 5)]) & M64
             for i in range(25)]
        a = [v & M64 for v in a]
        a[0] ^= _RC[rnd]
    return a


# ---------------------------------------------------------------------------
# mini-EVM (straight-line + static jumps; enough for this runtime)
# ---------------------------------------------------------------------------
def run_evm(code, calldata, max_steps=6_000_000, hook=None):
    insns = disasm(code)
    by_pc = {pc: (op, imm) for pc, op, imm in insns}
    jumpdests = {pc for pc, op, _ in insns if op == OP["JUMPDEST"]}
    stack, mem = [], bytearray()
    gas = 0
    words_touched = 0

    def memgas(end):
        nonlocal gas, words_touched, mem
        w = (end + 31) // 32
        if w > words_touched:
            gas += 3 * (w - words_touched) + (w * w // 512 - words_touched * words_touched // 512)
            words_touched = w
        if len(mem) < w * 32:
            mem.extend(b"\x00" * (w * 32 - len(mem)))

    pc, steps = 0, 0
    while True:
        steps += 1
        if steps > max_steps:
            raise SystemExit("mini-EVM: step limit")
        if pc not in by_pc:
            raise SystemExit(f"mini-EVM: bad pc {pc}")
        op, imm = by_pc[pc]
        if hook is not None:
            hook(pc, stack, mem)
        npc = pc + 1 + len(imm)
        gas += GAS.get(op, 3 if (0x5F < op <= 0x7F or 0x80 <= op <= 0x9F) else None) or 0
        if op == 0x5F:
            stack.append(0)
        elif 0x60 <= op <= 0x7F:
            stack.append(int.from_bytes(imm, "big"))
        elif 0x80 <= op <= 0x8F:
            stack.append(stack[-(op - 0x7F)])
        elif 0x90 <= op <= 0x9F:
            n = op - 0x8F
            stack[-1], stack[-n - 1] = stack[-n - 1], stack[-1]
        elif op == OP["ADD"]:
            a, b = stack.pop(), stack.pop(); stack.append((a + b) % 2**256)
        elif op == OP["MUL"]:
            a, b = stack.pop(), stack.pop(); stack.append((a * b) % 2**256)
        elif op == OP["SUB"]:
            a, b = stack.pop(), stack.pop(); stack.append((a - b) % 2**256)
        elif op == OP["DIV"]:
            a, b = stack.pop(), stack.pop(); stack.append(0 if b == 0 else a // b)
        elif op == OP["LT"]:
            a, b = stack.pop(), stack.pop(); stack.append(1 if a < b else 0)
        elif op == OP["GT"]:
            a, b = stack.pop(), stack.pop(); stack.append(1 if a > b else 0)
        elif op == OP["EQ"]:
            a, b = stack.pop(), stack.pop(); stack.append(1 if a == b else 0)
        elif op == OP["ISZERO"]:
            stack.append(1 if stack.pop() == 0 else 0)
        elif op == OP["AND"]:
            stack.append(stack.pop() & stack.pop())
        elif op == OP["OR"]:
            stack.append(stack.pop() | stack.pop())
        elif op == OP["XOR"]:
            stack.append(stack.pop() ^ stack.pop())
        elif op == OP["NOT"]:
            stack.append(stack.pop() ^ (2**256 - 1))
        elif op == OP["SHL"]:
            s, v = stack.pop(), stack.pop(); stack.append((v << s) % 2**256 if s < 256 else 0)
        elif op == OP["SHR"]:
            s, v = stack.pop(), stack.pop(); stack.append(v >> s if s < 256 else 0)
        elif op == OP["CALLDATALOAD"]:
            o = stack.pop()
            stack.append(int.from_bytes(calldata[o:o + 32].ljust(32, b"\x00"), "big"))
        elif op == OP["CALLDATASIZE"]:
            stack.append(len(calldata))
        elif op == OP["CALLDATACOPY"]:
            d, o, s = stack.pop(), stack.pop(), stack.pop()
            memgas(d + s)
            gas += 3 * ((s + 31) // 32)
            mem[d:d + s] = calldata[o:o + s].ljust(s, b"\x00")
        elif op == OP["POP"]:
            stack.pop()
        elif op == OP["MLOAD"]:
            o = stack.pop(); memgas(o + 32)
            stack.append(int.from_bytes(mem[o:o + 32], "big"))
        elif op == OP["MSTORE"]:
            o, v = stack.pop(), stack.pop(); memgas(o + 32)
            mem[o:o + 32] = v.to_bytes(32, "big")
        elif op == OP["MSTORE8"]:
            o, v = stack.pop(), stack.pop(); memgas(o + 1)
            mem[o] = v & 0xFF
        elif op == OP["JUMP"]:
            pc = stack.pop()
            if pc not in jumpdests:
                raise SystemExit(f"mini-EVM: JUMP to non-JUMPDEST {pc}")
            continue
        elif op == OP["JUMPI"]:
            t, c = stack.pop(), stack.pop()
            if c:
                if t not in jumpdests:
                    raise SystemExit(f"mini-EVM: JUMPI to non-JUMPDEST {t}")
                pc = t
                continue
        elif op == OP["RETURN"]:
            o, s = stack.pop(), stack.pop(); memgas(o + s)
            return bytes(mem[o:o + s]), gas
        elif op == OP["REVERT"]:
            raise SystemExit("mini-EVM: REVERT")
        elif op == OP["JUMPDEST"]:
            pass
        else:
            raise SystemExit(f"mini-EVM: unhandled op {op:#x}")
        pc = npc


# ---------------------------------------------------------------------------
# core transformations
# ---------------------------------------------------------------------------
def load_core():
    hx = open(CORE_PATH).read().strip()
    core = bytes.fromhex(hx)
    got = hashlib.sha256(hx.encode()).hexdigest()
    if got != CORE_SHA256:
        raise SystemExit(f"core digest mismatch: {got} != {CORE_SHA256}")
    return core


def scan_core(insns):
    """Symbolic-stack scan of the straight-line core. Returns

      drops  set of instruction indices to delete: for every AND whose TOP
             operand is the literal 64-bit lane mask (a rotation fixup), both
             the AND and the DUPn that fed it. Deleting a DUP+AND pair is
             stack-depth-neutral, so every other DUPn/SWAPn index in the core
             keeps its meaning -- this is what makes patch 5 a purely local
             2-byte deletion.
      iota   {index of a PUSH -> its value} for the round constants that reach
             an XOR as a literal (the iota step), i.e. every constant XOR
             operand that is NOT the lane mask.

    It also proves the properties patches 4-6 rely on: the mask is pushed
    exactly once (instruction 0) and its ONLY consumers are those ANDs plus
    XORs (the lane-complement fixups), every shift amount is a literal, and
    the core is stack-neutral.
    """
    stack = []            # entries: ('c', value, origin_index) | ('s', None, None)
    drops, iota = set(), {}
    mask_pushes = 0
    mask_uses = collections.Counter()
    for i, (pc, op, imm) in enumerate(insns):
        if op == 0x5F:
            stack.append(("c", 0, i))
            continue
        if 0x60 <= op <= 0x7F:
            v = int.from_bytes(imm, "big")
            if v == M64:
                mask_pushes += 1
                if i != 0:
                    raise SystemExit(f"unexpected extra lane-mask PUSH at insn {i}")
            stack.append(("c", v, i))
            continue
        if 0x80 <= op <= 0x8F:
            stack.append(stack[-(op - 0x7F)])
            continue
        if 0x90 <= op <= 0x9F:
            n = op - 0x8F
            stack[-1], stack[-n - 1] = stack[-n - 1], stack[-1]
            continue
        nargs = 1 if op in (OP["MLOAD"], OP["CALLDATALOAD"], OP["NOT"]) else 2
        if len(stack) < nargs:
            raise SystemExit(f"core stack underflow at insn {i}")
        args = [stack.pop() for _ in range(nargs)]
        for k, a in enumerate(args):
            if a[0] == "c" and a[1] == M64:
                mask_uses[(op, k)] += 1
        if op in (OP["SHL"], OP["SHR"]) and args[0][0] != "c":
            raise SystemExit(f"dynamic shift amount at insn {i}")
        if op == OP["AND"] and args[0][0] == "c" and args[0][1] == M64:
            if not (0x80 <= insns[i - 1][1] <= 0x8F):
                raise SystemExit(f"lane-mask AND at insn {i} not fed by a DUP")
            drops.add(i - 1)
            drops.add(i)
        if op == OP["XOR"] and args[1][0] == "c" and args[1][1] != M64:
            o = args[1][2]
            if not 0x60 <= insns[o][1] <= 0x7F:
                raise SystemExit(f"iota constant at insn {i} not from a PUSH")
            if o in iota:
                raise SystemExit(f"iota PUSH at insn {o} used twice")
            iota[o] = args[1][1]
        if op != OP["MSTORE"]:
            stack.append(("s", None, None))
    if stack:
        raise SystemExit(f"core not stack-neutral: leftover {len(stack)}")
    if mask_pushes != 1:
        raise SystemExit(f"expected exactly 1 lane-mask PUSH, saw {mask_pushes}")
    # The lane mask must only ever be an AND's top operand (rotation fixup,
    # deleted by patch 5) or an XOR's second operand (a lane-complement fixup,
    # which patch 4 widens to 256 bits). Any other use would break Q-form.
    allowed = {(OP["AND"], 0), (OP["XOR"], 1)}
    for key, n in mask_uses.items():
        if key not in allowed:
            raise SystemExit(f"unexpected lane-mask use {key} x{n}")
    if mask_uses[(OP["AND"], 0)] != len(drops) // 2:
        raise SystemExit("mask AND accounting mismatch")
    return drops, iota, mask_uses[(OP["XOR"], 1)]


def patch_core(core):
    """Apply patches 1-6 (see module docstring). Returns the patched body,
    which expects the Q-FORM state at memory 0x320..0x640 and falls through at
    the end with the permuted Q-form state at 0x320..0x640 and a neutral
    stack."""
    insns = disasm(core)
    # sanity: straight-line
    for _, op, _ in insns:
        if op in (OP["JUMP"], OP["JUMPI"], OP["JUMPDEST"]):
            raise SystemExit("core is not straight-line")
    # strip trailing PUSH2 0x320; DUP1; RETURN
    tail = insns[-3:]
    if not (tail[0][1] == 0x61 and tail[0][2] == b"\x03\x20"
            and tail[1][1] == 0x80 and tail[2][1] == OP["RETURN"]):
        raise SystemExit("unexpected core tail")
    insns = insns[:-3]

    drops, iota, n_xor_mask = scan_core(insns)

    out = bytearray()
    i = 0
    n_cdl = 0
    n_rc = 0
    n_iota = 0
    n_drop = 0
    while i < len(insns):
        pc, op, imm = insns[i]
        # patch 5: delete the `DUPn(mask); AND` rotation fixups
        if i in drops:
            n_drop += 1
            i += 1
            continue
        # patch 4: the top-level lane-mask variable widens to all-256-bits, so
        # the core's `xor(v, mask)` lane complements complement all four copies.
        # PUSH0; NOT is 2 bytes where PUSH8 0xff..ff was 9.
        if i == 0:
            if not (op == 0x67 and int.from_bytes(imm, "big") == M64):
                raise SystemExit("core insn 0 is not PUSH8 <lane mask>")
            out += bytes([OP["PUSH0"], OP["NOT"]])
            i += 1
            continue
        # patch 2+6: PUSH1 a; PUSH1 1; PUSH1 s; SHL; SUB -> PUSH<rep4((1<<s)-a)>
        if (op == 0x60 and i + 4 < len(insns)
                and insns[i + 1][1] == 0x60 and insns[i + 1][2] == b"\x01"
                and insns[i + 2][1] == 0x60 and insns[i + 2][2] in (b"\x3f", b"\x40")
                and insns[i + 3][1] == OP["SHL"] and insns[i + 4][1] == OP["SUB"]):
            a = imm[0]
            s = insns[i + 2][2][0]
            out += push(rep4((1 << s) - a))
            n_rc += 1
            i += 5
            continue
        # patch 6: iota round constants are replicated into all four lane copies
        if i in iota:
            out += push(rep4(iota[i]))
            n_iota += 1
            i += 1
            continue
        # patch 1: (PUSH0|PUSH1 off|PUSH2 off); CALLDATALOAD -> PUSH2 off+0x320; MLOAD
        if (i + 1 < len(insns) and insns[i + 1][1] == OP["CALLDATALOAD"]
                and (op == 0x5F or op in (0x60, 0x61))):
            off = 0 if op == 0x5F else int.from_bytes(imm, "big")
            if off % 32 or off > 0x300:
                raise SystemExit(f"unexpected calldataload offset {off:#x}")
            out += push(off + 0x320, 2) + bytes([OP["MLOAD"]])
            n_cdl += 1
            i += 2
            continue
        if op == OP["CALLDATALOAD"]:
            raise SystemExit(f"calldataload at pc {pc} not preceded by PUSH")
        if op == 0x5F or 0x60 <= op <= 0x7F:
            out += bytes([op]) + imm
        else:
            out += bytes([op])
        i += 1
    if n_cdl != 50:
        raise SystemExit(f"expected 50 calldataload patches, made {n_cdl}")
    if n_rc != 5:
        raise SystemExit(f"expected 5 round-constant patches, made {n_rc}")
    if n_iota != 19:
        raise SystemExit(f"expected 19 iota replications, made {n_iota}")
    if n_rc + n_iota != 24:
        raise SystemExit("iota sites do not cover 24 rounds")
    if n_drop != 2 * 696:
        raise SystemExit(f"expected 696 mask fixups (29/round), dropped {n_drop // 2}")
    if n_xor_mask == 0:
        raise SystemExit("no lane-complement XOR found; patch 4 would be dead")
    return bytes(out)


def check_stack_neutral(body):
    depth, maxd = 0, 0
    for _, op, imm in disasm(body):
        if op == 0x5F or 0x60 <= op <= 0x7F:
            depth += 1
        elif 0x80 <= op <= 0x8F:
            if depth < op - 0x7F:
                raise SystemExit("body DUP underflow")
            depth += 1
        elif 0x90 <= op <= 0x9F:
            if depth < op - 0x8E:
                raise SystemExit("body SWAP underflow")
        else:
            pops = {0x01: 2, 0x03: 2, 0x16: 2, 0x17: 2, 0x18: 2, 0x19: 1,
                    0x1B: 2, 0x1C: 2, 0x51: 1, 0x52: 2}[op]
            pushes = 0 if op == 0x52 else 1
            if depth < pops:
                raise SystemExit(f"body underflow at op {op:#x}")
            depth += pushes - pops
        maxd = max(maxd, depth)
    if depth != 0:
        raise SystemExit(f"body not stack-neutral: leftover {depth}")
    if maxd > 16:
        raise SystemExit(f"body max stack depth {maxd} > 16")
    return maxd


# ---------------------------------------------------------------------------
# wrapper assembly
# ---------------------------------------------------------------------------
GREV_MASKS = [
    (8,  int("ff00" * 16, 16)),
    (16, int("ffff0000" * 8, 16)),
    (32, int("ffffffff00000000" * 4, 16)),
]


def emit_grev():
    """[.., w] -> [.., byte-reversed-per-8-byte-group(w)]

    One mask per stage: with a = w & M (the high half of every 2s-bit field),
    the low half is exactly w ^ a, so the swap is or(shr(s,a), shl(s, w^a)).
    Same 11 opcodes as the two-mask form but 32 bytes shorter per stage, and
    this emitter is instantiated 10x (5 absorb + 5 squeeze)."""
    b = bytearray()
    for sh, mh in GREV_MASKS:
        b += bytes([0x80])                     # DUP1              [w, w]
        b += push(mh, 32) + bytes([OP["AND"]])  # a = w & M        [w, a]
        b += bytes([0x80])                     # DUP1              [w, a, a]
        b += push(sh, 1) + bytes([OP["SHR"]])   #                  [w, a, a>>s]
        b += bytes([0x91])                     # SWAP2             [a>>s, a, w]
        b += bytes([OP["XOR"]])                # b = w ^ a         [a>>s, b]
        b += push(sh, 1) + bytes([OP["SHL"]])   #                  [a>>s, b<<s]
        b += bytes([OP["OR"]])
    return bytes(b)


def emit_absorb():
    """[K, p] -> [K, p]; XORs the 136-byte rate block at memory p into the
    Q-form state lanes 0..16 (at 0x320..0x540), with per-8-byte-group byte
    reversal. K == QK must sit directly below p: each extracted 64-bit message
    lane is replicated with one MUL before it is XORed into the (Q-form) state
    word, which is the only caller-visible cost of Q-form on the batch path
    (17 x (DUPn + MUL) = 136 gas per rate block)."""
    b = bytearray()
    for j in range(4):
        b += bytes([0x80])                     # DUP1 (p)
        if j:
            b += push(32 * j, 1) + bytes([OP["ADD"]])
        b += bytes([OP["MLOAD"]])
        b += emit_grev()                       # [K, p, v]
        for k in range(4):
            lane = 0x320 + 32 * (4 * j + k)
            if k < 3:
                b += bytes([0x80])             # DUP1 (v)
            if k == 0:
                b += push(0xC0, 1) + bytes([OP["SHR"]])
            elif k < 3:
                b += push(0xC0 - 64 * k, 1) + bytes([OP["SHR"]])
                b += push(M64, 8) + bytes([OP["AND"]])
            else:
                b += push(M64, 8) + bytes([OP["AND"]])
            # replicate: stack is [K, p, v, lane] for k<3, else [K, p, lane]
            b += bytes([0x83 if k < 3 else 0x82, OP["MUL"]])
            b += push(lane, 2) + bytes([OP["MLOAD"]])
            b += bytes([OP["XOR"]])
            b += push(lane, 2) + bytes([OP["MSTORE"]])
    # lane 16: bytes 128..136 of the block (byte-reversed like the others)
    b += bytes([0x80]) + push(0x80, 1) + bytes([OP["ADD"], OP["MLOAD"]])
    b += emit_grev()
    b += push(0xC0, 1) + bytes([OP["SHR"]])
    b += bytes([0x82, OP["MUL"]])              # [K, p, lane] -> replicate
    b += push(0x520, 2) + bytes([OP["MLOAD"], OP["XOR"]])
    b += push(0x520, 2) + bytes([OP["MSTORE"]])
    return bytes(b)


def emit_squeeze():
    """[] -> []; writes the 136-byte squeeze block (lanes 0..16, byte-reversed)
    to memory 0x00..0x88 (the dead round buffer).

    Q-form makes this CHEAPER than a positional shift would be: word k of a
    Q-form lane is the lane value itself, so lane j of an output word is
    extracted with a single AND against a pre-shifted mask instead of a
    shift+mask pair. Only the top field (bits 192..255) still uses shl, whose
    own overflow does the masking."""
    b = bytearray()
    for j in range(5):
        base = 0x320 + 128 * j
        for k in range(4):
            b += push(base + 32 * k, 2) + bytes([OP["MLOAD"]])
            if k == 0:
                b += push(0xC0, 1) + bytes([OP["SHL"]])
            else:
                b += push(M64 << (64 * (3 - k))) + bytes([OP["AND"], OP["OR"]])
        b += emit_grev()
        b += (push(32 * j, 1) if j else bytes([OP["PUSH0"]])) + bytes([OP["MSTORE"]])
    return bytes(b)


def emit_lane_map(op_bytes, konst, src=OP["MLOAD"]):
    """[] -> []; `mstore(a, <op>(<src>(off), konst))` over the 25 state words at
    0x320..0x640, with konst held on the stack (DUP2). src == MLOAD reads the
    state in place; src == CALLDATALOAD reads lane i from calldata offset 32*i
    (the raw entry's Q-form lift, which therefore needs no CALLDATACOPY)."""
    b = bytearray(push(konst))
    for i, a in enumerate(range(0x320, 0x320 + 800, 32)):
        off = 32 * i if src == OP["CALLDATALOAD"] else a
        b += push(off, 2) + bytes([src, 0x81]) + op_bytes
        b += push(a, 2) + bytes([OP["MSTORE"]])
    b += bytes([OP["POP"]])
    return bytes(b)


def assemble(body):
    """Two-pass assembly of the full runtime. Items are raw bytes, ('label', n)
    definitions, or ('ref', n) 2-byte push-target references."""
    items = []

    def raw(bs):
        items.append(bs)

    def label(n):
        items.append(("label", n))

    def ref(n):
        items.append(("ref", n))

    # --- dispatcher: raw permutation iff calldatasize == 800
    raw(bytes([OP["CALLDATASIZE"]]) + push(0x320, 2) + bytes([OP["EQ"]]))
    ref("rawentry"); raw(bytes([OP["JUMPI"]]))

    # --- batch init (fallthrough)
    # calldatacopy(0x6c0, 0, calldatasize)
    raw(bytes([OP["CALLDATASIZE"], OP["PUSH0"]]) + push(0x6C0, 2) + bytes([OP["CALLDATACOPY"]]))
    # mstore8(0x6c0 + calldatasize, 0x1f)   -- domain padding byte
    raw(push(0x1F, 1) + bytes([OP["CALLDATASIZE"]]) + push(0x6C0, 2) + bytes([OP["ADD"], OP["MSTORE8"]]))
    # nb = calldatasize/136 + 1
    raw(push(0x88, 1) + bytes([OP["CALLDATASIZE"], OP["DIV"]]) + push(1, 1) + bytes([OP["ADD"]]))
    # a = 0x6a0 + nb*136 (word whose LAST byte is the final pad position);
    # mstore(a, mload(a) | 0x80)
    raw(bytes([0x80]) + push(0x88, 1) + bytes([OP["MUL"]]) + push(0x6A0, 2) + bytes([OP["ADD"]]))
    raw(bytes([0x80, OP["MLOAD"]]) + push(0x80, 1) + bytes([OP["OR"], 0x81, OP["MSTORE"], OP["POP"]]))
    # slots: 0x660 = nb, 0x680 = 0x6c0, 0x6a0 = 1
    raw(push(0x660, 2) + bytes([OP["MSTORE"]]))
    raw(push(0x6C0, 2) + push(0x680, 2) + bytes([OP["MSTORE"]]))
    raw(push(1, 1) + push(0x6A0, 2) + bytes([OP["MSTORE"]]))

    # --- sponge loop head
    label("loop")
    raw(bytes([OP["JUMPDEST"]]) + push(0x660, 2) + bytes([OP["MLOAD"], 0x80]))
    ref("more"); raw(bytes([OP["JUMPI"]]))
    # counter == 0: done. raw mode returns the state; batch mode squeezes.
    raw(bytes([OP["POP"]]) + push(0x6A0, 2) + bytes([OP["MLOAD"]]))
    ref("squeeze"); raw(bytes([OP["JUMPI"]]))
    # raw mode returns 25 CLEAN lanes: undo Q-form (one AND per lane).
    label("@qout")
    raw(emit_lane_map(bytes([OP["AND"]]), M64))
    raw(push(0x320, 2) + bytes([0x80, OP["RETURN"]]))

    # --- absorb one block, then fall through into the permutation
    label("more")
    raw(bytes([OP["JUMPDEST"]]))                                   # [cnt]
    raw(push(1, 1) + bytes([0x90, OP["SUB"]]) + push(0x660, 2) + bytes([OP["MSTORE"]]))
    raw(push(QK))                                                   # [K]
    raw(push(0x680, 2) + bytes([OP["MLOAD"]]))                      # [K, p]
    raw(emit_absorb())                                              # [K, p]
    raw(push(0x88, 1) + bytes([OP["ADD"]]) + push(0x680, 2) + bytes([OP["MSTORE"]]))
    raw(bytes([OP["POP"]]))

    # --- the permutation body (Q-form state 0x320..0x640 in place, stack-neutral)
    label("body")
    raw(bytes([OP["JUMPDEST"]]))
    raw(body)
    ref("loop"); raw(bytes([OP["JUMP"]]))

    # --- raw entry: lift the 800-byte calldata state straight into the Q-form
    #     state words at 0x320 (one CALLDATALOAD + MUL per lane -- no
    #     CALLDATACOPY, since every byte is read exactly once anyway), run once
    label("rawentry")
    raw(bytes([OP["JUMPDEST"]]))
    raw(emit_lane_map(bytes([OP["MUL"]]), QK, src=OP["CALLDATALOAD"]))
    label("@qin")
    ref("body"); raw(bytes([OP["JUMP"]]))

    # --- squeeze: 136 bytes to 0x00..0x88, return
    label("squeeze")
    raw(bytes([OP["JUMPDEST"]]))
    raw(emit_squeeze())
    raw(push(0x88, 1) + bytes([OP["PUSH0"], OP["RETURN"]]))

    # pass 1: layout
    pos, labels = 0, {}
    for it in items:
        if isinstance(it, tuple) and it[0] == "label":
            labels[it[1]] = pos
        elif isinstance(it, tuple) and it[0] == "ref":
            pos += 3
        else:
            pos += len(it)
    # pass 2: emit
    out = bytearray()
    for it in items:
        if isinstance(it, tuple) and it[0] == "label":
            continue
        if isinstance(it, tuple) and it[0] == "ref":
            out += push(labels[it[1]], 2)
        else:
            out += it
    return bytes(out), labels


# ---------------------------------------------------------------------------
# verification
# ---------------------------------------------------------------------------
def verify(runtime, core, labels):
    insns = disasm(runtime)
    jumpdests = {pc for pc, op, _ in insns if op == OP["JUMPDEST"]}
    for name, pos in labels.items():
        if name.startswith("@"):
            continue          # probe marker, not a jump target
        if pos not in jumpdests:
            raise SystemExit(f"label {name} at {pos} is not a JUMPDEST")
    # every static PUSH2-before-JUMP/JUMPI targets a JUMPDEST
    for i, (pc, op, imm) in enumerate(insns):
        if op in (OP["JUMP"], OP["JUMPI"]):
            ppc, pop, pimm = insns[i - 1]
            if pop != 0x61:
                raise SystemExit(f"dynamic jump at pc {pc}")
            if int.from_bytes(pimm, "big") not in jumpdests:
                raise SystemExit(f"jump at pc {pc} to non-JUMPDEST")
    if len(runtime) > EIP170_LIMIT:
        raise SystemExit(f"runtime {len(runtime)} exceeds EIP-170 {EIP170_LIMIT}")
    if runtime[0] == 0xEF:
        raise SystemExit("EIP-3541: runtime must not start with 0xEF")

    rnd = __import__("random").Random(0xF1600)

    # Q-form invariant probe: at @qin (raw entry, just after the lift) and at
    # @qout (after the last permutation, before the unlift) every one of the 25
    # state words must be EXACTLY the 4-fold replication of a 64-bit lane -- the
    # input state going in, the FIPS-202 model's output coming out. This checks
    # the REPRESENTATION directly, not just the masked 800-byte return value.
    probes = {"in": [], "out": []}

    def probe(pc, stack, mem):
        if pc == labels["@qin"]:
            probes["in"].append([int.from_bytes(mem[0x320 + 32 * i:0x340 + 32 * i], "big")
                                 for i in range(25)])
        elif pc == labels["@qout"]:
            probes["out"].append([int.from_bytes(mem[0x320 + 32 * i:0x340 + 32 * i], "big")
                                  for i in range(25)])

    # raw path: vs FIPS-202 model and vs the original core, on chained states
    st = [rnd.getrandbits(64) for _ in range(25)]
    raw_gas = None
    for _ in range(20):
        cd = b"".join(v.to_bytes(32, "big") for v in st)
        probes["in"].clear(); probes["out"].clear()
        got, g = run_evm(runtime, cd, hook=probe)
        want = keccak_f1600(st)
        old, _ = run_evm(core, cd)
        if got != b"".join(v.to_bytes(32, "big") for v in want):
            raise SystemExit("raw path mismatch vs FIPS-202 model")
        if got != old:
            raise SystemExit("raw path mismatch vs original core")
        if (probes["in"] != [[rep4(v) for v in st]]
                or probes["out"] != [[rep4(v) for v in want]]):
            raise SystemExit("Q-form invariant violated on the raw path")
        raw_gas = g
        st = want

    # batch path: vs hashlib.shake_256 over block-boundary message lengths
    batch_gas = {}
    for n in (0, 1, 17, 98, 135, 136, 137, 271, 272, 559, 666, 832, 833, 1360):
        msg = bytes(rnd.getrandbits(8) for _ in range(n))
        got, g = run_evm(runtime, msg)
        want = hashlib.shake_256(msg).digest(136)
        if got != want:
            raise SystemExit(f"batch path mismatch for len {n}")
        batch_gas[n] = g
    return raw_gas, batch_gas


def keccak256(data):
    # keccak-256 via our own f1600 (no external deps): rate 136, 0x01 padding
    st = [0] * 25
    msg = bytearray(data)
    msg.append(0x01)
    while len(msg) % 136:
        msg.append(0)
    msg[-1] |= 0x80
    for off in range(0, len(msg), 136):
        for k in range(17):
            st[k] ^= int.from_bytes(msg[off + 8 * k: off + 8 * k + 8], "little")
        st = keccak_f1600(st)
    return b"".join(st[k].to_bytes(8, "little") for k in range(4))


def sync_sol_constant(runtime_hex):
    src = open(SOL_PATH).read()
    pat = re.compile(r'(bytes constant _F1600_CODE_170 =\s*\n\s*hex")[0-9a-fA-F]+(";)')
    if not pat.search(src):
        raise SystemExit("could not locate _F1600_CODE_170 in test/ZZZ_FastKeccak170.sol")
    open(SOL_PATH, "w").write(pat.sub(lambda m: m.group(1) + runtime_hex + m.group(2), src))


def main():
    check = "--check" in sys.argv
    core = load_core()
    body = patch_core(core)
    maxd = check_stack_neutral(body)
    runtime, labels = assemble(body)
    raw_gas, batch_gas = verify(runtime, core, labels)
    hexstr = runtime.hex()
    ch = keccak256(runtime).hex()
    print(f"core: {len(core)} bytes -> runtime: {len(runtime)} bytes "
          f"(EIP-170 headroom {EIP170_LIMIT - len(runtime)})")
    print(f"body max stack depth: {maxd}")
    print(f"raw permutation callee gas: {raw_gas}")
    print(f"batch callee gas: " + ", ".join(f"{n}B={g}" for n, g in sorted(batch_gas.items())))
    print(f"keccak256 (F1600_CODEHASH pin): 0x{ch}")
    print(f"sha256(hex): {hashlib.sha256(hexstr.encode()).hexdigest()}")
    if check:
        cur = open(OUT_PATH).read().strip()
        if cur != hexstr:
            raise SystemExit("--check: helpers/f1600_170.hex does NOT match this build")
        print("--check: helpers/f1600_170.hex matches this build")
        return
    with open(OUT_PATH, "w") as fh:
        fh.write(hexstr)
    sync_sol_constant(hexstr)
    print(f"wrote {OUT_PATH} and synced _F1600_CODE_170 in {SOL_PATH}")


if __name__ == "__main__":
    main()
