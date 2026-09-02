# Every Optimization, Explained
### A FIPS 204 ML-DSA-44 verifier at 1.23M gas on the EVM, against 8.09M for the state of the art

> **FOR SECURITY RESEARCH ONLY — NOT FOR PRODUCTION USE.** This is unaudited
> research code. It is machine-checked (see `FORMAL_VERIFICATION.md`) but has had
> **no professional implementation audit and no independent cryptographic
> review**, and it is not deployed. Read `SAFETY.md` before doing anything with it.

For each technique: what it does, why, how it works, how security is preserved,
and the tradeoffs. All gas numbers are measured (Foundry, solc 0.8.30,
optimizer runs = 10000, via_ir = true, evm_version = osaka, current mainnet
schedule). The one authoritative figure is the end-to-end
`MLDSA44Verifier.verify()` call: **1,226,311 gas**, against the reproduced
ZKNox baseline of **8,094,831**, about **6.6×**.

The document is organised by subsystem. Every figure is a property of the
shipped artifact, an A/B measurement of one named alternative against the
shipped form on the same fixture, or a figure from the reproduced baseline.
Nothing here is a running total.

### The five-minute background, for readers arriving cold

**What an ML-DSA-44 verification computes.** Given a public key `(ρ, t1)`, a
message `M` and a signature `(c̃, z, h)`, the verifier hashes the message into
μ (SHAKE-256); expands the challenge hash c̃ into a sparse polynomial `c`
(SHAKE-256 rejection sampling, "SampleInBall"); computes the matrix identity
`w′ = Â·ẑ − ĉ·t̂1` in the NTT domain; rounds `w′` with the signature's hint
bits (`UseHint`); hashes the rounded result and requires it to equal c̃. All
the arithmetic is on 256-coefficient polynomials modulo `q = 8,380,417`
(a 23-bit prime). The transform between coefficient and NTT domain is the
number-theoretic transform, an FFT over this field. Nine 256-point transforms
run per verification.

**Where the gas goes, and why this is hard on the EVM.** Three cost centers
dominate: SHAKE-256 (the EVM's native `KECCAK256` opcode cannot compute it, see
§2.1, so the Keccak permutation is paid for in ordinary opcodes), the NTTs,
and getting 2,420 bytes of signature decoded into arithmetic-friendly form.
Three EVM facts shape every decision in this document. Memory costs grow
*quadratically* with the peak ever touched, so representation size is a gas
cost even when the arithmetic is free. A 256-bit word costs the same to
multiply whether you use 23 bits of it or all 256, so packing four
coefficients per word ("SWAR", SIMD within a register) quarters the
arithmetic. Loop framing, pointer bumps and stack shuffling cost more than
the loads and stores they surround, which is what makes fusion and unrolling
pay. Every "the EVM charges ~X for Y" figure comes from §1's calibration
suite.

### The shipped numbers

| | ZKNox baseline | shipped verifier |
|---|---:|---:|
| end-to-end `verify()` | 8,094,831 | **1,226,311** |
| Keccak-f[1600], per permutation | 153,267 | **41,664** |
| 256-point NTT, forward / inverse | 182,470 / 215,899 | **45,701 / 54,419** |
| peak EVM memory | 953 KB | **~41 KB** |
| verifier runtime bytes (EIP-170 margin) | — | **24,032** (544 spare) |
| Keccak helper runtime bytes (EIP-170 margin) | — | **21,622** (2,954 spare) |

Both columns of the two micro-benchmark rows are compiled by the *same code
generator*, and every figure in them is printed by a named test in this tree, so
each is checkable and none of the ratios is a codegen artifact. The NTT rows use
the same *measurement condition* on both sides. The permutation row does not,
and both readings are given. The baseline permutation is one in-contract call
on a random state (`test_gas_f1600_reference`, `test/ZZZ_fastkeccak.t.sol`).
The shipped one is the `finalHash` stage of `test_profile_10_stages`
(`test/PROFILE_E2E.t.sol`) divided by its seven permutations, 291,649 / 7 =
41,664 all-in including sponge glue; one warm standalone helper call is 41,573
(`test_gas_f1600Fast170`, `test/ZZZ_fastkeccak170.t.sol`). Both NTT columns are
one transform at fresh memory with the twiddle-table build inside the bracket:
`testGasV1Baseline` / `testGasV3` (`test/ZZZ_nttvariants.t.sol`) and
`testGasInvV1Baseline` / `testGasInvV3` (`test/ZZZ_invntt.t.sol`). With the
table hoisted the way `_wPrimeRows` hoists it across all nine transforms
(§5.4), the shipped transforms measure **44,931 / 53,591** on real signature
data (`test_profile_20_ntt_layers`, same file as the stage profile). The ratios
are 3.7× on the permutation and 4.0× on both transforms. See §9.1 for why
baseline figures measured under solc's legacy code generator run 7-9% above
these.

---

## 1. The method: profile first, calibrate the toolchain

**What.** Nothing here is optimized against intuition. An instrumented replica of
the ZKNox verifier carries `gasleft()` brackets around every stage, and a
calibration suite measures raw EVM cost shapes (loop iteration ≈ 45-55 gas of
framing, straight-line `mulmod` ≈ 23 gas all-in, stack traffic ≈ 2× naive opcode
counting, `keccak256` opcode = 151 gas for a full rate block).

**Why.** Intuition about EVM gas is reliably wrong at the 2-3× level. Two facts
from the profile drive everything below: SHAKE is 37% of all baseline gas (3.0M),
and ~1.8M gas hides in *quadratic memory expansion* (the baseline peaks at 953KB
of EVM memory). That cost belongs to no single line and is invisible unless you
look for it.

**Security.** None affected. Measurement only.

**Tradeoff.** None. This is the step most optimization efforts skip, and it is
why most of them plateau.

---

## 2. SHAKE-256: the Keccak-f[1600] helper contract

### 2.1 There is no KECCAK256-opcode shortcut

**What.** A negative result that fixes the floor of the whole hash budget: the
151-gas KECCAK256 opcode cannot compute any part of SHAKE.

**How it works.** keccak256 and SHAKE256 share the same permutation and even the
same rate (136 bytes). They differ in two ways, each enough to block a shortcut.

(1) Domain-separation padding. keccak256 XORs `0x01`, SHAKE XORs `0x1F` into the
final rate block. The opcode always applies *its* padding to *your* message, so
the absorbed final block always differs in bits you cannot touch. Making the
states collide anyway is a cross-domain Keccak collision.

(2) Output width. The opcode reveals only 32 bytes of the final state. ML-DSA
needs a 64-byte μ and a 7-block absorption whose chained 1600-bit states are
never exposed.

**Why this matters for security.** The compliant path's hash cost is
*irreducible* below 9 × cost(permutation). Anyone claiming a cheaper
"SHAKE via keccak opcode" is either non-compliant or wrong.

**Tradeoff.** None; it saves chasing a dead end. The exact permutation count
(μ: 1, SampleInBall: 1, w1-hash: 7, for short messages) is also where the last
budget line is pinned.

### 2.2 Rewriting Keccak-f[1600]: 153,267 → 41,664 gas per permutation

**What.** ML-DSA *requires* SHAKE-128/256 (Keccak sponges). The EVM has a KECCAK256
opcode but it cannot be used for SHAKE (§2.1), so the permutation must be implemented
in contract code.

ZKNox's implementation costs **153,267** gas per permutation as this tree compiles
it: one in-contract call on a random state, printed by `test_gas_f1600_reference` in
`test/ZZZ_fastkeccak.t.sol`, and via-IR like everything else here (§9.1). Optimism's
production `lib-keccak` (the best published implementation, used in their fault
proofs) measures 104,309 on the same toolchain (`testOpKeccakGasAndCrossCheck`,
`test/ZZZ_opkeccak.t.sol`).

Ours is **41,664** all-in per permutation where it actually runs: the 291,649-gas
seven-permutation `finalHash` stage of `test_profile_10_stages` divided by seven,
sponge glue included. Isolated, one warm helper call measures **41,570** end to
end (41,373 of callee execution; `test_gas_f1600Fast170` in
`test/ZZZ_fastkeccak170.t.sol` prints 41,573 for it on the current tree, and the
batched entry of §2.5 is cheaper still, 41,383 marginal per rate block). That is
**2.5× faster** than the best published, bit-exact against both. The four
structural layers below account for 153,267 → 44,750 per permutation; §2.3's
Q-form representation accounts for the remaining 3,180.

**How.** Four layers:

1. *Byte granularity.* The baseline kept the sponge buffer as `uint8[200]`, one
   full 32-byte EVM word per byte, and absorbed/squeezed one byte at a time through
   bounds-checked Solidity loops (SampleInBall literally called `shakeSqueeze(ctx, 1)`
   per rejection byte). We absorb and squeeze in full 64-bit lanes with word-level
   XORs.
2. *Per-call setup.* The baseline rebuilt the round-constant/rotation/permutation
   tables in memory on every call. We generate the 24 rounds fully unrolled with all
   constants inline: no tables, no loops, no dynamic shifts.
3. *Compile as a standalone Yul object.* solc's inline-assembly codegen addresses
   memory relative to a runtime base pointer (PUSH+DUP+ADD per access) and spills
   aggressively. Compiling the permutation as its own contract with compile-time-constant
   memory addresses (state at 0x000, scratch at 0x320) removes ~675 gas/round of
   addressing overhead. The caller does one `staticcall` per permutation (~200 gas,
   included in every per-permutation figure quoted here).
4. *Bit-level codegen surgery.* Byte-patching solc's 15-gas reconstruction of the
   64-bit mask into a PUSH8 at ~700 sites; operand-ordering to kill one SWAP per
   rotation; and *lane-complementing chi* (the standard Keccak trick, found here via
   beam search over complement-flag evolution): storing selected lanes complemented
   removes ~19 of 25 NOT ops per round, with flags provably returning to zero after
   the final (24th) round of the permutation (no exit fixup).

**Why it preserves security.** The output is bit-identical to the reference
permutation: verified against ZKNox's f1600 AND Optimism's LibKeccak on random
chained states, against a FIPS-202 Python model for every generated binary, and
against official SHAKE256 KATs (empty string, single-block, multi-block,
long-squeeze, and the exact 832-byte ML-DSA shape). The check is equality, not
statistics.

**Tradeoffs.** (a) The unrolled code is generated, not hand-written. Auditors
review the generator + the equivalence tests rather than 25KB of Yul. (b) It needs
its own contract (see §2.4). (c) Each permutation pays a ~200-gas call. The
compliant path needs exactly 9 permutations (§2.1), so the SHAKE budget falls from
~3.00M to roughly 0.38M (9 permutations + sponge glue; ~0.40M with SampleInBall's
rejection sampling, which is how the summary table counts it).

### 2.3 Q-form: making the 256-bit word its own rotation ring, −3,180 gas/permutation

**What.** By opcode census the permutation core sits at its structural floor: a
per-round count matching the dataflow minimum (§2.7). That census is about
*dataflow*. It is silent on *representation*.

Holding each 64-bit Keccak lane **4-fold replicated** inside its 256-bit word
deletes every masking operation in the permutation: a **gross −4,176 gas and
−1,392 bytes per permutation** (696 `DUPn; AND` pairs, 2 opcodes and 2 bytes
each). The raw entry then pays ~960 of that back, lifting 25 lanes in and
masking 25 out (see below), so the **net measurement is −3,180**: 44,750 →
**41,570** per permutation. The 832-byte final hash, where the lift is paid per
rate block instead, goes 319,415 → **291,214**. End to end, with the two smaller
companions below, **−36,669** under legacy codegen and **−36,563** under the
via-IR pipeline the tree ships (§9.1). The two are very nearly independent, but
not exactly, so the combined figure is measured, not added.

**How.** The EVM has no rotate instruction, so a 64-bit lane rotation is
`DUP1; PUSH a; SHR; SWAP1; PUSH b; SHL; OR`, and then a **mask**,
`DUPn(0xff..ff); AND`, because the `SHL` half overflows past bit 63.
Keccak-f[1600] performs 29 rotations per round (24 non-zero ρ offsets plus θ's
five `rot1`s), so an unreplicated core spends 29 × (DUP + AND) = 58 opcodes =
174 gas per round on masking alone.

Store the lane as `rep4(v) = v | v<<64 | v<<128 | v<<192` instead, i.e. fill the
word, and the mask becomes unnecessary, exactly:

1. *The word is the ring.* For a 64-periodic `W`, `or(shl(r,W), shr(64-r,W))`
   equals `rep4(rotl64(v,r))` with no mask: bit *i* of the `shr` term is
   `v[(i−r) mod 64]` for every `i < 192+r`, bit *i* of the `shl` term is
   `v[(i−r) mod 64]` for every `i ≥ r`, and those two ranges cover 0..255.
   **The bits `SHL` pushes past bit 255 are precisely the bits `SHR` brings
   back.** The core's existing shift amounts work unchanged, because
   `64−r ≡ 256−r` modulo the 64-bit period.
2. *Every other step is bitwise.* θ's XORs, χ's and/or/andnot forms, ι's XOR
   and the lane complements of §2.2 all preserve 64-periodicity, so the
   invariant is closed under the whole round with no fixups anywhere. χ in
   particular keeps its exact opcode count.

So on the pinned artifact this is a **pure deletion**, which is what makes it
safe to do to bytecode whose generator is lost. `DUPn; AND` pushes one and pops
two, so removing the pair is **stack-depth-neutral** and every other
`DUPn`/`SWAPn` index in the 13,396-instruction body keeps its meaning.
`tools/build_f1600_batch.py` carries a symbolic-stack pass (`scan_core`) that
*proves* the preconditions instead of assuming them: the lane mask is pushed
exactly once, its only consumers are those 696 ANDs and 22 lane-complement XORs
(any other use aborts the build), every shift amount is a literal, each ι
literal reaches its XOR from a single-use PUSH. The three patches are then:
widen the mask variable to all-256-bits (which is exactly the fixup the 22
complements need, at zero opcodes), delete the 696 `DUPn; AND` pairs, and
replicate the 24 ι constants.

The lift is paid only at the representation boundary, and Q-form is *resident*
in the callee's memory so the batched path pays it per rate block rather than
per permutation: the absorb replicates each extracted message lane with one
`MUL` (+136 gas/block), the squeeze gets *cheaper* (field *k* of a Q-form word
already holds the lane, so extraction is one `AND` against a pre-shifted mask
instead of shift+mask), and the raw entry lifts 25 lanes in and masks 25 out
(~960 gas, on 1 of the 9 permutations).

**Two companions in the same representation change.** The raw entry needs no
800-byte `CALLDATACOPY`: each lane is read straight from calldata by the lift,
since every byte is read exactly once anyway (−83). And SampleInBall's absorb is
specialized: absorbing one rate block into the **zero** sponge state is
*assignment*, not XOR-with-reload, so its 32-byte c̃ becomes six stores (lanes
0–3 from one byte-group reversal, lane 4 = the `0x1f` domain byte, lane 16 =
the `0x80` final bit) instead of a general 17-lane absorb (−1,170).

**Why it preserves security.** Callers cannot observe Q-form: **both** helper
protocols are stated in clean 64-bit lanes, byte-for-byte, and the lift/unlift
live entirely inside the callee. The check is unchanged: bit-exactness, not
review. The raw path is differentially tested against the FIPS-202 model *and*
against the unpatched core binary on 20 chained states inside the builder, the
batched path against `hashlib.shake_256` on 14 block-boundary lengths, and the
whole suite re-checks the SHAKE256 KATs (including the 832-byte ML-DSA shape),
the two independent implementations and the ACVP chain. One check is specific
to this representation: a **Q-form invariant probe** reads the 25 state words
out of the mini-EVM's memory after the entry lift and after the last round and
requires each to be *exactly* `rep4` of the FIPS-202 model's lane, checking the
representation itself rather than the masked output alone.

**Tradeoff.** None found in gas or size: the helper is **21,622 bytes** (2,954
under EIP-170) and the shipped via-IR verifier runtime **24,032** bytes (544
under). What the change does cost is a load-bearing invariant that is invisible
in the bytecode, which is why the builder proves it on every run and refuses to
write on any failure.

### 2.4 Code-size engineering: a deployable 19.6KB permutation contract

**What.** The fully-unrolled permutation is 25,357 bytes of runtime code as
generated, over the EIP-170 deployment limit of 24,576 (a fact that forge tests
silently mask). Fixed to **19,617 bytes** with *zero* gas cost (actually −10
gas). That 19,617-byte permutation core is committed as `helpers/f1600_core.hex`;
the runtime that ships as `helpers/f1600_170.hex` (21,622 bytes) wraps it with
the batched SHAKE256 entry point of §2.5 and the Q-form patches of §2.3.

**How.** The 64-bit lane mask `0xffff…ffff` appears as a 9-byte PUSH8 at ~700
sites (6.3KB of code). Holding it in a top-level Yul variable turns every use
into a 1-byte DUPn at the same 3 gas. Scoping the theta temporaries so the mask
stays within DUP16 reach is the only subtlety. The obvious alternative, a
12-round body looped twice, would cost +400-500 gas per permutation; this costs
nothing.

**Security.** Deployability asserted in-test via a real CREATE (size,
extcodesize, codehash), then the same bit-exactness checks as §2.2. Because the
helper is deployed byte-for-byte as raw runtime code, its `EXTCODEHASH` is a
toolchain-independent constant (currently `0x4afb4435…9a817b`, quoted in full in
`SAFETY.md` §2.3). That is what lets the verifier bind the helper by content
rather than by address.

**Tradeoff.** None found. This item exists because an *audit* pass checked
deployability; benchmark configurations that only ever run under `vm.etch` hide
it.

### 2.5 Batching the sponge into the helper: 9 staticcalls → 3, −6.7k gas

**What.** Measurement (not intuition) splits the plain-lane permutation's 44,750
gas into 44,543 of callee execution and ~200 of call marshaling, and puts the
caller-side sponge glue (word-level XOR-absorb, byte reversal, squeeze, Solidity
loop framing) at ~42k per verify. The permutation core is at its structural
floor: its per-round opcode census matches the dataflow's minimum (77 XOR, 29
rotations, 25 stores, DUP count = fan-out). The remaining win is the
*protocol*: under a state-in/state-out protocol the final-hash SHAKE absorbs 7
rate blocks = 7 staticcalls.

**How.** `tools/build_f1600_batch.py` rebuilds `helpers/f1600_170.hex` from the
pristine core with three mechanical patches (round-1 state reads relocated from
calldata to memory 0x320, making the permutation in-place and therefore
loopable; five iota constants solc had left as 15-gas `SHL/SUB` reconstructions
patched to 3-gas PUSH8s; the trailing RETURN removed) and wraps it in a
calldatasize dispatcher.

800 bytes of calldata is the raw permutation protocol, byte-for-byte. Anything
else is a raw SHAKE256 message: the helper pads (FIPS 202 `1111`+`pad10*1`),
absorbs and permutes per 136-byte block in a loop around the unchanged core, and
returns the first 136-byte squeeze block. μ and the final hash each become ONE
staticcall (`shake256Batch170`); SampleInBall keeps the raw protocol for its
incremental squeeze. The one preimage length the batched path cannot express is
exactly 800 bytes (|M| = 734 for μ); the verifier falls back to the lane-level
sponge for that length alone.

**Why it preserves security.** Same check as §2.2: bit-exactness, not review.
The raw path is differentially tested against the FIPS-202 model AND the
original core binary inside the builder, then continuously against two
independent implementations and the SHAKE256 KATs in the suite. The batched path
is checked against `hashlib.shake_256` at build time (block-boundary lengths
0/135/136/137/271/272, both ML-DSA shapes) and against the lane-level sponge +
KATs in `test/ZZZ_fastkeccak170.t.sol`. Fail-closed marshaling checks
(`returndatasize()` == 800 / == 136) cover absent or hostile helpers, and the
code-hash binding of §2.4 is unchanged in mechanism; the pin simply moves with
every helper rebuild.

**Tradeoff.** The raw permutation entry pays the dispatcher: +127 gas (44,670 vs
44,543 callee), i.e. ~+130 per verify on SampleInBall's single permutation,
against the measured savings on the batched shapes: the 832-byte final hash
325,892 → 319,415 (−6,477: 7 staticcalls → 1, glue moved into the helper where
state addresses are compile-time constants, the 50-word callee memory expansion
paid once instead of 7 times) and the 98-byte μ 48,130 → 46,972 (−1,158). End to
end the batched entry is worth **−6,713** on the reference vector; the per-shape
brackets and the whole-call figure are different measurements, so they do not
net exactly (792 apart here). Every figure in this paragraph is taken at the
plain-lane representation. §2.3's Q-form lowers all of them, the 832-byte hash
to 291,214.

**Measured and rejected here.** Switching `_squeezeBlockFast170`'s byte reversal
to the one-mask form used by the absorb (three `PUSH32`s per stage instead of
six, inlined at five call sites) measures **+395 bytes and +270 gas**, the
opposite of the prediction, and of what the same rewrite does in
`_xorBlockFast170`.

### 2.6 SampleInBall's draw loop, in one assembly block: −1,475 gas

**What.** The τ = 39 draws of Algorithm 29 are a natural fit for a Solidity `for`
around a `while(true)` around *two* assembly blocks, and in that shape the
framing plus the spills at each assembly boundary cost more than the draws
(61,258 on the staged bracket). The whole loop is one Yul block that LEAVES only
to refill the squeeze buffer (which needs a helper `STATICCALL`): it breaks with
`i` **not** advanced, the caller permutes, squeezes, resets `pos` and re-enters,
and the re-entered scan restarts the same draw at the new block's first byte,
byte-for-byte the semantics of `j := 256; continue`. Measured **59,783**, i.e.
−1,475.

This is the largest *over*-estimate in the program: predicted ~10k, measured
1,475. The per-draw cost was never the Solidity framing; it is the ~130 gas of
real lane-shuffling work times the ~1.7× stack-traffic factor that shows up
everywhere in this codebase.

### 2.7 What is actually left in the permutation

With Q-form in (§2.3), the per-round census is 556 opcodes / 1,673 gas and its
*entire* discretionary content is 19 stack ops: 609 gas of rotations (29 × 7
ops, and 7 is minimal: two shifts of one value plus the copy and the reorder to
feed them), 450 of memory traffic (50 loads + 25 stores + 75 address pushes;
each lane is genuinely read twice, once for its column parity and once for
`A ^ D`, and 25 live lanes will not fit a 16-deep stack), 231 of XOR, 98 of χ,
228 of fan-out DUPs, **and the DUP count equals the value fan-out exactly,
2,517 = 2,517.** A value-identity CSE audit over the whole body finds *no*
redundant load, *no* dead store and *no* recomputation of a live value, and
seven local peephole patterns (SWAP-before-commutative-op, SWAP/SWAP,
DUP1/SWAP1, zero shifts, NOT/NOT, store-to-load forwarding, adjacent duplicate
loads) return **zero** hits.

The residue is 449 stack ops across 24 rounds = **1,347 gas per permutation
(3.35%)**. A *perfect* scheduler, one emitting no SWAPs at all, which is not
achievable for 25 values with fan-out 3 on a 16-deep stack, is worth at most
~12k end to end. That is the honest ceiling for rewriting the lost generator,
and it is why it was not rewritten.

---

## 3. The public key, pre-expanded and streamed into the matvec

**What.** The baseline expands its cached public-key matrix Â from packed storage
into one-coefficient-per-word arrays (128KB of memory, 835k gas), abi-decodes
nested arrays, and then runs a matvec (605k) plus a separate c·t1
multiply-subtract pass (247k). The shipped verifier's `matvecRow`
(`src/Decode.sol`) reads the pk data contract's packed words *directly* inside
the matvec loop and folds the c·t1 subtraction into the same lazy accumulator
(add `Q·2^28 − c·t̂1` per lane): no expansion pass, no abi.decode, no separate
subtract pass. The matvec measures ~221k across the four rows (including the
lazy per-row EXTCODECOPY of the pk operands into a reused 5KB scratch, which
keeps the 20.5KB blob out of resident memory), and pk expansion 1.03M → ~5k.

Moving key expansion off-chain is ZKNoxHQ's idea, not ours. What is different
here is the delivery: the expanded key is a data contract that `EXTCODECOPY`
streams row by row, already in the packed lane layout the multiply consumes, so
nothing is reformatted on-chain. `prepare/prepare.py` runs ExpandA and the NTT
of t1 offline, once.

**Why.** Two of the profile's biggest buckets (expansions 12.7%, matvec+pointwise 10.5%)
plus a large slice of the memory-expansion term were pure representation overhead.

**Security.** Arithmetic equality is gated by the end-to-end tests (the verifier accepts
NIST KAT vectors and rejects bit-flips); the accumulator's no-overflow bound follows the
same discipline as §4. Rather than extracting each z lane down to bit 0 before
multiplying, the z word is masked IN PLACE, so `mul(a_k, and(wz, M64L{k}))` is already
the product in lane position; each accumulator lane then receives four products
`a_k·z_k < (q−1)(17q−1) = 1,193,933,463,748,608 < 2^51` plus one `KQ28 − c·t̂1` term
`< KQ28 = q·2^28`, for a lane total `< 2^53` and no carry into the neighbour. Lane
disjointness of the pre-shifted products is Z3 obligation **O7**; the accumulator bound
is **O8**, whose `ACC_ENTRY = 4(q−1)(17q−1) + q·2^28 = 7,025,334,913,859,584` is exactly
the entry contract of the inverse NTT (§5). `KQ28` is a multiple of q, so the added
offset vanishes under that entry reduction (S14).

**Tradeoff.** The fused loop is harder to read than compose-from-kernels; provenance
comments map each fragment back to its individually-tested kernel. This fusion is the main
reason the verifier comes in *below* its component-sum budget.

---

## 4. Packed-SWAR arithmetic and lazy reduction

**What.** Every polynomial in the pipeline is held four coefficients to a 256-bit word, in
64-bit lanes, and the arithmetic is SIMD-within-a-register. One 5-gas `MUL` of a packed
word by a shared scalar computes four products; one `ADD` adds four coefficients. Nothing
is reduced unless a proof says it must be.

**How.** Two ideas, and they are the ones the NTT of §5 is built on:

1. *Shared-scalar SWAR multiply.* A butterfly multiplies many coefficients by the same
   twiddle factor S < 2^23. One 5-gas MUL of a packed word by S computes 4 products at
   once. Lanes stay independent as long as each product < 2^64.
2. *Lazy reduction with proven growth bounds.* Additions never get reduced: lane values
   grow by ≤ 2q per layer (forward: bound (2L+1)q ≤ 17q < 2^28 after all 8 layers;
   inverse: sum-lanes double per layer, ≤ 256q < 2^31). Only the twiddle products are
   reduced, and the reduction itself is the subject of the rest of this section.

**Tradeoffs.** Packed layout is only a win *inside* long arithmetic chains. Packing
*loses* 8-21% when used for isolated compute (unpacking costs more than the mload it
saves). So the pipeline packs once, stays packed through NTT→matvec→invNTT, and
unpacks once. Pack/unpack boundaries cost ~10k/13.5k per polynomial.

### 4.1 The reduction: two lane-local Barrett steps

**What.** Every modular reduction inside both NTTs (192 sites per forward
transform, 160 per inverse, 1,600 executions per `verify()`) is **two lane-local
Barrett steps** with no spreading at all. Measured against the *spread* Barrett it
replaces, one change at a time on the same fixture:

| kernel | spread Barrett | two lane-local steps | delta |
|---|---:|---:|---:|
| `nttFwV3` (per transform, ×5) | 56,862 | 48,462 | **−8,400** |
| `nttInvV3` (per transform, ×4) | 61,373 | 54,285 | **−7,088** |

i.e. **−70,352 gas end to end (−5.14%)**, and the runtime *shrinks* by **644 bytes**.
The per-transform rows scale onto the end-to-end figure exactly
(5 × 8,400 + 4 × 7,088 = 70,352), because the change is local to the two
transforms: it moves no memory and shifts no allocation.

**Why a spread form has to pay for spreading.** A packed word holds four coefficients
in 64-bit lanes, and a Barrett reduction needs `⌊x·μ/2^k⌋` with `μ ≈ 2^k/q`. The
verified domain reaches `x ≤ 128q(q−1) < 2^53`, and `MU52 = ⌊2^52/q⌋` is
2^29, so `x·MU52` is an **83-bit** number: it does not fit a 64-bit lane. The
lanes therefore have to be spread to 128-bit spacing first (mask the even lanes,
shift-and-mask the odd ones, reduce twice, shift and OR the halves back): 98 gas
per site, of which 30 is pure representation.

**How.** Pick the multiplier so the product *does* fit the lane, and pay for the
lost precision with a second step:

```
x := sub(x, mul(and(shr(33, mul(x, MU33)), QHATM31), Q))   // MU33 = ⌊2^33/q⌋ = 1025
x := sub(x, mul(and(shr(23, x),            QHATM31), Q))   // ⌊2^23/q⌋ == 1, elided
```

* **Step 1** is a Barrett step with a deliberately coarse constant.
  `x·MU33 ≤ 128q(q−1)·1025 < 2^63`, so every lane's product stays inside its own
  lane and the four lanes reduce *simultaneously*, in place, with no spreading
  and no repack. Its quotient is only accurate to about one part in 2^33, so it
  leaves `x1 < 2^33` rather than `< 2q`.
* **Step 2** closes the remaining ten bits. It is the same Barrett step with
  `μ = ⌊2^23/q⌋`, which for this modulus is **1** because
  `q = 2^23 − 2^13 + 1`, so its multiply disappears and what is left is
  `x1 − q·⌊x1/2^23⌋`. Writing `x1 = a + 2^23·b` that is
  `a + b·(2^23 − q) = a + 8191·b`: each such step shrinks the high part by a
  factor 2^10, and one step from `2^33` lands under `2q`.
* **One mask does two jobs.** After `shr(33, ·)` the *next* lane's bits begin at
  bit `64 − 33 = 31` of this lane, and a lane's quotient is below `2^31` exactly
  when its product is below `2^64`. So a single 31-bit-per-lane mask both
  extracts the quotient and blocks the neighbour: the two conditions are the
  same condition. A 32-bit mask would admit one neighbour bit (mutant M59), and
  step 2 reuses the same constant (its own quotient is below `2^10`, its
  neighbour's bits begin at bit 41).

Net: 60 gas per executed site instead of 98, and the measured saving is 43.75
gas per site, *above* the 38 the opcode census predicts, which is the via-IR
stack scheduler paying back the two temporaries (`e`, `o`) the spread form kept
alive. On code size the two shipped files hold 22 reduction sites between them
(12 forward, 10 inverse) and the runtime shrinks by 644 bytes, i.e. ~29 bytes
per site: less than the ~86 an opcode-for-opcode count predicts, because the IR
pipeline was already sharing part of the spread form's constant material.

**What it costs, honestly: the margin is thinner.** The reduction is exact for
every input below **10,285,325,456,994,078**, where it returns exactly `2q`;
`128q(q−1)` sits **1.144×** below that, where the spread Barrett had 1.335×. The
guard is unchanged in kind and still bites: one more unreduced layer doubles lane
growth and `2·128q(q−1)` is past the cliff (C11c). A *second* cliff, the first
input whose step-1 product leaves its 64-bit lane, 17,996,823,486,545,905, is
higher, so `r < 2q` is the binding constraint, and that ordering is itself an
obligation (C11d) rather than a remark.

**Why it preserves correctness.** The reduction is the single most
proof-carrying line in the tree, so the whole apparatus is stated about this
form:

* **Z3.** The Barrett constant and its entire input domain (up to 15q(q−1)
  forward, 128q(q−1) inverse) are proven correct with Z3 (SMT, `unsat` on the
  negation, not fuzzing): C1 (`MU33 == ⌊2^33/q⌋`), C1b (`⌊2^23/q⌋ == 1`, with
  `q = 2^23 − 2^13 + 1` and `2^23 − q = 8191` as its own conjuncts), C9e
  (lane-locality: `max·MU33 < 2^64`, where a spread form only needs `< 2^128`),
  C9h (the mask is exactly `64 − 33` bits wide, and `qhat < 2^31` iff the
  product is lane-local), C11a-d, S1-S4 (with `lane_product_lt_2p64`,
  `qhat_lt_2p31`, `step1_lt_2p33` beside `0 ≤ r < 2q`), S5/S6 (the butterfly
  steps, each carrying `product_is_lane_local`), S13 and the E9a/E9b sweeps.
  **S7 is the strongest of them.** It is stated for the word the transform
  actually holds: **four** 64-bit lanes, reduced all four in place, with each
  lane's quotient field, each no-borrow and each recovered lane its own
  conjunct (stronger than a two-lane spread lemma). The lane-growth inductions
  are Z3 obligations too (S5/S6/C9f/C9g).
* **Lean.** `Mldsa/Barrett.lean` models the opcode chain exactly at EVM 256-bit
  semantics (`step1EVM`, `step2EVM`, wrap-around included) and proves
  `swar_lane_independent` for the real four-lane word rather than via a two-lane
  spread lemma, with zero `sorry` and no axioms beyond Lean's own.
  `step1_alone_is_not_enough` is a theorem, not a comment.
* **C16** extracts BOTH steps from the shipped Yul and requires their
  occurrence counts to agree region by region
  (`*_every_reduction_has_both_steps`), because a single-regex census would count
  a reduction that had lost its second line, and such a lane exits at `< 2^33`,
  three orders of magnitude above every lane bound the induction states. Mutants
  **M57/M58** delete exactly that line and are killed; **M59** widens the mask to
  32 bits and is killed; M29/M30/M49/M50 key on `MU33`.
* **EVM-side.** `test/FV3_NttLaneBounds.t.sol` carries
  `testFuzzPackedReductionIsFourScalarReductions` (the shipped four opcodes,
  twice, on a fuzzed packed word, against four scalar reductions),
  `testReductionIsLaneLocal` and `testStepOneAloneIsNotEnough`.

**Tradeoff.** The thinner margin, stated above and guarded; and one more line of
Yul per reduction site to read, in exchange for having no spread/repack
representation at all.

---

## 5. The NTT: fused radix-8 / radix-4 passes

**What.** The number-theoretic transform (the FFT-like core of Dilithium
arithmetic) at one coefficient per 32-byte word costs **182,470** gas per
256-point forward transform and **215,899** per inverse, measured on the
vendored baseline kernels in this tree: one transform at fresh memory, table
build inside the bracket, via-IR (§9.1), printed by `testGasV1Baseline`
(`test/ZZZ_nttvariants.t.sol`) and `testGasInvV1Baseline`
(`test/ZZZ_invntt.t.sol`).

Packed-SWAR arithmetic (§4) plus the pass fusion below cuts those to
**45,701 / 54,419** under the identical condition (`testGasV3`, `testGasInvV3`),
i.e. **4.0×** on each side.

On real signature data with the twiddle tables hoisted the way `_wPrimeRows`
hoists them across all nine transforms (§5.4), the shipped transforms measure
**44,931 (forward, `src/Ntt.sol`) / 53,591 (inverse, `src/InvNtt.sol`)** in
`test_profile_20_ntt_layers`. The corresponding brackets inside `verify()`
itself are `nttFw(c)` 44,924 and `nttFw(z)`×4 180,745
(`test_profile_10_stages`). The inverse figure *includes* the accumulator
reduction that would otherwise be a separate ~11k `reducePacked` pass per row.
Nine transforms run per verification: five forward (four z rows and c) and four
inverse.

(The same source measures 45,633 / 54,283 if each transform builds its own
twiddle table instead of taking a hoisted one (§5.4), 56,862 / 61,373 with the
spread Barrett in place of §4.1's two-step reduction, and 66,981 / 69,271 with
the spread Barrett under legacy codegen (§9.1).)

### 5.1 Radix pass fusion — the whole transform in three or four passes, not eight

A textbook NTT is one pass per layer, so a 64-word polynomial is loaded and
stored eight times. Loads and stores are only 3 gas each, but the *pointer
arithmetic and loop framing around them* are not: the calibration suite
measures ~50 gas of framing per iteration and ~15 gas per pointer bump, and a
per-layer pass pays both for every butterfly. Fusing layer pairs into a
**radix-4 butterfly** (load the quad (i, i+s, i+2s, i+3s) once, run BOTH
layers on the stack, store once) halves the memory traffic, the pointer
arithmetic and the loop count of the word-aligned layers at identical
arithmetic.

The **inverse** transform runs four passes: the entry fold + L1+L2, then
L3+L4, L5+L6 and L7+L8+scale. The **forward** transform runs THREE, because both
of its word-aligned passes are **radix-8**: one octet of eight words loaded once,
THREE layers on the stack, one store:

* pass A: L1+L2+L3 over the octet `(i, i+8, ..., i+56)`, word strides 32/16/8;
* pass B: L4+L5+L6 over eight CONSECUTIVE words, strides 4/2/1;
* pass C: the in-word L7+L8 (§5.3),

three passes where radix-4 needs four. What that removes is one entire traversal
of the polynomial: 64 loads, 64 stores, their address arithmetic, and 36 of
the transform's 82 loop iterations at the ~47 gas of framing the calibration
suite measures. Pass A's seven twiddles are the same for every octet, so they
are compile-time literals and the pass reads no table at all. The two in-word
passes additionally step **four** data words per iteration instead of two.

Measured per forward transform, radix-4 against radix-8: 48,462 → **45,633**,
i.e. its three passes cost 11,301 + 12,956 + 20,528 against radix-4's
8,277 + 8,939 + 9,873 + 20,528. Times the five forward transforms, −14,145 end
to end, for +1,755 bytes of runtime code. Radix-4 fusion itself, measured
against one pass per layer under legacy codegen: forward 77,337 → 66,981,
inverse 76,111 → 69,271, i.e. **−79,140 gas end to end** (−5.0%) for +2,174
bytes.

### 5.2 Fused boundary layers and lazy hand-offs

The forward transform's last in-word layers are merged into one pass whose output is
deliberately **not** canonicalised: every lane exits < 17q, exactly the domain the lazy
matvec accumulator admits (O7/O8). The inverse transform's first in-word layers fold
the matvec accumulator's reduction in: raw lanes ≤ 4(q−1)(17q−1) + q·2^28
enter directly and are reduced with the EVM's native mulmod/addmod against
multiple-of-q offsets (q·2^30 / q·2^31), which on already-extracted scalars
is cheaper than any Barrett plumbing (S14). Its last layers fold in the n⁻¹
scaling and the only canonicalisation of the pipeline.

One operational requirement falls out of the proofs: **forward-NTT inputs must be
canonical (< q)**, which is why the z=0-encoded-as-q quirk (§10) must be canonicalized
before the NTT, while the inverse NTT's entry contract is "lanes ≤ ACC_ENTRY", the exact
ceiling O8 proves for the matvec accumulator (the producer/consumer linkage is C9g/S14,
re-derived at EVM semantics in FV3/FV6).

### 5.3 The forward tail: mulmod, not Barrett

Layers 7 and 8 are the *in-word* ones: their butterflies pair lanes of a single word, so
the lanes are extracted to scalars anyway. All four of their twiddle products go through
the EVM's native `mulmod` for exactly that reason. The alternative for L7's pair (they
share one scalar, so they can be done as one `MUL` of the lane-2/3 pair, spread to
128-bit spacing, and reduced by one shared Barrett) costs 15 gas for the spread and 31
for the Barrett, i.e. ~25 gas per modular multiply, while `MULMOD` is 8 gas flat with
**no domain restriction at all**. Two `mulmod`s remove 32 gas of opcodes per data word,
~1,952 per transform, ×5 forward transforms. Measured: the L7+L8 pass 22,480 → **20,528**
per transform, **−9,760** end to end.

The packed passes keep their Barretts and should: there one `MUL` multiplies
FOUR lanes by a shared scalar and two lane-local Barrett steps reduce all four at
~15 gas per modular multiply, cheaper than `mulmod` once the extraction and
repacking are counted. The break-even is the lane count, not the opcode.

*Why it preserves the proofs.* `mulmod` output is **canonical (< q)** where a
Barrett's is `< 2q`, so every lane bound in the block is tighter: L7's outputs
are `< 14q` and `< 15q` rather than `< 15q`, L8's exit stays `< 17q`, the same
lazy domain O7/O8 admit and C9a/C9f prove. The final forward block therefore has
`barrett_per_block[3] == 0`, `mulmod == 16` (four per data word × four words
unrolled) and no `mul` outside a `mulmod`, in both shipped copies (`src/Ntt.sol`
and its `test/ZZZ_NttVariants.sol` mirror, which C16 requires to agree). The
negative control `ctl_fwd_barrett_back_in_the_tail` rejects a shape with a
Barrett smuggled back into that block, the forward mirror of
`ctl_inv_barrett_at_layer8`.

### 5.4 The twiddle tables, built once: −10,321 gas and −201 bytes

**What.** The natural place for each NTT's 1,024-byte twiddle table is a
`uint256[32] memory` array literal built on entry. `verify()` runs **nine**
transforms, so that shape builds the constant nine times and leaves nine
kilobytes of never-read memory below every later allocation. The tables are
instead `nttFwTable()` / `nttInvTable()`, called **once** each in `_wPrimeRows`
and passed in:

| | table per transform | table hoisted |
|---|---:|---:|
| `nttFwV3`, per transform (×5) | 45,633 | **44,931** |
| `nttInvV3`, per transform (×4) | 54,283 | **53,591** |

**−10,321 gas (−0.83%) and −201 bytes** end to end. The two transforms' PASS
profiles do not move at all: forward 11,301 / 12,977 / 20,543 and inverse
20,860 / 9,948 / 8,894 / 13,832, each within measurement noise of the per-pass
figures above. That is the numerical form of "the transform's Yul is
untouched": every gas this saves is outside the marker-delimited blocks.

**Where the 10,321 comes from.** Two independently measured parts:

* *The stores.* The whole-call bracket of `nttFwV3` minus the sum of its three
  pass brackets is **848 gas**, and the inverse's is **797**. That residue is
  the table build plus the internal call framing. Eight of the nine builds are
  gone.
* *The memory.* Probing it on its own (keep all nine builds, but hand the
  1,024 bytes back to the allocator instead of leaking them) measures
  **−1,977**. Nine kilobytes at a ~41 KB peak is worth about that, and the
  arithmetic checks out against the other direction (§8).

**The hand-off is by pointer, and that is load-bearing.** Passing
`uint256[32] memory` does not work: Solidity copies a fixed-size memory array into a
fresh allocation at every internal call, so nine copies of 32 words cost
**+1,795 gas**, most of the memory win handed straight back. `nttFwTable()`
returns a raw `uint256` instead (`assembly ("memory-safe") { tbl := psirev }`,
four lines, outside the transform), and the transform's parameter is a plain
`uint256`. Inside the transform, `add(psirev, 0x20*k)` addresses exactly the
words it always did: **not one character of either transform's Yul moves.**

**How C16 sees it.** Obligation C16 extracts the schedule from the shipped Yul, and
it partitions each transform TOTALLY (head, marker-delimited layer blocks, tail)
with the head and the tail required to be **INERT** (no offset constant, no reduction,
no `mstore`/`mload`/`mul`). An array literal in the head is inert *as text*; hoisting it
out leaves the head emptier still, so the inertness conjunct is unaffected. Concretely,
when the checks ran for this change **every structural conjunct passed unchanged**
(both region summaries region by region, both head/tail inertness conjuncts, the
offset-per-butterfly counts, the paired-store census, the two-step-reduction census, and
`all_shipped_{fwd,inv}_copies_agree`) and exactly the **four residual digests**
failed. That is the contract those digests carry, and they were re-pinned from
the values C16 prints, never recomputed inside the check.

Two consequences:

* the twiddle literals are covered by the **FILE** digest only (they are not
  inside the function body), so `_C16_FILE_DIGEST` is load-bearing rather
  than belt-and-braces for them, which is what it was written for
  (`ipackCoeffs`, the constant block and the `psirev` table are named in its own
  comment);
* both C16 copies of each transform (`src/` and the `test/ZZZ_*` mirror) had to
  move together, because `*_shipped_sources_are_the_pinned_bytes` requires all
  copies to normalise to the SAME digest. They do.

Nothing else in the apparatus moves for this change: no bound, domain, predicate or
constant changes, so no Z3 obligation, no Lean theorem and no mutant needs retargeting
(M29/M30/M49/M50/M57/M58/M59 all key on text inside the transforms, which is
byte-identical).

### 5.5 Why fusion preserves the proofs

Radix fusion is a **scheduling change and nothing else**: each fused block's second and
third layers consume the previous layer's outputs, which satisfy that layer's entry bound
by construction, so every lane bound, offset constant and Barrett domain in the proofs is
untouched. The lane budget is still +2q per LAYER (C9f/S5), the worst forward product is
still 15q(q−1), the exit is still < 17q. What fusion *does* determine is the block
partition **C16** extracts from the shipped Yul, and C16 is pinned to the shipped shape
rather than relaxed to admit any shape:

* the forward transform's marker-delimited partition is `n_blocks == 3` over **5**
  regions, with `barrett_per_block == [12,12,0]`, `K_per_block == [[2]×3]` and a
  paired-store census of **24/24**; the inverse's is 4 blocks. Each fused block must
  name ALL of its layers' offset constants.
* `_SUM_RE`/`_DIFF_RE` are a CLOSED enumeration of the octet's twelve minuend names
  (`u0..u3`, `a0/a1`, `b0/b1`, `c0/c2/c4/c6`), so a butterfly whose minuend is named
  anything else cannot hide inside the total. The sum/difference store counter pins
  the FULL `sub(add(X, TWOQ4), t0)` expression, so the subtraction direction is
  pinned too, which a bare `add(u, TWOQ4)` substring is not.
* `_offsets_every_butterfly` is stated as `2 × offsets == layers × stores`, which is
  the same as "offset occurrences == stores" at L = 2 and the right statement at
  L = 3 (twelve offsets against eight stores). Vacuity mutation **V107g** relaxes that
  equality to `<=` and must break `ctl_fwd_one_offset_dropped_in_a_block`; **V107h**
  re-tunes the per-block reduction census.
* Two C16 controls reject shapes radix-8 makes possible:
  `ctl_fwd_one_octet_butterfly_dropped` (a radix-8 block that lost one whole
  butterfly, with its offset, its reduction and its paired stores) and
  `ctl_fwd_octet_block_is_only_radix4` (a block whose offset/store ratio says it
  is running two layers where the schedule states three).
* EVM-side, `test/FV4_...` executes the shipped transform and requires
  **four** markers delimiting **three** non-empty blocks (and `prof[4] == 0`),
  and `test/FV6_...` pins the forward and inverse region counts separately
  because they differ. Every discrimination control is derived against this shape.

### 5.6 Measured and rejected inside the NTT

* *Hoisting `QHATM31` into a Yul local*, to turn 48 `PUSH32`s into `DUP`s: **exactly
  zero** bytes. The IR pipeline rematerialises constants rather than holding them live,
  and it does so even under the register pressure of an eight-word octet (§9.4).
* *The inverse transform's final pass* was decomposed and left alone: its 4 × `mod`
  canonicalisation costs ~104 gas per word against ~83 for a two-step Barrett plus
  a conditional subtraction, but the L8 sum lanes reach 256q(q−1), which is
  **1.75× past the two-step Barrett's exactness cliff** (C11c), and every way of
  getting them into the domain costs more than the 21 gas it would save.

---

## 6. Decoding the signature: z, the norm check, and h

**What.** Signature decoding (18-bit bit-unpacking of z with norm check, and the hint
vector h) costs 1.30M in the baseline together with the UseHint output stage of §7. The
shipped kernels (`src/Decode.sol`): `unpackZPacked` (FIPS 204 `sigDecode` /
`BitUnpack(z, gamma1-1, gamma1)`, plus the strict norm check of §10) **77,369**, and
`unpackHFast` (`HintBitUnpack`, Alg. 21) **8,146**, staged brackets on the canonical
`test_e2e_10` fixture, which is where every measurement in this document that says
"measured one change at a time" is taken.

**Why it preserves security.** The unpackers are fuzz-verified bit-equal against the
reference decoder across FFI-signed vectors plus malformed-encoding rejection cases, and
every predicate below is additionally proved. The exhaustive-verification approach used
throughout this section only works because the domain is 2^18 or 2^23, a fact of
Dilithium's small q.

**Tradeoff.** Aggressive unrolling grows code size; the byte costs are stated per change
below.

### 6.1 Reading the 18-bit fields: one aligned load and one mask

The baseline extracts each 18-bit field with three separate memory loads
plus bounds checks (~675 gas/coefficient). 18-bit fields are byte-aligned every 4
coefficients (72 bits = 9 bytes), so one aligned load per 4-coefficient group plus
in-register little-endian assembly replaces all of it, and `unpackZPacked`
decodes straight into packed-SWAR lanes so no separate `packFromFlat` pass is needed.

**One mask instead of six.** The 18-bit fields of a 9-byte group straddle
bytes 2, 4 and 6, and the obvious form isolates each straddling byte with its own
`and(byte(k,w), 3|15|63)` and its own `shr`. Instead, all **twelve** byte
terms are placed with pure LEFT shifts (`byte(2,w)<<16` *and* `byte(2,w)<<62`, and so on)
and ONE `and(·, Z_M18)` discards everything that lands outside a lane's
18-bit field. The twelve terms occupy pairwise **disjoint** bit ranges (top bit
209), so the OR is a sum and each output lane is a function of its own three
bytes alone; obligation **O10** proves that, then settles equality with FIPS
BitUnpack by a complete coordinate sweep, which is a complete argument
*because* both maps are bytewise additive (also a conjunct).

**Three of the twelve terms are fused into multiplies.** Bytes 2, 4 and 6, the ones
that straddle a field boundary, appear TWICE, at shifts 46 apart. For `b < 2^8` the two
shifted copies occupy disjoint bit ranges, so

```
b * (2^s + 2^t)  ==  or(shl(s, b), shl(t, b))          exactly, for every b < 256
```

and one `MUL` replaces two `SHL`s, an `OR` and a stack copy: 8 gas where the
shift form costs 18, three times per quad. The term set O10 models is
**unchanged**; only the way the shipped Yul emits three of its terms differs.
Measured: **−11,520 gas for +100 bytes**.

O10 carries three conjuncts and nine controls for the fused form:
`fused_constants_are_the_two_powers` (each constant is exactly `2^s + 2^t`),
`fused_multiply_is_the_two_terms` (**exhaustive** over all 256 byte values, for
each of the three pairs), and `mul_pairs_are_the_doubled_terms`, which ties the
constants back to `Z_TERMS`, so a constant encoding some *other* pair of shifts
cannot pass by agreeing with itself. Lean carries `fused_split`,
`fused_disjoint` and the three `zp{2,4,6}_is_two_powers`, and mutant **M64**
deletes one of the two powers from `Z_P4`: a change that still type-checks, is
still a multiply, and silently drops bits from every field-1 coefficient.

The unrolled body runs **four** quads (16 iterations per polynomial), not eight.
Measured against the eight-quad body, that trade is **+1,888 gas for −1,289 bytes**, and
it is taken deliberately to fund the forward transform's radix-8 passes (§5.1).

### 6.2 The centered map, four lanes at a time

FIPS 204's `BitUnpack(z, γ₁−1, γ₁)` maps each field `v` to the centred coefficient. The
form to avoid is `zc = γ₁ + q·(v>>17) − v`: at `v = γ₁` it returns **q** rather than 0,
which is exactly the ZKNox defect §10 fixes.

The shipped kernel computes `u := sub(Z_UOFF, V)` on the packed word (`Z_UOFF` is
`q + γ₁ = 8,511,489`, replicated per lane) followed by ONE conditional subtraction of q,
selected by a carry bit (`src/Decode.sol:139-140`):

```
o := sub(u, mul(shr(32, and(add(u, Z_QB32), Z_BIT32)), q))
```

Every lane's `u = q + γ₁ − v` lies in [8249346, 8511489] ⊂ [0, 2q), so `u + (2³² − q)` is
below 2³³ and its **bit 32 is exactly `[u ≥ q]`**, the one comparison a
reduction from [0,2q) needs. The `≥` is load-bearing: `u = q` happens at
exactly one field, `v = γ₁`, which is the z = 0 encoding, and taking the
comparison strictly stores q instead of 0. Mutant **M62** is that defect and is killed.
The reference decoder computes the same value as `mod(8511489 − v, q)` per coefficient,
so the two agree at `v = γ₁` on 0.

### 6.3 The strict norm check, four lanes at a time

The predicate is FIPS 204's:
reject `‖z‖∞ ≥ γ₁ − β`, boundary **INCLUDED**. In closed form on the raw field that is

```
fail  ⟺  (v − β − 1) ≥ 2γ₁ − 2β − 1
```

which with β = 78 and γ₁ = 131,072 is `v ≥ 262,066`, and 262,066 is precisely the
far-tail encoding of `‖z‖∞ = γ₁ − β`, the value FIPS 204 rejects. (The off-by-one
`fail ⟺ (v − β) ≥ 2γ₁ − 2β + 1` gives `v ≥ 262,067` and *accepts* it; that is the
baseline bug of §10.) The reference decoder writes the correct predicate as the single
unsigned range test `iszero(lt(sub(v, 79), 261987))`, whose wrap covers both tails in one
comparison.

The shipped kernel evaluates the same predicate on the **stored** word rather than on the
raw field, four lanes at a time:

```
bad := and(add(o, Z_NLO), sub(Z_NHI, o))      // bit 32 of each lane = REJECT
```

`o` is the canonical coefficient, i.e. `z mod q`, so `|z| ≥ γ₁ − β` is
"`o` is at distance ≥ γ₁ − β from 0 modulo q", i.e. **130994 ≤ o ≤ 8249423**.
Two constants turn that into two carry bits at the same position: with
`Z_NLO = 2³² − 130994`, bit 32 of `o + Z_NLO` is `[o ≥ 130994]`; with
`Z_NHI = 2³² + 8249423`, bit 32 of `Z_NHI − o` is `[o ≤ 8249423]`; both lane
values stay in [0, 2³³) so bit 32 is the flag and nothing crosses a lane
boundary. Their AND is the verdict, and because AND distributes over the OR
that accumulates the 256 words, the `Z_BIT32` mask that isolates the four
verdict bits is applied **once per polynomial** instead of once per word.
Note the second flag is a `sub`, not `add`+`not`: testing the far edge as a
subtraction from a constant is one opcode cheaper than complementing an
`add`, and it is why the check is four opcodes and not five.

Measured against the per-coefficient form (a `mod` for the centred map and a
`sub`/`lt`/`iszero` range test, 32 of each per unrolled loop body):
`unpackZPacked` + norm **123,803 → 88,959** on its staged bracket, i.e. **−36,072 end to
end (−2.78%)** for **+961 bytes** of runtime. With the fused byte placement of §6.1 on
top, the bracket reaches **77,369**.

**What actually paid.** The op census predicted ~29k and the measured saving is
34.8k, and the reason is a via-IR effect: the
accumulator is OR-ed through the **0x00 scratch word**, not a Yul local. Keeping
it in a local costs one more value live across the eight-quad body, which is one
more than the stack scheduler can place without a `memoryguard`, and the spills
it then inserts in every quad measure **+1,745 bytes and +19,916 gas**. That is
a bigger effect than the entire arithmetic change, and it is invisible in any
opcode count. (Two other shapes were measured and rejected: a
linear `V := or(V, ...)` accumulation chain instead of the balanced tree, +40
bytes and +3,840 gas; and hoisting the six SWAR constants into Yul locals before
the loop, byte-for-byte identical output, see §9.4.)

**Why it preserves the bound.** The predicate is the same predicate. The packed
form is checked as follows:

* **Z3.** **S8b** states the whole packed block symbolically at EVM
  semantics for four arbitrary 18-bit fields: 96 conjuncts covering, per lane,
  no-borrow on `sub(Z_UOFF, V)`, no-carry on all three flag words, the flag being
  a bit, the mask exposing exactly that bit, `[u ≥ q]`, canonicality of the
  stored lane, the closed form of the centered map, the two edge comparisons, and
  finally `and`-of-the-two-bits ⟺ the FIPS rejection. **E3b** enumerates the
  canonicalisation over all 2¹⁸ fields, **E4b** the check over all 2¹⁸, and
  **E5b** pins the boundary at BOTH tails in BOTH directions. The far tail is a
  genuinely separate claim, because it is reached through a different
  constant and a different opcode. **O10** is the extraction. The scalar form of
  the same bound is S8/E4/E5.
* **Lean.** `Mldsa/Decode.lean`: `canon_zero_field` (the z = 0 field
  canonicalises to 0), `flag_iff_u_ge_q`, `canon_closed_form`, `lo_iff`/`hi_iff`,
  `reject_iff_fips`, the four `boundary_*` witnesses, and
  `swar_z_lane_independent` for the word the kernel actually forms. Zero `sorry`
  and no axioms beyond Lean's own.
* **Mutation.** Per-coefficient repetition is what makes "every
  coefficient is gated" true in the scalar form, and a site count is a reasonable
  proxy for it there. It is not one here: coverage lives in the **replication of
  the constants**, so the catalogue carries mutants that break ONE LANE of one
  constant: **M60** (lane 3 of `Z_NLO` blanked: 256 coefficients silently ungated),
  **M61** (lane 1 of `Z_NHI` relaxed by one), **M63** (lane 2 of `Z_M18`
  narrowed to 17 bits), beside the whole-word edge relaxations **M40**/**M40b**,
  the removal **M41**, the single-site false-accept **M42**, the
  canonicalisation defect **M62** and the fused-constant defect **M64**. All are killed.
* **EVM-side.** `test/MUT_Gaps.t.sol` carries the matching discrimination
  control: both boundaries, both directions, at every lane of the first and last
  quad of every one of the four polynomials (32 positions × 4 field values),
  plus a fuzzed quad and a word-for-word comparison against the reference
  decoder. The reference decoder in `test/ZZZ_E2ERef.sol` still
  carries the per-coefficient `mod` and `iszero(lt(sub(v, 79), 261987))`, so it
  is an independent differential oracle for this one, coefficient for
  coefficient.
* **`formal/hypotheses.py`.** Thirteen tripwire rows for the shipped decoder:
  the check expression with its site count, each window constant in full, the mask that
  reads the verdict bits, the canonicalisation line, each multiply site with its count,
  each fused constant in full, the loop trip count (16) and the per-polynomial driver.
  The product that has to come to 1,024 has three factors, and all three are pinned.

**Tradeoff.** The margin: the +961 bytes are two thirds the six 32-byte SWAR constants,
materialised in each unrolled quad body (§9.4). Halving the unroll returns ~1.1KB for
~1.5k gas, which is the trade §6.1 takes.

### 6.4 h as four bitmasks: `unpackHFast`, 8,146 gas

The baseline materializes h as 4×256 words (32KB!); the FIPS encoding
is 84 bytes describing ≤ 80 set positions. We parse it (with ALL of HintBitUnpack's
validity conditions: monotonicity, count bounds, zero padding) directly into four
256-bit words, one bit per coefficient. 135k → ~8k, and 32KB of memory never exists.

The kernel is one assembly block rather than a Solidity loop over `bytes memory`; the
Solidity form pays 84 bounds-checked `hBytes[j]` index expressions per call, which the
IR pipeline compiles *worse* than legacy does (§9.1): 21,001 on the staged bracket
against **8,146** for the assembly form, **−12,855**. Three things differ and none of
them is a check:

* **byte reads.** `idx := and(mload(add(dm31, j)), 0xff)` with `dm31 = hBytes+1`
  reads byte *j* as the LOW byte of the 32 bytes *ending* at it. That word
  always lies inside the object: for `j = 0` it starts inside the object's own
  length field, whereas the natural `mload(add(d, j))` would reach 31 bytes
  past the array at the tail. Same value, two opcodes, no bounds check.
* **the padding check is branchless.** FIPS 204 Alg. 21 lines 16-18 ("every
  unused index byte is zero") is naturally a second loop over the ~40 unused
  slots. Shifting the 80 index bytes LEFT by `8*y[83]` bits drops the used
  prefix and leaves exactly the padding, so the whole region is zero iff three
  shifted words are, and an EVM shift of ≥ 256 yields 0, which is precisely
  "this word holds no padding". Three shifts and an `iszero` replace ~40
  iterations.
* **one accumulator instead of early returns.** All four checks OR into a single
  `bad`; `ok := iszero(bad)` at the end. The strict-increase test is
  `bad |= idx < prevP` with `prevP` = previous index + 1, reset to 0 at each row
  start, which is exactly "unconstrained at `First <- Index`, strictly
  increasing after it", with no per-iteration branch.

All four of Algorithm 21's validity conditions survive, each as its own line
with its own mutant (M43-M46) and its own `formal/hypotheses.py` tripwire: five
tripwire rows where the Solidity form has one. The counter check bounds only
`y[83]`, and that is *equivalent* to bounding all four only because the
non-decreasing check is enforced beside it. Neither check is sufficient without
the other; that is why M44 and M45 are separate mutants and both are killed.
The index scan's loop bound carries a `min(cut, 80)` clamp that is the identity
on every accepted encoding; it exists so the scan provably cannot read outside
the 80 index bytes on a *rejected* one, even under a mutation that removes the
ω check. A short input is rejected up front (`ok` stays false, `weight` stays 0)
rather than reverting on a bounds check.

---

## 7. UseHint + w1Encode, fused into one packed kernel: 72,544 gas

**What.** The output stage (`UseHint` on `w′` followed by `w1Encode`'s 6-bits-per-
coefficient packing) costs 359k in the baseline, in part because it lives in a second
helper contract behind a 32,900-byte cross-contract call. `useHintSwar` (`src/Decode.sol`)
is one kernel, small enough to inline, measuring **72,544** on its staged bracket. It
consumes the inverse NTT's packed output directly: four coefficients per word; one MUL
replaces four DIVs; add/shift comparators replace per-coefficient GT/EQ; one MUL gathers
four 6-bit fields.

**Why it preserves security.** UseHint feeds the final hash. Its arithmetic is verified
**exhaustively**: all 8,380,417 field values × both hint bits, compared against the FIPS
reference implementation, zero mismatches (Z3 obligation E1). That is a complete
verification of the function's entire input domain.

### 7.1 One `mod 44`, not two

FIPS 204's Decompose has an `r1 == 44` special case (reachable only at `r = q−1`), and
the natural kernel reduces `S1 = Q0 + C` for it and then reduces `S1 + ADJ` again. But
reducing first cannot change the result:
`(S1 mod 44 + ADJ) mod 44 == (S1 + ADJ) mod 44`,
so the intermediate reduction is redundant *given* the final one. (Mutant M26 records
exactly this about the reference kernel, as an equivalent mutant; this is that
observation cashed in.) The single reduction is a
magic-number division, `OUT = T − 44*((T*94) >> 12)` with `T = S1 + ADJ ≤ 87`.
Obligation **C17** enumerates the whole thing: the first `T` at which
`(T*94)>>12 ≠ ⌊T/44⌋` is 131, strictly above the reachable maximum 87; 94 is
`⌈2^12/44⌉`; the lane product `87*94 = 8,178` stays inside a 64-bit SWAR lane;
the quotient fits the `REP1` mask; and the fold itself is complete-enumerated
over `S1 ≤ 44 × ADJ ∈ {0,1,43}`. **−8,070** measured.

### 7.2 The output stores: one `mstore` per eight packed words

w1Encode emits 6 bits per coefficient, i.e. **3 bytes per
packed word**, and the natural form writes them with three `mstore8`s plus their
shifts and address arithmetic: 96 byte-ops per 24 bytes of output. Eight
packed words are exactly 24 bytes, so the loop consumes eight words per
iteration, accumulates their eight 24-bit groups into one register in
little-endian order, byte-reverses it once and lands it with ONE `mstore`. The
8-byte tail of that 32-byte store falls on the next chunk (and, for the last
chunk, inside `w1`'s own 800-byte allocation, whose length word is then set
back to 768, the same discipline `shake256Fast170`'s whole-rate-block squeeze
buffer uses). The unroll also pays the ~47-gas loop tax a quarter as often.
**−11,733** measured.

Together with §7.1, `useHintSwar` + w1Encode measures **93,115 → 72,544**,
i.e. **−20,571**; the two are measured one at a time, which is why they sum to 768 short
of the combined bracket.

**Tradeoff.** Eight unrolled word bodies cost **+2,060 bytes** of runtime, because each
body re-materialises its six 32-byte SWAR constants as `PUSH32`s (§9.4). It is spent
knowingly: 11,733 gas for 2,060 bytes is the best gas-per-byte trade on the table, and
one equal-gas rewrite (`and(not(x), REP1)` for `xor(and(x, REP1), REP1)`, one `PUSH32`
instead of two) buys 208 of those bytes back.

**Security.** No bound, domain or predicate is weakened by either change: the UseHint
domain is unchanged in meaning, E1's exhaustive sweep is over the same function, and
C17 is an obligation the fold *adds*.

---

## 8. Memory: staying out of the quadratic term

**What.** EVM memory costs 3 gas/word plus a quadratic term m²/512. At the baseline's
953KB peak, the quadratic term alone is ~1.8M gas, the single largest hidden cost in
the SOTA verifier, attributable to no individual operation. The shipped verifier's whole
memory-expansion bill is **~7.1k gas**, 0.6% of the call.

**How.** Every representation choice in this document (packed coefficients, bitmask h,
streamed pk, no abi.decode, no intermediate expansions, fused passes that skip
intermediate arrays, twiddle tables built once rather than nine times) doubles as a
memory-footprint fix.

**Raw allocation where zero-fill is dead work.** `new bytes(n)` and
`new uint256[](n)` zero-fill; a buffer every one of whose words is written
before any is read does not need it. `matvecRow` allocates its accumulator
raw, and five more allocations are in the same position:
`unpackZPacked`'s four 64-word polynomials and their outer array
(measured 550 gas each, 427 for the outer: 2,630 replaced by ~60),
`useHintSwar`'s 800-byte output, `_finalHash`'s 832-byte preimage,
`shake256Batch170`'s return buffer and `sampleInBallPacked`'s squeeze block.
Together **−3,041 gas and −317 bytes**. Each keeps the same object layout and the same
32-byte-aligned free-pointer bump, which is what `test/SEC_memsafety.t.sol`'s
write-footprint probe checks (it caught a 200-byte reservation that was not
word-aligned, on the first try). The one allocation deliberately left alone is
`_computeMu`'s: the two zero context bytes of `M' = 00 || 00 || M` come from that
zero-fill, and it is a pinned hypothesis row that they do.

**How big this row actually is, measured.** A footprint estimate puts it at "~40k";
a measurement does not. The measurement is taken twice and in
opposite directions: burning an extra 9,216 bytes at the bottom of `verify()`
costs **+2,483 gas** and 18,432 bytes costs **+5,270**, and the two fit
`3m + m²/512` at a peak of 1,295 and 1,286 words respectively. So the shipped
verifier peaks at **~41 KB** and its whole memory-expansion bill is **~7.1k gas**.
That also bounds what any further footprint work can be worth, which is why the
9 KB of leaked twiddle tables (−1,977, §5.4) was the last footprint item taken and
no more were hunted for.

**Security.** None affected. Same values, smaller footprint.

**Tradeoff.** None, but note the accounting subtlety: because expansion is quadratic and
global, component-level measurements can't see it. It only shows up when you measure the
whole call, one reason "component sums" and "end-to-end measured" are kept as separate,
honestly-labeled numbers.

---

## 9. Codegen and opcode-level technique

### 9.1 via-IR: −62,733 gas for one line of `foundry.toml`

**What.** The whole tree is compiled with `via_ir = true` (the Yul/IR pipeline)
instead of solc's legacy code generator. No source semantics change; the shipped
kernels are the same Yul the Z3 obligations describe. Measured as the STAGED
brackets of `test/PROFILE_E2E.t.sol` on the shipped fixture: same pipeline,
same inputs, same solc and EVM versions, only the code generator differs:

| stage | legacy | via-IR | delta |
|---|---:|---:|---:|
| `nttFw(z)` ×4 | 268,471 | 236,607 | **−31,864** |
| `nttInv` ×4 | 277,477 | 246,119 | **−31,358** |
| `nttFw(c)` ×1 | 66,995 | 58,858 | **−8,137** |
| `useHintSwar` + w1Encode | 102,823 | 92,391 | **−10,432** |
| `unpackZPacked` + norm | 126,302 | 124,493 | **−1,809** |
| `matvecRow` ×4 (+ pk row copy) | 212,708 | 218,099 | +5,391 |
| SampleInBall | 63,059 | 65,638 | +2,579 |
| `unpackHFast` | 17,381 | 28,994 | **+11,613** |
| mu / final hash / pk check | 377,201 | 377,764 | +563 |

End to end that is **−62,733** on `verify()`, and the runtime shrinks
**23,119 → 20,818 bytes**, i.e. the EIP-170 margin goes from 1,457 to 3,758 bytes.
Only the end-to-end figure is authoritative; the stage rows are `gasleft()` brackets
and carry ~15 gas of measurement noise each. Both columns are measured with the
plain-lane helper protocol of §2.5 and without the memory-safe reshaping of §9.2, so
the table isolates the codegen change alone; the shipped tree carries all three.

**What this does to the baseline figures.** `via_ir = true` is set for the *whole
tree*, including tests. A test that instantiates the verifier compiles it in the
test's own compilation unit, so a src-only setting would measure an artifact this
repository does not ship. That means the vendored ZKNox kernels every comparison
here is against are compiled through the IR pipeline too, and the baseline numbers
this document quotes are what via-IR costs *them*: 153,267 per Keccak permutation
(§2.2) and 182,470 / 215,899 per forward / inverse NTT (§5). The same kernels
compiled with the legacy code generator run 7-9% higher, which is the entire
difference between 182,470 and the ~195.6K figure published for `nttFw`, and
between 153,267 and the 167,638 published for `f1600`. Every ratio in this document
is therefore like-for-like: both sides of it come out of one compiler invocation,
and every one of them is slightly *smaller* than the mixed-codegen comparison would
have been.

**Why it is this large.** The packed-SWAR butterfly is a long dependency chain
over many simultaneously live Yul locals: four data words, the twiddles, the
Barrett temporaries, three pointers. Legacy codegen materialises that chain on
the EVM stack with a naive layout and pays for it in DUP/SWAP: hand-counting the
opcodes of one spread-Barrett block predicts ~110 gas, while the measured
per-butterfly cost under legacy is closer to 2× that. The IR pipeline's stack
scheduler is what closes the gap, so the win concentrates exactly where the
register pressure is (both NTTs, UseHint) and inverts where the code is a
Solidity loop over `bytes memory` instead (`unpackHFast`: +11.6k; it indexes
`hBytes[j]` up to 164 times per call, which the IR pipeline compiles worse than
legacy does, and which is why that kernel is assembly today, §6.4) or where the
scheduler picks a worse order (`matvecRow`, SampleInBall). All three regressions
are counted in the net.

**The cost, honestly.** Without a `memoryguard` the IR pipeline cannot spill to
memory, and it refuses to compile a function whose live set does not fit the
stack. `src/FastKeccak170.sol` is honestly `memory-safe` today (§9.2) so the deployed
object does get a guard, but three routines are shaped to fit the scheduler
regardless, and only reshaped, never re-specified:

* `unpackZPacked` keeps all 32 of its per-coefficient check sites and
  every stored word bit-identical; the 4-polynomial loop lives in Solidity
  (`_unpackZPoly`), the four per-quad verdicts are OR-ed into a quad-local
  `bad`, and that flag is folded through the 0x00 scratch word inside a single
  assembly block. It is 2.7k gas *cheaper* than the shape it replaces.
* the reference decoders in `test/ZZZ_E2ERef.sol` and `test/ZZZ_decode2.t.sol`
  run 1 quad per iteration × 256 iterations rather than 8 × 32. Same predicate,
  same output.
* `test/PROFILE_E2E.t.sol`'s staged pipeline keeps its stage table in a
  helper.

Because a site count alone never proved "every coefficient is gated" (it says
nothing about how many times the body runs), the `formal/hypotheses.py`
tripwires for both decoders pin the loop trip count as well as the site
count, and `formal/mutation/mutants.py` targets M11/M12/M13 at the reference's 4
sites and M41/M42/E01 at the shipped `let bad := ...` seeding site.

### 9.2 Making the Keccak glue honestly `memory-safe`, +1,464 gas

**What.** The two byte-reversal blocks of `src/FastKeccak170.sol` touch
**exactly** the 136 bytes of their rate block (no 24-byte overhang, in
either direction) and are annotated `assembly ("memory-safe")`, as are the
remaining three blocks in that file. It was the only file in `src/` with
unannotated assembly, so with it annotated solc emits a `memoryguard` for the
verifier's *deployed* object and the IR pipeline can spill to memory again.

**How.** Neither block needs an enlarged buffer; both need a different offset.

* *Absorb.* Lane 16 is block bytes 128..135. Read as the word at
  `ptr+128`, its upper 24 bytes lie past the block. Reading the word at
  `ptr+104` instead, the **last** 32 bytes of the rate block, puts those same
  8 bytes in the word's final 8-byte group after the byte-group reversal, so the
  extract becomes `and(v, _M64_170)` instead of `shr(192, v)`. Two opcodes
  either way, identical gas, and the load no longer leaves the block.
* *Squeeze.* Symmetrically, the fifth store lands at `outPtr+104` carrying
  lanes 13..16 rather than at `outPtr+128` (lanes 16..19, of which three are
  garbage). It sits flush with the end of the rate block and merely rewrites lanes
  13..15 with the identical bytes the fourth store just wrote there. Same opcode count.
* *Output buffer.* The squeeze emits whole 136-byte rate blocks, so
  `shake256Fast170` allocates its output in whole rate blocks and then sets the
  length word to `outLen`; the slack stays inside the object's own allocation,
  below the free-memory pointer, so nothing else can be handed it.

**Security.** This is the one place in the tree where a comment could have been
turned into a lie the compiler acts on: `memory-safe` is an *assertion* to solc,
and a false one licenses it to place spill slots on top of live data. So the
blocks were made to satisfy the annotation rather than the annotation asserted of
the blocks. Bit-exactness is unchanged and re-checked the usual way: the ACVP
chain, the SHAKE256 KATs, the batched/lane-level equivalence sweep and the two
independent implementations, plus `test/SEC_memsafety.t.sol`, whose squeeze
write-footprint probe measures zero bytes past the allocation.

**Tradeoff.** +1,464 gas end to end (0.10%): with a memoryguard
available the IR pipeline chooses to spill in a few places where it otherwise
had to keep everything live. That is the whole cost, and it buys a build that is
no longer one added local away from failing to compile, and an `src/` tree with no
unannotated inline assembly left in it. Without it, the build sits one solc setting
away from not compiling at all, and that setting's failure mode is a stack-scheduler
error rather than a wrong answer, so it fails loudly rather than silently.

**Suppressing the guard is a measured option, and is not taken.** The IR pipeline
spills in 22 reserved slots with 182 constant-address loads and stores in the hot loops,
and suppressing the guard (one deliberately un-annotated no-op assembly block) measures
**−8,853 gas and −248 bytes** on its own, or **−3,985 gas for 8 bytes of margin** once
§5.4's table hoist has removed most of the pressure that produced the spills. It is not
a soundness trade: the guard only licenses an optimisation; without it a live set that
will not fit fails to COMPILE, loudly. But it reverses a deliberate hygiene decision,
re-introduces the "one added local from not building" fragility, and is worth 0.32%.

### 9.3 `optimizer_runs`

Sweeping it is a one-line change with §9.1-sized precedent, so it was swept:
5,000 → 1,356,357 gas / 22,468 bytes; 7,000 → 1,340,961 /
22,825; 10,000 (shipped) → 1,226,311 / 24,032; 20,000 → indistinguishable from
10,000; 100,000 → 1,225,993 / 24,362. Below 10,000 there is an inlining cliff
that costs 9-11% of the gas to buy 1.2-1.6 KB; above it, 330 bytes buys 318
gas. 10,000 stays.

### 9.4 The IR pipeline rematerialises constants; it does not hold them

Hoisting a `PUSH32` constant into a Yul local, so that its uses become `DUP`s, changes
the output by **exactly zero bytes** in every place it has been measured here:
`useHintSwar`'s six SWAR constants across eight unrolled bodies, `unpackZPacked`'s six
across its quads, and `QHATM31` across the forward transform's 48 reduction sites, the
last even under the register pressure of an eight-word octet. This is worth knowing
because it makes the unroll-vs-size arithmetic predictable: an unrolled body's constants
are a per-body cost that no source-level hoist will recover, so the byte budget for an
unroll is (bodies × constants × 33) and the only lever on it is the unroll factor
(§6.1, §7.2).

---

## 10. Correctness hardening: two latent bugs found in the SOTA, one quirk neutralized

**What.** The verification campaign (fuzzing + exhaustive checks) found real issues in
the baseline repo that this verifier fixes:
1. `useHintDilithium(rv = q)` returns 44, an *invalid* w1 value (FIPS says 0). Latent
   in ZKNox's pipeline (their UseHint only ever sees reduced values) but a live hazard
   for anyone reusing the function, especially since their own `unpackZ` *produces*
   the value q (it encodes z=0 as q, not 0). `useHintSwar` is FIPS-correct there, and the
   z=0-as-q field is canonicalized to 0 before the NTT (§6.2; required anyway by §5.2's
   proven input bounds).
2. The z-norm check accepts ‖z‖∞ = γ1−β where FIPS 204 requires strict rejection.
   Honest signers never emit the boundary, so KATs can't catch it; crafted vectors would.
   This verifier restores the strict check `‖z‖∞ < γ1 − β`, proved equivalent to FIPS over
   all 2^18 field values (Z3 S8/E4/E5, and S8b/E4b/E5b for the packed form of §6.3).

**Why this matters.** Both are compliance edges rather than exploitable breaks, but both
are exactly the kind of thing a NIST ACVP validation or a determined auditor would flag.
The fuzz harness caught #1 on its second vector.

**Tradeoff.** The strict boundary check costs a little gas.

---

## 11. What was deliberately NOT done

- **No hash substitution** (the 4.9M "ETHDilithium" route): breaks FIPS 204. Excluded.
- **No precompile assumption** (a proposed ML-DSA precompile would do this in ~4.5k gas;
  it is a Draft with no scheduled fork; this work is the bridge and the fallback).
- **No ZK wrapping** (~250-300k on-chain): changes the trust model to computational
  soundness under SNARK assumptions, adds proving latency and prover-liveness
  requirements. Complementary to a pure-EVM verifier (it suits batching), not competing
  on the same terms. Documented as a separate direction, not developed here.

### Measured and left on the table

* **Radix-8 in the inverse NTT.** The inverse transform is not converted, and the reason
  is the byte budget rather than the arithmetic. Its first pass is the in-word entry fold,
  so a three-pass inverse means taking BOTH remaining word-aligned passes to radix-8,
  including the L7+L8+scale block with its canonicalising stores: the three word-aligned
  passes (L3+L4, L5+L6, L7+L8+scale) go from 12 fused butterflies to 24 and from 4
  canonicalising stores to 8, which at the measured ~146 bytes per unrolled butterfly and
  ~90 per canonicalising store is **~2.1 KB**, against the **544** bytes of EIP-170 margin
  the shipped runtime leaves. Scaling the forward transform's measured −2,829 per
  transform over the four inverse transforms puts it at roughly **−11k gas**. It is the
  largest single item left, and it is written down here unmeasured and labelled as such.
  Funding it means finding ~1.5 KB more, and the only slack of that size in the tree is
  `_xorBlockFast170` (1,811 bytes of unrolled absorb that exists solely to serve the ONE
  preimage length the batched helper entry cannot express, |M| = 734). Rewriting that as
  a compact loop is plausible (it is off the hot path entirely), but it is a rewrite of
  the one file where a `memory-safe` annotation is load-bearing (§9.2), to fund a rewrite
  that re-pins the whole inverse block partition. The arithmetic is worth ~0.9%; the two
  rewrites together are not a trade this program should take.
* **A perfect Keccak scheduler.** Worth at most ~12k end to end, and it requires
  rewriting a generator that no longer exists. See §2.7 for the census that bounds it.
* **Suppressing solc's `memoryguard`.** −3,985 gas for 8 bytes of margin, and a
  deliberate hygiene regression. See §9.2.

---

## Where the 8.09M → 1.23M went (summary table)

The final column is the shipped `MLDSA44Verifier`. The authoritative number is the
**measured end-to-end 1,226,311 gas**; the per-stage figures are the measured *component
costs* and do not sum exactly to it. Memory expansion is a global quadratic term counted
both as its own line and inside the stages that allocate. There is no standalone
`reducePacked` pass: the forward NTT hands the matrix multiply LAZY
lanes (< 17q) and the inverse NTT folds the accumulator reduction into its first layer
(native mulmod/addmod against multiple-of-q offsets), with the lane bounds
machine-checked end to end (Z3 O7/O8 → S14/C9g, EVM-side FV3/FV4/FV6). The baseline
column is from the instrumented profile of the reproduced ZKNox verifier.

Every figure in the shipped column is a sum of `gasleft()` brackets printed by
`test_profile_10_stages` (`./tools/profile.sh`, artifacts in `profiles/`), so the
mapping is reproducible: SHAKE = `mu` + `sampleInBall` + `finalHash`, NTT =
`nttFw(c)` + `nttFw(z)` + `nttInv`, decode = `unpackZ+norm` + `unpackH`, glue =
the harness slice copies plus the staged-sum residual. SampleInBall is counted
whole in the SHAKE row: its rejection sampling is driven by the squeeze stream
and has no other home.

| Bucket | Baseline | Shipped verifier | Mechanism |
|---|---|---|---|
| SHAKE256 (9 × Keccak-f[1600], batched sponge, Q-form) | 3,001k | ~399k | §2 |
| NTT (9 transforms, reduce folded in, radix-8/radix-4 fused passes) | 1,850k | ~440k | §§4, 5 |
| Matvec + fused c·t1 (+ lazy pk row copy) | 852k | ~221k | §3 |
| pk expansion → direct streaming | 1,030k | ~5k | §3 |
| Signature decode (z + norm, h) | 941k | ~86k | §6 |
| UseHint + w1Encode | 359k | ~72k | §7 |
| Memory expansion (embedded, quadratic) | ~1,800k | ~7k | §8 |
| Glue / dispatch | — | ~2k | — |
| **Total (measured end-to-end)** | **8,094,831** | **1,226,311** | |

For reference, the in-tree **reference verifier** (`test/ZZZ_E2ERef.sol`, the
pre-extraction build used as a differential oracle) measures **1,744,358 gas**; it
shares the shipped forward NTT, so the radix-8 fusion of §5.1 moves it too. The
shipped verifier is the extracted, opcode-swept build.
