# Machine-checked proofs for the ML-DSA-44 (FIPS 204) EVM verifier

Lean 4 proofs of the arithmetic and encoding facts that the verifier's tests and
solver obligations rest on. The development uses **only Lean 4 core**: no
mathlib, no external dependencies.

The words below are used precisely.

* **Audited** means a theorem is pinned in `check_axioms.py` by its name, a
  digest of its statement, and the set of axioms it depends on. A theorem that
  is not audited is not covered by this page's counts.
* **SWAR** is short for "SIMD within a register": packing several coefficients
  into one 256-bit EVM word and operating on all of them with a single opcode.
  Sound only if no operation lets one coefficient's bits reach a neighbour.
  That is what the *lane independence* theorems establish.

## What is proved

### `Mldsa/Barrett.lean` — the lazy Barrett reduction under exact EVM 256-bit semantics

27 audited theorems.

*Lazy* reduction means leaving an intermediate value larger than `q` for a few
steps instead of reducing it fully every time, because the arithmetic still fits
the machine word. It is cheaper, and it is correct only inside a proved bound.

The NTT kernels reduce lanes with the two-step form
`sub(x, mul(shr(33, mul(x, MU33)), Q))` followed by `sub(r, mul(shr(23, r), Q))`.
The EVM opcodes `MUL`, `SHR` and `SUB` are modelled exactly, wrap-around
included, and the proofs establish:

* the lazy bound `barrettEVM x < 2q` on both deployed input domains
  (`x ≤ 15·q·(q−1)` forward, `x ≤ 128·q·(q−1)` inverse), and congruence
  `barrettEVM x ≡ x (mod q)`;
* that the domain restriction is necessary: the first violating input
  (`11 999 581 245 788 645`) breaks the bound, its predecessor does not, and one
  extra unreduced NTT layer would overshoot it;
* SWAR lane independence: the packed 2-lane and 4-lane reductions equal the
  scalar reduction applied to each lane, with no cross-lane leakage, and each
  output lane fits its 64-bit slot.

These are exactly the obligations that time out at the bytecode level under
halmos. See the header of `Mldsa/Barrett.lean`. `test/FV2_Barrett.sol` states
the matching bytecode-level obligations (**13/15 PASS**; `w3` and `w11b`
TIMEOUT). Composing those with the Lean theorems is one modus ponens, done by a
reader; it is not a mechanised link.

The halmos runs behind that split are a dated measurement, not a CI check, and
no claim in this repository rests on a halmos verdict. What carries
`FV2_Barrett.sol` is a fuzz test showing its kernel copies equal the shipped
reductions, plus C18's `fv2_*` digest conjuncts. Both are stated in
`docs/FORMAL_VERIFICATION.md` §5.7.

### `Mldsa/Encoding.lean` — FIPS 204 encoding-layer canonicality

11 audited theorems.

* FIPS 204 Algorithm 21 `HintBitUnpack` is a canonical, injective decoder. A
  hint set has at most one accepted 84-byte encoding, the `ω` weight budget is
  enforced, and the strict-increase and zero-padding checks are each proved
  load-bearing: dropping either one admits the published hint-malleability bugs.
* The §5.2 message representative `M' = 0x00 ‖ |ctx| ‖ ctx ‖ M` is injective in
  `(ctx, M)`, the `|ctx| ≤ 255` check is load-bearing, and the domain byte makes
  pure ML-DSA and HashML-DSA disjoint.

### `Mldsa/Decode.lean` — a model of the shipped packed z decoder

26 audited theorems.

The model is written in exact `Nat` arithmetic with the EVM's `div` and `mod`
semantics. What it models is the four-coefficients-per-word validity check of
`src/Decode.sol`, which runs on every call.

Lean proves things about a model; the EVM runs bytecode. For this decoder the
two are joined by testing, not by proof. `docs/FORMAL_VERIFICATION.md` §5.7
names that gap (the *refinement gap*) and says what stands in for a refinement
proof: E3/E6 over all 2^18 fields, the halmos centered-map checks, and mutants
M11–M13.

About the model itself:

* the single conditional subtraction is `mod q`, including at `u = q`, the
  `z = 0` field, which must canonicalise to 0 and not to `q`
  (`canon_zero_field`);
* bit 32 of each of the two edge words is the comparison it is meant to be, and
  their conjunction is exactly the FIPS 204 rejection `|z| >= gamma1 - beta`,
  with the boundary rejected on both tails (`reject_iff_fips`, plus four
  `boundary_*` witnesses);
* the packed word is four independent copies of that: neither the `add` nor the
  `sub` moves a bit across a lane boundary (`swar_z_lane_independent`);
* and `b*(2^s + 2^t)` is the OR of the two shifted copies, with the three
  shipped constants exactly those powers (`fused_disjoint`,
  `zp*_is_two_powers`).

### `Mldsa/Audit.lean`

Runs `#print axioms` on all 64 audited theorems at build time.

`Mldsa/Barrett.lean` alone holds 48 top-level `theorem`s, of which 27 are pinned
by name, statement digest and axiom set in `check_axioms.py`. The other counts
on this page are audited counts too.

## How to run

```sh
cd formal/lean
elan toolchain install $(cat lean-toolchain)   # once
lake build
python3 check_axioms.py
```

`check_axioms.py` is the hard CI check. It scans the sources for proof escape
hatches, re-elaborates the whole development from source in a cache-free
sandbox, and checks the audited theorem names, their statements (by pinned
digest) and their axiom dependencies.

## Axiom and sorry policy

* **Zero `sorry`**, and no `admit`, `native_decide`, `unsafe`,
  `@[implemented_by]`, `@[extern]`, or user-declared axioms.
* Every audited theorem depends on **at most Lean's own three axioms**:
  `propext`, `Quot.sound`, `Classical.choice`. Anything else, `sorryAx` above
  all, fails the check.

Both policies are enforced mechanically by `check_axioms.py`, not by
inspection.
