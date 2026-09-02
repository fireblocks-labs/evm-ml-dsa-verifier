/-
# The lazy TWO-STEP Barrett reduction, proved under **exact EVM 256-bit semantics**

`test/ZZZ_NttVariants.sol` (forward) and `test/ZZZ_InvNtt.sol` (inverse) — and
the shipped `src/Ntt.sol` / `src/InvNtt.sol` they mirror — reduce a lane with
the two Yul expressions

    r := sub(x, mul(shr(33, mul(x, MU33)), Q))          MU33 = 1025 = ⌊2^33/q⌋
    r := sub(r, mul(shr(23, r),            Q))          ⌊2^23/q⌋ == 1, elided

and the whole packed-NTT lane analysis rests on `0 ≤ r < 2q`.

Both lines are Barrett steps.  The first uses a deliberately COARSE constant:
`x·MU33 < 2^64` for every `x` in the deployed domain, so in the packed form each
64-bit SWAR lane's product stays inside its own lane and **nothing has to be
spread to 128-bit spacing** — which is what the previous revision of this
development had to model, at two masks, a shift and a repack per reduction.  The
price of the coarse constant is that step 1 lands under `2^33` rather than under
`2q`; step 2 is the same Barrett step with `mu = 1` (an identity of *this*
modulus: `q = 2^23 − 2^13 + 1`, so `⌊2^23/q⌋ = 1` and `2^23 − q = 8191`), and it
closes the remaining ten bits.

That bound is also discharged by Z3 over the *integers*
(`formal/z3/verify_all.py` S1/S2/S7/S13) and by a dense sweep (E9a/E9b).  The
corresponding **bytecode-level** obligations in `test/FV_Kernels.sol` all TIME
OUT under halmos 0.3.3 — measured with yices 2.6.4, z3 4.12.6 **and**
bitwuzla 0.8.1, 300 s each.  That is not a tooling accident: the statement
bounds a quotient, and a raw QF_BV encoding of it returns `unknown` at every
word width from 96 to 256 bits (measured).

This module removes the need for that query.  Rather than asking a bit-vector
engine to rediscover the arithmetic, it **models the EVM opcodes exactly**

    evmMul a b = (a * b) % 2^256      evmShr k a = a / 2^k
    evmSub a b = (a + (2^256 - b % 2^256)) % 2^256

and proves the bound about `barrettEVM`, the literal composition of those
opcodes, in the Lean kernel.  Wrap-around is not assumed away: it is part of the
definition, and the proof *shows* it does not occur (`barrettEVM_eq_nat`).

After this, exactly one link remains outside the proof assistant, and it is
syntactic: that the Yul above is compiled to `MUL`/`SHR`/`MUL`/`SUB`, twice, on
the deployed bytecode.  `test/FV2_Barrett.sol` discharges that link at the
bytecode level (`check_w*`), because those are pure no-wrap facts that halmos
proves in milliseconds.
-/

set_option exponentiation.threshold 600
set_option maxRecDepth 100000

namespace Mldsa
namespace Barrett

/-! ## EVM word semantics (exact, wrap-around included) -/

/-- The EVM word modulus `2^256`. -/
def W : Nat := 2 ^ 256

/-- `MUL`: 256-bit wrapping multiplication. -/
def evmMul (a b : Nat) : Nat := (a * b) % W

/-- `SHR`: `shr(k, a)`, logical right shift = floor division by `2^k`. -/
def evmShr (k a : Nat) : Nat := a / 2 ^ k

/-- `SUB`: 256-bit wrapping subtraction, `(a - b) mod 2^256`. -/
def evmSub (a b : Nat) : Nat := (a + (W - b % W)) % W

/-! ## Kernel constants -/

/-- `q = 8380417`, the ML-DSA modulus. -/
def q : Nat := 8380417
/-- `MU33 = ⌊2^33 / q⌋ = 1025`, step 1's coarse Barrett constant. -/
def mu : Nat := 1025
/-- `d = 2^33 − MU33·q = 7167`, step 1's Barrett defect. -/
def d : Nat := 7167

theorem mu_val : mu = 1025 := by decide
/-- The constant in the source really is the floor the comment claims. -/
theorem mu_is_floor : mu = 2 ^ 33 / q := by decide
/-- The defining identity of the Barrett constant. -/
theorem mu_q_add_d : mu * q + d = 2 ^ 33 := by decide
/-- Step 2's constant is `⌊2^23/q⌋ = 1`, which is why its multiply is elided —
a fact about THIS modulus (`q = 2^23 − 2^13 + 1`), not a coincidence. -/
theorem unit_step_is_floor : 2 ^ 23 / q = 1 := by decide
/-- and `2^23 − q = 2^13 − 1 = 8191` is the factor by which step 2 shrinks the
high part of its input. -/
theorem q_sparse_form : 2 ^ 23 - q = 2 ^ 13 - 1 := by decide

/-- Step 1's quotient: `shr(33, mul(x, MU33))`. -/
def qhat (x : Nat) : Nat := x * mu / 2 ^ 33
/-- Step 1, over `Nat`, with no wrap-around anywhere. -/
def step1 (x : Nat) : Nat := x - qhat x * q
/-- Step 2's quotient: `shr(23, x1)` — the same Barrett step with `mu = 1`. -/
def bhat (y : Nat) : Nat := y / 2 ^ 23
/-- The whole reduction over `Nat`. -/
def barrettNat (x : Nat) : Nat := step1 x - bhat (step1 x) * q

/-- Step 1 as the exact composition of the opcodes it emits. -/
def step1EVM (x : Nat) : Nat := evmSub x (evmMul (evmShr 33 (evmMul x mu)) q)
/-- Step 2 as the exact composition of the opcodes it emits. -/
def step2EVM (y : Nat) : Nat := evmSub y (evmMul (evmShr 23 y) q)
/-- The kernel: the two lines, in order. -/
def barrettEVM (x : Nat) : Nat := step2EVM (step1EVM x)

/-! ## The two deployed input domains (`formal/z3/verify_all.py` C9b / C9d) -/

/-- Forward-NTT worst product, `15·q·(q−1)`. -/
def fwdMax : Nat := 15 * q * (q - 1)
/-- Inverse-NTT worst product, `128·q·(q−1)` (the larger of the two). -/
def invMax : Nat := 128 * q * (q - 1)

theorem fwdMax_val : fwdMax = 1053470710702080 := by decide
theorem invMax_val : invMax = 8989616731324416 := by decide
theorem fwdMax_lt_two_pow_50 : fwdMax < 2 ^ 50 := by decide
theorem invMax_lt_two_pow_53 : invMax < 2 ^ 53 := by decide

/-! ## Step 0 — LANE-LOCALITY, the fact the whole design rests on

`x·MU33 < 2^63` over the deployed domain, so in the packed form a lane's product
never reaches its neighbour and no spreading is needed.  The `2^63` (rather than
`2^64`) is what also keeps the four-lane word below `2^256` — see `mulSplit4`. -/

theorem lane_product_lt_two_pow_63 {x : Nat} (hx : x ≤ invMax) : x * mu < 2 ^ 63 := by
  simp only [invMax, q, mu] at *
  omega

/-- and therefore step 1's quotient fits the 31-bit field of the `QHATM31` mask
(with a bit to spare: it is in fact below `2^30`). -/
theorem qhat_lt_two_pow_31 {x : Nat} (hx : x ≤ invMax) : x * mu / 2 ^ 33 < 2 ^ 31 := by
  simp only [invMax, q, mu] at *
  omega

/-! ## Step 1 — neither subtraction ever borrows

`⌊x·MU/2^33⌋·q ≤ x` for **every** `x : Nat`, with no domain restriction at all:
`MU·q ≤ 2^33` by construction, so the quotient can never overshoot.  The same
argument gives step 2's no-borrow from `q ≤ 2^23`.  These are what make `evmSub`
ordinary subtraction, and they are also the `r ≥ 0` half of S1/S2. -/
theorem no_borrow (x : Nat) : qhat x * q ≤ x := by
  simp only [qhat, mu, q]
  omega

theorem second_no_borrow (y : Nat) : bhat y * q ≤ y := by
  simp only [bhat, q]
  omega

/-! ## Step 2 — the lazy bound over `Nat`

The side condition is the two-step margin, stated once and instantiated twice:

    (X·d + q·(2^33 − 1))·8191 + (2^23 − 1)·2^23·2^33  <  2·q·2^23·2^33

It bounds step 1's remainder `s = x·MU mod 2^33` by its worst case `2^33 − 1`
and step 2's by `2^23 − 1`, independently of `x`, which is *sufficient* but not
sharp.  The sharp threshold is pinned separately (`firstFail` below;
`formal/z3/verify_all.py` S13, C11a).  At `invMax` the margin is 1.144×, and
`2·invMax` violates it — see `margin_guard_hmg`. -/
theorem barrettNat_lt_two_q {X x : Nat} (hx : x ≤ X)
    (hmg : (X * d + q * (2 ^ 33 - 1)) * 8191 + (2 ^ 23 - 1) * 2 ^ 23 * 2 ^ 33
             < 2 * q * 2 ^ 23 * 2 ^ 33) :
    barrettNat x < 2 * q := by
  simp only [barrettNat, step1, qhat, bhat, mu, q, d] at *
  omega

/-- and step 1 on its own lands under `2^33` — the bound that lets step 2 reuse
the very same 31-bit mask (its own quotient is then below `2^10`). -/
theorem step1_lt_two_pow_33 {x : Nat} (hx : x ≤ invMax) : step1 x < 2 ^ 33 := by
  simp only [step1, qhat, mu, q, invMax] at *
  omega

/-! ## Step 3 — the EVM computation equals the `Nat` computation

Both `MUL`s and both `SUB`s of each step are shown not to wrap.  The only
hypothesis is that the first product fits in a word, which every domain of
interest satisfies with 193 bits to spare. -/
theorem step1EVM_eq_nat {X x : Nat} (hx : x ≤ X) (hW : X * mu < W) :
    step1EVM x = step1 x := by
  have h1 : x * mu < W := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right mu hx) hW
  have h2 : (x * mu / 2 ^ 33) * q ≤ x := no_borrow x
  have hxW : x < W := by
    have : x * 1 ≤ x * mu := Nat.mul_le_mul_left x (by decide)
    omega
  simp only [step1EVM, step1, qhat, evmMul, evmShr, evmSub]
  simp only [W] at h1 h2 hxW ⊢
  rw [Nat.mod_eq_of_lt h1]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h2 hxW)]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h2 hxW)]
  omega

theorem step2EVM_eq_nat {y : Nat} (hy : y < W) : step2EVM y = y - bhat y * q := by
  have h2 : y / 2 ^ 23 * q ≤ y := by
    have := second_no_borrow y; simpa [bhat] using this
  simp only [step2EVM, bhat, evmMul, evmShr, evmSub]
  simp only [W] at h2 hy ⊢
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h2 hy)]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h2 hy)]
  omega

theorem barrettEVM_eq_nat {X x : Nat} (hx : x ≤ X) (hW : X * mu < W) :
    barrettEVM x = barrettNat x := by
  have h1 : step1EVM x = step1 x := step1EVM_eq_nat hx hW
  have hxW : x < W := by
    have h1' : x * mu < W := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right mu hx) hW
    have : x * 1 ≤ x * mu := Nat.mul_le_mul_left x (by decide)
    omega
  have h3 : step1 x < W := by
    have := no_borrow x
    simp only [step1]
    omega
  simp only [barrettEVM, barrettNat, h1]
  exact step2EVM_eq_nat h3

/-- **The kernel theorem.**  For every `x ≤ X` satisfying the two side
conditions, the compiled Yul — modelled opcode by opcode, wrap-around included —
produces a value below `2q`. -/
theorem barrettEVM_lt_two_q {X x : Nat} (hx : x ≤ X) (hW : X * mu < W)
    (hmg : (X * d + q * (2 ^ 33 - 1)) * 8191 + (2 ^ 23 - 1) * 2 ^ 23 * 2 ^ 33
             < 2 * q * 2 ^ 23 * 2 ^ 33) :
    barrettEVM x < 2 * q := by
  rw [barrettEVM_eq_nat hx hW]
  exact barrettNat_lt_two_q hx hmg

/-! ## Step 4 — it is a *reduction*, not merely a bounded map -/

/-- `barrettNat x ≡ x (mod q)` for every `x`: BOTH steps subtract a multiple of
`q` (Z3 obligations S3/S4). -/
theorem barrettNat_congr (x : Nat) : barrettNat x % q = x % q := by
  have h1 : qhat x * q ≤ x := no_borrow x
  have h2 : bhat (step1 x) * q ≤ step1 x := second_no_borrow (step1 x)
  have e1 : step1 x + qhat x * q = x := by simp only [step1]; omega
  have e2 : barrettNat x + bhat (step1 x) * q = step1 x := by simp only [barrettNat]; omega
  calc barrettNat x % q
      = (barrettNat x + bhat (step1 x) * q) % q :=
        (Nat.add_mul_mod_self_right _ _ _).symm
    _ = step1 x % q := by rw [e2]
    _ = (step1 x + qhat x * q) % q := (Nat.add_mul_mod_self_right _ _ _).symm
    _ = x % q := by rw [e1]

/-! ## Instantiations at the two deployed domains -/

theorem fwd_no_wrap : fwdMax * mu < W := by decide
theorem fwd_margin :
    (fwdMax * d + q * (2 ^ 33 - 1)) * 8191 + (2 ^ 23 - 1) * 2 ^ 23 * 2 ^ 33
      < 2 * q * 2 ^ 23 * 2 ^ 33 := by decide
theorem inv_no_wrap : invMax * mu < W := by decide
theorem inv_margin :
    (invMax * d + q * (2 ^ 33 - 1)) * 8191 + (2 ^ 23 - 1) * 2 ^ 23 * 2 ^ 33
      < 2 * q * 2 ^ 23 * 2 ^ 33 := by decide

/-- **Forward NTT**: every lane product `x ≤ 15·q·(q−1)` reduces below `2q`. -/
theorem barrett_forward {x : Nat} (hx : x ≤ fwdMax) : barrettEVM x < 2 * q :=
  barrettEVM_lt_two_q hx fwd_no_wrap fwd_margin

/-- **Inverse NTT**: every lane product `x ≤ 128·q·(q−1)` reduces below `2q`. -/
theorem barrett_inverse {x : Nat} (hx : x ≤ invMax) : barrettEVM x < 2 * q :=
  barrettEVM_lt_two_q hx inv_no_wrap inv_margin

/-- …and on that domain it really is `x mod q` up to one multiple of `q`. -/
theorem barrett_inverse_congr {x : Nat} (hx : x ≤ invMax) :
    barrettEVM x % q = x % q := by
  rw [barrettEVM_eq_nat hx inv_no_wrap]
  exact barrettNat_congr x

/-! ## The domain restriction is necessary, and the margin is thin

The smallest input violating `r < 2q` is `10 285 325 456 994 078`, only 1.144×
above `invMax` (`formal/z3/verify_all.py` C11a).  Both halves of that claim are
re-checked here by kernel evaluation **of the EVM model itself**, so the
theorems above cannot be vacuously true of every input.

There is a SECOND cliff, and it is the higher of the two: the first `x` whose
step-1 product leaves its own 64-bit lane is `17 996 823 486 545 905`
(= `⌈2^64/MU33⌉`, obligation C11d).  `r < 2q` is therefore what binds. -/

/-- The first violating input, found by symbolic execution. -/
def firstFail : Nat := 10285325456994078

/-- At `firstFail` the EVM kernel returns exactly `2q`: the bound FAILS there. -/
theorem firstFail_breaks : barrettEVM firstFail = 2 * q := by decide

/-- One below it the kernel is still inside the bound — a threshold, not a
region, which is what makes the `invMax` margin meaningful. -/
theorem firstFail_pred_ok : barrettEVM (firstFail - 1) < 2 * q := by decide

/-- `invMax` is inside the safe domain. -/
theorem invMax_lt_firstFail : invMax < firstFail := by decide

/-- **Guard.**  One extra unreduced NTT layer doubles lane growth and overshoots
the first failure point: `2·invMax ≥ firstFail`.  This is obligation C11c of
`formal/z3/verify_all.py`, restated about the EVM model. -/
theorem margin_guard : firstFail ≤ 2 * invMax := by decide

/-- and the sufficient margin condition is likewise violated at `2·invMax`, so
`barrett_inverse` genuinely cannot be restated one layer deeper. -/
theorem margin_guard_hmg :
    ¬ ((2 * invMax * d + q * (2 ^ 33 - 1)) * 8191 + (2 ^ 23 - 1) * 2 ^ 23 * 2 ^ 33
         < 2 * q * 2 ^ 23 * 2 ^ 33) := by decide

/-- The lane-locality cliff is ABOVE the `r < 2q` cliff (obligation C11d), so
the binding constraint really is the one the margin theorems are stated about. -/
theorem lane_cliff_above_firstFail : firstFail < 17996823486545905 := by decide

/-- and it IS a cliff: at that input the step-1 product leaves the lane. -/
theorem lane_cliff_breaks : 17996823486545905 * mu ≥ 2 ^ 64 := by decide
theorem lane_cliff_pred_ok : (17996823486545905 - 1) * mu < 2 ^ 64 := by decide

/-- Non-vacuity witness: the model computes a concrete, correct value. -/
theorem invMax_reduces : barrettEVM invMax = 8380417 := by decide

/-- and the reduction of the worst inverse-NTT product really is congruent. -/
theorem invMax_reduces_congr : barrettEVM invMax % q = invMax % q := by decide

/-- **Step 2 is load-bearing.**  Step 1 alone leaves the worst inverse-NTT
product three orders of magnitude above `2q`, outside every lane bound the NTT
induction states. -/
theorem step1_alone_is_not_enough : step1EVM invMax > 2 * q := by decide

/-! # SWAR: the packed 4-lane form, with no spreading

The shipped transforms reduce one packed word — four 64-bit lanes — with exactly
the scalar opcodes above plus one mask each:

    w := sub(w, mul(and(shr(33, mul(w, MU33)), QHATM31), Q))
    w := sub(w, mul(and(shr(23, w),            QHATM31), Q))

The soundness question is **cross-lane leakage**: does lane 0's reduction see
lane 1's bits?  halmos times out on it.  Here `and(y, QHATM31)` is modelled
exactly as arithmetic on `Nat` — it keeps the 31-bit window at the bottom of
each of the four 64-bit lanes — and the result is proved to be *exactly* four
independent scalar reductions.

The mask width is not free: after `shr(33, ·)` the NEXT lane's bits begin at bit
`64 − 33 = 31` of this lane, and a lane's quotient is below `2^31` exactly when
its product is below `2^64`.  So ONE mask both extracts the quotient and blocks
the neighbour, and a 32-bit mask would admit one neighbour bit.  Step 2 reuses
it: its quotient is below `2^10` and its neighbour's bits begin at bit 41. -/

/-- `and(y, QHATM31)`: keep the 31-bit window at the bottom of each 64-bit lane. -/
def andQHATM31 (y : Nat) : Nat :=
  y % 2 ^ 31 + (y / 2 ^ 64) % 2 ^ 31 * 2 ^ 64
    + (y / 2 ^ 128) % 2 ^ 31 * 2 ^ 128 + (y / 2 ^ 192) % 2 ^ 31 * 2 ^ 192

/-- The packed step 1, opcode for opcode. -/
def swarStep1 (w : Nat) : Nat :=
  evmSub w (evmMul (andQHATM31 (evmShr 33 (evmMul w mu))) q)

/-- The packed step 2, opcode for opcode. -/
def swarStep2 (w : Nat) : Nat :=
  evmSub w (evmMul (andQHATM31 (evmShr 23 w)) q)

/-- The full packed block. -/
def swarBarrett4 (w : Nat) : Nat := swarStep2 (swarStep1 w)

/-- The four lane products fit one word, with no cross-lane carry: each is
below `2^63`, so their weighted sum is below `2^256`. -/
theorem mulSplit4 {l0 l1 l2 l3 : Nat}
    (h0 : l0 * mu < 2 ^ 63) (h1 : l1 * mu < 2 ^ 63)
    (h2 : l2 * mu < 2 ^ 63) (h3 : l3 * mu < 2 ^ 63) :
    evmMul (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192) mu
      = l0 * mu + l1 * mu * 2 ^ 64 + l2 * mu * 2 ^ 128 + l3 * mu * 2 ^ 192 := by
  simp only [evmMul, W, mu] at *
  have hexp : (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192) * 1025
      = l0 * 1025 + l1 * 1025 * 2 ^ 64 + l2 * 1025 * 2 ^ 128
        + l3 * 1025 * 2 ^ 192 := by omega
  rw [hexp]
  refine Nat.mod_eq_of_lt ?_
  omega

/-- `shr(33, ·)` of the product word: each lane's quotient lands at the bottom
of its own lane, and each lane's REMAINDER lands just below the next lane's
quotient — at bit `64k − 33`, i.e. 31 bits below the lane boundary. -/
theorem shrSplit4 {p0 p1 p2 p3 a0 a1 a2 a3 s0 s1 s2 s3 : Nat}
    (e0 : p0 = a0 * 2 ^ 33 + s0) (e1 : p1 = a1 * 2 ^ 33 + s1)
    (e2 : p2 = a2 * 2 ^ 33 + s2) (e3 : p3 = a3 * 2 ^ 33 + s3)
    (_b0 : s0 < 2 ^ 33) (b1 : s1 < 2 ^ 33) (b2 : s2 < 2 ^ 33) (b3 : s3 < 2 ^ 33) :
    (p0 + p1 * 2 ^ 64 + p2 * 2 ^ 128 + p3 * 2 ^ 192) / 2 ^ 33
      = a0 + s1 * 2 ^ 31 + a1 * 2 ^ 64 + s2 * 2 ^ 95 + a2 * 2 ^ 128
        + s3 * 2 ^ 159 + a3 * 2 ^ 192 := by
  subst e0; subst e1; subst e2; subst e3
  omega

/-- The mask keeps exactly the four quotients: the remainders sit at bits
`31 + 64k`, above each lane's 31-bit window and below the next lane. -/
theorem maskSplit4 {a0 a1 a2 a3 s1 s2 s3 : Nat}
    (h0 : a0 < 2 ^ 31) (h1 : a1 < 2 ^ 31) (h2 : a2 < 2 ^ 31) (h3 : a3 < 2 ^ 31)
    (b1 : s1 < 2 ^ 33) (b2 : s2 < 2 ^ 33) (b3 : s3 < 2 ^ 33) :
    andQHATM31 (a0 + s1 * 2 ^ 31 + a1 * 2 ^ 64 + s2 * 2 ^ 95 + a2 * 2 ^ 128
                + s3 * 2 ^ 159 + a3 * 2 ^ 192)
      = a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 := by
  simp only [andQHATM31]
  omega

/-- `mul(qhats, Q)` is again lane-local: each `a·q` is below `2^54`. -/
theorem mulSplit4q {a0 a1 a2 a3 : Nat}
    (h0 : a0 < 2 ^ 31) (h1 : a1 < 2 ^ 31) (h2 : a2 < 2 ^ 31) (h3 : a3 < 2 ^ 31) :
    evmMul (a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192) q
      = a0 * q + a1 * q * 2 ^ 64 + a2 * q * 2 ^ 128 + a3 * q * 2 ^ 192 := by
  simp only [evmMul, W, q] at *
  have hexp : (a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192) * 8380417
      = a0 * 8380417 + a1 * 8380417 * 2 ^ 64 + a2 * 8380417 * 2 ^ 128
        + a3 * 8380417 * 2 ^ 192 := by omega
  rw [hexp]
  refine Nat.mod_eq_of_lt ?_
  omega

/-- and the `SUB` is lane-wise ordinary subtraction when no lane borrows. -/
theorem subSplit4 {l0 l1 l2 l3 c0 c1 c2 c3 : Nat}
    (h0 : c0 ≤ l0) (h1 : c1 ≤ l1) (h2 : c2 ≤ l2) (h3 : c3 ≤ l3)
    (w0 : l0 < 2 ^ 64) (w1 : l1 < 2 ^ 64) (w2 : l2 < 2 ^ 64) (w3 : l3 < 2 ^ 64) :
    evmSub (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192)
           (c0 + c1 * 2 ^ 64 + c2 * 2 ^ 128 + c3 * 2 ^ 192)
      = (l0 - c0) + (l1 - c1) * 2 ^ 64 + (l2 - c2) * 2 ^ 128 + (l3 - c3) * 2 ^ 192 := by
  simp only [evmSub, W]
  omega

/-- **No cross-lane leakage, step 1.**  The packed first step of a word holding
four independent lanes is exactly the four scalar first steps. -/
theorem swar_step1_lane_independent {l0 l1 l2 l3 : Nat}
    (h0 : l0 ≤ invMax) (h1 : l1 ≤ invMax) (h2 : l2 ≤ invMax) (h3 : l3 ≤ invMax) :
    swarStep1 (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192)
      = step1 l0 + step1 l1 * 2 ^ 64 + step1 l2 * 2 ^ 128 + step1 l3 * 2 ^ 192 := by
  have p0 := lane_product_lt_two_pow_63 h0
  have p1 := lane_product_lt_two_pow_63 h1
  have p2 := lane_product_lt_two_pow_63 h2
  have p3 := lane_product_lt_two_pow_63 h3
  have q0 := qhat_lt_two_pow_31 h0
  have q1 := qhat_lt_two_pow_31 h1
  have q2 := qhat_lt_two_pow_31 h2
  have q3 := qhat_lt_two_pow_31 h3
  have n0 := no_borrow l0
  have n1 := no_borrow l1
  have n2 := no_borrow l2
  have n3 := no_borrow l3
  have lw : ∀ x : Nat, x ≤ invMax → x < 2 ^ 64 := by
    intro x hx; simp only [invMax, q] at hx; omega
  simp only [swarStep1, evmShr, mulSplit4 p0 p1 p2 p3]
  rw [shrSplit4 (a0 := l0 * mu / 2 ^ 33) (s0 := l0 * mu % 2 ^ 33)
        (a1 := l1 * mu / 2 ^ 33) (s1 := l1 * mu % 2 ^ 33)
        (a2 := l2 * mu / 2 ^ 33) (s2 := l2 * mu % 2 ^ 33)
        (a3 := l3 * mu / 2 ^ 33) (s3 := l3 * mu % 2 ^ 33)
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]
  rw [maskSplit4 (by simpa [qhat] using q0) (by simpa [qhat] using q1)
        (by simpa [qhat] using q2) (by simpa [qhat] using q3)
        (by omega) (by omega) (by omega)]
  rw [mulSplit4q (by simpa [qhat] using q0) (by simpa [qhat] using q1)
        (by simpa [qhat] using q2) (by simpa [qhat] using q3)]
  rw [subSplit4 (by simpa [qhat] using n0) (by simpa [qhat] using n1)
        (by simpa [qhat] using n2) (by simpa [qhat] using n3)
        (lw l0 h0) (lw l1 h1) (lw l2 h2) (lw l3 h3)]
  simp only [step1, qhat]

/-- `shr(23, ·)` of the step-1 word: the same shape one shift down, with the
remainders at bit `64k − 23` — 41 bits above each lane's window. -/
theorem shrSplit4b {p0 p1 p2 p3 a0 a1 a2 a3 s0 s1 s2 s3 : Nat}
    (e0 : p0 = a0 * 2 ^ 23 + s0) (e1 : p1 = a1 * 2 ^ 23 + s1)
    (e2 : p2 = a2 * 2 ^ 23 + s2) (e3 : p3 = a3 * 2 ^ 23 + s3)
    (_b0 : s0 < 2 ^ 23) (b1 : s1 < 2 ^ 23) (b2 : s2 < 2 ^ 23) (b3 : s3 < 2 ^ 23) :
    (p0 + p1 * 2 ^ 64 + p2 * 2 ^ 128 + p3 * 2 ^ 192) / 2 ^ 23
      = a0 + s1 * 2 ^ 41 + a1 * 2 ^ 64 + s2 * 2 ^ 105 + a2 * 2 ^ 128
        + s3 * 2 ^ 169 + a3 * 2 ^ 192 := by
  subst e0; subst e1; subst e2; subst e3
  omega

theorem maskSplit4b {a0 a1 a2 a3 s1 s2 s3 : Nat}
    (h0 : a0 < 2 ^ 31) (h1 : a1 < 2 ^ 31) (h2 : a2 < 2 ^ 31) (h3 : a3 < 2 ^ 31)
    (b1 : s1 < 2 ^ 23) (b2 : s2 < 2 ^ 23) (b3 : s3 < 2 ^ 23) :
    andQHATM31 (a0 + s1 * 2 ^ 41 + a1 * 2 ^ 64 + s2 * 2 ^ 105 + a2 * 2 ^ 128
                + s3 * 2 ^ 169 + a3 * 2 ^ 192)
      = a0 + a1 * 2 ^ 64 + a2 * 2 ^ 128 + a3 * 2 ^ 192 := by
  simp only [andQHATM31]
  omega

/-- **No cross-lane leakage, all four lanes, both steps.**  Every lane of the
packed word comes out as the scalar two-step reduction of the same input lane. -/
theorem swar_lane_independent {l0 l1 l2 l3 : Nat}
    (h0 : l0 ≤ invMax) (h1 : l1 ≤ invMax) (h2 : l2 ≤ invMax) (h3 : l3 ≤ invMax) :
    swarBarrett4 (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192)
      = barrettNat l0 + barrettNat l1 * 2 ^ 64
        + barrettNat l2 * 2 ^ 128 + barrettNat l3 * 2 ^ 192 := by
  have t0 := step1_lt_two_pow_33 h0
  have t1 := step1_lt_two_pow_33 h1
  have t2 := step1_lt_two_pow_33 h2
  have t3 := step1_lt_two_pow_33 h3
  have n0 := second_no_borrow (step1 l0)
  have n1 := second_no_borrow (step1 l1)
  have n2 := second_no_borrow (step1 l2)
  have n3 := second_no_borrow (step1 l3)
  simp only [swarBarrett4, swar_step1_lane_independent h0 h1 h2 h3, swarStep2, evmShr]
  rw [shrSplit4b (a0 := step1 l0 / 2 ^ 23) (s0 := step1 l0 % 2 ^ 23)
        (a1 := step1 l1 / 2 ^ 23) (s1 := step1 l1 % 2 ^ 23)
        (a2 := step1 l2 / 2 ^ 23) (s2 := step1 l2 % 2 ^ 23)
        (a3 := step1 l3 / 2 ^ 23) (s3 := step1 l3 % 2 ^ 23)
        (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]
  rw [maskSplit4b (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
  rw [mulSplit4q (by omega) (by omega) (by omega) (by omega)]
  rw [subSplit4 (by simpa [bhat] using n0) (by simpa [bhat] using n1)
        (by simpa [bhat] using n2) (by simpa [bhat] using n3)
        (by omega) (by omega) (by omega) (by omega)]
  simp only [barrettNat, bhat]

/-- Each output lane fits in its 64-bit slot (`< 2q < 2^24`), which is what makes
the packed word a valid input to the next layer. -/
theorem swar_lane_fits {x : Nat} (h : x ≤ invMax) : barrettNat x < 2 ^ 64 := by
  have := barrettNat_lt_two_q h inv_margin
  simp only [q] at this
  omega

end Barrett
end Mldsa
