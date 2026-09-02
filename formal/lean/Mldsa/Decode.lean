/-
# The packed z decoder: canonicalisation and the STRICT norm gate

`src/Decode.sol`'s `_unpackZPoly` decodes FOUR coefficients per 256-bit word.
Per 64-bit lane, with `v` the 18-bit wire field and `z = gamma1 - v` the signed
coefficient FIPS 204 BitUnpack produces:

```
u := sub(Z_UOFF, V)                                     -- q + gamma1 - v
o := sub(u, mul(shr(32, and(add(u, Z_QB32), Z_BIT32)), q))
bad := and(add(o, Z_NLO), sub(Z_NHI, o))                -- bit 32 = REJECT
```

Everything the gate does is carried by three carry/borrow flags, each read as
bit 32 of a lane that is provably below `2^33`.  This file proves, in exact Nat
arithmetic with the EVM's `div`/`mod` semantics, that

* the single conditional subtraction is `mod q`, including at `u = q` -- the
  `z = 0` field, which must canonicalise to `0` and not to `q`
  (`canon_zero_field`, the defect ZKNox's decoder has);
* `bit 32` of each of the two edge words is the comparison it is meant to be;
* their conjunction is EXACTLY the FIPS 204 rejection `|z| >= gamma1 - beta`,
  with the boundary REJECTED on both tails (`reject_iff_fips`, and the four
  `boundary_*` witnesses that pin both tails at both directions);
* and the packed word is four independent copies of that: neither the `add` nor
  the `sub` moves a bit across a lane boundary (`swar_z_lane_independent`).

Companion to Z3 obligations S8b (the same statement, symbolically, for four
symbolic lanes at EVM semantics) and E3b/E4b/E5b (the same statement, by
complete enumeration of the 2^18 field values).  Lean core only, no mathlib.
-/

namespace Mldsa.Decode

/-- Dilithium prime. -/
def q : Nat := 8380417
/-- ML-DSA-44 `gamma1 = 2^17`. -/
def gamma1 : Nat := 131072
/-- ML-DSA-44 `beta = tau * eta = 39 * 2`. -/
def beta : Nat := 78
/-- The STRICT norm bound `gamma1 - beta`. -/
def nbound : Nat := gamma1 - beta
/-- `Z_UOFF`, per lane. -/
def uoff : Nat := q + gamma1
/-- The flag bit's weight. -/
def W32 : Nat := 2 ^ 32
/-- `Z_QB32`, per lane. -/
def qb32 : Nat := W32 - q
/-- `Z_NLO`, per lane. -/
def nlo : Nat := W32 - nbound
/-- `Z_NHI`, per lane. -/
def nhi : Nat := W32 + q - nbound
/-- The wire field domain: 18 bits. -/
def fieldMax : Nat := 2 ^ 18

/-- `u = q + gamma1 - v`, the uncanonicalised centered value. -/
def u (v : Nat) : Nat := uoff - v
/-- The canonicalisation flag: bit 32 of `u + (2^32 - q)`. -/
def flag (v : Nat) : Nat := ((u v + qb32) / W32) % 2
/-- The stored lane. -/
def canon (v : Nat) : Nat := u v - q * flag v
/-- Bit 32 of `o + Z_NLO`. -/
def loBit (v : Nat) : Nat := ((canon v + nlo) / W32) % 2
/-- Bit 32 of `Z_NHI - o`. -/
def hiBit (v : Nat) : Nat := ((nhi - canon v) / W32) % 2
/-- The lane's verdict: the AND of the two edge bits. -/
def reject (v : Nat) : Prop := loBit v = 1 ∧ hiBit v = 1

instance (v : Nat) : Decidable (reject v) := by
  unfold reject; infer_instance

/-! ## The centered value -/

theorem u_bounds {v : Nat} (hv : v < fieldMax) : 8249346 ≤ u v ∧ u v ≤ 8511489 := by
  simp only [u, uoff, q, gamma1, fieldMax] at *
  omega

theorem u_lt_two_q {v : Nat} (hv : v < fieldMax) : u v < 2 * q := by
  have := u_bounds hv
  simp only [q] at *
  omega

/-! ## The single conditional subtraction is `mod q` -/

theorem flag_no_carry {v : Nat} (hv : v < fieldMax) : u v + qb32 < 2 ^ 33 := by
  have := u_bounds hv
  simp only [qb32, W32, q] at *
  omega

theorem flag_is_a_bit {v : Nat} (hv : v < fieldMax) : flag v = 0 ∨ flag v = 1 := by
  simp only [flag]
  omega

/-- The flag is EXACTLY `[u >= q]` -- the comparison the conditional subtraction
needs, obtained with one add and one bit. -/
theorem flag_iff_u_ge_q {v : Nat} (hv : v < fieldMax) : flag v = 1 ↔ q ≤ u v := by
  have hb := u_bounds hv
  simp only [flag, qb32, W32, q] at *
  omega

theorem canon_lt_q {v : Nat} (hv : v < fieldMax) : canon v < q := by
  have hb := u_bounds hv
  have hf := flag_is_a_bit hv
  have hi := flag_iff_u_ge_q hv
  simp only [canon, q] at *
  omega

/-- The stored lane, in closed form: `gamma1 - v` for the fields whose signed
coefficient is non-negative, and `gamma1 + q - v` for the rest.  This is FIPS 204
BitUnpack composed with reduction mod `q`. -/
theorem canon_closed_form {v : Nat} (hv : v < fieldMax) :
    (v ≤ gamma1 ∧ canon v = gamma1 - v) ∨ (gamma1 < v ∧ canon v = uoff - v) := by
  have hb := u_bounds hv
  have hi := flag_iff_u_ge_q hv
  have hf := flag_is_a_bit hv
  simp only [canon, u, uoff, q, gamma1, fieldMax] at *
  omega

/-- **The `z = 0` field canonicalises to 0, not to `q`.**  `v = gamma1` is the
one field at which `u` equals `q` exactly, so it is the one the `>=` in the flag
decides; taking the comparison strictly stores `q`, which is out of range for
every consumer and is the defect documented in EXPLAINER 10. -/
theorem canon_zero_field : canon gamma1 = 0 := by
  simp only [canon, flag, u, uoff, qb32, W32, q, gamma1]

/-! ## The two edges of the strict window -/

theorem lo_no_carry {v : Nat} (hv : v < fieldMax) : canon v + nlo < 2 ^ 33 := by
  have := canon_lt_q hv
  simp only [nlo, nbound, W32, q, gamma1, beta] at *
  omega

theorem hi_no_borrow {v : Nat} (hv : v < fieldMax) : canon v < nhi ∧ nhi - canon v < 2 ^ 33 := by
  have := canon_lt_q hv
  simp only [nhi, nbound, W32, q, gamma1, beta] at *
  omega

/-- Bit 32 of `o + Z_NLO` is `[o >= gamma1 - beta]`. -/
theorem lo_iff {v : Nat} (hv : v < fieldMax) : loBit v = 1 ↔ nbound ≤ canon v := by
  have := canon_lt_q hv
  simp only [loBit, nlo, nbound, W32, q, gamma1, beta] at *
  omega

/-- Bit 32 of `Z_NHI - o` is `[o <= q - (gamma1 - beta)]`. -/
theorem hi_iff {v : Nat} (hv : v < fieldMax) : hiBit v = 1 ↔ canon v ≤ q - nbound := by
  have := canon_lt_q hv
  simp only [hiBit, nhi, nbound, W32, q, gamma1, beta] at *
  omega

/-- **The gate is the FIPS 204 norm test.**  `reject v` holds exactly on the
fields whose signed coefficient has `|z| >= gamma1 - beta`, which on the wire
encoding `z = gamma1 - v` is `v <= beta` on one tail and `2*gamma1 - beta <= v`
on the other.  The bound is STRICT, so both boundary fields are IN the rejected
set. -/
theorem reject_iff_fips {v : Nat} (hv : v < fieldMax) :
    reject v ↔ (v ≤ beta ∨ 2 * gamma1 - beta ≤ v) := by
  have hl := lo_iff hv
  have hh := hi_iff hv
  have hc := canon_closed_form hv
  have hq := canon_lt_q hv
  simp only [reject, nbound, q, gamma1, beta, uoff, fieldMax] at *
  omega

/-! ## The boundary, both tails, both directions -/

theorem boundary_low_rejected : reject beta := by decide
theorem boundary_low_inside_accepted : ¬ reject (beta + 1) := by decide
theorem boundary_high_rejected : reject (2 * gamma1 - beta) := by decide
theorem boundary_high_inside_accepted : ¬ reject (2 * gamma1 - beta - 1) := by decide

/-! ## Four lanes, one word -/

def W : Nat := 2 ^ 256
def evmAdd (a b : Nat) : Nat := (a + b) % W
def evmSub (a b : Nat) : Nat := (a + (W - b % W)) % W
/-- `rep4 c` is the per-lane constant replicated into all four 64-bit lanes --
the shape of every `Z_*` constant in the kernel. -/
def rep4 (c : Nat) : Nat := c + c * 2 ^ 64 + c * 2 ^ 128 + c * 2 ^ 192

/-- The packed `add` of a replicated constant is four lane-wise adds, provided
no lane sum reaches `2^64`. -/
theorem addSplit4 {l0 l1 l2 l3 c : Nat}
    (h0 : l0 + c < 2 ^ 64) (h1 : l1 + c < 2 ^ 64)
    (h2 : l2 + c < 2 ^ 64) (h3 : l3 + c < 2 ^ 64) :
    evmAdd (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192) (rep4 c)
      = (l0 + c) + (l1 + c) * 2 ^ 64 + (l2 + c) * 2 ^ 128 + (l3 + c) * 2 ^ 192 := by
  simp only [evmAdd, rep4, W]
  omega

/-- The packed `sub` FROM a replicated constant is four lane-wise subtractions,
provided no lane borrows. -/
theorem subFromRep4 {l0 l1 l2 l3 c : Nat}
    (h0 : l0 ≤ c) (h1 : l1 ≤ c) (h2 : l2 ≤ c) (h3 : l3 ≤ c) (hc : c < 2 ^ 64) :
    evmSub (rep4 c) (l0 + l1 * 2 ^ 64 + l2 * 2 ^ 128 + l3 * 2 ^ 192)
      = (c - l0) + (c - l1) * 2 ^ 64 + (c - l2) * 2 ^ 128 + (c - l3) * 2 ^ 192 := by
  simp only [evmSub, rep4, W]
  omega

/-- **No cross-lane leakage.**  The word the kernel actually forms,
`sub(Z_UOFF, V)`, is exactly the four scalar `u`s in their lanes -- so lane `k`
of every later word is a function of `v k` alone, and the ONE gate expression is
four independent gates.  (The three later words are the same lemma at different
constants: `addSplit4` for `u + Z_QB32` and `o + Z_NLO`, `subFromRep4` for
`Z_NHI - o`, each with its no-carry / no-borrow side condition discharged by
`flag_no_carry`, `lo_no_carry` and `hi_no_borrow` above.) -/
theorem swar_z_lane_independent {v0 v1 v2 v3 : Nat}
    (h0 : v0 < fieldMax) (h1 : v1 < fieldMax) (h2 : v2 < fieldMax) (h3 : v3 < fieldMax) :
    evmSub (rep4 uoff) (v0 + v1 * 2 ^ 64 + v2 * 2 ^ 128 + v3 * 2 ^ 192)
      = u v0 + u v1 * 2 ^ 64 + u v2 * 2 ^ 128 + u v3 * 2 ^ 192 := by
  have b : ∀ x : Nat, x < fieldMax → x ≤ uoff := by
    intro x hx; simp only [fieldMax, uoff, q, gamma1] at *; omega
  have hw : uoff < 2 ^ 64 := by simp only [uoff, q, gamma1]; omega
  simp only [u]
  exact subFromRep4 (b v0 h0) (b v1 h1) (b v2 h2) (b v3 h3) hw

/-- ... and every lane of the flag word stays inside its own 64 bits, which is
the side condition `addSplit4` needs at `Z_QB32`. -/
theorem flag_word_lane_fits {v : Nat} (hv : v < fieldMax) : u v + qb32 < 2 ^ 64 := by
  have := flag_no_carry hv
  omega

/-! ## The fused byte placement

The three bytes of a 9-byte group that straddle a field boundary (bytes 2, 4
and 6) are placed at BOTH of their bit positions by ONE multiply:

```
mul(byte(2, w), Z_P2)   with   Z_P2 = 2^62 + 2^16
mul(byte(4, w), Z_P4)   with   Z_P4 = 2^124 + 2^78
mul(byte(6, w), Z_P6)   with   Z_P6 = 2^186 + 2^140
```

`b * (2^s + 2^t) = b * 2^s + b * 2^t`, and the two summands are DISJOINT for
`b < 2^8` because `t - s = 46 > 8`, so the sum is also the OR the twelve-term
model of Z3 obligation O10 states.  Proved here as an identity on `Nat`
addition, with disjointness discharged by the shift gap, so the statement holds
for every byte value rather than for a sample. -/

/-- `b * (2^s + 2^t)` splits into the two shifted copies. -/
theorem fused_split (b s t : Nat) :
    b * (2 ^ s + 2 ^ t) = b * 2 ^ s + b * 2 ^ t :=
  Nat.mul_add b (2 ^ s) (2 ^ t)

/-- ... and for a byte the two copies do not overlap, so the sum IS the OR:
`b * 2^s < 2^(s+8) ≤ 2^t`.  This is the whole content of "the multiply emits
the same two disjoint terms the twelve-term model states" -- the shipped shifts
are 46 apart, far more than the 8 bits a byte spans. -/
theorem fused_disjoint {b s t : Nat} (hb : b < 2 ^ 8) (hst : s + 8 ≤ t) :
    b * 2 ^ s < 2 ^ t := by
  have h1 : b * 2 ^ s < 2 ^ 8 * 2 ^ s :=
    Nat.mul_lt_mul_of_lt_of_le hb (Nat.le_refl _) (Nat.two_pow_pos s)
  have h2 : (2 : Nat) ^ 8 * 2 ^ s = 2 ^ (s + 8) := by
    rw [← Nat.pow_add, Nat.add_comm]
  have h3 : (2 : Nat) ^ (s + 8) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) hst
  omega

/-- The three shipped constants are exactly the two powers their pairs name. -/
theorem zp2_is_two_powers : (0x4000000000010000 : Nat) = 2 ^ 62 + 2 ^ 16 := by decide
theorem zp4_is_two_powers :
    (0x10000000000040000000000000000000 : Nat) = 2 ^ 124 + 2 ^ 78 := by decide
theorem zp6_is_two_powers :
    (0x40000000000100000000000000000000000000000000000 : Nat)
      = 2 ^ 186 + 2 ^ 140 := by decide

end Mldsa.Decode
