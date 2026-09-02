/-
# Encoding-layer theorems: canonicality, injectivity, domain separation

Machine-checked statements about the encoding-layer components of FIPS 204 that
are historically bug-prone in Dilithium/ML-DSA implementations:

* **FIPS 204 Alg. 21 `HintBitUnpack` is a CANONICAL decoder.** Every hint set has
  at most one accepted 84-byte encoding, so a signature cannot be re-encoded into
  a different byte string that still verifies. This is the encoding-layer half of
  strong unforgeability, and the exact property whose absence produced the
  well-known Dilithium hint-malleability bugs (draft FIPS 204 omitted the strict
  index ordering check; RustCrypto `ml-dsa` CVE-2026-24850 accepted a repeated
  hint index; libcrux PR #1348 fixed an `ω` overflow check that never fired).
* **FIPS 204 §5.2 message representative** `M' = 0x00 ‖ |ctx| ‖ ctx ‖ M` is
  injective in `(ctx, M)`, so a signature is bound to its context; the `0x00` /
  `0x01` domain byte makes pure ML-DSA and HashML-DSA disjoint; and the
  `|ctx| ≤ 255` gate is proved *load-bearing* (drop it and the byte-level
  representative is provably ambiguous).

Lean core only — no mathlib, no `sorry`, no axioms beyond Lean's own.
-/

namespace Mldsa
namespace Encoding

/-! ## Parameters (ML-DSA-44, FIPS 204 Table 1) -/

/-- `k = 4` polynomials in the hint vector. -/
def K : Nat := 4
/-- `ω = 80`, the total hint-weight budget. -/
def OM : Nat := 80

/-! ## 1. `HintBitUnpack` (FIPS 204 Algorithm 21) is canonical

An encoding is a list `y` of `ω + k` byte values: `y[0..ω)` are the hint indices
of all polynomials concatenated, `y[ω+i]` is the *cumulative* index count after
polynomial `i`.  Note the asymmetry that has caused real bugs: the cumulative
counters are only **non-strictly** monotone (a polynomial may have zero hints),
while the indices *inside* a polynomial must be **strictly** increasing.

Index bytes are 8-bit and `n = 256`, so `y[j] < n` holds by construction — FIPS
204 therefore needs no explicit index-range check, and neither do we. -/

/-- Strictly increasing (the FIPS `y[Index−1] ≥ y[Index] ⇒ ⊥` rule). -/
def strictInc : List Nat → Bool
  | []          => true
  | [_]         => true
  | a :: b :: t => decide (a < b) && strictInc (b :: t)

/-- The row loop of FIPS 204 Alg. 21, structurally recursive on the cut list.
`cs` are the remaining cumulative counters, `rem` the unconsumed index bytes and
`prev` the running `Index`. Returns the per-polynomial index lists. -/
def decRows : List Nat → List Nat → Nat → Option (List (List Nat))
  | [],      rem, _    => if rem.all (· == 0) then some [] else none
  | c :: cs, rem, prev =>
      if prev ≤ c ∧ c ≤ OM ∧ c - prev ≤ rem.length ∧ strictInc (rem.take (c - prev)) = true then
        match decRows cs (rem.drop (c - prev)) c with
        | some rest => some (rem.take (c - prev) :: rest)
        | none      => none
      else none

/-- `HintBitUnpack`: split the `ω + k` bytes and run the row loop. -/
def decode (y : List Nat) : Option (List (List Nat)) :=
  if y.length = OM + K then decRows (y.drop OM) (y.take OM) 0 else none

/-- Cumulative counters of a segment list, starting from `prev`. -/
def cutsFrom : List (List Nat) → Nat → List Nat
  | [],      _    => []
  | s :: ss, prev => (prev + s.length) :: cutsFrom ss (prev + s.length)

/-- The canonical encoder (`HintBitPack`): indices, zero padding, counters. -/
def encode (segs : List (List Nat)) : List Nat :=
  (segs.flatten ++ List.replicate (OM - segs.flatten.length) 0) ++ cutsFrom segs 0

/-- A list all of whose entries are `0` *is* a `replicate`. -/
theorem all_zero_replicate : ∀ (l : List Nat), l.all (· == 0) = true →
    l = List.replicate l.length 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ha : a = 0 := h.1
    have ht := ih h.2
    subst ha
    simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
    exact ht

/-- **Core canonicality lemma.** Anything the row loop accepts has the canonical
shape: the index area is the concatenation of the decoded segments followed by
zero padding, and the counters are exactly the cumulative sums. -/
theorem decRows_canonical :
    ∀ (cs rem : List Nat) (prev : Nat) (segs : List (List Nat)),
      decRows cs rem prev = some segs →
        (∃ p, rem = segs.flatten ++ List.replicate p 0) ∧ cs = cutsFrom segs prev := by
  intro cs
  induction cs with
  | nil =>
    intro rem prev segs h
    simp only [decRows] at h
    by_cases hz : rem.all (· == 0) = true
    · rw [if_pos hz] at h
      cases h
      exact ⟨⟨rem.length, by simpa using all_zero_replicate rem hz⟩, rfl⟩
    · rw [if_neg hz] at h
      exact absurd h (by simp)
  | cons c cs ih =>
    intro rem prev segs h
    simp only [decRows] at h
    by_cases hc : prev ≤ c ∧ c ≤ OM ∧ c - prev ≤ rem.length ∧
                  strictInc (rem.take (c - prev)) = true
    · rw [if_pos hc] at h
      obtain ⟨hcp, _, hcl, _⟩ := hc
      cases hrec : decRows cs (rem.drop (c - prev)) c with
      | none => rw [hrec] at h; exact absurd h (by simp)
      | some rest =>
        rw [hrec] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨⟨p, hp⟩, hcuts⟩ := ih (rem.drop (c - prev)) c rest hrec
        have hlen : (rem.take (c - prev)).length = c - prev := by
          simp only [List.length_take]; omega
        constructor
        · refine ⟨p, ?_⟩
          calc rem = rem.take (c - prev) ++ rem.drop (c - prev) :=
                    (List.take_append_drop _ _).symm
            _ = rem.take (c - prev) ++ (rest.flatten ++ List.replicate p 0) := by rw [hp]
            _ = (rem.take (c - prev) ++ rest.flatten) ++ List.replicate p 0 :=
                    (List.append_assoc _ _ _).symm
            _ = (rem.take (c - prev) :: rest).flatten ++ List.replicate p 0 := rfl
        · show c :: cs = cutsFrom (rem.take (c - prev) :: rest) prev
          simp only [cutsFrom, hlen, List.cons.injEq]
          have hc' : prev + (c - prev) = c := by omega
          rw [hc']
          exact ⟨rfl, hcuts⟩
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- **`HintBitUnpack` is canonical.** Any accepted 84-byte encoding is *the*
canonical encoding of the hint set it decodes to.

Consequence: the hint field of an ML-DSA signature admits no re-encoding — the
encoding-layer statement of strong unforgeability. -/
theorem hint_decode_canonical (y : List Nat) (segs : List (List Nat))
    (h : decode y = some segs) : y = encode segs := by
  simp only [decode] at h
  by_cases hy : y.length = OM + K
  · rw [if_pos hy] at h
    obtain ⟨⟨p, hp⟩, hcuts⟩ := decRows_canonical (y.drop OM) (y.take OM) 0 segs h
    have hlt : (y.take OM).length = OM := by simp only [List.length_take]; omega
    have hsum : segs.flatten.length + p = OM := by
      have := congrArg List.length hp
      simp only [List.length_append, List.length_replicate, hlt] at this
      omega
    have hp' : p = OM - segs.flatten.length := by omega
    subst hp'
    calc y = y.take OM ++ y.drop OM := (List.take_append_drop _ _).symm
      _ = (segs.flatten ++ List.replicate (OM - segs.flatten.length) 0) ++ cutsFrom segs 0 := by
            rw [← hp, ← hcuts]
      _ = encode segs := rfl
  · rw [if_neg hy] at h; exact absurd h (by simp)

/-- **No hint-encoding malleability.** Two byte strings that decode to the same
hint set are the same byte string. -/
theorem hint_decode_injective (y y' : List Nat) (segs : List (List Nat))
    (h : decode y = some segs) (h' : decode y' = some segs) : y = y' := by
  rw [hint_decode_canonical y segs h, hint_decode_canonical y' segs h']

/-- Accepted encodings respect the `ω` weight budget: the total number of hint
indices never exceeds 80 (FIPS 204 Alg. 21 line 4, `y[ω+i] ≤ ω`). -/
theorem hint_weight_le_omega (y : List Nat) (segs : List (List Nat))
    (h : decode y = some segs) : segs.flatten.length ≤ OM := by
  simp only [decode] at h
  by_cases hy : y.length = OM + K
  · rw [if_pos hy] at h
    obtain ⟨⟨p, hp⟩, _⟩ := decRows_canonical (y.drop OM) (y.take OM) 0 segs h
    have hlt : (y.take OM).length = OM := by simp only [List.length_take]; omega
    have := congrArg List.length hp
    simp only [List.length_append, List.length_replicate, hlt] at this
    omega
  · rw [if_neg hy] at h; exact absurd h (by simp)

/-- The strict-increase gate is *load-bearing*: without it the decoder would
accept two different byte strings for the same hint *set* (the indices of one
polynomial in a different order), i.e. exactly the published Dilithium
malleability bug. -/
theorem strictInc_rejects_permutation :
    strictInc [0, 1] = true ∧ strictInc [1, 0] = false := by decide

/-- The strict-increase gate also rejects a *repeated* index — the concrete
RustCrypto ML-DSA bug (CVE-2026-24850), which used `≤` where FIPS requires `<`. -/
theorem strictInc_rejects_repeat : strictInc [3, 3] = false := by decide

/-- The trailing-padding gate is load-bearing too: a nonzero pad byte must be
rejected, otherwise every hint set gains 255 extra encodings per unused slot. -/
theorem padding_gate_rejects_nonzero :
    ([0, 0] : List Nat).all (· == 0) = true ∧ ([0, 7] : List Nat).all (· == 0) = false := by
  decide

/-! ## 2. FIPS 204 §5.2 message representative and domain separation -/

/-- `M' = 0x00 ‖ |ctx| ‖ ctx ‖ M` for pure ML-DSA (FIPS 204 Alg. 3 step 5). -/
def mprime (ctx m : List Nat) : List Nat := 0 :: ctx.length :: (ctx ++ m)

/-- **Context binding.** The representative determines `(ctx, M)` uniquely, so a
signature made under one context can never be replayed under another. -/
theorem mprime_injective (c1 m1 c2 m2 : List Nat)
    (h : mprime c1 m1 = mprime c2 m2) : c1 = c2 ∧ m1 = m2 := by
  unfold mprime at h
  injection h with _ h
  injection h with hlen happ
  exact List.append_inj happ hlen

/-- The byte-level representative actually absorbed by the sponge: the context
length is stored in ONE byte, so `|ctx| ≤ 255` must be checked separately. -/
def mprimeByte (ctx m : List Nat) : List Nat := 0 :: (ctx.length % 256) :: (ctx ++ m)

/-- **The `|ctx| ≤ 255` gate is load-bearing.** Without it the byte-level
representative is provably ambiguous: an empty context with a 256-byte message
and a 256-byte context with an empty message produce the *same* `M'`, so one
signature would verify under two different `(ctx, M)` pairs. -/
theorem ctx_len_gate_is_load_bearing :
    mprimeByte [] (List.replicate 256 7) = mprimeByte (List.replicate 256 7) []
    ∧ ((([] : List Nat), List.replicate 256 (7 : Nat)) ≠
       (List.replicate 256 (7 : Nat), ([] : List Nat))) := by
  constructor
  · unfold mprimeByte
    simp only [List.length_nil, List.length_replicate, List.nil_append, List.append_nil]
  · intro h
    have h1 : ([] : List Nat) = List.replicate 256 (7 : Nat) := congrArg Prod.fst h
    have h2 := congrArg List.length h1
    simp only [List.length_nil, List.length_replicate] at h2
    exact absurd h2 (by decide)

/-- **Pure vs HashML-DSA separation.** FIPS 204 uses domain byte `0x00` for
ML-DSA and `0x01` for HashML-DSA, so the two representative sets are disjoint and
a HashML-DSA signature can never verify as pure ML-DSA. -/
theorem pure_prehash_disjoint (c1 m1 c2 m2 : List Nat) :
    mprime c1 m1 ≠ 1 :: c2.length :: (c2 ++ m2) := by
  intro h
  unfold mprime at h
  injection h with h0
  exact absurd h0 (by decide)

end Encoding
end Mldsa
