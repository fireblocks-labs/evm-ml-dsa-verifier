/-
# Machine-checked kernels for the ML-DSA-44 (FIPS 204) EVM verifier

* `Mldsa.Barrett` — the lazy Barrett reduction and its SWAR (packed-lane)
  forms, proved under exact EVM 256-bit word semantics: the `< 2q` lazy bound,
  congruence mod `q`, the necessity of the input-domain restriction, and
  cross-lane independence of the 2-lane and 4-lane packed reductions.  These
  back the NTT lane-bound analysis.
* `Mldsa.Decode` — the packed z decoder: the single conditional subtraction is
  reduction mod `q` (including at the `z = 0` field, which must become 0 and not
  `q`), each of the two window edges is one carry bit, their conjunction is
  exactly the STRICT FIPS 204 norm rejection with both boundaries inside it, and
  the packed word is four independent copies of all of that.
* `Mldsa.Encoding` — FIPS 204 encoding-layer canonicality: Algorithm 21
  `HintBitUnpack` accepts at most one byte encoding per hint set (no
  malleability), and the §5.2 message representative `M'` binds `(ctx, M)`
  and separates pure ML-DSA from HashML-DSA.
* `Mldsa.Audit` — `#print axioms` for every headline theorem; the axiom base
  is checked by `check_axioms.py`.

Lean core only — no mathlib, no `sorry`, no axioms beyond Lean's own
(`propext`, `Quot.sound`, `Classical.choice`).
-/
import Mldsa.Barrett
import Mldsa.Decode
import Mldsa.Encoding
import Mldsa.Audit
