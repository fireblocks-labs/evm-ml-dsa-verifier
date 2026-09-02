/-
# Audit hooks

Building this file prints the axiom dependencies of every headline theorem.
A trustworthy result shows only `propext`, `Quot.sound`, `Classical.choice`
(Lean's own three axioms). In particular `sorryAx` must NOT appear: its presence
is how an incomplete proof would show up.

`check_axioms.py` pins the set of audited names and their statement digests and
fails if any directive below is removed or reports an unexpected axiom.
-/

import Mldsa.Barrett
import Mldsa.Decode
import Mldsa.Encoding

-- The TWO-STEP Barrett kernel under exact EVM 256-bit semantics.  These are the
-- obligations that TIME OUT at the bytecode level under halmos 0.3.3 with
-- every solver available; see Mldsa/Barrett.lean's header.  The packed
-- statements are now about the FOUR 64-bit lanes of one word directly: the
-- spread-to-128-bit-spacing intermediate the previous kernel needed is gone,
-- so `spread_lane_independent` has no subject any more and its role is taken by
-- `lane_product_lt_two_pow_63` (why no spreading is needed) together with
-- `swar_step1_lane_independent` / `swar_lane_independent` (that none happens).
#print axioms Mldsa.Barrett.mu_is_floor
#print axioms Mldsa.Barrett.mu_q_add_d
#print axioms Mldsa.Barrett.unit_step_is_floor
#print axioms Mldsa.Barrett.q_sparse_form
#print axioms Mldsa.Barrett.no_borrow
#print axioms Mldsa.Barrett.second_no_borrow
#print axioms Mldsa.Barrett.barrettNat_lt_two_q
#print axioms Mldsa.Barrett.step1_lt_two_pow_33
#print axioms Mldsa.Barrett.barrettEVM_eq_nat
#print axioms Mldsa.Barrett.barrettEVM_lt_two_q
#print axioms Mldsa.Barrett.barrettNat_congr
#print axioms Mldsa.Barrett.lane_product_lt_two_pow_63
#print axioms Mldsa.Barrett.qhat_lt_two_pow_31
#print axioms Mldsa.Barrett.barrett_forward
#print axioms Mldsa.Barrett.barrett_inverse
#print axioms Mldsa.Barrett.barrett_inverse_congr
#print axioms Mldsa.Barrett.firstFail_breaks
#print axioms Mldsa.Barrett.firstFail_pred_ok
#print axioms Mldsa.Barrett.invMax_lt_firstFail
#print axioms Mldsa.Barrett.margin_guard
#print axioms Mldsa.Barrett.margin_guard_hmg
#print axioms Mldsa.Barrett.lane_cliff_above_firstFail
#print axioms Mldsa.Barrett.lane_cliff_breaks
#print axioms Mldsa.Barrett.step1_alone_is_not_enough
#print axioms Mldsa.Barrett.swar_step1_lane_independent
#print axioms Mldsa.Barrett.swar_lane_independent
#print axioms Mldsa.Barrett.swar_lane_fits

-- The packed z DECODER under the same exact semantics: the canonicalisation
-- (one conditional subtraction, taken at `u >= q` so the z = 0 field becomes 0),
-- the two window edges as single carry bits, the equivalence with the STRICT
-- FIPS 204 norm test, its boundary on BOTH tails in BOTH directions, and the
-- four-lane independence of the word the kernel actually forms.
#print axioms Mldsa.Decode.u_bounds
#print axioms Mldsa.Decode.u_lt_two_q
#print axioms Mldsa.Decode.flag_no_carry
#print axioms Mldsa.Decode.flag_is_a_bit
#print axioms Mldsa.Decode.flag_iff_u_ge_q
#print axioms Mldsa.Decode.canon_lt_q
#print axioms Mldsa.Decode.canon_closed_form
#print axioms Mldsa.Decode.canon_zero_field
#print axioms Mldsa.Decode.lo_no_carry
#print axioms Mldsa.Decode.hi_no_borrow
#print axioms Mldsa.Decode.lo_iff
#print axioms Mldsa.Decode.hi_iff
#print axioms Mldsa.Decode.reject_iff_fips
#print axioms Mldsa.Decode.boundary_low_rejected
#print axioms Mldsa.Decode.boundary_low_inside_accepted
#print axioms Mldsa.Decode.boundary_high_rejected
#print axioms Mldsa.Decode.boundary_high_inside_accepted
#print axioms Mldsa.Decode.addSplit4
#print axioms Mldsa.Decode.subFromRep4
#print axioms Mldsa.Decode.swar_z_lane_independent
#print axioms Mldsa.Decode.flag_word_lane_fits
#print axioms Mldsa.Decode.fused_split
#print axioms Mldsa.Decode.fused_disjoint
#print axioms Mldsa.Decode.zp2_is_two_powers
#print axioms Mldsa.Decode.zp4_is_two_powers
#print axioms Mldsa.Decode.zp6_is_two_powers

-- Encoding layer: FIPS 204 Algorithm 21 hint canonicality / injectivity, and
-- the §5.2 message representative (context binding, domain separation).
#print axioms Mldsa.Encoding.all_zero_replicate
#print axioms Mldsa.Encoding.decRows_canonical
#print axioms Mldsa.Encoding.hint_decode_canonical
#print axioms Mldsa.Encoding.hint_decode_injective
#print axioms Mldsa.Encoding.hint_weight_le_omega
#print axioms Mldsa.Encoding.strictInc_rejects_permutation
#print axioms Mldsa.Encoding.strictInc_rejects_repeat
#print axioms Mldsa.Encoding.padding_gate_rejects_nonzero
#print axioms Mldsa.Encoding.mprime_injective
#print axioms Mldsa.Encoding.ctx_len_gate_is_load_bearing
#print axioms Mldsa.Encoding.pure_prehash_disjoint
