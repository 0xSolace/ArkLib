/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv): the prize size factors as coherence times half-mass (#444)

Split `η_b = Σ_{y∈μ_n} e_p(b·y)` along the index-2 subgroup `μ_{n/2} < μ_n` into its two coset-half
sums `A, B` (so `η_b = A + B`).  The index-2 coset-half coherence is, by definition,
`ρ(b) = ‖A+B‖ / (‖A‖+‖B‖)` (the half-mass `L¹` is `‖A‖+‖B‖`).  This file records the exact
factorization and its consequence.

* `norm_eq_coherence_mul_halfMass`: `‖A+B‖ = coherence A B · (‖A‖+‖B‖)` — the prize size is exactly
  **coherence × half-mass** (a definitional identity, confirmed to machine precision by
  `probe_dooriv_halfmass_factorization.py`, residual `~1e-16`).
* `norm_eq_halfMass_of_coherence_one`: when coherence is `1` (the probed + separately-proven fact at
  the prize-worst frequency `b*`), `‖A+B‖ = ‖A‖+‖B‖`: the peak is the **full, undamped half-mass**.
* `prize_localizes_onto_halfMass`: combining the two, at a full-coherence frequency the period norm
  equals the half-mass `L¹`.  Together with `_DoorIVCoherenceSlackVacuousAtArgmax` (coherence is
  pinned at `1` at `b*`), the entire prize burden provably **relocates onto the half-mass `‖A‖+‖B‖`** —
  no escape: the probe shows `max_b (‖A‖+‖B‖)/√n ≈ max_b ‖η_b‖/√n` (the half-mass carries the same
  `√(n·log)` burden), it does not shrink the wall.

Scope: definitional norm algebra over a normed field.  No CORE/cancellation/capacity claim — this is a
faithful **reformulation** of where the open burden sits, in the spirit of the campaign meta-theorem.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The half-mass `L¹` of the two coset-half sums: `‖A‖ + ‖B‖`. -/
def halfMass (A B : E) : ℝ := ‖A‖ + ‖B‖

/-- The index-2 coset-half coherence `ρ = ‖A+B‖ / (‖A‖+‖B‖)`. -/
noncomputable def coherence (A B : E) : ℝ := ‖A + B‖ / halfMass A B

/-- Half-mass is nonnegative. -/
theorem halfMass_nonneg (A B : E) : 0 ≤ halfMass A B := by
  unfold halfMass; positivity

/-- **Prize size = coherence × half-mass.**  Whenever the half-mass is positive, the period norm
factors exactly as the coherence times the half-mass.  This is the definitional identity behind
"the prize is coherence times half-mass". -/
theorem norm_eq_coherence_mul_halfMass {A B : E} (h : 0 < halfMass A B) :
    ‖A + B‖ = coherence A B * halfMass A B := by
  unfold coherence
  field_simp

/-- **Full coherence ⇒ peak is the full half-mass.**  If coherence is `1` (the probed + proven fact at
the prize-worst frequency), the period norm equals the half-mass `L¹`: the peak is undamped. -/
theorem norm_eq_halfMass_of_coherence_one {A B : E} (h : 0 < halfMass A B)
    (hcoh : coherence A B = 1) :
    ‖A + B‖ = halfMass A B := by
  rw [norm_eq_coherence_mul_halfMass h, hcoh, one_mul]

/-- **Prize localizes onto the half-mass.**  Restated: at any full-coherence frequency the entire
period norm is carried by the half-mass `‖A‖+‖B‖`.  With coherence pinned at `1` at `b*`
(`_DoorIVCoherenceSlackVacuousAtArgmax`), the prize burden sits entirely on the half-mass `L¹`. -/
theorem prize_localizes_onto_halfMass {A B : E} (h : 0 < halfMass A B)
    (hcoh : coherence A B = 1) :
    ‖A + B‖ = ‖A‖ + ‖B‖ :=
  norm_eq_halfMass_of_coherence_one h hcoh

/-- The triangle inequality in this normalization: coherence never exceeds `1`, so the period norm is
always at most the half-mass.  (Hence full coherence is the extreme case, and the half-mass is a genuine
upper envelope for the period.) -/
theorem norm_le_halfMass (A B : E) : ‖A + B‖ ≤ halfMass A B :=
  norm_add_le A B

/-- Coherence is nonnegative, since it is a norm divided by a nonnegative half-mass. -/
theorem coherence_nonneg (A B : E) : 0 ≤ coherence A B := by
  unfold coherence
  exact div_nonneg (norm_nonneg _) (halfMass_nonneg A B)

/-- If the half-mass is positive, coherence is at most `1`.  Thus a door-(iv) coherence lever has no
room above the triangle-inequality envelope; it can only try to prove quantitative slack below `1`. -/
theorem coherence_le_one_of_halfMass_pos {A B : E} (h : 0 < halfMass A B) :
    coherence A B ≤ 1 := by
  unfold coherence
  rw [div_le_iff₀ h]
  simpa [one_mul] using norm_le_halfMass A B

/-- At positive half-mass, full coherence is equivalent to equality in the half-mass envelope.  This
packages the exact obstruction: proving `coherence < 1` is exactly proving strict loss in
`‖A+B‖ ≤ ‖A‖+‖B‖`, while at the prize-worst coherent frequency there is no such loss. -/
theorem coherence_eq_one_iff_norm_eq_halfMass {A B : E} (h : 0 < halfMass A B) :
    coherence A B = 1 ↔ ‖A + B‖ = halfMass A B := by
  constructor
  · exact norm_eq_halfMass_of_coherence_one h
  · intro heq
    unfold coherence
    rw [heq, div_self (ne_of_gt h)]

/-- At positive half-mass, a strict coherence drop is exactly strict loss in the triangle-inequality
half-mass envelope.  Thus a door-(iv) split does not gain anything from the act of splitting alone:
it must prove genuine strict triangle slack for the adversarial pieces. -/
theorem coherence_lt_one_iff_norm_lt_halfMass {A B : E} (h : 0 < halfMass A B) :
    coherence A B < 1 ↔ ‖A + B‖ < halfMass A B := by
  unfold coherence
  rw [div_lt_iff₀ h]
  simp

/-- If the period norm already saturates the half-mass envelope, there is no strict coherence drop. -/
theorem not_coherence_lt_one_of_norm_eq_halfMass {A B : E} (h : 0 < halfMass A B)
    (heq : ‖A + B‖ = halfMass A B) :
    ¬ coherence A B < 1 := by
  rw [coherence_lt_one_iff_norm_lt_halfMass h, heq]
  exact not_lt_of_ge le_rfl

/-- **Coherence floor times half-mass floor gives a period floor.**  In the split formulation, any
lower bound on the coherence and any lower bound on the half-mass transfer multiplicatively to a lower
bound on the original period norm.  This is only bookkeeping: it says a successful half-split route must
pay both factors, not that either factor has been bounded in the prize regime. -/
theorem norm_ge_of_coherence_ge_of_halfMass_ge {A B : E} {rho H : ℝ}
    (h : 0 < halfMass A B) (hrho0 : 0 ≤ rho) (hH0 : 0 ≤ H)
    (hcoh : rho ≤ coherence A B) (hmass : H ≤ halfMass A B) :
    rho * H ≤ ‖A + B‖ := by
  rw [norm_eq_coherence_mul_halfMass h]
  have hcoh0 : 0 ≤ coherence A B := le_trans hrho0 hcoh
  exact mul_le_mul hcoh hmass hH0 hcoh0

/-- **Upper-bound transfer through the split.**  Conversely, an upper bound on coherence and an upper
bound on half-mass transfer multiplicatively to an upper bound on the original period norm.  This names
exactly what a successful coset-half route must prove: either a genuine coherence drop or a genuine
half-mass upper bound (or both).  The algebra itself supplies no saving. -/
theorem norm_le_of_coherence_le_of_halfMass_le {A B : E} {rho H : ℝ}
    (h : 0 < halfMass A B) (hrho0 : 0 ≤ rho)
    (hcoh : coherence A B ≤ rho) (hmass : halfMass A B ≤ H) :
    ‖A + B‖ ≤ rho * H := by
  rw [norm_eq_coherence_mul_halfMass h]
  have hmass0 : 0 ≤ halfMass A B := halfMass_nonneg A B
  exact mul_le_mul hcoh hmass hmass0 hrho0

/-- **A norm floor plus a half-mass ceiling forces a coherence floor.**  This is the converse-facing
budget identity to `halfMass_ge_normFloor_div_of_coherence_le`: if the original period has floor `T`
and the two half-sums have total `L¹` at most `H`, then the coset-half coherence itself must be at least
`T / H`.  Therefore a Door-IV coherence-saving claim is only compatible with an independent half-mass
ceiling when the product `rho * H` still covers the observed norm floor. -/
theorem coherence_ge_normFloor_div_of_halfMass_le {A B : E} {T H : ℝ}
    (h : 0 < halfMass A B) (hH : 0 < H)
    (hT : T ≤ ‖A + B‖) (hmass : halfMass A B ≤ H) :
    T / H ≤ coherence A B := by
  rw [div_le_iff₀ hH]
  calc
    T ≤ ‖A + B‖ := hT
    _ = coherence A B * halfMass A B := norm_eq_coherence_mul_halfMass h
    _ ≤ coherence A B * H := by
      exact mul_le_mul_of_nonneg_left hmass (coherence_nonneg A B)

/-- **Product-budget obstruction.**  If a proposed coherence cap `rho` and half-mass cap `H` have product
strictly below the known period floor `T`, then the coherence cap is impossible.  The split algebra alone
cannot beat the floor: any advertised `rho < 1` must be paired with enough half-mass budget that
`rho * H` still reaches `T`, or else it contradicts the exact factorization. -/
theorem not_coherence_le_of_normFloor_gt_product {A B : E} {T rho H : ℝ}
    (h : 0 < halfMass A B) (hrho0 : 0 ≤ rho)
    (hcohMass : halfMass A B ≤ H) (hT : T ≤ ‖A + B‖) (hprod : rho * H < T) :
    ¬ coherence A B ≤ rho := by
  intro hcoh
  have hnorm : ‖A + B‖ ≤ rho * H :=
    norm_le_of_coherence_le_of_halfMass_le h hrho0 hcoh hcohMass
  have hle : T ≤ rho * H := le_trans hT hnorm
  exact (not_lt_of_ge hle) hprod

/-- **Coherence drop forces reciprocal half-mass spend.**  If the split has coherence at most
`rho > 0` while the original period norm is at least `T`, then the half-mass must be at least
`T / rho`.  Thus a door-(iv) proof cannot get a saving merely by proving `rho < 1`: any coherence
saving has to be paid for by a correspondingly larger `L¹` half-mass budget unless it also proves an
independent half-mass upper bound. -/
theorem halfMass_ge_normFloor_div_of_coherence_le {A B : E} {T rho : ℝ}
    (h : 0 < halfMass A B) (hrho : 0 < rho)
    (hcoh : coherence A B ≤ rho) (hT : T ≤ ‖A + B‖) :
    T / rho ≤ halfMass A B := by
  rw [div_le_iff₀ hrho]
  calc
    T ≤ ‖A + B‖ := hT
    _ = coherence A B * halfMass A B := norm_eq_coherence_mul_halfMass h
    _ ≤ halfMass A B * rho := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hcoh (halfMass_nonneg A B)

/-- Fixed-drop specialization of the reciprocal-spend obstruction: a certificate
`coherence ≤ 1 - ε` only converts a norm floor `T` into the half-mass floor `T/(1-ε)`.  For small or
constant `ε`, this is only a constant-factor relocation of the original prize burden onto half-mass,
not a square-root cancellation theorem. -/
theorem halfMass_ge_normFloor_div_one_sub_of_coherence_drop {A B : E} {T ε : ℝ}
    (h : 0 < halfMass A B) (hε : 0 < 1 - ε)
    (hcoh : coherence A B ≤ 1 - ε) (hT : T ≤ ‖A + B‖) :
    T / (1 - ε) ≤ halfMass A B :=
  halfMass_ge_normFloor_div_of_coherence_le h hε hcoh hT

/-- If the half-mass envelope is zero, the original period norm is zero too.  Thus any nonzero period
certificate must live in the positive-half-mass branch where the coherence factorization is meaningful;
the zero branch cannot hide a prize-sized peak. -/
theorem norm_eq_zero_of_halfMass_eq_zero {A B : E} (h : halfMass A B = 0) : ‖A + B‖ = 0 := by
  have hle : ‖A + B‖ ≤ 0 := by simpa [h] using norm_le_halfMass A B
  exact le_antisymm hle (norm_nonneg _)

/-- Under zero half-mass, Lean's totalized division gives coherence `0` (the numerator is already zero).
This records that the split has no separate zero-denominator escape hatch. -/
theorem coherence_eq_zero_of_halfMass_eq_zero {A B : E} (h : halfMass A B = 0) :
    coherence A B = 0 := by
  unfold coherence
  rw [h, norm_eq_zero_of_halfMass_eq_zero h, zero_div]

/-- Contrapositive form: a nonzero original period forces positive half-mass.  This is the anti-vacuity
branch guard for any coset-half coherence certificate. -/
theorem halfMass_pos_of_norm_pos {A B : E} (h : 0 < ‖A + B‖) : 0 < halfMass A B := by
  exact lt_of_lt_of_le h (norm_le_halfMass A B)

end ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization

#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass_nonneg
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.norm_eq_coherence_mul_halfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.norm_eq_halfMass_of_coherence_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.prize_localizes_onto_halfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.norm_le_halfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_nonneg
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_le_one_of_halfMass_pos
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_eq_one_iff_norm_eq_halfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_lt_one_iff_norm_lt_halfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.not_coherence_lt_one_of_norm_eq_halfMass
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.norm_ge_of_coherence_ge_of_halfMass_ge
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.norm_le_of_coherence_le_of_halfMass_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_ge_normFloor_div_of_halfMass_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.not_coherence_le_of_normFloor_gt_product
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass_ge_normFloor_div_of_coherence_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass_ge_normFloor_div_one_sub_of_coherence_drop
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.norm_eq_zero_of_halfMass_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.coherence_eq_zero_of_halfMass_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassFactorization.halfMass_pos_of_norm_pos
