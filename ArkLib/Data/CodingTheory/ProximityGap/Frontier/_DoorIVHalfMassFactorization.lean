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
