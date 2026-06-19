/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV multi-piece sign coherence: negation-stable refinements still reduce to signs

This file records a small axiom-clean constraint lemma for Shaw's door-(iv) localized coherence
object.  The raw index-2 split was already shown sign-degenerate in
`_DoorIVCosetHalfCoherence`: when the two half-period sums are real and have the same sign, the
coherence is exactly `1`.

The same obstruction is not special to two pieces.  Any refinement whose pieces are individually
negation-stable has real period sums, and if those real pieces all have one sign then the normalized
multi-piece coherence

`|∑ᵢ Aᵢ| / ∑ᵢ |Aᵢ|`

is exactly `1`.  Thus a door-(iv) anti-concentration theorem cannot get a nontrivial upper bound
merely by subdividing into more negation-stable cosets and hoping for automatic phase spread: on
same-sign fibers the statistic again saturates.  The companion probe
`scripts/probes/probe_dooriv_multipiece_sign_coherence.py` checks this for index `4` and `8` coset
refinements in the thin prize regime.  This is only a constraint lemma, not CORE and not a moment or
completion bound.
-/

open scoped BigOperators

namespace ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

/-- Normalized coherence of finitely many real pieces. -/
noncomputable def multiPieceCoherence {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) : ℝ :=
  |∑ i ∈ s, A i| / (∑ i ∈ s, |A i|)

/-- If all real pieces are nonnegative and the total is nonzero, multi-piece coherence is exactly
`1`.  This is the positive-sign saturation obstruction for negation-stable door-(iv) refinements. -/
theorem multiPieceCoherence_eq_one_of_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hpos : 0 < ∑ i ∈ s, A i) :
    multiPieceCoherence s A = 1 := by
  unfold multiPieceCoherence
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, A i := Finset.sum_nonneg hA
  have hden : (∑ i ∈ s, |A i|) = ∑ i ∈ s, A i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonneg (hA i hi)
  rw [abs_of_nonneg hsum_nonneg, hden]
  exact div_self (ne_of_gt hpos)

/-- If all real pieces are nonpositive and the total is nonzero, multi-piece coherence is exactly
`1`.  This is the negative-sign saturation obstruction for negation-stable door-(iv) refinements. -/
theorem multiPieceCoherence_eq_one_of_nonpos {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ)
    (hA : ∀ i ∈ s, A i ≤ 0) (hneg : (∑ i ∈ s, A i) < 0) :
    multiPieceCoherence s A = 1 := by
  unfold multiPieceCoherence
  have hsum_nonpos : (∑ i ∈ s, A i) ≤ 0 := Finset.sum_nonpos hA
  have hden : (∑ i ∈ s, |A i|) = -(∑ i ∈ s, A i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_of_nonpos (hA i hi)
  rw [abs_of_nonpos hsum_nonpos, hden]
  exact div_self (ne_of_gt (neg_pos.mpr hneg))

/-- Compact same-sign formulation: if all real pieces have one sign and the total is nonzero, then
multi-piece coherence is exactly `1`. -/
theorem multiPieceCoherence_eq_one_of_sameSign {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ)
    (hsign : (∀ i ∈ s, 0 ≤ A i) ∨ (∀ i ∈ s, A i ≤ 0))
    (hsum : (∑ i ∈ s, A i) ≠ 0) :
    multiPieceCoherence s A = 1 := by
  rcases hsign with hnonneg | hnonpos
  · exact multiPieceCoherence_eq_one_of_nonneg s A hnonneg
      (lt_of_le_of_ne (Finset.sum_nonneg hnonneg) hsum.symm)
  · exact multiPieceCoherence_eq_one_of_nonpos s A hnonpos
      (lt_of_le_of_ne (Finset.sum_nonpos hnonpos) hsum)

/-! ## Signed-mass compression

For real, negation-stable refinements, subdividing the period into more pieces does not by itself
create a new phase statistic.  Once the pieces are real, the normalized multi-piece coherence is
controlled entirely by the imbalance between the aggregate positive `L¹` mass and the aggregate
negative `L¹` mass.  Thus a nontrivial coherence-slack theorem for a refined split must prove a real
signed-mass balance statement; it cannot come merely from the existence of many pieces.
-/

/-- If the total real sum is `posMass - negMass` and the total `L¹` mass is `posMass + negMass`,
then the multi-piece coherence compresses exactly to the signed-mass ratio
`|posMass - negMass| / (posMass + negMass)`.  This abstracts the door-(iv) obstruction: after a
negation-stable refinement has made every piece real, all phase information has collapsed to the two
numbers `posMass` and `negMass`. -/
theorem multiPieceCoherence_eq_abs_signedMass_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass) :
    multiPieceCoherence s A = |posMass - negMass| / (posMass + negMass) := by
  unfold multiPieceCoherence
  rw [hsum, hden]

/-- A coherence upper bound below `c` is exactly a signed-mass-balance demand: the absolute
positive/negative imbalance must be at most `c` times the total `L¹` mass.  This is the formal
constraint behind the probe verdict: to get slack from a multi-piece real refinement, one must prove
aggregate sign balance at the worst frequency, not merely refine the coset split. -/
theorem abs_signedMass_le_of_multiPieceCoherence_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hpos : 0 < posMass + negMass)
    (hle : multiPieceCoherence s A ≤ c) :
    |posMass - negMass| ≤ c * (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden] at hle
  exact (div_le_iff₀ hpos).mp hle

/-- Conversely, a signed-mass-balance inequality is precisely a coherence bound for the refined
real pieces.  The door-(iv) multi-piece route is therefore equivalent to proving this balance at the
adversarial `b`; refinement alone supplies no cancellation. -/
theorem multiPieceCoherence_le_of_abs_signedMass_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass c : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hpos : 0 < posMass + negMass)
    (hbal : |posMass - negMass| ≤ c * (posMass + negMass)) :
    multiPieceCoherence s A ≤ c := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  exact (div_le_iff₀ hpos).mpr hbal

/-- If the positive mass is at least the negative mass, coherence is just the normalized excess
`(posMass - negMass)/(posMass + negMass)`. -/
theorem multiPieceCoherence_eq_posExcess_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hge : negMass ≤ posMass) :
    multiPieceCoherence s A = (posMass - negMass) / (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  rw [abs_of_nonneg (sub_nonneg.mpr hge)]

/-- If the negative mass is at least the positive mass, coherence is the opposite normalized excess
`(negMass - posMass)/(posMass + negMass)`. -/
theorem multiPieceCoherence_eq_negExcess_ratio {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hge : posMass ≤ negMass) :
    multiPieceCoherence s A = (negMass - posMass) / (posMass + negMass) := by
  rw [multiPieceCoherence_eq_abs_signedMass_ratio s A hsum hden]
  have hnonpos : posMass - negMass ≤ 0 := sub_nonpos.mpr hge
  rw [abs_of_nonpos hnonpos]
  ring

end ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

open ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

#print axioms multiPieceCoherence_eq_one_of_nonneg
#print axioms multiPieceCoherence_eq_one_of_nonpos
#print axioms multiPieceCoherence_eq_one_of_sameSign
#print axioms multiPieceCoherence_eq_abs_signedMass_ratio
#print axioms abs_signedMass_le_of_multiPieceCoherence_le
#print axioms multiPieceCoherence_le_of_abs_signedMass_le
#print axioms multiPieceCoherence_eq_posExcess_ratio
#print axioms multiPieceCoherence_eq_negExcess_ratio
