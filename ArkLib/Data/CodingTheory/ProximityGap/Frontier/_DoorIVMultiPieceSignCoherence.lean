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

end ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

open ProximityGap.Frontier.DoorIVMultiPieceSignCoherence

#print axioms multiPieceCoherence_eq_one_of_nonneg
#print axioms multiPieceCoherence_eq_one_of_nonpos
#print axioms multiPieceCoherence_eq_one_of_sameSign
