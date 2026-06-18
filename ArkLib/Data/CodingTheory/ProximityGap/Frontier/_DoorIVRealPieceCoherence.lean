/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV real-piece coherence constraint

A repeated failure mode in the localized door-(iv) probes is that a proposed split of the monomial
sum uses pieces that are already forced onto the real line.  If the adversarial frequency makes
those real pieces share one sign, the normalized coherence

`|Σ A_i| / Σ |A_i|`

is exactly `1`.  This file records the general finite-list version of that constraint.  It is not a
CORE bound: it says that real, same-sign piece decompositions have no anti-concentration slack.
-/

namespace ProximityGap.Frontier.DoorIVRealPieceCoherence

/-- Coherence of a finite list of real pieces. -/
noncomputable def realPieceCoherence (xs : List ℝ) : ℝ := |xs.sum| / (xs.map abs).sum

/-- For a nonnegative list, the sum of absolute values is the ordinary sum. -/
theorem sum_abs_eq_sum_of_forall_nonneg {xs : List ℝ}
    (h : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map abs).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : 0 ≤ a := h a (by simp)
      have hxs : ∀ x ∈ xs, 0 ≤ x := by
        intro x hx
        exact h x (by simp [hx])
      simp [abs_of_nonneg ha, ih hxs]

/-- For a nonpositive list, the sum of absolute values is the negated ordinary sum. -/
theorem sum_abs_eq_neg_sum_of_forall_nonpos {xs : List ℝ}
    (h : ∀ x ∈ xs, x ≤ 0) :
    (xs.map abs).sum = -xs.sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : a ≤ 0 := h a (by simp)
      have hxs : ∀ x ∈ xs, x ≤ 0 := by
        intro x hx
        exact h x (by simp [hx])
      simp [abs_of_nonpos ha, ih hxs]
      ring

/-- Any nonzero nonnegative real-piece split has coherence exactly one. -/
theorem realPieceCoherence_eq_one_of_forall_nonneg {xs : List ℝ}
    (h : ∀ x ∈ xs, 0 ≤ x) (hsum : 0 < xs.sum) :
    realPieceCoherence xs = 1 := by
  unfold realPieceCoherence
  rw [sum_abs_eq_sum_of_forall_nonneg h, abs_of_nonneg (le_of_lt hsum)]
  exact div_self (ne_of_gt hsum)

/-- Any nonzero nonpositive real-piece split has coherence exactly one. -/
theorem realPieceCoherence_eq_one_of_forall_nonpos {xs : List ℝ}
    (h : ∀ x ∈ xs, x ≤ 0) (hsum : xs.sum < 0) :
    realPieceCoherence xs = 1 := by
  unfold realPieceCoherence
  rw [sum_abs_eq_neg_sum_of_forall_nonpos h, abs_of_nonpos (le_of_lt hsum)]
  exact div_self (ne_of_gt (neg_pos.mpr hsum))

#print axioms sum_abs_eq_sum_of_forall_nonneg
#print axioms sum_abs_eq_neg_sum_of_forall_nonpos
#print axioms realPieceCoherence_eq_one_of_forall_nonneg
#print axioms realPieceCoherence_eq_one_of_forall_nonpos

end ProximityGap.Frontier.DoorIVRealPieceCoherence
