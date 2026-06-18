/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# Door (iv): complex/two-vector coherence is exactly same-ray saturation

The half-coset and real-piece Door-IV files show that negation-stable refinements collapse to a
real sign-mass problem.  This file records the corresponding phase-sensitive constraint for any
strictly convex real normed space, in particular `ℂ`: a two-piece split has coherence one exactly
when the two vector pieces lie on the same nonnegative ray.  Therefore a genuine two-piece phase
anti-concentration theorem cannot merely subdivide the sum; it must prove non-collinearity (or
quantitative distance from same-ray alignment) for the adversarial pieces.

No Gauss-period cancellation is claimed here.  These are pure triangle-equality bookkeeping lemmas
for the localized Door-IV coherence object.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.DoorIVComplexRayCoherence

variable {E : Type*} [NormedAddCommGroup E]

/-- Two-piece norm coherence: the ratio between the norm of the combined vector and the sum of
piece norms.  For complex Gauss-period pieces this is the phase-alignment ratio of the split. -/
noncomputable def twoPieceNormCoherence (x y : E) : ℝ :=
  ‖x + y‖ / (‖x‖ + ‖y‖)

/-- The two-piece coherence is always at most one when the denominator is positive. -/
theorem twoPieceNormCoherence_le_one {x y : E} (hden : 0 < ‖x‖ + ‖y‖) :
    twoPieceNormCoherence x y ≤ 1 := by
  unfold twoPieceNormCoherence
  have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hdiv : ‖x + y‖ / (‖x‖ + ‖y‖) ≤ (‖x‖ + ‖y‖) / (‖x‖ + ‖y‖) :=
    div_le_div_of_nonneg_right htri (le_of_lt hden)
  simpa [div_self (ne_of_gt hden)] using hdiv

variable [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- Saturation of two-piece norm coherence is exactly triangle-equality saturation, hence the two
pieces lie on the same nonnegative ray.  This is the complex/phase analogue of the real same-sign
lemmas: a claimed `ρ = 1` alignment is precisely a same-ray statement, not a new cancellation bound. -/
theorem twoPieceNormCoherence_eq_one_iff_sameRay {x y : E} (hden : 0 < ‖x‖ + ‖y‖) :
    twoPieceNormCoherence x y = 1 ↔ SameRay ℝ x y := by
  constructor
  · intro h
    have hnorm : ‖x + y‖ = ‖x‖ + ‖y‖ := by
      have hmul := congrArg (fun t : ℝ => t * (‖x‖ + ‖y‖)) h
      unfold twoPieceNormCoherence at hmul
      simpa [div_mul_cancel₀ _ (ne_of_gt hden)] using hmul
    exact (sameRay_iff_norm_add (x := x) (y := y)).2 hnorm
  · intro h
    unfold twoPieceNormCoherence
    have hnorm : ‖x + y‖ = ‖x‖ + ‖y‖ :=
      (sameRay_iff_norm_add (x := x) (y := y)).1 h
    rw [hnorm, div_self (ne_of_gt hden)]

/-- Contrapositive form: any non-same-ray two-piece split has strict coherence slack.  Thus a
useful Door-IV two-piece anti-concentration lemma must prove genuine phase non-collinearity for the
pieces; without that, triangle equality allows `ρ = 1`. -/
theorem twoPieceNormCoherence_lt_one_of_not_sameRay {x y : E} (hden : 0 < ‖x‖ + ‖y‖)
    (h : ¬ SameRay ℝ x y) :
    twoPieceNormCoherence x y < 1 := by
  unfold twoPieceNormCoherence
  have hlt : ‖x + y‖ < ‖x‖ + ‖y‖ :=
    (not_sameRay_iff_norm_add_lt (x := x) (y := y)).1 h
  have hdiv : ‖x + y‖ / (‖x‖ + ‖y‖) < (‖x‖ + ‖y‖) / (‖x‖ + ‖y‖) :=
    div_lt_div_of_pos_right hlt hden
  simpa [div_self (ne_of_gt hden)] using hdiv

/-- Threshold obstruction: any claimed two-piece coherence drop below a fixed `θ < 1` must first
rule out same-ray alignment of the pieces. -/
theorem not_sameRay_of_twoPieceNormCoherence_le {x y : E} {θ : ℝ} (hden : 0 < ‖x‖ + ‖y‖)
    (hθ : θ < 1) (hcoh : twoPieceNormCoherence x y ≤ θ) :
    ¬ SameRay ℝ x y := by
  intro hsame
  have hone : twoPieceNormCoherence x y = 1 :=
    (twoPieceNormCoherence_eq_one_iff_sameRay (x := x) (y := y) hden).2 hsame
  linarith

/-- Epsilon-drop obstruction: same-ray alignment forbids any positive `1 - ε` coherence bound. -/
theorem sameRay_not_twoPieceNormCoherence_le_one_sub {x y : E} {ε : ℝ}
    (hden : 0 < ‖x‖ + ‖y‖) (hε : 0 < ε) (hsame : SameRay ℝ x y) :
    ¬ twoPieceNormCoherence x y ≤ 1 - ε := by
  intro hcoh
  exact (not_sameRay_of_twoPieceNormCoherence_le (x := x) (y := y) (θ := 1 - ε) hden
    (sub_lt_self 1 hε) hcoh) hsame

end ProximityGap.Frontier.DoorIVComplexRayCoherence

#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_le_one
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_eq_one_iff_sameRay
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence_lt_one_of_not_sameRay
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.not_sameRay_of_twoPieceNormCoherence_le
#print axioms ProximityGap.Frontier.DoorIVComplexRayCoherence.sameRay_not_twoPieceNormCoherence_le_one_sub
