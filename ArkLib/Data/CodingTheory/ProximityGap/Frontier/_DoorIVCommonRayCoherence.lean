/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Door IV common-ray coherence constraint

Door-(iv) coherence probes repeatedly split the monomial sum into pieces and then measure

`ρ = |Σ pieces| / Σ |pieces|`.

This file records the exact obstruction behind those saturating probes: if all pieces lie on one
closed complex ray (nonnegative real multiples of a fixed unit direction), then the triangle
inequality has **no slack** and `ρ = 1`.  Therefore any useful anti-concentration theorem for the
worst-frequency coset-half coherence must first prove genuine angular spread; mere subdivision into
more pieces cannot help while the pieces remain ray-collinear.

This is a constraint lemma only, not a CORE bound.
-/

namespace ProximityGap.Frontier.DoorIVCommonRayCoherence

/-- Coherence of a finite list of complex pieces: triangle-inequality saturation ratio. -/
noncomputable def complexPieceCoherence (zs : List ℂ) : ℝ :=
  ‖zs.sum‖ / (zs.map norm).sum

/-- Sum of complex pieces all lying on the same ray `u` factors as the real coefficient sum times
`u`. -/
theorem sum_commonRay (xs : List ℝ) (u : ℂ) :
    (xs.map fun x => (x : ℂ) * u).sum = (xs.sum : ℂ) * u := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      change (x : ℂ) * u + (xs.map fun x => (x : ℂ) * u).sum = ((x + xs.sum : ℝ) : ℂ) * u
      rw [ih]
      norm_num [add_mul]

/-- If `u` is a unit complex direction and the coefficients are nonnegative, then the sum of the
absolute values of the common-ray pieces is just the real coefficient sum. -/
theorem sum_abs_commonRay_of_unit_of_nonneg {xs : List ℝ} {u : ℂ}
    (hu : ‖u‖ = 1) (hxs : ∀ x ∈ xs, 0 ≤ x) :
    ((xs.map fun x => (x : ℂ) * u).map norm).sum = xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hxs x (by simp)
      have htail : ∀ y ∈ xs, 0 ≤ y := by
        intro y hy
        exact hxs y (by simp [hy])
      change ‖(x : ℂ) * u‖ + ((xs.map fun x => (x : ℂ) * u).map norm).sum = x + xs.sum
      rw [Complex.norm_mul, Complex.norm_real, hu, mul_one, Real.norm_of_nonneg hx, ih htail]

/-- Any nonzero list of nonnegative pieces on a fixed unit complex ray has coherence exactly `1`.
This is the complex common-ray version of the real same-sign obstruction: triangle-inequality
saturation gives no door-(iv) anti-concentration slack. -/
theorem complexPieceCoherence_eq_one_of_commonRay_nonneg {xs : List ℝ} {u : ℂ}
    (hu : ‖u‖ = 1) (hxs : ∀ x ∈ xs, 0 ≤ x) (hsum : 0 < xs.sum) :
    complexPieceCoherence (xs.map fun x => (x : ℂ) * u) = 1 := by
  unfold complexPieceCoherence
  rw [sum_abs_commonRay_of_unit_of_nonneg hu hxs, sum_commonRay]
  have habs_sum : ‖(xs.sum : ℂ) * u‖ = xs.sum := by
    rw [Complex.norm_mul, hu, mul_one]
    exact Complex.norm_of_nonneg (le_of_lt hsum)
  rw [habs_sum]
  exact div_self (ne_of_gt hsum)

end ProximityGap.Frontier.DoorIVCommonRayCoherence

#print axioms ProximityGap.Frontier.DoorIVCommonRayCoherence.sum_commonRay
#print axioms ProximityGap.Frontier.DoorIVCommonRayCoherence.sum_abs_commonRay_of_unit_of_nonneg
#print axioms
  ProximityGap.Frontier.DoorIVCommonRayCoherence.complexPieceCoherence_eq_one_of_commonRay_nonneg
