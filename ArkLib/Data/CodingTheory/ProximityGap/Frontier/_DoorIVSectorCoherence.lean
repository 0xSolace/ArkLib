/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Door IV sector-coherence constraint

Door-(iv) asks for a non-moment anti-concentration theorem for the worst-frequency phase pieces of
`Σ_y e_p (b * y^m)`.  Recent common-ray bricks show exact saturation when all pieces lie on one ray.
This file records the quantitative next obstruction: a whole sector around one ray still prevents a
strict coherence drop.  If every piece has projection at least `c` times its norm along a fixed unit
complex direction, then the normalized coherence is at least `c`.

Consequently, any claimed door-(iv) estimate `ρ ≤ θ` must prove that the worst-frequency pieces are
not merely non-collinear, but leave every sector with projection floor `> θ`.  This is only a
constraint lemma; it is not a CORE bound.
-/

namespace ProximityGap.Frontier.DoorIVSectorCoherence

/-- Coherence of a finite list of complex pieces: triangle-inequality saturation ratio. -/
noncomputable def complexPieceCoherence (zs : List ℂ) : ℝ :=
  ‖zs.sum‖ / (zs.map norm).sum

/-- The real projection of a complex number onto the unit direction `u`.  We use `conj u * z` so
that the ray `z = t * u`, `t ≥ 0`, has projection `t`. -/
noncomputable def rayProj (u z : ℂ) : ℝ :=
  (starRingEnd ℂ u * z).re

/-- Projection is additive. -/
theorem rayProj_add (u z w : ℂ) : rayProj u (z + w) = rayProj u z + rayProj u w := by
  simp [rayProj, mul_add]

/-- Projection is additive over a finite list. -/
theorem rayProj_list_sum (u : ℂ) (zs : List ℂ) :
    rayProj u zs.sum = (zs.map (rayProj u)).sum := by
  induction zs with
  | nil => simp [rayProj]
  | cons z zs ih =>
      simp [rayProj_add, ih]

/-- A unit-direction projection is bounded above by the norm. -/
theorem rayProj_le_norm_of_unit {u z : ℂ} (hu : ‖u‖ = 1) : rayProj u z ≤ ‖z‖ := by
  unfold rayProj
  calc
    (starRingEnd ℂ u * z).re ≤ ‖starRingEnd ℂ u * z‖ := Complex.re_le_norm _
    _ = ‖z‖ := by
      rw [Complex.norm_mul, Complex.norm_conj, hu, one_mul]

/-- If all pieces have projection at least `c` times their norm along one unit ray, then the total
projection has the same lower bound. -/
theorem sector_projection_sum_lower {zs : List ℂ} {u : ℂ} {c : ℝ}
    (hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z) :
    c * (zs.map norm).sum ≤ rayProj u zs.sum := by
  rw [rayProj_list_sum]
  induction zs with
  | nil => simp
  | cons z zs ih =>
      have hz : c * ‖z‖ ≤ rayProj u z := hproj z (by simp)
      have htail : ∀ y ∈ zs, c * ‖y‖ ≤ rayProj u y := by
        intro y hy
        exact hproj y (by simp [hy])
      change c * (‖z‖ + (zs.map norm).sum) ≤ rayProj u z + (zs.map (rayProj u)).sum
      rw [mul_add]
      exact add_le_add hz (ih htail)

/-- **Sector coherence lower bound.**  A list contained in a sector with projection floor `c` along
some unit direction has normalized coherence at least `c` (provided the denominator is positive).
Thus a strict door-(iv) drop must prove genuine angular escape from every such sector. -/
theorem sector_floor_le_complexPieceCoherence {zs : List ℂ} {u : ℂ} {c : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z) :
    c ≤ complexPieceCoherence zs := by
  unfold complexPieceCoherence
  have hsum : c * (zs.map norm).sum ≤ rayProj u zs.sum :=
    sector_projection_sum_lower (zs := zs) (u := u) (c := c) hproj
  have hnorm : rayProj u zs.sum ≤ ‖zs.sum‖ := rayProj_le_norm_of_unit hu
  have hmul : c * (zs.map norm).sum ≤ ‖zs.sum‖ := le_trans hsum hnorm
  have hdiv := (le_div_iff₀ hden).2 hmul
  simpa [mul_comm] using hdiv

/-- Epsilon/threshold packaging: if the sector floor `c` is above a target `θ`, then the coherence
cannot be bounded by `θ`. -/
theorem not_complexPieceCoherence_le_of_sector_floor {zs : List ℂ} {u : ℂ} {c θ : ℝ}
    (hu : ‖u‖ = 1) (hden : 0 < (zs.map norm).sum)
    (hproj : ∀ z ∈ zs, c * ‖z‖ ≤ rayProj u z) (hθ : θ < c) :
    ¬ complexPieceCoherence zs ≤ θ := by
  intro hcoh
  have hfloor : c ≤ complexPieceCoherence zs :=
    sector_floor_le_complexPieceCoherence (zs := zs) (u := u) (c := c) hu hden hproj
  linarith

end ProximityGap.Frontier.DoorIVSectorCoherence

#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.rayProj_list_sum
#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.rayProj_le_norm_of_unit
#print axioms ProximityGap.Frontier.DoorIVSectorCoherence.sector_projection_sum_lower
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.sector_floor_le_complexPieceCoherence
#print axioms
  ProximityGap.Frontier.DoorIVSectorCoherence.not_complexPieceCoherence_le_of_sector_floor
