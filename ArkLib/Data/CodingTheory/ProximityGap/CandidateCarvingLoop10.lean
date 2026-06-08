/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 10 — the exact carving of the prize at the Johnson threshold

The proof side (Loop9/P1, and the in-tree `Hab25Johnson` port of Haböck Thm 2) reaches the prize
bound for radius **below the Johnson radius** `1 − √ρ`; the disproof reduction (Loop8/O6′) shows the
only remaining disproof route lives **beyond** it. The two sides meet exactly at the gap value

    η₀ := √ρ − ρ          (the gap-to-capacity at which the radius `1−ρ−η` equals the Johnson radius)

This file makes that carving precise and proves both regions are genuinely non-empty (so neither
side is vacuous), turning the open prize into a single named real parameter: the **beyond-Johnson
depth** `ζ := η₀ − η`, which is *literally* how far the prize radius `1−ρ−η` exceeds the Johnson
radius `1−√ρ`. The entire open content of the prize is the regime `ζ > 0` (i.e. `0 < η ≤ η₀`).

All sorry-free and axiom-clean. See `DISPROOF_LOG.md` (carving synthesis).
-/

namespace ArkLib.ProximityGap.CarvingLoop10

open scoped Real

/-- The Johnson gap-threshold `η₀ = √ρ − ρ`. -/
noncomputable def johnsonGapThreshold (ρ : ℝ) : ℝ := Real.sqrt ρ - ρ

/-- **The beyond-Johnson depth is exactly the radius excess over the Johnson radius.** For any
`ρ, η`, the prize radius `1−ρ−η` exceeds the Johnson radius `1−√ρ` by precisely
`η₀ − η = (√ρ − ρ) − η`. So "how deep into the open band" and "how far below the Johnson gap" are the
same quantity. -/
theorem prize_radius_excess_eq_depth (ρ η : ℝ) :
    (1 - ρ - η) - (1 - Real.sqrt ρ) = johnsonGapThreshold ρ - η := by
  unfold johnsonGapThreshold; ring

/-- **Exact Johnson-threshold iff (boundary radius).** At the maximal prize radius `δ = 1−ρ−η`, the
radius is strictly below the Johnson radius iff the gap exceeds the Johnson threshold:

    1 − ρ − η < 1 − √ρ   ↔   η₀ < η. -/
theorem below_johnson_iff_large_gap (ρ η : ℝ) :
    (1 - ρ - η) < (1 - Real.sqrt ρ) ↔ johnsonGapThreshold ρ < η := by
  unfold johnsonGapThreshold; constructor <;> intro h <;> linarith

/-- **The Johnson threshold is strictly positive for every nondegenerate rate.** For `0 < ρ < 1`,
`η₀ = √ρ − ρ > 0`, so there genuinely is an open band `0 < η ≤ η₀` (the prize is not vacuously
closed by the proof side). -/
theorem johnsonGapThreshold_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    0 < johnsonGapThreshold ρ := by
  unfold johnsonGapThreshold
  have hslt1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt (le_of_lt hρ0) hρ1; rwa [Real.sqrt_one] at this
  have hspos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
  have hlt : ρ < Real.sqrt ρ := by
    have hs : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt (le_of_lt hρ0)
    nlinarith [hs, hspos, hslt1]
  linarith

/-- **The provable (large-gap) region is non-empty.** For `0 < ρ < 1` there is a gap `η` that is
both a *valid* prize gap (`0 < η` and the radius `1−ρ−η ≥ 0`, i.e. `η ≤ 1−ρ`) and *above* the
Johnson threshold — so Loop9/P1 closes a genuine slice of the parameter space. Concretely any
`η ∈ (η₀, 1−ρ]` works, and that interval is non-empty since `η₀ < 1 − ρ`. -/
theorem provable_region_nonempty {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    johnsonGapThreshold ρ < 1 - ρ := by
  unfold johnsonGapThreshold
  have hslt1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt (le_of_lt hρ0) hρ1; rwa [Real.sqrt_one] at this
  linarith

/-- **Carving dichotomy at the threshold.** For valid prize parameters with radius `δ = 1−ρ−η`,
exactly one of the two regimes holds: either `η₀ < η` (provable side — radius below Johnson) or
`η ≤ η₀` (open side — radius at/beyond Johnson, the beyond-Johnson depth `ζ = η₀ − η ≥ 0`). -/
theorem carving_dichotomy (ρ η : ℝ) :
    (johnsonGapThreshold ρ < η) ∨ (η ≤ johnsonGapThreshold ρ) :=
  lt_or_ge (johnsonGapThreshold ρ) η

end ArkLib.ProximityGap.CarvingLoop10
