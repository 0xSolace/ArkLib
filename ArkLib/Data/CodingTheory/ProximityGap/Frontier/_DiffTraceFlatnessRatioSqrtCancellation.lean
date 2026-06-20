/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceFlatnessRatioRange

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option autoImplicit false

/-!
# CAPSTONE — the exact square-root-cancellation normalization of the flatness ratio (#444)

`_DiffTraceFlatnessRatio` introduced the dimensionless Door-(iv) variance-core ratio

`ρ_flat(Rel) = ‖Σ_T Jphase θ T‖² / #Rel`.

`_DiffTraceFlatnessRatioRange` pinned its global range `[0,#Rel]` and both extremes.  This file records
one more citable normalization rung: the square-root-cancellation / diagonal-floor target is EXACTLY
`ρ_flat ≤ 1`, with no hidden constants and no slack.

For nonempty `Rel`, dividing by `#Rel` gives the no-slack dictionary

* `ρ_flat ≤ 1` iff `‖Σ_T Jphase θ T‖² ≤ #Rel`;
* `ρ_flat < 1` iff `‖Σ_T Jphase θ T‖² < #Rel`;
* `ρ_flat = 1` iff `‖Σ_T Jphase θ T‖² = #Rel`.

This does NOT prove the left side.  It only names the exact square-root-cancellation target in the
Shaw-value/flatness normalization, so downstream Door-(iv) reductions can cite the diagonal-floor
threshold directly instead of redoing the algebra.  No CORE / cancellation / completion / moment-saving /
capacity claim is made.  #444.
-/

namespace ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatio

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-- **`flatnessRatio_le_one_iff_normSq_le_card`** — the dimensionless square-root-cancellation target
`ρ_flat ≤ 1` is exactly the diagonal-floor norm-square budget `‖Σ Jphase‖² ≤ #Rel`. -/
theorem flatnessRatio_le_one_iff_normSq_le_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ 1
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_le_iff₀ hne]
  ring_nf

/-- **`flatnessRatio_lt_one_iff_normSq_lt_card`** — the strict sub-diagonal form of the same
normalization: `ρ_flat < 1` iff `‖Σ Jphase‖² < #Rel`. -/
theorem flatnessRatio_lt_one_iff_normSq_lt_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel < 1
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) < (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_lt_iff₀ hne]
  ring_nf

/-- **`flatnessRatio_eq_one_iff_normSq_eq_card`** — the exact diagonal-floor equality form:
`ρ_flat = 1` iff `‖Σ Jphase‖² = #Rel`. -/
theorem flatnessRatio_eq_one_iff_normSq_eq_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) :
    flatnessRatio θ Rel = 1
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) = (Rel.card : ℝ) := by
  unfold flatnessRatio
  rw [div_eq_iff (ne_of_gt hne)]
  ring_nf

/-- **`flatnessRatio_le_one_of_normSq_le_card`** — forward-facing consumer wrapper for certificates of
the diagonal-floor norm-square budget. -/
theorem flatnessRatio_le_one_of_normSq_le_card (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ))
    (h : Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ)) :
    flatnessRatio θ Rel ≤ 1 :=
  (flatnessRatio_le_one_iff_normSq_le_card Rel hne).2 h

/-- **`normSq_le_card_of_flatnessRatio_le_one`** — reverse-facing consumer wrapper: any proof of
`ρ_flat ≤ 1` has proved the diagonal-floor aggregate norm-square budget. -/
theorem normSq_le_card_of_flatnessRatio_le_one (Rel : Finset (Fin r → R))
    (hne : 0 < (Rel.card : ℝ)) (h : flatnessRatio θ Rel ≤ 1) :
    Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) :=
  (flatnessRatio_le_one_iff_normSq_le_card Rel hne).1 h

end ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_le_one_iff_normSq_le_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_lt_one_iff_normSq_lt_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_eq_one_iff_normSq_eq_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.flatnessRatio_le_one_of_normSq_le_card
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceFlatnessRatioSqrtCancellation.normSq_le_card_of_flatnessRatio_le_one
