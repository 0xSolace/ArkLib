/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Door IV two-piece angular-deficit identity

The door-(iv) coherence files reduce the worst-frequency obstruction to bounding
`ρ = ‖A + B‖ / (‖A‖ + ‖B‖)` (two-piece coset-half / pair coherence).  `_DoorIVHalfMassFactorization`
records the `ρ ≤ 1` ceiling and the qualitative `ρ < 1 ⟺ ‖A+B‖ < ‖A‖+‖B‖`, and
`_DoorIVCommonRayCoherence` records that the common ray saturates (`ρ = 1`).  Neither states the
**exact** quantitative law linking the coherence deficit to the angular alignment `Re(A·conj B)`.

This file fills that gap for two complex pieces.  The key object is the **angular deficit**

`angularDeficit A B = ‖A‖·‖B‖ − Re(A·conj B) ≥ 0`,

which is `0` iff `A, B` are positively collinear (same ray) and grows with the angle between them.
The exact identity

`‖A + B‖² = (‖A‖ + ‖B‖)² − 2·angularDeficit A B`

shows the squared half-mass coherence loses *exactly* twice the angular deficit, and the
Cauchy–Schwarz nonnegativity `angularDeficit ≥ 0` is precisely the triangle inequality re-derived as
a phase-alignment statement.  Thus any anti-concentration slack `ρ < 1` in a two-piece split is
*exactly* a strictly positive angular deficit — genuine phase misalignment, not mere subdivision.

Constraint/identity lemmas only: no CORE / cancellation / completion / capacity / moment claim.
-/

namespace ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit

open Complex

/-- The angular deficit of two complex pieces: `‖A‖·‖B‖ − Re(A·conj B)`.  It is `≥ 0` by
Cauchy–Schwarz and vanishes exactly when `A, B` are positively collinear. -/
noncomputable def angularDeficit (A B : ℂ) : ℝ :=
  ‖A‖ * ‖B‖ - (A * starRingEnd ℂ B).re

/-- The real part of `A·conj B` is bounded by the product of norms (Cauchy–Schwarz for ℂ);
equivalently the angular deficit is nonnegative. -/
theorem re_mul_conj_le_norm_mul (A B : ℂ) : (A * starRingEnd ℂ B).re ≤ ‖A‖ * ‖B‖ := by
  calc (A * starRingEnd ℂ B).re ≤ ‖A * starRingEnd ℂ B‖ := Complex.re_le_norm _
    _ = ‖A‖ * ‖B‖ := by rw [Complex.norm_mul, Complex.norm_conj]

/-- The angular deficit is nonnegative. -/
theorem angularDeficit_nonneg (A B : ℂ) : 0 ≤ angularDeficit A B := by
  unfold angularDeficit
  linarith [re_mul_conj_le_norm_mul A B]

/-- The squared-norm expansion of a complex sum: `‖A+B‖² = ‖A‖² + ‖B‖² + 2·Re(A·conj B)`. -/
theorem norm_add_sq (A B : ℂ) :
    ‖A + B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * (A * starRingEnd ℂ B).re := by
  have hA : ‖A‖ ^ 2 = Complex.normSq A := (Complex.normSq_eq_norm_sq A).symm
  have hB : ‖B‖ ^ 2 = Complex.normSq B := (Complex.normSq_eq_norm_sq B).symm
  have hAB : ‖A + B‖ ^ 2 = Complex.normSq (A + B) := (Complex.normSq_eq_norm_sq (A + B)).symm
  rw [hA, hB, hAB, Complex.normSq_add]

/-- **Exact two-piece angular-deficit identity.**
`‖A + B‖² = (‖A‖ + ‖B‖)² − 2·angularDeficit A B`.

The squared half-mass coherence loses exactly twice the angular deficit.  Combined with
`angularDeficit_nonneg` this *is* the triangle inequality, now read as a phase-alignment statement:
the only loss in `‖A+B‖` vs the half-mass `‖A‖+‖B‖` is the angular misalignment of the two pieces. -/
theorem norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit (A B : ℂ) :
    ‖A + B‖ ^ 2 = (‖A‖ + ‖B‖) ^ 2 - 2 * angularDeficit A B := by
  rw [norm_add_sq, angularDeficit]
  ring

/-- A strict coherence deficit at the squared level (`‖A+B‖² < (‖A‖+‖B‖)²`) is equivalent to a
strictly positive angular deficit.  So two-piece anti-concentration slack is *exactly* genuine
angular misalignment. -/
theorem norm_add_sq_lt_halfMass_sq_iff_angularDeficit_pos (A B : ℂ) :
    ‖A + B‖ ^ 2 < (‖A‖ + ‖B‖) ^ 2 ↔ 0 < angularDeficit A B := by
  rw [norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Zero angular deficit forces saturation at the squared level (`‖A+B‖² = (‖A‖+‖B‖)²`).  This is
the two-piece common-ray saturation, matching `_DoorIVCommonRayCoherence`. -/
theorem norm_add_sq_eq_halfMass_sq_of_angularDeficit_zero {A B : ℂ}
    (h : angularDeficit A B = 0) : ‖A + B‖ ^ 2 = (‖A‖ + ‖B‖) ^ 2 := by
  rw [norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit, h]; ring

/-- Quantitative lower bound on the squared deficit from an angular-deficit floor: if
`angularDeficit A B ≥ δ` then `‖A+B‖² ≤ (‖A‖+‖B‖)² − 2δ`.  A two-piece coherence proof that
claims a drop must therefore exhibit at least the matching angular misalignment. -/
theorem norm_add_sq_le_halfMass_sq_sub_two_mul_of_angularDeficit_ge {A B : ℂ} {δ : ℝ}
    (h : δ ≤ angularDeficit A B) :
    ‖A + B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 - 2 * δ := by
  rw [norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit]
  linarith

end ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit

#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.re_mul_conj_le_norm_mul
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.angularDeficit_nonneg
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_lt_halfMass_sq_iff_angularDeficit_pos
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_eq_halfMass_sq_of_angularDeficit_zero
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_le_halfMass_sq_sub_two_mul_of_angularDeficit_ge
