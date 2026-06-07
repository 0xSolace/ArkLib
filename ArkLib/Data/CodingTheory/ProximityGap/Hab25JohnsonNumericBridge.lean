/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson
import ArkLib.Data.CodingTheory.ProximityGap.Hab25MultiplicityBridge

/-!
# Hab25 Johnson numeric residual from S11 cardinality scaling

This file provides the final lightweight adapter from the proven S11 scaling bridge into the
opened Hab25 residual bundle's `JohnsonNumericBound` field. It does not prove the
m-multiplicity bad-scalar count; it only states the exact way that future cardinality bound,
together with the remaining real numerator comparison, discharges the named numeric residual.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap
open Classical NNReal Code Finset
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **Constructor for the Hab25 numeric residual from cardinality data.** A uniform bound
`N` on the bad-scalar set of every word-stack, plus real arithmetic
`(N : ℝ) ≤ B` and `B / |F| ≤ johnsonBoundReal`, gives the exact `JohnsonNumericBound`
field consumed by `Hab25JohnsonResiduals`.

This is pure plumbing from the proven S11 scaling theorem into the opened residual bundle:
the hard theorem remains the m-multiplicity proof of the per-stack bad-scalar cardinality
bound and the closed-form numerator comparison. -/
theorem JohnsonNumericBound.of_card_le
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hNB : (N : ℝ) ≤ B)
    (hBdiv : B / (Fintype.card F₀ : ℝ) ≤
      CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ)
    (hN : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.filter
        (fun γ : F₀ =>
          mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
        Finset.univ).card ≤ N) :
    JohnsonNumericBound domain k η δ := by
  simpa [JohnsonNumericBound] using
    _root_.ProximityGap.epsMCA_rs_le_johnsonBoundReal_of_card_le
      domain k η δ N B hB hNB hBdiv hN

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.JohnsonNumericBound.of_card_le
