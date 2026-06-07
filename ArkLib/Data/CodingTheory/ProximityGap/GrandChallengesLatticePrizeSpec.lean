/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice

/-!
# Prize-lattice specification adapters

This lightweight module keeps the long faithful-lattice file from growing while exposing the
checked satisfy/maximality specification of the conjectural four-rate MCA prize aggregation.
-/

namespace ProximityGap

open scoped NNReal

namespace GrandChallengesLattice

open GrandChallenges

section MCAConjecturePrizeSpec

/-- The ignored-source MCA conjecture gives an existential faithful four-rate MCA prize
resolution together with the satisfy/maximality specification for the selected lattice
thresholds. The conjecture and all numeric side conditions remain explicit; this only packages the
existing existential aggregation with `mcaPrizeLatticeResolved_iff`. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_ignoredSource_mcaConjecture
    (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (δ : Fin 4 → ℝ≥0),
        (∀ j : Fin 4, 0 < ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊) →
        (∀ j : Fin 4, (δ j : ℝ) <
          1 - (⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ : ℝ) / Fintype.card ιC) →
        (∀ j : Fin 4, δ j ≤ 1) →
        (∀ j : Fin 4,
          ENNReal.ofReal
              (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC)
                ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊ (δ j) c₁ c₂ c₃) ≤
            (epsStar : ENNReal)) →
        ∃ τ : Fin 4 → Fin (Fintype.card ιC + 1),
          mcaPrizeLatticeResolved domain τ ∧
            ∀ j : Fin 4,
              let C : Set (ιC → FC) :=
                ReedSolomon.code domain
                  ⌊prizeRates j * (Fintype.card ιC : ℝ≥0)⌋₊
              ∃ _ : mcaThresholdExists C epsStar,
                mcaSatisfies C epsStar (τ j) ∧
                  ∀ i : Fin (Fintype.card ιC + 1),
                    mcaSatisfies C epsStar i → i ≤ τ j := by
  obtain ⟨c₁, c₂, c₃, hResolve⟩ :=
    exists_mcaPrizeLatticeResolved_of_ignoredSource_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain δ hk hδ hδ1 hbound
  rcases hResolve domain δ hk hδ hδ1 hbound with ⟨τ, hτ⟩
  exact ⟨τ, hτ, (mcaPrizeLatticeResolved_iff domain τ).mp hτ⟩

end MCAConjecturePrizeSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_ignoredSource_mcaConjecture

end GrandChallengesLattice

end ProximityGap
