/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.MCAGSWitness
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLatticePrizeSpec

/-!
# Faithful MCA prize specifications from GS mass frontiers

`MCAGSWitness.lean` packages the remaining Guruswami-Sudan obligations as explicit faithful
mass and pivot/list-size frontiers, and turns each such frontier into a `MCALowerWitness`.
This module routes those lower witnesses through the faithful four-rate lattice prize API and
the satisfy/maximality specification layer.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal ENNReal

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace GrandChallengesLattice

open GrandChallenges

section GSThresholdSpec

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- A faithful GS mass frontier supplies existence of the faithful MCA lattice threshold. -/
theorem mcaThresholdExists_of_GSMassFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCAGS.MCALowerWitness.ofGSMassFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS mass frontier supplies the selected threshold's satisfy fact. -/
theorem mcaThreshold_spec_of_GSMassFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    let hne := mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS mass frontier lower-bounds the selected faithful MCA lattice threshold. -/
theorem latticeIndexOf_le_mcaThreshold_of_GSMassFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSMassLowerWitnessFrontier (F := F) C δ ε_star) :
    let hne := mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold (C : Set (ι → F)) ε_star hne :=
  MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
    (mcaThresholdExists_of_GSMassFrontier C δ ε_star hδ_le_one frontier)
    (MCAGS.MCALowerWitness.ofGSMassFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS pivot/list-size frontier supplies existence of the faithful MCA lattice
threshold. -/
theorem mcaThresholdExists_of_GSPivotFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSPivotLowerWitnessFrontier (F := F) C δ ε_star) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCAGS.MCALowerWitness.ofGSPivotFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS pivot/list-size frontier supplies the selected threshold's satisfy fact. -/
theorem mcaThreshold_spec_of_GSPivotFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSPivotLowerWitnessFrontier (F := F) C δ ε_star) :
    let hne := mcaThresholdExists_of_GSPivotFrontier C δ ε_star hδ_le_one frontier
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_of_GSPivotFrontier C δ ε_star hδ_le_one frontier)

/-- A faithful GS pivot/list-size frontier lower-bounds the selected faithful MCA lattice
threshold. -/
theorem latticeIndexOf_le_mcaThreshold_of_GSPivotFrontier
    (C : LinearCode ι F) (δ ε_star : ℝ≥0) (hδ_le_one : δ ≤ 1)
    (frontier : MCAGS.GSPivotLowerWitnessFrontier (F := F) C δ ε_star) :
    let hne := mcaThresholdExists_of_GSPivotFrontier C δ ε_star hδ_le_one frontier
    latticeIndexOf (ι := ι) δ hδ_le_one ≤
      mcaThreshold (C : Set (ι → F)) ε_star hne :=
  MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
    (mcaThresholdExists_of_GSPivotFrontier C δ ε_star hδ_le_one frontier)
    (MCAGS.MCALowerWitness.ofGSPivotFrontier C δ ε_star hδ_le_one frontier)

/-- Per-rate faithful GS mass frontiers resolve the faithful MCA lattice prize existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    MCAGS.MCALowerWitness.ofGSMassFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)

/-- Per-rate faithful GS mass frontiers resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSMassLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCAGS.MCALowerWitness.ofGSMassFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)

/-- Per-rate faithful GS pivot/list-size frontiers resolve the faithful MCA lattice prize
existentially. -/
theorem exists_mcaPrizeLatticeResolved_of_GSPivotFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSPivotLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  exists_mcaPrizeLatticeResolved_of_lowerWitnesses domain fun j =>
    MCAGS.MCALowerWitness.ofGSPivotFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)

/-- Per-rate faithful GS pivot/list-size frontiers resolve the faithful MCA prize and expose the
satisfy/maximality specification for the selected lattice thresholds. -/
theorem exists_mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers
    (domain : ι ↪ F) (δ : Fin 4 → ℝ≥0)
    (hδ_le_one : ∀ j : Fin 4, δ j ≤ 1)
    (frontier : ∀ j : Fin 4,
      MCAGS.GSPivotLowerWitnessFrontier (F := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
        (δ j) epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1),
      mcaPrizeLatticeResolved domain τ ∧
        ∀ j : Fin 4,
          let C : Set (ι → F) :=
            ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
          ∃ _ : mcaThresholdExists C epsStar,
            mcaSatisfies C epsStar (τ j) ∧
              ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j :=
  exists_mcaPrizeLatticeResolved_with_spec_of_lowerWitnesses domain fun j =>
    MCAGS.MCALowerWitness.ofGSPivotFrontier
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
      (δ j) epsStar (hδ_le_one j) (frontier j)

end GSThresholdSpec

set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_GSMassFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_GSMassFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_of_GSMassFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_GSPivotFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_GSPivotFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.latticeIndexOf_le_mcaThreshold_of_GSPivotFrontier
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_of_GSPivotFrontiers
set_option linter.style.longLine false in
#print axioms ProximityGap.GrandChallengesLattice.exists_mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers

end GrandChallengesLattice

end ProximityGap
