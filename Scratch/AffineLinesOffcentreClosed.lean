import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.Main

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Finset Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_boundaryCard_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentre
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hBoundaryCard hδ

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_residual_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_boundaryCard_scratch
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ) hδ hInput
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_data_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_residual_scratch
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput hStrictBoundary
    (ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_quantization_data_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentre
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentre_lattice_data_scratch
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_boundaryCard_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundaryCard : BoundaryCardResidual (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines (ι := ι) (F := F) (deg := deg)
    (domain := domain) (δ := δ)
    (ArkLib.KeystoneStrictResidual.strictCoeffPolysResidual_of_betaRec_offcentreFin
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hInput)
    hBoundaryCard hδ

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_residual_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLattice :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeResidual
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_boundaryCard_scratch
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ) hδ hInput
    (ArkLib.BoundaryCardResidual.boundaryCardResidual_of_lattice_residual
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLattice hStrictBoundary)

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_data_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hStrictBoundary : ∀ (u : WordStack F (Fin 2) ι) (δ' : ℝ≥0),
      δ' < δ →
      Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι) →
      0 < (RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := domain) u δ').card →
      jointAgreement (C := ReedSolomon.code domain deg) (δ := δ') (W := u))
    (hLatticeData :
      ArkLib.BoundaryCardResidual.BoundaryCardLatticeData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_residual_scratch
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput hStrictBoundary
    (ArkLib.BoundaryDischarge.boundaryCardLatticeResidual_of_lattice_data
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hLatticeData)

omit [DecidableEq ι] in
theorem RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_quantization_data_scratch
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain)
    (hInput : ∀ (_hk : 0 < 1) (u : WordStack F (Fin 2) ι),
      Pr_{
        let z ← $ᵖ F}[δᵣ(∑ t : Fin 2, (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ] >
          (((1 : ℕ) : ENNReal) * (errorBound δ deg domain : ENNReal)) →
      (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
      δ < 1 - ReedSolomon.sqrtRate deg domain →
      ArkLib.KeystoneStrictResidual.BetaCurveInputOffcentreFin
        (k := 1) (deg := deg) (domain := domain) (δ := δ) u)
    (hBoundary :
      ArkLib.BoundaryDischarge.BoundaryCardQuantizationData
        (k := 1) (deg := deg) (domain := domain) (δ := δ)) :
  δ_ε_correlatedAgreementAffineLines (A := F) (F := F) (ι := ι)
    (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  RS_correlatedAgreement_affineLines_johnson_of_betaRec_offcentreFin_lattice_data_scratch
    (ι := ι) (F := F) (deg := deg) (domain := domain) (δ := δ)
    hδ hInput
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.strictInterior
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)
    (ArkLib.BoundaryDischarge.BoundaryCardQuantizationData.latticeData
      (k := 1) (deg := deg) (domain := domain) (δ := δ) hBoundary)

end CoreResults

end ProximityGap
