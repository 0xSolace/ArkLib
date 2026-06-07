import ArkLib.Data.CodingTheory.Connections.ListDecodingAndCA

namespace CodingTheory

open scoped NNReal ProbabilityTheory BigOperators
open ListDecodable ProximityGap Code

section ListImpliesMCA

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_strict_witnessCover_residual_scratch
    (C : LinearCode ι F) (L : ℕ) (δ η : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hη_pos : 0 < η) (hη_lt : η < 1) (hη_le_δ : η ≤ δ)
    (hΛ : Lambda ((C : Set (ι → F))) δ ≤ (L : ℕ∞))
    (hδp :
      2 * ((((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) : ℝ)) ≤ δ)
    (hres :
        ProximityGap.GKL24MaxCorrStrictWitnessCoverResidual C
          ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
          δ.toNNReal
          ((L : ℝ) ^ 2)) :
    epsMCA (F := F) (A := F) ((C : Set (ι → F)))
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) ≤
      ENNReal.ofReal
        (((L : ℝ) ^ 2 * δ * Fintype.card ι + 1 / η) / Fintype.card F) := by
  have hp_le_one : δ.toNNReal ≤ (1 : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    simpa [Real.toNNReal_of_nonneg (le_of_lt hδ_pos)] using hδ_lt.le
  have hδp :
      2 * ((((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal) : ℝ)) ≤
        (δ.toNNReal : ℝ) := by
    rw [Real.toNNReal_of_nonneg (le_of_lt hδ_pos)]
    exact hδp
  exact
    linear_listSize_to_epsMCA_gcxk25_of_gkl24_maxCorr_witnessCover_residual
      C L δ η hδ_pos hδ_lt hη_pos hη_lt hη_le_δ hΛ
      (ProximityGap.GKL24MaxCorrWitnessCoverResidual_of_strict_cover C
        ((1 - (1 - δ + η) ^ ((1 : ℝ) / 2)).toNNReal)
        δ.toNNReal hp_le_one hδp hres)

end ListImpliesMCA

end CodingTheory
