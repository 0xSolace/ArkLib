import ArkLib.Data.CodingTheory.Connections.GKL24FirstMoment

namespace ProximityGap

open scoped NNReal ProbabilityTheory BigOperators
open CodingTheory Code

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem lineAgreeSet_inter_card_ge_of_mem_mcaBadWitness_scratch
    (MC : Submodule F (ι → F)) (δ p : ℝ≥0) (u₀ u₁ w w' : ι → F)
    (hp_le_one : p ≤ 1)
    (hδp : 2 * (δ : ℝ) ≤ (p : ℝ))
    {γ γ' : F}
    (hγ : γ ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w)
    (hγ' : γ' ∈ mcaBadWitness (F := F) (MC : Set (ι → F)) δ u₀ u₁ w') :
    ((1 - p) * Fintype.card ι : ℝ≥0) ≤
      (((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w' γ').card : ℕ) : ℝ≥0) := by
  have hγ_card_nn :=
    lineAgreeSet_card_ge_of_mem_mcaBadWitness MC δ u₀ u₁ w hγ
  have hγ'_card_nn :=
    lineAgreeSet_card_ge_of_mem_mcaBadWitness MC δ u₀ u₁ w' hγ'
  have hγ_card :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
        ((lineAgreeSet u₀ u₁ w γ).card : ℝ) := by
    have h2 :
        (((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ≤
          ((lineAgreeSet u₀ u₁ w γ).card : ℝ) := by
      exact_mod_cast hγ_card_nn
    exact (NNReal.coe_one_sub_mul_le δ (by positivity)).trans h2
  have hγ'_card :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) ≤
        ((lineAgreeSet u₀ u₁ w' γ').card : ℝ) := by
    have h2 :
        (((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) ≤
          ((lineAgreeSet u₀ u₁ w' γ').card : ℝ) := by
      exact_mod_cast hγ'_card_nn
    exact (NNReal.coe_one_sub_mul_le δ (by positivity)).trans h2
  have hbon :
      (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) +
          (1 - (δ : ℝ)) * (Fintype.card ι : ℝ) -
            (Fintype.card ι : ℝ) ≤
        (((lineAgreeSet u₀ u₁ w γ ∩ lineAgreeSet u₀ u₁ w' γ').card : ℕ) : ℝ) :=
    lineAgreeSet_inter_card_ge_of_card_ge u₀ u₁ w w' γ γ' hγ_card hγ'_card
  have hp_real :
      (((1 - p : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ)) =
        (1 - (p : ℝ)) * (Fintype.card ι : ℝ) := by
    rw [NNReal.coe_sub hp_le_one, NNReal.coe_one]
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  rw [hp_real]
  nlinarith [hbon, hδp, Fintype.card_pos_iff.mpr inferInstance]

end

end ProximityGap
