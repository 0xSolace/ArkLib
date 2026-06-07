import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.Basic.Distance

open ToyProblem Code InterleavedCode ListDecodable ProximityGap ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

lemma toy_linear_eq_root {F : Type} [Field F] (a b c d γ : F) (h_eq : a + γ * b = c + γ * d) (h_not_both : ¬ (a = c ∧ b = d)) :
    b ≠ d := by
  intro hbd
  have hbd_eq : b = d := hbd
  rw [hbd_eq] at h_eq
  have hac : a = c := add_right_cancel h_eq
  exact h_not_both ⟨hac, hbd_eq⟩

theorem winningSetSoundness_le_toySoundnessError_mcaSafe_residual_proof {k : ℕ} {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F] [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) :
  δ < (minRelHammingDistCode C : ℝ≥0) →
  winningSetSoundness (k := k) C δ ≤
    (epsMCA (F := F) (A := F) C δ).toNNReal +
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
        / (Fintype.card F : ℝ≥0) := by
  intro hδ
  sorry
