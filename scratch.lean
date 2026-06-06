import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.ProofSystem.ToyProblem.Leaderboard
open ToyProblem
open Classical

theorem winningSetSoundness_le_toySoundnessError_residual_proof {k : ℕ} {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ≥0) :
  winningSetSoundness (k := k) C δ ≤
    (ProximityGap.epsMCA (F := F) (A := F) C δ).toNNReal +
      ((ProximityGap.Lambda (ProximityGap.interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
        / (Fintype.card F : ℝ≥0) := by
  sorry
