import ArkLib.ProofSystem.ToyProblem.Leaderboard
open ToyProblem

theorem test_proof {k : ℕ} {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
    (C : Set (ι → F)) (δ : ℝ≥0) :
  winningSetSoundness_le_toySoundnessError_residual (k := k) C δ := by
  sorry
