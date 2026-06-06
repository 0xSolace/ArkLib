import ArkLib.ProofSystem.RingSwitching.SumcheckPhase
import ArkLib.OracleReduction.Completeness

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial
  Module TensorProduct Nat Matrix
open scoped NNReal
open Sumcheck.Structured

namespace RingSwitching.SumcheckPhase
noncomputable section

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L]
  [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

theorem iteratedSumcheckOracleReduction_perfectCompleteness_residual_holds
    (hInit : NeverFail init) :
    iteratedSumcheckOracleReduction_perfectCompleteness_residual
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) := by
  intro i
  rw [OracleReduction.unroll_2_message_reduction_perfectCompleteness (hInit := hInit)
    (hDir0 := by rfl) (hDir1 := by rfl)
    (hImplSupp := by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])]
  intro stmtIn oStmtIn witIn h_relIn
  simp_rw [probEvent_eq_one_iff]
  dsimp only [iteratedSumcheckOracleReduction, iteratedSumcheckOracleProver,
    iteratedSumcheckOracleVerifier, OracleVerifier.toVerifier, FullTranscript.mk2]
  refine ⟨?_, ?_⟩
  · sorry
  · sorry

end
end RingSwitching.SumcheckPhase
