import ArkLib.OracleReduction.FiatShamir.StateRestorationTransport

open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type}

attribute [local instance 10000] Reduction.fiatShamirNoChallengeSampleable

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

local instance fiatShamirProverOnlyCanonicalKS2 : ProtocolSpec.ProverOnly
    (Reduction.FiatShamirProtocolSpec (pSpec := pSpec)) where
  prover_first' := by simp

-- Skeleton: just unfold to inspect the goal.
theorem fiatShamir_knowledgeSoundnessTransferResidual_canonical
    (srInit : ProbComp (QueryImpl (fsChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (fsChallengeOracle StmtIn pSpec) Id) ProbComp))
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (knowledgeError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec) :
    fiatShamir_knowledgeSoundnessTransferResidual srInit srImpl srInit
      (fiatShamirCoupledQueryImpl (oSpec := oSpec) (pSpec := pSpec) (StmtIn := StmtIn) srImpl)
      relIn relOut knowledgeError V := by
  intro hSR
  obtain ⟨srExtractor, hbound⟩ := hSR
  refine ⟨fiatShamirStraightlineExtractorOfStateRestoration
    (oSpec := oSpec) (pSpec := pSpec) srExtractor, ?_⟩
  intro stmtIn witIn prover
  have h := hbound (Prover.StateRestoration.knowledgeSoundnessOfFiatShamirProver
    (oSpec := oSpec) (pSpec := pSpec) prover stmtIn witIn)
  dsimp only
  trace_state
  sorry

end Reduction
