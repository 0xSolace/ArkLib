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
  refine le_trans ?_ h
  -- Step 1: rewrite the FS runWithLog+extractor exec to a run+extractor exec (logs dropped).
  have hrun :
      (do
        let __discr ← runWithLog stmtIn witIn
          { prover := prover, verifier := V.fiatShamir }
        let extractedWitIn ←
          liftM (fiatShamirStraightlineExtractorOfStateRestoration srExtractor stmtIn
            __discr.1.1.2.2 __discr.1.1.1 __discr.2.1.fst __discr.2.2)
        pure (stmtIn, extractedWitIn, __discr.1.2, __discr.1.1.2.2)) =
      (do
        let r ← Reduction.run stmtIn witIn
          { prover := prover, verifier := V.fiatShamir }
        let extractedWitIn ←
          liftM (fiatShamirStraightlineExtractorOfStateRestoration srExtractor stmtIn
            r.1.2.2 r.1.1 default default)
        pure (stmtIn, extractedWitIn, r.2, r.1.2.2)) := by
    rw [← Reduction.runWithLog_discard_logs_eq_run
      (reduction := { prover := prover, verifier := V.fiatShamir })]
    simp only [fiatShamirStraightlineExtractorOfStateRestoration_apply,
      map_eq_pure_bind, bind_assoc, pure_bind]
  rw [hrun]
  trace_state
  sorry

end Reduction
