import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness
open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
theorem tst
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : FullTranscript pSpec) (prv : StmtOut × WitOut) (vout : StmtOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : some vout ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    some ((tr, prv), vout) ∈ support (OptionT.run (R.run stmt wit)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff]
  refine ⟨some (tr, prv), ?_, ?_⟩
  · sorry
  · simp only [Option.elim_some, mem_support_bind_iff]
    refine ⟨some (some vout), ?_, ?_⟩
    · simp only [Option.getM_some, mem_support_bind_iff, support_pure, OptionT.run_pure]
      revert hV; extract_goal; sorry
    · sorry
end Reduction
