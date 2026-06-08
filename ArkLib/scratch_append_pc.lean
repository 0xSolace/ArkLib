import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness
open OracleComp OracleSpec ProtocolSpec
namespace Reduction
variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
theorem mem_support_run_of_prover_verifier
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : FullTranscript pSpec) (prv : StmtOut × WitOut) (vout : StmtOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : some vout ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    some ((tr, prv), vout) ∈ support (OptionT.run (R.run stmt wit)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff]
  refine ⟨some (tr, prv), ?_, ?_⟩
  · show some (tr, prv) ∈ support (some <$> R.prover.run stmt wit)
    simp only [support_map, Set.mem_image, Option.some.injEq]; exact ⟨_, hP, rfl⟩
  · simp only [Option.elim_some, mem_support_bind_iff, support_liftM, Set.mem_image,
      Option.getM_some, OptionT.run_pure, support_pure, Set.mem_singleton_iff, OptionT.run_bind,
      Option.elimM, bind_assoc, bind_pure_comp, map_pure, support_map]
    refine ⟨some vout, hV, ?_⟩
    simp [Option.getM_some]
end Reduction
