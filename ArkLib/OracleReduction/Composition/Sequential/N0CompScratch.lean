import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

-- Explore: unfold the appended reduction run via append_run_empty + Verifier.append_run.
example (stmt : Stmt₁) (wit : Wit₁) :
    (R₁.append R₂).run stmt wit = (do
      let proverResult ← (R₁.prover.append R₂.prover).run stmt wit
      let stmtOut ← liftM ((R₁.verifier.append R₂.verifier).run stmt proverResult.1).run
      return ⟨proverResult, ← stmtOut.getM⟩) := by
  rfl

end Reduction
