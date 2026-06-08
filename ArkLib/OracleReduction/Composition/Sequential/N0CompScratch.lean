import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

-- Factor the appended reduction's run by rewriting the prover via append_run_empty.
example (stmt : Stmt₁) (wit : Wit₁) :
    (R₁.append R₂).run stmt wit = (do
      let prv ← (do
        let ⟨tr₁, s₂, w₂⟩ ← liftM (R₁.prover.run stmt wit)
        let ⟨tr₂, s₃, w₃⟩ ← liftM (R₂.prover.run s₂ w₂)
        return (⟨tr₁ ++ₜ tr₂, s₃, w₃⟩ :
          ProtocolSpec.FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃))
      let sOut ← liftM ((R₁.verifier.append R₂.verifier).run stmt prv.1).run
      return ⟨prv, ← sOut.getM⟩) := by
  conv_lhs => unfold Reduction.run Reduction.append
  rw [Prover.append_run_empty]

end Reduction
