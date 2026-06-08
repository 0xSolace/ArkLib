import ArkLib.OracleReduction.Composition.Sequential.EmptyAppend
import ArkLib.ToVCVio.OracleComp.SimSemantics.SubsingletonState

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

theorem run_append_empty (stmt : Stmt₁) (wit : Wit₁) :
    (R₁.append R₂).run stmt wit = (do
      let x ← liftM (liftM (R₁.prover.run stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      let x_1 ← liftM (liftM (R₂.prover.run x.2.1 x.2.2) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      let stmtOut ← @liftM (OracleComp oSpec)
        (OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
          (OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))))
        (Option Stmt₃) ((R₁.verifier.append R₂.verifier).run stmt (x.1 ++ₜ x_1.1)).run
      return ((x.1 ++ₜ x_1.1, x_1.2.1, x_1.2.2), ← stmtOut.getM)) := by
  unfold Reduction.run Reduction.append
  rw [Prover.append_run_empty]
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]

variable [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {init : ProbComp Unit} {impl : QueryImpl oSpec (StateT Unit ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

example
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  unfold perfectCompleteness at h₁ h₂ ⊢
  rw [completeness_iff_completenessFromRun] at h₁ h₂ ⊢
  unfold completenessFromRun at h₁ h₂ ⊢
  intro stmt wit hmem
  dsimp only
  rw [run_append_empty]
  trace_state
  sorry

end Reduction
