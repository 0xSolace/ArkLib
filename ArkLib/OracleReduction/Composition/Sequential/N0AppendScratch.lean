import ArkLib.OracleReduction.Composition.Sequential.Append

/-! Scratch: attempt to discharge `Prover.appendRunRightResidual` for the empty trailing protocol
(`n = 0`). For `n = 0` the right-block continuation `continueFromTo ⟨m⟩ (last m)` is `pure`
(`continueFromTo_self`), and the left block is `append_runToRound_seam`; the only remaining content
is the `n = 0` `output` branch. -/

open OracleSpec OracleComp ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec 0}
  (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
  (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)

example (stmt : Stmt₁) (wit : Wit₁) :
    appendRunRightResidual (P₁ := P₁) (P₂ := P₂) stmt wit := by
  unfold appendRunRightResidual
  have hcont : (P₁.append P₂).continueFromTo stmt wit (⟨m, by omega⟩ : Fin (m + 0 + 1))
      (Fin.last (m + 0)) = pure := by
    funext rk
    exact continueFromTo_self _ _ _ _ rk
  rw [hcont, bind_pure]
  trace_state
  sorry

end Prover
