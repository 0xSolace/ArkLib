import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
  {stmtIn : Stmt₁} {witIn : Wit₁}

-- Support-half core: appended run support point ↦ component run support points
example (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (x : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃)
    (hx : some x ∈ support ((R₁.append R₂).run stmtIn witIn).run) :
    ∃ (p1 : FullTranscript pSpec₁ × Stmt₂ × Wit₂) (sv2 : Stmt₂)
      (p2 : FullTranscript pSpec₂ × Stmt₃ × Wit₃),
      some ((p1.1, p1.2), sv2) ∈ support (R₁.run stmtIn witIn).run ∧
      some ((p2.1, p2.2), x.2) ∈ support (R₂.run p1.2.1 p1.2.2).run := by
  unfold Reduction.run at hx
  rw [show (R₁.append R₂).prover = R₁.prover.append R₂.prover from rfl,
    Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂] at hx
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind, mem_support_bind_iff,
    support_liftM, Set.mem_image] at hx
  obtain ⟨p1opt, hp1, hx⟩ := hx
  sorry

end Reduction
