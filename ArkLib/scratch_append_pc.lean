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

example (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (x : (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃) × Stmt₃)
    (hx : some x ∈ support ((R₁.append R₂).run stmtIn witIn).run) :
    ∃ (tr1 : FullTranscript pSpec₁) (p1 : Stmt₂ × Wit₂) (sv2 : Stmt₂)
      (tr2 : FullTranscript pSpec₂),
      some ((tr1, p1), sv2) ∈ support (R₁.run stmtIn witIn).run ∧
      some ((tr2, x.1.2.1, x.1.2.2), x.2) ∈ support (R₂.run p1.1 p1.2).run := by
  unfold Reduction.run at hx
  rw [show (R₁.append R₂).prover = R₁.prover.append R₂.prover from rfl,
    Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover) stmtIn witIn hn hDir hDir₂] at hx
  simp only [OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind, mem_support_bind_iff,
    support_liftM, Set.mem_image] at hx
  obtain ⟨p1opt, hp1, hx⟩ := hx
  rcases p1opt with _ | ⟨tr1, s2, w2⟩
  · simp at hx
  · simp only [Option.elim, OptionT.run_bind, Option.elimM, bind_assoc, liftM_bind,
      mem_support_bind_iff, support_liftM, Set.mem_image, OptionT.run_pure, liftM_pure,
      bind_pure_comp, map_bind] at hx
    obtain ⟨p2opt, hp2, hx⟩ := hx
    rcases p2opt with _ | ⟨tr2, s3, w3⟩
    · simp at hx
    · simp only [Option.elim, Verifier.append_run, OptionT.run_bind, Option.elimM, bind_assoc,
        mem_support_bind_iff, OptionT.run_pure, liftM_pure, bind_pure_comp, map_bind,
        liftM_bind, support_liftM, Set.mem_image] at hx
      obtain ⟨sv2opt, hsv2, hx⟩ := hx
      rcases sv2opt with _ | sv2
      · simp at hx
      · simp only [Option.elim, OptionT.run_bind, Option.elimM, bind_assoc, mem_support_bind_iff,
          OptionT.run_pure, liftM_pure, bind_pure_comp, map_bind, liftM_bind, support_liftM,
          Set.mem_image, Option.getM_some, OptionT.run_pure, Option.bind_some] at hx
        obtain ⟨sv3opt, hsv3, hx⟩ := hx
        rcases sv3opt with _ | sv3
        · simp at hx
        · simp only [Option.elim, Option.getM_some, OptionT.run_pure, map_pure, support_pure,
            Set.mem_singleton_iff, Option.some.injEq] at hx
          extract_goal
          sorry

end Reduction
