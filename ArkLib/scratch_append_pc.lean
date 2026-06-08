import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ : Type}
  {m : ℕ} {pSpec₁ : ProtocolSpec m}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}

example
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    True := by
  have hIS₁ : ∀ {β} (q : OracleQuery (oSpec + [pSpec₁.Challenge]ₒ) β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery
        (QueryImpl.addLift impl challengeQueryImpl :
          QueryImpl (oSpec + [pSpec₁.Challenge]ₒ) (StateT σ ProbComp)) q).run s)
        = support (liftM q : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) β) := by
    intro β q s
    cases q with | mk t f =>
    cases t with
    | inl i => exact hImplSupp (OracleQuery.mk i f) s
    | inr i =>
      simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
        QueryImpl.addLift_def, QueryImpl.add_apply_inr]
      have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s
      rw [support_liftM]
      simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
        StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
        support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
        support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
        liftM_map] using hq
  have h₁' : ∀ stmtIn witIn, (stmtIn, witIn) ∈ rel₁ →
      ∀ x ∈ support (OptionT.mk (run stmtIn witIn R₁) :
        OptionT (OracleComp (oSpec + [pSpec₁.Challenge]ₒ)) _),
        ((x.2, x.1.2.2) ∈ rel₂ ∧ x.1.2.1 = x.2) := by
    intro st wt hmem
    have hh := h₁
    rw [perfectCompleteness_eq_prob_one] at hh
    have := hh st wt hmem
    rw [probEvent_eq_one_iff, support_bind_simulateQ_run'_eq_mk init _ _ hInit hIS₁] at this
    exact this.2
  trivial

end Reduction
