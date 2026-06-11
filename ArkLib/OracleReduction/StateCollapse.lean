/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.RunUnroll

/-!
# State collapse: reducing arbitrary-state implementations to `Unit`-state ones

Several seam keystones in the sequential-composition theory (append soundness, append
round-by-round knowledge soundness) are proven under a `[Subsingleton σ]` hypothesis on the
implementation state, because their seam-reorder steps fix the threaded state. This file
provides the **state-collapse transfer**: for a *state-preserving* implementation
`impl : QueryImpl oSpec (StateT σ ProbComp)` and a fixed initial state `s₀`, the collapsed
implementation

* `collapseState impl s₀ : QueryImpl oSpec (StateT Unit ProbComp)`

answers every query by running `impl` from `s₀` and discarding the (unchanged) state. The
master identity `evalDist_simulateQ_run'_collapseState` shows that simulating any computation
against the collapsed implementation from `()` has **the same distribution** as simulating it
against `impl` from `s₀`: state preservation means the threaded state is constantly `s₀`, so
re-running each query from `s₀` is indistinguishable. Since `Unit` is a subsingleton, the
`[Subsingleton σ]` keystones apply to the collapsed side verbatim, and the identity (plus an
averaging step over the initial-state distribution, `probEvent_bind_le_of_forall_le`)
transfers their conclusions back to arbitrary `σ`.

Side-condition bricks: the collapsed implementation is unconditionally state-preserving
(`collapseState_state_preserving`), inherits non-failure (`collapseState_neverFail`), and the
probability-level corollaries (`probEvent_simulateQ_run'_collapseState`,
`probFailure_simulateQ_run'_collapseState`) follow from the master identity since `probEvent`
and `probFailure` are functions of `evalDist`.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open OracleComp OracleSpec
open scoped NNReal ENNReal

namespace StateCollapse

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- Collapse a stateful query implementation to a `Unit`-state one by pinning the state to
`s₀`: every query runs `impl` from `s₀` and discards the result state. For state-preserving
`impl` this is distribution-faithful (`evalDist_simulateQ_run'_collapseState`). -/
def collapseState (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) :
    QueryImpl spec (StateT Unit ProbComp) :=
  fun t => StateT.lift ((impl t).run' s₀)

/-- The collapsed implementation is unconditionally state-preserving (the state is `Unit`). -/
theorem collapseState_state_preserving
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) :
    ∀ (t : spec.Domain) (u : Unit) (x : spec.Range t × Unit),
      x ∈ support ((collapseState impl s₀ t).run u) → x.2 = u := by
  intro t u x _
  exact Subsingleton.elim _ _

/-- The collapsed implementation runs the original from `s₀` on every query: the `run'`
distributions agree per query. -/
theorem collapseState_run'_apply
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ) (t : spec.Domain) (u : Unit) :
    evalDist ((collapseState impl s₀ t).run' u) = evalDist ((impl t).run' s₀) := by
  simp [collapseState, StateT.run'_eq, StateT.run_lift, evalDist_map, Functor.map_map]

/-- The collapsed implementation never fails when the original never fails from `s₀`. -/
theorem collapseState_neverFail
    (impl : QueryImpl spec (StateT σ ProbComp)) (s₀ : σ)
    (himpl : ∀ (t : spec.Domain), Pr[⊥ | (impl t).run s₀] = 0) :
    ∀ (t : spec.Domain) (u : Unit), Pr[⊥ | (collapseState impl s₀ t).run u] = 0 := by
  intro t u
  simp only [collapseState, StateT.run_lift]
  rw [probFailure_bind_eq_zero_iff]
  refine ⟨?_, fun a _ => probFailure_pure (a, u)⟩
  have h := himpl t
  rw [StateT.run'_eq]
  simp [h]

/-- **The master collapse identity**: simulating any computation against the collapsed
implementation (from `()`) has the same distribution as simulating it against the original
state-preserving implementation from the pinned state `s₀`. Induction on the computation;
state preservation keeps the original's threaded state constantly `s₀`, which is exactly what
the collapsed side re-supplies on every query. -/
theorem evalDist_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    evalDist ((simulateQ (collapseState impl s₀) X).run' u)
      = evalDist ((simulateQ impl X).run' s₀) := by
  induction X using OracleComp.inductionOn with
  | pure a => simp [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
  | query_bind t oa ih =>
    have hqR : (simulateQ impl (liftM (OracleSpec.query t))).run s₀ = (impl t).run s₀ := by
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have hqL : (simulateQ (collapseState impl s₀) (liftM (OracleSpec.query t))).run u
        = (collapseState impl s₀ t).run u := by
      simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have keyR :
        evalDist ((simulateQ impl (liftM (OracleSpec.query t) >>= oa)).run' s₀)
        = (evalDist ((impl t).run' s₀)) >>= fun a =>
            evalDist ((simulateQ impl (oa a)).run' s₀) := by
      rw [StateT.run'_eq,
        OptionTStateT.simulateQ_run_bind_state_fixed impl hso (liftM (OracleSpec.query t)) oa s₀,
        hqR, map_bind, evalDist_bind,
        show (evalDist ((impl t).run' s₀)) = (fun x => x.1) <$> evalDist ((impl t).run s₀) from by
          rw [StateT.run'_eq, evalDist_map],
        bind_map_left]
      refine bind_congr fun p => ?_
      rw [StateT.run'_eq]
    have keyL :
        evalDist ((simulateQ (collapseState impl s₀)
            (liftM (OracleSpec.query t) >>= oa)).run' u)
        = (evalDist ((collapseState impl s₀ t).run' u)) >>= fun a =>
            evalDist ((simulateQ (collapseState impl s₀) (oa a)).run' u) := by
      rw [StateT.run'_eq,
        OptionTStateT.simulateQ_run_bind_state_fixed (collapseState impl s₀)
          (collapseState_state_preserving impl s₀) (liftM (OracleSpec.query t)) oa u,
        hqL, map_bind, evalDist_bind,
        show (evalDist ((collapseState impl s₀ t).run' u))
            = (fun x => x.1) <$> evalDist ((collapseState impl s₀ t).run u) from by
          rw [StateT.run'_eq, evalDist_map],
        bind_map_left]
      refine bind_congr fun p => ?_
      rw [StateT.run'_eq]
    rw [keyL, keyR, collapseState_run'_apply impl s₀ t u]
    exact bind_congr fun a => ih a

/-- `probEvent` is a function of `evalDist`, across monads. -/
private lemma probEvent_congr_evalDist {m m' : Type → Type _}
    [Monad m] [Monad m'] [HasEvalSPMF m] [HasEvalSPMF m'] {α : Type}
    {mx : m α} {my : m' α} (h : evalDist mx = evalDist my) (p : α → Prop) :
    Pr[p | mx] = Pr[p | my] := by
  unfold probEvent
  rw [h]

/-- `probFailure` is a function of `evalDist`, across monads. -/
private lemma probFailure_congr_evalDist {m m' : Type → Type _}
    [Monad m] [Monad m'] [HasEvalSPMF m] [HasEvalSPMF m'] {α : Type}
    {mx : m α} {my : m' α} (h : evalDist mx = evalDist my) :
    Pr[⊥ | mx] = Pr[⊥ | my] := by
  unfold probFailure
  rw [h]

/-- Probability-level collapse identity for events. -/
theorem probEvent_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) (p : α → Prop) :
    Pr[p | (simulateQ (collapseState impl s₀) X).run' u]
      = Pr[p | (simulateQ impl X).run' s₀] :=
  probEvent_congr_evalDist (evalDist_simulateQ_run'_collapseState impl hso X s₀ u) p

/-- Probability-level collapse identity for failure. -/
theorem probFailure_simulateQ_run'_collapseState
    (impl : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    {α : Type} (X : OracleComp spec α) (s₀ : σ) (u : Unit) :
    Pr[⊥ | (simulateQ (collapseState impl s₀) X).run' u]
      = Pr[⊥ | (simulateQ impl X).run' s₀] :=
  probFailure_congr_evalDist (evalDist_simulateQ_run'_collapseState impl hso X s₀ u)

/-- **Averaging transfer**: a uniform bound on the pinned-state runs bounds the
initial-state-sampled run. This is the step that converts per-`s₀` collapsed conclusions
(obtained via the `[Subsingleton Unit]` keystones) into conclusions for an arbitrary
initial-state distribution `init`. -/
theorem probEvent_init_bind_le_of_forall_collapse_le
    (impl : QueryImpl spec (StateT σ ProbComp))
    (init : ProbComp σ) {α : Type} (X : OracleComp spec α) (p : α × σ → Prop) {ε : ℝ≥0∞}
    (h : ∀ s₀ : σ, Pr[p | (simulateQ impl X).run s₀] ≤ ε) :
    Pr[p | do (simulateQ impl X).run (← init)] ≤ ε := by
  exact probEvent_bind_le_of_forall_le fun s₀ _ => h s₀

end StateCollapse

/-! ## Axiom audit — kernel-clean. -/
#print axioms StateCollapse.evalDist_simulateQ_run'_collapseState
#print axioms StateCollapse.probEvent_simulateQ_run'_collapseState
#print axioms StateCollapse.probEvent_init_bind_le_of_forall_collapse_le
