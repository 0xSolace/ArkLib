/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToVCVio.EvalDist.Instances.OptionT
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec
import ArkLib.ToVCVio.ToMathlib.Control.StateT
import VCVio.EvalDist.Defs.NeverFails
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.StateT.Basic
import VCVio.OracleComp.SimSemantics.OptionT.Basic

/-!
# Additions to VCV-io's `OracleComp.SimSemantics.SimulateQ`
-/

open OracleSpec OracleComp

universe u v

/-- Simulating the random oracle leaves a mapped uniform `Fin` sample unchanged. -/
lemma simulateQ_randomOracle_map_uniformFin {α : Type} (n : ℕ) (f : Fin (n + 1) → α) :
    ((simulateQ (unifSpec.randomOracle :
      QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
      (f <$> uniformSample (Fin (n + 1)) : ProbComp α) :
        StateT unifSpec.QueryCache ProbComp α).run' ∅) =
      (f <$> uniformSample (Fin (n + 1))) := by
  rw [simulateQ_map, StateT.run'_map_comm]
  congr 1

/-- If all outputs of the original `OracleComp` are successful and satisfy `P`, then the
    simulated `OptionT` computation satisfies `P` with probability one. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk ((simulateQ impl oa).run' s₀)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    have hfail : Pr[⊥ | (simulateQ impl oa).run' s₀] = 0 :=
      probFailure_eq_zero
    rw [hfail, _root_.zero_add]
    exact probOutput_eq_zero_of_not_mem_support fun hnone =>
      let hnone' := _root_.support_simulateQ_run'_subset impl oa s₀ hnone
      let ⟨_, hsome, _⟩ := h none hnone'
      by cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    obtain ⟨a, ha, hP⟩ := h (some x) (_root_.support_simulateQ_run'_subset impl oa s₀ hx)
    cases ha
    exact hP

/-- Bind-prefixed variant of `OptionT.probEvent_eq_one_of_simulateQ_support`: the simulated
    `OptionT` computation may sample its initial state `s₀` from an arbitrary `ProbComp σ`
    (e.g. the `(← init)` of `Reduction.perfectCompleteness`). Since
    `support_simulateQ_run'_subset` bounds the support uniformly in `s₀`, the support hypothesis
    `h` (independent of `s₀`) still discharges both the never-fail and all-outputs-`P` obligations.

    This is the form needed to close `OracleReduction`-style perfect-completeness goals, whose
    `OptionT.mk` body is `do let s ← init; (simulateQ impl oa).run' s`. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support_bind
    {ι σ α : Type} {spec : OracleSpec ι}
    (init : ProbComp σ)
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk (do let s ← init; (simulateQ impl oa).run' s)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · -- The simulated computation never fails: for every sampled state `s`, the run' has no `none`
    -- in its support (it is bounded by `support oa`, which contains no `none` by `h`).
    rw [OptionT.probFailure_eq, OptionT.run_mk, add_eq_zero]
    refine ⟨probFailure_eq_zero, ?_⟩
    refine probOutput_eq_zero_of_not_mem_support fun hnone => ?_
    rw [mem_support_bind_iff] at hnone
    obtain ⟨s, _, hnone⟩ := hnone
    obtain ⟨_, hsome, _⟩ := h none (support_simulateQ_run'_subset impl oa s hnone)
    cases hsome
  · -- Every successful output satisfies `P`: peel the `init` bind, then `support_simulateQ_run'`.
    intro x hx
    rw [OptionT.mem_support_iff, OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, _, hx⟩ := hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s hx)
    cases ha
    exact hP

/-- Properties of `Option`-valued outputs of an underlying `OracleComp`
    propagate to elements in the support of the simulated, run, and `OptionT`-wrapped
    version. -/
lemma OptionT.aux_mem_support_simulateQ_run'
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∀ a, x = some a → P a)
    {x : α} (hx : x ∈ support (OptionT.mk ((simulateQ impl oa).run' s₀))) : P x := by
  rw [OptionT.mem_support_iff] at hx
  exact h (some x) (_root_.support_simulateQ_run'_subset impl oa s₀ hx) x rfl

namespace OptionT

lemma mem_support_bind_mk
    {α β : Type} (sample : ProbComp α) (body : α → ProbComp (Option β))
    {x : β}
    (hx : x ∈ support (OptionT.mk (do
      let a ← sample
      body a))) :
    ∃ a, a ∈ support sample ∧ x ∈ support (OptionT.mk (body a)) := by
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨a, _, hx⟩ := hx
  exact ⟨a, ‹a ∈ support sample›, by simpa [OptionT.mem_support_iff] using hx⟩

lemma map_mk_bind_eq_of_body
    {α β γ δ : Type}
    (sample : ProbComp α)
    (body₁ : α → ProbComp (Option β))
    (body₂ : α → ProbComp (Option γ))
    (f : β → δ) (post : α → γ → δ)
    (hBody : ∀ a, Option.map f <$> body₁ a = Option.map (post a) <$> body₂ a) :
    f <$> OptionT.mk (do
      let a ← sample
      body₁ a)
    =
    OptionT.mk (do
      let a ← sample
      let r ← body₂ a
      pure (Option.map (post a) r)) := by
  apply OptionT.ext
  rw [OptionT.run_map]
  simp only [OptionT.run_mk, map_eq_bind_pure_comp, bind_assoc]
  congr 1
  funext a
  rw [← map_eq_bind_pure_comp, hBody a, map_eq_bind_pure_comp]
  rfl

/-- Support-level peeler for an `OptionT`-monadic bind, stated at the underlying-monad (`m`,
typically `OracleComp spec`) `.run` level. Every element `y` of the support of the *run* of
`mx >>= f` factors through an intermediate `some a` in `mx`'s run support and a `y` in the run
support of `f a`. Companion to `mem_support_bind_mk` for the case where the `OptionT.run` has
already been stripped to the bare underlying computation (e.g. the `oa : OracleComp spec (Option …)`
produced by coercing a `Reduction.run`-style `OptionT` computation into the
`OptionT.probEvent_eq_one_of_simulateQ_support_bind` toolkit lemma).

Applies to a hypothesis `y ∈ support oa` whenever `oa` is *definitionally* `(mx >>= f).run`
(the `OptionT.run` is identity), so callers need not respell the giant bind term. -/
lemma mem_support_run_bind
    {ι α β : Type} {spec : OracleSpec ι}
    (mx : OptionT (OracleComp spec) α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((mx >>= f : OptionT (OracleComp spec) β).run)) :
    (none ∈ support mx.run ∧ y = none) ∨
      ∃ a, some a ∈ support mx.run ∧ y ∈ support ((f a).run) := by
  rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff] at hy
  obtain ⟨o, ho, hy⟩ := hy
  cases o with
  | none => exact Or.inl ⟨ho, by simpa using hy⟩
  | some a => exact Or.inr ⟨a, ho, hy⟩

/-- `OptionT.lift`-headed specialization of `mem_support_run_bind`: a `lift`ed (hence never-failing)
first computation `oa` peels cleanly, with the intermediate value living in `support oa` directly
(no `none` branch). This is the shape of the prover-run prefix of a `Reduction.run` (the prover is
lifted into `OptionT`, so it cannot itself produce the `none` that `mem_support_run_bind`
admits). -/
lemma mem_support_run_lift_bind
    {ι α β : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (f : α → OptionT (OracleComp spec) β) {y : Option β}
    (hy : y ∈ support ((OptionT.lift oa >>= f : OptionT (OracleComp spec) β).run)) :
    ∃ a, a ∈ support oa ∧ y ∈ support ((f a).run) := by
  rw [OptionT.run_bind, OptionT.run_lift, Option.elimM, bind_pure_comp, bind_map_left,
    mem_support_bind_iff] at hy
  obtain ⟨a, ha, hy⟩ := hy
  exact ⟨a, ha, hy⟩

end OptionT

/-- `obtain`-friendly bind support peeler at the bare `OracleComp` level. Unlike `rw
[mem_support_bind_iff]`, applying this lemma to a hypothesis uses *definitional* unification to
match `mx >>= f`, so it engages through the `Monad`/`MonadLift` instance-tree mismatches that block
the syntactic `rw` (the elaborated `OracleComp.instMonad`/`Bind.bind` spelling produced by unfolded
`Prover.runToRound`/`Fin.induction` differs syntactically from the canonical `>>=`). -/
lemma OracleComp.mem_support_bind_peel
    {ι α β : Type} {spec : OracleSpec ι}
    (mx : OracleComp spec α) (f : α → OracleComp spec β) {y : β}
    (hy : y ∈ support (mx >>= f)) :
    ∃ a, a ∈ support mx ∧ y ∈ support (f a) := by
  rw [mem_support_bind_iff] at hy; exact hy

/-- `obtain`-friendly `pure` support resolver at the bare `OracleComp` level: `y ∈ support (pure a)`
forces `y = a`, matched by definitional unification (so it engages on the `PFunctor.FreeM.pure`
spelling that the syntactic `support_pure` `rw` rejects). -/
lemma OracleComp.eq_of_mem_support_pure
    {ι α : Type} {spec : OracleSpec ι} (a : α) {y : α}
    (hy : y ∈ support (pure a : OracleComp spec α)) : y = a := by
  rwa [support_pure, Set.mem_singleton_iff] at hy

/-- `obtain`-friendly `<$>` (map) support peeler at the bare `OracleComp` level: `y ∈ support (g
<$> mx)` yields a preimage `a ∈ support mx` with `y = g a`, matched by definitional unification (so
it engages on the elaborated `Functor.map`/`OracleComp.instMonad` spelling that the syntactic
`support_map` `rw` rejects). -/
lemma OracleComp.mem_support_map_peel
    {ι α β : Type} {spec : OracleSpec ι} (g : α → β) (mx : OracleComp spec α) {y : β}
    (hy : y ∈ support (g <$> mx)) :
    ∃ a, a ∈ support mx ∧ y = g a := by
  rw [support_map, Set.mem_image] at hy
  obtain ⟨a, ha, hy⟩ := hy
  exact ⟨a, ha, hy.symm⟩

namespace StateT

lemma map_run'_eq_of_map_eq {m : Type → Type} {σ α β γ : Type}
    [Monad m] [LawfulMonad m] (f : α → γ) (g : β → γ)
    (mx : StateT σ m α) (my : StateT σ m β) (s : σ)
    (h : f <$> mx = g <$> my) :
    f <$> mx.run' s = g <$> my.run' s := by
  rw [← StateT.run'_map_comm f, ← StateT.run'_map_comm g]
  exact congrArg (fun mx : StateT σ m γ => mx.run' s) h

end StateT

lemma simulateQ_bind_map_eq_of_body
    {ι σ α β γ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    simulateQ impl (oa >>= body₁) = f <$> simulateQ impl (oa >>= body₂) := by
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  congr 1
  funext a
  exact hBody a

lemma StateT.run'_simulateQ_bind_map_eq_of_body
    {ι σ α β γ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β) (s : σ)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    (simulateQ impl (oa >>= body₁)).run' s =
      f <$> (simulateQ impl (oa >>= body₂)).run' s := by
  rw [← StateT.run'_map_comm f]
  exact congrArg (fun mx : StateT σ ProbComp β => mx.run' s)
    (simulateQ_bind_map_eq_of_body impl oa body₁ body₂ f hBody)

/-- **`simulateQ` fusion.** Simulating an `OracleComp spec₁` through an intermediate implementation
`R : QueryImpl spec₁ (OracleComp spec₂)` and then simulating the result through
`S : QueryImpl spec₂ m` equals simulating directly through the *composed* per-query handler
`fun q => simulateQ S (R q)`. This is functoriality of `simulateQ` in its implementation argument —
the universal-fold fusion law for the free monad `OracleComp`. It is the key step that lets a
two-stage routed run (e.g. the appended `OracleVerifier.Append.verify`, which is
`simulateQ router₁ … >>= simulateQ (router₂ …) …`) be re-expressed as a single direct simulation,
collapsing the outer-oracle simulation through the routers. -/
theorem simulateQ_simulateQ {ι₁ ι₂ : Type*}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type u → Type v} [Monad m] [LawfulMonad m]
    (R : QueryImpl spec₁ (OracleComp spec₂)) (S : QueryImpl spec₂ m)
    {α : Type u} (c : OracleComp spec₁ α) :
    simulateQ S (simulateQ R c) = simulateQ (fun q => simulateQ S (R q)) c := by
  induction c using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_congr ih

/-! ### Staged for upstream VCV-io (post-pin)

The following declarations are verbatim copies of additions staged for VCV-io on its
branch `feat/simulateq-routing-lemmas` (touching `OracleComp/SimSemantics/QueryImpl/Basic.lean`,
`OracleComp/SimSemantics/SimulateQ.lean`, `OracleComp/SimSemantics/Append.lean`,
`OracleComp/Coercions/SubSpec.lean`), not yet merged there. Once that PR merges and a
VCVio bump past it lands, delete them here — but only after confirming the bump actually
carries them. -/

namespace QueryImpl

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Functor m]

/-- Reduce `mapQuery` on an explicit constructor-form query. Companion to `mapQuery_query`
for queries that arise from `SubSpec`-lift normalization (which produces
`OracleQuery.mk`/anonymous-constructor forms rather than `OracleSpec.query`). -/
@[simp] lemma mapQuery_mk {α} (impl : QueryImpl spec m)
    (t : spec.Domain) (f : spec.Range t → α) :
    impl.mapQuery (OracleQuery.mk t f) = f <$> impl t := rfl

end QueryImpl

section simulateQ_liftM_query

variable {ι : Type} {spec : OracleSpec ι} {r : Type → Type}
  [Monad r] (impl : QueryImpl spec r)

/-- Companion to `simulateQ_query` for a query entering the computation through a
*query-level lift chain*: simulating a query lifted from a sub-spec `spec'` applies the
implementation to the lifted query.

The `(liftM q : OracleComp spec α)` on the left elaborates through the canonical
`MonadLift (OracleQuery spec) (OracleComp spec)` composed (via `instMonadLiftTOfMonadLift`)
with the given `MonadLiftT (OracleQuery spec') (OracleQuery spec)` — e.g. a `SubSpec`
embedding chain such as `spec₂ ⊂ₒ spec₁ + spec₂ ⊂ₒ spec + (spec₁ + spec₂)`. This is the
term shape produced by lifting a query helper (`liftM (liftM (spec'.query t))`) into a
larger interface, as `OracleSpec.SubSpec`-based protocol verifiers do. `simulateQ_query`
itself cannot match it: its query's spec is forced to equal the simulated spec, while here
the query lives in `spec'`.

The right-hand side is deliberately `mapQuery` of the *single* term `liftM q` rather than
the unbundled `(liftM q).cont <$> impl (liftM q).input`: the type of `.cont` depends on
`.input`, so the unbundled form blocks all further `simp` rewriting of the lifted query
(the dependent-motive trap). With `mapQuery`, the lifted query can then be normalized in
place (everything in the `SubSpec` lift chain is definitional) and landed on the
implementation with `mapQuery_mk`.

Not `@[simp]`: for the common sum-spec layouts the specialized routing lemmas
(`QueryImpl.simulateQ_add_add_liftM_query_left` and friends) resolve the routed query in
one step; this general form would preempt them and strand the goal at an un-normalized
`mapQuery (liftM q)`. Use it manually for bespoke lift chains. -/
lemma simulateQ_liftM_query [LawfulMonad r] {ι' : Type} {spec' : OracleSpec ι'} {α : Type}
    [MonadLiftT (OracleQuery spec') (OracleQuery spec)] (q : OracleQuery spec' α) :
    simulateQ impl (liftM q : OracleComp spec α) =
      impl.mapQuery (liftM q : OracleQuery spec α) :=
  simulateQ_query impl (liftM q)

end simulateQ_liftM_query

/-- `simulateQ` distributes over an `OptionT`-monadic `forIn` on a list: the `OptionT`-loop
sibling of `simulateQ_list_forIn`. The body lives in `OptionT (OracleComp spec)`, so the loop
is decomposed via `simulateQ_optionT_bind` (rather than the `OracleComp`-level `simulateQ_bind`
that `simulateQ_list_forIn` uses). Needed to push `simulateQ` past a verifier's spot-check
`for j in List.finRange t do …` when that loop is `OptionT`-monadic. -/
lemma simulateQ_optionT_list_forIn
    {ι' α β : Type} {spec : OracleSpec ι'} {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl spec n) (xs : List α) (init : β)
    (body : α → β → OptionT (OracleComp spec) (ForInStep β)) :
    simulateQ impl ((forIn xs init body : OptionT (OracleComp spec) β) :
        OracleComp spec (Option β))
      = ((forIn xs init (fun a b => simulateQ impl (body a b)) : OptionT n β) : n (Option β)) := by
  induction xs generalizing init with
  | nil =>
      rw [List.forIn_nil, List.forIn_nil]
      exact simulateQ_pure impl (some init)
  | cons x rest ih =>
      rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind]
      refine bind_congr fun step => ?_
      cases step with
      | done b =>
          change simulateQ impl ((pure b : OptionT (OracleComp spec) β) :
            OracleComp spec (Option β)) = _
          exact simulateQ_pure impl (some b)
      | yield b => exact ih b

/-- If under `simulateQ` every loop body resolves to `pure (some (ForInStep.yield init))`
(yields the accumulator unchanged at the initial value), the whole `OptionT`-monadic `forIn`
resolves to `pure (some init)`. Discharges a verifier spot-check loop whose body is a sequence
of oracle reads followed by an always-passing `guard` (under the relevant accept hypothesis).
The `OptionT` companion to a constant-yield `simulateQ_list_forIn` collapse. -/
lemma simulateQ_optionT_forIn_yield_pure_some
    {ι' α β : Type} {spec : OracleSpec ι'} {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl spec n) (xs : List α) (init : β)
    (body : α → β → OptionT (OracleComp spec) (ForInStep β))
    (hbody : ∀ a, simulateQ impl ((body a init : OptionT (OracleComp spec) (ForInStep β)) :
        OracleComp spec (Option (ForInStep β)))
      = (pure (some (ForInStep.yield init)) : n (Option (ForInStep β)))) :
    simulateQ impl ((forIn xs init body : OptionT (OracleComp spec) β) :
        OracleComp spec (Option β))
      = (pure (some init) : n (Option β)) := by
  rw [simulateQ_optionT_list_forIn]
  induction xs with
  | nil => rw [List.forIn_nil]; rfl
  | cons x rest ih =>
      rw [List.forIn_cons]
      change ((simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
          OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β)) >>= _ :
          OptionT n β) = _
      rw [show (simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
          OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β))
          = (pure (ForInStep.yield init) : OptionT n (ForInStep β)) from hbody x]
      rw [pure_bind]
      exact ih

namespace OracleComp

variable {ι τ : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type}

/-- Peel the outermost step off a *chained* `OracleComp`-level lift: a `liftM` whose
`MonadLiftT (OracleComp spec) (OracleComp spec₃)` instance is the transitive composition of
the query-keyed `MonadLift (OracleComp superSpec) (OracleComp spec₃)` step with a remaining
chain `MonadLiftT (OracleComp spec) (OracleComp superSpec)` is the `liftComp` of the
remaining lift. Typeclass resolution builds exactly this shape (via
`instMonadLiftTOfMonadLift`) when lifting across two or more `OracleSpec.add` layers, e.g.
`OracleComp spec₂ → OracleComp (spec + (spec₁ + spec₂))` through the intermediate
`spec + spec₂`. None of the single-step lemmas (`liftComp_eq_liftM`, `liftComp_query`, …)
can engage such a chain directly, since their statements bake in the one-step instance.

Not `@[simp]`: with `spec = superSpec` the remaining chain can be `MonadLiftT.refl`, and the
right-hand side would then re-match the left-hand side. Use via explicit `rw`, then rewrite
the inner lift with `← liftComp_eq_liftM` and proceed with the `liftComp` API. -/
lemma liftM_eq_liftComp_liftM {κ : Type} {spec₃ : OracleSpec κ}
    [MonadLift (OracleQuery superSpec) (OracleQuery spec₃)]
    [MonadLiftT (OracleComp spec) (OracleComp superSpec)]
    (mx : OracleComp spec α) :
    (liftM mx : OracleComp spec₃ α) =
      liftComp (liftM mx : OracleComp superSpec α) spec₃ := rfl

end OracleComp

namespace QueryImpl

/-! ### Query routing through a right-nested sum implementation

Routing lemmas for the `spec + (spec₁ + spec₂)` layout used by stateless protocol
simulation oracles (e.g. a base spec plus a pair of message/statement oracle families,
the `simOracle2` layout): a single query lifted from one component — either at the
*query* level (`OracleQuery`) or pre-embedded in its own *computation* monad
(`OracleComp`, the shape produced by reusable query helpers) — resolves under
`simulateQ` to the implementation at the routed index.

Each left-hand side spells the canonical `MonadLiftT` chain that typeclass resolution
synthesizes for that lift (through the intermediate `spec + spec₂` etc.), which is what
lets these fire by `simp` on goals produced by elaborated protocol definitions. All six
are definitional modulo `simulateQ_spec_query`. -/

variable {ι' ι₁' ι₂' : Type} {spec : OracleSpec ι'} {spec₁ : OracleSpec ι₁'}
  {spec₂ : OracleSpec ι₂'} {m' : Type → Type} [Monad m'] [LawfulMonad m']
  (implA : QueryImpl spec m') (implB : QueryImpl (spec₁ + spec₂) m')

@[simp]
lemma simulateQ_add_add_liftM_query_base (t : spec.Domain) :
    simulateQ (implA + implB)
      (liftM (spec.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec.Range t)) =
      implA t :=
  (simulateQ_spec_query (implA + implB) (Sum.inl t)).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_query_left (t : spec₁.Domain) :
    simulateQ (implA + implB)
      (liftM (spec₁.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₁.Range t)) =
      implB (Sum.inl t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inl t))).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_query_right (t : spec₂.Domain) :
    simulateQ (implA + implB)
      (liftM (spec₂.query t) : OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      implB (Sum.inr t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inr t))).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_comp_base (t : spec.Domain) :
    simulateQ (implA + implB)
      (liftM (liftM (spec.query t) : OracleComp spec (spec.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec.Range t)) =
      implA t :=
  (simulateQ_spec_query (implA + implB) (Sum.inl t)).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_comp_left (t : spec₁.Domain) :
    simulateQ (implA + implB)
      (liftM (liftM (spec₁.query t) : OracleComp spec₁ (spec₁.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec₁.Range t)) =
      implB (Sum.inl t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inl t))).trans rfl

@[simp]
lemma simulateQ_add_add_liftM_comp_right (t : spec₂.Domain) :
    simulateQ (implA + implB)
      (liftM (liftM (spec₂.query t) : OracleComp spec₂ (spec₂.Range t)) :
        OracleComp (spec + (spec₁ + spec₂)) (spec₂.Range t)) =
      implB (Sum.inr t) :=
  (simulateQ_spec_query (implA + implB) (Sum.inr (Sum.inr t))).trans rfl

end QueryImpl

/-! ### Further staged lemmas (mirrored on the VCV-io PR branch 2026-06-12)

Everything below is now ALSO staged on the VCV-io branch
`feat/simulateq-routing-lemmas` (commit `01ff338f`), in some cases generalized
(`ProbComp` → generic monad) — see `ArkLib/ToVCVio/README.md` for the
disposition table and the three rename-at-deletion cases. Delete here at the
first VCVio bump past that branch's merge, after confirming the bump carries
them. -/

/-- `OptionT` companion to `QueryImpl.simulateQ_liftM_eq_of_query`: simulating an
`OracleComp`-computation `oa` lifted into `OptionT (OracleComp spec₂')` (the shape produced by
an `OptionT`-monadic verifier's `let _ ← liftM (queryHelper)` binds) agrees, at the run
(`Option`) level, with `some`-mapping the simulation of `oa` through a per-query-bridged handler
`impl₁`.

The key step is that the `OptionT.run` of a lifted `OracleComp` is `some <$> (the OracleComp
lift)` *definitionally* (`hrun` below is `rfl`), which collapses the `OptionT` lift chain to a
plain `OracleComp` lift; the chain-agnostic `QueryImpl.simulateQ_liftM_eq_of_query` then resolves
it. This lets verifier-body query helpers be routed through a `simOracle2`-style handler even
though their lifts go through the composed `MonadLiftT` instance
`instMonadLiftTOfMonadLift ∘ instMonadLiftOptionTOfOracleQuery`.

Upstream candidate (would sit in VCVio's `SimSemantics/OptionT/Basic.lean`, but needs
`QueryImpl.simulateQ_liftM_eq_of_query` from `SimSemantics/Append.lean`, so upstreaming
requires an import restructure there). -/
lemma simulateQ_optionT_liftM_run_eq_of_query
    {ι₁' ι₂' : Type} {spec₁' : OracleSpec ι₁'} {spec₂' : OracleSpec ι₂'}
    {α : Type} {m' : Type → Type} [Monad m'] [LawfulMonad m']
    [MonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
    [LawfulMonadLiftT (OracleComp spec₁') (OracleComp spec₂')]
    (impl : QueryImpl spec₂' m') (impl₁ : QueryImpl spec₁' m')
    (h : ∀ t, simulateQ impl
      (liftM (liftM (spec₁'.query t) : OracleComp spec₁' (spec₁'.Range t)) :
        OracleComp spec₂' (spec₁'.Range t)) = impl₁ t)
    (oa : OracleComp spec₁' α) :
    simulateQ impl ((liftM oa : OptionT (OracleComp spec₂') α) :
        OracleComp spec₂' (Option α))
      = (some <$> simulateQ impl₁ oa : m' (Option α)) := by
  have hrun : ((liftM oa : OptionT (OracleComp spec₂') α) : OracleComp spec₂' (Option α))
      = some <$> (liftM oa : OracleComp spec₂' α) := rfl
  rw [hrun, simulateQ_map, QueryImpl.simulateQ_liftM_eq_of_query impl impl₁ h oa]


/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₁ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *left* inner implementation `impl₁`, leaving `liftM (simulateQ impl₁ x)`.

This is the `left` half of the `simOracle2`-routing pair: it peels the outer `addLift`
(`simulateQ_add_liftComp_right`), commutes the inner `simulateQ` past the target lift
(`simulateQ_liftTarget`), then peels the inner sum (`simulateQ_add_liftComp_left`). Stated
for the inner pair living in a possibly-different monad `n` lifted into the target `m`
(as `simOracle2`'s `Id`-valued `simOracle0`s are). Candidate for upstreaming to VCVio
next to `QueryImpl.simulateQ_add_liftComp_left`. -/
lemma simulateQ_addLift_add_liftM_left
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {m₀ : Type → Type} [Monad m₀] [LawfulMonad m₀] [MonadLiftT m₀ m] [LawfulMonadLiftT m₀ m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₁ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₁ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_left]

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₂ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *right* inner implementation `impl₂`, leaving `liftM (simulateQ impl₂ x)`.

The `right` companion of `simulateQ_addLift_add_liftM_left`; see that lemma for the
`simOracle2` motivation. -/
lemma simulateQ_addLift_add_liftM_right
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {m₀ : Type → Type} [Monad m₀] [LawfulMonad m₀] [MonadLiftT m₀ m] [LawfulMonadLiftT m₀ m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m₀) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₂ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_right]

/-- Binding a failed `OptionT` computation fails: `failure >>= f = failure`. The `OptionT`
sibling of core's `OptionT.bind_throw`; phrased for the `Alternative`-flavoured `failure`
that `guard`-based protocol verifiers produce. Candidate for upstreaming next to core's
`OptionT.run_failure`. -/
lemma OptionT.failure_bind.{u, v} {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {α β : Type u}
    (f : α → OptionT m β) :
    (failure : OptionT m α) >>= f = failure := by
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_failure, Option.elimM, pure_bind, Option.elim_none]

/-- `simulateQ` maps an `OptionT` `failure` (whose run is the underlying `pure none`) to
`failure`: the `failure` companion of `simulateQ_pure` for `OptionT`-monadic computations.
Both sides are definitionally `pure none`, but the `failure` spelling is what a failed
`guard` rewrites to in a simulated verifier body. -/
lemma simulateQ_optionT_failure
    {ι' α : Type} {spec : OracleSpec ι'} {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl spec n) :
    simulateQ impl ((failure : OptionT (OracleComp spec) α) : OracleComp spec (Option α))
      = (failure : OptionT n α) :=
  simulateQ_pure impl none

/-- Failing companion to `simulateQ_optionT_forIn_yield_pure_some`: if each loop body, under
`simulateQ`, resolves to `pure (some (ForInStep.yield init))` when its per-element condition
`cond a` holds and to `pure none` otherwise, and *some* element of the list fails its
condition, then the whole `OptionT`-monadic `forIn` resolves to `pure none` (the failure
propagates through the remaining `OptionT` binds). Together the two lemmas characterize a
guarded spot-check loop: `pure (some init)` iff every condition holds, `pure none`
otherwise. -/
lemma simulateQ_optionT_forIn_yield_pure_none
    {ι' α β : Type} {spec : OracleSpec ι'} {n : Type → Type} [Monad n] [LawfulMonad n]
    (impl : QueryImpl spec n) (xs : List α) (init : β)
    (body : α → β → OptionT (OracleComp spec) (ForInStep β))
    (cond : α → Prop) [DecidablePred cond]
    (hbody : ∀ a, simulateQ impl ((body a init : OptionT (OracleComp spec) (ForInStep β)) :
        OracleComp spec (Option (ForInStep β)))
      = (pure (if cond a then some (ForInStep.yield init) else none) :
          n (Option (ForInStep β))))
    (hfail : ¬ ∀ a ∈ xs, cond a) :
    simulateQ impl ((forIn xs init body : OptionT (OracleComp spec) β) :
        OracleComp spec (Option β))
      = (pure none : n (Option β)) := by
  rw [simulateQ_optionT_list_forIn]
  induction xs with
  | nil => exact absurd (List.forall_mem_nil _) hfail
  | cons x rest ih =>
      rw [List.forIn_cons]
      by_cases hx : cond x
      · change ((simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
            OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β)) >>= _ :
            OptionT n β) = _
        rw [show (simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
            OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β))
            = (pure (ForInStep.yield init) : OptionT n (ForInStep β)) from by
          rw [hbody x, if_pos hx]; rfl]
        rw [pure_bind]
        exact ih (fun hall ↦ hfail (List.forall_mem_cons.mpr ⟨hx, hall⟩))
      · change ((simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
            OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β)) >>= _ :
            OptionT n β) = _
        rw [show (simulateQ impl ((body x init : OptionT (OracleComp spec) (ForInStep β)) :
            OracleComp spec (Option (ForInStep β))) : OptionT n (ForInStep β))
            = (failure : OptionT n (ForInStep β)) from by
          rw [hbody x, if_neg hx]; rfl]
        rw [OptionT.failure_bind]
        rfl
