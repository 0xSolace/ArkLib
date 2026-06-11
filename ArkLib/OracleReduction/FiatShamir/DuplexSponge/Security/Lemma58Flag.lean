/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.EagerLazyDS

/-!
# The ghost-flagged lazy oracle (CO25 Lemma 5.8, the answer-anchored accounting carrier)

The birthday accounting for `EPaper` must anchor every counted collision on the *sampled*
side of the colliding pair, and must order hash entries against permutation entries
*temporally* — information the joint cache `DSCache` cannot recover (a query-side
coincidence with an earlier sampled slot is legitimate adaptive chaining, never a
random event). This file adds the temporal information as a **ghost `Prop` flag**:

* `collisionStep t c ans` — the step from cache `c` on query `t` was *fresh* and its
  sampled answer's capacity hit an existing slot (or its own query's capacity — the
  no-loop self events of CO25 Eqs. 25/26 at `j' = j`);
* `lazyDSImplFlagged` — runs `lazyDSImpl` verbatim and accumulates
  `flag' = flag ∨ collisionStep`; the cache trajectory and all answers are untouched;
* `lazyDSImpl_run_map_flagged` — the forgetting bridge: the plain run is the projection
  of the flagged run, so any probability statement transports;
* `lazyDSImplFlagged_step_size` — the engine's `hstep_size` for the flagged carrier.

The accumulator engine (`probEvent_simulateQ_stateT_le_sum_of_step`) then bounds
`Pr[final flag]` by the Gauss sum, and the support-level correspondence
(`EPaper log → flag`, separate file) closes Lemma 5.8.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace DuplexSpongeFS.EagerLazyDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype (CanonicalSpongeState U)] [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- **The anchored per-step collision event**: the query was fresh (a genuine sample), and
the sampled answer's capacity landed on an existing capacity slot of the cache — or, for
permutation queries, on its own query's capacity (the `j' = j` no-loop disjuncts of CO25
Eqs. 25/26). Query-side coincidences (an adversary choosing a query whose capacity matches
an existing slot) are deliberately *not* events. -/
def collisionStep (t : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (c : DSCache StmtIn U) :
    (duplexSpongeChallengeOracle StmtIn U).Range t → Prop :=
  match t with
  | .inl q => fun u => c.1 q = none ∧ u ∈ slotList c
  | .inr (.inl sIn) => fun b =>
      c.2.find? (fun w => w.1 = sIn) = none ∧
        (b.capacitySegment ∈ slotList c ∨
          b.capacitySegment = sIn.capacitySegment)
  | .inr (.inr sOut) => fun a =>
      c.2.find? (fun w => w.2 = sOut) = none ∧
        (a.capacitySegment ∈ slotList c ∨
          a.capacitySegment = sOut.capacitySegment)

/-- The ghost-flagged lazy combined oracle: run `lazyDSImpl` verbatim and accumulate, as a
`Prop` state component, whether any step so far was an anchored collision. -/
noncomputable def lazyDSImplFlagged :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (DSCache StmtIn U × Prop) ProbComp) :=
  fun t s =>
    (fun (p : _ × DSCache StmtIn U) =>
      (p.1, (p.2, s.2 ∨ collisionStep t s.1 p.1))) <$> (lazyDSImpl t).run s.1

/-- Single-step exposure of the flagged oracle (public; the defeq `show` does not
transport across files). -/
theorem lazyDSImplFlagged_run (t : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (s : DSCache StmtIn U × Prop) :
    (lazyDSImplFlagged t).run s
      = (fun (p : _ × DSCache StmtIn U) =>
          (p.1, (p.2, s.2 ∨ collisionStep t s.1 p.1))) <$> (lazyDSImpl t).run s.1 := rfl

/-- **The forgetting bridge**: the plain lazy run is the state projection of the flagged
run — the ghost flag changes nothing observable. -/
theorem lazyDSImpl_run_map_flagged {α : Type}
    (oa : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (c : DSCache StmtIn U) (fl : Prop) :
    (simulateQ lazyDSImpl oa).run c
      = (fun (p : α × (DSCache StmtIn U × Prop)) => (p.1, p.2.1)) <$>
          (simulateQ lazyDSImplFlagged oa).run (c, fl) := by
  induction oa using OracleComp.inductionOn generalizing c fl with
  | pure a =>
      rw [simulateQ_pure, simulateQ_pure, StateT.run_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
      rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      rw [show (simulateQ lazyDSImpl
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t))).run c
          = (lazyDSImpl t).run c from by
        refine congrArg (fun z => StateT.run z c) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]]
      rw [show (simulateQ lazyDSImplFlagged
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t))).run (c, fl)
          = (lazyDSImplFlagged t).run (c, fl) from by
        refine congrArg (fun z => StateT.run z (c, fl)) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]]
      rw [lazyDSImplFlagged_run t (c, fl)]
      simp only [map_bind]
      refine Eq.trans ?_ (Eq.symm (bind_map_left _ _ _))
      refine congrArg _ (funext fun w => ?_)
      exact ih w.1 w.2 (fl ∨ collisionStep t c w.1)

/-- The engine's `hstep_size` for the flagged carrier: the cache component grows by at
most one per step (the flag is size-free). -/
theorem lazyDSImplFlagged_step_size
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop) :
    ∀ us ∈ support ((lazyDSImplFlagged t).run s),
      dsCacheSize us.2.1 ≤ dsCacheSize s.1 + 1 := by
  intro us hus
  rw [lazyDSImplFlagged_run t s] at hus
  simp only [support_map, Set.mem_image] at hus
  obtain ⟨w, hw, rfl⟩ := hus
  exact lazyDSImpl_step_size t s.1 w hw

/-- The flag is sticky: once set, every reachable successor state keeps it. -/
theorem lazyDSImplFlagged_flag_monotone
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop)
    (hfl : s.2) :
    ∀ us ∈ support ((lazyDSImplFlagged t).run s), us.2.2 := by
  intro us hus
  rw [lazyDSImplFlagged_run t s] at hus
  simp only [support_map, Set.mem_image] at hus
  obtain ⟨w, _, rfl⟩ := hus
  exact Or.inl hfl

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImpl_run_map_flagged
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_size
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_flag_monotone
