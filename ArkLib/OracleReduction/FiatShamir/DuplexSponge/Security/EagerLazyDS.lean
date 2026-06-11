/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.LazyPermBridge
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# The combined lazy duplex-sponge oracle (brick 4C-1)

Toward discharging `Lemma5_8EagerPaperResidual` (CO25 Lemma 5.8): the duplex-sponge
challenge oracle `𝒟_𝔖 = (StmtIn →ₒ Vector U C) + permutationOracle (CanonicalSpongeState U)`
has an eager carrier (`D_DS`: one random hash table, one random permutation) and — defined
here — a **combined lazy implementation** with product state:

* the hash arm is VCVio's per-index caching `randomOracle`;
* the permutation arms are the bidirectional memoizing `lazyPermImpl`
  (`ToVCVio/LazyPermBridge.lean`), consuming the spec via `permutationOracle_eq_sumSpec`.

`dsOverlayFn` is the joint cache overlay (the deterministic answer function obtained by
overlaying both caches on the sampled carrier), the eager side of the combined bridge.
The master product-state induction (brick 4C-2) relates the two.
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace DuplexSpongeFS.EagerLazyDS

open LazyPermMarginal LazyPermBridge

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype (CanonicalSpongeState U)]

/-- The joint state of the combined lazy oracle: a per-statement hash cache and the
bidirectional permutation cache. -/
abbrev DSCache (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  (StmtIn →ₒ Vector U SpongeSize.C).QueryCache ×
    List (CanonicalSpongeState U × CanonicalSpongeState U)

/-- The joint cache overlay: answer hash queries through the hash-cache overlay on the
sampled table, and permutation queries through the permutation-cache overlay on the sampled
permutation. The eager answer function of the combined bridge. -/
def dsOverlayFn (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U)) :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range t :=
  fun t => match t with
  | .inl s => OracleComp.tableExtending ch g s
  | .inr (.inl sIn) => permExtending cp π sIn
  | .inr (.inr sOut) => (permExtending cp π).symm sOut

/-- The combined lazy implementation: hash queries through the caching `randomOracle`
(threading the hash cache), permutation queries through `lazyPermImpl` (threading the
permutation cache). -/
noncomputable def lazyDSImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (DSCache StmtIn U) ProbComp) :=
  fun t s =>
    match t with
    | .inl q =>
        (fun (p : Vector U SpongeSize.C × _) => (p.1, (p.2, s.2))) <$>
          (((StmtIn →ₒ Vector U SpongeSize.C).randomOracle q).run s.1)
    | .inr (.inl sIn) =>
        (fun (p : CanonicalSpongeState U × _) => (p.1, (s.1, p.2))) <$>
          ((lazyPermImpl (.inl sIn :
            CanonicalSpongeState U ⊕ CanonicalSpongeState U)).run s.2)
    | .inr (.inr sOut) =>
        (fun (p : CanonicalSpongeState U × _) => (p.1, (s.1, p.2))) <$>
          ((lazyPermImpl (.inr sOut :
            CanonicalSpongeState U ⊕ CanonicalSpongeState U)).run s.2)

@[simp] lemma dsOverlayFn_inl (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    (s : StmtIn) :
    dsOverlayFn ch cp g π (.inl s) = OracleComp.tableExtending ch g s := rfl

@[simp] lemma dsOverlayFn_fwd (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    (sIn : CanonicalSpongeState U) :
    dsOverlayFn ch cp g π (.inr (.inl sIn)) = permExtending cp π sIn := rfl

@[simp] lemma dsOverlayFn_inv (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    (sOut : CanonicalSpongeState U) :
    dsOverlayFn ch cp g π (.inr (.inr sOut)) = (permExtending cp π).symm sOut := rfl

/-! ## Step facts for the master induction -/

/-- Growing the hash cache at an uncached statement is the table update of the overlay
(the permutation arms are untouched). -/
lemma dsOverlayFn_cacheQuery_of_none
    (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    {q : StmtIn} (hq : ch q = none) (u : Vector U SpongeSize.C) :
    dsOverlayFn (ch.cacheQuery q u) cp g π
      = dsOverlayFn ch cp (Function.update g q u) π := by
  funext t
  rcases t with s | sIn | sOut
  · show OracleComp.tableExtending (ch.cacheQuery q u) g s
      = OracleComp.tableExtending ch (Function.update g q u) s
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_update_of_none ch g hq]
  · rfl
  · rfl

/-- The overlay's hash answer at the queried point recovers the cached/updated value. -/
lemma tableExtending_cacheQuery_self
    (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (g : StmtIn → Vector U SpongeSize.C) (q : StmtIn) (u : Vector U SpongeSize.C) :
    OracleComp.tableExtending (ch.cacheQuery q u) g q = u := by
  simp [OracleComp.tableExtending, OracleSpec.QueryCache.cacheQuery]

/-- Two uniform samples commute under any `ProbComp` continuation: both prefixes are
lifted `PMF`s, so the `OptionT` layer collapses and `PMF.bind_comm` applies. -/
lemma evalDist_uniformSample_swap {β γ : Type} [Fintype β] [Nonempty β] [SampleableType β]
    [Fintype γ] [Nonempty γ] [SampleableType γ] {δ : Type}
    (f : β → γ → ProbComp δ) :
    evalDist (do let b ← $ᵗ β; let c ← $ᵗ γ; f b c)
      = evalDist (do let c ← $ᵗ γ; let b ← $ᵗ β; f b c) := by
  classical
  rw [← SPMF.toPMF_inj]
  rw [evalDist_bind, SPMF.toPMF_bind, evalDist_bind, SPMF.toPMF_bind]
  rw [evalDist_uniformSample, evalDist_uniformSample, SPMF.liftM_eq_map, SPMF.liftM_eq_map,
    SPMF.toPMF_mk, SPMF.toPMF_mk]
  rw [show Option.elimM ((PMF.uniformOfFintype β).map some) (PMF.pure none)
      (fun b => (evalDist ($ᵗ γ >>= fun c => f b c)).toPMF)
    = (PMF.uniformOfFintype β).bind
        (fun b => (evalDist ($ᵗ γ >>= fun c => f b c)).toPMF) from by
    rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl]
  rw [show Option.elimM ((PMF.uniformOfFintype γ).map some) (PMF.pure none)
      (fun c => (evalDist ($ᵗ β >>= fun b => f b c)).toPMF)
    = (PMF.uniformOfFintype γ).bind
        (fun c => (evalDist ($ᵗ β >>= fun b => f b c)).toPMF) from by
    rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl]
  have hin : ∀ b, (evalDist ($ᵗ γ >>= fun c => f b c)).toPMF
      = (PMF.uniformOfFintype γ).bind (fun c => (evalDist (f b c)).toPMF) := by
    intro b
    rw [evalDist_bind, SPMF.toPMF_bind, evalDist_uniformSample, SPMF.liftM_eq_map,
      SPMF.toPMF_mk, Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl
  have hin' : ∀ c, (evalDist ($ᵗ β >>= fun b => f b c)).toPMF
      = (PMF.uniformOfFintype β).bind (fun b => (evalDist (f b c)).toPMF) := by
    intro c
    rw [evalDist_bind, SPMF.toPMF_bind, evalDist_uniformSample, SPMF.liftM_eq_map,
      SPMF.toPMF_mk, Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl
  simp only [hin, hin']
  exact PMF.bind_comm _ _ _


/-! ## The overlay, factored through its permutation slot -/

/-- The joint overlay as a function of the (already overlaid) permutation: the shape the
spectatored absorptions consume. -/
def dsOverlayOf (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (g : StmtIn → Vector U SpongeSize.C) (σ : Equiv.Perm (CanonicalSpongeState U)) :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range t :=
  fun t => match t with
  | .inl s => OracleComp.tableExtending ch g s
  | .inr (.inl sIn) => σ sIn
  | .inr (.inr sOut) => σ.symm sOut

lemma dsOverlayFn_eq_overlayOf (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U)) :
    dsOverlayFn ch cp g π = dsOverlayOf ch g (LazyPermBridge.permExtending cp π) := by
  funext t
  rcases t with s | sIn | sOut <;> rfl

section TwoSample

variable {β γ : Type} [Fintype β] [Nonempty β] [SampleableType β]
  [Fintype γ] [Nonempty γ] [SampleableType γ]

/-- `toPMF` of a two-sample-then-pure program, as nested PMF binds with the success tag
outermost on the inner fibre. -/
lemma toPMF_two_sample {α : Type} (F : β → γ → α) :
    (evalDist (do
      let b ← $ᵗ β
      let c ← $ᵗ γ
      pure (F b c) : ProbComp α)).toPMF
      = (PMF.uniformOfFintype β).bind
          (fun b => ((PMF.uniformOfFintype γ).map (F b)).map some) := by
  classical
  rw [evalDist_bind, SPMF.toPMF_bind, evalDist_uniformSample, SPMF.liftM_eq_map,
    SPMF.toPMF_mk]
  rw [show Option.elimM ((PMF.uniformOfFintype β).map some) (PMF.pure none)
      (fun b => (evalDist ($ᵗ γ >>= fun c => pure (F b c) : ProbComp α)).toPMF)
    = (PMF.uniformOfFintype β).bind
        (fun b => (evalDist ($ᵗ γ >>= fun c => pure (F b c) : ProbComp α)).toPMF) from by
    rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl]
  refine congrArg _ (funext fun b => ?_)
  have hprog : ($ᵗ γ >>= fun c => pure (F b c) : ProbComp α) = (F b) <$> ($ᵗ γ) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hprog, evalDist_map, SPMF.toPMF_map, evalDist_uniformSample, SPMF.liftM_eq_map,
    SPMF.toPMF_mk, PMF.monad_map_eq_map, PMF.map_comp, PMF.map_comp]
  rfl

end TwoSample

/-! ## The combined master induction -/

section Master

variable [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
  [Nonempty (StmtIn → Vector U SpongeSize.C)]
  [Nonempty (Equiv.Perm (CanonicalSpongeState U))]
  [Fintype (StmtIn → Vector U SpongeSize.C)]
  [Fintype (Vector U SpongeSize.C)] [Nonempty (Vector U SpongeSize.C)]

set_option maxHeartbeats 3200000 in
/-- **The combined eager–lazy duplex-sponge bridge**: simulating against the combined lazy
oracle (caching hash arm, memoizing bidirectional permutation arms) from duplicate-free
caches has the same distribution as sampling one hash table and one permutation and
answering eagerly through the joint cache overlay. -/
theorem evalDist_simulateQ_lazyDSImpl_run'
    {α : Type} (oa : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (hkeys : (cp.map Prod.fst).Nodup) (hvals : (cp.map Prod.snd).Nodup) :
    evalDist ((simulateQ lazyDSImpl oa).run' (ch, cp))
      = evalDist (do
          let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
          let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
          pure (evalWithAnswerFn (QueryImpl.ofFn (dsOverlayFn ch cp g π)) oa)
          : ProbComp α) := by
  classical
  induction oa using OracleComp.inductionOn generalizing ch cp with
  | pure a =>
    have hlhs : (simulateQ lazyDSImpl (pure a : OracleComp _ α)).run' (ch, cp)
        = (pure a : ProbComp α) := by
      rw [simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, (ch, cp)) : ProbComp (α × _)) = pure a
      rw [map_pure]
    rw [hlhs]
    simp only [evalWithAnswerFn_pure]
    symm
    refine evalDist_ext fun x => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ (StmtIn → Vector U SpongeSize.C)) (by simp),
      one_mul, probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ (Equiv.Perm (CanonicalSpongeState U))) (by simp),
      one_mul]
  | query_bind t k ih =>
    have hred : (simulateQ lazyDSImpl
          (liftM ((duplexSpongeChallengeOracle StmtIn U).query t) >>= k)).run' (ch, cp)
        = ((lazyDSImpl t).run (ch, cp)) >>= fun p =>
            (simulateQ lazyDSImpl (k p.1)).run' p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      change Prod.fst <$> (((lazyDSImpl t).run (ch, cp)) >>= fun p =>
        (simulateQ lazyDSImpl (k p.1)).run p.2) = _
      rw [map_bind]
      rfl
    have heval : ∀ (f : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
          (duplexSpongeChallengeOracle StmtIn U).Range t),
        evalWithAnswerFn (QueryImpl.ofFn f)
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t) >>= k)
          = evalWithAnswerFn (QueryImpl.ofFn f) (k (f t)) := by
      intro f
      rw [evalWithAnswerFn_bind]
      rfl
    rw [hred]
    simp_rw [heval]
    rcases t with q | sIn | sOut
    · -- hash arm
      have hexpose : (lazyDSImpl
            ((.inl q : (duplexSpongeChallengeOracle StmtIn U).Domain))).run (ch, cp)
          = (fun (p : Vector U SpongeSize.C × _) => (p.1, (p.2, cp))) <$>
              (((StmtIn →ₒ Vector U SpongeSize.C).randomOracle q).run ch) := rfl
      rcases hcq : ch q with _ | u
      · -- hash miss
        rw [hexpose, QueryImpl.withCaching_run_none _ hcq, Functor.map_map, bind_map_left]
        have hfib : ∀ u : Vector U SpongeSize.C,
            evalDist ((simulateQ lazyDSImpl (k u)).run' (ch.cacheQuery q u, cp))
            = evalDist (do
                let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
                let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
                pure (evalWithAnswerFn
                  (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π))
                  (k (Function.update g q u q))) : ProbComp α) := by
          intro u
          rw [ih u (ch.cacheQuery q u) cp hkeys hvals]
          refine congrArg evalDist
            (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
          refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
          rw [dsOverlayFn_cacheQuery_of_none ch cp g π hcq u]
          exact congrArg (fun z => (pure (evalWithAnswerFn
            (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π)) (k z))
              : ProbComp α)) (Function.update_self q u g).symm
        rw [evalDist_bind]
        rw [show (fun u => evalDist ((simulateQ lazyDSImpl (k u)).run'
              (ch.cacheQuery q u, cp))) = (fun u => evalDist (do
                let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
                let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
                pure (evalWithAnswerFn
                  (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π))
                  (k (Function.update g q u q))) : ProbComp α)) from funext hfib]
        rw [← evalDist_bind]
        rw [show (($ᵗ (Vector U SpongeSize.C)) >>= fun u => (do
              let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
              let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
              pure (evalWithAnswerFn
                (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π))
                (k (Function.update g q u q))) : ProbComp α))
            = ((do
                let u ← $ᵗ (Vector U SpongeSize.C)
                let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
                pure (Function.update g q u)) >>= fun g' => (do
                  let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
                  pure (evalWithAnswerFn (QueryImpl.ofFn (dsOverlayFn ch cp g' π))
                    (k (g' q))) : ProbComp α)) from by
          simp only [bind_assoc, pure_bind]]
        rw [evalDist_bind, evalDist_uniformSample_bind_update q, ← evalDist_bind]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
        refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
        have : OracleComp.tableExtending ch g q = g q := by
          simp [OracleComp.tableExtending, hcq]
        exact congrArg (fun z => (pure (evalWithAnswerFn
          (QueryImpl.ofFn (dsOverlayFn ch cp g π)) (k z)) : ProbComp α)) this.symm
      · -- hash hit
        rw [hexpose, QueryImpl.withCaching_run_some _ hcq, map_pure, pure_bind]
        rw [ih u ch cp hkeys hvals]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
        refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
        have : OracleComp.tableExtending ch g q = u := by
          simp [OracleComp.tableExtending, hcq]
        exact congrArg (fun z => (pure (evalWithAnswerFn
          (QueryImpl.ofFn (dsOverlayFn ch cp g π)) (k z)) : ProbComp α)) this.symm
    · -- forward permutation arm
      sorry
    · -- inverse permutation arm
      sorry

end Master

end DuplexSpongeFS.EagerLazyDS
/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.evalDist_uniformSample_swap
#print axioms DuplexSpongeFS.EagerLazyDS.dsOverlayFn_cacheQuery_of_none
#print axioms DuplexSpongeFS.EagerLazyDS.toPMF_two_sample
