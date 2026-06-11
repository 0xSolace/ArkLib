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

end DuplexSpongeFS.EagerLazyDS
/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.evalDist_uniformSample_swap
#print axioms DuplexSpongeFS.EagerLazyDS.dsOverlayFn_cacheQuery_of_none
#print axioms DuplexSpongeFS.EagerLazyDS.toPMF_two_sample
