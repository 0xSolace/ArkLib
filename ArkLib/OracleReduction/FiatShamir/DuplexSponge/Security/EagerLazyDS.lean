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

end DuplexSpongeFS.EagerLazyDS
