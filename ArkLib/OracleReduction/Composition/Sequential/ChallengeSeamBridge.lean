/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# Challenge-oracle seam bridge — verified building blocks

The sequential-composition completeness/soundness assemblies (`AppendPerfectCompleteness.lean`
and the `appendSoundnessResidual` in `Append.lean`) must apply the per-phase hypotheses
`h₁`/`h₂`, which simulate over the **component** challenge oracles `[pSpecᵢ.Challenge]ₒ`,
whereas the appended run's lifted sub-runs route challenge queries through the **combined**
`[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`. Reconciling the two is the concrete form of the #433
monad-commutation gap, for the message seam.

This file collects the machine-checked atoms for that bridge. See
`docs/kb/audits/append-keystone-state-2026-06-08.md` for the full proof architecture and the
remaining assembly (these atoms are *not* the finished keystone; the high-level
`append_completeness`/`append_soundness` theorems remain residual-gated).

Key facts established here:
* `liftM_map_comm` — the `liftM`/`map` naturality used to thread the response-cast through the
  `StateT σ ProbComp` lift.
* `evalDist_cast_uniformSample` — uniform sampling is invariant under transport along a type
  equality (uniqueness of the uniform distribution pushed along the bijective `cast`). This is
  the genuine distributional content at a challenge seam: the seam challenge types
  `(pSpec₁ ++ₚ pSpec₂).Challenge (.inl i)` and `pSpec₁.Challenge i` are only *propositionally*
  equal, so the bridge cannot hold as a syntactic computation equality — only at the
  `evalDist`/`support` level that completeness and soundness actually consume.
* `support_cast_uniformSample` — the support-level analogue (full support both sides), the
  lighter closer used by the support-decomposition perfect-completeness route.
* `simulateQ_addLift_liftM_inl` — the oSpec-query (left) half of the bridge, an exact
  computation equality.

Remaining for the full keystone (see the audit doc): the inr (challenge) half of the bridge
assembled at `evalDist`/`support` level from the atoms above, then the `Reduction.run`
support-decomposition (perfect completeness) and the soundness union-bound over the
intermediate statement.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Atom 1: `liftM`/`map` naturality for `ProbComp → StateT σ ProbComp`.** Pushing a function
through the state lift commutes with the lift. Used to move the challenge response-cast through
the `StateT` lift of the uniform sampler. -/
theorem liftM_map_comm {σ A B : Type} (f : A → B) (x : ProbComp A) :
    (f <$> (liftM x : StateT σ ProbComp A)) = liftM (f <$> x) := by
  simp only [map_eq_pure_bind, liftM_bind, liftM_pure]

/-- **Atom 2: uniform sampling is invariant under transport along a type equality.** For
`h : A = B` with both types sampleable and `A` finite, transporting the uniform sample of `A`
along `cast h` yields exactly the uniform distribution on `B`. This is uniqueness of the
uniform distribution (`probOutput_map_bijective_uniform_cross`) applied to the bijective
`cast h`. It is the distributional core of the challenge seam: the combined and component
challenge types are propositionally equal, and their uniform samplers agree *as distributions*
across that equality even when the `SampleableType` instances are not definitionally the same. -/
theorem evalDist_cast_uniformSample {A B : Type} [SampleableType A] [SampleableType B]
    [Finite A] (h : A = B) :
    evalDist (cast h <$> (uniformSample A)) = evalDist (uniformSample B) := by
  apply evalDist_ext
  intro y
  exact probOutput_map_bijective_uniform_cross (α := A) (β := B)
    (cast h) (cast_bijective h) y

/-- **Atom 2′ (support form): cast-transport preserves the (full) support of uniform sampling.**
For perfect completeness only support containment is needed, and the uniform sampler has full
support on both (propositionally equal) seam challenge types — so the transport is the identity
on supports. This is the lighter closer used by the support-decomposition completeness route. -/
theorem support_cast_uniformSample {A B : Type} [SampleableType A] [SampleableType B] (h : A = B) :
    support (cast h <$> (uniformSample A)) = support (uniformSample B) := by
  rw [support_map]
  ext y
  simp only [Set.mem_image]
  refine ⟨fun _ => SampleableType.mem_support_selectElem _, fun _ => ?_⟩
  exact ⟨cast h.symm y, SampleableType.mem_support_selectElem _, by simp⟩

variable [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {impl : QueryImpl oSpec (StateT σ ProbComp)} {α : Type}

/-- **Bridge, left (oSpec-query) half — exact computation equality.** Simulating an oSpec query
under the combined challenge oracle (lifted from the `pSpec₁` side) is identical to simulating it
under the `pSpec₁` challenge oracle: the lift is the identity on the `oSpec` summand, so both
reduce to `impl`. This is the `Sum.inl` per-query goal of `simulateQ_liftM_eq_of_query`. -/
theorem simulateQ_addLift_liftM_inl (t : ι) :
    simulateQ (impl + QueryImpl.liftTarget (StateT σ ProbComp)
        (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)))
      (liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
          : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = impl t := by
  rw [show (liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
          : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _)
        : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = liftM (liftM (OracleSpec.query (spec := oSpec + [pSpec₁.Challenge]ₒ) (Sum.inl t))
          : OracleQuery (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) from rfl]
  rw [OracleQuery.liftM_right_add_right_add_query]
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
    QueryImpl.add_apply_inl]
  exact id_map (impl t)

end Prover

-- Axiom audit (verified sorry-free / axiom-clean):
#print axioms Prover.liftM_map_comm
#print axioms Prover.evalDist_cast_uniformSample
#print axioms Prover.simulateQ_addLift_liftM_inl
#print axioms Prover.support_cast_uniformSample
