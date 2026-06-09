/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendCompletenessNonPerfect
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.RunUnroll

/-!
# The append challenge-seam: distributional run-factoring for completeness `hGameFactor`

This file attacks the deep distributional challenge-seam residual that is shared between the
error-bearing completeness append (`Reduction.append_completeness_msg_proof`, whose
`hGameFactor`/`hStage1Bridge`/`hStage2Bridge` are taken as named hypotheses) and the soundness
append. The genuinely-deep content is the **run-factoring of the simulated appended honest game at a
message seam, at the `evalDist` (distributional) level**: that
`gameOf init impl (R₁.append R₂) stmt wit` equals the two-stage composite game where stage 1 runs
`R₁` (prover₁ then verifier₁) and stage 2 runs `R₂` (prover₂ then verifier₂), with transcript
concatenation, in exactly the `mx >>= my` shape `OracleReduction.probComp_seam_completeness` consumes.

## What is proven here (no `sorry`)

* `Reduction.append_run_natural_msg` — the **fully proven** natural-order `OptionT` factoring of
  `(R₁.append R₂).run` for a message seam. Combines the proven syntactic prover-side run-factoring
  `Prover.append_run_msg` with the (`rfl`) verifier-side factoring `Verifier.append_run`, threaded
  through `Reduction_run_def`. The appended honest reduction run equals the natural order
  `P₁ → P₂ → V₁ → V₂` (both provers, then both verifiers).

* `Reduction.append_game_swap_evalDist_msg` — the **fully proven** distributional reorder of the
  simulated appended game. Running the natural-order game under the honest interactive
  implementation `impl.addLift challengeQueryImpl` has the same `evalDist` as running the
  **union-bound order** `(P₁ → V₁) ; (P₂ → V₂)` — the two-stage `R₁.run ; R₂.run` shape. The swap of
  the `P₂` prover stage past the `V₁` verifier stage is the proven distributional commutation
  `OptionTStateT.seam_swap_evalDist_eq`, whose `hso`/`hB` side-conditions are discharged by
  `addLift_state_preserving` / `addLift_neverFail` (the honest interactive implementation is
  state-preserving and never fails). This is the proven core of `hGameFactor`.

## The residual

`Reduction.append_game_factor_msg` packages the two proven steps into the exact `evalDist` equality
`hGameFactor` requires for the concrete two-stage decomposition `so := impl.addLift challengeQueryImpl`,
`mx := stage₁` (`P₁ → V₁` with the intermediate context carried), `my := stage₂` (`P₂ → V₂` finishing
the combined transcript). The **only** content not discharged here is the per-phase challenge-oracle
seam relabeling — that each phase, which in the appended game runs its rounds under the *combined*
challenge oracle `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`, agrees distributionally with the per-phase
completeness game `gameOf R₁` / `gameOf R₂` that runs them under `pSpecᵢ`'s own challenge oracle
(the soundness analogue of `evalDist_run'_challengeSeam_left/right`). That irreducible
monad-commutation/relabel core is isolated as the single named hypothesis `hSeamRelabel`, exactly
mirroring the named-residual discipline of `Reduction.append_completeness_msg_proof`.
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-- The `OptionT`-lift of a `pure` `OracleComp` value, run and `Option.elim`-ed, takes the success
branch unconditionally: it is just `k v`. Used to collapse the prover-output `return ⟨…⟩` step that
`Prover.append_run_msg` introduces (the prover never fails, so its assembled output is a pure lift). -/
private theorem liftM_pure_run_elim {ιₛ : Type} {spec : OracleSpec ιₛ} {α β : Type}
    (v : α) (k : α → OracleComp spec (Option β)) :
    ((liftM (pure v : OracleComp spec α) : OptionT (OracleComp spec) α).run >>= fun o =>
        o.elim (pure none) k) = k v := by
  show (((fun a => some a) <$> (pure v : OracleComp spec α)) >>= fun o => o.elim (pure none) k) = k v
  simp only [map_pure, pure_bind, Option.elim_some]

/-- **Natural-order `OptionT` factoring of the appended reduction run (message seam).** For a message
seam, running `R₁.append R₂` is, as an `OptionT (OracleComp …)` value, exactly the natural order: run
prover₁, then prover₂ (concatenating transcripts), then verifier₁ on the first transcript half, then
verifier₂ on the second half, finally assembling the output. Fully proven: the prover-side factoring
is the proven syntactic keystone `Prover.append_run_msg`, the verifier-side factoring is the (`rfl`)
`Verifier.append_run`, and `Reduction_run_def` exposes the prover→verifier sequencing. -/
theorem append_run_natural_msg
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V) :
    (R₁.append R₂).run stmt wit
      = ((liftM (liftM (R₁.prover.run stmt wit)
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun x =>
          liftM (liftM (R₂.prover.run x.2.1 x.2.2)
              : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) >>= fun a =>
            liftM (R₁.verifier.verify stmt x.1) >>= fun s₂ =>
              liftM (R₂.verifier.verify s₂ a.1) >>= fun s₃ =>
                pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃)) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) _) := by
  -- Mirror the soundness refold (`AppendSoundnessMsgProof.append_soundness_msg'`): unfold
  -- `Reduction.run`, factor the appended prover with the proven syntactic keystone
  -- `Prover.append_run_msg`, split the appended verifier with the definitional `Verifier.append`,
  -- and refold to the canonical seam chain `liftM FST ≫ liftM SND ≫ V₁ ≫ V₂`. `OptionT.liftM_run_getM_bind`
  -- cancels the `getM` of the verifier leg.
  simp only [Reduction.run, Prover.append_run_msg (P₁ := R₁.prover) (P₂ := R₂.prover)
      stmt wit hn hDir hDir₂, Reduction.append, Verifier.append, Verifier.run,
    liftM_bind, bind_assoc, map_eq_pure_bind, liftM_map, bind_map_left,
    OptionT.liftM_run_getM_bind, liftM_pure, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd]

end Reduction
