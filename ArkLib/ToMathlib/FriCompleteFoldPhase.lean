/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriCompleteFinalRound
import ArkLib.OracleReduction.Composition.Sequential.SeqComposePerfectCompletenessChallengeThreaded

/-!
# FRI: folding-phase perfect completeness — toward discharging the Brick D residual

This module assembles the FRI folding-phase completeness from the per-round legs
(`foldRoundPerfectCompletenessResidual_holds`, `finalFoldRoundPerfectCompletenessResidual_holds`)
via the n-ary challenge-seam `seqCompose` keystone
(`OracleReduction.seqCompose_perfectCompleteness_challenge_threaded`).

Assembly plan (see the campaign notes): (i) `perfectCompleteness` is monotone in the output
relation (`perfectCompleteness_mono_relOut` below); (ii) the round relations chain through the
`j`-indexed family `foldChainRel` (the proximity + witness-binding clauses of
`FoldPhase.inputRelation`, generic in the round index); (iii) each round's output relation
entails the next round's input relation (forgetting the folding-consistency clause);
(iv–vi) the keystone application and the final binary challenge-seam append.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- **`perfectCompleteness` is monotone in the output relation** (for plain reductions).
If every output in `relOut` is also in `relOut'`, perfect completeness w.r.t. `relOut`
implies perfect completeness w.r.t. `relOut'`. Candidate for upstreaming to
`OracleReduction/Security/Basic.lean`. -/
theorem _root_.Reduction.perfectCompleteness_mono_relOut
    {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {σ' : Type} {init' : ProbComp σ'} {impl' : QueryImpl oSpec (StateT σ' ProbComp)}
    {StmtIn WitIn StmtOut WitOut : Type} {m : ℕ} {pSpec : ProtocolSpec m}
    [∀ j, SampleableType (pSpec.Challenge j)]
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (hsub : relOut ⊆ relOut')
    (h : R.perfectCompleteness init' impl' relIn relOut) :
    R.perfectCompleteness init' impl' relIn relOut' := by
  intro stmtIn witIn hmem
  refine le_trans (h stmtIn witIn hmem) ?_
  refine probEvent_mono ?_
  rintro ⟨⟨_, prvOut, witOut⟩, stmtOut⟩ _ ⟨hrel, hagree⟩
  exact ⟨hsub hrel, hagree⟩

/-- **Oracle-level output-relation monotonicity for `perfectCompleteness`.** Definitionally the
`toReduction` statement of `Reduction.perfectCompleteness_mono_relOut`. -/
theorem _root_.OracleReduction.perfectCompleteness_mono_relOut
    {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {σ' : Type} {init' : ProbComp σ'} {impl' : QueryImpl oSpec (StateT σ' ProbComp)}
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ j, OracleInterface (OStmtIn j)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {m : ℕ} {pSpec : ProtocolSpec m}
    [∀ j, OracleInterface (pSpec.Message j)]
    [∀ j, SampleableType (pSpec.Challenge j)]
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {relIn : Set ((StmtIn × ∀ j, OStmtIn j) × WitIn)}
    {relOut relOut' : Set ((StmtOut × ∀ j, OStmtOut j) × WitOut)}
    (hsub : relOut ⊆ relOut')
    (h : R.perfectCompleteness init' impl' relIn relOut) :
    R.perfectCompleteness init' impl' relIn relOut' :=
  Reduction.perfectCompleteness_mono_relOut hsub h

end Fri.Spec.Completeness

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Reduction.perfectCompleteness_mono_relOut
#print axioms OracleReduction.perfectCompleteness_mono_relOut
