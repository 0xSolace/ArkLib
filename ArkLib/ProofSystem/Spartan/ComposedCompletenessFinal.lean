/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.ComposedCompleteness
import ArkLib.ProofSystem.Spartan.ComposedCompletenessLeaves
import ArkLib.ProofSystem.Spartan.FirstChallengeComplete
import ArkLib.ProofSystem.Spartan.LinearCombinationComplete
import ArkLib.ProofSystem.Spartan.FinalCheckLeafComplete

/-!
# Spartan composed PIOP perfect completeness — final assembly (issue #114)

This file discharges **all five** remaining leaf hypotheses of
`composedCompletenessResidual_of_five_leaves`, yielding the composed Spartan PIOP
perfect-completeness obligation `composedCompletenessResidual` with **no leaf
hypotheses left** — only the standard honest-implementation side conditions
(`NeverFail init`, support-faithfulness, state-preservation, no-failure) remain, exactly
as in every other completeness consumer in the tree.

The honesty-threading relation chain (the design fix for the D1 target-`0` mismatch):

* `h₂` — `firstChallenge_perfectCompleteness`, re-pointed across two seams:
  `firstMessageRelOut ⊆ firstChallengeRelIn` (the `SendSingleWitness` pushforward *is*
  R1CS satisfiability with the witness in the oracle slot) and
  `firstChallengeRelOut = firstSumcheckRelInBF` (definitionally equal `setOf` bodies).
* `h₄` — the parametric `sendEvalClaim_perfectCompleteness` at
  `relIn := firstSumcheckRelOutBF`; its output relation *carries the eval-claim honesty
  conjunct* — the fact that the bundled claim oracle stores `evalClaimValue`.
* `h₅` — the parametric `linearCombination_perfectCompleteness_of`: the RLC round records
  the challenge and passes the (honesty-carrying) relation through unchanged.
* `h₆` — `prependRLCTarget_perfectCompleteness`, re-pointed across
  `linearCombinationRelOutOf (sendEvalClaimRelOut firstSumcheckRelOutBF) ⊆
   prependRLCTargetRelIn` (proved here: the honesty conjunct survives the two pushforwards)
  and the proven D1 inclusion `prependRLCTargetRelOut ⊆ secondSumcheckRelIn`.
* `h₈` — `finalCheck_perfectCompleteness_leaf`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Spartan.Spec.Bricks

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] [VCVCompatible R] (pp : PublicParams)
  {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Seam 1→2:** the `firstMessage` pushforward relation is (an inclusion into) the
`firstChallenge` input relation: membership in `firstMessageRelOut` *is* R1CS satisfiability
with the witness read off the appended oracle slot, which is the defining condition of
`firstChallengeRelIn` (`spartanRelIn` is `@[reducible]`). -/
theorem firstMessageRelOut_subset_firstChallengeRelIn :
    firstMessageRelOut (R := R) pp ⊆ firstChallengeRelIn (R := R) pp :=
  fun _ hx => hx

/-- **Seam 5→6 (the honesty-threading inclusion):** the linear-combination pushforward of the
`sendEvalClaim` output relation (over the bridge-free first-sum-check output) refines the honest
RLC-target input relation: the R1CS conjunct transports verbatim, and the function-level
eval-claim honesty specializes pointwise. -/
theorem linearCombinationRelOutOf_subset_prependRLCTargetRelIn :
    linearCombinationRelOutOf (R := R) pp
        (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
      ⊆ prependRLCTargetRelIn (R := R) pp := by
  rintro x ⟨h1, h2⟩
  exact ⟨h1, fun idx => congrFun h2 idx⟩

/-- **Composed Spartan PIOP perfect completeness, fully discharged (issue #114).**
`composedCompletenessResidual` holds with *no leaf hypotheses*: all eight phase
perfect-completenesses are the in-tree machine-checked theorems, threaded along the
honesty-carrying relation chain. Only the standard honest-implementation side conditions
remain as inputs. -/
theorem composedCompletenessResidual_proven
    (hm : 0 < pp.ℓ_m) (hn : 0 < pp.ℓ_n)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    composedCompletenessResidual R pp oSpec (composedPIOP_Rc pp oSpec) init impl := by
  -- h₂: firstChallenge, re-pointed across the two seams
  have h₂ : (oracleReduction.firstChallenge R pp oSpec).perfectCompleteness init impl
      (firstMessageRelOut (R := R) pp) (firstSumcheckRelInBF (R := R) pp) := by
    have h := firstChallenge_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
      (init := init) (impl := impl)
    exact Reduction.completeness_relIn_mono init impl
      (firstMessageRelOut_subset_firstChallengeRelIn pp) h
  -- h₄: parametric sendEvalClaim leaf at the bridge-free first-sum-check output
  have h₄ := sendEvalClaim_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl) (firstSumcheckRelOutBF (R := R) pp)
  -- h₅: parametric linearCombination leaf at the honesty-carrying relation
  have h₅ := linearCombination_perfectCompleteness_of (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl)
    (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp))
  -- h₆: honest RLC-target adapter, re-pointed across the honesty-threading inclusion
  -- and the proven D1 inclusion into `secondSumcheckRelIn` (defeq `secondSumcheckRelInBF`)
  have h₆ : (prependRLCTarget (R := R) pp oSpec).perfectCompleteness init impl
      (linearCombinationRelOutOf (R := R) pp
        (sendEvalClaimRelOut R pp (firstSumcheckRelOutBF (R := R) pp)))
      (secondSumcheckRelInBF (R := R) pp) := by
    have h := prependRLCTarget_perfectCompleteness (R := R) (pp := pp) (oSpec := oSpec)
      (init := init) (impl := impl)
    have h' := Reduction.completeness_relOut_mono init impl
      (prependRLCTargetRelOut_subset_secondSumcheckRelIn (R := R) pp) h
    exact Reduction.completeness_relIn_mono init impl
      (linearCombinationRelOutOf_subset_prependRLCTargetRelIn pp) h'
  -- h₈: finalCheck leaf
  have h₈ := finalCheck_perfectCompleteness_leaf (R := R) (pp := pp) (oSpec := oSpec)
    (init := init) (impl := impl)
  exact composedCompletenessResidual_of_five_leaves pp oSpec hm hn
    h₂ h₄ h₅ h₆ h₈ hInit hImplSupp himplSP himplNF

end Spartan.Spec.Bricks

-- Axiom checks
#print axioms Spartan.Spec.Bricks.firstMessageRelOut_subset_firstChallengeRelIn
#print axioms Spartan.Spec.Bricks.linearCombinationRelOutOf_subset_prependRLCTargetRelIn
#print axioms Spartan.Spec.Bricks.composedCompletenessResidual_proven
