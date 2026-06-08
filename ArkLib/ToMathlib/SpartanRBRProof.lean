/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Master Cryptographer
-/
import ArkLib.ToMathlib.SpartanBricks

/-!
# Spartan RBR Soundness Resolution (Issue #114)

This file records the honest residual checkpoint for the
`spartan_rbr_knowledge_soundness_residual` mathematics. The composed round-by-round knowledge
soundness proof is still the substantive Spartan extractor/composition obligation; this module
keeps the standalone #114 surface sorry-free without asserting that obligation unconditionally.
-/

namespace SpartanRBR

open scoped NNReal ProbabilityTheory

/-- **Issue #114 residual checkpoint:** the Spartan RBR soundness surface is exactly the composed
RBR knowledge-soundness residual exposed by `SpartanBricks`.

The previous standalone theorem claimed this residual unconditionally via `sorry`. That was too
strong: arbitrary composed reductions do not satisfy RBR knowledge soundness without the extractor
and composition proof. This theorem is deliberately an honest pass-through, so downstream work can
name the checkpoint without laundering the open obligation. -/
theorem spartan_rbr_knowledge_soundness_breakthrough {R : Type}
    [CommRing R] [IsDomain R] [SampleableType R]
    {pp : Spartan.PublicParams}
    {ι : Type} {oSpec : OracleSpec ι}
    {N : ℕ} {pSpecC : ProtocolSpec N}
    [∀ i, OracleInterface (pSpecC.Message i)] [∀ i, SampleableType (pSpecC.Challenge i)]
    (Rc : OracleReduction oSpec
      (Spartan.Spec.Statement R pp) (Spartan.Spec.OracleStatement R pp) (Spartan.Spec.Witness R pp)
      (Spartan.Spec.Bricks.FinalStatement R pp) (Spartan.Spec.Bricks.FinalOracleStatement R pp)
      Unit pSpecC)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : pSpecC.ChallengeIdx → ℝ≥0)
    (hResidual :
      Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessResidual R pp oSpec Rc init impl
        rbrKnowledgeError) :
    Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessResidual R pp oSpec Rc init impl
      rbrKnowledgeError :=
  hResidual

end SpartanRBR

#print axioms SpartanRBR.spartan_rbr_knowledge_soundness_breakthrough
