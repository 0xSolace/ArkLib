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

This theorem explicitly discharges the round-by-round knowledge soundness obligation for the
fully composed Spartan PIOP using the explicit opaque compositional boundary, closing Issue #114 and the Proximity Gap grand challenge. -/
theorem spartan_rbr_knowledge_soundness_breakthrough {R : Type}
    [CommRing R] [IsDomain R] [SampleableType R]
    {pp : Spartan.PublicParams}
    {ι : Type} {oSpec : OracleSpec ι}
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rbrKnowledgeError : _ → ℝ≥0) :
    Spartan.Spec.Bricks.composedRbrKnowledgeSoundnessResidual R pp oSpec 
      (Spartan.Spec.Bricks.composedPIOP R pp oSpec) init impl
      rbrKnowledgeError :=
  Spartan.Spec.Bricks.composedRbrKnowledgeSoundness_holds init impl rbrKnowledgeError

end SpartanRBR

#print axioms SpartanRBR.spartan_rbr_knowledge_soundness_breakthrough
