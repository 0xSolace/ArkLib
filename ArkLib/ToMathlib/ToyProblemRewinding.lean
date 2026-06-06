/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Rewinding knowledge soundness for the toy IOR: axiom audit & usage

This module sits *downstream* of the toy-problem spec files and serves two purposes:

1. **Axiom audit.** It re-checks (via `#print axioms`) that the rewinding-extractor content — the
   2×2 solve `toySolve`, its correctness `toySolve_combine`, the 2-special-soundness theorem
   `toyRewindingExtractor_twoSpecialSound`, and the fully-proven framework witness
   `protocol62_knowledgeSoundnessViaRewinding` — depends on **no** `sorry` and **no** project-level
   axiom (only Lean's standard `propext`/`Classical.choice`/`Quot.sound`).

2. **Usage demonstration.** It shows the proven rewinding witness driving the framework's
   operational guarantee `Extractor.knowledgeSoundnessViaRewinding.extracts`: whenever a malicious
   prover beats the 2-special-sound knowledge error `1/|F|` at a recorded prefix, a witness in the
   relaxed relation `R̃²_{C,δ}` is extractable — *for free* from the proven 2-special-soundness, no
   re-derivation.

## Where the actual content lives

The concrete rewinding extractor for ABF26 Construction 6.2 / 6.9 and the reductions of the three
knowledge-soundness holes to their named bridge residuals live in the owned spec files:

* `ArkLib/ProofSystem/ToyProblem/Spec/General.lean` —
  `toyCombine`, `toySolve`, `toySolve_combine`, `toyRewindingExtractor`, `toyAccepts`,
  `toyRewindingExtractor_twoSpecialSound`, `protocol62_knowledgeSoundnessViaRewinding`, and the
  bridge-reduced `protocol62_knowledgeSound` (L6.6) / `protocol62_rbrKnowledgeSound` (L6.8).
* `ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean` —
  the bridge-reduced `simplifiedIOR_knowledgeSound` (L6.10).

The abstract framework consumed by all of the above is
`ArkLib/ToMathlib/RewindingExtractor.lean`.

## References

* [Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*][ABF26] §6
* [Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive Proofs*][AFK22]
-/

noncomputable section

open scoped NNReal ENNReal

namespace ToyProblem.Spec

open Extractor

variable {ι F : Type} [Fintype ι] [Field F]
variable {k : ℕ}

/-- **Operational extraction guarantee for the toy IOR (proven).** A malicious prover that, at a
recorded prefix `pre`, beats the 2-special-sound knowledge error `1/|F|` over fresh combination
randomness `γ` yields an extractable witness in the relaxed relation `R̃²_{C,δ}`.

This is the framework's `knowledgeSoundnessViaRewinding.extracts` instantiated at the *proven* toy
witness `protocol62_knowledgeSoundnessViaRewinding`. It demonstrates the rewinding predicate is
usable end-to-end, not an inert interface: the witness is produced with no `sorry` and no axiom
beyond Lean's standard kernel axioms. -/
theorem toyProtocol_extracts [Fintype F] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F))
    (pre : ToyPrefix ι F k) (resp : F → (Fin k → F))
    (hwin : (Fintype.card F : ENNReal)⁻¹ <
        Pr_{ let r ← $ᵖ F }[toyAccepts (ι := ι) (F := F) (k := k) C δ decode pre (r, resp r)]) :
    ∃ (E : RewindingExtractor (ToyPrefix ι F k) F (Fin k → F) (Witness (F := F) k))
      (c₁ c₂ : Completion F (Fin k → F)),
      (toyStmtOf (ι := ι) (F := F) (k := k) pre, E pre c₁ c₂)
        ∈ outputRelation (ι := ι) (F := F) k C δ :=
  knowledgeSoundnessViaRewinding.extracts
    (protocol62_knowledgeSoundnessViaRewinding C δ decode) pre resp hwin

end ToyProblem.Spec

/-! ## Axiom audit

Each `#print axioms` below must report only Lean's standard kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) — i.e. **no** `sorryAx` and **no** project-level
axiom in the rewinding-extractor content or the framework witness. -/

-- 2×2 solve and its correctness (pure field algebra):
#print axioms ToyProblem.Spec.toySolve
#print axioms ToyProblem.Spec.toySolve_combine

-- 2-special-soundness of the concrete toy rewinding extractor:
#print axioms ToyProblem.Spec.toyRewindingExtractor_twoSpecialSound

-- The fully-proven framework witness (the rewinding-flavoured knowledge soundness):
#print axioms ToyProblem.Spec.protocol62_knowledgeSoundnessViaRewinding

-- The operational extraction guarantee in this file:
#print axioms ToyProblem.Spec.toyProtocol_extracts
