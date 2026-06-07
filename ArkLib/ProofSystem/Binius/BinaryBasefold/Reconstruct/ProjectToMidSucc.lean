/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Structured
import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# Round-transition recursion for the projected sumcheck polynomial (`projectToMidSumcheckPoly_succ`)

`projectToMidSumcheckPoly_succ` relates `projectToMidSumcheckPoly` at round `i.succ` to
`projectToNextSumcheckPoly` applied to `projectToMidSumcheckPoly` at round `i.castSucc`.
Consumed by `Binius.BinaryBasefold.ReductionLogic` (the fold-step witness structural invariant)
and `Binius.RingSwitching.SumcheckPhase`.
-/

open MvPolynomial Finset RingSwitching

namespace Sumcheck.Structured

variable {L : Type} [CommRing L]

/-- **Round-transition recursion for the projected sumcheck polynomial.**
Advancing the projected round polynomial from round `i.castSucc` to round `i.succ` by folding in
the verifier challenge `r_i'` (via `projectToNextSumcheckPoly`) equals directly projecting at round
`i.succ` with the challenge vector extended by `Fin.snoc`. -/
theorem projectToMidSumcheckPoly_succ (ℓ : ℕ) [NeZero ℓ] (t m : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (r_i' : L) :
    projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i')
      = projectToNextSumcheckPoly ℓ i (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i' := by
  sorry

end Sumcheck.Structured
