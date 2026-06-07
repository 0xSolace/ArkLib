/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# `projectToMidSumcheckPoly` at the last round — evaluation

This file supplies `Sumcheck.Structured.projectToMidSumcheckPoly_at_last_eval`, the
final-round evaluation of the projected sumcheck polynomial.

At round `i = Fin.last ℓ`, `projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges` is the
result of fixing **all** `ℓ` variables of the initial round polynomial `m · t` to the accumulated
challenges. The surviving variable set is `Fin (ℓ - ℓ) = Fin 0`, so the polynomial is a constant.
Evaluating it at the (only) `0`-variate point reproduces `(m · t)(challenges)`, i.e.
`m(challenges) * t(challenges)`.

This is the bridge consumed by the final-sumcheck-step completeness proofs in
`Binius.BinaryBasefold.ReductionLogic`, `Binius.RingSwitching.SumcheckPhase`, and
`Binius.FRIBinius.CoreInteractionPhase`.
-/

namespace Sumcheck.Structured

open MvPolynomial

/-- **Evaluation of `projectToMidSumcheckPoly` at the last round (`i = Fin.last ℓ`).**

The fully-projected round polynomial (all `ℓ` variables fixed to `challenges`) evaluates, at the
`0`-variate point, to the product of the multiplier and the witness multilinear, each evaluated at
the accumulated challenges. -/
theorem projectToMidSumcheckPoly_at_last_eval {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
    (t m : MultilinearPoly L ℓ) (challenges : Fin (Fin.last ℓ) → L) :
    (projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges).val.eval (fun _ => 0)
      = m.val.eval challenges * t.val.eval challenges := by
  rw [RingSwitching.projectToMidSumcheckPoly_eq_fixVars]
  rw [RingSwitching.fixFirstVariablesOfMQP_eval, MvPolynomial.eval_mul]
  -- The recombined evaluation point coincides with `challenges` on all `Fin ℓ` indices, because the
  -- last-`ℓ` variables are *all* the variables: the `finSumFinEquiv` split always lands on the
  -- `Sum.inr` (fixed) side.
  have hpt : (fun i => Sum.elim (fun _ : Fin (ℓ - (Fin.last ℓ).val) => (0 : L)) challenges
      (((finCongr (by rw [Nat.add_comm]; exact (Nat.add_sub_of_le (Fin.last ℓ).is_le).symm)).trans
        (finSumFinEquiv (m := ℓ - (Fin.last ℓ).val) (n := (Fin.last ℓ).val).symm)) i))
      = challenges := by
    funext i
    -- Classify the index of the equiv: with `ℓ - ℓ = 0`, the left summand is empty, so the
    -- `finSumFinEquiv.symm` always returns `Sum.inr`.
    rw [RingSwitching.finSumFinEquiv_symm_dite]
    simp only [Fin.val_last, Nat.sub_self, finCongr_apply, Fin.coe_cast]
    rw [dif_neg (by omega)]
    simp only [Sum.elim_inr]
    congr 1
    apply Fin.ext
    simp only [Fin.val_last, Nat.sub_zero, Nat.sub_self]
  rw [hpt]
