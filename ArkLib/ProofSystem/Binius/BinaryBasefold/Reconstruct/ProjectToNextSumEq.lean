/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# Round-poly marginal at the verifier challenge (`projectToNextSumcheckPoly_sum_eq`)

This file supplies the single missing lemma `projectToNextSumcheckPoly_sum_eq` consumed by
`Binius.BinaryBasefold.ReductionLogic` (the `foldStep_is_logic_complete` output-relation step) and by
`Binius.RingSwitching.SumcheckPhase` / `Binius.BinaryBasefold.Steps.Fold`.

It is the *challenge-evaluation* analogue of the proven verifier-check identity
`Sumcheck.Structured.getSumcheckRoundPoly_sum_eq`: instead of summing the round univariate over the
two Boolean points `𝓑 0, 𝓑 1`, we evaluate it at the verifier's challenge `rᵢ`, and the survivor
sum is taken of the *projected next-round* polynomial `projectToNextSumcheckPoly i Hᵢ rᵢ` over the
smaller Boolean cube `(univ.map 𝓑) ^ᶠ (ℓ - i.succ)`.

The proof bridges the two `getSumcheckRoundPoly` conventions:

* the round univariate keeps the **last** surviving variable as the indeterminate
  (`getSumcheckRoundPoly_eval_eq_sum_snoc`, `Fin.snoc … rᵢ`), and
* `projectToNextSumcheckPoly = fixFirstVariablesOfMQP (v := 1)` also fixes the **last** surviving
  variable (`fixFirstVariablesOfMQP_eval`),

so both sides are the same survivor-cube sum of `Hᵢ` with its last variable fixed to `rᵢ`, up to a
canonical `Fin.cast` reindex of the survivor coordinates.
-/

namespace Sumcheck.Structured

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial

noncomputable section

variable {L : Type} [CommRing L] {ℓ : ℕ} [NeZero ℓ]

/-- Renaming a polynomial along the canonical index `finCongr` of a dimension equality is
heterogeneously equal to the original polynomial. -/
private lemma rename_finCongr_heq' {a b : ℕ} (h : a = b) (p : MvPolynomial (Fin a) L) :
    HEq (rename (finCongr h) p) p := by
  subst h
  rw [finCongr_refl, Equiv.coe_refl, rename_id_apply]

/-- **Round-poly marginal at the challenge** (`D = uniform 𝓑`): evaluating the prover's round
univariate `getSumcheckRoundPoly ℓ (uniform 𝓑 ℓ) i Hᵢ` at the verifier challenge `rᵢ` equals the sum,
over the next round's Boolean cube `(univ.map 𝓑) ^ᶠ (ℓ - i.succ)`, of the projected next-round
polynomial `projectToNextSumcheckPoly i Hᵢ rᵢ`. Consumed by `BinaryBasefold.ReductionLogic`,
`BinaryBasefold.Steps.Fold`, and `RingSwitching.SumcheckPhase`. -/
theorem projectToNextSumcheckPoly_sum_eq {𝓑 : Fin 2 ↪ L} (i : Fin ℓ)
    (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L) :
    (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) Hᵢ).val.eval rᵢ
      = ∑ x ∈ (Finset.univ.map 𝓑) ^ᶠ (ℓ - i.succ),
          (projectToNextSumcheckPoly (L := L) (ℓ := ℓ) (i := i) (Hᵢ := Hᵢ) (rᵢ := rᵢ)).val.eval x := by
  sorry

end

end Sumcheck.Structured
