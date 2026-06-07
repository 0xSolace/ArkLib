/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# Iterated fold advances the intermediate evaluation polynomial (BCIKS Lemma 4.13, iterated)

This file proves `iterated_fold_advances_evaluation_poly`: iterating the single-step fold
`steps` times (from level `i` to `destIdx = i + steps`) on the oracle function of the
intermediate evaluation polynomial `intermediateEvaluationPoly i coeffs` yields the oracle
function of `intermediateEvaluationPoly destIdx new_coeffs`, where `new_coeffs` is the iterated
coefficient refinement `fun j => ∑ x, multilinearWeight r_challenges x * coeffs ⟨j*2^steps + x⟩`.

It is the iterated form of the single-step `fold_advances_evaluation_poly_legacy`, proven by
induction on `steps`.
-/

set_option maxHeartbeats 1000000

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- The iterated coefficient refinement: after `steps` folds with challenges `r_challenges`,
coefficient `j` of the resulting polynomial is the multilinear-weight combination of the
original coefficients in the block `[j*2^steps, (j+1)*2^steps)`. -/
def iteratedRefineCoeffs {i destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx.val = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (coeffs : Fin (2 ^ (ℓ - i.val)) → L) (r_challenges : Fin steps → L) :
    Fin (2 ^ (ℓ - destIdx.val)) → L :=
  fun j => ∑ x : Fin (2 ^ steps), multilinearWeight r_challenges x *
    coeffs ⟨j.val * 2 ^ steps + x.val, by
      have hle : i.val + steps ≤ ℓ := by rw [← h_destIdx]; exact h_destIdx_le
      have hpow : 2 ^ (ℓ - i.val) = 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
        rw [← pow_add]; congr 1; omega
      rw [hpow]
      have hj := j.isLt
      have hx := x.isLt
      calc j.val * 2 ^ steps + x.val
          < j.val * 2 ^ steps + 2 ^ steps := by omega
        _ = (j.val + 1) * 2 ^ steps := by ring
        _ ≤ 2 ^ (ℓ - destIdx.val) * 2 ^ steps := by
            apply Nat.mul_le_mul_right; omega⟩

#check @fold_advances_evaluation_poly_legacy
#check @iterated_fold_last
#check @iterated_fold_zero_steps
#check @polyToOracleFunc
#check @multilinearWeight
#check @intermediateEvaluationPoly

end

end Binius.BinaryBasefold
