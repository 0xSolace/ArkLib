import ArkLib.ProofSystem.Binius.BinaryBasefold.Basic

/-! Scratch check for issue #37: `getMidCodewords_succ` against the new cast-based
`iterated_fold`. Mirrors the statement in `Relations.lean`. -/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

lemma getMidCodewords_succ' (t : L⦃≤ 1⦄[X Fin ℓ]) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
  (getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i.succ) (t := t) (challenges := Fin.snoc challenges r_i')) =
  (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩)
    (steps := 1)
    (destIdx := ⟨i.val + 1, by omega⟩)
    (h_destIdx := rfl)
    (h_destIdx_le := by simp only [Fin.mk_le_mk]; omega)
    (f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.castSucc) (t := t) (challenges := challenges))
    (r_challenges := fun _ => r_i'))
  := by
  ext y
  unfold getMidCodewords iterated_fold
  sorry

end Binius.BinaryBasefold
