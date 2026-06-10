import ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic

namespace Binius.BinaryBasefold.CoreInteraction
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Sumcheck.Structured
open Binius.BinaryBasefold
open scoped NNReal

universe u v

theorem scratch_cast_fun_cast_arg_apply {α β : Type u} {γ : Type v} {hαβ : α = β}
    {hfun : (α → γ) = (β → γ)} (f : β → γ) (x : β) :
    cast hfun (fun y : α => f (cast hαβ y)) x = f x := by
  subst hαβ
  cases hfun
  rfl

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section CommitStep

variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

set_option maxHeartbeats 5000000 in
omit [CharP L 2] [SampleableType L] in
private lemma scratch_snoc_oracle_eq_mkVerifierOStmtOut_commitStep_apply
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (h_transcript_eq : transcript.messages ⟨0, rfl⟩ = newOracle)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ)) :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle j =
      OracleVerifier.mkVerifierOStmtOut (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
        (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript j := by
  dsimp only [snoc_oracle]
  simp only [hCR, ↓reduceDIte]
  have h_count_succ :
      toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    simp only [toOutCodewordsCount_succ_eq, hCR, ↓reduceIte]
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · have h_embed : (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j =
        Sum.inl ⟨j.val, hj⟩ := by
      simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
        commitStepLogic_embedFn, hj, dif_pos]
    rw [OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ h_embed]
    simp only [hj, dif_pos, eqRec_eq_cast, cast_cast]
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ (oStmtIn ⟨j.val, hj⟩)).symm
    have hidx : (⟨j.val, by omega⟩ :
        Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) = ⟨j.val, hj⟩ := by
      ext
      rfl
    cases hidx
    rfl
  · have h_embed : (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j =
        Sum.inr ⟨0, rfl⟩ := by
      simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
        commitStepLogic_embedFn, hj, dif_neg, not_false_eq_true]
      rfl
    rw [OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ h_embed]
    simp only [hj, dif_neg, not_false_eq_true]
    have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
      have h_lt := j.isLt
      conv_rhs at h_lt => rw [h_count_succ]
      omega
    have h_j_mul : j.val * ϑ = i.val + 1 := by
      rw [h_j_eq]
      exact toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i hCR
    have h_i_succ_lt_r : i.val + 1 < r := by
      have hRpos : 0 < 𝓡 := Nat.pos_of_neZero 𝓡
      have hi_le : i.val + 1 ≤ ℓ := Nat.succ_le_of_lt i.isLt
      omega
    have h_j_mul_lt_r : j.val * ϑ < r := by
      rw [h_j_mul]
      exact h_i_succ_lt_r
    have h_domain_j :
        ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨j.val * ϑ, h_j_mul_lt_r⟩) =
          ↥(sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, h_i_succ_lt_r⟩) := by
      have h_fin : (⟨j.val * ϑ, h_j_mul_lt_r⟩ : Fin r) =
          ⟨i.val + 1, h_i_succ_lt_r⟩ := by
        apply Fin.eq_of_val_eq
        exact h_j_mul
      exact congrArg (fun idx => ↥(sDomain 𝔽q β h_ℓ_add_R_rate idx)) h_fin
    rw [h_transcript_eq]
    funext y
    dsimp only [commitStepLogic, commitStepHEq, commitStepLogic_embed, commitStepLogic_embedFn,
      Function.Embedding.coeFn_mk, OracleStatement, pSpecCommit, Message]
    simp only [hj, dif_neg, not_false_eq_true, eqRec_eq_cast, cast_cast]
    simpa using (scratch_cast_fun_cast_arg_apply (hαβ := h_domain_j) (f := newOracle) y)

end CommitStep
end
end Binius.BinaryBasefold.CoreInteraction
