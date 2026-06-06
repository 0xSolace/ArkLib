import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.LinearizedSupport

noncomputable section
open Polynomial BigOperators Finset
namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

local instance instFintypeSub (W : Submodule F K) : Fintype W := Fintype.ofFinite W

/-- Base case: subFinset ⊥ = {0}. -/
example : subFinset (⊥ : Submodule F K) = {0} := by
  ext x
  simp only [mem_subFinset, Submodule.mem_bot, Finset.mem_singleton]

/-- subspacePoly {0} = X. -/
example : subspacePoly ({0} : Finset K) = X := by
  unfold subspacePoly
  simp

/-- F-homogeneity of the subspace-polynomial evaluation map.
`eval (c • y) (subspacePoly (subFinset W)) = algebraMap c * eval y (...)`
for `c ∈ F`, via reindexing the product `w ↦ c • w` on `W` and `c^{q^v}=c`. -/
example (W : Submodule F K) (c : F) (y : K) :
    (subspacePoly (subFinset W)).eval (c • y)
      = (algebraMap F K c) * (subspacePoly (subFinset W)).eval y := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · -- c = 0: LHS = eval 0 = 0 (since 0 ∈ W), RHS = 0
    rw [zero_smul, map_zero, zero_mul]
    exact subspacePoly_eval_zero _ (by simp [W.zero_mem])
  · -- c ≠ 0: reindex
    have hcdef : ∀ (a : K), c • a = algebraMap F K c * a := fun a => Algebra.smul_def c a
    have hcK_ne : algebraMap F K c ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective F K).ne hc
    have hcard : (subFinset W).card = Fintype.card F ^ (Module.finrank F W) := by
      rw [subFinset]; simp only [Set.toFinset_card]
      exact Module.card_eq_pow_finrank (K := F) (V := W)
    unfold subspacePoly
    rw [eval_prod, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    -- reindex ℓ = c • ℓ' over the bijection ℓ' ↦ c • ℓ' of subFinset W
    have key : ∏ ℓ ∈ subFinset W, (c • y - ℓ)
        = ∏ ℓ' ∈ subFinset W, (c • y - c • ℓ') := by
      refine (Finset.prod_nbij' (fun ℓ' => c • ℓ') (fun ℓ => c⁻¹ • ℓ) ?_ ?_ ?_ ?_ ?_).symm
      · intro ℓ' hℓ'; rw [mem_subFinset] at hℓ' ⊢; exact W.smul_mem _ hℓ'
      · intro ℓ hℓ; rw [mem_subFinset] at hℓ ⊢; exact W.smul_mem _ hℓ
      · intro ℓ' _; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      · intro ℓ _; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      · intro ℓ' _; rfl
    rw [key]
    -- c•y - c•ℓ' = c•(y - ℓ') = algebraMap c * (y - ℓ')
    have hfac : ∀ ℓ' : K, c • y - c • ℓ' = algebraMap F K c * (y - ℓ') := by
      intro ℓ'; rw [← smul_sub, hcdef]
    simp only [hfac]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    -- (algebraMap c)^{q^v} = algebraMap c since c^q = c in F
    have hpow : (algebraMap F K c) ^ (Fintype.card F ^ Module.finrank F W) = algebraMap F K c := by
      rw [← map_pow, FiniteField.pow_card_pow]
    rw [hpow]

end BKR06
