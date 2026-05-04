/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova
-/

import ArkLib.Data.CodingTheory.ProximityGap.ProximityGenerators
import Mathlib.Data.Rat.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib

/-!
# Proximity Generators fundamental definitions

Define the fundamental concepts for different types of generators functions used in coding theory.

## Main Results



## References

* [Guruswami, V., Rudra, A., Sudan M., *Essential Coding Theory*, online copy][GRS25]
* [Bordage, S., Chiesa, A., Guan, Z., Manzur, I., *All Polynomial Generators Preserve Distance
with Mutual Correlated Agreement*][BSGM25]. Full paper : https://eprint.iacr.org/2025/2051}
-/

section

namespace LinearTransformations

open NNReal ENNReal unitInterval LinearCode CoreDefinitions
open scoped ProbabilityTheory

variable {ι : Type} [Fintype ι]
         {F : Type} [Field F]
         {ℓ ℓ' : Type} [Fintype ℓ] [Fintype ℓ']
         {S : Type}

def hasPseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) : Prop :=
 ∃ B : Matrix ℓ' ℓ F, B * A = 1

-- noncomputable def pseudoInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) (hA : hasPseudoLeftInverse A) :
--   Matrix ℓ' ℓ F := Classical.choose hA

def isPseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) : Prop :=
    B * A = 1

lemma pseudoLeftInverse [DecidableEq ℓ'] (A : Matrix ℓ ℓ' F)
  (hA : IsUnit (A.transpose * A).det) :
  isPseudoLeftInverse A ((A.transpose * A)⁻¹ * A.transpose) := by
  unfold isPseudoLeftInverse
  simp only [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ hA

/-- Generator `G'` inside Lemma 4.1 [BSGM25] -/
def pseudoInvNewGen [DecidableEq ℓ'] {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
(A : Matrix ℓ ℓ' F) : Generator S ℓ' F := fun x ↦ Matrix.vecMul (G x) A

/-- Generator `G'` inside Corollary 4.2 [BSGM25] -/
def projectedGenerator {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (κ : Set ℓ) :
  Generator S κ F := fun x ↦ Set.restrict κ (G x)


/-- Compose a word family `U : ℓ' → (ι → F)` with a matrix `A : Matrix ℓ ℓ' F` to get
a word family indexed by `ℓ`. Entry `i` of the result is `∑ j, A i j • U j`. -/
def composeWords (A : Matrix ℓ ℓ' F) (U : ℓ' → (ι → F)) : ℓ → (ι → F) :=
  fun i k => ∑ j : ℓ', A i j * U j k

omit [Fintype ι] in
/-! ### IsMCA implication for pseudoInvNewGen -/
/-- `vecMul (pseudoInvNewGen G A x) U = vecMul (G x) (composeWords A U)`. -/
lemma vecMul_pseudoInvNewGen [DecidableEq ℓ']
    {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (A : Matrix ℓ ℓ' F) (U : ℓ' → (ι → F)) (x : S) :
    Matrix.vecMul (pseudoInvNewGen G A x) U = Matrix.vecMul (G x) (composeWords A U) := by
  ext i
  simp only [Matrix.vecMul, dotProduct, composeWords, pseudoInvNewGen, Matrix.vecMul, dotProduct,
  mul_comm, Finset.mul_sum, mul_left_comm]
  exact Finset.sum_comm

/-- If every word in a family lies in the projected code, then any `F`-linear combination also
lies in the projected code. -/
lemma projectedCode_linearCombination (LC : LinearCode ι F) (T : Finset ι) {α : Type}
    [Fintype α] (U : α → (ι → F)) (c : α → F)
    (hU : ∀ j, projectedWord (U j) T ∈ projectedCode LC.carrier T) :
    projectedWord (fun k => ∑ j, c j * U j k) T ∈ projectedCode LC.carrier T := by
  obtain ⟨w, hw⟩ : ∃ w ∈ LC, ∀ t ∈ T, w t = ∑ j, c j * U j t := by
    choose! w hw using hU
    use ∑ j, c j • w j
    exact ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hw j |>.1),
      fun t ht => by simp [show ∀ j, U j t = w j t from
        fun j => congr_fun (hw j |>.2) ⟨t, ht⟩]⟩
  exact ⟨w, hw.1, funext fun t => by simpa using Eq.symm (hw.2 t t.2)⟩

/-- If `IsMCA` holds for `pseudoInvNewGen G A` with words `U`, then `IsMCA` holds
for `G` with the composed words `composeWords A U`. The proof is by contrapositive on the
"some column is outside the projected code" clause, using that `U = B * (A * U)`
(from `B * A = 1`) and closure of the projected code under linear combinations. -/
lemma isMCA_pseudoInvNewGen_of_isMCA [DecidableEq ℓ'] (LC : LinearCode ι F)
    {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
    (A : Matrix ℓ ℓ' F) (B : Matrix ℓ' ℓ F) (hBA : B * A = 1)
    (U : ℓ' → (ι → F)) (γ : I) (x : S) :
    IsMCA (pseudoInvNewGen G A) LC x U γ → IsMCA G LC x (composeWords A U) γ := by
  rintro ⟨T, hT_card, hT_proj, j, hj⟩
  generalize_proofs at *
  refine ⟨T, hT_card, ?_, ?_⟩
  · convert hT_proj using 1
    ext i
    simp only [pseudoInvNewGen, Matrix.vecMul_vecMul]
    congr! 2
  · contrapose! hj
    convert projectedCode_linearCombination LC T (fun i => composeWords A U i)
      (fun i => B j i) (fun i => hj i) using 1
    ext k
    simp [composeWords]
    simp only [← Matrix.mul_apply]
    simp [← Matrix.mul_assoc, hBA]


/-- Monotonicity of probability: if `P x → Q x` for all `x`, then
`Pr_{x ←$ᵖ S}[P x] ≤ Pr_{x ←$ᵖ S}[Q x]`. -/
lemma prob_mono {S : Type} [Nonempty S] [Fintype S] (P Q : S → Prop) (h : ∀ x, P x → Q x) :
    Pr_{let x ←$ᵖ S}[P x] ≤ Pr_{let x ←$ᵖ S}[Q x] := by
  simp only [bind_pure_comp, Functor.map, PMF.bind_apply, PMF.uniformOfFintype_apply,
    Function.comp_apply, PMF.pure_apply, eq_iff_iff, true_iff, mul_ite, mul_one, mul_zero,
    tsum_fintype] at *
  gcongr; aesop

/-- Lemma 4.1 [BSGM25] -/
lemma pseudoinverseGen [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hG : IsMCAGenerator G ε_mca LC) (A : Matrix ℓ ℓ' F) (hA : hasPseudoLeftInverse A) :
IsMCAGenerator (pseudoInvNewGen G A) ε_mca LC := by
  obtain ⟨B, hB⟩ := hA
  intro U γ
  exact le_trans (prob_mono _ _ fun x h => isMCA_pseudoInvNewGen_of_isMCA LC G A B hB U γ x h)
    (hG (composeWords A U) γ)

open Classical in
/-- Zero-extend a word family `U : κ → (ι → F)` to `ℓ → (ι → F)`. -/
noncomputable def zeroExtend (κ : Set ℓ) (U : κ → (ι → F)) : ℓ → (ι → F) :=
fun i => if h : i ∈ κ then U ⟨i, h⟩ else 0

omit [Fintype ι] in
/-- `vecMul` over a subset equals `vecMul` over the full type with zero-extended words. -/
lemma vecMul_neSubsetGen {S : Type} [Nonempty S] [Fintype S]
    (G : Generator S ℓ F) (κ : Set ℓ) [Fintype κ]
    (U : κ → (ι → F)) (x : S) :
    Matrix.vecMul (projectedGenerator G κ x) U = Matrix.vecMul (G x) (zeroExtend κ U) := by
  ext i
  simp only [Matrix.vecMul, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ (Set.toFinset κ))]
  · refine Finset.sum_bij (fun j _ => j) ?_ ?_ ?_ ?_ <;>
      simp +decide [projectedGenerator, zeroExtend]
  · intro x _ hx; simp [zeroExtend]; aesop


omit [Fintype ι] [Fintype ℓ] in
/-- `zeroExtend κ U j.val = U j` for `j : κ`. -/
lemma zeroExtend_val (κ : Set ℓ) (U : κ → (ι → F)) (j : κ) :
    zeroExtend κ U j.val = U j := by
  simp [zeroExtend, j.property]

/-- If `IsMCA` holds for the subset generator with words `U`, then `IsMCA` holds for `G` with the
zero-extended words. -/
lemma isMCA_neSubsetGen_of_isMCA (LC : LinearCode ι F)
    {S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F)
    (κ : Set ℓ) [Fintype κ]
    (U : κ → (ι → F)) (γ : I) (x : S) :
    IsMCA (projectedGenerator G κ) LC x U γ → IsMCA G LC x (zeroExtend κ U) γ := by
  rintro ⟨T, hT₁, hT₂, j, hT₃⟩
  exact ⟨T, hT₁,
    by convert hT₂ using 1; exact funext fun _ => by simp [vecMul_neSubsetGen],
    ⟨j, by rwa [zeroExtend_val]⟩⟩


/-- Corollary 4.2 [BSGM25]-/
lemma generatorSubset [DecidableEq ℓ']
{S : Type} [Nonempty S] [Fintype S] (G : Generator S ℓ F) (ε_mca : I → I) (LC : LinearCode ι F)
(hG : IsMCAGenerator G ε_mca LC) (κ : Set ℓ) :
  IsMCAGenerator (projectedGenerator G κ) ε_mca LC := by
  intro U γ
  exact le_trans (prob_mono _ _ fun x h => isMCA_neSubsetGen_of_isMCA LC G κ U γ x h)
    (hG (zeroExtend κ U) γ)

end LinearTransformations

end
