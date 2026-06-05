import ArkLib.ProofSystem.Whir.MCAJohnsonMutualExtract
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Matrix.Mul

/-! # Curve mutual extraction (general-parℓ MCA, Vandermonde inversion)

The degree-`(parℓ−1)` curve generalization of `affineLine_mutual_extract`
(which is the `parℓ = 2` case): for the Reed–Solomon power generator
`r = (1, α, …, α^{parℓ−1})`, if a word stack `f` has, at `parℓ` distinct slopes
`αs i`, proximate codewords `c i` agreeing with the combination
`∑ⱼ (αs i)ʲ · fⱼ` on a common set `S`, then the ENTIRE stack `f` is recovered as
a codeword tuple `p` on `S` — by inverting the (invertible, distinct-node)
Vandermonde system. This is the joint interleaved-code proximate the general-parℓ
mutual correlated agreement asserts. -/

namespace MCAJohnson

open Polynomial Matrix Finset

variable {F : Type*} [Field F] {ι : Type*} (domain : ι ↪ F)

/-- **Curve mutual extraction.** With `parℓ` distinct slopes and degree-`<deg`
proximates of the power-generator combinations agreeing on `S`, the whole word
stack is a codeword tuple on `S`. -/
theorem curve_mutual_extract {parℓ : ℕ} {deg : ℕ}
    (αs : Fin parℓ → F) (hα : Function.Injective αs)
    (c : Fin parℓ → F[X]) (hc : ∀ i, c i ∈ Polynomial.degreeLT F deg)
    (f : Fin parℓ → ι → F) {S : Finset ι}
    (h : ∀ x ∈ S, ∀ i, (c i).eval (domain x) = ∑ j : Fin parℓ, (αs i) ^ (j : ℕ) * f j x) :
    ∃ p : Fin parℓ → F[X], (∀ j, p j ∈ Polynomial.degreeLT F deg) ∧
      ∀ x ∈ S, ∀ j, (p j).eval (domain x) = f j x := by
  classical
  set V : Matrix (Fin parℓ) (Fin parℓ) F := Matrix.vandermonde αs with hV
  have hdet : V.det ≠ 0 := by
    rw [hV]; exact (Matrix.det_vandermonde_ne_zero_iff).mpr hα
  have hVunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hdet
  -- the recovered polynomials: p j = ∑ i, (V⁻¹) j i • c i
  refine ⟨fun j => ∑ i, V⁻¹ j i • c i, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hc i))
  · intro x hx j
    -- eval distributes over the finite F-linear combination
    have hpe : (∑ i, V⁻¹ j i • c i).eval (domain x)
        = ∑ i, V⁻¹ j i * (c i).eval (domain x) := by
      rw [Polynomial.eval_finset_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.eval_smul, smul_eq_mul])
    rw [hpe]
    -- the Vandermonde system: c·eval = V *ᵥ (f · x), so V⁻¹ *ᵥ (c·eval) = f · x
    set cv : Fin parℓ → F := fun i => (c i).eval (domain x) with hcv
    set fv : Fin parℓ → F := fun j => f j x with hfv
    have hsys : cv = V *ᵥ fv := by
      funext i
      rw [hcv, hfv, Matrix.mulVec, hV]
      simp only [Matrix.vandermonde, Matrix.of_apply, dotProduct]
      exact h x hx i
    -- f j x = (V⁻¹ *ᵥ cv) j
    have hrec : fv = V⁻¹ *ᵥ cv := by
      rw [hsys, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul V hVunit, Matrix.one_mulVec]
    have : (∑ i, V⁻¹ j i * cv i) = fv j := by
      have := congrFun hrec j
      rw [Matrix.mulVec, dotProduct] at this
      exact this.symm
    rw [hcv] at this
    exact this

end MCAJohnson
