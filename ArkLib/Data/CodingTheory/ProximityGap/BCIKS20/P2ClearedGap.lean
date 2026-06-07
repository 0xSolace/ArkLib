/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb

/-!
# BCIKS20 Appendix A.4 — order-zero P2 obstruction as a cleared/uncleared representative gap (#139)

`P2Reabsorb` reduces the fixed order-zero partition residual to the cleared-vs-uncleared
obstruction `hasseEvalAtRoot 1 0 = embedding(hasseCoeffRepr𝒪 1 0) / W ^ R.natDegree`
(`restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree`).

This module takes that obstruction one step further and pins it to the **proven** cleared
embedding bridge `hasseEvalAtRoot_mul_W_pow_eq_embedding_cleared`
(`embedding ⟦cleared⟧ = W ^ natDegreeY p · hasseEvalAtRoot`).  Under the Y-degree match
`natDegreeY p = R.natDegree` and the legitimate `ζ`/`W` cancellation hypotheses, the order-zero
residual is *exactly* the equality of the two `𝒪`-representatives' images in `𝕃`:

`RestrictedFaaDiBrunoPartitionMatchAt 0 ↔ embedding (hasseCoeffRepr𝒪 1 0)
    = embedding (mk (hasseCoeffRepr𝒪_cleared 1 0))`.

Since `embedding (hasseCoeffRepr𝒪 1 0) = ∑ᵢ lift(pᵢ) · Tⁱ` (the `Y ↦ T` lift) while
`embedding (mk (hasseCoeffRepr𝒪_cleared 1 0)) = ∑ᵢ lift(pᵢ) · W ^ (d - i) · Tⁱ` (with
`d = natDegreeY p`), the whole remaining order-zero content is the single identity
`∑ᵢ lift(pᵢ) · (1 - W ^ (d - i)) · Tⁱ = 0` in `𝕃 = F[X][Y] ⧸ ⟨H̃'⟩`.  Only the top term
(`i = d`) cancels termwise; the lower terms vanish only through the minimal-polynomial relation
`H̃'(T) = 0` (`T` is algebraic), so this is the genuine field-theoretic residue, not a uniform
`W`-scaling.  See issue #139.

NO `axiom`/`admit`/`native_decide`/`sorry`. Audited in-file via `#print axioms`.
-/

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Order-zero P2 residual ⟺ cleared/uncleared representative gap.**  Under the Y-degree match
`natDegreeY p = R.natDegree` (`p = evalX (C x₀) (Δ_X¹ Δ_Y⁰ R)`) and the legitimate
`2 ≤ R.natDegree`, `ζ ≠ 0` cancellation hypotheses, the fixed order-zero partition residual is
exactly the equality, in
`𝕃`, of the un-cleared iterated-Hasse representative's image with the (proven) cleared
representative's image.  This isolates the entire remaining order-zero content to the single
algebraic identity `embedding (mk p) = embedding (mk (W-cleared p))`, which holds only via the
minimal-polynomial relation `H̃'(T) = 0`, never by a uniform per-term `W`-scaling. -/
theorem t0_residual_iff_uncleared_emb_eq_cleared_emb
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hdeg : Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) = R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0)) := by
  rw [restrictedPartitionMatchAt_zero_iff_hasseEvalAtRoot_eq_single_B_coeff H x₀ R hHyp,
      restrictedMatchRecursionPartitionFormZeroSingleBCoeff_eq_unclearedHasseCoeff_div_W_natDegree
        H x₀ R hHyp hd hζ]
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hbridge :
      hasseEvalAtRoot H x₀ R 1 0
          * liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree
        = embeddingOf𝒪Into𝕃 H
            (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
              (hasseCoeffRepr𝒪_cleared H x₀ R 1 0)) := by
    rw [← hdeg]
    exact hasseEvalAtRoot_mul_W_pow_eq_embedding_cleared H x₀ R 1 0
  constructor
  · intro h
    rw [← hbridge, h, div_mul_cancel₀ _ (pow_ne_zero _ hW)]
  · intro h
    rw [h, ← hbridge, mul_div_assoc, div_self (pow_ne_zero _ hW), mul_one]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.t0_residual_iff_uncleared_emb_eq_cleared_emb
