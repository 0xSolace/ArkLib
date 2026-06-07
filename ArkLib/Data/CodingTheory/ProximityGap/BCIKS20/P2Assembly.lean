/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Match
import ArkLib.ToMathlib.Polynomial.HasseDerivEval

/-!
# BCIKS20 Appendix A.4 — assembling `RestrictedFaaDiBrunoMatch` (issue #9, P2)

This file assembles the *proven* P2 pieces into the carved core `RestrictedFaaDiBrunoMatch`:

  LHS  (`restrictedFaaDiBrunoSum_eq_partitionForm`, proven)  — partition form;
  RHS  `-ζ · coeff(t+1)(βHenselAssembled)`  — expand via the assembled-series def + `βHensel_succ`;
  glue: (★) `Polynomial.hasseDeriv_eval_eq_sum`, `prefactor = countPerms`, the W/ξ exponent
        telescopes, and `partitionProd_coeff_assembled`.

Landed incrementally; each lemma compiles standalone against the (heavy) P2 import chain.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open ArkLib.PowerSeriesComposition Finset

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Assembly step A (def unfold).** The `(t+1)`-coefficient of the assembled series is the
embedded `βHensel (t+1)` over the `W/ξ` clearing denominator. Pure `βHenselAssembled` def +
`PowerSeries.coeff_mk`. -/
theorem coeff_succ_βHenselAssembled (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (t + 1))
          / ((liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)) := by
  rw [βHenselAssembled, PowerSeries.coeff_mk]

/-- **Assembly step B (recursion in `𝕃`).** Pushing the ring-hom `embeddingOf𝒪Into𝕃` through the
`(A.1)` recursion `βHensel_succ`: the embedded successor coefficient is the negated double sum of
the embedded recursion terms, with `embedding` distributed over the `W/ξ/B_coeff/partitionProd`
product. -/
theorem embedding_βHensel_succ (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (k : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp (k + 1))
      = - ∑ i1 ∈ Finset.range (k + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - i1))).filter
                    (fun lam => (k + 1) ∉ lam.parts),
            (embeddingOf𝒪Into𝕃 H (W𝒪 H)) ^ (i1 + deltaSave i1 - 1)
              * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * i1 + sigmaLambda lam - 2)
              * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
              * embeddingOf𝒪Into𝕃 H (partitionProd lam
                  (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) := by
  rw [βHensel_succ, map_neg, map_sum]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun i1 _ => ?_))
  rw [map_sum]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  rw [map_mul, map_mul, map_mul, map_pow, map_pow]

end BCIKS20.HenselNumerator
