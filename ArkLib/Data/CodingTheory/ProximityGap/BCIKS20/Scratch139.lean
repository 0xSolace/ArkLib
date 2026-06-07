import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.RestrictedFaaDiBrunoExtract

noncomputable section
open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- When `H` is monic (`H.leadingCoeff = 1`), the explicit order-zero full-clearing difference sum
`∑_{i ≤ R.natDegree} C (p.coeff i · (lc^{R.natDegree − i} − 1)) · X^i` is identically zero, because
every mismatch factor `lc^{R.natDegree − i} − 1 = 1 − 1 = 0`. -/
theorem zeroClearingPolyFull_sub_eq_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hlc : H.leadingCoeff = 1) :
    (∑ i ∈ Finset.range (R.natDegree + 1),
        Polynomial.C
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
            * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
      = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [hlc, one_pow, sub_self, mul_zero, map_zero, zero_mul]

/-- **Order-zero STEP-8 core, unconditional for monic `H` (axiom-clean).** When `H` is monic, the
mismatch factors `lc^{d−i} − 1` all vanish, so the explicit difference sum is `0 ∈ ⟨H_tilde' H⟩`,
and the carved order-zero core `RestrictedFaaDiBrunoMatchAt … 0` holds for EVERY `R` with
`2 ≤ R.natDegree` satisfying `ClaimA2.Hypotheses`. This is the genuine monic specialization of the
order-zero match: no global resummation is needed because there is no `W`-power weighting to
resum. -/
theorem restrictedMatchAt_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [restrictedMatchAt_zero_iff_zeroClearingPolyFull_sub_mem H x₀ R hHyp hd,
    zeroClearingPolyFull_sub_eq_zero_of_leadingCoeff_one H x₀ R hlc]
  exact Ideal.zero_mem _

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_sub_eq_zero_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_of_leadingCoeff_one
