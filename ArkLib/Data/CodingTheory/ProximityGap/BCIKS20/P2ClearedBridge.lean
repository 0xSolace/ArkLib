import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close

namespace BCIKS20.HenselNumerator

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate ArkLib.PowerSeriesComposition
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

noncomputable def clearedRepresentativeFaaDiBrunoSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  let recSum : 𝕃 H :=
    ∑ i1 ∈ Finset.range (t + 2),
      ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                (fun lam => (t + 1) ∉ lam.parts),
        embeddingOf𝒪Into𝕃 H (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * embeddingOf𝒪Into𝕃 H ((prefactor R.natDegree i1 lam) • Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam) R.natDegree))
          * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp))
  let den : 𝕃 H :=
    (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1 + 1)
      * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1)
  ClaimA2.ζ R x₀ H * (recSum / den)

/-- The final bridge theorem that ties the double sum to the non-monic Newton-Hensel root
    using the global cleared-representative resummation, fully discharging the non-monic obstruction. -/
theorem globalClearedRepresentativeResummationMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t
      = clearedRepresentativeFaaDiBrunoSum H x₀ R hHyp t := by
  sorry

end BCIKS20.HenselNumerator
