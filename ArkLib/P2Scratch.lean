import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.ToMathlib.FaaDiBrunoMatchProof

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)

theorem restrictedFaaDiBrunoMatch_proof : RestrictedFaaDiBrunoMatch H x₀ R hHyp := by
  intro t
  sorry
