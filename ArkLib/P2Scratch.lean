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

/-- Historical scratch proposition for the unrestricted P2 match statement.

Current P2 progress proves the monic/cleared variants; this unrestricted proposition is retained
only as a non-asserting `Prop`, not as a theorem target to close as stated. -/
def restrictedFaaDiBrunoMatch_unrestricted_status : Prop :=
  RestrictedFaaDiBrunoMatch H x₀ R hHyp
