import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MonicWfreeRange

/-!
# Issue #138 scratch: direct monic closure of W-free surfaces

These wrappers consume the already-proved monic carved match
`restrictedFaaDiBrunoMatch_of_monic` and project it onto the named W-free and range-W-free
surfaces.  They do not prove the remaining P1 successor divisibility core.
-/

noncomputable section

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem RestrictedFaaDiBrunoWfreeMatch.of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoWfreeMatch H x₀ R hHyp :=
  RestrictedFaaDiBrunoWfreeMatch.of_restrictedMatch H x₀ R hHyp hlc
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc)

theorem RestrictedFaaDiBrunoRangeWfreeMatch.of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoRangeWfreeMatch H x₀ R hHyp :=
  RestrictedFaaDiBrunoRangeWfreeMatch.of_WfreeMatch H x₀ R hHyp
    (RestrictedFaaDiBrunoWfreeMatch.of_leadingCoeff_one H x₀ R hHyp hlc)

theorem RestrictedFaaDiBrunoRangeWfreeMatchAt.of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoRangeWfreeMatchAt H x₀ R hHyp t :=
  (RestrictedFaaDiBrunoRangeWfreeMatch.of_leadingCoeff_one H x₀ R hHyp hlc) t

theorem WfreeForm_eq_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) (hlc : H.leadingCoeff = 1) :
    restrictedFaaDiBrunoPartitionForm H x₀ R hHyp t =
      restrictedMatchRecursionPartitionWfreeForm H x₀ R hHyp t :=
  (RestrictedFaaDiBrunoWfreeMatch.of_leadingCoeff_one H x₀ R hHyp hlc) t

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoWfreeMatch.of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatch.of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoRangeWfreeMatchAt.of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.WfreeForm_eq_of_leadingCoeff_one
