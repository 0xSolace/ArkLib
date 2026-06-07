import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

noncomputable section

open scoped BigOperators
open Finset
open Polynomial Polynomial.Bivariate
open ArkLib.PowerSeriesComposition
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Scratch target for the remaining partition-match step in the P2 lift identity.

This records the obligation without claiming a proof; downstream proof work can target this
proposition or replace it with a theorem once the combinatorial step is discharged. -/
def restrictedFaaDiBrunoPartitionMatchAt_target (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∀ t : ℕ, 1 ≤ t → RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp t

end BCIKS20.HenselNumerator
