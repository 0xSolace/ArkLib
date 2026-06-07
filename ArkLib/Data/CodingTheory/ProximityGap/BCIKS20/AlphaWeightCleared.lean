/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight

/-!
# Cleared base wrappers for the BCIKS20 Appendix-A weight invariant

`AlphaWeight.lean` contains the corrected order-zero cleared predicates. This small companion keeps
fixed-base convenience wrappers out of that near-cap file.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace AlphaWeight

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Package the proved beta-side base weight bound into the corrected cleared div-weight
predicate. -/
theorem DivWeightLe_zero_cleared.of_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  DivWeightLe_zero_cleared.of_betaWeight H x₀ R hHyp hH
    (βHensel_zero_weight_le_one H x₀ R hHyp hH hd hD)

/-- Standalone spelling of the corrected cleared div-weight base witness. -/
theorem divWeight_zero_cleared_fixed
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (hd : 2 ≤ H.natDegree) {D : ℕ} (hD : D ≤ H.natDegree) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D :=
  DivWeightLe_zero_cleared.of_fixed H x₀ R hHyp hH hd hD

/-- Div-weight-oriented symmetry for the corrected cleared base alpha/div-weight equivalence. -/
theorem divWeight_zero_cleared_iff_alphaWeight_zero_cleared
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) (D : ℕ) :
    DivWeightLe_zero_cleared H x₀ R hHyp hH D ↔
      AlphaGenuineRegularWeightLe_zero_cleared H x₀ R hHyp hH D :=
  (alphaWeight_zero_cleared_iff_divWeight_zero_cleared H x₀ R hHyp hH D).symm

end AlphaWeight
end BCIKS20.HenselNumerator

namespace BCIKS20.HenselNumerator.AlphaWeight

#print axioms DivWeightLe_zero_cleared.of_fixed
#print axioms divWeight_zero_cleared_fixed
#print axioms divWeight_zero_cleared_iff_alphaWeight_zero_cleared

end BCIKS20.HenselNumerator.AlphaWeight
