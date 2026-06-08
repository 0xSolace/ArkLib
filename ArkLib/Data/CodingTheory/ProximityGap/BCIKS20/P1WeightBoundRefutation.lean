/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P1MonicIntegrality

/-!
# BCIKS20 Appendix A.4 (P1) — weight-bound obstruction for unconstrained lift direction (#138)

Scratch landing zone for testing whether the remaining `Λ_𝒪 ≤ 1` claim follows from the current
two-field `ClaimA2.Hypotheses`.
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]

#check Polynomial.irreducible_X
#check Polynomial.natDegree_X
#check Polynomial.separable_X
#check ClaimA2.Hypotheses
#check AlphaWeight.AlphaGenuineRegularWeightLe

end BCIKS20.HenselNumerator
