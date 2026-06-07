/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# Un-cleared embedding of the iterated-Hasse coefficient (BCIKS20 A.4, issue #139)

`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared` names the **un-cleared** `Y ↦ T` embedding of the
genuine iterated-Hasse coefficient `hasseCoeffRepr𝒪` as `eval₂ liftToFunctionField T p` with
`p = (Δ_X^{i1} Δ_Y^{m} R)|x₀`. This is the sibling of `hasseEvalAtRoot` (the **cleared** `Y ↦ T/W`
evaluation `eval₂ liftToFunctionField (T/W) p`).

Together they make the BCIKS20 Appendix-A.4 STEP-8 obstruction explicit at the `eval₂` level: the
LHS partition form collapses onto `hasseEvalAtRoot` (cleared) while `B_coeff` on the RHS carries
this un-cleared embedding, and the two differ by the `m = |λ|`-dependent `W^{natDegreeY p}` factor
of `embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`. See issue #139 for the obstruction analysis.
-/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- The un-cleared `Y ↦ T` embedding of `hasseCoeffRepr𝒪`: `embed (hasseCoeffRepr𝒪 i1 m)
= eval₂ liftToFunctionField T ((Δ_X^{i1} Δ_Y^{m} R)|x₀)`, the un-cleared sibling of
`hasseEvalAtRoot` (`eval₂ liftToFunctionField (T/W) …`). -/
theorem embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))) := by
  rw [hasseCoeffRepr𝒪, embeddingOf𝒪Into𝕃_mk, liftBivariate_eq_eval₂_functionFieldT]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared
