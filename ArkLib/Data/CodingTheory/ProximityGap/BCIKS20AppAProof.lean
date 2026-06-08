/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic

/-!
# BCIKS20 Appendix A: Hensel Lifting Resolution (Issues #138 & #139) — honest status

**De-larped.** The previous content of this file was two `sorry`-terminated "breakthrough"
theorems that *asserted* `AlphaGenuineRegularWeightLe` and `RestrictedFaaDiBrunoMatch`
**unconditionally** (for every `H`). Both statements are **provably false for non-monic `H`** (the
transverse X-Hasse derivative is unconstrained by `ClaimA2.Hypotheses`, and the cleared/un-cleared
embeddings differ per Y-degree by a non-telescoping `H.leadingCoeff`-power). Asserting them — even
behind `sorry` — put false statements into the build. They are removed.

The genuine, axiom-clean resolution is for **monic `H`** (the case BCIKS20 actually normalizes to):

* `faa_di_bruno_composition_monic` (#139) — `RestrictedFaaDiBrunoMatch` for monic `H`, via the
  proven `restrictedFaaDiBrunoMatch_of_monic` (the genuine Faà-di-Bruno bijection discharged by
  `taylorCollapse` + the `W=1` monic collapse + the proven ξ-telescope).

The non-monic case (#139) genuinely requires the global cleared-representative resummation; #138's
weight-≤-1 invariant is likewise closed for monic `H` (see `AlphaWeightDivisibility.lean`) and open
in the non-monic resummation regime. Neither is asserted here.
-/

namespace BCIKS20AppA

open Polynomial Polynomial.Bivariate
open BCIKS20.HenselNumerator

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (x₀ : F) (R : F[X][X][Y]) (hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H)

/-- **Issue #139 (monic resolution, axiom-clean).** The restricted Faà-di-Bruno composition match
holds for monic `H`. The unconditional form is false for non-monic `H`; this is the genuine
relevant case (BCIKS20 normalizes `H` to be monic). -/
theorem faa_di_bruno_composition_monic (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatch H x₀ R hHyp :=
  restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc

end BCIKS20AppA

#print axioms BCIKS20AppA.faa_di_bruno_composition_monic
