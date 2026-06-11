/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.GenuineTruncationFin
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Claim59Vandermonde

/-!
# Claim 5.8′ tail wiring (#302): the truncation capstone feeds the hlin weld's tail input

The hlin weld (`Claim510Weld.natDegree_eq_one_of_heavy_data`) consumes the coefficient
tail `αGenuine t = 0` for `t ≥ k`.  The bridge
(`Claim59Lagrange.alphaGenuine_tail_zero_of_trunc`) converts the genuine truncation
identity into exactly that tail, and the truncation capstone
(`ArkLib.GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc`) produces the identity
from the graded-disc data.  This file is the one-composition weld:

* **`alphaGenuine_tail_zero_of_graded_disc`** — the weld's tail input produced outright
  from the graded-disc package (monic `H`, degree budgets, the vanishing matching-set data,
  the disc cover, and the cardinality leg).

With this, the first of the hlin weld's four inputs is supplied end-to-end; combined with
`Claim510Supply` (the weight bound + the automatic monic pinning), the weld's remaining
genuinely-open input is the **per-place agreement** (Seam B of the frontier map).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open ArkLib BCIKS20.Claim59Lagrange ArkLib.GenuineTruncationFin

namespace BCIKS20.Claim58TailWiring

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **The Claim 5.8′ tail, produced from the graded-disc package**: the truncation capstone
composed with the tail bridge — the hlin weld's first input, end-to-end. -/
theorem alphaGenuine_tail_zero_of_graded_disc {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    {D k : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (hmonic : H.Monic) (hd2 : 2 ≤ Bivariate.natDegreeY R)
    (hdHD : H.natDegree ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hR : ∀ j, Bivariate.degreeX (R.coeff j) ≤ D - j)
    {Ppoly : F[X][Y]}
    (hrepG : polyToPowerSeries𝕃 H Ppoly = gammaGenuine x₀ R H hHyp)
    {matchingSet : Finset F}
    (hvanish : ∀ t, k ≤ t → t ≤ Ppoly.natDegree → ∀ z ∈ matchingSet,
      ∃ r : rationalRoot (H_tilde' H) z, (π_z z r) (βHensel H x₀ R hHyp t) = 0)
    {disc : F[X]} (hdisc : disc ≠ 0)
    (hcover : ∀ z : F, disc.eval z ≠ 0 → z ∈ matchingSet)
    (hbig : gradedCardBudget
        (Bivariate.natDegreeY R) D H.natDegree Ppoly.natDegree
        + disc.natDegree < Fintype.card F) :
    ∀ t, k ≤ t → αGenuine H x₀ R hHyp t = 0 :=
  BCIKS20.Claim59Lagrange.alphaGenuine_tail_zero_of_trunc H hHyp
    (ArkLib.GenuineTruncationFin.gammaGenuine_eq_trunc_of_graded_disc H hHyp hD hH hmonic
      hd2 hdHD hD_Rx0 hR hrepG hvanish hdisc hcover hbig)

end BCIKS20.Claim58TailWiring

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.Claim58TailWiring.alphaGenuine_tail_zero_of_graded_disc
