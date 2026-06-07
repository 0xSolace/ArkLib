/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Assembly
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Reabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.UnclearedEmbedding

/-!
# Quantitative extraction / base-case API for the carved P2 core (BCIKS20 A.4, issue #139)

Infrastructure around `RestrictedFaaDiBrunoMatch` — the #139 analogue of #138's clearing-product
divisibility/quotient API. Every consequence lemma takes the (unproven) combinatorial core
`RestrictedFaaDiBrunoMatchAt` only as an explicit hypothesis (using just the proven `ζ ≠ 0`),
exactly as the in-tree P2 consequence theorems do — none assumes the STEP-8 core.

* `coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt` / `restrictedMatchAt_of_…` /
  `restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq` — the carved core at order `t` is *exactly*
  the normalized-quotient coefficient equation `coeff (t+1) βHenselAssembled = −rFdBSum t / ζ`.
* `coeff_succ_βHenselAssembled_eq_of_restrictedMatch` — the all-orders consumer.
* `restrictedFaaDiBrunoSum_zero_eq_powerSum` — the `t = 0` base case of the raw STEP-1 defect sum.
* `neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree` /
  `coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree_div_ζ` — the order-zero
  recursion side alone gives a closed form for the first successor coefficient.
* `RestrictedMatchAtZeroTaylorWDivTarget` — the fixed order-zero core as the exact equality of the
  root-side Taylor sum and the un-cleared Taylor sum divided by `W ^ R.natDegree`.
* `RestrictedMatchAtZeroEval₂WDivTarget` — the same fixed order-zero target in compact `eval₂`
  form, before expanding either side into Taylor sums.
* `restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget` — direct bridge between the compact
  `eval₂` target and the expanded Taylor-sum target.
* `restrictedMatchAtZeroEval₂WDivTarget_iff_uncleared{Eval₂,}WDivTarget` — identifies the fixed
  order-zero target with the general un-cleared/W-divisor target at `(i1,m,e)=(1,0,R.natDegree)`.
* `restrictedMatchAt_zero_iff_uncleared{Eval₂,}WDivTarget` and the partition-at-zero analogues —
  direct iff packaging between the order-zero residual surfaces and the general W-divisor targets.
* `HasseCoeffRepr𝒪Uncleared{Eval₂,}WDivTarget.of_…` / partition target constructors — endpoint
  adapters between the generalized order-zero W-divisor target and the carved / partition residuals.
* `RestrictedMatchAtZero{Taylor,Eval₂}WDivTarget.of_…` / `RestrictedFaaDiBrunoPartitionMatchAt`
  target constructors — endpoint adapters between the order-zero targets and the full carved /
  normalized partition residual surfaces.
* `embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_wDivTarget` — converts a generalized
  W-divisor target into the exact cleared-vs-un-cleared representative scaling relation, with
  order-zero carved / partition specializations.
* `restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_lift` — exposes the same explicit
  polynomial-lift obstruction on the normalized partition-residual surface, with constructors and
  projections for the carved and partition order-zero endpoints.
* `hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_iff_zeroClearingPolyFull_lift` — composes
  the reabsorbed un-cleared-over-`W^R.natDegree` endpoint with the zero-clearing lift identity.
* `embeddingCleared_eq_Wpow_mul_uncleared_of_target` — makes the cleared/un-cleared `eval₂` mismatch
  *quantitative*: under the STEP-8 target, the two `𝒪`-reps differ by exactly `W^{natDegreeY p}`.
-/

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

/-- **Quantitative coefficient extraction from the carved P2 core (consequence, axiom-clean).**
Given `RestrictedFaaDiBrunoMatchAt t` and the genuine separability non-vanishing `ζ ≠ 0`, the
`(t+1)` coefficient of `βHenselAssembled` is `−restrictedFaaDiBrunoSum t / ζ`.
#139 analogue of #138's `divWeight_quotient_unique`: the unproven combinatorial core is taken
only as a hypothesis. -/
theorem coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H := by
  unfold RestrictedFaaDiBrunoMatchAt at hmatch
  rw [hmatch, neg_neg, mul_comm, mul_div_assoc, div_self (ζ_ne_zero H x₀ R hHyp), mul_one]

/-- **Converse of the quantitative extraction (axiom-clean).** The explicit coefficient equation
implies the carved single-order core `RestrictedFaaDiBrunoMatchAt t` (again only using `ζ ≠ 0`). -/
theorem restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hcoeff : PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t := by
  unfold RestrictedFaaDiBrunoMatchAt
  rw [hcoeff, mul_div_assoc', mul_comm (ClaimA2.ζ R x₀ H),
    mul_div_assoc, div_self (ζ_ne_zero H x₀ R hHyp), mul_one, neg_neg]

/-- **The carved core at order `t` is exactly the normalized-quotient coefficient equation.** -/
theorem restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp t ↔
      PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
        = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  ⟨coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp t,
    restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq H x₀ R hHyp t⟩

/-- **All-orders quantitative coefficient extraction (axiom-clean).** From the full carved core
`RestrictedFaaDiBrunoMatch`, every successor coefficient of the assembled numerator series is the
normalized quotient `−restrictedFaaDiBrunoSum t / ζ`. -/
theorem coeff_succ_βHenselAssembled_eq_of_restrictedMatch (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) (t : ℕ) :
    PowerSeries.coeff (t + 1) (βHenselAssembled H x₀ R hHyp)
      = -restrictedFaaDiBrunoSum H x₀ R hHyp t / ClaimA2.ζ R x₀ H :=
  coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp t (hmatch t)

/-- **Order-zero base case of the raw restricted Faà-di-Bruno sum (axiom-clean).** The un-normalized
STEP-1 defect sum collapses at `t = 0` to the single surviving Taylor power-sum over the `Y`-degree
of `Q` — the raw sibling of `restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum`. -/
theorem restrictedFaaDiBrunoSum_zero_eq_powerSum (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 =
      ∑ i ∈ Finset.range ((Q x₀ R H).natDegree + 1),
        (liftToFunctionField (H := H)
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i))
        * (PowerSeries.coeff 0 (βHenselAssembled H x₀ R hHyp)) ^ i := by
  rw [restrictedFaaDiBrunoSum_eq_restrictedPartitionForm H x₀ R hHyp 0,
    restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum H x₀ R hHyp]

/-- **Order-zero raw sum after reabsorbing the surviving power-sum (axiom-clean).** The raw
restricted Faà-di-Bruno sum at `t = 0` is exactly the cleared root evaluation
`hasseEvalAtRoot ... 1 0`. -/
theorem restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    restrictedFaaDiBrunoSum H x₀ R hHyp 0 = hasseEvalAtRoot H x₀ R 1 0 := by
  rw [restrictedFaaDiBrunoSum_zero_eq_powerSum H x₀ R hHyp,
    ← restrictedFaaDiBrunoPartitionZeroPowerSum_eq_hasseEvalAtRoot H x₀ R hHyp]
  rfl

/-- **Order-zero quantitative coefficient extraction (axiom-clean).** The carved P2 core at
order zero gives the base successor coefficient equation directly in terms of `hasseEvalAtRoot`. -/
theorem coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H := by
  simpa [restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot H x₀ R hHyp] using
    coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt H x₀ R hHyp 0 hmatch

/-- **Converse order-zero quantitative extraction (axiom-clean).** The base coefficient equation
with the reabsorbed LHS `hasseEvalAtRoot` implies the carved order-zero core. -/
theorem restrictedMatchAt_zero_of_coeff_one_βHenselAssembled_eq
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hcoeff :
      PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
        = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  apply restrictedMatchAt_of_coeff_succ_βHenselAssembled_eq H x₀ R hHyp 0
  simpa [restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot H x₀ R hHyp] using hcoeff

/-- **Order-zero carved core iff the reabsorbed base coefficient equation.** -/
theorem restrictedMatchAt_zero_iff_coeff_one_βHenselAssembled_eq
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
        = -hasseEvalAtRoot H x₀ R 1 0 / ClaimA2.ζ R x₀ H :=
  ⟨coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero H x₀ R hHyp,
    restrictedMatchAt_zero_of_coeff_one_βHenselAssembled_eq H x₀ R hHyp⟩

/-- **Order-zero recursion-side closed form, unsolved coefficient form.**  The `βHensel`
recursion itself makes the normalized RHS `-ζ * coeff 1 βHenselAssembled` equal to the un-cleared
Hasse numerator divided by `W ^ R.natDegree`, under the same degree hypothesis used by the
order-zero RHS cancellation. This is recursion-side normalization only; it does not compare with
the LHS `hasseEvalAtRoot`. -/
theorem neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    - (ClaimA2.ζ R x₀ H * PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp))
      = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
  calc
    - (ClaimA2.ζ R x₀ H * PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp))
        = restrictedMatchRecursionPartitionForm H x₀ R hHyp 0 := by
      simpa using restrictedMatch_rhs_eq_restrictedRecursionPartitionForm H x₀ R hHyp 0
    _ = restrictedMatchRecursionPartitionZeroSingleBcoeff H x₀ R hHyp := by
      exact restrictedMatchRecursionPartitionForm_zero_eq_singleBcoeff H x₀ R hHyp
    _ = embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree := by
      exact
        restrictedMatchRecursionPartitionZeroSingleBcoeff_eq_unclearedHasseCoeff_div_W_natDegree
          H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp)

/-- **Order-zero recursion-side closed form, solved coefficient form.**  Dividing the previous
closed form by the nonzero separability factor `ζ` gives the first successor coefficient of
`βHenselAssembled` explicitly in terms of the un-cleared Hasse numerator. -/
theorem coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree_div_ζ
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    PowerSeries.coeff 1 (βHenselAssembled H x₀ R hHyp)
      = - (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree)
          / ClaimA2.ζ R x₀ H := by
  have hneg :=
    neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree H x₀ R hHyp hd
  have hζ : ClaimA2.ζ R x₀ H ≠ 0 := ζ_ne_zero H x₀ R hHyp
  rw [← hneg]
  field_simp [hζ]

/-- **Order-zero Taylor/W-divisor target.** The fixed order-zero P2 obstruction after all proven
normalizations: the root-side shifted Hasse-Taylor sum with powers `(T/W)^i` equals the un-cleared
shifted Hasse-Taylor sum with powers `T^i`, divided by the global factor `W ^ R.natDegree`. -/
def RestrictedMatchAtZeroTaylorWDivTarget (x₀ : F) (R : F[X][X][Y]) : Prop :=
  (∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX 1 (hasseDerivY 0 R))).natDegree + 1),
      (i + 0).choose 0
        • (liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff (i + 0))
            * (functionFieldT (H := H)
                / liftToFunctionField (H := H) H.leadingCoeff) ^ i))
    =
    (∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
          (hasseDerivX 1 (hasseDerivY 0 R))).natDegree + 1),
      (i + 0).choose 0
        • (liftToFunctionField (H := H)
              ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff (i + 0))
            * (functionFieldT (H := H)) ^ i))
      / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree

/-- The un-cleared `Y ↦ T` embedding of `hasseCoeffRepr𝒪` in shifted Hasse-Taylor form. -/
theorem embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) :
    embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m)
      = ∑ i ∈ Finset.range ((Bivariate.evalX (Polynomial.C x₀)
              (hasseDerivX i1 (hasseDerivY m R))).natDegree + 1),
          (i + m).choose m
            • (liftToFunctionField (H := H)
                  ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 R)).coeff (i + m))
                * (functionFieldT (H := H)) ^ i) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]
  rw [Polynomial.eval₂_eq_sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [evalX_hasseDeriv_Y_coeff, map_nsmul (liftToFunctionField (H := H)), smul_mul_assoc]

/-- The carved order-zero P2 core is exactly the named Taylor/W-divisor target under the same
degree hypothesis as the order-zero RHS cancellation. -/
theorem restrictedMatchAt_zero_iff_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      RestrictedMatchAtZeroTaylorWDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroTaylorWDivTarget
  rw [restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
    H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp)]
  rw [hasseEvalAtRoot_eq_taylorSum,
    embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum]

/-- Project the Taylor/W-divisor target from the carved order-zero P2 core. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  (restrictedMatchAt_zero_iff_taylorWDivTarget H x₀ R hHyp hd).1 hmatch

/-- Build the carved order-zero P2 core from the Taylor/W-divisor target. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroTaylorWDivTarget H x₀ R) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_taylorWDivTarget H x₀ R hHyp hd).2 htarget

/-- **Order-zero `eval₂`/W-divisor target.** The same fixed order-zero P2 obstruction as
`RestrictedMatchAtZeroTaylorWDivTarget`, but before expanding the two sides into shifted Taylor
sums: `Y ↦ T/W` equals `Y ↦ T` divided by `W ^ R.natDegree` on
`(Δ_X Δ_Y^0 R)|x₀`. -/
def RestrictedMatchAtZeroEval₂WDivTarget (x₀ : F) (R : F[X][X][Y]) : Prop :=
  Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))
    =
    Polynomial.eval₂ (liftToFunctionField (H := H)) (functionFieldT (H := H))
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))
      / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree

/-- The carved order-zero P2 core is exactly the compact `eval₂`/W-divisor target under the
same degree hypothesis as the order-zero RHS cancellation. -/
theorem restrictedMatchAt_zero_iff_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      RestrictedMatchAtZeroEval₂WDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroEval₂WDivTarget
  rw [restrictedMatchAt_zero_iff_unclearedHasseCoeff_div_W_natDegree
    H x₀ R hHyp hd (ζ_ne_zero H x₀ R hHyp)]
  unfold hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]

/-- Project the compact `eval₂`/W-divisor target from the carved order-zero P2 core. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).1 hmatch

/-- Build the carved order-zero P2 core from the compact `eval₂`/W-divisor target. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroEval₂WDivTarget H x₀ R) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).2 htarget

/-- The compact `eval₂`/W-divisor order-zero target is exactly the expanded shifted Taylor-sum
order-zero target. This bridge has no `ClaimA2` or degree hypotheses; it only changes presentation
of the same equality. -/
theorem restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R ↔
      RestrictedMatchAtZeroTaylorWDivTarget H x₀ R := by
  unfold RestrictedMatchAtZeroEval₂WDivTarget RestrictedMatchAtZeroTaylorWDivTarget
  rw [← hasseEvalAtRoot_eq_taylorSum H x₀ R 1 0,
    ← embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared_eq_taylorSum H x₀ R 1 0]
  unfold hasseEvalAtRoot
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_uncleared]

/-- Expand the compact `eval₂`/W-divisor target into the Taylor-sum target. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y])
    (htarget : RestrictedMatchAtZeroEval₂WDivTarget H x₀ R) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget H x₀ R).1 htarget

/-- Compress the Taylor-sum target back into the compact `eval₂`/W-divisor target. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y])
    (htarget : RestrictedMatchAtZeroTaylorWDivTarget H x₀ R) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget H x₀ R).2 htarget

/-- The compact order-zero target is the `(i1,m,e) = (1,0,R.natDegree)` specialization of the
general un-cleared/W-divisor `eval₂` target. -/
theorem restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedEval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R ↔
      HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree := by
  rfl

/-- The compact order-zero target is the `(i1,m,e) = (1,0,R.natDegree)` specialization of the
general embedded un-cleared/W-divisor target. -/
theorem restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedWDivTarget
    (x₀ : F) (R : F[X][X][Y]) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R ↔
      HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedEval₂WDivTarget H x₀ R).trans
    (hasseCoeffRepr𝒪UnclearedWDivTarget_iff_eval₂WDivTarget H x₀ R 1 0 R.natDegree).symm

/-- The carved order-zero P2 core is equivalent to the generalized un-cleared/W-divisor
`eval₂` target. -/
theorem restrictedMatchAt_zero_iff_unclearedEval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).trans
    (restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedEval₂WDivTarget H x₀ R)

/-- The carved order-zero P2 core is equivalent to the generalized embedded
un-cleared/W-divisor target. -/
theorem restrictedMatchAt_zero_iff_unclearedWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).trans
    (restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedWDivTarget H x₀ R)

/-- The normalized order-zero partition residual is equivalent to the generalized
un-cleared/W-divisor `eval₂` target. -/
theorem restrictedPartitionMatchAt_zero_iff_unclearedEval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).symm.trans
    (restrictedMatchAt_zero_iff_unclearedEval₂WDivTarget H x₀ R hHyp hd)

/-- The normalized order-zero partition residual is equivalent to the generalized embedded
un-cleared/W-divisor target. -/
theorem restrictedPartitionMatchAt_zero_iff_unclearedWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).symm.trans
    (restrictedMatchAt_zero_iff_unclearedWDivTarget H x₀ R hHyp hd)

/-- Project the general un-cleared/W-divisor `eval₂` target from the carved order-zero P2 core. -/
theorem HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedEval₂WDivTarget H x₀ R).1
    (RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd hmatch)

/-- Project the general embedded un-cleared/W-divisor target from the carved order-zero P2 core. -/
theorem HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  (restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedWDivTarget H x₀ R).1
    (RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd hmatch)

/-- Build the carved order-zero P2 core from the general un-cleared/W-divisor `eval₂` target. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_unclearedEval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget H x₀ R hHyp hd
    ((restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedEval₂WDivTarget H x₀ R).2 htarget)

/-- Build the carved order-zero P2 core from the general embedded un-cleared/W-divisor target. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_unclearedWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget H x₀ R hHyp hd
    ((restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedWDivTarget H x₀ R).2 htarget)

/-- Project the general un-cleared/W-divisor `eval₂` target from the full carved P2 core. -/
theorem HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree :=
  HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (hmatch 0)

/-- Project the general embedded un-cleared/W-divisor target from the full carved P2 core. -/
theorem HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd (hmatch 0)

/-- Project the general un-cleared/W-divisor `eval₂` target from the fixed order-zero partition
residual. -/
theorem HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree :=
  HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- Project the general embedded un-cleared/W-divisor target from the fixed order-zero partition
residual. -/
theorem HasseCoeffRepr𝒪UnclearedWDivTarget.of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- Project the general un-cleared/W-divisor `eval₂` target from the all-orders partition
residual. -/
theorem HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree :=
  HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatch.at H x₀ R hHyp hpart 0)

/-- Project the general embedded un-cleared/W-divisor target from the all-orders partition
residual. -/
theorem HasseCoeffRepr𝒪UnclearedWDivTarget.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree :=
  HasseCoeffRepr𝒪UnclearedWDivTarget.of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatch.at H x₀ R hHyp hpart 0)

/-- Build the fixed order-zero partition residual from the general un-cleared/W-divisor `eval₂`
target. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedEval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂WDivTarget H x₀ R 1 0 R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_unclearedEval₂WDivTarget H x₀ R hHyp hd htarget)

/-- Build the fixed order-zero partition residual from the general embedded un-cleared/W-divisor
target. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R 1 0 R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_unclearedWDivTarget H x₀ R hHyp hd htarget)

/-- Project the expanded Taylor/W-divisor target from the full carved P2 core. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd (hmatch 0)

/-- Project the compact `eval₂`/W-divisor target from the full carved P2 core. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd (hmatch 0)

/-- Project the expanded Taylor/W-divisor target from the fixed order-zero partition residual. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- Project the compact `eval₂`/W-divisor target from the fixed order-zero partition residual. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoMatchAt.of_partitionMatchAt H x₀ R hHyp 0 hpart)

/-- Build the fixed order-zero partition residual from the expanded Taylor/W-divisor target. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_taylorWDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroTaylorWDivTarget H x₀ R) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_taylorWDivTarget H x₀ R hHyp hd htarget)

/-- Build the fixed order-zero partition residual from the compact `eval₂`/W-divisor target. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_eval₂WDivTarget
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (htarget : RestrictedMatchAtZeroEval₂WDivTarget H x₀ R) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget H x₀ R hHyp hd htarget)

/-- Project the expanded Taylor/W-divisor target from the all-orders partition residual. -/
theorem RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroTaylorWDivTarget H x₀ R :=
  RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatch.at H x₀ R hHyp hpart 0)

/-- Project the compact `eval₂`/W-divisor target from the all-orders partition residual. -/
theorem RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatch
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatch H x₀ R hHyp) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R :=
  RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatch.at H x₀ R hHyp hpart 0)

/-! ### Order-zero STEP-8 as a single polynomial-lift identity (axiom-clean)

The compact `eval₂`/W-divisor order-zero target `RestrictedMatchAtZeroEval₂WDivTarget` is reduced to
an explicit equality of two `F[X][Y]`-polynomial lifts.  This is strictly sharper than the `eval₂`
form: it isolates the whole remaining order-zero content into a single difference
`zeroClearingPolyFull − evalX (C x₀) (Δ_X^1 R)` lying in the kernel of `liftBivariate` (equivalently
in `⟨H_tilde' H⟩`), with the per-`Y`-degree mismatch factor `lc^{R.natDegree − i}` made fully
explicit.  Both bridges below are axiom-clean and use ONLY the always-true `W`-clearing identity
`W_pow_mul_eval₂_div_eq_liftBivariate` (valid for the full exponent `R.natDegree ≥ natDegreeY p`)
plus `W ≠ 0`; neither uses the STEP-8 core. -/

/-- The explicit `W`-power-weighted clearing polynomial for the order-zero Hasse coefficient
`p = evalX (C x₀) (Δ_X^1 Δ_Y^0 R)`, cleared by the FULL `R.natDegree` (not `natDegreeY p`): each
`Y`-power `i` of `p` is scaled by `lc^{R.natDegree − i}`.  Its `Y↦T` lift is exactly
`W^{R.natDegree} · eval₂(T/W) p` by `W_pow_mul_eval₂_div_eq_liftBivariate`. -/
def zeroClearingPolyFull (x₀ : F) (R : F[X][X][Y]) : F[X][Y] :=
  ∑ i ∈ Finset.range (R.natDegree + 1),
    Polynomial.C
      ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))).coeff i
        * H.leadingCoeff ^ (R.natDegree - i)) * Polynomial.X ^ i

/-- **Order-zero STEP-8 `eval₂`/W-divisor target ⟺ the full-clearing polynomial lifts to the
un-cleared one (axiom-clean, NO hypotheses).**  `RestrictedMatchAtZeroEval₂WDivTarget` is
exactly the polynomial-lift identity `liftBivariate (zeroClearingPolyFull) = liftBivariate p`, with
`p = evalX (C x₀) (Δ_X^1 R)`.  No degree or `ζ`-nonvanishing hypothesis is needed: it follows purely
from the always-true `W`-clearing identity `W_pow_mul_eval₂_div_eq_liftBivariate` at the full
exponent `R.natDegree ≥ natDegreeY p` together with `W ≠ 0`. -/
theorem restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R ↔
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) := by
  set p : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)) with hp
  have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hpdeg : p.natDegree ≤ R.natDegree := by
    have h1 : Bivariate.natDegreeY p ≤ Bivariate.natDegreeY R := by
      rw [hp, hasseDerivY_zero]
      exact (evalX_natDegreeY_le (Polynomial.C x₀) _).trans (hasseDerivX_natDegreeY_le 1 R)
    simpa [Bivariate.natDegreeY] using h1
  unfold RestrictedMatchAtZeroEval₂WDivTarget zeroClearingPolyFull
  rw [← hp, ← liftBivariate_eq_eval₂_functionFieldT H p]
  have hclear := W_pow_mul_eval₂_div_eq_liftBivariate H (P := p) (k := R.natDegree) hpdeg
  constructor
  · intro htarget
    rw [htarget, mul_div_cancel₀ _ (pow_ne_zero _ hWne)] at hclear
    exact hclear.symm
  · intro hpoly
    rw [hpoly] at hclear
    rw [eq_div_iff (pow_ne_zero _ hWne), mul_comm]
    exact hclear

/-- **The actual carved order-zero P2 core ⟺ the explicit polynomial-lift identity (axiom-clean).**
Under the standard `2 ≤ R.natDegree` regime hypothesis, the genuine carved core
`RestrictedFaaDiBrunoMatchAt … 0` — which DOES carry `hHyp` (including
`hHyp.dvd_evalX : H ∣ evalX (C x₀) R`) — is logically equivalent to the concrete polynomial-lift
identity `liftBivariate (zeroClearingPolyFull) = liftBivariate (evalX (C x₀) (Δ_X^1 R))`.

This is the sharpest in-tree restatement of the order-zero STEP-8 obstruction: it pins the entire
remaining order-zero content to a single equation between two `F[X][Y]`-polynomial lifts, whose
per-`Y`-degree mismatch factor is exactly `lc^{R.natDegree − i}`.  The equation is equivalently the
membership of the difference `zeroClearingPolyFull − evalX (C x₀) (Δ_X^1 R)` in `⟨H_tilde' H⟩`.
Closing it requires routing the `H ∣ evalX (C x₀) R` arithmetic into that quotient-membership — the
genuine non-per-term global-resummation step (note the bare W-divisor target without `hHyp` is
generically false whenever the `Y`-degree strictly drops, `natDegreeY p < R.natDegree`, since then
the mismatch factors `lc^{R.natDegree − i} ≠ 1` survive). -/
theorem restrictedMatchAt_zero_iff_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).trans
    (restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_lift H x₀ R)

/-- Build the carved order-zero core from the explicit full-clearing polynomial-lift identity. -/
theorem RestrictedFaaDiBrunoMatchAt.zero_of_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hzero :
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 :=
  (restrictedMatchAt_zero_iff_zeroClearingPolyFull_lift H x₀ R hHyp hd).2 hzero

/-- Project the explicit full-clearing polynomial-lift identity from the carved order-zero core. -/
theorem zeroClearingPolyFull_lift_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) :=
  (restrictedMatchAt_zero_iff_zeroClearingPolyFull_lift H x₀ R hHyp hd).1 hmatch

/-- The normalized partition order-zero residual is equivalent to the explicit full-clearing
polynomial-lift identity. -/
theorem restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).symm.trans
    (restrictedMatchAt_zero_iff_zeroClearingPolyFull_lift H x₀ R hHyp hd)

/-- Build the normalized partition order-zero residual from the explicit full-clearing
polynomial-lift identity. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hzero :
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_lift H x₀ R hHyp hd).2 hzero

/-- Project the explicit full-clearing polynomial-lift identity from the normalized partition
order-zero residual. -/
theorem zeroClearingPolyFull_lift_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) :=
  (restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_lift H x₀ R hHyp hd).1 hpart

/-- The reabsorbed un-cleared-over-`W ^ R.natDegree` endpoint implies the explicit
zero-clearing polynomial-lift identity. -/
theorem zeroClearingPolyFull_lift_of_unclearedHasseCoeff_div_W_natDegree
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hzero :
      hasseEvalAtRoot H x₀ R 1 0 =
        embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
          / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree) :
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) :=
  zeroClearingPolyFull_lift_of_partitionMatchAt_zero H x₀ R hHyp hd
    (RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ hzero)

/-- The explicit zero-clearing polynomial-lift identity implies the reabsorbed
un-cleared-over-`W ^ R.natDegree` endpoint under the same cancellation hypotheses. -/
theorem hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0)
    (hzero :
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))) :
    hasseEvalAtRoot H x₀ R 1 0 =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree :=
  hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_partitionMatchAt_zero
    H x₀ R hHyp hd hζ
    (RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroClearingPolyFull_lift
      H x₀ R hHyp hd hzero)

/-- The reabsorbed un-cleared-over-`W ^ R.natDegree` endpoint is equivalent to the explicit
zero-clearing polynomial-lift identity. -/
theorem hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_iff_zeroClearingPolyFull_lift
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hζ : ClaimA2.ζ R x₀ H ≠ 0) :
    (hasseEvalAtRoot H x₀ R 1 0 =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0)
        / (liftToFunctionField (H := H) H.leadingCoeff) ^ R.natDegree) ↔
      liftBivariate (H := H) (zeroClearingPolyFull H x₀ R)
        = liftBivariate (H := H)
            (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))) :=
  ⟨zeroClearingPolyFull_lift_of_unclearedHasseCoeff_div_W_natDegree
      H x₀ R hHyp hd hζ,
    hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_zeroClearingPolyFull_lift
      H x₀ R hHyp hd hζ⟩

/-- **W-divisor target to cleared/un-cleared scaling (axiom-clean).**  A general
`HasseCoeffRepr𝒪UnclearedWDivTarget ... e` says the root evaluation equals the un-cleared
representative divided by `W^e`; combining it with the proven cleared embedding identity gives the
exact multiplicative relation
`embedding(cleared) * W^e = W^(natDegreeY p) * embedding(uncleared)`. -/
theorem embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_wDivTarget
    (x₀ : F) (R : F[X][X][Y]) (i1 m e : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R i1 m e) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R i1 m
            (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))) : 𝒪 H)
      * liftToFunctionField (H := H) H.leadingCoeff ^ e
      =
      liftToFunctionField (H := H) H.leadingCoeff
          ^ Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
        * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R i1 m
    (Bivariate.natDegreeY
      (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))) le_rfl, htarget]
  rw [mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H)))]

/-- Exact-degree corollary of the W-divisor target: when the divisor exponent is precisely the
clearing degree of the specialized Hasse coefficient, the cleared and un-cleared `𝒪` representative
embeddings coincide. -/
theorem embeddingCleared_eq_uncleared_of_wDivTarget_exactDegree
    (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedWDivTarget H x₀ R i1 m
      (Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R i1 m
            (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))) : 𝒪 H)
      =
      embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) := by
  have hscale :=
    embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_wDivTarget
      H x₀ R i1 m
      (Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))
      htarget
  rw [mul_comm
    (liftToFunctionField (H := H) H.leadingCoeff
      ^ Bivariate.natDegreeY
          (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))
    (embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m))] at hscale
  exact mul_right_cancel₀
    (pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))) hscale

/-- Order-zero carved-core specialization of the W-divisor-to-cleared scaling bridge. -/
theorem embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_restrictedMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmatch : RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R 1 0
            (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))))) : 𝒪 H)
      * liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree
      =
      liftToFunctionField (H := H) H.leadingCoeff
          ^ Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))
        * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0) := by
  exact embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_wDivTarget
    H x₀ R 1 0 R.natDegree
    (HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatchAt_zero
      H x₀ R hHyp hd hmatch)

/-- Order-zero partition-residual specialization of the W-divisor-to-cleared scaling bridge. -/
theorem embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R 1 0
            (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))))) : 𝒪 H)
      * liftToFunctionField (H := H) H.leadingCoeff ^ R.natDegree
      =
      liftToFunctionField (H := H) H.leadingCoeff
          ^ Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R)))
        * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R 1 0) := by
  exact embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_wDivTarget
    H x₀ R 1 0 R.natDegree
    (HasseCoeffRepr𝒪UnclearedWDivTarget.of_partitionMatchAt_zero
      H x₀ R hHyp hd hpart)

/-- **The cleared `𝒪`-rep embedding is `W^{natDegreeY p}` times the un-cleared rep embedding, GIVEN
the STEP-8 target (axiom-clean).** Makes the cleared/un-cleared `eval₂` mismatch *quantitative*:
under the carved STEP-8 match `HasseCoeffRepr𝒪UnclearedEval₂Target`, the two `𝒪`-reps are related by
exactly the `m = |λ|`-dependent factor `W^{natDegreeY p}` named in the #139 obstruction analysis. -/
theorem embeddingCleared_eq_Wpow_mul_uncleared_of_target (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ)
    (htarget : HasseCoeffRepr𝒪UnclearedEval₂Target H x₀ R i1 m) :
    embeddingOf𝒪Into𝕃 H
        (Ideal.Quotient.mk (Ideal.span {H_tilde' H})
          (hasseCoeffRepr𝒪_cleared H x₀ R i1 m
            (Bivariate.natDegreeY
              (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R))))) : 𝒪 H)
      = liftToFunctionField (H := H) H.leadingCoeff
            ^ Bivariate.natDegreeY
                (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))
          * embeddingOf𝒪Into𝕃 H (hasseCoeffRepr𝒪 H x₀ R i1 m) := by
  rw [embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared H x₀ R i1 m
      (Bivariate.natDegreeY
        (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))) le_rfl,
    (HasseCoeffRepr𝒪UnclearedMatchesRoot.of_eval₂Target H x₀ R i1 m htarget)]

/-! ### Public kernel bridge for `liftBivariate` and the order-zero core as ideal membership

The lift `liftBivariate (H := H) : F[X][Y] →+* 𝕃 H` is `(Quotient.mk ⟨H_tilde H⟩) ∘ bivPolyHom`.
Its kernel is exactly the ideal `⟨H_tilde' H⟩` generated by the integral monicization, with NO
degree restriction on the argument: the bridge is a clean iff obtained from the *injective*
`𝒪 H ↪ 𝕃 H` embedding (`embeddingOf𝒪Into𝕃_injective`), which routes around the `private`
divisibility lemma `mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde`. This makes the order-zero
STEP-8 obstruction a single explicit *ideal membership* in `F[X][Y]`. -/

omit [Fact (Irreducible H)] in
/-- **Public kernel bridge (axiom-clean).** `liftBivariate (H := H) q = 0` iff
`q ∈ ⟨H_tilde' H⟩`. No degree bound on `q` is needed and irreducibility is not used: it follows
solely from the injectivity of `𝒪 H ↪ 𝕃 H` (`embeddingOf𝒪Into𝕃_injective`, needing only
`0 < H.natDegree`) together with `Ideal.Quotient.eq_zero_iff_mem`. This is the public form of the
`private mem_span_H_tilde'_of_bivPolyHom_mem_span_H_tilde`: the `→` direction is the injectivity
content, the `←` direction is `liftBivariate` killing the generator. -/
theorem liftBivariate_eq_zero_iff_mem_span_H_tilde' (q : F[X][Y]) :
    liftBivariate (H := H) q = 0 ↔ q ∈ Ideal.span {H_tilde' H} := by
  have hHdeg : 0 < H.natDegree := (inferInstance : Fact (0 < H.natDegree)).out
  rw [← embeddingOf𝒪Into𝕃_mk H q,
    ← Ideal.Quotient.eq_zero_iff_mem (a := q) (I := Ideal.span {H_tilde' H})]
  exact ⟨fun h => embeddingOf𝒪Into𝕃_injective (H := H) hHdeg (by rw [h, map_zero]),
    fun h => by rw [h, map_zero]⟩

omit [Fact (Irreducible H)] in
/-- **Equality of two lifts ⟺ membership of the difference (axiom-clean).** Specialization of the
kernel bridge to the difference `p - q`: `liftBivariate p = liftBivariate q` iff
`p - q ∈ ⟨H_tilde' H⟩`. -/
theorem liftBivariate_eq_iff_sub_mem_span_H_tilde' (p q : F[X][Y]) :
    liftBivariate (H := H) p = liftBivariate (H := H) q ↔
      p - q ∈ Ideal.span {H_tilde' H} := by
  rw [← liftBivariate_eq_zero_iff_mem_span_H_tilde' H (p - q), map_sub, sub_eq_zero]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The order-zero full-clearing difference, expanded (axiom-clean, NO hypotheses).** The
polynomial `zeroClearingPolyFull − evalX (C x₀) (Δ_X^1 R)` is the explicit single sum
`∑_{i ≤ R.natDegree} C (p.coeff i · (lc^{R.natDegree − i} − 1)) · X^i`, where
`p = evalX (C x₀) (Δ_X^1 R)`.  Each `Y`-power `i` carries the mismatch factor `lc^{d−i} − 1`,
which vanishes only at `i = d` (and at indices where `p.coeff i = 0`); for every other `i < d`
with `p.coeff i ≠ 0` and `lc ≠ 1` it survives — the source of the #139 obstruction. -/
theorem zeroClearingPolyFull_sub_eq (x₀ : F) (R : F[X][X][Y]) :
    zeroClearingPolyFull H x₀ R
      - Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 (hasseDerivY 0 R))
    = ∑ i ∈ Finset.range (R.natDegree + 1),
        Polynomial.C
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
            * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i := by
  unfold zeroClearingPolyFull
  simp only [hasseDerivY_zero]
  set p : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R) with hp
  have hpdeg : p.natDegree ≤ R.natDegree := by
    have h1 : Bivariate.natDegreeY p ≤ Bivariate.natDegreeY R :=
      (evalX_natDegreeY_le (Polynomial.C x₀) _).trans (hasseDerivX_natDegreeY_le 1 R)
    simpa [hp, Bivariate.natDegreeY] using h1
  have hp_sum : p = ∑ i ∈ Finset.range (R.natDegree + 1),
      Polynomial.C (p.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range' p (R.natDegree + 1) (by omega)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.C_mul_X_pow_eq_monomial])
  nth_rewrite 2 [hp_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [← sub_mul, ← Polynomial.C_sub, mul_sub, mul_one])

/-- **Order-zero STEP-8 target ⟺ ideal membership of the explicit difference
(axiom-clean, NO hypotheses).** The pure-lift form of
`restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_lift`:
the order-zero `eval₂`/W-divisor target is exactly
`∑_{i ≤ R.natDegree} C (p.coeff i · (lc^{d−i} − 1)) · X^i ∈ ⟨H_tilde' H⟩`,
the single difference of the full-clearing polynomial and the un-cleared Hasse coefficient lying in
the kernel of `liftBivariate`.  Combines the always-true `W`-clearing identity with the public
kernel bridge; uses no degree or `ζ`-nonvanishing hypothesis. -/
theorem restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_sub_mem
    (x₀ : F) (R : F[X][X][Y]) :
    RestrictedMatchAtZeroEval₂WDivTarget H x₀ R ↔
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} := by
  rw [restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_lift H x₀ R,
    liftBivariate_eq_iff_sub_mem_span_H_tilde' H, zeroClearingPolyFull_sub_eq H x₀ R]

/-- **The actual carved order-zero P2 core ⟺ the explicit difference lies in `⟨H_tilde' H⟩`
(axiom-clean).**  The sharpest in-tree restatement of the order-zero STEP-8 obstruction: under the
standard regime `2 ≤ R.natDegree`, the genuine carved core `RestrictedFaaDiBrunoMatchAt … 0`
(carrying `hHyp`, including `hHyp.dvd_evalX : H ∣ evalX (C x₀) R`) is equivalent to the membership
`∑_{i ≤ R.natDegree} C (p.coeff i · (lc^{R.natDegree − i} − 1)) · X^i ∈ ⟨H_tilde' H⟩`.

This isolates the entire remaining order-zero content into a *single explicit ideal membership* in
`F[X][Y]`.  Closing it requires routing the `H ∣ evalX (C x₀) R` arithmetic into divisibility of
this difference by the monic `H_tilde' H`.  NOTE: `hHyp.dvd_evalX` constrains `evalX (C x₀) R`,
whereas `p = evalX (C x₀) (Δ_X^1 R)` is the *`X`-Hasse* derivative (taken in the transverse inner
`X`-variable before specialization); `X`-differentiation does not preserve `Y`-divisibility by `H`,
so the membership is NOT available from `dvd_evalX` per se — it is the genuine global-resummation
content of #139's STEP-8. -/
theorem restrictedMatchAt_zero_iff_zeroClearingPolyFull_sub_mem
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 ↔
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  (restrictedMatchAt_zero_iff_eval₂WDivTarget H x₀ R hHyp hd).trans
    (restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_sub_mem H x₀ R)

/-- **The normalized partition order-zero residual ⟺ the explicit ideal membership.**  This is
the partition-facing form of `restrictedMatchAt_zero_iff_zeroClearingPolyFull_sub_mem`, so callers
using the normalized residual surface can target the single `⟨H_tilde' H⟩` membership directly. -/
theorem restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_sub_mem
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 ↔
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  (restrictedMatchAt_iff_partitionMatchAt H x₀ R hHyp 0).symm.trans
    (restrictedMatchAt_zero_iff_zeroClearingPolyFull_sub_mem H x₀ R hHyp hd)

/-- Build the normalized partition order-zero residual from the explicit ideal membership. -/
theorem RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroClearingPolyFull_sub_mem
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hmem :
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H}) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  (restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_sub_mem
    H x₀ R hHyp hd).2 hmem

/-- Project the explicit ideal membership from the normalized partition order-zero residual. -/
theorem zeroClearingPolyFull_sub_mem_of_partitionMatchAt_zero
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree)
    (hpart : RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0) :
      (∑ i ∈ Finset.range (R.natDegree + 1),
          Polynomial.C
            ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
              * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
        ∈ Ideal.span {H_tilde' H} :=
  (restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_sub_mem
    H x₀ R hHyp hd).1 hpart

/-! ### Order-zero STEP-8: monic specialization (closed) and the obstruction for non-monic `H`

The explicit order-zero membership above carries the per-`Y`-degree mismatch factor
`lc^{R.natDegree − i} − 1` (`lc = H.leadingCoeff`). When `H` is **monic** (`lc = 1`) every such
factor vanishes, the difference sum is identically `0`, and the carved order-zero core is closed
*unconditionally* — no global resummation is needed. For **non-monic** `H` (`lc ≠ 1`) the
membership is, by contrast, GENUINELY FALSE for generic `R` even under the full `ClaimA2.Hypotheses`
(`dvd_evalX` AND `separable_evalX`): the two hypotheses constrain `evalX (C x₀) R`, but the
order-zero numerator depends on `p = evalX (C x₀) (Δ_X^1 R)`, the transverse `X`-Hasse derivative,
which is unconstrained by either field of `Hypotheses`. Concretely, with `F = ℚ`,
`H = X·Y² + Y + X` (so `lc = X`, monic-fails), `evalX (C 0) R = H · (Y + X)` (separable, so both
  hypotheses hold) and a generic transverse part, the difference sum is NOT in `⟨H_tilde' H⟩`
  (verified by exact division by the monic generator `H_tilde' H`). Hence
  `RestrictedFaaDiBrunoMatchAt … 0` is
NOT a theorem from `ClaimA2.Hypotheses` alone in the non-monic regime: the recursively-defined
`βHenselAssembled` order-1 coefficient (the recursion RHS) does not, in general, agree with the
genuine root quantity `hasseEvalAtRoot` (the LHS). The order-zero match is therefore part of the
irreducible STEP-8 content, not a per-order consequence of the local divisibility datum. -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The order-zero full-clearing difference vanishes for monic `H` (axiom-clean, NO regime
hypotheses).** When `H.leadingCoeff = 1`, every mismatch factor `lc^{R.natDegree − i} − 1 = 0`, so
the explicit difference sum
`∑_{i ≤ R.natDegree} C (p.coeff i · (lc^{R.natDegree − i} − 1)) · X^i` is identically `0`. -/
theorem zeroClearingPolyFull_sub_eq_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hlc : H.leadingCoeff = 1) :
    (∑ i ∈ Finset.range (R.natDegree + 1),
        Polynomial.C
          ((Bivariate.evalX (Polynomial.C x₀) (hasseDerivX 1 R)).coeff i
            * (H.leadingCoeff ^ (R.natDegree - i) - 1)) * Polynomial.X ^ i)
      = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [hlc, one_pow, sub_self, mul_zero, map_zero, zero_mul]

/-- **Order-zero STEP-8 core, unconditional for monic `H` (axiom-clean).** When `H` is monic, the
mismatch factors `lc^{R.natDegree − i} − 1` all vanish, so the explicit order-zero difference sum is
`0 ∈ ⟨H_tilde' H⟩`, and the carved order-zero core `RestrictedFaaDiBrunoMatchAt … 0` holds for
EVERY `R` with `2 ≤ R.natDegree` satisfying `ClaimA2.Hypotheses`. This is the genuine monic
specialization of the order-zero match: with no `W`-power weighting there is nothing to resum, so
the global-resummation obstruction of #139's STEP-8 is vacuous at order zero. (For non-monic `H` the
membership is generically false — see the section note.) -/
theorem restrictedMatchAt_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoMatchAt H x₀ R hHyp 0 := by
  rw [restrictedMatchAt_zero_iff_zeroClearingPolyFull_sub_mem H x₀ R hHyp hd,
    zeroClearingPolyFull_sub_eq_zero_of_leadingCoeff_one H x₀ R hlc]
  exact Ideal.zero_mem _

/-- **Monic `H` ⟹ the order-zero partition residual holds (axiom-clean).** The partition-residual
endpoint of `restrictedMatchAt_zero_of_leadingCoeff_one`. -/
theorem restrictedPartitionMatchAt_zero_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hd : 2 ≤ R.natDegree) (hlc : H.leadingCoeff = 1) :
    RestrictedFaaDiBrunoPartitionMatchAt H x₀ R hHyp 0 :=
  RestrictedFaaDiBrunoPartitionMatchAt.of_restrictedMatchAt H x₀ R hHyp 0
    (restrictedMatchAt_zero_of_leadingCoeff_one H x₀ R hHyp hd hlc)

/-! ### The `W`-power weighting collapses for monic `H` at EVERY order — but is NOT the only
obstruction (axiom-clean)

The #139 obstruction analysis documents the surviving `W`-power weighting (`W = liftToFunctionField
H.leadingCoeff`) as the order-zero obstruction. For **monic** `H` (`H.leadingCoeff = 1`) that
weighting genuinely collapses at *every* order: `W = liftToFunctionField 1 = 1` and the `𝒪`-level
unit `W𝒪 H = ⟦C 1⟧ = 1` embeds to `1`, so every `W^k`-factor in the recursion-side
`restrictedMatchRecursionPartitionForm` is `1`. The lemmas below land that collapse unconditionally.

HOWEVER, contrary to the conjecture that the `W`-weighting is the *only* all-orders obstruction,
removing `W` does **not** trivialize `RestrictedFaaDiBrunoMatchAt t` for `t ≥ 1`. The recursion side
`restrictedMatchRecursionPartitionForm` still carries, even after `W = 1`:

  * the **`ξ`-telescope** — powers `ξ^{2 i₁ + σλ − 2}` inside `recSum`, the global `ξ^{2(t+1)−1}`
    in `den`, and the dual `1 / ξ^{2t−1}` weighting *inside every* `βHenselAssembled` coefficient on
    the LHS partition form. `ξ = ClaimA2.ξ` is the separability discriminant unit; it is a
    DIFFERENT unit from `W` and does not collapse for monic `H`;
  * the genuine **Faà-di-Bruno bijection** — the term-level identification of restricted
    value-multisets `m` (LHS, `restrictedFaaDiBrunoPartitionForm`) against index pairs `(i₁, λ)`
    (RHS, `recSum`), matching `countPerms`/binomial/`B_coeff`/`partitionProd` — which is exactly the
    unformalized BCIKS20 A.4 content carried as the hypothesis `RestrictedFaaDiBrunoMatch`.

At order zero both of these collapse to a *single* surviving term on each side
(`restrictedFaaDiBrunoPartitionForm_zero_eq_powerSum` and
`restrictedMatchRecursionPartitionForm_zero_eq_singleBcoeff`), so the `W`-mismatch was the only
discrepancy left — which is why `restrictedMatchAt_zero_of_leadingCoeff_one` closes order zero
unconditionally. For `t ≥ 1` neither side collapses, so the `W = 1` collapse, while genuine, is not
sufficient: the all-orders monic core is NOT closeable from `W = 1` alone. -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **`W = liftToFunctionField H.leadingCoeff = 1` for monic `H` (axiom-clean).** The
function-field `W`-unit is the identity precisely when `H` is monic. -/
theorem liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one
    (hlc : H.leadingCoeff = 1) :
    liftToFunctionField (H := H) H.leadingCoeff = 1 := by
  rw [hlc, map_one]

/-- **The `𝒪`-level `W`-unit `W𝒪 H` embeds to `1` for monic `H` (axiom-clean).** Since
`W𝒪 H = ⟦C H.leadingCoeff⟧`, its embedding is `liftToFunctionField H.leadingCoeff`
(`embed_W𝒪`), which is `1` when `H.leadingCoeff = 1`. Hence every `W`-power factor in the
recursion-side partition form collapses for monic `H`. -/
theorem embed_W𝒪_eq_one_of_leadingCoeff_one (hlc : H.leadingCoeff = 1) :
    embeddingOf𝒪Into𝕃 H (W𝒪 H) = 1 := by
  rw [embed_W𝒪, liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one H hlc]

/-- **Monic-`H` recursion-side partition form: ALL `W`-powers collapse to `1` (axiom-clean).** For
monic `H`, `restrictedMatchRecursionPartitionForm` at EVERY order `t` simplifies to the
`W`-free recursion form: the `W^{i₁+δ−1}` factor in each `(i₁,λ)` summand becomes `1`, and the
`lc^{t+2}` factor in the denominator becomes `1`. The remaining structure is the pure
`ξ`-telescoped recursion `ζ · (∑_{i₁,λ} ξ^{2i₁+σλ−2}·⟦B_coeff⟧·⟦partitionProd λ βHensel⟧) /
ξ^{2(t+1)−1}` — entirely `W`-independent. This makes the W-collapse fully explicit at all orders and
exposes the surviving `ξ`-telescope + combinatorial `B_coeff`/`partitionProd` content that is the
genuine remaining obstruction. -/
theorem restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (t : ℕ)
    (hlc : H.leadingCoeff = 1) :
    restrictedMatchRecursionPartitionForm H x₀ R hHyp t
      = ClaimA2.ζ R x₀ H
          * ((∑ i1 ∈ Finset.range (t + 2),
                ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (t + 1 - i1))).filter
                          (fun lam => (t + 1) ∉ lam.parts),
                  embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                    * embeddingOf𝒪Into𝕃 H (B_coeff H x₀ R i1 lam)
                    * embeddingOf𝒪Into𝕃 H (partitionProd lam (βHensel H x₀ R hHyp)))
              / ((embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * (t + 1) - 1))) := by
  unfold restrictedMatchRecursionPartitionForm
  simp only [embed_W𝒪_eq_one_of_leadingCoeff_one H hlc,
    liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one H hlc,
    one_pow, one_mul]

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.coeff_succ_βHenselAssembled_eq_of_restrictedMatchAt
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_iff_coeff_succ_βHenselAssembled_eq
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_zero_eq_powerSum
#print axioms BCIKS20.HenselNumerator.restrictedFaaDiBrunoSum_zero_eq_hasseEvalAtRoot
#print axioms BCIKS20.HenselNumerator.coeff_one_βHenselAssembled_eq_of_restrictedMatchAt_zero
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_coeff_one_βHenselAssembled_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.neg_ζ_mul_coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.coeff_one_βHenselAssembled_eq_unclearedHasseCoeff_div_W_natDegree_div_ζ
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_taylorWDivTarget
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAtZeroEval₂WDivTarget_iff_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedEval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAtZeroEval₂WDivTarget_iff_unclearedWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_unclearedEval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_unclearedWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_unclearedEval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_unclearedWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_unclearedEval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_unclearedWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedWDivTarget.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedWDivTarget.of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedEval₂WDivTarget.of_partitionMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.HasseCoeffRepr𝒪UnclearedWDivTarget.of_partitionMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedEval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_unclearedWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_restrictedMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_taylorWDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_eval₂WDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroTaylorWDivTarget.of_partitionMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedMatchAtZeroEval₂WDivTarget.of_partitionMatch
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_wDivTarget
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.embeddingCleared_eq_uncleared_of_wDivTarget_exactDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.embeddingCleared_mul_Wpow_eq_Wpow_mul_uncleared_of_partitionMatchAt_zero
#print axioms BCIKS20.HenselNumerator.embeddingCleared_eq_Wpow_mul_uncleared_of_target
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoMatchAt.zero_of_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_lift_of_restrictedMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_lift_of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_lift_of_unclearedHasseCoeff_div_W_natDegree
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_of_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.hasseEvalAtRoot_eq_unclearedHasseCoeff_div_W_natDegree_iff_zeroClearingPolyFull_lift
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.liftBivariate_eq_zero_iff_mem_span_H_tilde'
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.liftBivariate_eq_iff_sub_mem_span_H_tilde'
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_sub_eq
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAtZeroEval₂WDivTarget_iff_zeroClearingPolyFull_sub_mem
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_iff_zeroClearingPolyFull_sub_mem
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_iff_zeroClearingPolyFull_sub_mem
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.RestrictedFaaDiBrunoPartitionMatchAt.zero_of_zeroClearingPolyFull_sub_mem
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_sub_mem_of_partitionMatchAt_zero
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.zeroClearingPolyFull_sub_eq_zero_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchAt_zero_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedPartitionMatchAt_zero_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.liftToFunctionField_leadingCoeff_eq_one_of_leadingCoeff_one
#print axioms BCIKS20.HenselNumerator.embed_W𝒪_eq_one_of_leadingCoeff_one
set_option linter.style.longLine false in
#print axioms BCIKS20.HenselNumerator.restrictedMatchRecursionPartitionForm_eq_Wfree_of_leadingCoeff_one
