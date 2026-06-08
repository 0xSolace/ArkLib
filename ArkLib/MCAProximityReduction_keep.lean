import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-! # The irreducible core of every MCA conjecture: reduction to a BCIKS20 proximity-gap bound.

`hasMutualCorrAgreement Gen BStar errStar` (WHIR mutual-correlated-agreement, over the per-row
asymmetric `proximityCondition`) follows from the symmetric BCIKS20 proximity-gap bound at the same
radius/error, because the per-row event implies the symmetric relative-distance event
(`proximityCondition_imp_relDist`) and probability is monotone. So for the Johnson conjecture
(`mca_johnson_bound_CONJECTURE`, `BStar=√ρ`) the ONLY remaining obligation is the RS proximity-gap
bound at the Johnson radius — the genuine open mathematics. NOT in build. -/

open scoped NNReal ENNReal
open MutualCorrAgreement ProbabilityTheory Code Generator ReedSolomon

namespace MCAProximityReduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **General MCA ⟸ proximity-gap reduction.** For any generator and any target `BStar`,
`errStar`, the WHIR mutual-correlated-agreement predicate follows from the symmetric proximity-gap
bound. Probability monotonicity is done inline via mathlib (`Pr_eq_tsum_indicator` is pure
unfolding; `ENNReal.tsum_le_tsum`), avoiding flaky cross-module probability lemmas. -/
theorem hasMutualCorrAgreement_of_proximityGap
    (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
    (BStar : ℝ) (errStar : ℝ → ENNReal)
    (hPG : haveI := Gen.Gen_nonempty
      ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0), (0 < δ ∧ (δ : ℝ) < 1 - BStar) →
        Pr_{let r ←$ᵖ Gen.Gen}[
          δᵣ((fun x => ∑ j : Gen.parℓ, (r : Gen.parℓ → F) j * f j x),
            (Gen.C : Set (ι → F))) ≤ δ] ≤ errStar δ) :
    hasMutualCorrAgreement Gen BStar errStar := by
  classical
  intro f δ hδ
  refine le_trans ?_ (hPG f δ hδ)
  rw [Pr_eq_tsum_indicator, Pr_eq_tsum_indicator]
  apply ENNReal.tsum_le_tsum
  intro r
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  by_cases hp : MutualCorrAgreement.proximityCondition f δ (↑r) Gen.C
  · have hr := proximityCondition_imp_relDist f δ (↑r) Gen.C hp
    rw [if_pos hp, if_pos hr]
  · rw [if_neg hp]; exact zero_le _

end MCAProximityReduction

