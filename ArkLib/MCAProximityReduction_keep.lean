import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-! # The irreducible core of every MCA conjecture: reduction to a BCIKS20 proximity-gap bound.

`hasMutualCorrAgreement Gen BStar errStar` (the WHIR mutual-correlated-agreement predicate, over
the per-row asymmetric `proximityCondition`) follows from the **symmetric** BCIKS20 proximity-gap
bound at the same radius/error: `Pr_r[δᵣ(∑ⱼ rⱼ·fⱼ, C) ≤ δ] ≤ errStar δ`. This is because the
per-row `proximityCondition` implies the symmetric relative-distance event
(`proximityCondition_imp_relDist`), so probability monotonicity transfers the bound.

Consequence: for the Johnson conjecture (`mca_johnson_bound_CONJECTURE`, `BStar = √ρ`), the ONLY
remaining obligation is the proximity-gap bound for the Reed-Solomon generator at the Johnson
radius — the genuine open mathematics (RS list-decoding / Johnson combinatorics). Everything else
(the per-row → symmetric reconciliation) is now discharged generically. NOT in build. -/

open scoped NNReal ENNReal
open MutualCorrAgreement ProbabilityTheory Code Generator ReedSolomon

namespace MCAProximityReduction

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **General MCA ⟸ proximity-gap reduction.** For any proximity generator and any target
`BStar`, `errStar`, the WHIR mutual-correlated-agreement predicate follows from the BCIKS20
symmetric proximity-gap bound at the same radius and error. This isolates the genuine core. -/
theorem hasMutualCorrAgreement_of_proximityGap
    (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
    (BStar : ℝ) (errStar : ℝ → ENNReal)
    (hPG : haveI := Gen.Gen_nonempty
      ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0), (0 < δ ∧ (δ : ℝ) < 1 - BStar) →
        Pr_{let r ←$ᵖ Gen.Gen}[
          δᵣ((fun x => ∑ j : Gen.parℓ, (r : Gen.parℓ → F) j * f j x),
            (Gen.C : Set (ι → F))) ≤ δ] ≤ errStar δ) :
    hasMutualCorrAgreement Gen BStar errStar := by
  intro f δ hδ
  refine le_trans (Pr_le_Pr_of_implies _ _ _ ?_) (hPG f δ hδ)
  intro r h
  exact proximityCondition_imp_relDist f δ r Gen.C h

end MCAProximityReduction




