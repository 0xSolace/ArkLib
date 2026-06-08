import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge141PrizeMath

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- Candidate 2: List-Decoding Collapse
    Prove that a tight list-decoding bound implies the MCA bound directly.
    We seek to bridge the definition of list-size bounds to the `epsMCA`
    proximity gap error definition. -/
theorem candidate_collapse_mca_bound (F : Type) [Field F] [Fintype F]
    (L : Finset F) (hL_smooth : L.card.IsPowerOfTwo) :
    ∃ τ, GrandChallengesLattice.mcaPrizeLatticeResolved L τ := by
  -- We assume `|Λ(C^{≡m},δ)| ≤ ε*·|F|` for an interleaved Reed-Solomon code,
  -- and use this to bound the mutual correlated agreement error (mcaBad count).
  sorry

end ArkLib.CodingTheory.Research
