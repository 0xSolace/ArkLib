import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentHighDist
import ArkLib.Data.CodingTheory.ReedSolomon

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem rs_finCarrier_sum_closeCount_sq_high_dist
    (domain : ι ↪ F) (k r : ℕ) [NeZero k]
    (hk : k ≤ Fintype.card ι)
    (h2r : 2 * r < Fintype.card ι - k + 1) :
    (∑ w : ι → F, (closeCount (ReedSolomon.finCarrier domain k) r w) ^ 2)
      = (ReedSolomon.finCarrier domain k).card * ballInterCount r (0 : ι → F) := by
  refine sum_closeCount_sq_high_dist (ReedSolomon.finCarrier domain k) r ?hsub ?hadd ?h0 ?hd
  · intro a ha b hb
    have ha' : a ∈ ReedSolomon.code domain k := by
      simpa [ReedSolomon.finCarrier] using ha
    have hb' : b ∈ ReedSolomon.code domain k := by
      simpa [ReedSolomon.finCarrier] using hb
    simpa [ReedSolomon.finCarrier] using
      (Submodule.sub_mem (ReedSolomon.code domain k) ha' hb')
  · intro a ha b hb
    have ha' : a ∈ ReedSolomon.code domain k := by
      simpa [ReedSolomon.finCarrier] using ha
    have hb' : b ∈ ReedSolomon.code domain k := by
      simpa [ReedSolomon.finCarrier] using hb
    simpa [ReedSolomon.finCarrier] using
      (Submodule.add_mem (ReedSolomon.code domain k) ha' hb')
  · simpa [ReedSolomon.finCarrier] using
      (Submodule.zero_mem (ReedSolomon.code domain k))
  · intro v hv hv0
    have hmin : Code.minDist ((ReedSolomon.code domain k) : Set (ι → F))
        ≤ hammingDist (0 : ι → F) v := by
      unfold Code.minDist
      apply Nat.sInf_le
      exact ⟨0, by simp, v, by simpa [ReedSolomon.finCarrier] using hv, hv0.symm, rfl⟩
    rw [ReedSolomon.minDist_eq' hk] at hmin
    exact lt_of_lt_of_le h2r hmin

end ArkLib.CS25
