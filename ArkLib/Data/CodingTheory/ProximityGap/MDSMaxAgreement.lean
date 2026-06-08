import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS

open scoped NNReal
open Polynomial

namespace ArkLib.MDS

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Hypothesis 30: The maximal agreement of any vector with an MDS code is at least k.
    This implies the maximum agreement can never be k-1.
    For Reed-Solomon codes, this follows from polynomial interpolation.
-/
theorem rs_max_agreement_ge_k (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι) (v : ι → F) :
    ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)), 
      (Finset.univ.filter (fun i => c i = v i)).card ≥ k := by
  sorry

end ArkLib.MDS
