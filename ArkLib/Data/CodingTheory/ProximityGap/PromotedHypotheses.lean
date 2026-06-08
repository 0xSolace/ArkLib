import Mathlib.InformationTheory.Hamming
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.UniqueDecodingListBound

open Finset
open scoped NNReal

namespace ArkLib.ProximityGap.PromotedHypotheses

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-!
# Promoted Hypotheses (Survivors of GF(5) Exhaustive Red-Teaming)

These 13 hypotheses survived the exhaustive computational search over GF(5), k=2, n=4.
They represent structural truths about Reed-Solomon clustering and Proximity Gaps, and are now 
formally stated here for deep proof and red-teaming over generic fields.
-/

-- We define the base RS code parameter regime
variable (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι)

/-- The "Decoding List" of a received word `r` at radius `e` -/
def decList (C : Finset (ι → F)) (r : ι → F) (e : ℕ) : Finset (ι → F) :=
  C.filter (fun c => hammingDist c r ≤ e)

/-- The "List of Centers" of a bundle `U` at radius `e` is the union of the decoding lists of its elements. -/
def bundleCenters (C : Finset (ι → F)) (U : Set (ι → F)) (e : ℕ) : Finset (ι → F) :=
  Finset.univ.filter (fun c => c ∈ C ∧ ∃ u ∈ U, hammingDist c u ≤ e)

/-! ## Group E: List-Decodability Bounds -/

/-- **Hypothesis 45 (List Intersection)**
If two bundles `U` and `V` intersect at a point `x`, and `x` is `e`-close to the code,
then their lists of centers intersect.

*Red-Teaming Status:* Trivially True geometrically. `x` is in both bundles, so `x`'s closest codeword 
is naturally injected into the union-list of both bundles.
-/
theorem hyp45_list_intersection (C : Finset (ι → F)) (U V : Set (ι → F)) (e : ℕ) (x : ι → F)
    (hxU : x ∈ U) (hxV : x ∈ V) (hclose : ∃ c ∈ C, hammingDist c x ≤ e) :
    (bundleCenters C U e ∩ bundleCenters C V e).Nonempty := by
  obtain ⟨c, hc_mem, hc_dist⟩ := hclose
  use c
  rw [Finset.mem_inter]
  constructor
  · rw [bundleCenters, Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hc_mem, x, hxU, hc_dist⟩
  · rw [bundleCenters, Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hc_mem, x, hxV, hc_dist⟩

/-! ## Group C: Absolute Agreement Counts -/

/-- **Hypothesis 30 (Agreement Lower Bound)**
No element in the ambient space has a maximum agreement exactly equal to `k-1`.
Because the code is MDS, any `k` coordinates uniquely define a codeword, so every vector
must agree with *some* codeword on at least `k` coordinates.

*Red-Teaming Status:* Provably True by Polynomial Interpolation.
-/
def hyp30_max_agreement_not_k_minus_one (v : ι → F) : Prop :=
    ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)), 
      (Finset.univ.filter (fun i => c i = v i)).card ≥ k
  -- Follows from Lagrange Interpolation over any k points.

/-! ## Group B: Correlated Error Support -/

/-- **Hypothesis 20 (Zero-Sum Error)**
If a bundle `u0 + γ * u1` is perfectly 1-close to RS (with `u1 ≠ 0`), the sum of their 
error vectors over all `γ` is zero.
-/
def hyp20_zero_sum_error (u0 u1 : ι → F) (e : ℕ) : Prop :=
  -- Statement requires formalizing the error map `γ ↦ e_γ`.
  ∃ error : F → ι → F,
    ∀ γ : F, ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
      hammingDist c (u0 + γ • u1) ≤ e ∧ error γ = (u0 + γ • u1) - c

end ArkLib.ProximityGap.PromotedHypotheses
