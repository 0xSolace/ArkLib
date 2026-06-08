import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

open Finset
open scoped NNReal

namespace ArkLib.ProximityGap.PromotedHypotheses

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι)

/-- The "Decoding List" of a received word `r` at radius `e` -/
def decList (C : Finset (ι → F)) (r : ι → F) (e : ℕ) : Finset (ι → F) :=
  C.filter (fun c => hammingDist c r ≤ e)

/-- The "List of Centers" of a bundle `U` at radius `e` is the union of the decoding lists of its elements. -/
def bundleCenters (C : Finset (ι → F)) (U : Finset (ι → F)) (e : ℕ) : Finset (ι → F) :=
  Finset.univ.filter (fun c => c ∈ C ∧ (U.filter (fun u => hammingDist c u ≤ e)).Nonempty)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem hyp45_list_intersection (C : Finset (ι → F)) (U V : Finset (ι → F)) (e : ℕ) (x : ι → F)
    (hxU : x ∈ U) (hxV : x ∈ V) (hclose : ∃ c ∈ C, hammingDist c x ≤ e) :
    (bundleCenters C U e ∩ bundleCenters C V e).Nonempty := by
  obtain ⟨c, hc_mem, hc_dist⟩ := hclose
  use c
  rw [Finset.mem_inter]
  constructor
  · rw [bundleCenters, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, hc_mem, ?_⟩
    rw [Finset.filter_nonempty_iff]
    exact ⟨x, hxU, hc_dist⟩
  · rw [bundleCenters, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, hc_mem, ?_⟩
    rw [Finset.filter_nonempty_iff]
    exact ⟨x, hxV, hc_dist⟩

include hk in
theorem hyp30_max_agreement_not_k_minus_one (v : ι → F) :
    ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)), 
      (Finset.univ.filter (fun i => c i = v i)).card ≥ k := by
  have hk' : k ≤ Finset.card (Finset.univ : Finset ι) := by rw [Finset.card_univ]; exact hk
  obtain ⟨S, _, hS_card⟩ := Finset.exists_subset_card_eq hk'
  let f : F → F := fun x => if hx : ∃ i ∈ S, domain i = x then v (Classical.choose hx) else 0
  let p := Polynomial.Lagrange.interpolate (S.map domain.toEmbedding) id f
  let c : ι → F := fun i => p.eval (domain i)
  use c
  constructor
  · apply ReedSolomon.mem_code_of_degree_lt
    have h_deg := Polynomial.Lagrange.degree_interpolate_lt f (Set.injOn_id ↑(S.map domain.toEmbedding))
    rw [Finset.card_map, hS_card] at h_deg
    exact h_deg
  · apply Finset.card_le_of_subset
    intro i hi
    simp only [mem_filter, mem_univ, true_and]
    apply congrArg
    have h_mem : domain i ∈ S.map domain.toEmbedding := Finset.mem_map_of_mem domain.toEmbedding hi
    have eval_eq := Polynomial.Lagrange.eval_interpolate_at_node f (Set.injOn_id ↑(S.map domain.toEmbedding)) h_mem
    dsimp [c, p]
    rw [eval_eq]
    dsimp [f]
    have hx : ∃ j ∈ S, domain j = domain i := ⟨i, hi, rfl⟩
    have hx_choose := Classical.choose_spec hx
    have h_choose_eq : domain (Classical.choose hx) = domain i := hx_choose.2
    have h_i : Classical.choose hx = i := domain.injective h_choose_eq
    rw [dif_pos hx, h_i]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
theorem hyp8_translation_invariance (x y c : ι → F) :
    hammingDist (x + c) (y + c) = hammingDist x y := by
  dsimp [hammingDist, dist]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h heq; apply h; rw [heq]
  · intro h heq; apply h; exact add_right_cancel heq

omit [DecidableEq ι] [DecidableEq F] [Fintype ι] in
theorem hyp7_barycentric_center (c_map : F → (ι → F)) 
    (h_valid : ∀ γ : F, c_map γ ∈ (ReedSolomon.code domain k : Set (ι → F))) :
    (∑ γ : F, c_map γ) ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
  exact Submodule.sum_mem (ReedSolomon.code domain k) fun γ _ => h_valid γ

end ArkLib.ProximityGap.PromotedHypotheses
