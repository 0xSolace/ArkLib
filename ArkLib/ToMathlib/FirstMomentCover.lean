import Mathlib

/-! Scratch: generic cover-cardinality + first-moment assembly for MCA bad scalars (#67). -/

open Finset

namespace ProximityGap.FirstMomentCover

/-- **Generic cover bound.** If every element of `Bad` lies in some witness set `W b` for a
`b` in the carrier `L`, then `|Bad| ≤ ∑_{b∈L} |W b|`. -/
theorem card_le_sum_card_of_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Bad : Finset α) (L : Finset β) (W : β → Finset α)
    (hcover : ∀ a ∈ Bad, ∃ b ∈ L, a ∈ W b) :
    Bad.card ≤ ∑ b ∈ L, (W b).card := by
  classical
  calc Bad.card ≤ (L.biUnion W).card := by
        apply Finset.card_le_card
        intro a ha
        obtain ⟨b, hb, hab⟩ := hcover a ha
        exact Finset.mem_biUnion.mpr ⟨b, hb, hab⟩
    _ ≤ ∑ b ∈ L, (W b).card := Finset.card_biUnion_le

/-- **Uniform per-witness sharpening.** If additionally every witness set has card `≤ B`, then
`|Bad| ≤ |L| · B`. -/
theorem card_le_card_mul_of_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Bad : Finset α) (L : Finset β) (W : β → Finset α) (B : ℕ)
    (hcover : ∀ a ∈ Bad, ∃ b ∈ L, a ∈ W b)
    (hB : ∀ b ∈ L, (W b).card ≤ B) :
    Bad.card ≤ L.card * B := by
  calc Bad.card ≤ ∑ b ∈ L, (W b).card := card_le_sum_card_of_cover Bad L W hcover
    _ ≤ ∑ _b ∈ L, B := Finset.sum_le_sum hB
    _ = L.card * B := by rw [Finset.sum_const, smul_eq_mul]

/-- **Real-valued first-moment assembly.** With the per-witness real bound `(W b).card ≤ b₀`
and a carrier of size `≤ ℓ`, the bad count is `≤ ℓ · b₀`. This is the shape consumed by the
epsMCA supremum-to-count plumbing: `|mcaBad| ≤ ℓ · (2δn)` ⟹ `ε_mca ≤ ℓ·2δn/|F| = 2ℓδ`. -/
theorem card_le_real_of_cover {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Bad : Finset α) (L : Finset β) (W : β → Finset α) (ℓ b₀ : ℝ)
    (hcover : ∀ a ∈ Bad, ∃ b ∈ L, a ∈ W b)
    (hB : ∀ b ∈ L, ((W b).card : ℝ) ≤ b₀) (hb0 : 0 ≤ b₀)
    (hL : (L.card : ℝ) ≤ ℓ) :
    (Bad.card : ℝ) ≤ ℓ * b₀ := by
  calc (Bad.card : ℝ) ≤ ((∑ b ∈ L, (W b).card : ℕ) : ℝ) := by
        exact_mod_cast card_le_sum_card_of_cover Bad L W hcover
    _ = ∑ b ∈ L, ((W b).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ _b ∈ L, b₀ := Finset.sum_le_sum hB
    _ = (L.card : ℝ) * b₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ℓ * b₀ := by exact mul_le_mul_of_nonneg_right hL hb0

#print axioms ProximityGap.FirstMomentCover.card_le_sum_card_of_cover
#print axioms ProximityGap.FirstMomentCover.card_le_card_mul_of_cover
#print axioms ProximityGap.FirstMomentCover.card_le_real_of_cover

end ProximityGap.FirstMomentCover
