import ArkLib.Data.CodingTheory.ProximityGap.LamLeungMultisetAntipodal
import Mathlib.Tactic

set_option linter.style.longLine false
set_option autoImplicit false

/-! Scratch: the per-P fiber count for shape-(2,1). If this lands, shape-(2,1)=360 follows by
summing over P. Fiber bijection: c ↦ ({i∈P : c i = x}, {i∈Pᶜ : c i = y}) to a product of
two `powersetCard`s. -/

open Finset

namespace E3Shape21Scratch

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The per-`P` fiber count: tuples `c : Fin 6 → F` that are `±x` on `P` (balanced: `|P|/2` x's)
and `±y` off `P` (balanced: `|Pᶜ|/2` y's) number `C(|P|,|P|/2)·C(|Pᶜ|,|Pᶜ|/2)`. (Here `x,-x,y,-y`
are 4 distinct values.) -/
theorem fiber_card (P : Finset (Fin 6)) (x y : F)
    (hx : x ≠ -x) (hy : y ≠ -y) (hxy : x ≠ y) (hxy' : x ≠ -y) (hmxy : -x ≠ y) (hmxy' : -x ≠ -y) :
    ((Finset.univ.filter (fun c : Fin 6 → F =>
        (∀ i, i ∈ P → (c i = x ∨ c i = -x)) ∧ (∀ i, i ∉ P → (c i = y ∨ c i = -y))
        ∧ (Finset.univ.filter (fun i => c i = x)).card = P.card / 2
        ∧ (Finset.univ.filter (fun i => c i = y)).card = Pᶜ.card / 2))).card
      = Nat.choose P.card (P.card / 2) * Nat.choose Pᶜ.card (Pᶜ.card / 2) := by
  classical
  -- value distinctness helpers
  have hxny : x ≠ -y := hxy'
  rw [show Nat.choose P.card (P.card / 2) * Nat.choose Pᶜ.card (Pᶜ.card / 2)
        = ((P.powersetCard (P.card / 2)) ×ˢ (Pᶜ.powersetCard (Pᶜ.card / 2))).card by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]]
  refine Finset.card_nbij'
    (fun c => (P.filter (fun i => c i = x), Pᶜ.filter (fun i => c i = y)))
    (fun pr => fun i => if i ∈ pr.1 then x else if i ∈ P then -x else if i ∈ pr.2 then y else -y)
    ?_ ?_ ?_ ?_
  · -- forward into the product
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hP, hPc, hxk, hyk⟩ := hc
    -- x occurs only on P
    have hxonP : Finset.univ.filter (fun i => c i = x) = P.filter (fun i => c i = x) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; refine ⟨?_, h⟩
        by_contra hiP
        rcases hPc i hiP with h' | h'
        · exact hxy (h.symm.trans h')
        · exact hxy' (h.symm.trans h')
      · exact fun h => h.2
    have hyonPc : Finset.univ.filter (fun i => c i = y) = Pᶜ.filter (fun i => c i = y) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
      constructor
      · intro h; refine ⟨?_, h⟩
        intro hmem
        rcases hP i hmem with h' | h'
        · exact hxy (h'.symm.trans h)
        · exact hmxy (h'.symm.trans h)
      · exact fun h => h.2
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨Finset.filter_subset _ _, ?_⟩, ⟨Finset.filter_subset _ _, ?_⟩⟩
    · rw [← hxonP]; exact hxk
    · rw [← hyonPc]; exact hyk
  · -- backward into the fiber
    intro pr hpr
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hpr
    obtain ⟨⟨hAxP, hAxc⟩, ⟨hAyPc, hAyc⟩⟩ := hpr
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hiP
      by_cases h : i ∈ pr.1
      · left; simp [h]
      · right; simp [h, hiP]
    · intro i hiP
      have hiAx : i ∉ pr.1 := fun h => hiP (hAxP h)
      by_cases h : i ∈ pr.2
      · left; simp [hiAx, hiP, h]
      · right; simp [hiAx, hiP, h]
    · -- #x = |Ax| = |P|/2
      rw [show (Finset.univ.filter (fun i => (if i ∈ pr.1 then x else if i ∈ P then -x else if i ∈ pr.2 then y else -y) = x)) = pr.1 from ?_, hAxc]
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h : i ∈ pr.1
      · simp [h]
      · by_cases h2 : i ∈ P
        · simp [h, h2, (Ne.symm hx)]
        · by_cases h3 : i ∈ pr.2
          · simp [h, h2, h3, Ne.symm hxy]
          · simp [h, h2, h3, Ne.symm hxy']
    · rw [show (Finset.univ.filter (fun i => (if i ∈ pr.1 then x else if i ∈ P then -x else if i ∈ pr.2 then y else -y) = y)) = pr.2 from ?_, hAyc]
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hAyP : i ∈ pr.2 → i ∉ P := fun h hP => by
        have := hAyPc h; rw [Finset.mem_compl] at this; exact this hP
      by_cases h : i ∈ pr.1
      · have hiP : i ∈ P := hAxP h
        have hi2 : i ∉ pr.2 := fun hh => (Finset.mem_compl.mp (hAyPc hh)) hiP
        simp [h, hxy, hi2]
      · by_cases h2 : i ∈ P
        · have hi2 : i ∉ pr.2 := fun hh => (Finset.mem_compl.mp (hAyPc hh)) h2
          simp [h, h2, hmxy, hi2]
        · by_cases h3 : i ∈ pr.2
          · simp [h, h2, h3]
          · simp [h, h2, h3, (Ne.symm hy)]
  · -- left inverse
    intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hP, hPc, _, _⟩ := hc
    funext i
    by_cases h : i ∈ P
    · rcases hP i h with h' | h'
      · simp only; rw [if_pos (Finset.mem_filter.mpr ⟨h, h'⟩)]; exact h'.symm
      · have hnx : i ∉ P.filter (fun j => c j = x) := by
          simp only [Finset.mem_filter, not_and]; intro _; rw [h']; exact (Ne.symm hx)
        simp only; rw [if_neg hnx, if_pos h]; exact h'.symm
    · rcases hPc i h with h' | h'
      · have hnx : i ∉ P.filter (fun j => c j = x) := fun hh => h (Finset.mem_filter.mp hh).1
        have hy' : i ∈ Pᶜ.filter (fun j => c j = y) := Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr h, h'⟩
        simp only; rw [if_neg hnx, if_neg h, if_pos hy']; exact h'.symm
      · have hnx : i ∉ P.filter (fun j => c j = x) := fun hh => h (Finset.mem_filter.mp hh).1
        have hny : i ∉ Pᶜ.filter (fun j => c j = y) := by
          simp only [Finset.mem_filter, not_and]; intro _; rw [h']; exact (Ne.symm hy)
        simp only; rw [if_neg hnx, if_neg h, if_neg hny]; exact h'.symm
  · -- right inverse
    intro pr hpr
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hpr
    obtain ⟨⟨hAxP, _⟩, ⟨hAyPc, _⟩⟩ := hpr
    have hAyP : ∀ i ∈ pr.2, i ∉ P := fun i h hP => by
      have := hAyPc h; rw [Finset.mem_compl] at this; exact this hP
    refine Prod.ext ?_ ?_
    · ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hiP, hval⟩
        by_cases h : i ∈ pr.1
        · exact h
        · exfalso; rw [if_neg h, if_pos hiP] at hval; exact (Ne.symm hx) hval
      · intro h; exact ⟨hAxP h, by rw [if_pos h]⟩
    · ext i
      simp only [Finset.mem_filter, Finset.mem_compl]
      constructor
      · rintro ⟨hiP, hval⟩
        by_cases h : i ∈ pr.2
        · exact h
        · exfalso
          by_cases h1 : i ∈ pr.1
          · rw [if_pos h1] at hval; exact hxy hval
          · rw [if_neg h1, if_neg hiP, if_neg h] at hval; exact (Ne.symm hy) hval
      · intro h
        refine ⟨hAyP i h, ?_⟩
        have h1 : i ∉ pr.1 := fun hh => (hAyP i h) (hAxP hh)
        rw [if_neg h1, if_neg (hAyP i h), if_pos h]

end E3Shape21Scratch

#print axioms E3Shape21Scratch.fiber_card
