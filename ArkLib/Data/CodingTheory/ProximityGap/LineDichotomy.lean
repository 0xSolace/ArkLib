/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Abel

/-!
# The proximity-gap line dichotomy

A core ingredient of the unique-decoding-regime proximity gap / MCA upper bound: if two
distinct points of an affine line `{u₀ + γ·u₁}` are close to the code, then `u₁`
(and symmetrically `u₀`) is itself close to the code. This is the "either at most one
close point, or the whole line has structure" dichotomy.

* `u1_close_of_two_line_points` — two distinct close line points, witnessed by codewords
  `w₁, w₂` on sets `S₁, S₂`, imply that `u₁` agrees with
  `(γ₁ - γ₂)⁻¹ • (w₁ - w₂) ∈ C` on the overlap `S₁ ∩ S₂`.
* `card_inter_ge` — `|S₁| + |S₂| ≤ n + |S₁ ∩ S₂|`, so two large witness sets have
  a controlled overlap.

Combined with bad-scalar counting and minimum-distance codeword uniqueness, these are the
elementary linear-algebra bricks behind the below-unique-decoding-radius MCA upper bound.

All results are hole-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. #232.
- [BCIKS20] Proximity gaps for Reed-Solomon codes.
-/

namespace ProximityGap

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F]
variable {A : Type*} [AddCommGroup A] [Module F A]

/-- **Proximity-gap dichotomy (half).** If two distinct points of the affine line
`{u₀ + γ • u₁}` are close to `C`, witnessed by codewords `w₁, w₂` agreeing with the
line on `S₁, S₂`, then `u₁` agrees with the codeword
`(γ₁ - γ₂)⁻¹ • (w₁ - w₂) ∈ C` on the overlap `S₁ ∩ S₂`. -/
theorem u1_close_of_two_line_points (C : Submodule F (ι → A)) (u₀ u₁ : ι → A)
    {γ₁ γ₂ : F} (hne : γ₁ ≠ γ₂) {S₁ S₂ : Finset ι} {w₁ w₂ : ι → A}
    (hw₁ : w₁ ∈ C) (h₁ : ∀ i ∈ S₁, w₁ i = u₀ i + γ₁ • u₁ i)
    (hw₂ : w₂ ∈ C) (h₂ : ∀ i ∈ S₂, w₂ i = u₀ i + γ₂ • u₁ i) :
    ∃ c ∈ C, ∀ i ∈ S₁ ∩ S₂, c i = u₁ i := by
  have hd : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨(γ₁ - γ₂)⁻¹ • (w₁ - w₂), C.smul_mem _ (C.sub_mem hw₁ hw₂), ?_⟩
  intro i hi
  rw [Finset.mem_inter] at hi
  have hwi : (w₁ - w₂) i = (γ₁ - γ₂) • u₁ i := by
    have e₁ := h₁ i hi.1
    have e₂ := h₂ i hi.2
    simp only [Pi.sub_apply, e₁, e₂, sub_smul]
    abel
  simp only [Pi.smul_apply, hwi, inv_smul_smul₀ hd]

/-- The overlap of two witness sets is large: `|S₁| + |S₂| ≤ n + |S₁ ∩ S₂|`. -/
theorem card_inter_ge [Fintype ι] (S₁ S₂ : Finset ι) :
    S₁.card + S₂.card ≤ Fintype.card ι + (S₁ ∩ S₂).card := by
  have hun : (S₁ ∪ S₂).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (S₁ ∪ S₂)
  have hui : (S₁ ∪ S₂).card + (S₁ ∩ S₂).card = S₁.card + S₂.card :=
    Finset.card_union_add_card_inter S₁ S₂
  omega

#print axioms u1_close_of_two_line_points
#print axioms card_inter_ge

end ProximityGap
