/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# `johnson_bound_lambda_le_ell` needs a missing radius-regime hypothesis

`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean` carries a documented residual for
`johnson_bound_lambda_le_ell` (ABF26 Theorem 3.2). This file records the concrete bad
parameter regime behind that residual: for `q = 2`, `ell = 2`, and `delta = 1/2`, the
Johnson-radius radicand is negative, so Lean's `Real.sqrt` clamps it to `0` and
`Jqell 2 2 (1/2) = 1/2`.

The explicit three-word binary length-two code below has minimum distance `1`, hence
`delta_min = 1/2`. The remaining Lambda-cardinality contradiction is deliberately not
claimed here; it requires a small but fiddly `closeCodewordsRel` decidable-instance
transport. The verified pieces below are the statement-repair spine: the code witness,
its minimum distance, and the radius collapse.
-/

namespace JohnsonBound.FamilyRefutation

open JohnsonBound Code

/-- The refuting alphabet/index types: `iota = alpha = Fin 2`. -/
abbrev ι : Type := Fin 2
abbrev α : Type := Fin 2

/-- The three codewords. -/
def c0 : ι → α := ![0, 0]
def c1 : ι → α := ![0, 1]
def c2 : ι → α := ![1, 0]

/-- The explicit three-word code. -/
def C : Set (ι → α) := {c0, c1, c2}

theorem c0_ne_c1 : c0 ≠ c1 := by decide
theorem c0_ne_c2 : c0 ≠ c2 := by decide
theorem c1_ne_c2 : c1 ≠ c2 := by decide

theorem ham_c0_c1 : hammingDist c0 c1 = 1 := by decide
theorem ham_c0_c2 : hammingDist c0 c2 = 1 := by decide
theorem ham_c1_c2 : hammingDist c1 c2 = 2 := by decide

theorem mem_C_iff (x : ι → α) : x ∈ C ↔ x = c0 ∨ x = c1 ∨ x = c2 := by
  simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- `card iota = 2`. -/
theorem card_ι : Fintype.card ι = 2 := by decide

/-- Every distinct pair of codewords has Hamming distance at least `1`, and `c0,c1` attain it. -/
theorem minDist_C : Code.minDist C = 1 := by
  apply le_antisymm
  · refine Nat.sInf_le ?_
    refine ⟨c0, ?_, c1, ?_, c0_ne_c1, ham_c0_c1⟩
    · exact (mem_C_iff c0).mpr (Or.inl rfl)
    · exact (mem_C_iff c1).mpr (Or.inr (Or.inl rfl))
  · refine le_csInf ⟨1, ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩⟩ ?_
    rintro d ⟨u, _, v, _, huv, rfl⟩
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [hammingDist_eq_zero] using huv)

/-- The Johnson radius collapses to `1/2` at `q = ell = 2`, `delta = 1/2`. -/
theorem Jqℓ_eq_half : Jqℓ (2 : ℚ) (2 : ℚ) ((1 : ℚ) / 2) = (1 / 2 : ℝ) := by
  norm_num [Jqℓ, Real.sqrt_eq_zero_of_nonpos]

/-- The witness has `delta_min = 1/2`. -/
theorem delta_min_C_eq_half : ((Code.minDist C : ℚ) / Fintype.card ι) = 1 / 2 := by
  norm_num [minDist_C, card_ι]

end JohnsonBound.FamilyRefutation
