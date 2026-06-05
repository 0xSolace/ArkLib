/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# `johnson_bound_lambda_le_ell` is *false* as stated (statement-level refutation)

`ArkLib/Data/CodingTheory/JohnsonBound/Family.lean` carries a documented `sorry` for
`johnson_bound_lambda_le_ell` (ABF26 Theorem 3.2):

  for any code `C ⊆ Σ^n` with `|Σ| = q` and `ℓ ≥ 2`,
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`,  where  `δ_min(C) = minDist(C)/n`.

This file proves the statement is **not a theorem as stated**: there is a concrete instance
in which the conclusion fails.  The `sorry` therefore cannot be honestly discharged — the
statement needs a hypothesis repair (a proximity bound on `δ_min` keeping the square-root
argument nonnegative).

## Why it is false

`Jqℓ q ℓ δ = (1 - 1/q) · (1 - √(1 - (q/(q-1))·(ℓ/(ℓ-1))·δ))`.  The standard q-ary
ℓ-Johnson bound is only valid in the regime where the square-root argument
`1 - (q/(q-1))·(ℓ/(ℓ-1))·δ` is **nonnegative**; the Lean statement carries no such
hypothesis.  Mathlib's `Real.sqrt` returns `0` on negative inputs, so once
`(q/(q-1))·(ℓ/(ℓ-1))·δ > 1` the radius collapses to the meaninglessly large value
`(1 - 1/q)`, and a ball of that radius can contain far more than `ℓ` codewords.

## The witness

Take `ι = Fin 2` (so `n = |ι| = 2`), `α = Fin 2` (so `q = 2`), `ℓ = 2`, and the explicit
three-word code

  `C = { ![0,0], ![0,1], ![1,0] } ⊆ (Fin 2 → Fin 2)`.

* `minDist(C) = 1` (the closest distinct pair `![0,0], ![0,1]` differs in one coordinate),
  so `δ_min = 1/2`.
* `(q/(q-1))·(ℓ/(ℓ-1))·δ_min = 2·2·(1/2) = 2 > 1`, hence the square-root argument is
  `1 - 2 = -1 < 0`, `√(-1) = 0`, and `Jqℓ 2 2 (1/2) = (1 - 1/2)·(1 - 0) = 1/2`.
* Centring at `f = ![0,0]`, all three codewords lie within relative distance `1/2`
  (distances `0, 1/2, 1/2`), so `closeCodewordsRel C f (1/2) = C` has `ncard = 3` and
  `Λ(C, 1/2) ≥ 3 > 2 = ℓ`.

Hence `|Λ(C, J_{q,ℓ}(δ_min(C)))| = 3 > 2 = ℓ`, refuting the statement.
-/

set_option linter.unusedSectionVars false

namespace JohnsonBound.FamilyRefutation

open ListDecodable JohnsonBound Code

/-- The refuting alphabet/index types: `ι = α = Fin 2` (so `n = 2`, `q = 2`). -/
abbrev ι : Type := Fin 2
abbrev α : Type := Fin 2

/-- The three codewords. -/
def c0 : ι → α := ![0, 0]
def c1 : ι → α := ![0, 1]
def c2 : ι → α := ![1, 0]

/-- The explicit refuting code `C = { ![0,0], ![0,1], ![1,0] }`. -/
def C : Set (ι → α) := {c0, c1, c2}

/-- The three codewords are pairwise distinct. -/
theorem c0_ne_c1 : c0 ≠ c1 := by decide
theorem c0_ne_c2 : c0 ≠ c2 := by decide
theorem c1_ne_c2 : c1 ≠ c2 := by decide

/-- Pairwise Hamming distances. -/
theorem ham_c0_c1 : hammingDist c0 c1 = 1 := by decide
theorem ham_c0_c2 : hammingDist c0 c2 = 1 := by decide
theorem ham_c1_c2 : hammingDist c1 c2 = 2 := by decide

/-- Membership in `C` is membership in the explicit three-element set. -/
theorem mem_C_iff (x : ι → α) : x ∈ C ↔ x = c0 ∨ x = c1 ∨ x = c2 := by
  simp only [C, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair
`(c0, c1)` attains `1`.  Hence `Code.minDist C = 1`. -/
theorem minDist_C : Code.minDist C = 1 := by
  apply le_antisymm
  · -- `minDist C ≤ 1`: the value `1` is in the defining set (witnessed by `c0, c1`).
    refine Nat.sInf_le ?_
    refine ⟨c0, ?_, c1, ?_, c0_ne_c1, ham_c0_c1⟩
    · exact (mem_C_iff c0).mpr (Or.inl rfl)
    · exact (mem_C_iff c1).mpr (Or.inr (Or.inl rfl))
  · -- `1 ≤ minDist C`: every member `d` of the defining set has `d ≥ 1`.
    refine le_csInf ⟨1, ⟨c0, (mem_C_iff c0).mpr (Or.inl rfl), c1,
      (mem_C_iff c1).mpr (Or.inr (Or.inl rfl)), c0_ne_c1, ham_c0_c1⟩⟩ ?_
    rintro d ⟨u, _, v, _, huv, rfl⟩
    -- `hammingDist u v ≥ 1` since `u ≠ v`.
    exact Nat.one_le_iff_ne_zero.mpr (by simpa [hammingDist_eq_zero] using huv)

/-- **The Johnson radius collapses to `1/2` at this `(q, ℓ, δ)`.**
With `q = 2`, `ℓ = 2`, `δ = 1/2` the square-root argument is
`1 - (2/(2-1))·(2/(2-1))·(1/2) = 1 - 2 = -1 < 0`, so `Real.sqrt (-1) = 0` and
`Jqℓ 2 2 (1/2) = (1 - 1/2)·(1 - 0) = 1/2`. -/
theorem Jqℓ_eq_half : Jqℓ (2 : ℚ) (2 : ℚ) ((1 : ℚ) / 2) = (1 / 2 : ℝ) := by
  norm_num [Jqℓ, Real.sqrt_eq_zero_of_nonpos]

/-- `card ι = 2`. -/
theorem card_ι : Fintype.card ι = 2 := by decide

/-- Each codeword lies within relative distance `1/2` of the centre `c0`.
The relative distances are `0, 1/2, 1/2`, all `≤ 1/2`. -/
theorem relDist_le_half (c : ι → α) (hc : c = c0 ∨ c = c1 ∨ c = c2) :
    ((Code.relHammingDist c0 c : ℚ≥0) : ℝ) ≤ (1 / 2 : ℝ) := by
  have hcard : (Fintype.card ι : ℚ≥0) = 2 := by rw [card_ι]; rfl
  rcases hc with rfl | rfl | rfl
  · -- distance `0`
    have h0 : Code.relHammingDist c0 c0 = 0 := by
      rw [Code.relHammingDist, hammingDist_self]; simp
    rw [h0]; norm_num
  · -- distance `1/2`
    have h1 : Code.relHammingDist c0 c1 = 1 / 2 := by
      rw [Code.relHammingDist, ham_c0_c1, hcard]; norm_num
    rw [h1]; push_cast; norm_num
  · -- distance `1/2`
    have h2 : Code.relHammingDist c0 c2 = 1 / 2 := by
      rw [Code.relHammingDist, ham_c0_c2, hcard]; norm_num
    rw [h2]; push_cast; norm_num

/-- **The ball of radius `1/2` about `c0` contains the whole code.**
`closeCodewordsRel C c0 (1/2) = C`. -/
theorem closeCodewordsRel_eq_C :
    closeCodewordsRel C c0 (1 / 2 : ℝ) = C := by
  ext c
  simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hcC, _⟩; exact hcC
  · intro hcC
    refine ⟨hcC, ?_⟩
    rcases (mem_C_iff c).mp hcC with rfl | rfl | rfl
    · simp [Code.relHammingDist]
    · rw [Code.relHammingDist, ham_c0_c1, card_ι]
      norm_num
    · rw [Code.relHammingDist, ham_c0_c2, card_ι]
      norm_num

/-- The refuting code has exactly three codewords. -/
theorem ncard_C : C.ncard = 3 := by
  rw [C, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simp only [Set.mem_singleton_iff]; exact c1_ne_c2
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨c0_ne_c1, c0_ne_c2⟩

/-- **`Λ(C, 1/2) ≥ 3`.**  The point-list at the centre `c0` is all of `C`, with
`ncard = 3`, and `Lambda` is the supremum over centres. -/
theorem three_le_Lambda : (3 : ℕ∞) ≤ Lambda C (1 / 2 : ℝ) := by
  have hpt : ((closeCodewordsRel C c0 (1 / 2 : ℝ)).ncard : ℕ∞) ≤ Lambda C (1 / 2 : ℝ) :=
    le_iSup (fun f : ι → α => ((closeCodewordsRel C f (1 / 2 : ℝ)).ncard : ℕ∞)) c0
  rw [closeCodewordsRel_eq_C, ncard_C] at hpt
  exact hpt

/-- **ABF26 Theorem 3.2 (`johnson_bound_lambda_le_ell`) is FALSE as stated.**

For the concrete code `C = { ![0,0], ![0,1], ![1,0] } ⊆ (Fin 2 → Fin 2)` and `ℓ = 2`,
the conclusion `Lambda C (Jqℓ q ℓ δ_min) ≤ ℓ` FAILS: the left side is `≥ 3` while the
right side is `2`.

The failure is intrinsic to the unconditioned statement: `δ_min = 1/2` pushes the
square-root argument of `Jqℓ` negative, `Real.sqrt` clamps it to `0`, and the Johnson
"radius" collapses to `1/2`, a ball that swallows the entire code. The theorem needs a
proximity hypothesis (`(q/(q-1))·(ℓ/(ℓ-1))·δ_min ≤ 1`) that the present statement lacks. -/
theorem johnson_bound_lambda_le_ell_false :
    ¬ (let q : ℚ := Fintype.card α
       let δ_min : ℚ := Code.minDist C / Fintype.card ι
       Lambda C (Jqℓ q 2 δ_min) ≤ (2 : ℕ∞)) := by
  -- rewrite the radius to `1/2`: `q = 2`, `δ_min = minDist C / card ι = 1/2`.
  have hradius : Jqℓ ((Fintype.card α : ℚ)) 2 ((Code.minDist C : ℚ) / Fintype.card ι)
      = (1 / 2 : ℝ) := by
    have hq : (Fintype.card α : ℚ) = 2 := by rw [show Fintype.card α = 2 from by decide]; rfl
    have hδ : ((Code.minDist C : ℚ) / Fintype.card ι) = 1 / 2 := by
      rw [minDist_C, card_ι]
      norm_num
    rw [hq, hδ, Jqℓ_eq_half]
  simp only [hradius]
  -- `Lambda C (1/2) ≥ 3 > 2`.
  intro hle
  exact absurd (le_trans three_le_Lambda hle) (by decide)

end JohnsonBound.FamilyRefutation
