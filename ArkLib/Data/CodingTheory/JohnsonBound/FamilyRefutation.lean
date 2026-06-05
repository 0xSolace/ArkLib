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
  unfold Jqℓ
  -- the `let`-bound `frac`, `lFac` evaluate to `2`; the radicand is `(-1 : ℝ)`.
  have hrad : ((1 - (2 / (2 - 1)) * (2 / (2 - 1)) * (1 / 2) : ℚ) : ℝ) = (-1 : ℝ) := by
    norm_num
  simp only
  rw [hrad, Real.sqrt_eq_zero_of_nonpos (by norm_num)]
  norm_num

end JohnsonBound.FamilyRefutation
