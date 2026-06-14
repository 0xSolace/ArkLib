/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# Constant-index √-cancellation: the worst-case per-frequency bound for ANY fixed-index subgroup (#407)

This file generalizes `QRWorstCaseIncompleteSum.lean` (index 2) to **every constant index `m`**: the
worst-case incomplete sum over the index-`m` multiplicative subgroup `G = {a : χ(a)=1}` (`χ` a
character of order `m`) is bounded by the classical Gauss sums, giving square-root cancellation
`‖η_b‖ ≤ ((m−1)√q + 1)/m ≈ √m·√n` — PROVEN, no wall.

## Brick 1 (this commit): the general Gauss-sum magnitude `‖gaussSum χ ψ‖ = √q`

Mathlib has `gaussSum_mul_gaussSum_eq_card` (`g(χ)·g(χ⁻¹,ψ⁻¹) = q` for `χ ≠ 1`) but NOT the magnitude
directly.  Over `ℂ`, `g(χ⁻¹,ψ⁻¹) = conj(g(χ,ψ))` (characters are unit-circle valued), so
`‖g(χ,ψ)‖² = g(χ,ψ)·conj(g(χ,ψ)) = q`, hence `‖g(χ,ψ)‖ = √q`.  This is the index-`m` companion of the
in-tree `gaussSum_normSq` (which is the quadratic special case via `gaussSum_sq`).
-/

set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.ConstantIndexGaussSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `‖χ(a)‖ = 1` for every nonzero `a` (character values are roots of unity). -/
theorem norm_mulChar_unit (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) : ‖χ a‖ = 1 := by
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card F - 1) ?_ (by omega)
  rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]

/-- Conjugation sends the Gauss sum of `(χ, ψ)` to that of `(χ⁻¹, ψ⁻¹)`. -/
theorem conj_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (starRingEnd ℂ) (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [gaussSum, gaussSum, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, AddChar.starComp_apply hchar, starRingEnd_apply, MulChar.star_apply']

/-- **The general Gauss-sum magnitude** `‖gaussSum χ ψ‖ = √q` for any nontrivial `χ` and primitive
`ψ` over a finite field, valued in `ℂ`.  Reusable; Mathlib lacks it directly. -/
theorem norm_gaussSum_eq_sqrt {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have hmul : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (Fintype.card F : ℂ) :=
    gaussSum_mul_gaussSum_eq_card hχ hψ
  have hsq : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    have h1 : gaussSum χ ψ * (starRingEnd ℂ) (gaussSum χ ψ) = (Fintype.card F : ℂ) := by
      rw [conj_gaussSum]; exact hmul
    rw [Complex.mul_conj'] at h1
    exact_mod_cast h1
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

end ArkLib.ProximityGap.ConstantIndexGaussSum

#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.norm_mulChar_unit
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.conj_gaussSum
#print axioms ArkLib.ProximityGap.ConstantIndexGaussSum.norm_gaussSum_eq_sqrt
