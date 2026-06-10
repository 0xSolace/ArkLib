/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Core
import ArkLib.Data.CodingTheory.ProximityGap.MCAUDRBound
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson

/-!
# The Johnson numeric bound dominates the unique-decoding error

`johnsonBoundReal` (the [Hab25] Theorem 2 numeric form) is at least `n/q`: the
unique-decoding MCA error `|ι|/|F|` (`epsMCA_rs_udr_le_full`) never exceeds the
Johnson-range budget.  This is the arithmetic half of the first *unconditional*
instance of `JohnsonNumericBound` — below the unique-decoding radius the numeric
edge holds outright, since the in-tree UD bound is stronger than the Johnson budget.

The slack is large: with `m ≥ 3` the leading coefficient is
`2·(m+1/2)⁵/(3·ρ₊^{3/2}) ≥ 2·3.5⁵/12 > 87`, so the budget exceeds `n/q` by two
orders of magnitude; the proof only needs `1 ≤` that coefficient.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
-/

namespace CodingTheory

open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F]

/-- The standalone real-arithmetic core: the [Hab25] numeric formula dominates `n/q`
whenever `1 ≤ n`, `0 < ρ ≤ 2`, `3 ≤ m`, and the remaining quantities are nonnegative. -/
theorem hab25_formula_ge_n_div_q
    {n q ρ m d : ℝ} (hn : 1 ≤ n) (hq : 0 < q)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hm : 3 ≤ m) (hd : 0 ≤ d) :
    n / q ≤ ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * d * ρ)
        / (3 * ρ ^ ((3 : ℝ) / 2)) * n
      + (m + 1/2) / ρ ^ ((1 : ℝ) / 2)) / q := by
  have hm0 : (0 : ℝ) ≤ m + 1/2 := by linarith
  have hrpow32 : (0 : ℝ) < ρ ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hρ0 _
  have hrpow12 : (0 : ℝ) < ρ ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hρ0 _
  -- the second summand is nonnegative
  have hsecond : (0 : ℝ) ≤ (m + 1/2) / ρ ^ ((1 : ℝ) / 2) :=
    div_nonneg hm0 hrpow12.le
  -- the leading coefficient is at least 1: `3·ρ^{3/2} ≤ 12 ≤ 2·(m+1/2)^5`
  have hρ32_le : ρ ^ ((3 : ℝ) / 2) ≤ 4 := by
    calc ρ ^ ((3 : ℝ) / 2) ≤ 2 ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow hρ0.le hρ2 (by norm_num)
      _ ≤ 2 ^ ((2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by
          rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hpow5 : (3.5 : ℝ) ^ 5 ≤ (m + 1/2) ^ 5 := by
    have h35 : (3.5 : ℝ) ≤ m + 1/2 := by linarith
    exact pow_le_pow_left₀ (by norm_num) h35 5
  have hcoeff : (1 : ℝ) ≤ (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * d * ρ)
      / (3 * ρ ^ ((3 : ℝ) / 2)) := by
    rw [le_div_iff₀ (by positivity)]
    have hcross : (0 : ℝ) ≤ 3 * (m + 1/2) * d * ρ := by positivity
    nlinarith [hpow5, hρ32_le]
  -- conclude: `n ≤ coeff·n + second`
  have hnum : n ≤ (2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * d * ρ)
      / (3 * ρ ^ ((3 : ℝ) / 2)) * n + (m + 1/2) / ρ ^ ((1 : ℝ) / 2) := by
    have h1 : n = 1 * n := (one_mul n).symm
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (by linarith : (0:ℝ) ≤ n)]
  gcongr

/-- **The Johnson budget dominates the unique-decoding error.**  `johnsonBoundReal` is at
least `|ι|/|F|`, the unconditional below-UD MCA error (`epsMCA_rs_udr_le_full`).  This is
the arithmetic half of the unconditional UD-window instance of `JohnsonNumericBound`. -/
theorem card_div_card_le_johnsonBoundReal
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) (hk : k ≤ Fintype.card ι) :
    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)
      ≤ CodingTheory.ProximityGap.Hab25Core.Hab25Johnson.johnsonBoundReal domain k η δ := by
  have hn : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hρ0 : (0 : ℝ) < (k : ℝ) / (Fintype.card ι : ℝ) + 1 / (Fintype.card ι : ℝ) := by
    have : (0 : ℝ) < 1 / (Fintype.card ι : ℝ) := by positivity
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / (Fintype.card ι : ℝ) := by positivity
    linarith
  have hρ2 : (k : ℝ) / (Fintype.card ι : ℝ) + 1 / (Fintype.card ι : ℝ) ≤ 2 := by
    have h1 : (k : ℝ) / (Fintype.card ι : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact_mod_cast hk
    have h2 : 1 / (Fintype.card ι : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hn
    linarith
  have hm : (3 : ℝ) ≤
      max (⌈(((k : ℝ) / (Fintype.card ι : ℝ) + 1 / (Fintype.card ι : ℝ))
        ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 := le_max_right _ _
  have hd : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  exact hab25_formula_ge_n_div_q hn hq hρ0 hρ2 hm hd

end CodingTheory

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open _root_.ProximityGap _root_.ProximityGap.UDRwire _root_.Code
open scoped NNReal ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The first unconditional instance of the numeric edge.**  Below the unique-decoding
radius (in the regime of `epsMCA_rs_udr_le_full`), `JohnsonNumericBound` holds outright:
the unconditional UD error `|ι|/|F|` never exceeds the Johnson budget
(`card_div_card_le_johnsonBoundReal`).  No production hypothesis. -/
theorem johnsonNumericBound_of_udr_window
    (domain : ι₀ ↪ F₀) (k : ℕ) [NeZero k] (η δ : ℝ≥0)
    (hk : k ≤ Fintype.card ι₀)
    (hδ : δ ≤ relativeUniqueDecodingRadius
      ((ReedSolomon.code domain k : Submodule F₀ (ι₀ → F₀)) : Set (ι₀ → F₀)))
    (hreg : 2 * (Fintype.card ι₀ - ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊)
      < Fintype.card ι₀ - k + 1) :
    JohnsonNumericBound domain k η δ := by
  unfold JohnsonNumericBound
  refine le_trans (epsMCA_rs_udr_le_full domain k hk δ hδ hreg) ?_
  have h1 : (Fintype.card ι₀ : ℝ≥0∞) / (Fintype.card F₀ : ℝ≥0∞)
      = ENNReal.ofReal ((Fintype.card ι₀ : ℝ) / (Fintype.card F₀ : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [h1]
  exact ENNReal.ofReal_le_ofReal
    (CodingTheory.card_div_card_le_johnsonBoundReal domain k η δ hk)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.hab25_formula_ge_n_div_q
#print axioms CodingTheory.card_div_card_le_johnsonBoundReal
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_udr_window

namespace CodingTheory

open scoped NNReal

/-- The pure-real core of the tight `harith` closure: with `y = x·s ≤ 3(M+1/2)`,
`s ≤ 1`, `12 ≤ M`, the canonical budget `(x+1)·(c·x+1)` fits inside
`(2/3)·(M+1/2)⁵/s³` (all per-`n`). -/
theorem harith_core_real {x s c M : ℝ}
    (hx0 : 0 ≤ x) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hM : 12 ≤ M) (hc : c ≤ M * (M + 1) / 2)
    (hc0 : 0 ≤ c) (hy : x * s ≤ 3 * (M + 1/2)) :
    (x + 1) * (c * x + 1) ≤ (2/3) * (M + 1/2) ^ 5 / s ^ 3 := by
  have hM0 : (0 : ℝ) < M + 1/2 := by linarith
  have hkey : ((x + 1) * (c * x + 1)) * s ^ 3 ≤ (2/3) * (M + 1/2) ^ 5 := by
    have h1 : (x + 1) * s ≤ 3 * (M + 1/2) + 1 := by nlinarith
    have h2 : (c * x + 1) * s ≤ (3/2) * (M + 1/2) ^ 3 + 1 := by nlinarith
    have hs3 : s ^ 3 ≤ s * s := by nlinarith
    have hxs : 0 ≤ (x + 1) * s := by positivity
    have hcs : 0 ≤ (c * x + 1) * s := by positivity
    calc ((x + 1) * (c * x + 1)) * s ^ 3
        ≤ ((x + 1) * s) * ((c * x + 1) * s) * s := by nlinarith [sq_nonneg s, mul_nonneg hx0 hc0]
      _ ≤ (3 * (M + 1/2) + 1) * ((3/2) * (M + 1/2) ^ 3 + 1) * 1 := by
          have hAB : ((x + 1) * s) * ((c * x + 1) * s)
              ≤ (3 * (M + 1/2) + 1) * ((3/2) * (M + 1/2) ^ 3 + 1) :=
            mul_le_mul h1 h2 hcs (by linarith)
          have hABnn : 0 ≤ ((x + 1) * s) * ((c * x + 1) * s) := mul_nonneg hxs hcs
          nlinarith [mul_le_mul_of_nonneg_left hs1 hABnn]
      _ ≤ (2/3) * (M + 1/2) ^ 5 := by nlinarith [pow_pos hM0 3, pow_pos hM0 5, sq_nonneg (M + 1/2)]
  have hs3p : (0 : ℝ) < s ^ 3 := by positivity
  rw [le_div_iff₀ hs3p]
  exact hkey

end CodingTheory
