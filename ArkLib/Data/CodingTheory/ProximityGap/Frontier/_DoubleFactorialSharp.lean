/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# A sharp double-factorial bound `(2r−1)‼ ≤ r^r` (#407)

The moment-optimization (`GaussPeriodOptimizedBound.eta_le_optimized`) bounds the prize constant via
`((2r−1)‼)^{1/r}`. The crude `(2r−1)‼ ≤ (2r)^r` gives constant `√(2e) ≈ 2.33`. The AM–GM bound — the
geometric mean of the `r` odd numbers `{1,3,…,2r−1}` is at most their arithmetic mean `r²/r = r` —
is sharper:

> **`doubleFactorial_le_pow_self`** — `(2r−1)‼ ≤ r^r`.

This yields `((2r−1)‼)^{1/r} ≤ r`, hence the optimized constant improves to `√e ≈ 1.65` (vs the crude
`√(2e)`; the sharp `√2` needs the full Stirling `(2r−1)‼ ∼ √2(2r/e)^r`). Proof: induction, using the
Bernoulli step `2·r^r ≤ (r+1)^r` (from `(1+1/r)^r ≥ 2`).

Issue #407.
-/

namespace ProximityGap.Frontier.DoubleFactorialSharp

/-- **Bernoulli step.** `2·r^r ≤ (r+1)^r` for `r ≥ 1` (i.e. `(1+1/r)^r ≥ 2`). -/
theorem two_mul_pow_le_succ_pow (r : ℕ) (hr : 1 ≤ r) : 2 * r ^ r ≤ (r + 1) ^ r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
  have hb := one_add_mul_le_pow (a := (1 : ℝ) / r)
    (le_trans (by norm_num : (-2 : ℝ) ≤ 0) (by positivity)) r
  have heq : (1 : ℝ) + (r : ℝ) * (1 / r) = 2 := by field_simp
  rw [heq] at hb  -- hb : 2 ≤ (1 + 1/r)^r
  have h1 : ((1 : ℝ) + 1 / r) ^ r = ((r : ℝ) + 1) ^ r / (r : ℝ) ^ r := by
    rw [div_pow]; congr 1; field_simp
  rw [h1, le_div_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) ^ r)] at hb
  have hcast : (2 : ℝ) * (r : ℝ) ^ r ≤ ((r : ℝ) + 1) ^ r := by linarith [hb]
  exact_mod_cast hcast

/-- **AM–GM double-factorial bound.** `(2r−1)‼ ≤ r^r`: the product of the `r` odd numbers `1,3,…,2r−1`
is at most `(their mean = r)^r`. -/
theorem doubleFactorial_le_pow_self (r : ℕ) : Nat.doubleFactorial (2 * r - 1) ≤ r ^ r := by
  induction r with
  | zero => simp [Nat.doubleFactorial]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Nat.doubleFactorial]
    · have he : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
      rw [he, Nat.doubleFactorial_add_two]
      have hb := two_mul_pow_le_succ_pow k hk
      have h2k1 : (2 * k - 1) + 2 = 2 * k + 1 := by omega
      rw [h2k1]
      calc (2 * k + 1) * Nat.doubleFactorial (2 * k - 1)
          ≤ (2 * k + 1) * k ^ k := Nat.mul_le_mul_left _ ih
        _ ≤ (2 * k + 2) * k ^ k := by exact Nat.mul_le_mul_right _ (by omega)
        _ = (k + 1) * (2 * k ^ k) := by ring
        _ ≤ (k + 1) * (k + 1) ^ k := Nat.mul_le_mul_left _ hb
        _ = (k + 1) ^ (k + 1) := by rw [pow_succ]; ring

end ProximityGap.Frontier.DoubleFactorialSharp

#print axioms ProximityGap.Frontier.DoubleFactorialSharp.doubleFactorial_le_pow_self
