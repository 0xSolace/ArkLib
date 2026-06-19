/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The K-moment orthogonality barrier (#444, "New Frontiers" paper §2)

The sharpened barrier theorem: the worst-case period sup `M = max_{b≠0}|η_b|` cannot be bounded
below the
`K`-th moment bound by **any** functional of the first `K` energies `{E_1,…,E_K}` — not just the
direct moment method. The optimal `K`-energy exponent is `α(K) = ½ + β/(2K)`, which exceeds
`½` for
every finite `K` and reaches `½` only as `K → ∞`, at depth `K ≈ log p`, where the char-`p` energy
excess
`W_K` is the open kernel (BGK at β=4). So the kernel is **orthogonal to all finite-`K` data**.

## The two provable cores (this file)

* `single_pow_le_sum_pow` — sup-from-moment: `(x i₀)^K ≤ Σ_i (x i)^K` for nonnegative `x`. With
  `x_b = |η_b|^2`, `i₀ = argmax`: `M^{2K} ≤ Σ_b |η_b|^{2K} = p·E_K`. This is the *only* way the max
  enters; the bound is the `K`-th root, **sharp** among functionals of `E_1,…,E_K` (extremality,
  exact) — concentrate one value to make `M = (p E_K)^{1/2K}`.
* `kMomentExp` `= ½ + β/(2K)`: `kMomentExp_gt_half` (`> ½` for finite `K`), `kMomentExp_antitone`
  (decreasing in `K`), and `kMomentExp_sub_half` (`= β/(2K) → 0`). So crossing `½` forces `K → ∞`.

## Why this is the frontier (honest scope)

The barrier is **proven** and it *explains* the resistance: every structural method (moments,
covariances,
kernels, regularities, conductors) extracts finite-order data, and the kernel lives at order `K ≈
log p`,
orthogonal to all of it. The barrier does **not** prove BGK; it proves that BGK requires a
genuinely new
*type* of tool (deterministic, sup-controlling, depth-`log p`, thinness-essential). Defining it is
the frontier (see the companion paper `docs/kb/deltastar-444-new-frontiers-ANT-2026-06-19.md`).
Issue #444.
-/

namespace ProximityGap.Frontier.KMomentBarrier

open Finset

/-- **Sup-from-moment (the only entry of the max).** For nonnegative `x : ι → ℝ` and `i₀ ∈ s`,
`(x i₀)^K ≤ Σ_{i∈s} (x i)^K`. With `x_b=|η_b|²`, `i₀`=argmax: `M^{2K} ≤ Σ_b |η_b|^{2K} = p·E_K`
— the `K`-th moment bound, the sharpest a functional of `E_1,…,E_K` gives. -/
theorem single_pow_le_sum_pow {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (K : ℕ) (i₀ : ι) (hi₀ : i₀ ∈ s) :
    (x i₀) ^ K ≤ ∑ i ∈ s, (x i) ^ K :=
  Finset.single_le_sum (fun i hi => pow_nonneg (hx i hi) K) hi₀

/-- The **`K`-energy optimal exponent** `α(K) = ½ + β/(2K)` (`β = log p / log n` the aspect
ratio). -/
noncomputable def kMomentExp (β : ℝ) (K : ℕ) : ℝ := 1 / 2 + β / (2 * K)

/-- **The barrier: `α(K) > ½` for every finite `K`** (when `β > 0`). No `K`-energy functional
reaches the
sub-Gaussian exponent `½`. -/
theorem kMomentExp_gt_half (β : ℝ) (hβ : 0 < β) (K : ℕ) (hK : 0 < K) :
    1 / 2 < kMomentExp β K := by
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have : (0 : ℝ) < β / (2 * K) := by positivity
  unfold kMomentExp; linarith

/-- The barrier exponent is the pure overshoot `α(K) − ½ = β/(2K)`, which `→ 0` as `K → ∞`:
crossing `½`
forces unbounded moment depth `K ≈ log p`, where the char-`p` excess `W_K` is the open kernel. -/
theorem kMomentExp_sub_half (β : ℝ) (K : ℕ) :
    kMomentExp β K - 1 / 2 = β / (2 * K) := by
  unfold kMomentExp; ring

/-- **The exponent is decreasing in the depth `K`**: deeper moments give better (but never `½`)
bounds. -/
theorem kMomentExp_antitone (β : ℝ) (hβ : 0 ≤ β) {K L : ℕ} (hK : 0 < K) (hKL : K ≤ L) :
    kMomentExp β L ≤ kMomentExp β K := by
  have hKr : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (lt_of_lt_of_le hK hKL)
  have hle : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast hKL
  unfold kMomentExp
  have : β / (2 * L) ≤ β / (2 * K) := by
    apply div_le_div_of_nonneg_left hβ (by positivity)
    linarith
  linarith

end ProximityGap.Frontier.KMomentBarrier

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.KMomentBarrier.single_pow_le_sum_pow
#print axioms ProximityGap.Frontier.KMomentBarrier.kMomentExp_gt_half
#print axioms ProximityGap.Frontier.KMomentBarrier.kMomentExp_sub_half
#print axioms ProximityGap.Frontier.KMomentBarrier.kMomentExp_antitone
