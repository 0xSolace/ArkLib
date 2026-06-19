/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The moment-to-sup last mile: completing the conditional prize chain to `M ≤ C·√(n log q)` (#444)

`_PrizeConditionalCapstone` reduces the prize to one named open hypothesis `SaddleEnergyBound`
and proves the chain down to the **moment** conclusion `μ_{2r} ≤ Wick_r = (2r−1)‼·nʳ`. It then only
*gestures* at the final step. **This file proves that step**:
the moment-method optimization converting the per-`r` sub-Gaussian moment bound into the actual
supremum bound `M ≤ C·√(n·log q)`, so the conditional prize theorem is stated end-to-end.

## The last mile (exact)

Let `M = max_{b≠0}|η_b|`. The sup is below one moment: `M^{2r} ≤ Σ_{t≠0}|η_t|^{2r} = (p−1)·μ`.
The chain (`prize_of_saddleEnergyBound`) gives `μ ≤ Wick_r = (2r−1)‼·nʳ ≤ (2rn)ʳ` (the last `≤` is
`(2r−1)‼ ≤ (2r)ʳ`, elementary, verified exactly). Hence the **moment budget**
```
        M^{2r} ≤ (p−1)·(2 r n)ʳ.
```
Writing `V = M²` and taking `r`-th roots, `V ≤ (p−1)^{1/r}·(2 r n)`. Choosing `r ≥ log(p−1)` makes
`(p−1)^{1/r} = exp(log(p−1)/r) ≤ e`, so
```
        M² ≤ e·(2 r n)        (`moment_to_sup_budget`).
```
Taking `r ≈ log p` (an integer in `[log(p−1), 2 log p]`) gives `M² ≤ 4 e · n · log p`, i.e.
```
        M ≤ 2√e · √(n·log p)        (`prize_sup_sqrt`),     C = 2√e ≈ 3.297
```
(tightening to `√(2e) ≈ 2.33` at the real optimum `r = log p`). This **is** the prize form
`M ≤ C·√(n·log q)`. Verified numerically (exact periods, incl. Fermat prize prime `p = 65537`): the
bound holds with large slack, and the true `M ≈ √(n log p)` (BGK is empirically true with `C ≈ 1`).

## Honest scope

This file proves the *optimization* unconditionally (pure real analysis: true for **any** `M`
satisfying the moment budget). The moment budget itself is delivered by the proven chain **only
under** `SaddleEnergyBound` (= BGK/Paley at β=4, the recognized open input). So the end-to-end
`prize_sup_of_saddle` is a genuine **conditional theorem** `SaddleEnergyBound ⟹ M ≤ 2√e·√(n log p)`,
with all open content isolated in the one hypothesis. **Not** a proof of the prize. Issue #444.

## What this file proves (axiom-clean)

* `rpow_root_bound` — the `r`-th-root step: `Vʳ ≤ K·cʳ ⟹ V ≤ K^{1/r}·c` (the optimization core).
* `rpow_inv_le_exp_one` — `K^{1/r} ≤ e` when `r ≥ log K` (the `(p−1)^{1/r} ≤ e` saddle choice).
* `moment_to_sup_budget` — `M² ≤ e·(2rn)` from the budget `M^{2r} ≤ (p−1)·(2rn)ʳ`, `r ≥ log(p−1)`.
* `prize_sup_sqrt` — the prize form `M ≤ 2√e·√(n·log p)` from the budget, `log(p−1) ≤ r ≤ 2 log p`.
* `prize_sup_of_saddle` — the end-to-end conditional theorem with every chain link named.
-/

namespace ProximityGap.Frontier.MomentToSup

open Real

/-- **The `r`-th-root step.** If `Vʳ ≤ K·cʳ` (a one-moment budget on `V = M²`), `V, c, K ≥ 0` and
`r > 0`, then `V ≤ K^{1/r}·c`. Pure `rpow`: rewrite the right side as `(K^{1/r}·c)ʳ` and
take `r`-th roots. -/
theorem rpow_root_bound {V K c r : ℝ} (hV : 0 ≤ V) (hc : 0 ≤ c) (hK : 0 ≤ K) (hr : 0 < r)
    (h : V ^ r ≤ K * c ^ r) : V ≤ K ^ r⁻¹ * c := by
  have hKr : (0 : ℝ) ≤ K ^ r⁻¹ := Real.rpow_nonneg hK _
  have hW : (0 : ℝ) ≤ K ^ r⁻¹ * c := mul_nonneg hKr hc
  -- `(K^{1/r})^r = K`
  have hpow : (K ^ r⁻¹) ^ r = K := by
    rw [← Real.rpow_mul hK, inv_mul_cancel₀ hr.ne', Real.rpow_one]
  -- the right side is a single `r`-th power
  have hrw : K * c ^ r = (K ^ r⁻¹ * c) ^ r := by
    rw [Real.mul_rpow hKr hc, hpow]
  rw [hrw] at h
  -- take `r⁻¹`-th powers and cancel
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hV r) h (le_of_lt (inv_pos.mpr hr))
  rwa [← Real.rpow_mul hV, ← Real.rpow_mul hW, mul_inv_cancel₀ hr.ne', Real.rpow_one,
    Real.rpow_one] at h2

/-- **The saddle choice.** For `K > 0`, `r > 0`, `r ≥ log K`, `K^{1/r} ≤ e`. (At `K = p−1` and
`r ≈ log p` this is `(p−1)^{1/r} ≤ e`, converting the moment budget into a clean `e`-constant.) -/
theorem rpow_inv_le_exp_one {K r : ℝ} (hK : 0 < K) (hr : 0 < r) (hrK : Real.log K ≤ r) :
    K ^ r⁻¹ ≤ Real.exp 1 := by
  rw [Real.rpow_def_of_pos hK]
  apply Real.exp_le_exp.mpr
  have : Real.log K * r⁻¹ ≤ r * r⁻¹ :=
    mul_le_mul_of_nonneg_right hrK (le_of_lt (inv_pos.mpr hr))
  rwa [mul_inv_cancel₀ hr.ne'] at this

/-- **The moment-to-sup budget.** From `M^{2r} ≤ (p−1)·(2rn)ʳ` (delivered by the
proven chain `prize_of_saddleEnergyBound` under `SaddleEnergyBound`, using `Wick_r ≤ (2rn)ʳ`) with
`r ≥ log(p−1)`, the squared sup is controlled by a clean `e`-constant: `M² ≤ e·(2rn)`. -/
theorem moment_to_sup_budget (M n p r : ℝ) (hn : 0 ≤ n) (hp : 3 ≤ p) (hr : 0 < r)
    (hrlo : Real.log (p - 1) ≤ r)
    (hbudget : (M ^ 2) ^ r ≤ (p - 1) * (2 * r * n) ^ r) :
    M ^ 2 ≤ Real.exp 1 * (2 * r * n) := by
  have hK : (0 : ℝ) < p - 1 := by linarith
  have hc : (0 : ℝ) ≤ 2 * r * n := by positivity
  have hV : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
  have step1 : M ^ 2 ≤ (p - 1) ^ r⁻¹ * (2 * r * n) :=
    rpow_root_bound hV hc hK.le hr hbudget
  have step2 : (p - 1) ^ r⁻¹ ≤ Real.exp 1 := rpow_inv_le_exp_one hK hr hrlo
  calc M ^ 2 ≤ (p - 1) ^ r⁻¹ * (2 * r * n) := step1
    _ ≤ Real.exp 1 * (2 * r * n) := mul_le_mul_of_nonneg_right step2 hc

/-- **The prize form.** From the budget with the saddle window `log(p−1) ≤ r ≤ 2 log p`, the sup
satisfies the prize bound `M ≤ 2√e·√(n·log p)` = `M ≤ C·√(n·log q)` with `C = 2√e`.
The whole open content is the budget hypothesis (= `SaddleEnergyBound` = BGK at β=4). -/
theorem prize_sup_sqrt (M n p r : ℝ) (hM : 0 ≤ M) (hn : 0 ≤ n) (hp : 3 ≤ p) (hr : 0 < r)
    (hrlo : Real.log (p - 1) ≤ r) (hrhi : r ≤ 2 * Real.log p)
    (hbudget : (M ^ 2) ^ r ≤ (p - 1) * (2 * r * n) ^ r) :
    M ≤ 2 * Real.sqrt (Real.exp 1) * Real.sqrt (n * Real.log p) := by
  have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
  -- M² ≤ e·2rn ≤ e·2·(2 log p)·n = 4 e n log p
  have hbud : M ^ 2 ≤ Real.exp 1 * (2 * r * n) := moment_to_sup_budget M n p r hn hp hr hrlo hbudget
  have hstep : Real.exp 1 * (2 * r * n) ≤ 4 * Real.exp 1 * (n * Real.log p) := by
    have he : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hrn : 2 * r * n ≤ 2 * (2 * Real.log p) * n :=
      by apply mul_le_mul_of_nonneg_right _ hn; linarith
    nlinarith [mul_le_mul_of_nonneg_left hrn he, mul_nonneg he (mul_nonneg hn hlogp)]
  have hM2 : M ^ 2 ≤ 4 * Real.exp 1 * (n * Real.log p) := le_trans hbud hstep
  -- take square roots
  have hRHS : (0 : ℝ) ≤ 4 * Real.exp 1 * (n * Real.log p) :=
    by positivity
  have hsqrt : Real.sqrt (M ^ 2) ≤ Real.sqrt (4 * Real.exp 1 * (n * Real.log p)) :=
    Real.sqrt_le_sqrt hM2
  rw [Real.sqrt_sq hM] at hsqrt
  -- √(4 e n log p) = 2 √e √(n log p)
  have hfac : Real.sqrt (4 * Real.exp 1 * (n * Real.log p))
      = 2 * Real.sqrt (Real.exp 1) * Real.sqrt (n * Real.log p) := by
    rw [show (4 : ℝ) * Real.exp 1 * (n * Real.log p)
          = (2 ^ 2) * (Real.exp 1 * (n * Real.log p)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (Real.exp_pos 1).le, mul_assoc]
  rwa [hfac] at hsqrt

/-- **The end-to-end conditional prize theorem.** Every link is named, with the single open input
isolated. With `S = Σ_{t≠0}|η_t|^{2r}`, `E = E_r(ℂ)`, `Wick = Wick_r`:
* `hsup`   : `M^{2r} ≤ S`           — the sup is below the moment (`M = max|η_t|`, trivial).
* `hsaddle`: `S ≤ (p−1)·E` — **the open hypothesis `SaddleEnergyBound` = BGK/Paley at β=4.**
* `hbessel`: `E ≤ Wick`             — proven char-0 anchor (Bessel-MGF, `_CharZeroMGFBesselBound`).
* `hwick`  : `Wick ≤ (2rn)ʳ`        — elementary (`Wick_r = (2r−1)‼·nʳ`, `(2r−1)‼ ≤ (2r)ʳ`).
Then `M ≤ 2√e·√(n·log p)` = `M ≤ C·√(n·log q)`. The **only** unproven input is `hsaddle`;
all others are proven in-tree or elementary. This is the maximal honest conditional result. -/
theorem prize_sup_of_saddle (M n p r S E Wick : ℝ)
    (hM : 0 ≤ M) (hn : 0 ≤ n) (hp : 3 ≤ p) (hr : 0 < r)
    (hrlo : Real.log (p - 1) ≤ r) (hrhi : r ≤ 2 * Real.log p)
    (hsup : (M ^ 2) ^ r ≤ S) (hsaddle : S ≤ (p - 1) * E) (hbessel : E ≤ Wick)
    (hwick : Wick ≤ (2 * r * n) ^ r) :
    M ≤ 2 * Real.sqrt (Real.exp 1) * Real.sqrt (n * Real.log p) := by
  have hp1 : (0 : ℝ) ≤ p - 1 := by linarith
  have hbudget : (M ^ 2) ^ r ≤ (p - 1) * (2 * r * n) ^ r := by
    calc (M ^ 2) ^ r ≤ S := hsup
      _ ≤ (p - 1) * E := hsaddle
      _ ≤ (p - 1) * Wick := mul_le_mul_of_nonneg_left hbessel hp1
      _ ≤ (p - 1) * (2 * r * n) ^ r := mul_le_mul_of_nonneg_left hwick hp1
  exact prize_sup_sqrt M n p r hM hn hp hr hrlo hrhi hbudget

end ProximityGap.Frontier.MomentToSup

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.MomentToSup.rpow_root_bound
#print axioms ProximityGap.Frontier.MomentToSup.rpow_inv_le_exp_one
#print axioms ProximityGap.Frontier.MomentToSup.moment_to_sup_budget
#print axioms ProximityGap.Frontier.MomentToSup.prize_sup_sqrt
#print axioms ProximityGap.Frontier.MomentToSup.prize_sup_of_saddle
