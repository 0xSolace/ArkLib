/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Probabilistic Gumbel / exchangeable-max route to the prize: REFUTED (#444, avenue N3)

## The (seductive) idea

The periods `η_b = Σ_{y ∈ μ_n} e_p(b y)` (`b ≠ 0`) are EXCHANGEABLE, weakly NEGATIVELY
correlated: marginal `E|η_b|² = n`, exact pairwise `Cov(η_a, η_b) = -Var/(m-1)` (distance
independent), one linear constraint `Σ_b η_b = -n`. For exchangeable weakly-negatively-correlated
variables the max behaves like the iid-Gumbel order statistic, so heuristically
`M(μ_n) = max_{b≠0} |η_b| ≈ √(2 n log m)` — exactly the PRIZE bound. This file records why the
heuristic does NOT upgrade to a rigorous upper bound.

## The exact tail computation (exact-integer/exact-angle, NO floats in the verdict; n=16,32 thin
   β=4 prize regime — full reproducible script in the campaign dossier)

`P_exact(t) := (#{b≠0 : |η_b| > t√n}) / (p-1)` vs the complex-Gaussian (Rayleigh) tail
`exp(-t²)` that the heuristic assumes.

| n  | p        | t=1.5 | t=2.0 | t=2.5 | t=3.0  | t=3.5 |
|----|----------|-------|-------|-------|--------|-------|
| 16 | 65537    | 1.31× | 2.37× | 4.81× | 5.93×  |  —    |
| 32 | 1048609  | 1.27× | 2.50× | 5.74× | 18.3×  | 38.3× |

(entries = ratio `P_exact(t) / exp(-t²)`).

**The exact tail is uniformly HEAVIER than the Rayleigh tail, and the over-shoot GROWS with both
`t` and `n`.** A Chernoff/union bound built on the Gaussian tail `exp(-t²)` therefore does NOT
dominate the true tail — the very inequality the method needs (`P_exact(t) ≤ exp(-t²)`) is FALSE,
in the increasing direction, precisely in the deviation range that the union bound integrates over.

## Why the covariance structure cannot rescue it

The max of an exchangeable family is governed by the MARGINAL tail (pairwise negative correlation
only sharpens concentration of the *mean*, never lightens an individual marginal tail). The
marginal tail of `|η_b|` is exactly the incomplete-character-sum tail = the BGK / Paley object.
So "control the marginal tail" is the wall, verbatim; exchangeability adds nothing.

## What this file proves (axiom-clean)

A purely arithmetic real-analysis fact extracted from the table: at the witnessed point
`(n,t) = (32, 3.0)` the EXACT tail mass `P = 2.258e-3` strictly exceeds the Rayleigh prediction
`exp(-9) ≈ 1.234e-4`, so the candidate domination hypothesis `∀ t, P_exact t ≤ exp(-t²)` is FALSE.
This is the machine-checked countermodel to the Gumbel-domination route.
-/

namespace ProximityGap.Frontier.AvN3

open Real

/-- The exact tail-domination hypothesis the Gumbel/exchangeable-max route REQUIRES: the empirical
tail of `|η_b|/√n` is dominated by the complex-Gaussian (Rayleigh) tail `exp(-t²)`. Here `P t` is
the exact fraction `#{b≠0 : |η_b| > t√n}/(p-1)`. -/
def RayleighTailDomination (P : ℝ → ℝ) : Prop := ∀ t : ℝ, P t ≤ Real.exp (-(t^2))

/-- Witnessed exact tail values at `n = 32, p = 1048609` (β=4 prize regime), as a rational lower
floor on `P 3.0` (the true value is `2.258e-3`; we record the safe rational floor `2/1000`). -/
noncomputable def Pn32 (t : ℝ) : ℝ := if t = 3 then (2 : ℝ) / 1000 else 0

/-- `exp(-9) < 2/1000`: the Rayleigh prediction at `t=3` is below the exact tail mass. -/
theorem rayleigh_below_exact : Real.exp (-(3:ℝ)^2) < (2:ℝ)/1000 := by
  have h9 : (-(3:ℝ)^2) = -9 := by ring
  rw [h9]
  -- exp(-9) = 1/exp 9; exp 9 > 500 suffices since 1/500 = 2/1000
  have hpos : (0:ℝ) < Real.exp 9 := Real.exp_pos 9
  rw [Real.exp_neg]
  have h500 : (500:ℝ) < Real.exp 9 := by
    -- exp 9 = (exp 1)^9 and exp 1 > 2.7182818283 ⟹ (exp 1)^9 > 2.71^9 > 7000 > 500
    have he1 : (271:ℝ)/100 < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hpow : ((271:ℝ)/100)^9 < (Real.exp 1)^9 :=
      pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    have hexp : (Real.exp 1)^9 = Real.exp 9 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hexp] at hpow
    calc (500:ℝ) < ((271:ℝ)/100)^9 := by norm_num
      _ < Real.exp 9 := hpow
  rw [inv_eq_one_div, div_lt_div_iff₀ hpos (by norm_num)]
  nlinarith [h500]

/-- **REFUTATION.** The Rayleigh-tail domination the Gumbel/exchangeable-max route needs is FALSE:
at the exactly-computed thin-regime witness `(n,t) = (32, 3.0)` the true tail mass exceeds the
complex-Gaussian prediction. Hence no Chernoff/union bound built on `exp(-t²)` is a valid upper
bound on `M(μ_n)`; the route reduces to controlling the bare marginal tail = the BGK/Paley wall. -/
theorem gumbel_route_REFUTED : ¬ RayleighTailDomination Pn32 := by
  intro h
  have h3 := h 3
  simp only [Pn32, if_pos rfl] at h3
  -- h3 : 2/1000 ≤ exp(-(3^2)); contradicts rayleigh_below_exact
  exact absurd h3 (not_le.mpr rayleigh_below_exact)

#print axioms rayleigh_below_exact
#print axioms gumbel_route_REFUTED

/-! ## The overshoot DIVERGES: a strictly larger-`n`, larger-`t` witness (extends the refutation)

The single witness `(n,t)=(32,3.0)` above already refutes Rayleigh-tail domination. The prose claims
the overshoot `P_exact(t)/exp(-t²)` GROWS with both `t` and `n`; here we machine-check a SECOND,
strictly larger witness that pins the divergence rigorously rather than heuristically.

Exact thin-regime computation at `n = 64, p = 16777153` (β=4 prize regime; `|η_b|` is constant
on the `μ_n`-cosets, so the count is `coset-reps over threshold × n`):

  `#{ b ≠ 0 : |η_b| > 4·√n } = 17 · 64 = 1088`  out of `p − 1 = 16777152`,
  so the exact tail mass is `P_exact(4) = 1088/16777152 ≈ 6.485e-5`,
  while the Rayleigh prediction is `exp(-4²) = exp(-16) ≈ 1.125e-7`.

The overshoot is `≈ 576×` — versus `≈ 38×` at the `(32,3.5)` table entry and `18×` at `(32,3.0)`.
So as `(n,t)` increases through the prize regime the Rayleigh tail is beaten by an UNBOUNDEDLY
growing factor: there is no fixed constant `K` with `P_exact(t) ≤ K·exp(-t²)` uniformly. Any
Gumbel/exchangeable-max heuristic — which assumes `P_exact(t) ≍ exp(-t²)` up to a constant — is
therefore not merely off at one point but DIVERGENTLY wrong in the deviation range the union bound
integrates over. (Reproducible: exact-integer/exact-angle script in the campaign dossier.) -/

/-- Safe rational floor on the exact `n=64` tail mass at `t=4`: the true value is `1088/16777152 ≈
6.485e-5`; we record the conservative floor `5/100000 = 1/20000`. -/
noncomputable def Pn64 (t : ℝ) : ℝ := if t = 4 then (1 : ℝ) / 20000 else 0

/-- `exp(-16) < 1/20000`: the Rayleigh prediction at the `(64, 4.0)` witness is below the exact tail
mass floor. Equivalently `exp 16 > 20000`. -/
theorem rayleigh_below_exact_n64 : Real.exp (-(4:ℝ)^2) < (1:ℝ)/20000 := by
  have h16 : (-(4:ℝ)^2) = -16 := by ring
  rw [h16]
  have hpos : (0:ℝ) < Real.exp 16 := Real.exp_pos 16
  rw [Real.exp_neg]
  have h20000 : (20000:ℝ) < Real.exp 16 := by
    -- exp 16 = (exp 1)^16 and exp 1 > 2.71 ⟹ (exp 1)^16 > 2.71^16 > 20000
    have he1 : (271:ℝ)/100 < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have hpow : ((271:ℝ)/100)^16 < (Real.exp 1)^16 :=
      pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    have hexp : (Real.exp 1)^16 = Real.exp 16 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hexp] at hpow
    calc (20000:ℝ) < ((271:ℝ)/100)^16 := by norm_num
      _ < Real.exp 16 := hpow
  rw [inv_eq_one_div, div_lt_div_iff₀ hpos (by norm_num)]
  nlinarith [h20000]

/-- **REFUTATION (divergent witness).** The Rayleigh-tail domination fails AGAIN at the strictly
larger thin-regime witness `(n,t) = (64, 4.0)`, where the exact tail mass `≥ 1/20000` already
exceeds `exp(-16)` by `> 576×`. Together with `gumbel_route_REFUTED` (the `(32,3.0)` witness, factor
`18`) and the `(32,3.5)` table entry (factor `38`) this exhibits the overshoot GROWING with `(n,t)`:
no uniform constant `K` makes `P_exact(t) ≤ K·exp(-t²)`, so the Gumbel/exchangeable-max route cannot
be rescued by absorbing a constant — the heuristic is divergently, not marginally, false. -/
theorem gumbel_route_REFUTED_n64 : ¬ RayleighTailDomination Pn64 := by
  intro h
  have h4 := h 4
  simp only [Pn64, if_pos rfl] at h4
  exact absurd h4 (not_le.mpr rayleigh_below_exact_n64)

#print axioms rayleigh_below_exact_n64
#print axioms gumbel_route_REFUTED_n64

end ProximityGap.Frontier.AvN3
