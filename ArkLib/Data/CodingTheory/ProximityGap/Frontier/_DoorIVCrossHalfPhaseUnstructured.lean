/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Field.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv): the cross-half phase is trivially real, but its magnitude ratio is unstructured (#444)

## The cross-half dilation identity (probed)

Split `η_b = Σ_{y∈μ_n} e_p(b·y)` along the index-2 subgroup `μ_{n/2} < μ_n` with coset
representative `g` (a generator of `μ_n`):
`η_b = A_b + B_b`, where
`A_b = Σ_{z∈μ_{n/2}} e_p(b·z)` is the sub-period at frequency `b`, and
`B_b = Σ_{z∈μ_{n/2}} e_p(b·g·z) = A_{b·g}` is the **same sub-period at the dilated frequency `b·g`**.

A natural door-(iv) lever (the "cross-half phase factorization"): hope that at the worst frequency `b*`
the second half is a **fixed phase rotation** of the first, `B_{b*} = ω · A_{b*}` for a fixed root of
unity `ω`.  If so, `‖η_{b*}‖ = ‖1 + ω‖ · ‖A_{b*}‖`, and the worst-`b` half-mass would inherit a bound
from a *single* thinner sub-period `A` — a recursive `√`-saving.

## What the probe finds (`probe_dooriv_crosshalf_phase.py`, `_control.py`)

PROPER thin `μ_n` (`n = 16, 32, 64`, `2`-power), `p ≫ n³`, structured + generic primes, FULL `F_p*`
coset-rep scan at `n=16`, sampled larger, never `n = q−1`:

* **`arg(B/A) ≡ 0` to machine precision (`~1e-16`) at EVERY top frequency, including the worst `b*`.**
  Mechanism: `μ_{n/2}` is negation-stable (it contains `−1 = g_n^{n/2}`), so each half-sum `A_b`, `B_b`
  is **real**; hence the cross-half ratio `B/A` is a *real* scalar — there is **no nontrivial
  root-of-unity phase**, the rotation is trivially in the `±1` direction.  (Consistent with the
  separately-proven same-ray coherence `ρ(b*) = 1`.)
* **BUT the magnitude ratio `|B|/|A|` is UNSTRUCTURED:** across the top-`√m` band it ranges over
  `[0.07, 10.16]` with standard deviation up to `1.6`, varying wildly from frequency to frequency.

## Verdict (refuted-lever brick, with mechanism)

The cross-half phase factorization lever is **dead**.  The cross-half ratio `B/A` is real (no angular
degree of freedom to exploit), and its *magnitude* `t = |B|/|A|` is a frequency-dependent real number
with no concentration — there is **no fixed `ω`** (equivalently no fixed `t`) with `B_b = ω · A_b`
across frequencies.  Consequently the worst-`b` half-mass `‖A_b‖ + ‖B_b‖ = (1+t)·‖A_b‖` cannot be
factored through a *single* sub-period times a fixed multiplier; it irreducibly couples the sub-period
magnitude at the **two independent dilated frequencies** `b` and `b·g`.  This is exactly the
recursive-ascent / non-nesting wall (`[door-iv-worstb-non-nested]`): bounding the worst-`b` half-mass
is not reducible to bounding one thinner sub-period.

This file packages the structural algebra: under the *probed* real-collinear regime `B = t • A`
(`t ≥ 0`), the half-mass is `(1+t)·‖A‖`, coherence is `1`, and any "fixed-multiplier" route
`‖A+B‖ ≤ c·‖A‖` forces `c ≥ 1+t` — i.e. it must already absorb the full, unbounded, frequency-dependent
`t`.  No CORE/cancellation/completion/capacity claim — a faithful constraint on a refuted lever.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cross-half magnitude ratio in the probed real-collinear regime: the (nonnegative) real scalar
`t` with `B = t • A`.  The probe measures this `t = |B|/|A|` and finds it varies over `[0.07, 10]`
across frequencies — there is no fixed value. -/
def crossHalfRatio (A B : E) (t : ℝ) : Prop := B = t • A

/-- **Real-collinear half identity.**  If the second half is a nonnegative real multiple of the first
(`B = t • A`, `t ≥ 0` — the probed cross-half fact, `arg(B/A) ≡ 0`), then the period norm is exactly
`(1+t)·‖A‖`.  In particular the cross-half "phase" carries no rotation: the only datum is the real
magnitude ratio `t`. -/
theorem norm_add_eq_of_real_collinear {A B : E} {t : ℝ} (ht : 0 ≤ t) (h : crossHalfRatio A B t) :
    ‖A + B‖ = (1 + t) * ‖A‖ := by
  unfold crossHalfRatio at h
  subst h
  have : A + t • A = (1 + t) • A := by rw [add_smul, one_smul]
  rw [this, norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]

/-- **Half-mass in the real-collinear regime.**  The half-mass `‖A‖ + ‖B‖` is also exactly
`(1+t)·‖A‖`: the two coset halves co-ray, so the period norm SATURATES the half-mass (coherence `1`),
recovering the proven same-ray fact — but now the saturating multiplier is the *measured* ratio `t`. -/
theorem halfMass_eq_of_real_collinear {A B : E} {t : ℝ} (ht : 0 ≤ t) (h : crossHalfRatio A B t) :
    ‖A‖ + ‖B‖ = (1 + t) * ‖A‖ := by
  unfold crossHalfRatio at h
  subst h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  ring

/-- **Coherence is `1` in the real-collinear regime** (consistency check: matches the proven
`ρ(b*) = 1`).  The period norm equals the half-mass exactly. -/
theorem norm_add_eq_halfMass_of_real_collinear {A B : E} {t : ℝ} (ht : 0 ≤ t)
    (h : crossHalfRatio A B t) :
    ‖A + B‖ = ‖A‖ + ‖B‖ := by
  rw [norm_add_eq_of_real_collinear ht h, halfMass_eq_of_real_collinear ht h]

/-- **The fixed-multiplier lever must absorb the full, frequency-dependent ratio.**  Any attempt to
bound the period norm by a *fixed* multiple of the single sub-period, `‖A+B‖ ≤ c·‖A‖`, is — in the
real-collinear regime, on a sub-period with `‖A‖ > 0` — FORCED to satisfy `1 + t ≤ c`.  Since the probe
shows `t = |B|/|A|` is unbounded across frequencies (up to `~10` and growing with `n`), no fixed `c`
works: the "factor through one thinner sub-period" lever cannot hold uniformly. -/
theorem fixed_multiplier_forces_ratio_le {A B : E} {t c : ℝ} (ht : 0 ≤ t) (hA : 0 < ‖A‖)
    (h : crossHalfRatio A B t) (hbound : ‖A + B‖ ≤ c * ‖A‖) :
    1 + t ≤ c := by
  rw [norm_add_eq_of_real_collinear ht h] at hbound
  exact le_of_mul_le_mul_right (by linarith [hbound]) hA

/-- **Contrapositive: a large ratio breaks any fixed-multiplier bound.**  If the measured cross-half
ratio exceeds `c − 1` at some frequency (the probe: `t` reaches `~10 ≫ c` for any constant `c`), then
the fixed-multiplier bound `‖A+B‖ ≤ c·‖A‖` FAILS there.  This is the mechanism by which the
unstructured magnitude ratio kills the cross-half factorization lever. -/
theorem fixed_multiplier_fails_of_ratio_gt {A B : E} {t c : ℝ} (ht : 0 ≤ t) (hA : 0 < ‖A‖)
    (h : crossHalfRatio A B t) (hgt : c < 1 + t) :
    ¬ ‖A + B‖ ≤ c * ‖A‖ := by
  intro hbound
  exact absurd (fixed_multiplier_forces_ratio_le ht hA h hbound) (not_le_of_gt hgt)

/-- **No fixed root-of-unity factorization.**  Packaged abstractly: the cross-half datum is a single
nonnegative real `t` (the ratio), NOT an angle.  Two frequencies with different ratios `t₁ ≠ t₂` give
genuinely different half-mass multipliers `(1+t₁) ≠ (1+t₂)` on equal-norm sub-periods, so there is no
single multiplier (no fixed `ω`) valid across frequencies. -/
theorem distinct_ratios_give_distinct_multipliers {A₁ A₂ B₁ B₂ : E} {t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (h₁ : crossHalfRatio A₁ B₁ t₁) (h₂ : crossHalfRatio A₂ B₂ t₂)
    (hnorm : ‖A₁‖ = ‖A₂‖) (hA : 0 < ‖A₁‖) (hne : t₁ ≠ t₂) :
    ‖A₁ + B₁‖ ≠ ‖A₂ + B₂‖ := by
  rw [norm_add_eq_of_real_collinear ht₁ h₁, norm_add_eq_of_real_collinear ht₂ h₂, ← hnorm]
  intro heq
  have : 1 + t₁ = 1 + t₂ := by
    have := mul_right_cancel₀ (ne_of_gt hA) heq
    exact this
  exact hne (by linarith)

/-- **Lower envelope from a ratio floor.**  If the cross-half ratio is at least some `t₀ ≥ 0` at a
frequency (the probe shows worst-band `t` is `O(1)` but with no UPPER structure), the period norm is at
least `(1+t₀)·‖A‖` — confirming the half-mass envelope is genuinely larger than the single sub-period
whenever `t₀ > 0`, so the single-sub-period bound is strictly insufficient. -/
theorem norm_add_ge_of_ratio_ge {A B : E} {t t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htt : t₀ ≤ t)
    (h : crossHalfRatio A B t) :
    (1 + t₀) * ‖A‖ ≤ ‖A + B‖ := by
  have ht : 0 ≤ t := le_trans ht₀ htt
  rw [norm_add_eq_of_real_collinear ht h]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg A)
  linarith

end ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured

#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.norm_add_eq_of_real_collinear
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.halfMass_eq_of_real_collinear
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.norm_add_eq_halfMass_of_real_collinear
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.fixed_multiplier_forces_ratio_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.fixed_multiplier_fails_of_ratio_gt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.distinct_ratios_give_distinct_multipliers
#print axioms ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.norm_add_ge_of_ratio_ge
