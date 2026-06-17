/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The moment/energy route is vacuous at scale: Cauchy–Schwarz forces the moment bound `≥ n` (#444)

**The result.** After mapping the wall from 14 analytic-NT directions, the only routes that could in principle reach
the prize `M = max_{b≠0}|η_b| ≤ C√(n log q)` are the **moment/energy** family: from the exact identity
`Σ_{b∈F_p} |η_b|^{2r} = p·E_r` (`E_r` = the `r`-fold additive energy of `μ_n`, `= Σ_s c_r(s)²` where
`c_r(s) = #{r-tuples from μ_n summing to s}`), one gets `M^{2r} ≤ p·E_r`, hence the moment bound
`M ≤ (p·E_r)^{1/2r}`. The char-0 ideal `E_r ≤ (2r−1)‼·n^r` at the optimal depth `r ≈ log p` would give exactly the
prize `√(2n log p)`.

**Why it is vacuous (this file).** The additive energy has an **unconditional Cauchy–Schwarz lower bound**: the
`n^r` `r`-tuples distribute over at most `p` sums, so
```
n^{2r} = (Σ_s c_r(s))²  ≤  (#support)·Σ_s c_r(s)²  ≤  p·E_r       (Chebyshev/Cauchy–Schwarz),
```
i.e. `p·E_r ≥ n^{2r}` for **every** depth `r` and **every** prime `p`. Therefore the moment bound
`(p·E_r)^{1/2r} ≥ n` always — the moment/energy method **cannot certify even `M < n`**, let alone the prize
`√(n log q) ≪ n`. Equivalently: for any prize-shaped target `T < n`, the moment certificate `M^{2r} ≤ p·E_r` is
consistent with `M` as large as `n > T` (since `T^{2r} < n^{2r} ≤ p·E_r`), so it cannot prove `M ≤ T`. This is the
exact mechanism behind the measured failure: the energy *saturates* (`E_r → n^{2r}/p` once the `r`-fold sumset fills
`F_p`, exact-verified `E_9(μ_32)=1.54e21 > Wick 1.21e21` at the β=4 prime `1048609`), and the saturated moment bound
is the trivial `n`. At the prize scale `n = 2^30` this overshoots the target `√(2n log q)` by `√(n/(2 log q)) ≈ 2540×`.

`T < n` (the prize is below `n`) holds exactly when `n > C²·log q`, true for all `n` past the small crossover
`n ≈ 2 log q` (the moment bound `≈ n` undercuts the prize only at tiny `n ≲ 16`, an artifact of `n ≈ √(n log q)`
there). So the moment/energy route provably **cannot reach the prize at scale**; the prize requires the direct
BGK/Paley sup-norm bound, not moments. This is the rigorous, unconditional core of trichotomy bucket **B1**
(second-moment-blind) and of the in-tree `moment_ladder_exceeds_prize`.

**What this file proves (axiom-clean).**
* `energy_cauchy_schwarz_lower` — the unconditional `N² ≤ p·E` from Chebyshev (`N = Σc`, support `≤ p`, `E = Σc²`).
* `moment_bound_ge_card` — specialized to `N = n^r`: `n^{2r} ≤ p·E_r` (the saturation floor).
* `moment_certificate_cannot_reach_prize` — if a target `T` has `T < n` then `T^{2r} < p·E_r`, so the moment
  inequality `M^{2r} ≤ p·E_r` cannot certify `M ≤ T` — the route is vacuous for any sub-`n` (hence prize) target.

Not a closure; the rigorous reason the energy ladder fails. Issue #444.
-/

namespace ProximityGap.Frontier.MomentSaturation

open Finset

/-- **Unconditional Cauchy–Schwarz (Chebyshev) energy floor.** For a nonnegative fiber-count function `c` supported
on a finset `s` of size `≤ p`, with total mass `Σ_{s} c = N`, the energy `E = Σ_{s} c²` satisfies `N² ≤ p·E`. (For
the additive energy, `c = c_r` the `r`-tuple fiber counts over `F_p`, `N = n^r`, `s` the `r`-fold sumset support
`≤ p`.) The `n^r` tuples cannot concentrate below the `n^{2r}/p` energy floor — the saturation lower bound. -/
theorem energy_cauchy_schwarz_lower {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (p : ℕ) (hcard : (s.card : ℝ) ≤ (p : ℝ)) (hcsq : 0 ≤ ∑ i ∈ s, c i ^ 2)
    (N : ℝ) (hN : ∑ i ∈ s, c i = N) :
    N ^ 2 ≤ (p : ℝ) * ∑ i ∈ s, c i ^ 2 := by
  have hcheb : (∑ i ∈ s, c i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, c i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc N ^ 2 = (∑ i ∈ s, c i) ^ 2 := by rw [hN]
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, c i ^ 2 := hcheb
    _ ≤ (p : ℝ) * ∑ i ∈ s, c i ^ 2 := by exact mul_le_mul_of_nonneg_right hcard hcsq

/-- **The saturation floor for the additive energy.** Specializing the Cauchy–Schwarz floor to the `r`-fold sumset
(`N = n^r` tuples over a support `≤ p`): `n^{2r} ≤ p·E_r`. So the moment quantity `p·E_r` — which upper-bounds
`M^{2r}` via `M^{2r} ≤ Σ_b|η_b|^{2r} = p·E_r` — is itself `≥ n^{2r}`, i.e. the moment bound `(p·E_r)^{1/2r} ≥ n`. -/
theorem moment_bound_ge_card {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (p n r : ℕ) (hcard : (s.card : ℝ) ≤ (p : ℝ)) (hcsq : 0 ≤ ∑ i ∈ s, c i ^ 2)
    (hN : ∑ i ∈ s, c i = (n : ℝ) ^ r) :
    ((n : ℝ) ^ r) ^ 2 ≤ (p : ℝ) * ∑ i ∈ s, c i ^ 2 :=
  energy_cauchy_schwarz_lower s c p hcard hcsq ((n : ℝ) ^ r) hN

/-- **The moment certificate cannot reach a sub-`n` target (vacuity at scale).** Given the saturation floor
`n^{2r} ≤ p·E` and any target `T` with `0 ≤ T < n` (the prize target `√(2n log q)` is `< n` for all `n > 2 log q`),
the certificate `M^{2r} ≤ p·E` cannot prove `M ≤ T`: indeed `T^{2r} < n^{2r} ≤ p·E`, so the upper bound `p·E` on
`M^{2r}` strictly exceeds `T^{2r}`, leaving `M > T` consistent. The moment/energy route is therefore vacuous for the
prize (which is far below `n`); only the direct sup-norm bound can reach it. -/
theorem moment_certificate_cannot_reach_prize
    (p n r : ℕ) (E T : ℝ) (hr : 1 ≤ r) (hT0 : 0 ≤ T) (hTn : T < (n : ℝ))
    (hfloor : ((n : ℝ) ^ r) ^ 2 ≤ (p : ℝ) * E) :
    T ^ (2 * r) < (p : ℝ) * E := by
  have h2r : 2 * r ≠ 0 := by omega
  have hTlt : T ^ (2 * r) < (n : ℝ) ^ (2 * r) :=
    pow_lt_pow_left₀ hTn hT0 h2r
  have hrw : ((n : ℝ) ^ r) ^ 2 = (n : ℝ) ^ (2 * r) := by
    rw [← pow_mul, mul_comm]
  rw [hrw] at hfloor
  linarith

end ProximityGap.Frontier.MomentSaturation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.MomentSaturation.energy_cauchy_schwarz_lower
#print axioms ProximityGap.Frontier.MomentSaturation.moment_bound_ge_card
#print axioms ProximityGap.Frontier.MomentSaturation.moment_certificate_cannot_reach_prize
