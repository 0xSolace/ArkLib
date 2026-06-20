/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The trivial-cocycle Fourier fiber is RIGID: full mass `n` forces the genuine-character ratio `r = 1`

**Door (iv), Lane 3 — frontier-movement, extends a proven anchor (`trivial_cocycle_delta_fiber`).**

`_JacobiCocycleDispersion` proved the *forward* on/off-support delta pattern of the length-`n` geometric
Fourier fiber `∑_{g<n} r^g` for an `n`-th root of unity `r`:
* `trivial_cocycle_delta_fiber` — `∑_{g<n} r^g = if r = 1 then n else 0`, and
* `trivial_cocycle_full_concentration` / `trivial_cocycle_offSupport_zero` — the full-mass spike at `r = 1`
  and the exact cancellation off support.

What was MISSING is the *converse / rigidity direction*: that the value `n` is attained **only** at `r = 1`.
Equivalently, the geometric fiber is RIGID — its modulus reaches the triangle ceiling `n` exactly when the
ratio is trivial. This file locks that rigidity as kernel statements:

* `fiber_eq_card_iff_one` — `∑_{g<n} r^g = n ⟺ r = 1` (for `0 < n`, `r^n = 1`).
* `norm_fiber_eq_card_iff_one` — `‖∑_{g<n} r^g‖ = n ⟺ r = 1`.
* `norm_fiber_lt_card_of_ne_one` — a nontrivial ratio gives STRICTLY sub-ceiling modulus (`‖·‖ = 0 < n`).
* `fiber_full_mass_forces_trivial_cocycle` — the Door-IV reading: full Fourier concentration (fiber `= n`,
  the maximally-bad trivial bound) is attainable **only** by the genuine-character / trivial-cocycle ratio,
  so any genuine `r ≠ 1` (a nontrivial projective phase) is forced strictly below `n`.

This is the rigidity counterpart of the named open `JacobiCocycleDispersion`: it does NOT prove that the
Jacobi cocycle disperses (the prize); it proves that the *only* way to fail dispersion all the way up to the
ceiling `n` on a single fiber is the degenerate trivial-cocycle ratio. Probe-validated (510 roots of unity,
n = 2,4,…,256: fiber modulus equals `n` iff `r = 1`, zero otherwise). Axiom-clean. No CORE, cancellation,
completion, moment-saving, or capacity claim. Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity

open Finset

/-- **Rigidity of the trivial-cocycle Fourier fiber (exact value).** For `0 < n` and an `n`-th root of unity
`r`, the length-`n` geometric fiber `∑_{g<n} r^g` equals the full mass `n` **iff** `r = 1`. The reverse
direction is the geometric-sum spike (`r = 1`); the forward direction is the rigidity: if `r ≠ 1` the fiber is
`0` (orthogonality), so it cannot also be `n` (since `(n : ℂ) ≠ 0` for `0 < n`). -/
theorem fiber_eq_card_iff_one {n : ℕ} (hn : 0 < n) {r : ℂ} (hrpow : r ^ n = 1) :
    (∑ g ∈ range n, r ^ g) = (n : ℂ) ↔ r = 1 := by
  constructor
  · intro hsum
    by_contra hr
    -- off support: the fiber is zero, contradicting it being the nonzero `n`.
    have hzero : (∑ g ∈ range n, r ^ g) = 0 :=
      ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
        r hrpow hr
    rw [hzero] at hsum
    have hne0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn.ne'
    exact hne0 hsum.symm
  · intro hr
    subst hr
    simp

/-- **Rigidity in modulus.** For `0 < n` and an `n`-th root of unity `r`, the fiber modulus reaches the
triangle ceiling `n` **iff** `r = 1`. Off support the modulus is `0`. -/
theorem norm_fiber_eq_card_iff_one {n : ℕ} (hn : 0 < n) {r : ℂ} (hrpow : r ^ n = 1) :
    ‖∑ g ∈ range n, r ^ g‖ = (n : ℝ) ↔ r = 1 := by
  constructor
  · intro hnorm
    by_contra hr
    have hzero : (∑ g ∈ range n, r ^ g) = 0 :=
      ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
        r hrpow hr
    rw [hzero, norm_zero] at hnorm
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact this.ne hnorm
  · intro hr
    subst hr
    simp

/-- **A nontrivial ratio is strictly below the ceiling.** If `r ≠ 1` is an `n`-th root of unity (`0 < n`),
the fiber modulus is `0`, hence strictly less than the full mass `n`. This is the dispersion-toward-a-single-
fiber statement: the only fiber that saturates the triangle ceiling is the trivial one. -/
theorem norm_fiber_lt_card_of_ne_one {n : ℕ} (hn : 0 < n) {r : ℂ}
    (hrpow : r ^ n = 1) (hr : r ≠ 1) :
    ‖∑ g ∈ range n, r ^ g‖ < (n : ℝ) := by
  have hzero : (∑ g ∈ range n, r ^ g) = 0 :=
    ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
      r hrpow hr
  rw [hzero, norm_zero]
  exact_mod_cast hn

/-- **Door-IV reading: full single-fiber concentration forces the trivial cocycle.** The maximally-bad
(`= n`, zero-dispersion) value of the trivial-cocycle Fourier fiber is attainable on an `n`-th root of unity
`r` ONLY by the genuine-character / trivial-cocycle ratio `r = 1`. Contrapositive: any genuine nontrivial
projective phase `r ≠ 1` cannot saturate the ceiling, so failing to disperse all the way to `n` on a fiber is
EXACTLY the degenerate character case. This is the rigidity counterpart of the open `JacobiCocycleDispersion`;
it does not bound the cocycle dispersion (the prize), only certifies the unique full-mass attainer. -/
theorem fiber_full_mass_forces_trivial_cocycle {n : ℕ} (hn : 0 < n) {r : ℂ}
    (hrpow : r ^ n = 1) (hfull : ‖∑ g ∈ range n, r ^ g‖ = (n : ℝ)) :
    r = 1 :=
  (norm_fiber_eq_card_iff_one hn hrpow).mp hfull

end ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity
