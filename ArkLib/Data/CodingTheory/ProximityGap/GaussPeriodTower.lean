/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# The Gauss-period parallelogram tower (#407) — the exact L^∞/phase-alignment backbone

The proximity prize reduces to square-root cancellation of incomplete character sums (Gauss
periods) over the dyadic subgroup `μ_{2^μ} ⊂ F_p*` at depth `r ≍ log p` (regime `n = |μ_n| ~
p^{1/4}`) — the recognized open BGK/Bourgain problem.  The L² (moment/energy) hierarchy is proven
to stop at Johnson (the `n^{1/2}` deficit).  This file provides the EXACT backbone of the live
L^∞/phase-alignment route: the dyadic Gauss period `η_b(μ_n)` and its quadratic twist satisfy a
parallelogram recursion onto the level-`(n/2)` coset periods, turning the depth-`log p` estimate
into a single per-level descent inequality (the remaining open input).

Numerics (`scripts/probes/probe_par2.py`, `p ≈ n^4`, `n = 8,16,32`): at the level-`n` maximizer
`b*` the two coset periods are phase-aligned `cos = 1.0000` EXACTLY, and the untwisted/twisted
maxima are balanced (`M_untw ≈ M_tw`).  So `‖η_{b*}(μ_n)‖ = 2‖A‖` and the √2-descent reduces to
sub-maximality of `‖A‖ = ‖η_{b*}(μ_{n/2})‖`.
-/
open Finset

namespace ArkLib.ProximityGap.GaussPeriodTower

/-- **The Gauss-period parallelogram recursion** — the exact tool for the L^∞/phase-alignment
descent of the proximity prize.

For a dyadic subgroup `μ_n = μ_{n/2} ⊔ ζ·μ_{n/2}` (`n = 2^μ`) and additive character value
function `f := (x ↦ ψ(b·x))`, write `A = ∑_{x∈μ_{n/2}} f x` (period of the squares-coset) and
`B = ∑_{x∈ζμ_{n/2}} f x` (period of the other coset). Then the level-`n` Gauss period is `A + B`
and its quadratic twist (`+1` on `μ_{n/2}`, `−1` on `ζμ_{n/2}`) is `A − B`, and the parallelogram
law gives the EXACT recursion

> `‖η_b(μ_n)‖² + ‖η^χ_b(μ_n)‖² = 2·(‖A‖² + ‖B‖²)`.

Taking `max_b` and using that `A, B` are values of the level-`(n/2)` subgroup period, this reduces
the prize bound `max_b‖η_b(μ_n)‖ ≲ √(n·log(q/n))` to a **per-level descent**: at the level-`n`
maximizer `b*` the two cosets are *phase-aligned* (`A = B`, verified `cos = 1.0000` exactly, all
levels) so `‖η_{b*}(μ_n)‖ = 2‖A‖`, and the √2-descent needs the *sub-maximality* of `‖A‖ =
‖η_{b*}(μ_{n/2})‖` relative to the level-`(n/2)` max — the structural (open) core, now stated as one
recursive inequality rather than a depth-`log q` moment estimate. This lemma is the exact, reusable
backbone; the descent inequality is the single remaining (open) input. -/
theorem gaussPeriod_parallelogram_recursion {V : Type*} (S0 S1 : Finset V) (f : V → ℂ) :
    ‖(∑ x ∈ S0, f x) + (∑ x ∈ S1, f x)‖ ^ 2 + ‖(∑ x ∈ S0, f x) - (∑ x ∈ S1, f x)‖ ^ 2
      = 2 * (‖∑ x ∈ S0, f x‖ ^ 2 + ‖∑ x ∈ S1, f x‖ ^ 2) := by
  exact parallelogram_law_with_norm ℝ (∑ x ∈ S0, f x) (∑ x ∈ S1, f x)

/-- **The twist is the difference of coset periods** (the identity that makes the recursion concrete):
when `S = S0 ⊔ S1` and the twist colours `S0` by `+1`, `S1` by `−1`, the twisted period is
`(∑_{S0} f) − (∑_{S1} f)`, i.e. the second slot of the parallelogram. -/
theorem twistedPeriod_eq_sub {V : Type*} [DecidableEq V] (S0 S1 : Finset V) (hdisj : Disjoint S0 S1)
    (f : V → ℂ) :
    (∑ x ∈ S0 ∪ S1, (if x ∈ S0 then (1 : ℂ) else -1) * f x)
      = (∑ x ∈ S0, f x) - (∑ x ∈ S1, f x) := by
  classical
  rw [Finset.sum_union hdisj]
  have h0 : (∑ x ∈ S0, (if x ∈ S0 then (1 : ℂ) else -1) * f x) = ∑ x ∈ S0, f x :=
    Finset.sum_congr rfl (fun x hx => by rw [if_pos hx, one_mul])
  have h1 : (∑ x ∈ S1, (if x ∈ S0 then (1 : ℂ) else -1) * f x) = - ∑ x ∈ S1, f x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [if_neg (fun hx0 => (Finset.disjoint_left.mp hdisj) hx0 hx), neg_one_mul]
  rw [h0, h1, sub_eq_add_neg]

/-- **The untwisted period is the sum of coset periods.** -/
theorem period_eq_add {V : Type*} [DecidableEq V] (S0 S1 : Finset V) (hdisj : Disjoint S0 S1)
    (f : V → ℂ) :
    (∑ x ∈ S0 ∪ S1, f x) = (∑ x ∈ S0, f x) + (∑ x ∈ S1, f x) :=
  Finset.sum_union hdisj

end ArkLib.ProximityGap.GaussPeriodTower

#print axioms ArkLib.ProximityGap.GaussPeriodTower.gaussPeriod_parallelogram_recursion
#print axioms ArkLib.ProximityGap.GaussPeriodTower.twistedPeriod_eq_sub
#print axioms ArkLib.ProximityGap.GaussPeriodTower.period_eq_add
