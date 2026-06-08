/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 12 — the Diamond–Gruen super-poly disproof needs vanishing rate (it cannot hit the prize)

The strongest 2025 disproof of the RS proximity-gap *capacity* conjecture is Diamond–Gruen
(eprint 2025/2010): for each `c* ∈ ℕ` they build an infinite RS family with field size
`q = n^{c*+1}`, dimension `k(n) = ⌊e·n^{1/3}⌋·(1 − …)`, and proximity error `err > n^{c*}/q`,
refuting every polynomial bound. The construction's defining feature is the **cube-root degree
budget** `k ≈ e·n^{1/3}`, i.e. a degree budget obeying `k³ ≲ (const)·n`.

The ABF26 prize, however, fixes the rate `ρ = k/n` at one of `{1/2, 1/4, 1/8, 1/16}`. This file
proves the elementary but decisive obstruction: **a cube-root degree budget `k³ ≤ C·n` is
incompatible with any fixed positive rate `ρ₀` except for boundedly many block lengths** — the
Diamond–Gruen rate must *vanish* (`ρ → 0`), so their family is never an infinite fixed-prize-rate
family. This is exactly why the prize's `ρ^{−c₂}` factor (generous as `ρ → 0`) absorbs the
Diamond–Gruen blow-up and the disproof does not transfer to the prize. (Companion to the
`η^{−c₃}` near-capacity absorption of Loop 7.)

Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (literature frontier, Diamond–Gruen row).
-/

namespace ArkLib.ProximityGap.DisproofLoop12

/-- **Cube-root degree budget forces a vanishing rate.** If a degree budget satisfies `k³ ≤ C·n`
(the Diamond–Gruen `k ≈ e·n^{1/3}` regime) at a *fixed* positive rate `k = ρ₀·n`, then the block
length is bounded: `n² ≤ C / ρ₀³`. So only finitely many block lengths are possible — there is no
infinite fixed-rate family with a cube-root degree budget. -/
theorem cubeRoot_budget_forces_bounded_n
    {C ρ₀ n k : ℝ} (hρ₀ : 0 < ρ₀) (hn : 0 < n)
    (hbudget : k ^ 3 ≤ C * n) (hrate : k = ρ₀ * n) :
    n ^ 2 ≤ C / ρ₀ ^ 3 := by
  -- substitute `k = ρ₀·n`: `ρ₀³ n³ ≤ C n`, cancel one `n > 0` to get `ρ₀³ n² ≤ C`.
  have hsub : ρ₀ ^ 3 * n ^ 3 ≤ C * n := by
    have : (ρ₀ * n) ^ 3 = ρ₀ ^ 3 * n ^ 3 := by ring
    rw [hrate] at hbudget; rwa [this] at hbudget
  -- `ρ₀³ n² ≤ C`
  have hcancel : ρ₀ ^ 3 * n ^ 2 ≤ C := by
    have hn3 : ρ₀ ^ 3 * n ^ 3 = (ρ₀ ^ 3 * n ^ 2) * n := by ring
    rw [hn3] at hsub
    exact le_of_mul_le_mul_right (by linarith [hsub]) hn
  -- divide by `ρ₀³ > 0`
  have hρ3 : 0 < ρ₀ ^ 3 := by positivity
  rw [le_div_iff₀ hρ3]
  linarith [hcancel]

/-- **The Diamond–Gruen rate vanishes (contrapositive form).** Under a cube-root degree budget
`k³ ≤ C·n` with `C > 0`, the rate `ρ = k/n` cannot stay at or above any fixed `ρ₀ > 0` once the
block length exceeds `√(C/ρ₀³)`: for `n² > C/ρ₀³` (and `n,k > 0`) we cannot have `k = ρ₀·n`. -/
theorem cubeRoot_budget_excludes_fixed_rate
    {C ρ₀ n k : ℝ} (hρ₀ : 0 < ρ₀) (hn : 0 < n)
    (hbudget : k ^ 3 ≤ C * n) (hbig : C / ρ₀ ^ 3 < n ^ 2) :
    k ≠ ρ₀ * n := by
  intro hrate
  exact absurd (cubeRoot_budget_forces_bounded_n hρ₀ hn hbudget hrate) (not_le_of_gt hbig)

end ArkLib.ProximityGap.DisproofLoop12
