/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Newton-step truncation propagation for power-series powers

This file keeps the proved, reusable part of the BCIKS20 Appendix A.4 Newton-linearization route:
if two power series agree below order `t`, then all of their powers agree below order `t`.

The next intended step is the order-`t` linearization
`coeff t (γ₁^(i+1)) - coeff t (γ₂^(i+1)) = (i+1) • (c^i * δ)`.
That requires a careful antidiagonal endpoint/interior split and is intentionally not stated here
until the proof is kernel-checked.
-/

namespace ProximityPrize.NewtonLinearization

open PowerSeries

variable {R : Type*} [CommRing R]

/-- **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient
`j < t`, then so do `γ₁^i` and `γ₂^i`, for every `i`.

Proof by induction on `i`. The `coeff_mul` antidiagonal sum for `coeff j (γ * γ^i)` only
references coefficient indices `a, b` with `a + b = j < t`, so both `a < t` and `b < t`,
where the hypothesis, respectively the inductive hypothesis, supplies agreement. -/
theorem coeff_pow_sub_below {γ₁ γ₂ : R⟦X⟧} {t : ℕ}
    (h : ∀ j < t, coeff j γ₁ = coeff j γ₂) :
    ∀ (i : ℕ), ∀ j < t, coeff j (γ₁ ^ i) = coeff j (γ₂ ^ i) := by
  intro i
  induction i with
  | zero =>
      intro j _
      simp
  | succ i ih =>
      intro j hj
      rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      have h1 : p.1 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_right _ _) hj
      have h2 : p.2 < t := lt_of_le_of_lt (by rw [← hp]; exact Nat.le_add_left _ _) hj
      rw [ih p.1 h1, h p.2 h2]

end ProximityPrize.NewtonLinearization
