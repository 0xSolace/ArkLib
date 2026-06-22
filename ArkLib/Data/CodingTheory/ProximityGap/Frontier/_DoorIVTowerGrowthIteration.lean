/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv): the per-level wall-growth floor ITERATES to a super-`√n` tower lower bound — IF SUSTAINED (#444)

A pure-induction companion to `_DoorIVWorstBPerLevelGrowthFloor`.  That file proved a CONDITIONAL
per-level floor: at the coherent worst frequency, under the measured imbalance band (`r_lo`) and
near-worst sub-transfer (`ε`), `M(μ_n) ≥ c · M(μ_{n/2})` with `c = (1+r_lo)(1−ε)`, and the probe
measured `c ≈ 1.46–1.74 > √2` at `n = 16/32/64`.

This file records the **honest iteration**: a chain bound `M_{k+1} ≥ c · M_k` (the per-level floor at
every level `k = 0..a−1` of the dyadic tower `μ_1 ⊂ μ_2 ⊂ … ⊂ μ_{2^a}`) **multiplies** to
`M_a ≥ c^a · M_0`.  Taking `c > √2` (so `log₂ c > 1/2`) and `M_0 = M(μ_1) = 1` this is `M(μ_{2^a}) ≥
c^a = (2^a)^{log₂ c} = n^{log₂ c}` with `log₂ c > 1/2` — a **super-`√n` lower bound**.

## HONESTY (this is a CONDITIONAL, NOT a CORE claim or an asymptotic over-claim)

The hypothesis is exactly "the per-level floor `c` holds at EVERY level down the tower".  This is
**measured** at the probed levels (`n=16/32/64`), **not proven** to persist as `n → ∞`.  Asserting the
super-`√n` conclusion unconditionally would be precisely the kind of "`δ* → capacity`" over-claim the
campaign has refused (and Shaw refuted once).  So this file formalizes ONLY the implication
"sustained per-level floor `⟹` tower lower bound", a pure-arithmetic certainty.  It does NOT bound
`M(n)` from above (not CORE) and makes NO claim that the floor `c > √2` persists asymptotically.  The
value is making explicit that **the prize is exactly the question of whether the per-level floor is
sustained**: a sustained `c < √2` would be needed for the prize `√n`, while the measured `c > √2` (if
sustained) overshoots it — the open object is the floor's asymptotic behaviour, nothing else.

No CORE, cancellation, completion, moment, anti-concentration, or capacity claim.  CORE remains OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVTowerGrowthIteration

/-- **Tower iteration (ℕ-indexed chain).**  If a nonneg chain `M : ℕ → ℝ` satisfies the per-level
floor `c · M k ≤ M (k+1)` for all `k < a` with `0 ≤ c`, then `c^a · M 0 ≤ M a`.  The per-level
multiplicative floor multiplies down the tower. -/
theorem tower_floor_iterate {M : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hM0 : 0 ≤ M 0)
    (a : ℕ) (hstep : ∀ k, k < a → c * M k ≤ M (k + 1)) :
    c ^ a * M 0 ≤ M a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hMa_nonneg : 0 ≤ M a := by
      -- M a ≥ c^a * M 0 ≥ 0
      have hih := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      have : 0 ≤ c ^ a * M 0 := mul_nonneg (pow_nonneg hc a) hM0
      linarith
    have hih := ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hstepa : c * M a ≤ M (a + 1) := hstep a (Nat.lt_succ_self a)
    calc c ^ (a + 1) * M 0 = c * (c ^ a * M 0) := by ring
      _ ≤ c * M a := by
            apply mul_le_mul_of_nonneg_left hih hc
      _ ≤ M (a + 1) := hstepa

/-- **Strict super-`√n` overshoot under a sustained `c > √2` floor.**  If the chain floor holds with a
constant `c` and `M 0 > 0`, then `M a ≥ c^a · M 0`.  Specialized: with `√2 < c` (the measured floor),
`c^a > (√2)^a = (2^a)^{1/2} = √(2^a)` — the tower value strictly exceeds the `√n` Plancherel scale at
every depth `a ≥ 1`. -/
theorem tower_value_gt_sqrt_scale {M : ℕ → ℝ} {c : ℝ}
    (hc2 : Real.sqrt 2 < c) (hM0 : 0 < M 0) (a : ℕ) (ha : 1 ≤ a)
    (hstep : ∀ k, k < a → c * M k ≤ M (k + 1)) :
    (Real.sqrt 2) ^ a * M 0 < M a := by
  have hcpos : (0:ℝ) ≤ c := le_of_lt (lt_of_le_of_lt (Real.sqrt_nonneg 2) hc2)
  have hfloor : c ^ a * M 0 ≤ M a := tower_floor_iterate hcpos (le_of_lt hM0) a hstep
  have hsqrt2_nonneg : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpow_lt : (Real.sqrt 2) ^ a < c ^ a :=
    pow_lt_pow_left₀ hc2 hsqrt2_nonneg (Nat.one_le_iff_ne_zero.mp ha)
  have hstrict : (Real.sqrt 2) ^ a * M 0 < c ^ a * M 0 :=
    mul_lt_mul_of_pos_right hpow_lt hM0
  linarith

end ArkLib.ProximityGap.Frontier.DoorIVTowerGrowthIteration

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerGrowthIteration.tower_floor_iterate
#print axioms ArkLib.ProximityGap.Frontier.DoorIVTowerGrowthIteration.tower_value_gt_sqrt_scale
