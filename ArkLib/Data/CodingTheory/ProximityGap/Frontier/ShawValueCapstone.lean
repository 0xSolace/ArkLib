/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Shaw-value capstone rungs for the proximity-prize normalization (#444)

Door (iv) has localized the remaining analytic object to the worst-frequency monomial-sum
coherence.  This file packages the harmless, citable normalization around that object:

* `prizeScale n L = sqrt (n * L)` is the native square-root target scale.
* `shawValue M n L = M / prizeScale n L` is the normalized Shaw value.
* `prizeBound_iff_shawValue_le` states the exact arithmetic equivalence, under a positive scale:
  bounding the raw worst-frequency value `M` by `C * sqrt(n L)` is the same as bounding the
  normalized Shaw value by `C`.
* `shawValue_floor_of_plancherel_floor` and `shawValue_le_of_trivial_ceiling` record the two easy
  ends of the chain: a Plancherel/RMS floor passes to the normalized value, and the trivial ceiling
  passes to the normalized value.

Scope: this is Lane-2 infrastructure only.  It does **not** prove the prize inequality or any new
anti-concentration for the monomial phase set; it makes the “prize ⇔ bounded Shaw value” arithmetic
rung explicit and axiom-clean so future door-(iv) work can cite the normalized target without
re-proving division-by-scale bookkeeping.
-/

namespace ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- The square-root target scale in the prize normalization.  In applications `n` is the subgroup
size and `L` is the logarithmic thinness parameter such as `log (p / n)`. -/
noncomputable def prizeScale (n L : ℝ) : ℝ :=
  Real.sqrt (n * L)

/-- The normalized Shaw value: raw worst-frequency size divided by the prize scale. -/
noncomputable def shawValue (M n L : ℝ) : ℝ :=
  M / prizeScale n L

/-- Positivity of the prize scale from positive subgroup size and positive logarithmic thinness. -/
theorem prizeScale_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    0 < prizeScale n L := by
  unfold prizeScale
  exact Real.sqrt_pos.2 (mul_pos hn hL)

/-- **Capstone normalization equivalence.**  Once the target scale is positive, the raw prize-shaped
bound `M ≤ C * sqrt(n L)` is exactly the statement that the Shaw value is at most `C`.

This is the formal Lane-2 rung behind the prose “prize ⇔ bounded Shaw value”: all hard content is in
proving a uniform bound for the normalized object; this theorem only removes the arithmetic wrapper. -/
theorem prizeBound_iff_shawValue_le {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C := by
  constructor
  · intro h
    unfold shawValue
    have hdiv : M / prizeScale n L ≤ (C * prizeScale n L) / prizeScale n L :=
      div_le_div_of_nonneg_right h (le_of_lt hs)
    simpa [mul_comm, mul_left_comm, mul_assoc, ne_of_gt hs] using hdiv
  · intro h
    unfold shawValue at h
    calc
      M = (M / prizeScale n L) * prizeScale n L := by
        field_simp [ne_of_gt hs]
      _ ≤ C * prizeScale n L := mul_le_mul_of_nonneg_right h (le_of_lt hs)

/-- The equivalence in expanded parameters: for `0 < n` and `0 < L`, raw prize boundedness by `C`
is exactly boundedness of the normalized Shaw value by `C`. -/
theorem prizeBound_iff_shawValue_le_of_pos {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C :=
  prizeBound_iff_shawValue_le (prizeScale_pos hn hL)

/-- A Plancherel/RMS floor `sqrt n ≤ M` becomes the corresponding normalized lower bound for the
Shaw value.  This records the easy Johnson-side floor in Shaw-value units. -/
theorem shawValue_floor_of_plancherel_floor {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hfloor : Real.sqrt n ≤ M) :
    Real.sqrt n / prizeScale n L ≤ shawValue M n L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hfloor (le_of_lt hs)

/-- The trivial ceiling `M ≤ n` becomes the corresponding normalized upper bound for the Shaw value.
This is the harmless top bracket `M ≤ n`, in Shaw-value units. -/
theorem shawValue_le_of_trivial_ceiling {M n L : ℝ} (hs : 0 < prizeScale n L) (hceil : M ≤ n) :
    shawValue M n L ≤ n / prizeScale n L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hceil (le_of_lt hs)

end ArkLib.ProximityGap.Frontier.ShawValueCapstone

#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeBound_iff_shawValue_le
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeBound_iff_shawValue_le_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_floor_of_plancherel_floor
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_le_of_trivial_ceiling
