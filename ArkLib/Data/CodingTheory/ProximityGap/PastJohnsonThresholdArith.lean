/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# The past-Johnson threshold arithmetic for the `M → δ*` bridge (#444)

A clean, self-contained re-formalization of the threshold arithmetic that the (now-removed,
non-compiling) `_e04`/`_e09` Frontier scaffolds *claimed* but did not prove (`Real.logb` was
unimported there). This file proves only the real-analysis inequality; it has NO ProximityGap
dependency and reduces to nothing open.

The `M → δ*` bridge (governing law + the tracked primitive
`MCADeltaStarListReduction.mcaDeltaStar_ge_of_uniform_mcaBad`) converts a worst-case far-line
list budget `B` (with `B/q ≤ ε*`) into `δ* ≥ 1 − ρ − H(ρ)/log₂ B`. That lower bound is **past the
Johnson radius `1 − √ρ`** exactly when `H(ρ)/log₂ B < √ρ − ρ`, i.e. when
`log₂ B > H(ρ)/(√ρ − ρ)`. This file proves that equivalence's binding direction.

`pastJohnson_threshold_correct` : for `ρ ∈ (0,1)`, if `H(ρ)/(√ρ − ρ) < log₂ B`
(the past-Johnson budget threshold) then `H(ρ)/log₂ B < √ρ − ρ` (the floor gap is below the
Johnson margin), i.e. `δ* = 1 − ρ − H(ρ)/log₂ B > 1 − √ρ = Johnson`.

Honest scope: this is the *arithmetic* of the bridge only. The bridge's open input — that a
worst-case `M`-bound actually supplies such a budget `B` at the Ramanujan exponent — is the
recognized open core (BGK/BCHKS 1.12) and is NOT addressed here.
-/

namespace ArkLib.ProximityGap.PastJohnsonThreshold

open Real

/-- For `ρ ∈ (0,1)`, `ρ < √ρ`, hence the Johnson margin `√ρ − ρ > 0`. -/
theorem johnson_margin_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < Real.sqrt ρ - ρ := by
  have hpos : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
  have hlt1 : Real.sqrt ρ < 1 := by
    have := Real.sqrt_lt_sqrt hρ0.le hρ1
    rwa [Real.sqrt_one] at this
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
  nlinarith [hsq, hlt1, hpos]

/-- **Past-Johnson threshold (binding direction).** For `ρ ∈ (0,1)`, if the worst-case list-budget
exponent clears the threshold `log₂ B > H(ρ)/(√ρ − ρ)`, then the implied floor gap satisfies
`H(ρ)/log₂ B < √ρ − ρ`, i.e. `δ* = 1 − ρ − H(ρ)/log₂ B` is strictly **past Johnson** `1 − √ρ`. -/
theorem pastJohnson_threshold_correct {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B) :
    Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ := by
  have hc : 0 < Real.sqrt ρ - ρ := johnson_margin_pos hρ0 hρ1
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hfrac : 0 < Real.binEntropy ρ / (Real.sqrt ρ - ρ) := div_pos hH hc
  have hlb : 0 < Real.logb 2 B := lt_trans hfrac hbudget
  -- H/(√ρ−ρ) < L  ⟹  H < L·(√ρ−ρ)
  have h1 : Real.binEntropy ρ < Real.logb 2 B * (Real.sqrt ρ - ρ) :=
    (div_lt_iff₀ hc).mp hbudget
  -- conclude H/L < √ρ−ρ
  rw [div_lt_iff₀ hlb]
  nlinarith [h1]

end ArkLib.ProximityGap.PastJohnsonThreshold
