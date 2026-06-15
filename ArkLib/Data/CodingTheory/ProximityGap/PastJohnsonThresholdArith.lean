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

This file now closes the equivalence into a full **iff** and packages the actual conclusion:
* `threshold_of_floorGap_lt_margin` : the converse direction (floor gap below margin ⇒ budget
  exponent clears threshold), on the positive-exponent regime `0 < log₂ B`.
* `pastJohnson_threshold_iff` : the two combined — `H(ρ)/log₂ B < √ρ − ρ ↔ H(ρ)/(√ρ − ρ) < log₂ B`.
* `deltaStar_gt_johnson_of_budget` : the **named deliverable** — a checkable sufficient condition
  on the list-budget exponent (`log₂ B > H(ρ)/(√ρ − ρ)`) under which `1 − √ρ < δ*` (the recovered
  list-decoding radius is strictly past Johnson), with no `δ*`-side hypotheses.

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

/-- **Past-Johnson threshold (converse direction).** For `ρ ∈ (0,1)`, if the implied floor gap is
below the Johnson margin (`H(ρ)/log₂ B < √ρ − ρ`) *and* the budget exponent is positive
(`0 < log₂ B`, automatic once any list at all is past trivial), then the budget exponent clears the
threshold `log₂ B > H(ρ)/(√ρ − ρ)`. Together with `pastJohnson_threshold_correct` this makes the
threshold an **iff** on the positive-exponent regime. -/
theorem threshold_of_floorGap_lt_margin {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlb : 0 < Real.logb 2 B)
    (hgap : Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ) :
    Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B := by
  have hc : 0 < Real.sqrt ρ - ρ := johnson_margin_pos hρ0 hρ1
  -- H/L < √ρ−ρ  ⟹  H < (√ρ−ρ)·L
  have h1 : Real.binEntropy ρ < (Real.sqrt ρ - ρ) * Real.logb 2 B :=
    (div_lt_iff₀ hlb).mp hgap
  -- conclude H/(√ρ−ρ) < L
  rw [div_lt_iff₀ hc]
  nlinarith [h1]

/-- **The threshold equivalence (iff).** On the positive-budget-exponent regime `0 < log₂ B`, the
floor gap is below the Johnson margin **iff** the budget exponent clears the threshold. -/
theorem pastJohnson_threshold_iff {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlb : 0 < Real.logb 2 B) :
    Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ ↔
      Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B :=
  ⟨threshold_of_floorGap_lt_margin hρ0 hρ1 hlb,
   pastJohnson_threshold_correct hρ0 hρ1⟩

/-- **The actual past-Johnson conclusion, packaged.** For `ρ ∈ (0,1)`, if the budget exponent clears
the threshold `log₂ B > H(ρ)/(√ρ − ρ)`, then the floor `δ* = 1 − ρ − H(ρ)/log₂ B` strictly exceeds
the Johnson radius `1 − √ρ`. This is the named deliverable of the bridge arithmetic: a sufficient,
*checkable* condition on the list-budget exponent under which the recovered list-decoding radius is
provably **past Johnson**. (The open input remains supplying such a `B` at the Ramanujan exponent —
the BGK/BCHKS 1.12 core — and is NOT addressed here.) -/
theorem deltaStar_gt_johnson_of_budget {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B) :
    (1 : ℝ) - Real.sqrt ρ < 1 - ρ - Real.binEntropy ρ / Real.logb 2 B := by
  -- floor gap below margin
  have hgap : Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ :=
    pastJohnson_threshold_correct hρ0 hρ1 hbudget
  -- 1 − √ρ < 1 − ρ − (gap)  ⟺  gap < √ρ − ρ
  linarith [hgap]

end ArkLib.ProximityGap.PastJohnsonThreshold

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.johnson_margin_pos
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.pastJohnson_threshold_correct
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.threshold_of_floorGap_lt_margin
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.pastJohnson_threshold_iff
#print axioms ArkLib.ProximityGap.PastJohnsonThreshold.deltaStar_gt_johnson_of_budget
