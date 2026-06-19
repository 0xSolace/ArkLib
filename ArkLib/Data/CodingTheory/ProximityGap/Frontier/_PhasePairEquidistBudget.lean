/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PhaseLinearFormDecoupling

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# Door-IV pair-discrepancy budget for the phase-linear form (#444)

`_PhaseLinearFormDecoupling` names the honest open residual `PairEquidistributed φ δ` and proves the
variance proxy

`avg η² ≤ 2m + 2δ · m(2m-1)`.

This file repackages that inequality in the normalized prize-budget form.  Dividing by the prize proxy
`2m = n`, the entire remaining door-(iv) obligation is the dimensionless correction

`δ · (2m-1)`.

So the pair-discrepancy residual must be at the `O(1/m)` scale to keep the variance within a constant
multiple of the Plancherel/prize floor.  This is a reduction/constraint only: it proves no new
anti-concentration, no CORE cancellation, and no capacity claim.
-/

namespace ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget

open ArkLib.ProximityGap.Frontier.PhaseLinearFormDecoupling

variable {B : Type*} [Fintype B] [Nonempty B]

/-- The prize variance proxy attached to `m = n/2` antipodal phase pairs: `2m = n`. -/
def prizeVarianceProxy (m : ℕ) : ℝ := 2 * (m : ℝ)

/-- The pair-discrepancy correction in `_PhaseLinearFormDecoupling.variance_le_of_pairEquidist`. -/
def pairResidualCorrection (m : ℕ) (δ : ℝ) : ℝ := 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))

/-- **Pair-discrepancy budget, multiplicative form.**  If the dimensionless residual obeys
`δ(2m-1) ≤ ε`, then the variance is bounded by the prize proxy times `1+ε`.

This is the clean normalized statement of the open door-(iv) target: the named pair-equidistribution
residual must be `O(1/m)` to make the variance proxy stay at the prize scale. -/
theorem variance_le_prizeProxy_mul_one_add_of_pairResidual {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : δ * (2 * (m : ℝ) - 1) ≤ ε)
    (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
      ≤ prizeVarianceProxy m * (1 + ε) := by
  have hbase := variance_le_of_pairEquidist (B := B) φ δ hδ hpair
  have hmnonneg : (0 : ℝ) ≤ 2 * (m : ℝ) := by positivity
  have hcorr : 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1)) ≤ 2 * (m : ℝ) * ε := by
    calc
      2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1))
          = 2 * (m : ℝ) * (δ * (2 * (m : ℝ) - 1)) := by ring
      _ ≤ 2 * (m : ℝ) * ε := mul_le_mul_of_nonneg_left hε hmnonneg
  calc
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
        ≤ 2 * (m : ℝ) + 2 * δ * ((m : ℝ) * (2 * (m : ℝ) - 1)) := hbase
    _ ≤ 2 * (m : ℝ) + 2 * (m : ℝ) * ε := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hcorr (2 * (m : ℝ))
    _ = prizeVarianceProxy m * (1 + ε) := by unfold prizeVarianceProxy; ring

/-- **Pair-discrepancy budget, explicit `O(1/m)` form.**  If
`δ ≤ ε/(2m-1)`, then the variance is bounded by the prize proxy times `1+ε`.
The denominator is positive for every nonempty antipodal-pair list `m>0`. -/
theorem variance_le_prizeProxy_mul_one_add_of_delta_le_div {m : ℕ} (hm : 0 < m)
    (φ : Fin m → B → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hδle : δ ≤ ε / (2 * (m : ℝ) - 1))
    (hpair : PairEquidistributed φ δ) :
    avg (fun b => (∑ k : Fin m, 2 * Real.cos (φ k b)) ^ 2)
      ≤ prizeVarianceProxy m * (1 + ε) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hden_pos : 0 < 2 * (m : ℝ) - 1 := by
    nlinarith [hmR]
  apply variance_le_prizeProxy_mul_one_add_of_pairResidual (hm := hm) (φ := φ) (hδ := hδ) (hpair := hpair)
  calc
    δ * (2 * (m : ℝ) - 1) ≤ (ε / (2 * (m : ℝ) - 1)) * (2 * (m : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hδle (le_of_lt hden_pos)
    _ = ε := by
      exact div_mul_cancel₀ ε (ne_of_gt hden_pos)

/-- **The normalized correction is exactly `δ(2m-1)`.**  This pins the anti-concentration target with
no asymptotic handwaving: after division by the prize variance proxy `2m`, the pair-discrepancy
correction from `_PhaseLinearFormDecoupling` is precisely `δ(2m-1)`. -/
theorem correction_div_prizeProxy_eq_pairResidual {m : ℕ} (hm : 0 < m) (δ : ℝ) :
    pairResidualCorrection m δ / prizeVarianceProxy m = δ * (2 * (m : ℝ) - 1) := by
  have hm2 : (2 * (m : ℝ)) ≠ 0 := by positivity
  unfold pairResidualCorrection prizeVarianceProxy
  field_simp [hm2]

end ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound; no `sorryAx`). -/
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.variance_le_prizeProxy_mul_one_add_of_pairResidual
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.variance_le_prizeProxy_mul_one_add_of_delta_le_div
#print axioms ArkLib.ProximityGap.Frontier.PhasePairEquidistBudget.correction_div_prizeProxy_eq_pairResidual
