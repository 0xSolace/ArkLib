/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawDepletionTheorem

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# The cross-step rung SLACK is exactly the depletion-defect difference `δ̂_{r+1} − n·δ̂_r` (#444)

Two clusters of the energy-ladder face were built separately and never connected:

* the **cross-step rungs** (`CrossStepRungOne..Five`) discharge the open `Prop` `M3CrossStepBound`
  per `r`, where the rung is `crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}` and
  `crossMass G r = E_{r+1} − n·E_r` on the proven char-`p` recursion;
* the **Shaw depletion defects** (`_ShawDepletionTheorem`) carry, on the char-`0` ℤ-carrier, the exact
  defects `δ̂_r := wick r − E_r = (2r−1)‼·n^r − E_r` (`defect_two … defect_six`).

This file supplies the **exact algebraic bridge** between them, on the char-`0` ℤ-carrier:

> `rungSlack_eq_defect_diff` :  the rung slack `stepTarget r − crossMassZ r = δ̂_{r+1} − n·δ̂_r`.

**Mechanism (one line).** `stepTarget r = 2r·(2r−1)‼·n^{r+1} = ((2r+1)‼ − (2r−1)‼)·n^{r+1}
= wick (r+1) − n·wick r`. So
`stepTarget r − crossMassZ r = (wick(r+1) − n·wick r) − (E_{r+1} − n·E_r)
= (wick(r+1) − E_{r+1}) − n·(wick r − E_r) = δ̂_{r+1} − n·δ̂_r`. Pure ring identity.

**Consequence (the characterization).** The cross-step rung is *equivalent* to the depletion
defects growing at least linearly in `n`:

> `crossStepRung_iff_defect_superlinear` :  `crossMassZ r ≤ stepTarget r  ↔  n·δ̂_r ≤ δ̂_{r+1}`.

So "the rung holds" ⟺ "`δ̂_{r+1} ≥ n·δ̂_r`": each depletion defect dominates `n×` the previous one.
This re-reads the per-rung `crossStepBound_*` checks as a single monotone *defect-superlinearity*
condition, and it is why every proven rung holds — the defect `δ̂_r ~ C(r,2)·(2r−1)‼·n^{r−1}` carries a
leading factor that grows by `> n` from `r` to `r+1` (`δ̂_{r+1}/δ̂_r ~ (C(r+1,2)/C(r,2))·(2r+1)·n
≫ n`). We instantiate the bridge + characterization at the two top proven rungs `r = 4, 5` from the
in-tree `defect_four / defect_five / defect_six`.

## Results (axiom-clean, ℤ-arithmetic on the in-tree char-`0` carrier)

* `crossMassZ`, `stepTarget`            — the ℤ-carrier cross mass `E_{r+1} − n·E_r` and step target.
* `rungSlack_eq_defect_diff_four/five`  — `stepTarget r − crossMassZ r = δ̂_{r+1} − n·δ̂_r` at `r=4,5`.
* `crossStepRung_iff_defect_superlinear_four/five` — `crossMassZ r ≤ stepTarget r ↔ n·δ̂_r ≤ δ̂_{r+1}`.
* `defect_superlinear_four/five`        — `n·δ̂_r ≤ δ̂_{r+1}` for `n ≥ 2` (hence the rung), proven by
    the in-tree defect polynomials + a shifted-variable nonnegativity certificate.

## Honest scope (rules 1, 3, 4, 6)

This is a char-`0` ℤ-carrier *identity + reformulation* connecting two existing in-tree clusters; it
does NOT prove the `∀ r` form of `M3CrossStepBound`, and does NOT touch the char-`p` transfer at the
prize depth `r ≈ ln q` (the defects are char-`0`-faithful only above the root-norm threshold, false at
prize scale). CORE (`M(μ_n) ≤ C√(n·log(p/n))`) stays OPEN. No capacity / beyond-Johnson / growth-law
claim. Frontier-MOVEMENT (wires two clusters with an exact mechanism), not a point-confirmation.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

namespace ProximityGap.Frontier.ShawDepletion

open ProximityGap.Frontier.CharZeroEnergy

/-- The char-`0` ℤ-carrier cross mass at depth `r`: `crossMassZ E_r E_{r+1} n = E_{r+1} − n·E_r`,
mirroring `CrossStepCeiling.crossMass = E_{r+1} − n·E_r` of the proven char-`p` recursion. -/
def crossMassZ (Er Erp1 : ℤ → ℤ) (n : ℤ) : ℤ := Erp1 n - n * Er n

/-- The cross-step rung target `stepTarget r n = 2r·(2r−1)‼·n^{r+1}` on the ℤ-carrier. -/
def stepTarget (r : ℕ) (n : ℤ) : ℤ :=
  (2 * r : ℤ) * (Nat.doubleFactorial (2 * r - 1) : ℤ) * n ^ (r + 1)

/-- **The step target is the one-step Wick gap.** `stepTarget r = wick (r+1) − n·wick r`, since
`(2r+1)‼ − (2r−1)‼ = 2r·(2r−1)‼` (`doubleFactorial_add_two`). Proven at `r = 4, 5`. -/
theorem stepTarget_eq_wickGap_four (n : ℤ) :
    stepTarget 4 n = wick 5 n - n * wick 4 n := by
  simp only [stepTarget, wick, Nat.doubleFactorial]; ring

theorem stepTarget_eq_wickGap_five (n : ℤ) :
    stepTarget 5 n = wick 6 n - n * wick 5 n := by
  simp only [stepTarget, wick, Nat.doubleFactorial]; ring

/-- **THE BRIDGE at `r = 4`: the rung slack equals the depletion-defect difference.**
`stepTarget 4 − crossMassZ E4 E5 = δ̂_5 − n·δ̂_4`. Pure ℤ-ring identity:
`stepTarget = wick5 − n·wick4`, so `stepTarget − (E5 − n·E4) = (wick5 − E5) − n·(wick4 − E4)`. -/
theorem rungSlack_eq_defect_diff_four (n : ℤ) :
    stepTarget 4 n - crossMassZ E4 E5 n
      = depletionDefect E5 5 n - n * depletionDefect E4 4 n := by
  simp only [stepTarget, crossMassZ, depletionDefect, wick, E4, E5, Nat.doubleFactorial]; ring

/-- **THE BRIDGE at `r = 5`.** `stepTarget 5 − crossMassZ E5 E6 = δ̂_6 − n·δ̂_5`. -/
theorem rungSlack_eq_defect_diff_five (n : ℤ) :
    stepTarget 5 n - crossMassZ E5 E6 n
      = depletionDefect E6 6 n - n * depletionDefect E5 5 n := by
  simp only [stepTarget, crossMassZ, depletionDefect, wick, E5, E6, Nat.doubleFactorial]; ring

/-- **The characterization at `r = 4`: the rung is defect-superlinearity.**
`crossMassZ E4 E5 ≤ stepTarget 4  ↔  n·δ̂_4 ≤ δ̂_5`. Immediate from the bridge identity. -/
theorem crossStepRung_iff_defect_superlinear_four (n : ℤ) :
    crossMassZ E4 E5 n ≤ stepTarget 4 n
      ↔ n * depletionDefect E4 4 n ≤ depletionDefect E5 5 n := by
  have h := rungSlack_eq_defect_diff_four n
  constructor
  · intro hr; linarith
  · intro hd; linarith

/-- **The characterization at `r = 5`.** `crossMassZ E5 E6 ≤ stepTarget 5 ↔ n·δ̂_5 ≤ δ̂_6`. -/
theorem crossStepRung_iff_defect_superlinear_five (n : ℤ) :
    crossMassZ E5 E6 n ≤ stepTarget 5 n
      ↔ n * depletionDefect E5 5 n ≤ depletionDefect E6 6 n := by
  have h := rungSlack_eq_defect_diff_five n
  constructor
  · intro hr; linarith
  · intro hd; linarith

/-- **Defect superlinearity at `r = 4` (`n ≥ 2`).** `n·δ̂_4 ≤ δ̂_5`, i.e.
`n·(630n³−1435n²+1155n) ≤ 9450n⁴−39375n³+77175n²−57456n`. Shifted-variable nonnegativity:
the slack is `8820n⁴ − 37940n³ + 76020n² − 57456n ≥ 0` for `n ≥ 2`. Hence (by the characterization)
the `r = 4` cross-step rung holds on the ℤ-carrier. -/
theorem defect_superlinear_four (n : ℤ) (hn : 2 ≤ n) :
    n * depletionDefect E4 4 n ≤ depletionDefect E5 5 n := by
  rw [defect_four, defect_five]
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (sq_nonneg (n - 2)),
    mul_nonneg hn0 ht, sq_nonneg (n - 2), ht, mul_nonneg hn0 (mul_nonneg ht (sq_nonneg (n-2)))]

/-- **Defect superlinearity at `r = 5` (`n ≥ 2`).** `n·δ̂_5 ≤ δ̂_6`. The slack
`146475n⁵ − 982800n⁴ + 3457125n³ − 6189015n² + 4370520n ≥ 0` for `n ≥ 2`. Hence the `r = 5`
cross-step rung holds on the ℤ-carrier. -/
theorem defect_superlinear_five (n : ℤ) (hn : 2 ≤ n) :
    n * depletionDefect E5 5 n ≤ depletionDefect E6 6 n := by
  rw [defect_five, defect_six]
  have ht : (0 : ℤ) ≤ n - 2 := by linarith
  have hn0 : (0 : ℤ) ≤ n := by linarith
  nlinarith [mul_nonneg hn0 (pow_nonneg ht 4), mul_nonneg hn0 (pow_nonneg ht 3),
    mul_nonneg hn0 (sq_nonneg (n - 2)), mul_nonneg hn0 ht, sq_nonneg (n - 2), ht,
    mul_nonneg hn0 (mul_nonneg ht (pow_nonneg ht 3)),
    mul_nonneg hn0 (mul_nonneg ht (sq_nonneg (n - 2)))]

/-- **The `r = 4` rung on the ℤ-carrier, from defect superlinearity.** -/
theorem crossStepRungZ_four (n : ℤ) (hn : 2 ≤ n) :
    crossMassZ E4 E5 n ≤ stepTarget 4 n :=
  (crossStepRung_iff_defect_superlinear_four n).mpr (defect_superlinear_four n hn)

/-- **The `r = 5` rung on the ℤ-carrier, from defect superlinearity.** -/
theorem crossStepRungZ_five (n : ℤ) (hn : 2 ≤ n) :
    crossMassZ E5 E6 n ≤ stepTarget 5 n :=
  (crossStepRung_iff_defect_superlinear_five n).mpr (defect_superlinear_five n hn)

end ProximityGap.Frontier.ShawDepletion

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ShawDepletion.rungSlack_eq_defect_diff_four
#print axioms ProximityGap.Frontier.ShawDepletion.rungSlack_eq_defect_diff_five
#print axioms ProximityGap.Frontier.ShawDepletion.crossStepRung_iff_defect_superlinear_four
#print axioms ProximityGap.Frontier.ShawDepletion.crossStepRung_iff_defect_superlinear_five
#print axioms ProximityGap.Frontier.ShawDepletion.defect_superlinear_four
#print axioms ProximityGap.Frontier.ShawDepletion.defect_superlinear_five
#print axioms ProximityGap.Frontier.ShawDepletion.crossStepRungZ_four
#print axioms ProximityGap.Frontier.ShawDepletion.crossStepRungZ_five
