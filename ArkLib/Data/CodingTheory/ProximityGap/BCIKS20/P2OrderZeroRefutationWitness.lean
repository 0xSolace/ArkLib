/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2OrderZeroRefutation
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.WPowerInjective

/-!
# BCIKS20 Appendix A.4 — a concrete witness refuting the order-zero P2 carved core

`P2OrderZeroRefutation` proves the *conditional* refutation
`restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one`: the carved P2 core
`RestrictedFaaDiBrunoMatchAt … 0` is false whenever the order-1 `X`-Taylor coefficient
`evalX (C x₀) (Δ_X¹ R)` is a nonzero `Y`-constant `C c` and `W ^ R.natDegree ≠ 1`.

This file discharges that hypothesis set with a **fully concrete witness over `ℚ`**, making the
refutation **unconditional**: there genuinely exists `(H, x₀, R)` satisfying `ClaimA2.Hypotheses`
on which the carved core fails.

* `H = 2·Y` over `ℚ[X]` — non-monic (leading coeff `2`), irreducible (a unit-associate of the prime
  `Y`), separable.
* `R = X_mid²·Y² + 2·Y + X_mid` in `ℚ[X][X][Y]`.

Then `evalX (C 0) R = H` (so `ClaimA2.Hypotheses 0 R H` holds: `H ∣ H` and `H` separable),
`R.natDegree = 2`, the order-1 coefficient `evalX (C 0) (Δ_X¹ R) = C 1` (a nonzero `Y`-constant),
and `W ^ 2 = (lift 2) ^ 2 = lift 4 ≠ 1` (by injectivity of `liftToFunctionField`, char zero).

The capstone `orderZero_match_false : ¬ RestrictedFaaDiBrunoMatchAt myH 0 myR myHyp 0` is
axiom-clean (`[propext, Classical.choice, Quot.sound]`).  Together with `P2OrderZeroRefutation` and
the unsoundness escalation on issue #169, this establishes that the allowlisted axiom
`restrictedFaaDiBrunoMatch_residual` asserts a proposition that is *false* for non-monic `H`.
-/

noncomputable section

open scoped Polynomial.Bivariate
open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.Witness

/-- Non-monic irreducible `H = 2·Y` over `ℚ[X]` (leading coeff `2`, a unit ⟹ associate of `Y`). -/
abbrev myH : ℚ[X][Y] := Polynomial.monomial 1 (2 : ℚ[X])

/-- Witness `R = X_mid²·Y² + 2·Y + X_mid` in `ℚ[X][X][Y]`. -/
abbrev myR : ℚ[X][X][Y] :=
  Polynomial.monomial 2 ((Polynomial.X : ℚ[X][X]) ^ 2)
    + Polynomial.monomial 1 (2 : ℚ[X][X])
    + Polynomial.monomial 0 (Polynomial.X : ℚ[X][X])

/-- `Δ_X` on a single `Y`-monomial. -/
lemma hasseDerivX_monomial (i1 k : ℕ) (a : ℚ[X][X]) :
    hasseDerivX i1 (Polynomial.monomial k a)
      = Polynomial.monomial k (Polynomial.hasseDeriv i1 a) := by
  unfold hasseDerivX
  exact Polynomial.sum_monomial_index a _ (by simp)

lemma myH_natDegree : myH.natDegree = 1 := by
  rw [myH, Polynomial.natDegree_monomial]
  norm_num

lemma myH_leadingCoeff : myH.leadingCoeff = 2 := by
  rw [Polynomial.leadingCoeff, myH_natDegree, myH, Polynomial.coeff_monomial]
  norm_num

lemma two_isUnit_QX : IsUnit (2 : ℚ[X]) := by
  rw [show (2 : ℚ[X]) = Polynomial.C (2 : ℚ) by rw [map_ofNat]]
  exact Polynomial.isUnit_C.mpr (by norm_num)

lemma myH_irreducible : Irreducible myH := by
  have hCunit : IsUnit (Polynomial.C (2 : ℚ[X]) : ℚ[X][Y]) :=
    Polynomial.isUnit_C.mpr two_isUnit_QX
  have hHeq : myH = Polynomial.C (2 : ℚ[X]) * (Polynomial.X : ℚ[X][Y]) := by
    rw [myH, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]
  obtain ⟨u, hu⟩ := hCunit
  have hassoc : Associated (Polynomial.X : ℚ[X][Y]) myH := by
    refine ⟨u, ?_⟩
    rw [hHeq, hu, mul_comm]
  exact hassoc.irreducible_iff.mp Polynomial.irreducible_X

instance instFactIrr : Fact (Irreducible myH) := ⟨myH_irreducible⟩
instance instFactDeg : Fact (0 < myH.natDegree) := ⟨by rw [myH_natDegree]; norm_num⟩

/-- `evalX (C 0) R = H = 2·Y`. -/
lemma evalX_myR : Bivariate.evalX (Polynomial.C (0 : ℚ)) myR = myH := by
  rw [myR, Bivariate.evalX_eq_map, Polynomial.map_add, Polynomial.map_add,
    Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.map_monomial]
  simp [Polynomial.coe_evalRingHom, myH]

lemma myR_natDegree : myR.natDegree = 2 := by
  rw [myR]
  compute_degree!

lemma myH_separable : myH.Separable := by
  have hHeq : myH = Polynomial.C (2 : ℚ[X]) * (Polynomial.X : ℚ[X][Y]) := by
    rw [myH, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]
  rw [hHeq]
  exact (Polynomial.separable_X).unit_mul (Polynomial.isUnit_C.mpr two_isUnit_QX)

lemma myHyp : ClaimA2.Hypotheses (0 : ℚ) myR myH where
  dvd_evalX := by rw [evalX_myR]
  separable_evalX := by rw [evalX_myR]; exact myH_separable

/-- `p = evalX (C 0) (Δ_X¹ R) = C 1` (a nonzero `Y`-constant). -/
lemma p_eq :
    Bivariate.evalX (Polynomial.C (0 : ℚ)) (hasseDerivX 1 (hasseDerivY 0 myR))
      = Polynomial.C (1 : ℚ[X]) := by
  rw [hasseDerivY_zero, myR, hasseDerivX_add, hasseDerivX_add,
    hasseDerivX_monomial, hasseDerivX_monomial, hasseDerivX_monomial]
  simp only [Polynomial.hasseDeriv_one', Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_ofNat]
  rw [Bivariate.evalX_eq_map, Polynomial.map_add, Polynomial.map_add,
    Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.map_monomial]
  simp [Polynomial.coe_evalRingHom]

/-- `W ^ R.natDegree = (lift 2) ^ 2 = lift 4 ≠ 1` by injectivity of `liftToFunctionField`
(`4 ≠ 1` in `ℚ[X]`). -/
lemma myW :
    (liftToFunctionField (H := myH) myH.leadingCoeff) ^ myR.natDegree ≠ 1 := by
  rw [myH_leadingCoeff, myR_natDegree, ← map_pow]
  intro h
  rw [show (1 : 𝕃 myH) = liftToFunctionField (H := myH) 1 by rw [map_one]] at h
  have := BCIKS20.WPow.liftToFunctionField_injective myH h
  norm_num at this

/-- **The carved order-zero P2 core is FALSE on a concrete `ClaimA2.Hypotheses` witness over `ℚ`.**
Fully unconditional refutation: `H = 2·Y`, `R = X²·Y² + 2·Y + X` satisfy `ClaimA2.Hypotheses 0 R H`
yet `RestrictedFaaDiBrunoMatchAt H 0 R … 0` is false.  Hence the carved P2 core
`RestrictedFaaDiBrunoMatch` (and the `restrictedFaaDiBrunoMatch_residual` axiom asserting it) is
genuinely false, not merely open, for non-monic `H`. -/
theorem orderZero_match_false :
    ¬ RestrictedFaaDiBrunoMatchAt myH (0 : ℚ) myR myHyp 0 :=
  restrictedMatchAt_zero_false_of_constant_of_W_pow_ne_one myH 0 myR myHyp
    (le_of_eq myR_natDegree.symm) (1 : ℚ[X]) p_eq
    (by rw [map_one]; exact one_ne_zero) myW

end BCIKS20.HenselNumerator.Witness

#print axioms BCIKS20.HenselNumerator.Witness.orderZero_match_false
