/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

open scoped BigOperators
open Finset Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem hasseDerivY_eq_zero_of_lt (R : F[X][X][Y]) {s : ℕ} (h : R.natDegree < s) :
    hasseDerivY s R = 0 :=
  Polynomial.hasseDeriv_eq_zero_of_lt_natDegree R s h

theorem B_coeff_eq_zero_of_natDegree_lt (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (h : R.natDegree < sigmaLambda lam) :
    B_coeff H x₀ R i1 lam = 0 := by
  have hX0 : hasseDerivX i1 (0 : F[X][X][Y]) = 0 := by
    simp [hasseDerivX]
  unfold B_coeff hasseCoeffRepr𝒪
  have hE0 : Polynomial.Bivariate.evalX (Polynomial.C x₀) (0 : F[X][X][Y]) = 0 := by
    ext n m
    show (Polynomial.eval (Polynomial.C x₀) ((0 : F[X][X][Y]).coeff n)).coeff _ = 0
    simp
  rw [hasseDerivY_eq_zero_of_lt R h, hX0, hE0]
  simp

end BCIKS20.HenselNumerator

#print axioms BCIKS20.HenselNumerator.B_coeff_eq_zero_of_natDegree_lt
