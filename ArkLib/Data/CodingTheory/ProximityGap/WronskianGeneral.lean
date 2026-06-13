/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# The general (`l × l`) Wronskian of a family of polynomials (#389, Stepanov route)

Mathlib has only the two-element `Polynomial.wronskian` (for Mason–Stothers).  The Stepanov
method for bounding multiplicative-subgroup intersections (Garcia–Voloch / Heath-Brown–
Konyagin, the named `GVRepBound` input) requires the **general `l × l` Wronskian** and its
linear-independence criterion — the non-vanishing of the Stepanov auxiliary polynomial is
exactly an `l × l` Wronskian computation (Shkredov–Vyugin, *On additive shifts of
multiplicative subgroups*, Lemma 3.1 / Prop 3.2).

This file builds that foundation:

* `wronskianMatrix f` — the matrix `(i, j) ↦ derivative^[i] (f j)`.
* `wronskianDet f` — its determinant.
* `wronskianDet_eq_zero_of_dependent` — **the key criterion**: if a *constant-coefficient*
  linear combination `∑_j μ_j · f_j` vanishes with `μ ≠ 0`, the Wronskian is zero.  Equivalently
  (contrapositive `wronskianDet_ne_zero_imp_linearIndependent`) a nonzero Wronskian certifies
  linear independence of `f` — the engine for proving the Stepanov generators independent.
The degree bound `deg W ≤ ∑_j deg f_j − C(l,2)` (the SV degree contradiction) is the next brick.
-/

open Polynomial Matrix Finset

namespace ArkLib.ProximityGap.Wronskian

variable {R : Type*} [CommRing R] {l : ℕ}

/-- The `l × l` Wronskian matrix of a family `f : Fin l → R[X]`: entry `(i, j)` is the
`i`-th derivative of `f j`. -/
noncomputable def wronskianMatrix (f : Fin l → R[X]) : Matrix (Fin l) (Fin l) R[X] :=
  fun i j => (Polynomial.derivative^[(i : ℕ)]) (f j)

/-- The general Wronskian determinant of a family of polynomials. -/
noncomputable def wronskianDet (f : Fin l → R[X]) : R[X] :=
  (wronskianMatrix f).det

@[simp] theorem wronskianMatrix_apply (f : Fin l → R[X]) (i j : Fin l) :
    wronskianMatrix f i j = (Polynomial.derivative^[(i : ℕ)]) (f j) := rfl

/-- The mul-vec of the Wronskian matrix by a constant vector is the derivative-column of the
corresponding combination: `(W ⬝ᵥ (C ∘ μ)) i = derivative^[i] (∑_j μ_j · f_j)`. -/
theorem wronskianMatrix_mulVec_C (f : Fin l → R[X]) (μ : Fin l → R) (i : Fin l) :
    (wronskianMatrix f).mulVec (fun j => C (μ j)) i
      = (Polynomial.derivative^[(i : ℕ)]) (∑ j, C (μ j) * f j) := by
  rw [Matrix.mulVec, dotProduct]
  rw [iterate_derivative_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [wronskianMatrix_apply, iterate_derivative_C_mul, mul_comm]

/-- **The key criterion**: a vanishing constant-coefficient combination forces the Wronskian
to vanish.  (Over a domain; the contrapositive certifies linear independence.) -/
theorem wronskianDet_eq_zero_of_dependent [IsDomain R] {f : Fin l → R[X]} {μ : Fin l → R}
    (hμ : μ ≠ 0) (hdep : ∑ j, C (μ j) * f j = 0) :
    wronskianDet f = 0 := by
  classical
  rw [wronskianDet]
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => C (μ j), ?_, ?_⟩
  · intro h
    apply hμ
    funext j
    have := congrFun h j
    simpa using (Polynomial.C_eq_zero.mp this)
  · funext i
    rw [wronskianMatrix_mulVec_C, hdep, iterate_derivative_zero]
    rfl

/-- **Linear independence from a nonzero Wronskian**: if `wronskianDet f ≠ 0` then no nonzero
constant combination of the `f j` vanishes — the certificate the Stepanov construction needs. -/
theorem linearIndependent_of_wronskianDet_ne_zero [IsDomain R] {f : Fin l → R[X]}
    (hW : wronskianDet f ≠ 0) {μ : Fin l → R} (hdep : ∑ j, C (μ j) * f j = 0) :
    μ = 0 := by
  by_contra hμ
  exact hW (wronskianDet_eq_zero_of_dependent hμ hdep)

end ArkLib.ProximityGap.Wronskian
