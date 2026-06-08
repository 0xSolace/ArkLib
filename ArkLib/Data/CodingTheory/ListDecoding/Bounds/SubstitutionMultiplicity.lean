/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Team
-/
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div

/-!
# Substitution–multiplicity transfer (Guruswami–Sudan companion)

If a bivariate `Q(X,Y)` has Hasse-multiplicity `≥ m` at `(x, f x)`, then the univariate
substitution `P(T) = Q(T, f(T))` has a root of multiplicity `≥ m` at `x` — **provided `P ≠ 0`**.

The `P ≠ 0` hypothesis is essential: for `Q = X₀ − X₁`, `f = X` one has `P = T − T = 0`, and
`rootMultiplicity x 0 = 0`, so the statement without it (the older `rootMultiplicity_aeval_ge`)
is false. This is the companion to `gkl24_interpolation_existence`; together they are the two
halves of the Guruswami–Sudan list-decoding argument.

The proof: writing `R := Q(X + (x, f x))` (the bivariate Taylor shift), the Hasse-multiplicity
hypothesis says every monomial of `R` has total degree `≥ m` (Lemma
`coeff_shift_eq_eval_hasseDeriv`). The substitution factors as `taylor x P = Θ R` for a ring map
`Θ` sending `X₀ ↦ T` and `X₁ ↦ w` with `T ∣ w`; hence every monomial of `R` (degree `≥ m`) maps
to a multiple of `Tᵐ`, so `Tᵐ ∣ taylor x P`, i.e. `(T − x)ᵐ ∣ P`.
-/

open MvPolynomial Polynomial
open _root_.ArkLib.MvPolynomial
open scoped BigOperators

namespace CodingTheory.Bounds

variable {F : Type} [Field F]

/-- **Hasse–shift identity.** The `X^d`-coefficient of the bivariate Taylor shift
`Q(X + p)` equals the value at `p` of the `d`-th Hasse derivative of `Q`. -/
lemma coeff_shift_eq_eval_hasseDeriv (p : Fin 2 → F) (Q : MvPolynomial (Fin 2) F)
    (d : Fin 2 →₀ ℕ) :
    coeff d (aeval (fun i => X i + C (p i)) Q) = eval p (hasseDeriv d Q) := by
  have hmap : MvPolynomial.map (eval p) (taylor Q) = aeval (fun i => X i + C (p i)) Q := by
    have h : (MvPolynomial.map (eval p)).comp taylor
        = (aeval (fun i => X i + C (p i)) : MvPolynomial (Fin 2) F →ₐ[F] _).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [taylor, eval₂Hom_C, MvPolynomial.map_C, eval_C, RingHom.comp_apply]
      · intro i
        simp [taylor, eval₂Hom_X, map_add, MvPolynomial.map_C, MvPolynomial.map_X,
          eval_X, add_comm, RingHom.comp_apply]
    calc MvPolynomial.map (eval p) (taylor Q)
        = ((MvPolynomial.map (eval p)).comp taylor) Q := rfl
      _ = (aeval (fun i => X i + C (p i))).toRingHom Q := by rw [h]
      _ = aeval (fun i => X i + C (p i)) Q := rfl
  rw [← hmap, MvPolynomial.coeff_map]
  rfl

/-- **Substitution–multiplicity transfer** (the corrected `rootMultiplicity_aeval_ge`).
If `Q` has Hasse multiplicity `≥ m` at `(x, f x)` and the substitution `P = Q(T, f(T))` is
nonzero, then `x` is a root of `P` of multiplicity `≥ m`. -/
theorem rootMultiplicity_aeval_ge
    (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) (x : F) (m : ℕ)
    (hP : (aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q) ≠ 0)
    (h_mult : ArkLib.MvPolynomial.mult_ge ![x, f.eval x] m Q) :
    m ≤ rootMultiplicity x
      (aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q) := by
  classical
  set v : Fin 2 → Polynomial F := fun i => if i = 0 then Polynomial.X else f with hv
  set P : Polynomial F := aeval v Q with hPdef
  -- It suffices to show `(X - C x)^m ∣ P`.
  rw [Polynomial.le_rootMultiplicity_iff hP]
  -- `w := f(T + x) - C (f x)` is divisible by `T`.
  set w : Polynomial F := f.comp (Polynomial.X + C x) - C (f.eval x) with hw
  have hXw : (Polynomial.X : Polynomial F) ∣ w := by
    rw [Polynomial.X_dvd_iff]
    simp [hw, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  -- `Θ : MvPoly (Fin 2) F →ₐ Poly F`, `X₀ ↦ T`, `X₁ ↦ w`.
  set Θ : MvPolynomial (Fin 2) F →ₐ[F] Polynomial F :=
    aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else w) with hΘ
  set point : Fin 2 → F := ![x, f.eval x] with hpoint
  -- `R := Q(X + point)`, the bivariate Taylor shift.
  set R : MvPolynomial (Fin 2) F := aeval (fun i => X i + C (point i)) Q with hR
  -- Key factorisation: `taylor x P = Θ R`.
  have hfact : Polynomial.taylor x P = Θ R := by
    rw [hR, hPdef]
    -- both sides are `aeval`-composites of `Q`
    rw [Polynomial.taylor_apply]
    -- (aeval v Q).comp (X + C x) = aeval (fun i => (v i).comp (X + C x)) Q
    rw [← MvPolynomial.aeval_comp_aeval_eq_comp] at *
    sorry
  sorry

end CodingTheory.Bounds
