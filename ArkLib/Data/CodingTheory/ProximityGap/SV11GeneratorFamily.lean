/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WronskianNonVanishing

/-!
# The Garcia–Voloch / Shkredov–Vyugin Stepanov generator family has nonzero Wronskian (#389)

The Stepanov bound on `|R ∩ (R+c)|` (Garcia–Voloch / Heath-Brown–Konyagin, Shkredov–Vyugin
arXiv:1102.1172 Prop 3.2) is built from the generator family `g_{a,b}(X) = X^a · (X − c)^{t·b}`. To
run the method one must certify these generators are *linearly independent* — equivalently, that
their classical Wronskian is nonzero.

This file supplies that certificate by routing through the distinct-degree Wronskian non-vanishing
(`wronskianDet_ne_zero_of_distinctDeg`): `g_{a,b}` has `natDegree = a + t·b` (`sv11Gen_natDegree`),
and `(a,b) ↦ a + t·b` is **injective for `a < t`** (`add_mul_lt_injective`, a mod-`t` argument) — so
in the SV11 regime `D·B ≤ t` (where each `a < D ≤ t`) the family has distinct degrees, and the
Wronskian is nonzero (`sv11_wronskianDet_ne_zero`) in characteristic `0` or `> l−1`.

This is the connector between the non-vanishing certificate chain (`BinomialMatrixDet` →
`HasseWronskian{Monomial,Poly}` → `WronskianNonVanishing`) and the concrete Stepanov family. The one
remaining piece for the sharp `O(n^{2/3})` split-case bound is the multiplicity-from-relations
construction: at a rep point `(X−c)^{t·b} = 1`, so `g_{a,b}` collapses to `X^a`, and the `t·b`-weighted
derivatives engineer the high-order vanishing (the sibling `RepCountStepanovOrderTwo` is its base case).

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Matrix Polynomial Finset

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- The SV11 / Garcia–Voloch generator `g_{a,b}(X) = X^a · (X − c)^{t·b}`. -/
noncomputable def sv11Gen (c : F) (t : ℕ) (ab : ℕ × ℕ) : F[X] :=
  X ^ ab.1 * (X - C c) ^ (t * ab.2)

/-- The SV11 generator has `natDegree = a + t·b`. -/
theorem sv11Gen_natDegree (c : F) (t : ℕ) (ab : ℕ × ℕ) :
    (sv11Gen c t ab).natDegree = ab.1 + t * ab.2 := by
  unfold sv11Gen
  rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
        (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c)),
    Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one, mul_one]

/-- The SV11 generator is nonzero. -/
theorem sv11Gen_ne_zero (c : F) (t : ℕ) (ab : ℕ × ℕ) : sv11Gen c t ab ≠ 0 := by
  unfold sv11Gen
  exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
    (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero c))

/-- **The key degree-injectivity:** `(a, b) ↦ a + t·b` is injective on `a < t` (mod-`t` argument).
This is why the SV11 family `X^a (X−c)^{t b}` has *distinct degrees* — the engine for applying the
distinct-degree Wronskian non-vanishing certificate to it. -/
theorem add_mul_lt_injective {t a₁ b₁ a₂ b₂ : ℕ} (ha₁ : a₁ < t) (ha₂ : a₂ < t)
    (h : a₁ + t * b₁ = a₂ + t * b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) ha₁
  have hmod : a₁ = a₂ := by
    have h2 := congrArg (· % t) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂] using h2
  subst hmod
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left ht (by omega)⟩

/-- **The SV11 family Wronskian is nonzero.** Any indexed subfamily of `sv11Gen` whose degrees
`aᵢ + t·bᵢ` are distinct in `F` (e.g. by `add_mul_lt_injective` with `aᵢ < t` and the degrees below
`char F`) has nonzero classical Wronskian, in characteristic `0` or `> l−1`. This is the concrete
connector between the distinct-degree non-vanishing certificate and the Garcia–Voloch / HBK Stepanov
generator family. -/
theorem sv11_wronskianDet_ne_zero {l : ℕ} (c : F) (t : ℕ) (idx : Fin l → ℕ × ℕ)
    (hchar : ∀ a : Fin l, ((a : ℕ).factorial : F) ≠ 0)
    (hdistinct : Function.Injective
      (fun i => (((idx i).1 + t * (idx i).2 : ℕ) : F))) :
    ArkLib.ProximityGap.Wronskian.wronskianDet (fun i => sv11Gen c t (idx i)) ≠ 0 := by
  apply wronskianDet_ne_zero_of_distinctDeg
  · exact hchar
  · intro j; exact sv11Gen_ne_zero c t (idx j)
  · intro i j hij
    apply hdistinct
    dsimp only at hij ⊢
    rw [sv11Gen_natDegree, sv11Gen_natDegree] at hij
    exact hij


/-- **The b-collapse at a rep point.** If `(y − c)^t = 1` (the subgroup relation defining a rep
point), the SV11 generator `g_{a,b}(X) = X^a (X−c)^{tb}` evaluates to `y^a`, *independent of `b`*.
This is the seed of the Stepanov multiplicity-from-relations mechanism: all `g_{a,b}` sharing an `a`
collapse to the same value `y^a` at rep points, so the value-evaluation map has rank `≤ D` (not
`D·B`) — the rank deficiency the high-order vanishing exploits. -/
theorem sv11Gen_eval_of_pow_eq_one (c y : F) {t : ℕ} (a b : ℕ) (h : (y - c) ^ t = 1) :
    (sv11Gen c t (a, b)).eval y = y ^ a := by
  unfold sv11Gen
  rw [eval_mul, eval_pow, eval_X, eval_pow, eval_sub, eval_X, eval_C, pow_mul, h, one_pow, mul_one]


/-- **Free order-1 vanishing from the b-collapse rank deficiency.** Any combination
`Ψ = ∑_{a<D} ∑_{b<B} coef(a,b) · g_{a,b}` whose *row sums* vanish (`∑_b coef(a,b) = 0` ∀`a`)
evaluates to `0` at every rep point `y` (`(y−c)^t = 1`) — independent of the number of rep points.
So order-1 vanishing at *all* rep points costs only the `D` row-sum conditions (not `D·B` or one per
point): the rank deficiency (value-map rank `≤ D`) the Stepanov high-order vanishing exploits. -/
theorem sv11_combination_vanishes_of_rowsum_zero {D B : ℕ} (c : F) (t : ℕ)
    (coef : ℕ → ℕ → F) (y : F) (h : (y - c) ^ t = 1)
    (hrow : ∀ a, ∑ b ∈ Finset.range B, coef a b = 0) :
    (∑ a ∈ Finset.range D, ∑ b ∈ Finset.range B,
        Polynomial.C (coef a b) * sv11Gen c t (a, b)).eval y = 0 := by
  rw [eval_finset_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [eval_finset_sum]
  have hb : ∀ b ∈ Finset.range B,
      (Polynomial.C (coef a b) * sv11Gen c t (a, b)).eval y = coef a b * y ^ a := by
    intro b _
    rw [eval_mul, eval_C, sv11Gen_eval_of_pow_eq_one c y a b h]
  rw [Finset.sum_congr rfl hb, ← Finset.sum_mul, hrow a, zero_mul]

end ProximityGap.BinomialDet


-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.sv11Gen_eval_of_pow_eq_one
#print axioms ProximityGap.BinomialDet.sv11_combination_vanishes_of_rowsum_zero
#print axioms ProximityGap.BinomialDet.add_mul_lt_injective
#print axioms ProximityGap.BinomialDet.sv11_wronskianDet_ne_zero
