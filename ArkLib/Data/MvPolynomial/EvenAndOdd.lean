/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.CharP.Basic

import CompPoly.Data.MvPolynomial.Notation
import ArkLib.Data.MvPolynomial.Interpolation

namespace MvPolynomial

open BigOperators Fintype Finset

universe u

variable {σ : Type*} {R : Type*}

variable [Field R]
variable {n : ℕ} [NeZero n]
variable {p : MvPolynomial (Fin n) R}

private noncomputable def substPlus (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  p.aeval (fun i ↦ if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R))

private noncomputable def substMinus (p : MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) R :=
  p.aeval (fun i ↦ if i = 0 then -1 else MvPolynomial.X i)

private lemma substPlus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substPlus p ∈ restrictDegree (Fin n) R 1 := by
  have h_support : ∀ m ∈ p.support, ∀ i, m i ≤ 1 := by
    rwa [mem_restrictDegree] at hp
  unfold substPlus
  have h_monomial : ∀ m ∈ p.support, 
    (MvPolynomial.monomial m (p.coeff m)).aeval 
      (fun i ↦ if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R)) ∈ 
        restrictDegree (Fin n) R 1 := by
    intro m hm
    have h_monomial : 
      (MvPolynomial.monomial m (p.coeff m)).aeval (fun i ↦ 
        if i = 0 then 1 else (MvPolynomial.X i : MvPolynomial (Fin n) R)) = 
          MvPolynomial.monomial (m.erase 0) (p.coeff m) := by
      simp [MvPolynomial.monomial_eq, Finset.prod_ite, Finset.filter_ne', Finsupp.erase]
    rw [mem_restrictDegree]
    intro s hs i
    by_cases hi : i = 0 <;> aesop
  rw [MvPolynomial.as_sum p]
  convert Submodule.sum_mem _ h_monomial using 1
  rw [map_sum]

private lemma substMinus_mem_restrictDegree 
  {p : MvPolynomial (Fin n) R} (hp : p ∈ restrictDegree (Fin n) R 1) :
  substMinus p ∈ restrictDegree (Fin n) R 1 := by
  have := substPlus_mem_restrictDegree hp
  unfold substPlus substMinus at *
  have h_subst : 
    ∀ i : Fin n, 
      (MvPolynomial.degreeOf i 
        (MvPolynomial.bind₁ (fun i ↦ if i = 0 then -1 else X i) p)) ≤ 1 := by
    intro i
    have h_subst : ∀ m ∈ p.support, 
      (MvPolynomial.degreeOf i 
        (MvPolynomial.bind₁ 
          (fun i ↦ if i = 0 then -1 else X i) (MvPolynomial.monomial m (p.coeff m)))) ≤ 1 := by
      intro m hm
      have h_deg : ∀ i, m i ≤ 1 := by aesop 
      simp_all only [aeval_eq_bind₁, mem_support_iff, ne_eq, bind₁_monomial, ite_pow,
        ge_iff_le]
      apply le_trans (MvPolynomial.degreeOf_mul_le _ _ _) _ 
      simp_all only [degreeOf_C, zero_add]
      apply le_trans (MvPolynomial.degreeOf_prod_le _ _ _) _
      rw [Finset.sum_eq_add_sum_diff_singleton i _ (by aesop)]
      rw [Finset.sum_equiv (t := m.support \ {i}) (Equiv.refl _) (by simp) (g := fun x ↦ 0) (by {
      intro j hj 
      split_ifs with hjeq0
      · subst hjeq0
        simp
        have : m 0 = 1 := by grind
        simp [this]
      · rw [MvPolynomial.degreeOf_pow_le]
  })]


      simp [degreeOf]
      refine' le_trans ( Finset.sum_le_sum fun j hj => _ ) _;
      use fun j => if j = i then m i else 0;
      · split_ifs  
        · simp_all only [Finsupp.mem_support_iff, ne_eq, degreeOf_eq_sup,
          Finset.sup_le_iff, mem_support_iff];
          interval_cases m 0 <;> simp_all +decide [ MvPolynomial.coeff_one ];
        · cases Nat.even_or_odd ( m 0 ) <;> simp_all +decide; all_goals simp +decide [ MvPolynomial.coeff_one ];
        · simp_all +decide [ MvPolynomial.degreeOf_eq_sup ];
          simp +decide [ MvPolynomial.coeff_X_pow ];
        · simp_all +decide [ MvPolynomial.degreeOf_eq_sup ];
          rw [show 0 = ⊥ by rfl, Finset.sup_eq_bot_iff] 
          aesop (add simp [MvPolynomial.coeff_X_pow])          
      · aesop;
    rw [ MvPolynomial.as_sum p ];
    rw [ map_sum ];
    exact le_trans ( MvPolynomial.degreeOf_sum_le _ _ _ ) ( Finset.sup_le fun m hm => h_subst m hm );
  simp_all +decide [ MvPolynomial.mem_restrictDegree ];
    intro s hs i; specialize h_subst i; rw [ MvPolynomial.degreeOf_eq_sup ] at h_subst; simp_all +decide [ Finset.sup_le_iff ] ;

private lemma mul_C_mem_restrictDegree {n : ℕ} [CommRing R]
    {p : MvPolynomial (Fin n) R} (hp : p ∈ restrictDegree (Fin n) R 1)
    (c : R) : p * C c ∈ restrictDegree (Fin n) R 1 := by
      convert Submodule.smul_mem _ c hp using 1;
      rw [ mul_comm, MvPolynomial.C_mul' ]

private lemma even_mem {n : ℕ} [Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
    (substPlus p.1 + substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin n) R 1 :=
  mul_C_mem_restrictDegree ((restrictDegree (Fin n) R 1).add_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

private lemma odd_mem {n : ℕ} [Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
    (substPlus p.1 - substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin n) R 1 :=
  mul_C_mem_restrictDegree ((restrictDegree (Fin n) R 1).sub_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

noncomputable def even {n : ℕ} [Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin n)] :=
    ⟨(substPlus p.1 + substMinus p.1) * C (2⁻¹), even_mem p⟩

noncomputable def odd {n : ℕ} [Field R] [NeZero n] (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin n)] :=
    ⟨(substPlus p.1 - substMinus p.1) * C (2⁻¹), odd_mem p⟩

private lemma formula_for_monomial {n : ℕ} [NeZero n] [Field R] 
  (h2ne0 : (2 : R) ≠ 0)
  (m : Fin n →₀ ℕ) (c : R) (hm : ∀ i, m i ≤ 1) :
  (substPlus (monomial m c) + substMinus (monomial m c)) * C (2⁻¹) +
  X 0 * ((substPlus (monomial m c) - substMinus (monomial m c)) * C (2⁻¹)) = monomial m c := by
  -- Consider two cases: $m_0 = 0$ and $m_0 = 1$.
  by_cases h0 : m 0 = 0;
  · have h_subst : substPlus (MvPolynomial.monomial m c) = MvPolynomial.monomial m c ∧ substMinus (MvPolynomial.monomial m c) = MvPolynomial.monomial m c := by
      simp +decide [ substPlus, substMinus, h0 ];
      simp +decide [ MvPolynomial.bind₁_monomial, h0 ];
      simp +decide [ MvPolynomial.monomial_eq, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', h0 ];
    simp [h_subst];
    rw [ ← two_smul R, smul_mul_assoc ];
    rw [ ← MvPolynomial.C_mul' ] ; ring ;
    rw [ mul_right_comm, ← MvPolynomial.C_mul, mul_inv_cancel₀ h2ne0, MvPolynomial.C_1, one_mul ];
  · have h_monomial : monomial m c = C c * X 0 * ∏ i ∈ m.support \ {0}, X i ^ (m i) := by
      rw [MvPolynomial.monomial_eq]
      simp +decide [ mul_assoc, Finsupp.prod] 
      have : (X 0 : R[X (Fin n)]) = X 0 ^ (m 0) := by simp [show m 0 = 1 by grind]
      rw [this,
          ←Finset.prod_eq_mul_prod_diff_singleton (s := m.support) 0 
            (f := fun i ↦ X i ^ m i) (by {
        intro hmem
        have : 0 ∈ m.support := by simp [h0]
        aesop
      })] 
      exact Or.inl <| by simp +decide
    -- Now substitute this into the expression.
    simp [h_monomial, substPlus, substMinus] at *; (
    simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', h0 ] ; ring;
    simp +decide [ mul_assoc, ← mul_add ];
    erw [ ← map_mul, inv_mul_cancel₀ ] <;> norm_num [ NeZero.ne ]); -- Use `substPlus` and `substMinus` definitions.

private lemma formula_generic
  (h2ne0 : (2 : R) ≠ 0)
  (p : MvPolynomial (Fin n) R) (hp : p ∈ restrictDegree (Fin n) R 1) :
  (substPlus p + substMinus p) * C (2⁻¹) +
  X 0 * ((substPlus p - substMinus p) * C (2⁻¹)) = p := by
  have h_expand : ∀ m ∈ p.support, (substPlus (monomial m (p.coeff m)) + substMinus (monomial m (p.coeff m))) * C (2⁻¹) + X 0 * ((substPlus (monomial m (p.coeff m)) - substMinus (monomial m (p.coeff m))) * C (2⁻¹)) = monomial m (p.coeff m) := by
    intro m hm
    apply formula_for_monomial h2ne0
    exact fun i => by rw [ mem_restrictDegree ] at hp; exact hp m hm i;
  rw [ MvPolynomial.as_sum p ];
  convert Finset.sum_congr rfl h_expand using 1;
  simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_add, mul_comm, substPlus, substMinus ];
  conv_lhs => rw [ MvPolynomial.as_sum p ];
  simp +decide only [map_sum, Finset.mul_sum _ _ _];
  simp +decide only [mul_sub, Finset.mul_sum _ _ _, Finset.sum_sub_distrib]

lemma even_and_odd_formula   
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even p).1 + (MvPolynomial.X 0) * (odd p).1 = p.1 := formula_generic 
    (by aesop (add simp [CharP.charP_iff_prime_eq_zero, Nat.prime_two])) p.1 p.2

noncomputable def even_pred (p : R⦃≤ 1⦄[X (Fin n)]) : R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(even p).1.aeval 
    (fun i ↦ if h : i = 0 then 0 else X ⟨i.val - 1, by omega⟩), by sorry⟩

noncomputable def odd_pred (p : R⦃≤ 1⦄[X (Fin n)]) : R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(odd p).1.aeval 
    (fun i ↦ if h : i = 0 then 0 else X ⟨i.val - 1, by omega⟩), by sorry⟩

lemma even_and_odd_formula'
  (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even_pred p).1.aeval 
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) + 
      (MvPolynomial.X 0) * (odd_pred p).1.aeval 
        (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) = p.1 := sorry


end MvPolynomial
