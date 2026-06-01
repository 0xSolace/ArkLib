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
  MvPolynomial (Fin (n - 1)) R := p.aeval <| fun i ↦ 
  if h : i = 0 then 1 else MvPolynomial.X ⟨i.val - 1, by omega⟩ 

private noncomputable def substMinus (p : MvPolynomial (Fin n) R) : 
  MvPolynomial (Fin (n - 1)) R := p.aeval <| 
  fun i ↦ if h : i = 0 then -1 else MvPolynomial.X ⟨i.val - 1, by omega⟩

omit [Field R] [NeZero n] in
private lemma prod_X_injective_mem_restrictDegree {σ τ : Type*} [DecidableEq σ]
    [DecidableEq τ] {R : Type*} [CommSemiring R] [Nontrivial R]
    {S : Finset σ} {g : σ → τ} (hg : Set.InjOn g ↑S) :
    (∏ i ∈ S, (X (g i) : MvPolynomial τ R)) ∈ restrictDegree τ R 1 := by
      -- Apply the lemma that the degree of the product of polynomials is the sum of their degrees.
      have h_deg : ∀ j : τ, Multiset.count j (∏ i ∈ S, X (g i) : MvPolynomial τ R).degrees ≤ 1 := by
        intro j
        have h_deg_p : Multiset.count j (∏ i ∈ S, (X (g i)) : MvPolynomial τ R).degrees ≤ ∑ i ∈ S, Multiset.count j (X (g i) : MvPolynomial τ R).degrees := by
          convert MvPolynomial.degreeOf_prod_le _ _ _ using 1;
          any_goals exact j;
          any_goals exact S;
          any_goals exact R;
          any_goals exact fun i => X ( g i );
          · exact?;
          · simp +decide [ degreeOf ];
            convert rfl;
        refine' le_trans h_deg_p _;
        simp +decide [ Multiset.count_singleton ];
        exact Finset.card_le_one.mpr fun x hx y hy => hg ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hy |>.1 ) ( by aesop );
      exact?

omit [Field R] [NeZero n] in
private lemma C_mul_mem_restrictDegree {σ : Type*} {R : Type*} [CommSemiring R]
  {q : MvPolynomial σ R} (hq : q ∈ restrictDegree σ R 1) (r : R) :
  C r * q ∈ restrictDegree σ R 1 := by grind +suggestions

omit [NeZero n] in
private lemma mul_C_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) (c : R) : 
  p * C c ∈ restrictDegree (Fin n) R 1 := by
  convert Submodule.smul_mem _ c hp using 1
  rw [mul_comm, MvPolynomial.C_mul']


private lemma substPlus_monomial_mem (m : Fin n →₀ ℕ) (c : R)
    (hm : ∀ i, m i ≤ 1) :
    substPlus (monomial m c) ∈ restrictDegree (Fin (n - 1)) R 1 := by
      by_contra! h_contra;
      unfold MvPolynomial.substPlus at h_contra;
      refine' h_contra _;
      simp +decide [ aeval_def, monomial_eq ];
      refine' C_mul_mem_restrictDegree _ c;
      convert prod_X_injective_mem_restrictDegree _ using 1;
      any_goals exact Finset.univ.filter fun i => m i = 1 ∧ i ≠ 0;
      any_goals try infer_instance;
      rotate_left;
      use fun i => ⟨ i.val - 1, by
        rcases i with ⟨ _ | i, hi ⟩ <;> norm_num;
        · rcases n with ( _ | _ | n ) <;> simp_all +decide;
          simp_all +decide [ restrictDegree ];
        · exact Nat.lt_pred_iff.mpr hi ⟩
      all_goals generalize_proofs at *;
      · intro i hi j hj hij;
        grind;
      · rw [ Finset.prod_filter ] ; congr ; ext i ; specialize hm i ; interval_cases _ : m i <;> aesop;

/-
The monomial case for substMinus
-/
private lemma substMinus_monomial_mem (m : Fin n →₀ ℕ) (c : R)
    (hm : ∀ i, m i ≤ 1) :
    substMinus (monomial m c) ∈ restrictDegree (Fin (n - 1)) R 1 := by
      rcases n with ( _ | _ | n ) <;> simp_all +decide [ MvPolynomial, Finsupp.prod ];
      · exact False.elim <| NeZero.ne 0 rfl;
      · interval_cases _ : m 0 <;> simp_all +decide [ substMinus, restrictDegree ];
      · -- Consider the product $\prod_{i \in m.support} (if i = 0 then -1 else X (i - 1))^{m i}$.
        have h_prod : (∏ i ∈ m.support, (if i = 0 then (-1 : MvPolynomial (Fin (n + 1)) R) else MvPolynomial.X ⟨i.val - 1, by omega⟩) ^ (m i)) ∈ restrictDegree (Fin (n + 1)) R 1 := by
          -- Consider the product $\prod_{i \in m.support} (if i = 0 then -1 else X (i - 1))^{m i}$ and split it into two parts: one for $i = 0$ and one for $i \neq 0$.
          have h_prod_split : (∏ i ∈ m.support.filter (· ≠ 0), (MvPolynomial.X ⟨i.val - 1, by omega⟩) ^ (m i)) ∈ restrictDegree (Fin (n + 1)) R 1 := by
            -- Since $m i \ (�le�q 1$ for all $i$, we have $m i = 1$ for all $i \in m.support$.
            have h_m_one : ∀ i ∈ m.support.filter (· ≠ 0), m i = 1 := by
              exact fun i hi => le_antisymm ( hm i ) ( Nat.pos_of_ne_zero ( by aesop ) );
            rw [ Finset.prod_congr rfl fun i hi => by rw [ h_m_one i hi, pow_one ] ];
            convert prod_X_injective_mem_restrictDegree _;
            · infer_instance;
            · infer_instance;
            · infer_instance;
            · intro i hi j hj hij; rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> norm_num at * ; aesop;
          by_cases h : m 0 = 0 <;> simp_all +decide [ Finset.prod_ite, Finset.filter_ne' ];
          convert C_mul_mem_restrictDegree h_prod_split ( ( -1 ) ^ m 0 ) using 1;
          rw [ Finset.card_filter ] ; aesop;
        convert C_mul_mem_restrictDegree h_prod c using 1;
        convert MvPolynomial.aeval_monomial _ _ _ using 1

private lemma substPlus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substPlus p ∈ restrictDegree (Fin (n - 1)) R 1 := by  
  convert Submodule.sum_mem _ _;
  intro c hc; convert substPlus_monomial_mem c ( p.coeff c ) ?_ using 1;
  · simp +decide [ MvPolynomial.substPlus ];
    erw [ MvPolynomial.bind₁_monomial ] ; aesop;
  · convert hp using 1;
    unfold restrictDegree; aesop;

private lemma substMinus_mem_restrictDegree
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  substMinus p ∈ restrictDegree (Fin (n - 1)) R 1 := by
    convert Submodule.sum_mem _ _;
    intro c hc; convert substMinus_monomial_mem c ( p.coeff c ) ?_ using 1;
    · unfold MvPolynomial.substMinus; simp +decide [ MvPolynomial.monomial_eq ] ;
      simp +decide [ Finsupp.prod ];
      rw [ Finset.prod_subset ( Finset.subset_univ _ ) ] ; aesop;
      aesop;
    · intro i; have := hp; aesop;

private lemma even_mem (p : R⦃≤ 1⦄[X (Fin n)]) :
  (substPlus p.1 + substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin (n - 1)) R 1 :=
  mul_C_mem_restrictDegree
    ((restrictDegree (Fin (n - 1)) R 1).add_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

private lemma odd_mem (p : R⦃≤ 1⦄[X (Fin n)]) :
  (substPlus p.1 - substMinus p.1) * C (2⁻¹) ∈ restrictDegree (Fin (n - 1)) R 1 :=
  mul_C_mem_restrictDegree
  ((restrictDegree (Fin (n - 1)) R 1).sub_mem
    (substPlus_mem_restrictDegree p.2) (substMinus_mem_restrictDegree p.2)) _

noncomputable def even (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(substPlus p.1 + substMinus p.1) * C (2⁻¹), even_mem p⟩

noncomputable def odd (p : R⦃≤ 1⦄[X (Fin n)]) :
  R⦃≤ 1⦄[X (Fin (n - 1))] :=
  ⟨(substPlus p.1 - substMinus p.1) * C (2⁻¹), odd_mem p⟩

omit [NeZero n] in
private lemma decomposition_lemma
  (p : MvPolynomial (Fin n) R) :
  ∃ q : Fin n →₀ ℕ, p = monomial q (p.coeff q) + ∑ m ∈ p.support \ {q}, monomial m (p.coeff m) := by
  rcases p.support.eq_empty_or_nonempty with h | ⟨q, hq⟩
  · aesop
  · exists q
    aesop

omit [NeZero n] in
private lemma multilinear_monomial_bound
  (p : MvPolynomial (Fin n) R)
  (hp : p ∈ restrictDegree (Fin n) R 1)
  {m : Fin n →₀ ℕ} (hm : m ∈ p.support) {i : Fin n} :
  m i ≤ 1 := by grind +suggestions

private lemma mono_decomposition_lemma
  (p : MvPolynomial (Fin n) R) 
  (hp : p ∈ restrictDegree (Fin n) R 1) :
  ∀ m ∈ p.support, (aeval (fun i ↦ X ⟨i.val + 1, by omega⟩) (substPlus (monomial m (p.coeff m)) + substMinus (monomial m (p.coeff m))) * C (2⁻¹) + X 0 * (aeval (fun i ↦ X ⟨i.val + 1, by omega⟩) (substPlus (monomial m (p.coeff m)) - substMinus (monomial m (p.coeff m))) * C (2⁻¹))) = monomial m (p.coeff m) := by
  intro m hm
  have h_m : ∀ i, m i ≤ 1 := fun i ↦ multilinear_monomial_bound p hp hm (i := i)
  unfold substPlus substMinus
  rcases n with _ | n
  · aesop (add simp [Fin.prod_univ_succ, MvPolynomial.monomial_eq]) 
  · simp only [mem_support_iff, ne_eq, Nat.add_one_sub_one, aeval_eq_bind₁, monomial_eq,
    Finsupp.prod_pow, Fin.prod_univ_succ] at *
    have := h_m 0
    interval_cases _ : m 0 
    · simp +decide [‹_›]; ring_nf;
      simp +decide [ add_comm, mul_assoc, mul_comm, mul_left_comm ];
      convert congr_arg ( fun x : MvPolynomial ( Fin ( n + 1 ) ) R => x * ( C ( coeff m p ) * ∏ x : Fin n, X x.succ ^ m x.succ ) ) ( show ( 2 : MvPolynomial ( Fin ( n + 1 ) ) R ) * C 2⁻¹ = 1 from ?_ ) using 1 ; ring!;
      · rw [ one_mul ];
      · rw [ show ( 2 : MvPolynomial ( Fin ( n + 1 ) ) R ) = C 2 by rfl, ← MvPolynomial.C_mul ] ; norm_num;
        rw [ ← MvPolynomial.C_mul, mul_inv_cancel₀ ] <;> norm_num;
        contrapose! hchar;
        constructor;
        intro x; rw [ ← Nat.mod_add_div x 2 ] ; norm_num [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hchar ] ;
        cases Nat.mod_two_eq_zero_or_one x <;> simp +decide [ ‹_›, hchar ];
    · simp +decide [ ‹_› ] ; ring;
      simp +decide [ ← two_mul, mul_assoc, mul_comm, mul_left_comm ];
      convert congr_arg ( fun x : MvPolynomial ( Fin ( n + 1 ) ) R => x * ( C ( coeff m p ) * ∏ i : Fin n, X ⟨ i + 1, by linarith [ Fin.is_lt i ] ⟩ ^ m ( Fin.succ i ) ) ) ( show ( 2 : MvPolynomial ( Fin ( n + 1 ) ) R ) * C 2⁻¹ = 1 from ?_ ) using 1 ; ring!;
      · simp +decide [ Fin.add_def, Fin.succ ];
      · erw [ ← MvPolynomial.C_mul ] ; norm_num;
        rw [ ← MvPolynomial.C_mul, mul_inv_cancel₀ ] <;> norm_num;
        exact fun h => hchar <| by exact ⟨ fun n => by
          rw [ ← Nat.mod_add_div n 2 ] ; norm_cast ; simp +decide [ Nat.add_mod, Nat.mul_mod, h ] ;
          cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [ *, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ] ⟩ ;

set_option maxHeartbeats 8000000 in
private lemma formula_generic
  (hchar : ¬CharP R 2)
  (p : MvPolynomial (Fin n) R) (hp : p ∈ restrictDegree (Fin n) R 1) :
  (substPlus p + substMinus p).aeval 
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) * C (2⁻¹) +
  X 0 * ((substPlus p - substMinus p).aeval
    (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) * C (2⁻¹)) = p := by
  obtain ⟨q, hq⟩ := decomposition_lemma p
  -- By linearity of the substitution maps and the fact that $p$ is a sum of monomials, we can apply the decomposition to each monomial.
  have h_decomp_mono : ∀ m ∈ p.support, (aeval (fun i => X ⟨i.val + 1, by omega⟩) (substPlus (monomial m (p.coeff m)) + substMinus (monomial m (p.coeff m))) * C (2⁻¹) + X 0 * (aeval (fun i => X ⟨i.val + 1, by omega⟩) (substPlus (monomial m (p.coeff m)) - substMinus (monomial m (p.coeff m))) * C (2⁻¹))) = monomial m (p.coeff m) := by
    intro m hm
    have h_m : ∀ i, m i ≤ 1 := by
      grind +suggestions;
    unfold substPlus substMinus;
    rcases n with ( _ | n ) <;> simp +decide [ Fin.prod_univ_succ, MvPolynomial.monomial_eq ] at *;
    · exact False.elim <| NeZero.ne 0 rfl;
    · have := h_m 0; interval_cases _ : m 0 <;> simp +decide [ ‹_› ] ; ring;
      · simp +decide [ add_comm, mul_assoc, mul_comm, mul_left_comm ];
        convert congr_arg ( fun x : MvPolynomial ( Fin ( n + 1 ) ) R => x * ( C ( coeff m p ) * ∏ x : Fin n, X x.succ ^ m x.succ ) ) ( show ( 2 : MvPolynomial ( Fin ( n + 1 ) ) R ) * C 2⁻¹ = 1 from ?_ ) using 1 ; ring!;
        · rw [ one_mul ];
        · rw [ show ( 2 : MvPolynomial ( Fin ( n + 1 ) ) R ) = C 2 by rfl, ← MvPolynomial.C_mul ] ; norm_num;
          rw [ ← MvPolynomial.C_mul, mul_inv_cancel₀ ] <;> norm_num;
          contrapose! hchar;
          constructor;
          intro x; rw [ ← Nat.mod_add_div x 2 ] ; norm_num [ pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, hchar ] ;
          cases Nat.mod_two_eq_zero_or_one x <;> simp +decide [ ‹_›, hchar ];
      · simp +decide [ ← two_mul, mul_assoc, mul_comm, mul_left_comm ];
        convert congr_arg ( fun x : MvPolynomial ( Fin ( n + 1 ) ) R => x * ( C ( coeff m p ) * ∏ i : Fin n, X ⟨ i + 1, by linarith [ Fin.is_lt i ] ⟩ ^ m ( Fin.succ i ) ) ) ( show ( 2 : MvPolynomial ( Fin ( n + 1 ) ) R ) * C 2⁻¹ = 1 from ?_ ) using 1 ; ring!;
        · simp +decide [ Fin.add_def, Fin.succ ];
        · erw [ ← MvPolynomial.C_mul ] ; norm_num;
          rw [ ← MvPolynomial.C_mul, mul_inv_cancel₀ ] <;> norm_num;
          exact fun h => hchar <| by exact ⟨ fun n => by
            rw [ ← Nat.mod_add_div n 2 ] ; norm_cast ; simp +decide [ Nat.add_mod, Nat.mul_mod, h ] ;
            cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [ *, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod ] ⟩ ;
  -- Apply the decomposition to each monomial in the sum.
  have h_decomp_sum : (aeval (fun i => X ⟨i.val + 1, by omega⟩) (∑ m ∈ p.support, substPlus (monomial m (p.coeff m)) + ∑ m ∈ p.support, substMinus (monomial m (p.coeff m))) * C (2⁻¹) + X 0 * (aeval (fun i => X ⟨i.val + 1, by omega⟩) (∑ m ∈ p.support, substPlus (monomial m (p.coeff m)) - ∑ m ∈ p.support, substMinus (monomial m (p.coeff m))) * C (2⁻¹))) = ∑ m ∈ p.support, monomial m (p.coeff m) := by
    rw [ ← Finset.sum_congr rfl h_decomp_mono ];
    simp +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
    simp +decide only [add_mul, sum_mul, sub_mul, mul_sub, mul_sum, sum_add_distrib];
    rw [ Finset.sum_sub_distrib ];
  convert h_decomp_sum using 1;
  · rw [ ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib ];
    rw [ show p.substPlus = ∑ m ∈ p.support, ( monomial m ( p.coeff m ) ).substPlus from ?_, show p.substMinus = ∑ m ∈ p.support, ( monomial m ( p.coeff m ) ).substMinus from ?_ ];
    · simp +decide only [sum_add_distrib, sum_sub_distrib];
    · conv_lhs => rw [ p.as_sum ];
      unfold MvPolynomial.substMinus;
      rw [ map_sum ];
    · convert congr_arg ( fun q => q.substPlus ) ( MvPolynomial.as_sum p ) using 1;
      unfold MvPolynomial.substPlus;
      rw [ map_sum ];
  · conv_lhs => rw [ MvPolynomial.as_sum p ] ;
  
/-- The original formula `even_and_odd_formula` is false in characteristic 2 (where `2⁻¹ = 0`).
    This corrected version adds the hypothesis `[NeZero (2 : R)]` to ensure characteristic ≠ 2. -/
lemma even_and_odd_formula (hchar : ¬CharP R 2)
  {p : R⦃≤ 1⦄[X (Fin n)]} :
  (even p).1.aeval (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) + 
    (MvPolynomial.X 0) * (odd p).1.aeval (fun i ↦ X (⟨i.val + 1, by omega⟩ : Fin n)) = p.1 := by
  aesop 
    (add simp [even, odd])
    (add safe forward [formula_generic])

end MvPolynomial
