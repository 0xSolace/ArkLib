/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Hasse-derivative evaluation identity

`Polynomial.hasseDeriv_eval_eq_sum`:
`(hasseDeriv k p).eval a = ∑_{i ≤ deg p} C(i,k) · p.coeff i · a^{i-k}`.

This is the order-`k` Hasse-derivative analogue of `Polynomial.eval_eq_sum_range`, expressing the
evaluation of the `k`-th Hasse derivative as a binomial-weighted, shifted coefficient sum. It is
the genuine combinatorial core (★) underlying BCIKS20 Appendix-A's `RestrictedFaaDiBrunoMatch`
(issue #9): summing the `Y`-Hasse coefficients of a polynomial against the order-`k` binomial
`C(i,k)` and the `α₀^{i-k}` shift *is* the order-`k` Hasse derivative evaluated at `α₀`, which is the
`hasseCoeffRepr𝒪` representative emitted by the `(A.1)` recursion.

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace Polynomial

open Finset

/-- **Hasse-derivative evaluation identity (★).** The evaluation of the order-`k` Hasse derivative
of `p` at `a` equals the binomial-weighted, `k`-shifted coefficient sum
`∑_{i ≤ deg p} C(i,k) · p.coeff i · a^{i-k}`.

Proof: rewrite the LHS as a range sum via `eval_eq_sum_range'`, rewrite each Hasse coefficient via
`hasseDeriv_coeff`, drop the `i < k` terms (`Nat.choose_eq_zero_of_lt`) on the RHS and the
`i + k > deg p` terms (`coeff_eq_zero_of_natDegree_lt`) on the LHS, and reindex `i = n + k` by the
explicit bijection `i ↦ i − k` between the two surviving filtered ranges. -/
theorem hasseDeriv_eval_eq_sum {R : Type*} [CommRing R] (k : ℕ) (p : R[X]) (a : R) :
    (hasseDeriv k p).eval a
      = ∑ i ∈ Finset.range (p.natDegree + 1), (i.choose k : R) * p.coeff i * a ^ (i - k) := by
  set D := p.natDegree with hD
  have hbd : (hasseDeriv k p).natDegree < D + 1 :=
    Nat.lt_succ_of_le ((natDegree_hasseDeriv_le p k).trans (Nat.sub_le _ _))
  rw [eval_eq_sum_range' hbd]
  have hL : ∀ n ∈ Finset.range (D + 1),
      (hasseDeriv k p).coeff n * a ^ n
        = ((n + k).choose k : R) * p.coeff (n + k) * a ^ n := by
    intro n _; rw [hasseDeriv_coeff]
  rw [Finset.sum_congr rfl hL]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (D + 1)) (fun i => k ≤ i)]
  have hlow : ∑ i ∈ (Finset.range (D + 1)).filter (fun i => ¬ k ≤ i),
        (i.choose k : R) * p.coeff i * a ^ (i - k) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [Nat.choose_eq_zero_of_lt (not_le.mp hi.2)]; simp
  rw [hlow, add_zero]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (D + 1)) (fun n => n + k ≤ D)]
  have hhi : ∑ n ∈ (Finset.range (D + 1)).filter (fun n => ¬ n + k ≤ D),
        ((n + k).choose k : R) * p.coeff (n + k) * a ^ n = 0 := by
    refine Finset.sum_eq_zero (fun n hn => ?_)
    rw [Finset.mem_filter] at hn
    rw [show p.coeff (n + k) = 0 from
      coeff_eq_zero_of_natDegree_lt (by rw [← hD]; omega)]
    ring
  rw [hhi, add_zero]
  refine Finset.sum_bij' (fun i _ => i - k) (fun n _ => n + k) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    dsimp only; omega
  · intro n hn
    dsimp only; omega
  · intro i hi
    rw [Finset.mem_filter] at hi
    have hik : k ≤ i := hi.2
    rw [Nat.sub_add_cancel hik]

end Polynomial

-- Axiom audit.
#print axioms Polynomial.hasseDeriv_eval_eq_sum
