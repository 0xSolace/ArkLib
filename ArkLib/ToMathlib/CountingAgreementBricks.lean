/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Counting / polynomial-agreement / hypercube bricks (WHIR #113, Fiat-Shamir #116, sumcheck #13/#114)

* `card_filter_forall_pi` — the count of length-`s` tuples whose every coordinate satisfies a
  predicate `Q` is `(#Q)^s` (WHIR out-of-domain / FS union-bound counting, #113/#116).
* `Polynomial.card_eval_agreement_le_of_natDegree_lt` — two distinct polynomials of degree `< N`
  agree on at most `N-1` field points (the counting/Schwartz–Zippel dual used in collision-count
  arguments, #113/#116).
* `Finset.sum_boolCube_prod_factor_eq_prod_sum` — the boolean-hypercube identity
  `∑_{x∈{0,1}^σ} ∏ᵢ (xᵢ=0 ? aᵢ : bᵢ) = ∏ᵢ (aᵢ + bᵢ)` underlying multilinear-extension sumcheck
  folding (#13/#114).
-/

open Finset Polynomial

/-- Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`. -/
theorem card_filter_forall_pi {β : Type*} [Fintype β] [DecidableEq β] (s : ℕ)
    (Q : β → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i))).card
      = (Finset.univ.filter Q).card ^ s := by
  have h : (Finset.univ.filter (fun r : Fin s → β => ∀ i, Q (r i)))
      = Fintype.piFinset (fun _ : Fin s => Finset.univ.filter Q) := by
    ext r; simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]; simp

namespace Polynomial

/-- Two distinct polynomials of degree `< N` agree on at most `N-1` field points. -/
theorem card_eval_agreement_le_of_natDegree_lt {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {N : ℕ} {p q : F[X]} (hpq : p ≠ q) (hp : p.natDegree < N) (hq : q.natDegree < N) :
    (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card ≤ N - 1 := by
  have hr : p - q ≠ 0 := sub_ne_zero_of_ne hpq
  have hdeg : (p - q).natDegree < N := (natDegree_sub_le p q).trans_lt (max_lt hp hq)
  have hsub : (Finset.univ.filter (fun x : F => p.eval x = q.eval x)) ⊆ (p - q).roots.toFinset := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hr, Polynomial.IsRoot.def,
      Polynomial.eval_sub, sub_eq_zero]
    exact hx
  calc (Finset.univ.filter (fun x : F => p.eval x = q.eval x)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := Polynomial.card_roots' _
    _ ≤ N - 1 := by omega

end Polynomial

namespace Finset

/-- Boolean-hypercube sum of per-coordinate two-way products factors as the product of sums. -/
theorem sum_boolCube_prod_factor_eq_prod_sum {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]
    (a b : σ → R) :
    ∑ x : σ → Fin 2, ∏ i : σ, (if x i = 0 then a i else b i) = ∏ i : σ, (a i + b i) := by
  have key : (∏ i : σ, ∑ j : Fin 2, (if j = 0 then a i else b i))
      = ∑ x : σ → Fin 2, ∏ i : σ, (if x i = 0 then a i else b i) := by
    rw [Finset.prod_univ_sum, ← Fintype.piFinset_univ]
  rw [← key]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]; simp

end Finset

#print axioms card_filter_forall_pi
#print axioms Polynomial.card_eval_agreement_le_of_natDegree_lt
#print axioms Finset.sum_boolCube_prod_factor_eq_prod_sum
