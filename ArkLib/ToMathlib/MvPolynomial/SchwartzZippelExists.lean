/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib

/-!
# Multivariate Schwartz–Zippel: existence of a non-vanishing point (#389)

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` bounds the *fraction* of a finite cube
`S^n` on which a nonzero polynomial vanishes by `totalDegree / #S`.  For the GM-MDS /
generic-zero-pattern construction (Lovett arXiv:1803.02523, p. 3) we need the *existence*
consequence: when the total degree is strictly below the field (or sample-set) size, a
non-vanishing evaluation point exists; and, taking the polynomial multiplied by the
Vandermonde difference product, a non-vanishing point with **pairwise distinct** coordinates
exists, i.e. an injection `Fin n ↪ F`.

## Main results

* `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card`: nonzero `P` with
  `P.totalDegree < Fintype.card F` over a finite field `F` has a point `r` with `eval r P ≠ 0`.
* `MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card_finset`: the `Finset` form over an
  integral domain, using a sample set `S` with `P.totalDegree < #S`.
* `MvPolynomial.exists_embedding_eval_ne_zero`: the distinct-coordinate upgrade — if
  `P.totalDegree + n*(n-1)/2 < #S` then there is an embedding `φ : Fin n ↪ R` (distinct
  coordinates inside `S`) with `eval (φ ·) P ≠ 0`.

Issue #389.
-/

open Finset Fintype

namespace MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Schwartz–Zippel, existence form (Finset version).**  Over an integral domain `R`, a
nonzero polynomial `P` whose total degree is strictly below the size of a sample set `S` has a
point `f : Fin n → R` with all coordinates in `S` at which `eval f P ≠ 0`.

Proof: the SZ counting bound `#{zeros in S^n} / #S^n ≤ totalDegree / #S < 1` forces the zero
set to be a proper subset of `S^n`, which is nonempty. -/
theorem exists_eval_ne_zero_of_totalDegree_lt_card_finset {n : ℕ}
    {P : MvPolynomial (Fin n) R} (hP : P ≠ 0) (S : Finset R)
    (hdeg : P.totalDegree < S.card) :
    ∃ f : Fin n → R, (∀ i, f i ∈ S) ∧ eval f P ≠ 0 := by
  classical
  -- The full cube `S^n`.
  set cube : Finset (Fin n → R) := Fintype.piFinset (fun _ : Fin n => S) with hcube
  have hScard_pos : 0 < S.card := lt_of_le_of_lt (Nat.zero_le _) hdeg
  have hSne : S.Nonempty := Finset.card_pos.mp hScard_pos
  -- The cube is nonempty.
  have hcube_ne : cube.Nonempty := by
    rw [hcube]
    exact Fintype.piFinset_nonempty.mpr (fun _ => hSne)
  -- The zero-set, as a subset of the cube.
  set Z : Finset (Fin n → R) := {f ∈ cube | eval f P = 0} with hZ
  -- SZ counting bound gives `#Z / #S^n ≤ totalDegree / #S`.
  have hsz := schwartz_zippel_totalDegree (p := P) hP S
  -- Rewrite using `cube`/`Z` cardinalities.
  -- The LHS numerator in `schwartz_zippel_totalDegree` is exactly `#Z`.
  -- Show `#Z < #cube`, hence `Z ⊊ cube`, giving an element of `cube \ Z`.
  have hcube_card : cube.card = S.card ^ n := by
    rw [hcube, Fintype.card_piFinset]
    simp [Finset.prod_const]
  -- Convert the rational inequality to a strict cardinality inequality.
  -- From `#Z / #S^n ≤ deg / #S` and `deg < #S` we get `#Z * #S ≤ deg * #S^n < #S * #S^n`.
  have hbound : (Z.card : ℚ≥0) * S.card < (S.card : ℚ≥0) * (S.card ^ n) := by
    have hScast : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hScard_pos
    have hSncast : (0 : ℚ≥0) < (S.card ^ n : ℚ≥0) := by positivity
    -- `#Z / #S^n ≤ deg / #S`
    have hsz' : (Z.card : ℚ≥0) / (S.card ^ n : ℚ≥0) ≤ (P.totalDegree : ℚ≥0) / S.card := by
      simpa [hZ, hcube] using hsz
    -- multiply both sides by `#S^n * #S` and use `deg < #S`.
    have hdeg' : (P.totalDegree : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hdeg
    calc (Z.card : ℚ≥0) * S.card
        = ((Z.card : ℚ≥0) / (S.card ^ n)) * ((S.card ^ n) * S.card) := by
          field_simp
      _ ≤ ((P.totalDegree : ℚ≥0) / S.card) * ((S.card ^ n) * S.card) := by
          gcongr
      _ = (P.totalDegree : ℚ≥0) * (S.card ^ n) := by
          have hSne0 : (S.card : ℚ≥0) ≠ 0 := by exact_mod_cast hScard_pos.ne'
          field_simp
      _ < (S.card : ℚ≥0) * (S.card ^ n) := by gcongr
  -- Cancel `#S > 0` to get `#Z < #S^n = #cube`.
  have hZlt : Z.card < cube.card := by
    rw [hcube_card]
    have hScast : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hScard_pos
    have hkey : (Z.card : ℚ≥0) < (S.card ^ n : ℚ≥0) := by
      have := hbound
      rw [mul_comm (S.card : ℚ≥0) ((S.card : ℚ≥0) ^ n)] at this
      exact lt_of_mul_lt_mul_right this (le_of_lt hScast)
    exact_mod_cast hkey
  -- `Z ⊆ cube` and `#Z < #cube` ⟹ `cube \ Z` nonempty.
  obtain ⟨f, hf⟩ := Finset.sdiff_nonempty_of_card_lt_card hZlt
  rw [Finset.mem_sdiff] at hf
  refine ⟨f, ?_, ?_⟩
  · intro i
    have := hf.1
    rw [hcube, Fintype.mem_piFinset] at this
    exact this i
  · intro hcontra
    exact hf.2 (Finset.mem_filter.mpr ⟨hf.1, hcontra⟩)

/-- **Schwartz–Zippel, existence form over a finite field.**  A nonzero polynomial `P` whose
total degree is strictly below `Fintype.card F` has a point `r` with `eval r P ≠ 0`. -/
theorem exists_eval_ne_zero_of_totalDegree_lt_card {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {n : ℕ} {P : MvPolynomial (Fin n) F} (hP : P ≠ 0)
    (hdeg : P.totalDegree < Fintype.card F) :
    ∃ r : Fin n → F, eval r P ≠ 0 := by
  obtain ⟨f, _, hf⟩ := exists_eval_ne_zero_of_totalDegree_lt_card_finset hP
    (S := (Finset.univ : Finset F)) (by simpa [Finset.card_univ] using hdeg)
  exact ⟨f, hf⟩

/-! ## Distinct-coordinate upgrade -/

/-- The Vandermonde difference polynomial `∏_{i<j} (Xᵢ − Xⱼ)` in `n` variables. -/
noncomputable def vandermondeDiff (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n) R :=
  ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
    (MvPolynomial.X p.1 - MvPolynomial.X p.2)

/-- A point evaluates the Vandermonde difference to a nonzero value iff its coordinates are
pairwise distinct (over a domain). -/
theorem eval_vandermondeDiff_ne_zero_iff {n : ℕ} (f : Fin n → R) :
    eval f (vandermondeDiff R n) ≠ 0 ↔ Function.Injective f := by
  classical
  rw [vandermondeDiff, map_prod]
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := h (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
      simp [hij] at this
    · have := h (j, i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
      simp [hij] at this
  · intro hinj p hp
    rw [Finset.mem_filter] at hp
    have hlt := hp.2
    simp only [map_sub, eval_X, sub_ne_zero]
    intro hcontra
    exact (ne_of_lt hlt) (hinj hcontra)

/-- The total degree of the Vandermonde difference is at most `C(n,2) = n*(n-1)/2`. -/
theorem totalDegree_vandermondeDiff_le {n : ℕ} :
    (vandermondeDiff R n).totalDegree ≤ n * (n - 1) / 2 := by
  classical
  rw [vandermondeDiff]
  refine le_trans (totalDegree_finset_prod _ _) ?_
  have hbound : ∀ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (MvPolynomial.X (R := R) p.1 - MvPolynomial.X p.2).totalDegree ≤ 1 := by
    intro p _
    refine le_trans (totalDegree_sub _ _) ?_
    simp [totalDegree_X]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  -- the number of strict pairs is `C(n,2) = n*(n-1)/2`.
  have hcard : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card
      = n * (n - 1) / 2 := by
    classical
    rw [← Finset.sum_range_id n]
    -- fiber strict pairs over the second coordinate `j`; each fiber has `j` elements `i < j`.
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : Fin n × Fin n => (p.2 : ℕ)) (t := Finset.range n)
      (fun p hp => by simp [p.2.2])]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    -- the fiber over `j` is `{ (i, j') | i < j' ∧ j' = j }`, which has card `j`.
    have : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2) |>.filter
        (fun p => (p.2 : ℕ) = j)).card = j := by
      rw [Finset.filter_filter]
      -- bijection with `{ i : Fin n | (i:ℕ) < j }`, image of `Finset.range j`.
      have hbij : (Finset.univ.filter
          (fun p : Fin n × Fin n => p.1 < p.2 ∧ (p.2 : ℕ) = j)).card
          = (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)).card := by
        apply Finset.card_bij (fun p _ => p.1)
        · rintro ⟨a, b⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          rw [← hp.2]; exact_mod_cast hp.1
        · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          simp only at h
          have : b = d := by
            apply Fin.ext; rw [hp.2, hq.2]
          subst h this; rfl
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hjlt : j < n := hj
          refine ⟨(i, ⟨j, hjlt⟩), ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, rfl⟩
          exact_mod_cast hi
      rw [hbij]
      -- count `i : Fin n` with `(i:ℕ) < j`: this is `Finset.Iio ⟨j, _⟩`, of card `j`.
      have hjlt : j < n := hj
      have heq : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < j))
          = Finset.Iio (⟨j, hjlt⟩ : Fin n) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
          Fin.lt_def]
      rw [heq, Fin.card_Iio]
    convert this using 2
  rw [hcard]

/-- **Schwartz–Zippel with distinct coordinates (existence of an injective evaluation point).**
If `P.totalDegree + n*(n-1)/2 < #S` for a sample set `S` over an integral domain, then there is
an injection `φ : Fin n ↪ R` with all coordinates in `S` and `eval (φ ·) P ≠ 0`.

This is the key GM-MDS upgrade: multiplying `P` by the Vandermonde difference forces the
non-vanishing point to have pairwise-distinct coordinates. -/
theorem exists_embedding_eval_ne_zero {n : ℕ} {P : MvPolynomial (Fin n) R} (hP : P ≠ 0)
    (S : Finset R) (hdeg : P.totalDegree + n * (n - 1) / 2 < S.card) :
    ∃ φ : Fin n ↪ R, (∀ i, φ i ∈ S) ∧ eval (φ ·) P ≠ 0 := by
  classical
  set Q : MvPolynomial (Fin n) R := P * vandermondeDiff R n with hQ
  -- `vandermondeDiff ≠ 0`: product of nonzero factors over a domain.
  have hVne : vandermondeDiff R n ≠ 0 := by
    rw [vandermondeDiff, Finset.prod_ne_zero_iff]
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [sub_ne_zero]
    intro hXeq
    exact (ne_of_lt hp.2) (MvPolynomial.X_injective hXeq)
  have hQne : Q ≠ 0 := mul_ne_zero hP hVne
  -- total degree of `Q` is below `#S`.
  have hQdeg : Q.totalDegree < S.card := by
    refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
    exact lt_of_le_of_lt (Nat.add_le_add_left totalDegree_vandermondeDiff_le _) hdeg
  -- find a non-vanishing point of `Q` inside `S`.
  obtain ⟨f, hfS, hfQ⟩ := exists_eval_ne_zero_of_totalDegree_lt_card_finset hQne S hQdeg
  rw [hQ, map_mul, mul_ne_zero_iff] at hfQ
  -- `f` has distinct coordinates, hence is an embedding.
  have hinj : Function.Injective f := (eval_vandermondeDiff_ne_zero_iff f).mp hfQ.2
  refine ⟨⟨f, hinj⟩, hfS, ?_⟩
  exact hfQ.1

end MvPolynomial

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]`.
#print axioms MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card_finset
#print axioms MvPolynomial.exists_eval_ne_zero_of_totalDegree_lt_card
#print axioms MvPolynomial.eval_vandermondeDiff_ne_zero_iff
#print axioms MvPolynomial.totalDegree_vandermondeDiff_le
#print axioms MvPolynomial.exists_embedding_eval_ne_zero
