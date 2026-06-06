/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeJ1Cap
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower

/-!
# The exact interior radius-`1/n` MCA error: `ε_mca(C, 1/n) = 2/q`

This file ports the *resultant / quadratic* form of the proven interior J1 theorem
("`P[1] = 2`", research note `J1-EXACT-THEOREM-2026-06-06.md`) to Lean: for a Reed–Solomon
code `C = RS[F, domain, k]` over an `n`-point domain (`n := #ι`) with `n ≥ k + 3` (so an
interior lattice point exists) and `2 ≤ q := |F|`,

  `ε_mca(C, 1/n) = 2 / q`.

The radius `1/n` is the first nonzero MCA lattice point, `mcaLatticePoint n 1`.

## The two directions

* **Upper bound `ε_mca(C, 1/n) ≤ 2/q`** — the new content.  Via the exact extremal form
  `ε_mca(C, δ) = (⨆ u, mcaBadCount C δ (u 0) (u 1)) / q` (`epsMCA_eq_iSup_mcaBadCount`) this
  reduces to the finite cap `mcaBadCount C (1/n) u₀ u₁ ≤ 2`, which we re-derive here through
  the **resultant route** the research note specifies:

  - **Lemma HIGH / LINE** (imported from `GrandChallengesLattice`).  Every MCA-bad scalar `γ`
    at radius `1/n` is a J1 ratio constraint (`mcaEvent_j1_exists_window_ratio_constraints`),
    and the omit-one-window high-coefficient equations
    (`cT_vanish_on_j1_window_full_top_coeff_equations`) eliminate the omitted coordinate.
  - **Lemma QUAD** (this file: `j1FullTopQuadratic_natDegree_le_two`,
    `j1RatioConstraintBadScalars_subset_quadratic_roots`,
    `j1RatioConstraintBadScalars_card_le_two_via_quadratic`).  The eliminant is the universal
    degree-`≤ 2` polynomial `Q := j1FullTopQuadratic domain u₀ u₁`; every constrained scalar is
    a root of it (`j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero`).  When `Q ≠ 0`, a nonzero
    degree-`≤ 2` polynomial over a field has `≤ 2` roots (`card_le_degree_of_subset_roots`), so
    the constrained set has `≤ 2` elements.
  - **Lemma DEGEN** (imported `j1RatioConstraintBadScalars_card_le_two`).  When `Q ≡ 0` the
    resultant carries no information; the cap is instead closed by the joint-extendability
    window-collision argument (`not_three_j1_ratioConstraints`), which is unconditional.

* **Lower bound `2/q ≤ ε_mca(C, 1/n)`** — the explicit `2`-spike plant
  (`epsMCA_ge_spike` with `t = 2`), the in-tree two-window construction.  At radius `1/n` its
  size hypothesis `(1 - 1/n)·n ≤ n - 2 + 1` is an equality, and `n ≥ k + 3`, `2 ≤ q` discharge
  the remaining hypotheses.  This realizes the research note's *two-window plant* and is even
  cleaner than the note's stated `q ≥ 2n` threshold (`2 ≤ q` suffices).

## Main results

* `j1FullTopQuadratic_natDegree_le_two` — the QUAD eliminant has degree `≤ 2`.
* `j1RatioConstraintBadScalars_card_le_two_via_quadratic` — the resultant-route finite cap.
* `mcaBadCount_j1_le_two_via_quadratic` — the radius-`1/n` bad-count cap via the resultant.
* `epsMCA_interiorJ1_le` — `ε_mca(C, 1/n) ≤ 2/q` (upper bound; SILVER).
* `epsMCA_interiorJ1_ge` — `2/q ≤ ε_mca(C, 1/n)` (lower bound; spike plant).
* `epsMCA_interiorJ1_eq` — `ε_mca(C, 1/n) = 2/q` (GOLD).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

namespace GrandChallengesLattice

open Polynomial Code ReedSolomon
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Lemma QUAD — the degree-`≤ 2` resultant and its roots

The universal quadratic eliminant `j1FullTopQuadratic domain u₀ u₁` is defined in
`GrandChallengesLattice` as `r * r − C n₁ · q · r + C n₂ · q · q − q · s`, where `q, r, s` are
the affine-in-`γ` coefficient polynomials `j1AffineCoeffPolynomial` (degree `≤ 1` each) carrying
the top three full-interpolant coefficients of `u₀, u₁`, and `n₁, n₂` are the top two nodal
coefficients (constants).  Hence it has degree `≤ 2`. -/

/-- The affine-in-`γ` coefficient polynomial `C a + C b · X` has degree `≤ 1`. -/
theorem j1AffineCoeffPolynomial_natDegree_le (a b : F) :
    (j1AffineCoeffPolynomial a b).natDegree ≤ 1 := by
  unfold j1AffineCoeffPolynomial
  compute_degree

/-- **Lemma QUAD, degree bound.**  The universal J1 eliminant `Q = j1FullTopQuadratic` is a
polynomial of degree `≤ 2` in the line scalar `γ`. -/
theorem j1FullTopQuadratic_natDegree_le_two (domain : ι ↪ F) (u₀ u₁ : ι → F) :
    (j1FullTopQuadratic domain u₀ u₁).natDegree ≤ 2 := by
  rw [j1FullTopQuadratic]
  set P₀ := Lagrange.interpolate Finset.univ (fun a => domain a) u₀
  set P₁ := Lagrange.interpolate Finset.univ (fun a => domain a) u₁
  set N := Lagrange.nodal Finset.univ (fun a => domain a)
  set q := j1AffineCoeffPolynomial (P₀.coeff (Fintype.card ι - 1)) (P₁.coeff (Fintype.card ι - 1))
  set r := j1AffineCoeffPolynomial (P₀.coeff (Fintype.card ι - 2)) (P₁.coeff (Fintype.card ι - 2))
  set s := j1AffineCoeffPolynomial (P₀.coeff (Fintype.card ι - 3)) (P₁.coeff (Fintype.card ι - 3))
  have hq : q.natDegree ≤ 1 := j1AffineCoeffPolynomial_natDegree_le _ _
  have hr : r.natDegree ≤ 1 := j1AffineCoeffPolynomial_natDegree_le _ _
  have hs : s.natDegree ≤ 1 := j1AffineCoeffPolynomial_natDegree_le _ _
  have h1 : (r * r).natDegree ≤ 2 := le_trans natDegree_mul_le (by omega)
  have h2 : (C (N.coeff (Fintype.card ι - 1)) * q * r).natDegree ≤ 2 := by
    refine le_trans natDegree_mul_le ?_
    have hcq : (C (N.coeff (Fintype.card ι - 1)) * q).natDegree ≤ 1 := by
      refine le_trans natDegree_mul_le ?_; rw [natDegree_C]; omega
    omega
  have h3 : (C (N.coeff (Fintype.card ι - 2)) * q * q).natDegree ≤ 2 := by
    refine le_trans natDegree_mul_le ?_
    have hcq : (C (N.coeff (Fintype.card ι - 2)) * q).natDegree ≤ 1 := by
      refine le_trans natDegree_mul_le ?_; rw [natDegree_C]; omega
    omega
  have h4 : (q * s).natDegree ≤ 2 := le_trans natDegree_mul_le (by omega)
  refine le_trans (natDegree_sub_le _ _) ?_
  refine max_le ?_ h4
  refine le_trans (natDegree_add_le _ _) ?_
  refine max_le ?_ h3
  exact le_trans (natDegree_sub_le _ _) (max_le h1 h2)

/-- **Lemma QUAD, root inclusion.**  When the eliminant `Q` is not the zero polynomial, every
J1-constrained scalar lies in its root multiset.  (Every constrained scalar is a root of `Q`
by `j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero`; over a field a nonzero polynomial's roots
are exactly its zeros.) -/
theorem j1RatioConstraintBadScalars_subset_quadratic_roots
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F)
    (hQ : j1FullTopQuadratic domain u₀ u₁ ≠ 0) :
    (j1RatioConstraintBadScalars domain k u₀ u₁).val ⊆
      (j1FullTopQuadratic domain u₀ u₁).roots := by
  classical
  intro γ hγ
  have hγc : j1RatioConstraint domain k u₀ u₁ γ := by
    have : γ ∈ j1RatioConstraintBadScalars domain k u₀ u₁ := hγ
    rwa [mem_j1RatioConstraintBadScalars] at this
  rw [mem_roots hQ]
  exact j1RatioConstraint_eval_j1FullTopQuadratic_eq_zero domain hk hγc

/-- **Lemma QUAD + Lemma DEGEN — the finite cap via the resultant route.**

The set of scalars cut out by the J1 window ratio constraints has at most two elements.

This is a *new proof* of `j1RatioConstraintBadScalars_card_le_two`, structured as the research
note's resultant argument:

* **non-degenerate (`Q ≠ 0`):** the constrained set injects into the root multiset of the
  degree-`≤ 2` eliminant `Q`, so its cardinality is `≤ deg Q ≤ 2`;
* **degenerate (`Q ≡ 0`):** the resultant is vacuous, and the cap is closed by the
  joint-extendability window-collision argument `not_three_j1_ratioConstraints` (Lemma DEGEN). -/
theorem j1RatioConstraintBadScalars_card_le_two_via_quadratic
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    (j1RatioConstraintBadScalars domain k u₀ u₁).card ≤ 2 := by
  classical
  by_cases hQ : j1FullTopQuadratic domain u₀ u₁ = 0
  · -- Lemma DEGEN: `Q ≡ 0`, close by window collision.
    exact j1RatioConstraintBadScalars_card_le_two domain hk u₀ u₁
  · -- Lemma QUAD: bad scalars are roots of the degree-`≤ 2` eliminant.
    refine le_trans (card_le_degree_of_subset_roots
      (j1RatioConstraintBadScalars_subset_quadratic_roots domain hk u₀ u₁ hQ)) ?_
    exact j1FullTopQuadratic_natDegree_le_two domain u₀ u₁

/-- **Radius-`1/n` bad-count cap via the resultant route.**  Every stack `(u₀, u₁)` has at most
two MCA-bad scalars at the interior lattice radius `1/n`, proved through the QUAD eliminant +
DEGEN window collision. -/
theorem mcaBadCount_j1_le_two_via_quadratic
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    mcaBadCount (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (mcaLatticePoint (Fintype.card ι)
        (⟨1, by
          have hn : 0 < Fintype.card ι := Fintype.card_pos
          omega⟩ : Fin (Fintype.card ι + 1)))
      u₀ u₁ ≤ 2 :=
  mcaBadCount_j1_le_two_of_ratioConstraint_card_le_two domain u₀ u₁
    (j1RatioConstraintBadScalars_card_le_two_via_quadratic domain hk u₀ u₁)

/-! ## The interior radius-`1/n` MCA error -/

/-- **Upper bound (SILVER): `ε_mca(C, 1/n) ≤ 2/q`.**  The exact extremal identity
`ε_mca = (⨆ u, mcaBadCount)/q` (`epsMCA_eq_iSup_mcaBadCount`) turns the per-stack resultant cap
`mcaBadCount_j1_le_two_via_quadratic` into the error bound. -/
theorem epsMCA_interiorJ1_le
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨1, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1)))
      ≤ (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  apply ENNReal.div_le_div_right
  refine iSup_le fun u => ?_
  have := mcaBadCount_j1_le_two_via_quadratic domain hk (u 0) (u 1)
  exact_mod_cast this

/-- The size hypothesis of the `2`-spike construction at radius `1/n` is an equality:
`(1 - 1/n)·n = n - 1 = n - 2 + 1` (for `1 ≤ n`). -/
theorem spike_two_size_at_interiorJ1 {n : ℕ} (hn1 : 1 ≤ n) :
    ((1 - (1 : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) ≤ ((n - 2 + 1 : ℕ) : ℝ≥0) := by
  have hnpos : 0 < n := hn1
  have hnne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  have key : ((1 - (1 : ℝ≥0) / (n : ℝ≥0)) * (n : ℝ≥0)) = (n : ℝ≥0) - 1 := by
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ hnne]
  rw [key]
  have he : (n - 2 + 1 : ℕ) = n - 1 := by omega
  rw [he, Nat.cast_sub hn1, Nat.cast_one]

/-- **Lower bound: `2/q ≤ ε_mca(C, 1/n)`.**  The explicit `2`-spike plant
(`epsMCA_ge_spike` with `t = 2`) realizes two bad scalars at radius `1/n`.  This is the research
note's two-window plant; here `2 ≤ q` and `n ≥ k + 3` suffice (cleaner than the note's `q ≥ 2n`
sufficient threshold). -/
theorem epsMCA_interiorJ1_ge
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨1, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1))) := by
  classical
  set n := Fintype.card ι with hndef
  have hn1 : 1 ≤ n := Fintype.card_pos
  have ht_n : 2 + k ≤ n := by omega
  have hδ : ((1 - mcaLatticePoint n (⟨1, by omega⟩ : Fin (n + 1))) * n : ℝ≥0)
      ≤ ((n - 2 + 1 : ℕ) : ℝ≥0) := by
    rw [mcaLatticePoint]
    simpa using spike_two_size_at_interiorJ1 (n := n) hn1
  have hspike := epsMCA_ge_spike domain k 2
    (mcaLatticePoint n (⟨1, by omega⟩ : Fin (n + 1))) ht_n hq hδ
  simpa using hspike

/-- **GOLD — the exact interior radius-`1/n` MCA error.**  For `RS[F, domain, k]` over an
`n`-point domain with `n ≥ k + 3` and `2 ≤ q`,

  `ε_mca(C, 1/n) = 2/q`.

The upper bound is the resultant cap; the lower bound is the `2`-spike plant. -/
theorem epsMCA_interiorJ1_eq
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 2 ≤ Fintype.card F) :
    epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨1, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1)))
      = (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  le_antisymm (epsMCA_interiorJ1_le domain hk) (epsMCA_interiorJ1_ge domain hk hq)

end GrandChallengesLattice

end ProximityGap
