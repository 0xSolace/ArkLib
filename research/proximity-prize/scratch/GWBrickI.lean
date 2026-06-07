/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.ToMathlib.SiegelInterpolation

/-!
# BRICK-I: the Guruswami–Wang interpolation-existence skeleton (issue #93)

This scratch file delivers **BRICK-I** of the GW `|L| > 1` kernel
(`CZ25CoordFiberCap` / `CZ25DimensionCount`): the existence of a **nonzero**
interpolating polynomial that is **linear in the `Y`-block** and of **bounded
coefficient degree**, vanishing on the agreement set.

## The GW interpolant shape

The Guruswami–Wang (2013) / CZ25 folded-RS list-decoder interpolates a
polynomial

  `Q(X, Y₁, …, Y_s) = A₀(X) + ∑_{j=1}^{s} A_j(X) · Y_j`

that is **affine-linear in the `Y`-block** `(Y₁,…,Y_s)`, with the coefficient
polynomials of **bounded degree**

  `deg A₀ < n + k`,    `deg A_j < n`   (`j = 1,…,s`).

The list-decoder substitutes the folded codeword coordinates
`Y_j ↦ p(γ^{j-1} X)` and asks `Q` to vanish on the `n` agreement evaluation
points.  BRICK-I is the **linear-algebra existence** of such a nonzero `Q`:
the number of free coefficients

  `#unknowns = (n + k) + s · n`

strictly exceeds the number of homogeneous linear **agreement constraints**

  `#constraints = n`,

so the constraint map between the (finite-dimensional) coefficient space and
the constraint space has a nontrivial kernel (a nonzero `Q`).  This is the
classic *more-unknowns-than-constraints* Siegel/pigeonhole count, here packaged
by the already-proven `ArkLib.siegel_exists_nonzero` /
`ArkLib.exists_nonzero_constraint_solution` (in
`ArkLib/ToMathlib/SiegelInterpolation.lean`).

## What is proven here, and what stays a named residual

* `GWCoeffSpace` — the concrete coefficient space of a `Y`-linear interpolant
  with the bounded-degree blocks: a Pi-type over the disjoint union of the
  monomial index sets, whose `Fintype.card` is exactly `(n + k) + s · n`.
* `gwInterpolantToPoly` — assembling a coefficient vector into the actual
  bivariate-block polynomial `Q = A₀ + ∑ A_j Y_j` of `Polynomial`s
  (`Fin (s+1) → F[X]`), the honest `Y`-linear object with the degree blocks.
* `gw_unknowns_gt_constraints` — the **strict count** `n < (n+k) + s·n` from
  `0 < n` (and the trivial `s·n ≥ 0`, `k ≥ 0`), i.e. unknowns exceed
  constraints.  This is the combinatorial heart that powers the Siegel step.
* `gw_interpolant_exists` — **BRICK-I.**  For any constraint matrix
  `agree : Fin n → GWCoeffSpace → F` (an arbitrary `F`-linear agreement
  functional indexed by the `n` evaluation points), there is a **nonzero**
  coefficient vector satisfying every agreement constraint
  `∑ i, c i · agree j i = 0`.  Built directly on
  `ArkLib.exists_nonzero_constraint_solution` under the proven strict count.
* `gw_interpolant_exists_poly` — the same existence packaged as an actual
  nonzero `Y`-linear polynomial tuple `A : Fin (s+1) → F[X]` with the stated
  degree blocks, satisfying the agreement constraints expressed through the
  coefficient coordinates.

* `GWFoldedDegreeObligation` — the **named genuine residual** (BRICK-I's
  irreducible analytic bookkeeping).  Relating the degree of the *folded
  substitution* `R_p(X) := Q(X, p(X), p(γX), …, p(γ^{s-1} X))` to the agreement
  count is **not** linear-algebra: one must show `deg R_p < (#agreement points)`
  so that an agreement-with-multiplicity forces `R_p ≡ 0` (this hands off to
  BRICK-V).  This file isolates that obligation as an explicit `Prop`
  hypothesis and proves everything else around it.

## References

* [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon
  codes.*  IEEE Trans. IT 59(5), 2013.
* [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
* `ArkLib/ToMathlib/SiegelInterpolation.lean` — the reusable Siegel core.
* `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean`
  (`modified_guruswami_has_a_solution`) — the analogous GS-interpolant existence,
  proven by the same nonzero-kernel count (`exists_nonzero_triSolution`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory.GWBrickI

open Polynomial

/-! ## 1. The coefficient space of a `Y`-linear interpolant -/

/-- The **monomial index** of a `Y`-linear GW interpolant of inner block size
`s`, base degree `k`, and code length `n`.  An interpolant
`Q = A₀ + ∑_{j} A_j Y_j` is determined by:

* the `n + k` coefficients of `A₀` (degrees `0 ≤ a < n + k`), and
* for each of the `s` inner indices `j`, the `n` coefficients of `A_j`
  (degrees `0 ≤ a < n`).

`GWMonomialIndex s n k` is the disjoint union of these blocks; its cardinality
is exactly `(n + k) + s · n`, the number of free unknowns. -/
abbrev GWMonomialIndex (s n k : ℕ) : Type :=
  Fin (n + k) ⊕ (Fin s × Fin n)

/-- The **coefficient space** of a `Y`-linear GW interpolant: a function from the
monomial index to the field, i.e. one scalar per free coefficient. -/
abbrev GWCoeffSpace (F : Type*) [Field F] (s n k : ℕ) : Type _ :=
  GWMonomialIndex s n k → F

/-- The number of unknowns of a `Y`-linear GW interpolant is exactly
`(n + k) + s · n`. -/
lemma card_gwMonomialIndex (s n k : ℕ) :
    Fintype.card (GWMonomialIndex s n k) = (n + k) + s * n := by
  simp [GWMonomialIndex, Fintype.card_sum, Fintype.card_prod]

/-! ## 2. The strict unknowns-vs-constraints count -/

/-- **The strict count powering BRICK-I.**  With `n` agreement constraints (one
per evaluation point) and `(n + k) + s · n` free coefficients, the unknowns
strictly exceed the constraints whenever the base-degree slack is positive
(`0 < k`): `(n + k) + s·n = n + (k + s·n) > n` because the extra `A₀`-degree
block of width `k` is already strictly positive.  (The slack `k` is exactly the
`+ k` in the GW degree budget `deg A₀ < n + k`; this is the structural counting
gap, the analogue of `numVars_gt_numConstraints` in the GS development.)  This
is the combinatorial pigeonhole that guarantees a nonzero interpolant. -/
lemma gw_unknowns_gt_constraints {s n k : ℕ} (hk : 0 < k) :
    n < Fintype.card (GWMonomialIndex s n k) := by
  rw [card_gwMonomialIndex]
  omega

/-! ## 3. BRICK-I: existence of a nonzero interpolant (coefficient form) -/

/-- **BRICK-I (coefficient form).**  *More unknowns than constraints ⟹ a nonzero
interpolant.*

Let `agree : Fin n → GWMonomialIndex s n k → F` be the agreement-constraint
matrix: for each evaluation point `j : Fin n` and each free coefficient `i`,
`agree j i` is that coefficient's contribution to the value of the folded
substitution at the `j`-th point.  The interpolation constraint at point `j` is
the homogeneous linear equation `∑ i, c i · agree j i = 0`.  Because the number
of free coefficients `(n + k) + s·n` strictly exceeds the `n` constraints
(`gw_unknowns_gt_constraints`, using the base-degree slack `0 < k`), there is a
**nonzero** coefficient vector `c : GWCoeffSpace F s n k` satisfying every
agreement constraint.

This is the GW analogue of `modified_guruswami_has_a_solution`'s nonzero-kernel
step, discharged here directly by the reusable Siegel core
`ArkLib.exists_nonzero_constraint_solution`. -/
theorem gw_interpolant_exists {F : Type*} [Field F] {s n k : ℕ} (hk : 0 < k)
    (agree : Fin n → GWMonomialIndex s n k → F) :
    ∃ c : GWCoeffSpace F s n k, c ≠ 0 ∧
      ∀ j : Fin n, ∑ i : GWMonomialIndex s n k, c i * agree j i = 0 := by
  classical
  -- `a : C → M → F` is the constraint matrix; `C = Fin n`, `M = GWMonomialIndex`.
  have hcount : Fintype.card (Fin n) < Fintype.card (GWMonomialIndex s n k) := by
    simpa [Fintype.card_fin] using gw_unknowns_gt_constraints (s := s) (k := k) hk
  obtain ⟨c, hc0, hc⟩ :=
    ArkLib.exists_nonzero_constraint_solution
      (K := F) (M := GWMonomialIndex s n k) (C := Fin n)
      agree hcount
  exact ⟨c, hc0, hc⟩

/-! ## 4. The honest `Y`-linear polynomial object with the degree blocks -/

/-- Assemble a coefficient vector into the **coefficient polynomial block**
`A : Fin (s+1) → F[X]` of the `Y`-linear GW interpolant
`Q = A₀ + ∑_{j} A_j Y_j`:

* `A 0 = A₀` collects the `Fin (n + k)` block (degrees `< n + k`);
* `A (j+1) = A_j` collects the `(j, ·)` slice of the `Fin s × Fin n` block
  (degrees `< n`).

The `Y`-linearity is structural: the data is *exactly* `s + 1` univariate
polynomials, one constant block `A₀` and one block `A_j` per inner index. -/
noncomputable def gwInterpolantBlocks {F : Type*} [Field F] {s n k : ℕ}
    (c : GWCoeffSpace F s n k) : Fin (s + 1) → F[X] :=
  fun b =>
    if hb : b = 0 then
      ∑ a : Fin (n + k), Polynomial.C (c (Sum.inl a)) * X ^ (a : ℕ)
    else
      have hb' : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      let j : Fin s := ⟨(b : ℕ) - 1, by omega⟩
      ∑ a : Fin n, Polynomial.C (c (Sum.inr (j, a))) * X ^ (a : ℕ)

/-- **Degree block for `A₀`.**  The assembled `A₀` has degree `< n + k`
(`natDegree`-form), realising the GW coefficient-degree budget for the
constant block. -/
lemma natDegree_gwBlock_zero {F : Type*} [Field F] {s n k : ℕ}
    (hnk : 0 < n + k) (c : GWCoeffSpace F s n k) :
    (gwInterpolantBlocks c 0).natDegree < n + k := by
  classical
  have hexpand : gwInterpolantBlocks c 0
      = ∑ a : Fin (n + k), Polynomial.C (c (Sum.inl a)) * X ^ (a : ℕ) := by
    simp [gwInterpolantBlocks]
  have hle : (gwInterpolantBlocks c 0).natDegree ≤ n + k - 1 := by
    rw [hexpand]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    calc (Polynomial.C (c (Sum.inl a)) * X ^ (a : ℕ)).natDegree
        ≤ (a : ℕ) := by
          refine le_trans (Polynomial.natDegree_mul_le) ?_
          simp [Polynomial.natDegree_C]
      _ ≤ n + k - 1 := by have := a.isLt; omega
  omega

/-- **Degree block for `A_j`, `j ≥ 1`.**  Each inner block `A_j` has degree
`< n`, realising the GW coefficient-degree budget for the inner blocks. -/
lemma natDegree_gwBlock_succ {F : Type*} [Field F] {s n k : ℕ}
    (hn : 0 < n) (c : GWCoeffSpace F s n k) {b : Fin (s + 1)} (hb : b ≠ 0) :
    (gwInterpolantBlocks c b).natDegree < n := by
  classical
  have hb' : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
  have hjlt : (b : ℕ) - 1 < s := by have := b.isLt; omega
  have hexpand : gwInterpolantBlocks c b
      = ∑ a : Fin n,
          Polynomial.C (c (Sum.inr ((⟨(b : ℕ) - 1, hjlt⟩ : Fin s), a))) * X ^ (a : ℕ) := by
    simp only [gwInterpolantBlocks, dif_neg hb]
  have hle : (gwInterpolantBlocks c b).natDegree ≤ n - 1 := by
    rw [hexpand]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro a _
    calc (Polynomial.C (c (Sum.inr (_, a))) * X ^ (a : ℕ)).natDegree
        ≤ (a : ℕ) := by
          refine le_trans (Polynomial.natDegree_mul_le) ?_
          simp [Polynomial.natDegree_C]
      _ ≤ n - 1 := by have := a.isLt; omega
  omega

/-- The `a`-th coefficient of the assembled `A₀` block is exactly `c (inl a)`. -/
lemma coeff_gwBlock_zero {F : Type*} [Field F] {s n k : ℕ}
    (c : GWCoeffSpace F s n k) (a : Fin (n + k)) :
    (gwInterpolantBlocks c 0).coeff (a : ℕ) = c (Sum.inl a) := by
  classical
  have hexpand : gwInterpolantBlocks c 0
      = ∑ a' : Fin (n + k), Polynomial.C (c (Sum.inl a')) * X ^ (a' : ℕ) := by
    simp [gwInterpolantBlocks]
  rw [hexpand, Polynomial.finset_sum_coeff, Finset.sum_eq_single a]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  · intro b _ hba
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [if_neg (by exact fun h => hba (Fin.ext h.symm))]
    ring
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The `a`-th coefficient of the assembled `A_{j+1}` block is exactly
`c (inr (j, a))`. -/
lemma coeff_gwBlock_succ {F : Type*} [Field F] {s n k : ℕ}
    (c : GWCoeffSpace F s n k) (j : Fin s) (a : Fin n) :
    (gwInterpolantBlocks c j.succ).coeff (a : ℕ) = c (Sum.inr (j, a)) := by
  classical
  have hsne : (j.succ : Fin (s + 1)) ≠ 0 := Fin.succ_ne_zero j
  have hjeq : (⟨(j.succ : ℕ) - 1, by simp [Fin.val_succ]⟩ : Fin s) = j := by
    apply Fin.ext; simp [Fin.val_succ]
  have hexpand : gwInterpolantBlocks c j.succ
      = ∑ a' : Fin n,
          Polynomial.C (c (Sum.inr ((⟨(j.succ : ℕ) - 1, by
            simp [Fin.val_succ]⟩ : Fin s), a'))) * X ^ (a' : ℕ) := by
    simp only [gwInterpolantBlocks, dif_neg hsne]
  rw [hexpand, Polynomial.finset_sum_coeff, Finset.sum_eq_single a]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one, hjeq]
  · intro b _ hba
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [if_neg (by exact fun h => hba (Fin.ext h.symm))]
    ring
  · intro h; exact absurd (Finset.mem_univ a) h

/-- A nonzero coefficient vector yields a **nonzero** block tuple: at least one
block is a nonzero polynomial.  (The coefficient-to-polynomial assembly is
injective on each block, so `c ≠ 0` forces some `A_b ≠ 0`.) -/
lemma gwInterpolantBlocks_ne_zero {F : Type*} [Field F] {s n k : ℕ}
    (c : GWCoeffSpace F s n k) (hc : c ≠ 0) :
    gwInterpolantBlocks c ≠ 0 := by
  classical
  intro hAll
  apply hc
  funext i
  have hblock : ∀ b : Fin (s + 1), gwInterpolantBlocks c b = 0 := by
    intro b; rw [hAll]; rfl
  cases i with
  | inl a =>
      have hcoeff := coeff_gwBlock_zero c a
      rw [hblock 0, Polynomial.coeff_zero] at hcoeff
      simpa using hcoeff.symm
  | inr jp =>
      obtain ⟨j, a⟩ := jp
      have hcoeff := coeff_gwBlock_succ c j a
      rw [hblock j.succ, Polynomial.coeff_zero] at hcoeff
      simpa using hcoeff.symm

/-- **BRICK-I (polynomial form).**  The same existence, packaged as an actual
nonzero `Y`-linear polynomial tuple `A : Fin (s+1) → F[X]` (the blocks of
`Q = A₀ + ∑_j A_j Y_j`) with the GW degree budget `deg A₀ < n+k`, `deg A_j < n`,
satisfying every agreement constraint (expressed through the coefficient
coordinates `c` from which the blocks are assembled). -/
theorem gw_interpolant_exists_poly {F : Type*} [Field F] {s n k : ℕ}
    (hn : 0 < n) (hk : 0 < k)
    (agree : Fin n → GWMonomialIndex s n k → F) :
    ∃ (c : GWCoeffSpace F s n k) (A : Fin (s + 1) → F[X]),
      A ≠ 0 ∧
      A = gwInterpolantBlocks c ∧
      (A 0).natDegree < n + k ∧
      (∀ b : Fin (s + 1), b ≠ 0 → (A b).natDegree < n) ∧
      (∀ j : Fin n, ∑ i : GWMonomialIndex s n k, c i * agree j i = 0) := by
  obtain ⟨c, hc0, hc⟩ := gw_interpolant_exists hk agree
  refine ⟨c, gwInterpolantBlocks c, gwInterpolantBlocks_ne_zero c hc0, rfl, ?_, ?_, hc⟩
  · exact natDegree_gwBlock_zero (by omega) c
  · intro b hb; exact natDegree_gwBlock_succ hn c hb

/-! ## 5. The named genuine residual: folded-substitution degree bookkeeping -/

/-- The **folded substitution** of a `Y`-linear interpolant.  Given the block
tuple `A : Fin (s+1) → F[X]` (so `Q = A₀ + ∑_j A_j Y_j`), the inner codeword
polynomial `p`, and the folding shifts `shift : Fin s → F[X]` (in GW,
`shift j = γ^j · X`, formalised as the substitution maps `X ↦ γ^j X`), the
**folded substitution** is the univariate

  `R_p(X) := A₀(X) + ∑_{j} A_{j+1}(X) · p(shift_j(X))`,

i.e. `Q` with `Y_{j+1} ↦ p ∘ shift_j`.  This is the polynomial whose roots are
the agreement points and whose vanishing (BRICK-V) is the GW functional
equation `R_p = 0`. -/
noncomputable def foldedSubstitution {F : Type*} [Field F] {s : ℕ}
    (A : Fin (s + 1) → F[X]) (p : F[X]) (shift : Fin s → F[X]) : F[X] :=
  A 0 + ∑ j : Fin s, (A j.succ) * (p.comp (shift j))

/-- **NAMED RESIDUAL — the folded-substitution degree obligation (BRICK-I core).**

The genuinely-analytic part of BRICK-I that is *not* the under-determined
linear-algebra count: the degree of the folded substitution `R_p` is strictly
below the number of agreement points, so that an agreement-with-multiplicity (a
codeword agreeing with the received word at `≥ deg-bound` points) forces
`R_p ≡ 0`.  Concretely, with `deg A₀ < n + k`, `deg A_j < n`, `deg p ≤ k`, and
the multiplicative folding shifts of degree `1`, the standard GW bookkeeping
gives `deg R_p < n + k + (s-1)·… `; the precise inequality that closes the
hand-off to BRICK-V (`R_p = 0` on enough agreement points ⟹ `R_p = 0`) is the
content named here.

This is exposed as a `Prop` over the interpolant data so the rest of the GW kernel
(BRICK-W, BRICK-L) can consume BRICK-I *conditionally* on this single bookkeeping
fact, exactly as the campaign reduces `CZ25CoordFiberCap` to `{BRICK-I, BRICK-V}`. -/
def GWFoldedDegreeObligation {F : Type*} [Field F] {s : ℕ}
    (A : Fin (s + 1) → F[X]) (p : F[X]) (shift : Fin s → F[X])
    (agreeCount : ℕ) : Prop :=
  (foldedSubstitution A p shift).natDegree < agreeCount

/-- **BRICK-I ⟹ vanishing folded substitution, conditional on the named
residual.**  If the folded substitution `R_p` is *not* the zero polynomial yet
its degree is below the agreement count (the named residual
`GWFoldedDegreeObligation`), and `R_p` vanishes at `agreeCount` distinct points,
then `R_p` must in fact be zero — a contradiction giving `R_p = 0`.  This is the
clean linear-algebra/degree hand-off to BRICK-V; the *only* admitted analytic
input is the named degree bookkeeping `hdeg`. -/
theorem foldedSubstitution_eq_zero_of_degree_and_roots
    {F : Type*} [Field F] {s : ℕ}
    (A : Fin (s + 1) → F[X]) (p : F[X]) (shift : Fin s → F[X])
    (agreeCount : ℕ)
    (hdeg : GWFoldedDegreeObligation A p shift agreeCount)
    (roots : Finset F) (hcard : agreeCount ≤ roots.card)
    (hroots : ∀ x ∈ roots, (foldedSubstitution A p shift).eval x = 0) :
    foldedSubstitution A p shift = 0 := by
  classical
  by_contra hne
  -- a nonzero polynomial has at most `natDegree` distinct roots
  have hsub : roots ⊆ (foldedSubstitution A p shift).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact hroots x hx
  have hle : roots.card ≤ (foldedSubstitution A p shift).roots.toFinset.card :=
    Finset.card_le_card hsub
  have hcard_roots :
      (foldedSubstitution A p shift).roots.toFinset.card
        ≤ (foldedSubstitution A p shift).natDegree := by
    refine le_trans (Multiset.toFinset_card_le _) ?_
    exact Polynomial.card_roots' _
  have hdeg' : (foldedSubstitution A p shift).natDegree < agreeCount := hdeg
  omega

end CodingTheory.GWBrickI

-- Axiom-cleanliness checks: the proven BRICK-I declarations rest only on the
-- standard Lean/mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`);
-- no `sorryAx`, no new axioms.  The folded-degree obligation is a *named Prop*,
-- not an axiom.
#print axioms CodingTheory.GWBrickI.gw_interpolant_exists
#print axioms CodingTheory.GWBrickI.gw_interpolant_exists_poly
#print axioms CodingTheory.GWBrickI.gw_unknowns_gt_constraints
#print axioms CodingTheory.GWBrickI.foldedSubstitution_eq_zero_of_degree_and_roots
