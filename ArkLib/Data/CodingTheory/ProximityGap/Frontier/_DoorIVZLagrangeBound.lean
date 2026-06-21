/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A41_DescentAZForm
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The Lagrange bound on the non-symmetric `Z` term of the even/odd descent (#444, SEAM A, gap G1)

`Sweep_A41_DescentAZForm.lean` locked the A+Z form of the even/odd dyadic descent identity for the
list-decoding side of #444:

  `agreement(f, u) = A + Z`,  `A = #{y∈μ_N : P=Q=0}`,  `Z = #{y∈μ_N : P(y)² = y·Q(y)²}`,

and `Z_eq_card_quadform` re-expressed `Z` as the zero-count of the explicit quadratic form
`R(y) := P(y)² − y·Q(y)²` over the base. Its docstring names the load-bearing consequence:

> "When the word is **low-weight** (`u_e, u_o` Laurent polynomials of bounded degree), `R` is a
>  genuine low-degree polynomial and `Z ≤ deg R` is a Lagrange bound."

That `Z ≤ deg R` rung was stated as PROSE but never locked as a Lean theorem. This file lands it,
honestly, for the POLYNOMIAL form of the non-symmetric term: when `P, Q` are given by polynomials
`Pp, Qp : F[X]` and `R := Pp² − X·Qp²` is the explicit quadratic-form polynomial, the descent
`Z`-count `#{y∈B : Pp.eval y ^ 2 = y · Qp.eval y ^ 2}` is bounded by `R.natDegree` whenever `R ≠ 0`.

This is the exact Lagrange (`Polynomial.card_roots'`) handle: the non-symmetric single-fibre
correction is degree-controlled, so a low-weight word (bounded `deg Pp, deg Qp`) contributes a
degree-bounded `Z`. This is the rigorous backbone of G1's "the worst word's exponent governs the
list" — the exponent enters only through `deg R = 2·max(deg Pp, deg Qp) + 1` (the mid-exponent
`≈ n/4` maximiser), with NO Gauss-sum equidistribution and NO sup-norm.

PROBE BACKING (probe-first, per the honesty contract — `scripts/probes/probe_444_g1_*`):
* The A+Z descent identity reproduces EXACTLY on random `(f,u)` over proper `μ_n`, `p ≫ n³`.
* The non-symmetric `Z`-count `R = #roots_{μ_N}(P²−yQ²)` scales as `~ N/2 = n/4` at the worst
  weight-2 word — i.e. LINEAR, consistent with the degree bound `deg R ≈ n`, NOT a constant
  collapse (the naive "subgroup-root is `O(1)`" hope is refuted; the honest control is `deg R`).
* The single-fibre correction `S₁` is `0` in the beyond-Johnson window and globally `≤ 1`, so the
  window agreement is double-root-dominated; the degree bound `Z ≤ deg R` is the exact non-vacuous
  handle on the non-symmetric part.

SCOPE / honesty: this is the polynomial Lagrange bound on the descent `Z`-term — a degree-control
lemma, NOT a CORE/cancellation/completion/moment/anti-concentration/capacity claim, and NOT a
closure of G1 (G1 also needs the worst-word exponent dichotomy + the over-`log n`-levels uniform
branching). It locks the one prose rung A41 left open. CORE OPEN.

Axiom-clean: field arithmetic + `Polynomial.card_roots'` (the same idiom as
`ProofSystem/Whir/SchwartzZippelCore.card_listEval_eq_le`). No `sorry`, no extra axioms.
-/

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset Polynomial

variable {F : Type*} [Field F]

/-- The explicit non-symmetric quadratic-form polynomial of the even/odd descent:
`R = Pp² − X·Qp²`. Its zero set over a base `B ⊆ μ_N` is exactly the descent `Z`-count, and its
`natDegree` Lagrange-bounds that count. -/
noncomputable def descentQuadform (Pp Qp : F[X]) : F[X] := Pp ^ 2 - X * Qp ^ 2

/-- Evaluating the descent quadform at `y` gives the per-fibre quadratic-form value
`P(y)² − y·Q(y)²` (`P = Pp.eval y`, `Q = Qp.eval y`). -/
@[simp] theorem descentQuadform_eval (Pp Qp : F[X]) (y : F) :
    (descentQuadform Pp Qp).eval y = (Pp.eval y) ^ 2 - y * (Qp.eval y) ^ 2 := by
  simp [descentQuadform, eval_sub, eval_pow, eval_mul, eval_X]

variable [DecidableEq F]

/-- **The descent `Z`-set is contained in the roots of the quadform `R = Pp² − X·Qp²`.**
A base point `y ∈ B` on which the polynomial single-fibre condition `Pp(y)² = y·Qp(y)²` holds is a
root of `R`, provided `R ≠ 0`. -/
theorem descentZ_subset_roots {Pp Qp : F[X]} (hR : descentQuadform Pp Qp ≠ 0) (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2))
      ⊆ (descentQuadform Pp Qp).roots.toFinset := by
  intro y hy
  rw [Finset.mem_filter] at hy
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hR, Polynomial.IsRoot, descentQuadform_eval,
    sub_eq_zero]
  exact hy.2

/-- **The Lagrange bound on the non-symmetric descent term `Z` (the open prose rung of A41).**
For polynomial parts `Pp, Qp` with nonzero quadform `R = Pp² − X·Qp²`, the descent `Z`-count
`#{y∈B : Pp(y)² = y·Qp(y)²}` is at most `R.natDegree`. Hence a low-weight word — bounded
`deg Pp, deg Qp` — contributes a degree-bounded non-symmetric single-fibre count. This is the exact
Lagrange (`card_roots'`) handle the descent identity's `Z`-term sits on. -/
theorem descentZ_card_le_natDegree {Pp Qp : F[X]} (hR : descentQuadform Pp Qp ≠ 0) (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ (descentQuadform Pp Qp).natDegree := by
  calc (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ (descentQuadform Pp Qp).roots.toFinset.card :=
        Finset.card_le_card (descentZ_subset_roots hR B)
    _ ≤ Multiset.card (descentQuadform Pp Qp).roots := Multiset.toFinset_card_le _
    _ ≤ (descentQuadform Pp Qp).natDegree := Polynomial.card_roots' _

/-- **The descent `Z`-term equals the quadform root count and is Lagrange-bounded** (consumer form,
bridging `Sweep_A41.Z_eq_card_quadform`'s shape `Pf(y)² − ρy²·Qf(y)²` here specialized to the base
itself, `ρ y² = y`). Combining: the descent identity's non-symmetric term `Z` is at most the degree
of the explicit quadratic-form polynomial. -/
theorem descentZ_indicator_sum_le_natDegree {Pp Qp : F[X]}
    (hR : descentQuadform Pp Qp ≠ 0) (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ (descentQuadform Pp Qp).natDegree := by
  have hsum :
      (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
        = (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card := by
    rw [Finset.card_filter]
  rw [hsum]
  exact descentZ_card_le_natDegree hR B

end ArkLib.ProximityGap.EvenOddDescent
