/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Lagrange

/-!
# The moving direction discharging `SurvivingTPrimeCoord` (#389, route 2)

The deep-stratum rank bound `deep_pair_rank_ge_m_succ` was conditional on
`SurvivingTPrimeCoord` — the existence of one `T'`-band coordinate independent
of the `T`-band.  This file proves the **moving direction** that discharges it:
take the generator `Z = ∏_{i∈T}(X − dom i)` (the vanishing polynomial of `T`).
Then `Z` vanishes on `T` (so `coreInterp dom T Z = 0`, all `T`-band coefficients
zero) while its interpolant on `T'` is nonzero and vanishes on the `j` overlap
points, putting its nonzero leading coefficient in the band `[k+1, k+m]`.

This file lands the elementary structural facts about `Z` (vanishing on `T`,
nonzero off `T`, degree `= |T|`); these are the substrate of the moving-direction
argument confirmed by `probe_surviving_coord.py`.

Honest scope: route-2 *rank* substrate; the route-2 list input (sub-Johnson
list-size wall) is the recognized open core and is untouched.
-/

open Finset Polynomial

namespace ProximityGap.DeepStratumMoving

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- The vanishing polynomial of the core `T`: `Z_T = ∏_{i∈T} (X − dom i)`. -/
noncomputable def vanishPoly (dom : Fin n ↪ F) (T : Finset (Fin n)) : F[X] :=
  ∏ i ∈ T, (X - C (dom i))

/-- `Z_T` vanishes at every node of `T`. -/
theorem vanishPoly_eval_eq_zero (dom : Fin n ↪ F) (T : Finset (Fin n))
    {i : Fin n} (hi : i ∈ T) : (vanishPoly dom T).eval (dom i) = 0 := by
  rw [vanishPoly, eval_prod]
  refine Finset.prod_eq_zero hi ?_
  rw [eval_sub, eval_X, eval_C, sub_self]

/-- `Z_T` is nonzero at any node OUTSIDE `T` (the nodes are distinct via `dom`). -/
theorem vanishPoly_eval_ne_zero (dom : Fin n ↪ F) (T : Finset (Fin n))
    {p : Fin n} (hp : p ∉ T) : (vanishPoly dom T).eval (dom p) ≠ 0 := by
  rw [vanishPoly, eval_prod, Finset.prod_ne_zero_iff]
  intro i hi
  rw [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro h
  exact absurd hi (dom.injective h ▸ hp)

/-- `Z_T` has degree exactly `|T|`. -/
theorem vanishPoly_natDegree (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    (vanishPoly dom T).natDegree = T.card := by
  rw [vanishPoly, Polynomial.natDegree_prod _ _
    (fun i _ => Polynomial.X_sub_C_ne_zero (dom i))]
  rw [Finset.sum_congr rfl (fun i _ => Polynomial.natDegree_X_sub_C (dom i))]
  rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- **The `T`-interpolant of `Z_T` is zero.**  `coreInterp dom T Z_T = 0` —
all `T`-band coefficients vanish (the `T`-band of the moving direction is zero). -/
theorem interp_T_vanishPoly_eq_zero (dom : Fin n ↪ F) (T : Finset (Fin n)) :
    Lagrange.interpolate T (⇑dom) (fun i => (vanishPoly dom T).eval (dom i)) = 0 := by
  have hinj : Set.InjOn (⇑dom) T := fun a _ b _ h => dom.injective h
  refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
    (s := T.image (fun i => dom i)) ?_ ?_
  · have hcard : (T.image (fun i => dom i)).card = T.card :=
      Finset.card_image_of_injective _ dom.injective
    rw [hcard]
    exact Lagrange.degree_interpolate_lt _ hinj
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Lagrange.eval_interpolate_at_node _ hinj hi]
    exact vanishPoly_eval_eq_zero dom T hi

/-- **The `T'`-interpolant of `Z_T` vanishes on the overlap `T ∩ T'`.**  Together
with its nonzero value off `T`, this confines its degree to `[|T∩T'|, |T'|−1]` —
the band `[k+1, k+m]` on the deep stratum. -/
theorem interp_Tp_vanishPoly_eval_overlap (dom : Fin n ↪ F) (T T' : Finset (Fin n))
    {i : Fin n} (hi : i ∈ T') (hiT : i ∈ T) :
    (Lagrange.interpolate T' (⇑dom)
      (fun i => (vanishPoly dom T).eval (dom i))).eval (dom i) = 0 := by
  have hinj : Set.InjOn (⇑dom) T' := fun a _ b _ h => dom.injective h
  rw [Lagrange.eval_interpolate_at_node _ hinj hi]
  exact vanishPoly_eval_eq_zero dom T hiT

/-- **The `T'`-interpolant of `Z_T` is nonzero** when `T'` has a node outside `T`
(true on the deep stratum, where `|T'∖T| = (k+m+1) − |T∩T'| ≥ 1`): it takes the
nonzero value `Z_T(dom p) ≠ 0` at such a node `p`. -/
theorem interp_Tp_vanishPoly_ne_zero (dom : Fin n ↪ F) (T T' : Finset (Fin n))
    {p : Fin n} (hpT' : p ∈ T') (hpT : p ∉ T) :
    Lagrange.interpolate T' (⇑dom) (fun i => (vanishPoly dom T).eval (dom i)) ≠ 0 := by
  have hinj : Set.InjOn (⇑dom) T' := fun a _ b _ h => dom.injective h
  intro hzero
  have hval : (Lagrange.interpolate T' (⇑dom)
      (fun i => (vanishPoly dom T).eval (dom i))).eval (dom p) = 0 := by
    rw [hzero, Polynomial.eval_zero]
  rw [Lagrange.eval_interpolate_at_node _ hinj hpT'] at hval
  exact vanishPoly_eval_ne_zero dom T hpT hval

end ProximityGap.DeepStratumMoving

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeepStratumMoving.vanishPoly_eval_eq_zero
#print axioms ProximityGap.DeepStratumMoving.vanishPoly_eval_ne_zero
#print axioms ProximityGap.DeepStratumMoving.vanishPoly_natDegree
#print axioms ProximityGap.DeepStratumMoving.interp_T_vanishPoly_eq_zero
#print axioms ProximityGap.DeepStratumMoving.interp_Tp_vanishPoly_eval_overlap
#print axioms ProximityGap.DeepStratumMoving.interp_Tp_vanishPoly_ne_zero
