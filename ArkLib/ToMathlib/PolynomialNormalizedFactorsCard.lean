/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Distinct-irreducible-factor count over a field

For a polynomial `p : K[X]` over a *field* `K`, the number of DISTINCT irreducible factors of `p`
is at most `p.natDegree`.

Unlike the in-tree `F[Z][X]` count
`pg_card_normalizedFactors_toFinset_le_natDegree` (in `BCIKS20.ListDecoding.Extraction`), which
needs `p.Separable` because the coefficient ring `F[Z]` is *not* a field and admits constant-in-`X`
irreducible factors of `X`-degree `0`, the field-base statement needs **no separability
hypothesis**: every irreducible factor of a polynomial over a field is non-constant
(`Irreducible.natDegree_pos`), so the number of distinct factors is bounded by the total degree.

This is the function-field analogue (`K = F(Z)`) of the list-size degree bound used in
Guruswami–Sudan extraction: the distinct irreducible factors of the interpolant over `K` index the
candidate messages, and their number is `≤ deg_Y` of the interpolant. It supplies the shape of the
`hYbound : Index.card ≤ ℓ` field of `Hab25JohnsonAlgebraicData` (issue #68) for any GS factorisation
carried out over a field rather than over `F[Z]`.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] [NormalizationMonoid K] [DecidableEq K]

/-- Over a field, the number of DISTINCT irreducible factors of a polynomial `p : K[X]` is at most
`p.natDegree`. No separability hypothesis: each irreducible factor has positive degree because
non-units over a field are non-constant. -/
theorem card_normalizedFactors_toFinset_le_natDegree (p : K[X]) :
    (normalizedFactors p).toFinset.card ≤ p.natDegree := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine (Multiset.toFinset_card_le _).trans ?_
  have hzero : (0 : K[X]) ∉ normalizedFactors p := zero_notMem_normalizedFactors p
  have hsum : ((normalizedFactors p).map natDegree).sum = p.natDegree := by
    have h1 : (normalizedFactors p).prod.natDegree = ((normalizedFactors p).map natDegree).sum :=
      natDegree_multiset_prod (normalizedFactors p) hzero
    have h2 : (normalizedFactors p).prod.natDegree = p.natDegree :=
      natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hp))
    rw [← h1, h2]
  have hmem : ∀ x ∈ (normalizedFactors p).map natDegree, 1 ≤ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hx
    exact (irreducible_of_normalized_factor q hq).natDegree_pos
  have key := Multiset.card_nsmul_le_sum hmem
  simp only [Multiset.card_map, smul_eq_mul, mul_one, hsum] at key
  exact key

end Polynomial

#print axioms Polynomial.card_normalizedFactors_toFinset_le_natDegree
