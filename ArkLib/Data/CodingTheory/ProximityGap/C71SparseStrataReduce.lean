/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Group.Basic
import ArkLib.Data.CodingTheory.ProximityGap.C71SparseStrataIncidence

/-!
# Conjecture 7.1 residual: the THINNESS-ESSENTIAL exponent-reduction of the `m`-sparse strata
incidence (#444)

## Context
`C71SparseStrataIncidence.munRoot_card_le_gcd_natDegree` (`4c5a3a27a`) bounds the `μ_n`-incidence
of an *arbitrary* direction polynomial `g` by `deg gcd(X^n - 1, g)`. That bound is correct but
the gcd is an abstract object, and in the prize regime the direction polynomial's exponents range up
to `q - 1 ≫ n` (the far-line / sparse-strata directions live at high degree). This file supplies the
missing **thinness-essential** preprocessing step:

> Over `μ_n` every `x` satisfies `x ^ n = 1`, so `x ^ e = x ^ (e % n)`
> (`Mathlib.pow_eq_pow_mod`). Hence an `m`-sparse direction `Σ_i c_i X^(e_i)` has the
> **same** `μ_n`-incidence as its **mod-`n` reduction** `Σ_i c_i X^(e_i % n)`, a polynomial
> of degree `< n`.

This is what makes the incidence count *usable*: it collapses the unbounded-degree far-line
direction onto a `deg < n` polynomial **without changing the count**, and it genuinely uses
`x ^ n = 1` (rule-3 thinness-essential -- the reduction is FALSE off `μ_n`).

## What this file supplies
- `sparsePoly` / `sparsePolyReduce` : the explicit `m`-sparse direction `Σ_{i∈t} C (c i) * X^(e i)`
  and its mod-`n` reduction `Σ_{i∈t} C (c i) * X^(e i % n)`.
- `sparsePoly_eval_eq_reduce_of_pow` (CORE) : the two evaluate **equally** at any `x` with
  `x ^ n = 1`.
- `munRoot_sparse_iff_reduce` : the `μ_n`-root predicates of the two coincide on the nonzero domain.
- `sparse_munRoot_card_le_reduce_gcd` : the headline `μ_n`-incidence bound applied to the
  **reduced** polynomial -- `#{x∈S : x≠0 ∧ (sparsePoly).IsRoot x} ≤ deg gcd(X^n-1, reduce)`.
- `sparse_munRoot_card_eq_zero_of_reduce_gcd_eq_one` : the exact empty-stratum corollary -- if the
  reduced direction is coprime to `X^n - 1`, then the sparse direction has **no** nonzero `μ_n` roots.
- `sparsePolyReduce_natDegree_lt` : the reduced direction has degree `< n` when `0 < n`
  (the explicit `< n` cap the abstract gcd lacked), so the incidence is `< n`.

## Probe
`scripts/probes/probe_c71_gcd_reduced_window.py` (reproducible; PROPER thin `μ_n = 2^a`,
`p ≡ 1 mod n` incl `p > n^3` + Fermat, NEVER `n = q-1`, exact `GF(p)[X]` gcds): the reduction
`deg gcd(X^n-1, g) = deg gcd(X^n-1, gbar)` holds `1080/1080`; the reduced support window
`deg gcd(gbar) ≤ rtop - rbot` holds `1080/1080`; and the reduced window is STRICTLY smaller
than the raw window in `1025/1080` (the high-degree wrap-around far-line directions where the
reduction bites).

## Honest scope (rules 1,3,4,6)
This is the exponent-reduction PREPROCESSING for the sparse-strata incidence COUNT only. The
reduction of the strata-incidence to a FRI **soundness** bound (the actual Conjecture-7.1
content) remains OPEN and is NOT claimed. This is NOT a CORE / Conj-7.1 closure. No capacity /
cliff-at-n/2 / beyond-Johnson claim (ASYMPTOTIC GUARD).

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.C71SparseStrataReduce

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [DecidableEq ι]

/-- An explicit `m`-sparse direction polynomial `Σ_{i ∈ t} C (c i) * X ^ (e i)`. -/
noncomputable def sparsePoly (t : Finset ι) (c : ι → F) (e : ι → ℕ) : F[X] :=
  ∑ i ∈ t, C (c i) * X ^ (e i)

/-- Its mod-`n` reduction `Σ_{i ∈ t} C (c i) * X ^ (e i % n)` (degree `< n`). -/
noncomputable def sparsePolyReduce (n : ℕ) (t : Finset ι) (c : ι → F) (e : ι → ℕ) : F[X] :=
  ∑ i ∈ t, C (c i) * X ^ (e i % n)

/-- **The thinness-essential evaluation identity.** At any `x` with `x ^ n = 1` the sparse direction
and its mod-`n` reduction evaluate to the *same* value: each monomial `c_i x^(e_i)` equals
`c_i x^(e_i % n)` by `pow_eq_pow_mod`. (FALSE off `μ_n`: the reduction needs `x ^ n = 1`.) -/
theorem sparsePoly_eval_eq_reduce_of_pow {n : ℕ} (t : Finset ι) (c : ι → F) (e : ι → ℕ)
    {x : F} (hx : x ^ n = 1) :
    (sparsePoly t c e).eval x = (sparsePolyReduce n t c e).eval x := by
  unfold sparsePoly sparsePolyReduce
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [pow_eq_pow_mod (e i) hx]

/-- **The `μ_n`-root predicate is invariant under mod-`n` exponent reduction.** On any `x` with
`x ^ n = 1`, `x` is a root of the sparse direction iff it is a root of its reduction. -/
theorem munRoot_sparse_iff_reduce {n : ℕ} (t : Finset ι) (c : ι → F) (e : ι → ℕ)
    {x : F} (hx : x ^ n = 1) :
    (sparsePoly t c e).IsRoot x ↔ (sparsePolyReduce n t c e).IsRoot x := by
  unfold Polynomial.IsRoot
  rw [sparsePoly_eval_eq_reduce_of_pow t c e hx]

/-- **The reduced direction has degree `< n`** (when `0 < n`): every exponent `e i % n < n`, so the
sum of monomials `C (c i) * X ^ (e i % n)` has degree `< n`. The explicit cap the abstract
`deg gcd(X^n-1, ·)` did not expose. -/
theorem sparsePolyReduce_natDegree_lt {n : ℕ} (hn : 0 < n) (t : Finset ι) (c : ι → F) (e : ι → ℕ) :
    (sparsePolyReduce n t c e).natDegree < n := by
  refine (natDegree_sum_le _ _).trans_lt ((Finset.fold_max_lt _).mpr ⟨hn, ?_⟩)
  intro i _
  calc (C (c i) * X ^ (e i % n)).natDegree
      ≤ (X ^ (e i % n)).natDegree := natDegree_C_mul_le _ _
    _ ≤ e i % n := natDegree_X_pow_le (e i % n)
    _ < n := Nat.mod_lt _ hn

/-- **Headline: the sparse-strata `μ_n`-incidence, computed on the REDUCED direction.** For any
finite `S ⊆ F` with `∀ x ∈ S, x ^ n = 1` (i.e. `S ⊆ μ_n`), the count of nonzero points of `S` that
are roots of the sparse direction is at most `deg gcd(X^n - 1, sparsePolyReduce)`. Applying the
uniform `munRoot_card_le_gcd_natDegree` to the reduced (degree `< n`) polynomial after rewriting
the predicate via `munRoot_sparse_iff_reduce`. Requires the reduced polynomial be nonzero. -/
theorem sparse_munRoot_card_le_reduce_gcd {n : ℕ} (S : Finset F) (t : Finset ι) (c : ι → F)
    (e : ι → ℕ) (hg : sparsePolyReduce n t c e ≠ 0) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ (sparsePoly t c e).IsRoot x)).card
      ≤ (gcd (X ^ n - 1 : F[X]) (sparsePolyReduce n t c e)).natDegree := by
  have hfilter : (S.filter (fun x => x ≠ 0 ∧ (sparsePoly t c e).IsRoot x))
      = (S.filter (fun x => x ≠ 0 ∧ (sparsePolyReduce n t c e).IsRoot x)) := by
    apply Finset.filter_congr
    intro x hxS
    constructor
    · rintro ⟨hxne, hr⟩
      exact ⟨hxne, (munRoot_sparse_iff_reduce t c e (hSn x hxS)).mp hr⟩
    · rintro ⟨hxne, hr⟩
      exact ⟨hxne, (munRoot_sparse_iff_reduce t c e (hSn x hxS)).mpr hr⟩
  rw [hfilter]
  exact ArkLib.ProximityGap.C71SparseStrataIncidence.munRoot_card_le_gcd_natDegree S hg hSn

/-- **The punchline usable cap: the sparse-strata `μ_n`-incidence is `< n`.** Composing the headline
gcd bound with `deg gcd(X^n-1, reduce) ≤ deg reduce < n` (the gcd divides the nonzero reduced
polynomial, whose degree is `< n` by `sparsePolyReduce_natDegree_lt`). This is the explicit,
closed `< n` count the abstract `deg gcd` did not expose -- the form a soundness bridge consumes. -/
theorem sparse_munRoot_card_lt_n {n : ℕ} (hn : 0 < n) (S : Finset F) (t : Finset ι) (c : ι → F)
    (e : ι → ℕ) (hg : sparsePolyReduce n t c e ≠ 0) (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧ (sparsePoly t c e).IsRoot x)).card < n := by
  calc (S.filter (fun x => x ≠ 0 ∧ (sparsePoly t c e).IsRoot x)).card
      ≤ (gcd (X ^ n - 1 : F[X]) (sparsePolyReduce n t c e)).natDegree :=
        sparse_munRoot_card_le_reduce_gcd S t c e hg hSn
    _ ≤ (sparsePolyReduce n t c e).natDegree :=
        Polynomial.natDegree_le_of_dvd (gcd_dvd_right _ _) hg
    _ < n := sparsePolyReduce_natDegree_lt hn t c e

/-- **Exact empty sparse stratum under reduced coprimality.** If the mod-`n` reduced sparse
direction is coprime to `X^n - 1`, then the original high-exponent sparse direction has no nonzero
roots on `S ⊆ μ_n`. This is the exact zero-incidence consuming form of the C71 sparse-strata gcd
bound: exponent reduction first collapses the direction to degree `< n`, then `gcd = 1` leaves zero
common roots. -/
theorem sparse_munRoot_card_eq_zero_of_reduce_gcd_eq_one {n : ℕ} (S : Finset F) (t : Finset ι)
    (c : ι → F) (e : ι → ℕ) (hg : sparsePolyReduce n t c e ≠ 0) (hSn : ∀ x ∈ S, x ^ n = 1)
    (hcop : gcd (X ^ n - 1 : F[X]) (sparsePolyReduce n t c e) = 1) :
    (S.filter (fun x => x ≠ 0 ∧ (sparsePoly t c e).IsRoot x)).card = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc (S.filter (fun x => x ≠ 0 ∧ (sparsePoly t c e).IsRoot x)).card
      ≤ (gcd (X ^ n - 1 : F[X]) (sparsePolyReduce n t c e)).natDegree :=
        sparse_munRoot_card_le_reduce_gcd S t c e hg hSn
    _ = 0 := by simp [hcop]

end ArkLib.ProximityGap.C71SparseStrataReduce

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71SparseStrataReduce.sparsePoly_eval_eq_reduce_of_pow
#print axioms ArkLib.ProximityGap.C71SparseStrataReduce.munRoot_sparse_iff_reduce
#print axioms ArkLib.ProximityGap.C71SparseStrataReduce.sparsePolyReduce_natDegree_lt
#print axioms ArkLib.ProximityGap.C71SparseStrataReduce.sparse_munRoot_card_le_reduce_gcd
#print axioms ArkLib.ProximityGap.C71SparseStrataReduce.sparse_munRoot_card_lt_n
#print axioms ArkLib.ProximityGap.C71SparseStrataReduce.sparse_munRoot_card_eq_zero_of_reduce_gcd_eq_one
