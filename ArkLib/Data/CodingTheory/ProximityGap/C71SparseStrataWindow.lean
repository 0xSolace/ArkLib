/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.C71SparseStrataReduce

/-!
# Conjecture 7.1 residual: the SUPPORT-SPAN (degree-window) incidence bound (#444)

## Context
`C71SparseStrataIncidence.munRoot_card_le_gcd_natDegree` bounds the `μ_n`-incidence of an arbitrary
direction `g` by `deg gcd(X^n - 1, g)`, and `C71SparseStrataReduce.sparse_munRoot_card_lt_n`
collapses that to the trivial `< n` cap after the thinness-essential mod-`n` reduction. Both are
correct, but
neither uses the **internal sparsity of the support**: a direction whose nonzero coefficients are
*concentrated* in a short exponent band `[t, d]` (e.g. the reduced binomial / trinomial directions,
whose reduced support spans far less than `n`) should be much weaker than a generic degree-`<n`
polynomial.

This file supplies the missing **support-span / degree-window** sharpening, a NON-orbit, char-free
polynomial-method count that is strictly tighter than the `< n` cap whenever the support is narrow:

> A direction `g` factors as `g = X^t · h` with `t = g.natTrailingDegree`, `h.eval 0 ≠ 0`, and
> `h.natDegree = g.natDegree − t`. Every **nonzero** root of `g` is a root of `h`, of which there
> are at most `deg h = g.natDegree − g.natTrailingDegree`. So
>
>   `#{ x ∈ μ_n : x ≠ 0 ∧ g(x) = 0 } ≤ g.natDegree − g.natTrailingDegree`  =  the support span.

The bound holds for **any** `g` (no `x ^ n = 1` hypothesis even needed: factoring out `X^t` is a
field identity), so it is a uniform pre-reduction count; combined with the proven mod-`n` reduction
it gives the sharp `span(reduced support)` incidence for the `m`-sparse strata.

Probe `scripts/probes/probe_c71_window_span.py` (EXACT, seeded-reproducible `719/719` over thin
`μ_n = 2^a`, multi-prime incl `p > n^3` and Fermat `257`, NEVER `n = q-1`, `m ∈ {2,3,4}`,
wrap-around supports): the window bound `#roots ≤ d − t` of the reduced support HOLDS with **zero**
failures and
is strictly `< n` in every case (sharper than the trivial cap).

## Theorems
* `card_nonzeroRoots_le_natDegree_sub_natTrailingDegree` (HEADLINE) : for any `g ≠ 0` and any finite
  `S`, the count of nonzero points of `S` at which `g` vanishes is at most
  `g.natDegree − g.natTrailingDegree` (the support span). Pure polynomial-method, no thinness
  hypothesis.
* `sparse_munRoot_card_le_window` : the `m`-sparse strata instance on the mod-`n` reduced
  direction. The `μ_n`-incidence of a sparse direction is at most the span of its reduced
  support `(reduce).natDegree − (reduce).natTrailingDegree`. By the proven incidence-invariance
  under mod-`n` reduction (`munRoot_sparse_iff_reduce`), this is the genuinely usable cap.

## Honest scope
This is the support-span polynomial-method **incidence count** sharpening for the sparse strata. The
reduction of the strata-incidence to a FRI **soundness** bound (the actual Conjecture-7.1 content)
remains OPEN and is NOT claimed here. This is NOT a CORE / Conj-7.1 closure. NON-orbit, char-free,
field-universal; the `μ_n` corollary uses `x ^ n = 1` only through the already-proven mod-`n`
reduction, exactly as honest.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.C71SparseStrataWindow

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [DecidableEq ι]

/-- **The number of distinct nonzero roots of `g` in a multiset of roots is at most the support
span `natDegree − natTrailingDegree`.** The multiplicity of `0` in `g.roots` is exactly
`g.rootMultiplicity 0 = g.natTrailingDegree`; removing those leaves at most
`card g.roots − natTrailingDegree ≤ natDegree − natTrailingDegree` nonzero roots (counted with
multiplicity, hence at least that many distinct ones). -/
theorem card_nonzero_roots_le_span (g : F[X]) :
    Multiset.card (g.roots.filter (· ≠ 0)) ≤ g.natDegree - g.natTrailingDegree := by
  -- `card (filter ≠0) = card g.roots − count 0`
  have hsplit : Multiset.card (g.roots.filter (· ≠ (0 : F)))
      = Multiset.card g.roots - g.roots.count 0 := by
    have hadd : g.roots.filter (· ≠ (0 : F)) + g.roots.filter (fun a => ¬ a ≠ (0 : F))
        = g.roots := Multiset.filter_add_not _ _
    have hcard := congrArg Multiset.card hadd
    rw [Multiset.card_add] at hcard
    -- `filter (¬ a ≠ 0) = filter (a = 0)`, whose card is `count 0`
    have hcount : Multiset.card (g.roots.filter (fun a => ¬ a ≠ (0 : F))) = g.roots.count 0 := by
      rw [Multiset.count_eq_card_filter_eq]
      apply congrArg
      apply Multiset.filter_congr
      intro a _
      constructor
      · intro h; exact (not_not.mp h).symm
      · intro h; rw [← h]; exact fun h' => h' rfl
    omega
  rw [hsplit]
  -- `count 0 = rootMultiplicity 0 = natTrailingDegree`, and `card g.roots ≤ natDegree`
  have hcount0 : g.roots.count 0 = g.natTrailingDegree := by
    rw [Polynomial.count_roots, Polynomial.rootMultiplicity_eq_natTrailingDegree']
  have hcardroots : Multiset.card g.roots ≤ g.natDegree := Polynomial.card_roots' g
  rw [hcount0]
  omega

/-- **Headline: the nonzero-root count of `g` on a finite set is at most its support span.** For any
`g ≠ 0` and any finite `S ⊆ F`, the number of nonzero points of `S` at which `g` vanishes is at most
`g.natDegree − g.natTrailingDegree`. Pure polynomial-method (factor out `X^{trailing}`); NO thinness
/ `x ^ n = 1` hypothesis. -/
theorem card_nonzeroRoots_le_natDegree_sub_natTrailingDegree
    (S : Finset F) {g : F[X]} (hg : g ≠ 0) :
    (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x)).card ≤ g.natDegree - g.natTrailingDegree := by
  -- the distinct nonzero roots inject into the nonzero part of `g.roots`
  have hsub : (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x))
      ⊆ (g.roots.filter (· ≠ (0 : F))).toFinset := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨_, hxne, hroot⟩ := hx
    rw [Multiset.mem_toFinset, Multiset.mem_filter]
    exact ⟨(Polynomial.mem_roots hg).mpr hroot, hxne⟩
  calc (S.filter (fun x => x ≠ 0 ∧ g.IsRoot x)).card
      ≤ (g.roots.filter (· ≠ (0 : F))).toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (g.roots.filter (· ≠ (0 : F))) := Multiset.toFinset_card_le _
    _ ≤ g.natDegree - g.natTrailingDegree := card_nonzero_roots_le_span g

/-- **The `m`-sparse strata `μ_n`-incidence, bounded by the SPAN of its reduced support.** For
`S ⊆ μ_n` (every `x ∈ S` has `x ^ n = 1`) and a sparse direction `Σ_{i∈t} c_i X^(e_i)` whose mod-`n`
reduction is nonzero, the count of nonzero `μ_n`-points where the direction vanishes is at most the
reduced support span `(reduce).natDegree − (reduce).natTrailingDegree`. The incidence-invariance
under mod-`n` reduction (`munRoot_sparse_iff_reduce`, thinness-essential) lets the support-span
bound apply to the low-degree reduced polynomial: the sharp refinement of the `< n` cap. -/
theorem sparse_munRoot_card_le_window {n : ℕ} (S : Finset F) (t : Finset ι) (c : ι → F)
    (e : ι → ℕ)
    (hg : ArkLib.ProximityGap.C71SparseStrataReduce.sparsePolyReduce n t c e ≠ 0)
    (hSn : ∀ x ∈ S, x ^ n = 1) :
    (S.filter (fun x => x ≠ 0 ∧
        (ArkLib.ProximityGap.C71SparseStrataReduce.sparsePoly t c e).IsRoot x)).card
      ≤ (ArkLib.ProximityGap.C71SparseStrataReduce.sparsePolyReduce n t c e).natDegree
        - (ArkLib.ProximityGap.C71SparseStrataReduce.sparsePolyReduce
            n t c e).natTrailingDegree := by
  -- rewrite the predicate to the REDUCED direction's root predicate (same incidence on `μ_n`)
  have hfilter : (S.filter (fun x => x ≠ 0 ∧
        (ArkLib.ProximityGap.C71SparseStrataReduce.sparsePoly t c e).IsRoot x))
      = (S.filter (fun x => x ≠ 0 ∧
        (ArkLib.ProximityGap.C71SparseStrataReduce.sparsePolyReduce n t c e).IsRoot x)) := by
    apply Finset.filter_congr
    intro x hxS
    constructor
    · rintro ⟨hxne, hr⟩
      exact ⟨hxne, (ArkLib.ProximityGap.C71SparseStrataReduce.munRoot_sparse_iff_reduce
        t c e (hSn x hxS)).mp hr⟩
    · rintro ⟨hxne, hr⟩
      exact ⟨hxne, (ArkLib.ProximityGap.C71SparseStrataReduce.munRoot_sparse_iff_reduce
        t c e (hSn x hxS)).mpr hr⟩
  rw [hfilter]
  exact card_nonzeroRoots_le_natDegree_sub_natTrailingDegree S hg

end ArkLib.ProximityGap.C71SparseStrataWindow

/-! ## Axiom audit -/
open ArkLib.ProximityGap.C71SparseStrataWindow in
#print axioms card_nonzeroRoots_le_natDegree_sub_natTrailingDegree
#print axioms ArkLib.ProximityGap.C71SparseStrataWindow.sparse_munRoot_card_le_window
