/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.GroupTheory.OrderOfElement

/-!
# Loop 19 — the smooth domain's *sparse annihilator*: the concrete smooth-vs-generic obstruction

Loop 18 reduced the prize to one binary question: is the smooth-deterministic-domain RS list at the
prize radius `q`-independently bounded (TRUE / BGM-generic) or `q`-growing (FALSE / Diamond–Gruen
deterministic)? The proof-side conditional (Loop17) needs the smooth domain to behave like *generic*
evaluation points. This file pins down the exact algebraic reason it might not.

The prize's evaluation domain is a **smooth multiplicative subgroup** `L ⊆ Fˣ` of size `N = 2^m`
(the `N`-th roots of unity). Two structural facts, both verified here:

* **Sparse annihilation (`smooth_domain_annihilated_by_sparse`):** every domain element is a root of
  the **2-term** polynomial `X^N − 1`. (A finite group element satisfies `g^{|G|}=1`; push through the
  inclusion into the field.)
* **The annihilator is sparse (`annihilator_coeff_zero_of_mem_interior`):** `X^N − 1` has *zero*
  coefficient at every degree strictly between `0` and `N` — only `2` nonzero terms among `N+1`.

A **generic** set of `N` field points has, by contrast, a *dense* degree-`N` annihilator
`∏(X − xᵢ)` with `≈ N` nonzero coefficients and no algebraic relations among the points. This
sparsity / high symmetry (the domain is closed under multiplication by `N`-th roots of unity and under
Frobenius) is exactly what a genericity argument like BGM assumes *absent*. So Loop19 is the concrete
algebraic obstruction to discharging Loop17's "(BGM-for-smooth)" hypothesis — and the structural
foothold a Diamond–Gruen-style deterministic disproof would exploit. It does not decide the prize; it
names the obstruction precisely. Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (Loop19).
-/

namespace ArkLib.ProximityGap.StructureLoop19

open Polynomial

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [Field F]

/-- **Sparse annihilation of the smooth domain.** If the smooth evaluation domain is the image of a
finite group `G` of order `N = Fintype.card G` under an inclusion `ι : G →* F` (a multiplicative
subgroup of `Fˣ` pushed into `F`), then every domain element `ι g` is a root of the 2-term polynomial
`X^N − 1`: `(ι g)^N = 1`. -/
theorem smooth_domain_annihilated_by_sparse (ι : G →* F) (g : G) :
    (ι g) ^ (Fintype.card G) = 1 := by
  rw [← map_pow, pow_card_eq_one, map_one]

/-- **The annihilator `X^N − 1` is sparse.** For `0 < i < N`, the coefficient of `X^N − 1` at degree
`i` is `0`: only the degree-`0` and degree-`N` coefficients are nonzero (`2` terms among `N+1`),
unlike a generic dense degree-`N` annihilator. -/
theorem annihilator_coeff_zero_of_mem_interior {N i : ℕ} (h0 : 0 < i) (hN : i < N) :
    (X ^ N - 1 : F[X]).coeff i = 0 := by
  rw [coeff_sub, coeff_X_pow, coeff_one]
  rw [if_neg (Nat.ne_of_lt hN), if_neg (Nat.pos_iff_ne_zero.mp h0)]
  ring

/-- **Exactly two nonzero coefficients band the annihilator.** The endpoints are nonzero in any
nontrivial case: the degree-`N` coefficient of `X^N − 1` is `1` (for `N ≥ 1`). Together with
`annihilator_coeff_zero_of_mem_interior` this shows `X^N − 1` is `2`-sparse — the algebraic
signature distinguishing the smooth domain from generic points. -/
theorem annihilator_leading_coeff {N : ℕ} (hN : 1 ≤ N) :
    (X ^ N - 1 : F[X]).coeff N = 1 := by
  rw [coeff_sub, coeff_X_pow, coeff_one, if_pos rfl,
    if_neg (by omega : ¬ N = 0), sub_zero]

end ArkLib.ProximityGap.StructureLoop19
