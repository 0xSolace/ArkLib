/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.EvalOnZNonzero
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

set_option linter.style.longLine false

/-!
# The per-parameter list-size bound, fully discharged

`EvalOnZNonzero.perZ_listSize_le` bounds the number of degree-`≤ k` interpolants close to the line at
a single parameter `z` by `D_Y Q` — *assuming* each interpolant's linear factor `(Y - C p)` divides
the `Z`-specialization `eval_on_Z Q z`.  This file discharges that assumption.

The divisibility is exactly the BCIKS20 §5 graph-vanishing keystone, generalized to an arbitrary
close interpolant (`Agreement.Q_vanishes_on_close_codeword_graph_gen`): if `p` agrees with the line on
a set `A` with `natWeightedDegree(eval_on_Z Q z) 1 k < m·|A|`, then `eval_on_Z Q z` vanishes at `p`.
The non-degeneracy `eval_on_Z Q z ≠ 0` is the generic GAP-NZ discharge (`card_badZ_le`).

Composing the two gives `close_interpolants_card_le`: at a good `z`, the number of distinct degree-`≤ k`
codewords close to the line is `≤ D_Y Q = poly(n)` — *unconditionally* (no divisibility input).  This
is the per-`z` ingredient of the Guruswami–Sudan curve list size, the small-`L` content of the
`RSCurveListSizeResidual`.
-/

open Polynomial Finset

namespace ProximityGap

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [Finite F]
variable {m : ℕ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-- **Per-parameter list-size bound, fully discharged.** At a good parameter `z`
(`eval_on_Z Q z ≠ 0`, ensured for all but `≤ d` params by `card_badZ_le` with `ZdegLE Q d`), any
finite family `Ps` of degree-`≤ k` interpolants, EACH agreeing with the line `u₀+z•u₁` on a set `A p`
with `natWeightedDegree(eval_on_Z Q z) 1 k < m·|A p|`, has cardinality `≤ D_Y Q`.

Every such interpolant is a `Y`-root of `eval_on_Z Q z` by the generalized graph-vanishing keystone
(`Q_vanishes_on_close_codeword_graph_gen`), so `(Y - C p)` divides it, and distinct roots of a nonzero
bivariate polynomial number `≤ natDegreeY ≤ D_Y Q`.  This bounds the number of distinct codewords close
to the line at a single parameter — unconditionally, with the divisibility discharged. -/
theorem close_interpolants_card_le [DecidableEq (RatFunc F)] [DecidableEq (Polynomial F)]
    (k : ℕ) {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (Ps : Finset (Polynomial F))
    (hdeg : ∀ p ∈ Ps, p.natDegree ≤ k)
    (A : Polynomial F → Finset (Fin n))
    (hA : ∀ p ∈ Ps, ∀ i ∈ A p, (u₀ + z • u₁) i = p.eval (ωs i))
    (hcount : ∀ p ∈ Ps,
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * (A p).card) :
    Ps.card ≤ Trivariate.D_Y Q := by
  have hdvd : ∀ p ∈ Ps, (Polynomial.X - Polynomial.C p) ∣ Trivariate.eval_on_Z Q z := by
    intro p hp
    refine Polynomial.dvd_iff_isRoot.mpr ?_
    rw [Polynomial.IsRoot.def]
    exact Q_vanishes_on_close_codeword_graph_gen (F := F) (n := n) (m := m) (k := k)
      h_gs hQz_ne p (hdeg p hp) (A p) (hA p hp) (hcount p hp)
  exact perZ_listSize_le (F := F) hQz_ne Ps hdvd

end ProximityGap
