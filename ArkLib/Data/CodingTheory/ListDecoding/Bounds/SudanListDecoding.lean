/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GuruswamiSudanListSize
import ArkLib.Data.CodingTheory.ProximityGap.VerifiedBricks
import Mathlib

open MvPolynomial Polynomial
open ArkLib.ProximityGap.Issue232Bricks
set_option linter.style.longLine false

/-!
# The assembled Guruswami–Sudan list-decoding bound (#232/#389)

The pieces of the Guruswami–Sudan list-decoder are present in-tree but scattered across two
polynomial representations:

* interpolation existence — `gkl24_interpolation_existence` (in `MvPolynomial (Fin 2) F`);
* the list-size half — `gs_list_size_bound` (annihilated codewords `≤ deg_Y`, same representation);
* the degree budget and agreement ⇒ root step — `natDegree_eval_le`,
  `eval_zero_of_agreement_gt_degree`, `sudan_codeword_list_bound` (in `F[X][Y]`, `VerifiedBricks`).

This file supplies the **missing glue**, entirely in the `MvPolynomial (Fin 2) F` representation that
`gkl24_interpolation_existence` outputs, and assembles the quantitative list-decoder output:

> `natDegree_substitution_le` :  `deg (Q(X, f(X))) ≤ deg_X + deg_Y · deg f`
> `sudan_list_bound`          :  an interpolant `Q ≠ 0` of bidegree `(deg_X, deg_Y)` lists at most
>                                `deg_Y` degree-`≤ k` messages agreeing past `deg_X + deg_Y · k`.

The degree budget is transported across the `F[X₀,X₁] ≅ F[X][Y]` isomorphism `psi` (so the
`VerifiedBricks` `natDegree_eval_le` engine applies), then chained with the agreement ⇒ annihilation
step and `gs_list_size_bound`.

This is the classical Sudan baseline — the radius the Proximity Prize (#232/#389) is defined to beat.
It is the *known* result (not the open core): choosing `(deg_X, deg_Y)` to make
`deg_X + deg_Y · k < t` with `(deg_X+1)(deg_Y+1) > n` realizes the Sudan radius `1 − √(2ρ)`
(`sudan_params_feasible`); pushing the agreement threshold `t` below the **Johnson** radius `1 − √ρ`
for explicit smooth-domain RS is what remains open.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

namespace CodingTheory.Bounds
variable {F : Type} [Field F]

/-- The `X`-degree of each `Y`-coefficient of `psi Q` is bounded by the `X₀`-degree of `Q`. The
`Y`-coefficient at power `i` of `psi Q = ∑_m C(C(c_m)·X^{m₀})·X^{m₁}` is `∑_{m : m₁ = i} C(c_m)·X^{m₀}`,
whose `X`-degree is `≤ max_m m₀ ≤ deg_{X₀} Q`. -/
theorem coeff_psi_natDegree_le (Q : MvPolynomial (Fin 2) F) (deg_X : ℕ)
    (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X) (i : ℕ) :
    ((psi Q).coeff i).natDegree ≤ deg_X := by
  classical
  have hsum : psi Q = ∑ m ∈ Q.support, psi (MvPolynomial.monomial m (MvPolynomial.coeff m Q)) := by
    conv_lhs => rw [Q.as_sum]; rw [map_sum]
  rw [hsum, Polynomial.finset_sum_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => ?_)
  have hmono : psi (MvPolynomial.monomial m (MvPolynomial.coeff m Q))
      = Polynomial.C (Polynomial.C (MvPolynomial.coeff m Q) * Polynomial.X ^ m 0)
          * Polynomial.X ^ m 1 := by
    rw [psi, MvPolynomial.aeval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (algebraMap F (Polynomial (Polynomial F))) (MvPolynomial.coeff m Q)
          = Polynomial.C (Polynomial.C (MvPolynomial.coeff m Q)) from rfl,
      Polynomial.C_mul, Polynomial.C_pow]
    ring
  rw [hmono, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h
  · rw [mul_one]
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
    exact le_trans (MvPolynomial.monomial_le_degreeOf 0 hm) hX
  · rw [mul_zero, Polynomial.natDegree_zero]
    exact Nat.zero_le _

/-- **Degree of the GS substitution.** The univariate substitution `Q(X, f(X))` has `X`-degree at
most `deg_X + deg_Y · deg f`, where `deg_X, deg_Y` bound the `X₀, X₁`-degrees of `Q`. Proven by
transporting `Q` across `psi` (`coeff_psi_natDegree_le`, `natDegree_psi_le`) and applying the
`F[X][Y]` substitution degree bound `natDegree_eval_le`. -/
theorem natDegree_substitution_le (Q : MvPolynomial (Fin 2) F) (deg_X deg_Y : ℕ)
    (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X) (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
    (f : Polynomial F) :
    (MvPolynomial.aeval
        (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q).natDegree
      ≤ deg_X + deg_Y * f.natDegree := by
  rw [← psi_eval]
  refine le_trans
    (natDegree_eval_le (psi Q) f deg_X (fun i => coeff_psi_natDegree_le Q deg_X hX i)) ?_
  calc deg_X + (psi Q).natDegree * f.natDegree
      ≤ deg_X + deg_Y * f.natDegree := by gcongr; exact natDegree_psi_le Q deg_Y hY

/-- **Guruswami–Sudan list-decoding bound (assembled).** Fix an interpolation polynomial `Q ≠ 0`
with `deg_{X₀} Q ≤ deg_X` and `deg_{X₁} Q ≤ deg_Y`. Any family `L` of degree-`≤ k` message
polynomials, each agreeing with the received data on a curve-set `agree f` of size
`> deg_X + deg_Y · k` (i.e. `Q(x, f(x)) = 0` for `x ∈ agree f`), has at most `deg_Y` members.

This packages the substitution degree budget (`natDegree_substitution_le`), the agreement ⇒
annihilation step (more roots than degree forces `Q(X, f(X)) = 0`), and the list-size bound
(`gs_list_size_bound`) into a single quantitative GS list-decoder output. -/
theorem sudan_list_bound (Q : MvPolynomial (Fin 2) F) (hQ : Q ≠ 0) (deg_X deg_Y k : ℕ)
    (hX : MvPolynomial.degreeOf 0 Q ≤ deg_X) (hY : MvPolynomial.degreeOf 1 Q ≤ deg_Y)
    (L : Finset (Polynomial F)) (hdeg : ∀ f ∈ L, f.natDegree ≤ k)
    (agree : Polynomial F → Finset F)
    (hroot : ∀ f ∈ L, ∀ x ∈ agree f,
      (MvPolynomial.aeval
        (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q).eval x = 0)
    (hbig : ∀ f ∈ L, deg_X + deg_Y * k < (agree f).card) :
    L.card ≤ deg_Y := by
  classical
  have hg0 : ∀ f ∈ L,
      MvPolynomial.aeval (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q = 0 := by
    intro f hf
    set g := MvPolynomial.aeval
      (fun i => if i = 0 then (Polynomial.X : Polynomial F) else f) Q with hgdef
    by_contra hne
    have hsub : agree f ⊆ g.roots.toFinset := by
      intro a ha
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hroot f hf a ha
    have h1 : (agree f).card ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    have h2 : g.roots.toFinset.card ≤ g.natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
    have h3 : g.natDegree ≤ deg_X + deg_Y * k := by
      refine le_trans (natDegree_substitution_le Q deg_X deg_Y hX hY f) ?_
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hdeg f hf)) deg_X
    have h4 := hbig f hf
    omega
  exact gs_list_size_bound Q hQ deg_Y hY L hg0

end CodingTheory.Bounds

/-! ## Axiom audit -/
#print axioms CodingTheory.Bounds.coeff_psi_natDegree_le
#print axioms CodingTheory.Bounds.natDegree_substitution_le
#print axioms CodingTheory.Bounds.sudan_list_bound
