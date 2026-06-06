/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable

/-!
# Discriminant ↔ separability: specialization commutation and the separability converse

This file supplies the two `Polynomial.discr`-facing lemmas needed to discharge the BCIKS20 §5
*good-specialization* step (`lalalune/ArkLib` issue #8 follow-up).  Both are stated for **mathlib's**
`Polynomial.discr` (the Sylvester-determinant discriminant of `Mathlib.RingTheory.Polynomial.`
`Resultant.Basic`), which is exactly the object the in-tree bivariate `Polynomial.Bivariate.discr_y`
is built from: `discr_y f = (-1) ^ (d * (d-1) / 2) * f.discr` once `0 < f.degree`
(see `CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean`).

This file imports **only** Mathlib (no `CompPoly`, in particular no `discr_y` / `evalX`): the
in-tree `discr_y` / `evalX` chain routes through `CompPoly`, which is mid-repair, so we phrase
everything in terms of `Polynomial.discr` and `Polynomial.map`, and leave the final
`discr_y` / `evalX` wiring to the issue-#8 owner via the bridge corollary at the end.

## Main results

* `Polynomial.discr_map_of_natDegree_preserved`  — **Lemma 1 (specialization commutation).**
  For a ring hom `φ : A →+* B` into a *domain* `B` that *preserves the `natDegree`* of `f`
  (`(f.map φ).natDegree = f.natDegree`, the honest "leading coefficient survives" side condition),
  the discriminant commutes with `φ`: `(f.map φ).discr = φ f.discr`.

* `Polynomial.separable_of_discr_ne_zero` — **Lemma 2 (separability converse).**
  Over a field `K`, a positive-degree `f : K[X]` with `f.discr ≠ 0` is `Separable`.

* `Polynomial.discr_eval_C_comm` / `Polynomial.discrSpecializationBridge` — **Lemma 3 (the payoff
  bridge).**  The `Polynomial.discr`-level corollary the #8 owner wires to `discr_y` / `evalX`:
  from a nonvanishing *specialized* discriminant of a positive-degree bivariate factor, conclude the
  specialized factor is nonzero **and** `Separable`.

## The honest X-vs-Z caveat (read before wiring)

The issue sketch asks for `discr (evalX (C x₀) R) = evalX x₀ (discr_y R)`.  Unfolding the in-tree
definitions (`evalX a f = f.map (Polynomial.evalRingHom a)`,
`discr_y f = ± f.discr` for `0 < f.degree`) reveals these two sides specialize **different**
variables, so the equation is *false as literally sketched*:

* `R : F[Z][X][Y] = Polynomial (Polynomial (Polynomial F))`, top variable `Y`.
* `evalX (C x₀) R = R.map (evalRingHom (C x₀))` with `evalRingHom (C x₀) : F[Z][X] →+* F[Z]`
  specializes the **middle `X`** variable (it maps the `F[Z][X]` coefficients of the `Y`-poly).
  Hence `discr (evalX (C x₀) R)` is the `Y`-discriminant of `R |_{X := x₀}`, lying in `F[Z]`.
* `evalX x₀ (discr_y R) = (discr_y R).map (evalRingHom x₀)` with `evalRingHom x₀ : F[Z] →+* F`
  specializes the **inner `Z`** variable of the `Y`-discriminant, lying in `F[X]`.

Both land in `Polynomial F` (so the equation type-checks), but the left kills `X` while the right
kills `Z`.  The mathematically-true commutation specializes the **same** variable on both sides:

  `discr (R.map (evalRingHom (C x₀))) = (evalRingHom (C x₀)) (discr R)`   (specialize `X`),

which is exactly `Polynomial.discr_map_of_natDegree_preserved` with `φ = evalRingHom (C x₀)`.  The
`discr_y` normalizing sign `(-1) ^ (d (d-1)/2)` is a *unit*, so it does not affect the
nonvanishing/separability conclusions the bridge needs.

So the corrected Lemma 1 is `discr_map_of_natDegree_preserved`; the bridge corollaries below are
phrased on the `X`-specialization (`evalRingHom (C x₀)`) consistently, and we flag that the
#8 producer (`exists_good_x₀_evalX_discr_y_ne`, which produces `evalX x₀ (discr_y R) ≠ 0`, i.e. a
**`Z`-good** point) must be matched to an `X`-good point — or the bridge re-derived for `Z` — before
it discharges the `evalX (C x₀) R` shape of `hx0` / `hsep`.
-/

namespace Polynomial

open scoped Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-! ## Lemma 1 — specialization commutation for `Polynomial.discr` -/

/-- A `natDegree`-preserving ring hom keeps the leading coefficient nonzero
(the honest "leading coefficient survives specialization" side condition), provided the source has
positive degree and the target is a domain. -/
theorem map_ne_zero_of_natDegree_preserved {φ : A →+* B} {f : A[X]}
    (hdeg : 0 < f.natDegree) (hmap : (f.map φ).natDegree = f.natDegree) :
    f.map φ ≠ 0 := by
  intro h
  rw [h, natDegree_zero] at hmap
  omega

/-- **Lemma 1 (specialization commutation).**  For a ring hom `φ : A →+* B` into a domain that
preserves the `natDegree` of a positive-degree `f`, the discriminant commutes with `φ`:
`(f.map φ).discr = φ f.discr`.

The genuine side conditions are exposed explicitly:
* `0 < f.natDegree` — the discriminant–resultant identity `Polynomial.resultant_deriv` is only
  valid in positive degree (it is *false* for constants);
* `(f.map φ).natDegree = f.natDegree` — the leading coefficient (and degree) must survive the
  specialization, otherwise the resultant size arguments change and the identity breaks;
* `[IsDomain B]` — needed to cancel the surviving `(-1) ^ … * leadingCoeff` factor (a nonzero,
  hence non-zero-divisor, element of the target).

The proof runs the resultant–discriminant identity `resultant_deriv` on both `f` and `f.map φ`,
transports the resultant across `φ` at *fixed* size arguments via `resultant_map_map`, and cancels
the common nonzero sign·leadingCoeff factor. -/
theorem discr_map_of_natDegree_preserved [IsDomain B] {φ : A →+* B} {f : A[X]}
    (hdeg : 0 < f.natDegree) (hmap : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  classical
  set g : B[X] := f.map φ with hg
  have hfdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hdeg
  have hgdegnat : 0 < g.natDegree := by rw [hmap]; exact hdeg
  have hgdeg : 0 < g.degree := natDegree_pos_iff_degree_pos.mp hgdegnat
  have hgne : g ≠ 0 := map_ne_zero_of_natDegree_preserved hdeg hmap
  -- leading coefficient survives: `g.leadingCoeff = φ f.leadingCoeff`.
  have hglc : g.leadingCoeff = φ f.leadingCoeff := by
    rw [← coeff_natDegree, ← coeff_natDegree, hmap, hg, coeff_map]
  have hlc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgne
  -- transport the resultant across `φ` at the *fixed* size arguments `(natDegree, natDegree-1)`.
  have hmapres :
      resultant g g.derivative g.natDegree (g.natDegree - 1)
        = φ (resultant f f.derivative f.natDegree (f.natDegree - 1)) := by
    rw [hg, derivative_map, hmap, resultant_map_map]
  -- the discriminant–resultant identity on both rings.
  have hrd := resultant_deriv (f := g) hgdeg
  have hrdf := resultant_deriv (f := f) hfdeg
  rw [hrd, hrdf] at hmapres
  rw [map_mul, map_mul, map_pow, map_neg, map_one, hglc] at hmapres
  -- the two `(-1)^…` exponents agree once `natDegree` is preserved.
  have hsigneq :
      (g.natDegree * (g.natDegree - 1) / 2) = (f.natDegree * (f.natDegree - 1) / 2) := by
    rw [hmap]
  rw [hsigneq] at hmapres
  -- cancel the common nonzero `(-1)^… * leadingCoeff` factor.
  have hcancel :
      ((-1 : B) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.leadingCoeff) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by rw [← hglc]; exact hlc_ne)
  exact mul_left_cancel₀ hcancel hmapres

/-! ## Lemma 2 — separability converse for `Polynomial.discr` over a field -/

/-- **Lemma 2 (separability converse).**  Over a field `K`, a positive-`natDegree` polynomial
`f : K[X]` with nonzero discriminant is separable.

Route: by `resultant_deriv`, `f.discr ≠ 0` (and `f.leadingCoeff ≠ 0` over a field) forces
`resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0`.  The Bézout-from-resultant lemma
`exists_mul_add_mul_eq_C_resultant` (valid at these size arguments since
`f.derivative.natDegree ≤ f.natDegree - 1` by `natDegree_derivative_le`) then yields polynomials
`p, q` with `f * p + f.derivative * q = C (resultant …)`; scaling by `C (resultant …)⁻¹` (nonzero in
the field) produces the Bézout identity `IsCoprime f f.derivative`, which is *definitionally*
`f.Separable` (`Polynomial.separable_def`).

Char-`p` caveat: the conclusion is `Separable`, i.e. coprimality with the derivative; in
characteristic `p` an inseparable `f` has `f.discr = 0` (the contrapositive), so the hypothesis
`f.discr ≠ 0` genuinely excludes those — no separability is faked. -/
theorem separable_of_discr_ne_zero {K : Type*} [Field K] {f : K[X]}
    (hdeg : 0 < f.natDegree) (hdiscr : f.discr ≠ 0) :
    f.Separable := by
  classical
  have hfdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hdeg
  have hfne : f ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; exact absurd hdeg (lt_irrefl 0)
  have hlc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfne
  -- the `(natDegree, natDegree-1)` resultant is nonzero.
  set c : K := resultant f f.derivative f.natDegree (f.natDegree - 1) with hc
  have hc_ne : c ≠ 0 := by
    rw [hc, resultant_deriv hfdeg]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hlc_ne) hdiscr
  -- Bézout identity from the resultant at these size arguments.
  obtain ⟨p, q, _hp, _hq, he⟩ :=
    exists_mul_add_mul_eq_C_resultant f f.derivative (le_refl f.natDegree)
      (natDegree_derivative_le f) (Or.inl (by omega))
  rw [← hc] at he
  -- scale by `C c⁻¹` to get the unit Bézout identity, hence coprimality, hence separability.
  rw [separable_def]
  refine ⟨C c⁻¹ * p, C c⁻¹ * q, ?_⟩
  have : C c⁻¹ * (f * p + f.derivative * q) = C c⁻¹ * C c := by rw [he]
  rw [mul_add, ← C_mul, inv_mul_cancel₀ hc_ne, C_1] at this
  rw [← this]; ring

/-! ## Lemma 3 — the payoff bridge (`Polynomial.discr` level)

The §5 producer `exists_good_x₀_evalX_discr_y_ne` (`Claim57FieldDischarge.lean`) hands the #8 owner
a nonvanishing *specialized* discriminant.  Combined with Lemmas 1+2 above, this fixes both the
nonvanishing of the specialized factor and its separability.  We phrase the bridge purely with
`Polynomial.discr` and `Polynomial.map (evalRingHom _)` so it imports only Mathlib; the #8 owner
rewrites with the in-tree `Polynomial.Bivariate.evalX_eq_map` and the `discr_y = ± discr` unfolding
to land on the `evalX (C x₀) R` / `(evalX (C x₀) R).Separable` shapes of `hx0` / `hsep`.

NB the X-vs-Z caveat in the module docstring: instantiate the general bridges below at
`φ := Polynomial.evalRingHom (C x₀)` to get the `X`-specialization (consistent on both sides), since
`evalX (C x₀) R = R.map (Polynomial.evalRingHom (C x₀))` by `Polynomial.Bivariate.evalX_eq_map`. -/

/-- **Lemma 3 (the payoff bridge), `discr` form.**  Let `R` be a positive-degree polynomial over the
domain `A` (e.g. `A = F[Z][X]`, `R : F[Z][X][Y]`), and `φ : A →+* B` a `natDegree`-preserving hom
into a *field* `B` (e.g. `φ = evalRingHom (C x₀) : F[Z][X] →+* F[Z]` — but note `F[Z]` is a domain,
not a field; over a field-valued specialization such as the residue/fraction field this applies
directly, otherwise compose with the fraction-field embedding).

From the **nonvanishing of the specialized discriminant** `(f.map φ).discr ≠ 0` (equivalently, by
Lemma 1, `φ f.discr ≠ 0`) we get, *outright*:

* `f.map φ ≠ 0` (the specialized factor does not collapse), and
* `(f.map φ).Separable` (the specialized factor is separable),

which are exactly the `hx0` / `hsep` payloads.  This is the direct combination of Lemma 1
(`discr_map_of_natDegree_preserved`) and Lemma 2 (`separable_of_discr_ne_zero`). -/
theorem ne_zero_and_separable_of_specialized_discr_ne_zero
    {K : Type*} [Field K] {φ : A →+* K} {f : A[X]}
    (hdeg : 0 < f.natDegree) (hmap : (f.map φ).natDegree = f.natDegree)
    (hdiscr : (f.map φ).discr ≠ 0) :
    f.map φ ≠ 0 ∧ (f.map φ).Separable := by
  refine ⟨map_ne_zero_of_natDegree_preserved hdeg hmap, ?_⟩
  have hgdeg : 0 < (f.map φ).natDegree := by rw [hmap]; exact hdeg
  exact separable_of_discr_ne_zero hgdeg hdiscr

/-- **Lemma 3 (the payoff bridge), restated from the un-mapped discriminant.**  Same conclusion as
above but driven from `φ f.discr ≠ 0` (the shape `exists_good_x₀_evalX_discr_y_ne` produces, modulo
the `discr_y = ± discr` unit and the X-vs-Z variable match): Lemma 1 turns it into
`(f.map φ).discr ≠ 0`, then Lemma 2 finishes. -/
theorem ne_zero_and_separable_of_specialized_base_discr_ne_zero
    {K : Type*} [Field K] {φ : A →+* K} {f : A[X]}
    (hdeg : 0 < f.natDegree) (hmap : (f.map φ).natDegree = f.natDegree)
    (hdiscr : φ f.discr ≠ 0) :
    f.map φ ≠ 0 ∧ (f.map φ).Separable := by
  have : (f.map φ).discr ≠ 0 := by
    rw [discr_map_of_natDegree_preserved hdeg hmap]; exact hdiscr
  exact ne_zero_and_separable_of_specialized_discr_ne_zero hdeg hmap this

end Polynomial
