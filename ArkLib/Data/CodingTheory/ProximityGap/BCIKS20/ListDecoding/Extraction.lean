/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami

namespace ProximityGap

open Polynomial Polynomial.Bivariate  NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *Cartesian cross-term blowup* witnessing the indexing defect in the factorization
conjunct of `irreducible_factorization_of_gs_solution` (= [BCIKS20, Eq. 5.12] as currently
formalized). For two distinct factors `a, b` the *intended* Eq-5.12 witnesses
`R = [a, b]`, `f = [1, 1]`, `e = [1, 2]` (which should encode `a¹ · b²`) instead make the
displayed triple product over the three `toFinset`s evaluate to `a³ · b³`: each factor is
raised to `∑ (eᵢ ∈ {1,2}) = 3` and is copied across `f.toFinset = {1}`. Hence the
Cartesian-product form cannot represent a factorization with non-uniform multiplicities,
confirming the product is mis-indexed relative to the paper's single index `∏ᵢ`. -/
lemma eq512_cartesian_product_blowup (a b : F[Z][X][Y]) (hab : a ≠ b) :
    (∏ (Rᵢ ∈ ([a, b]).toFinset) (fᵢ ∈ ([1, 1] : List ℕ).toFinset)
        (eᵢ ∈ ([1, 2] : List ℕ).toFinset),
        (Rᵢ.comp ((Polynomial.X : F[Z][X][Y]) ^ fᵢ)) ^ eᵢ)
      = a ^ 3 * b ^ 3 := by
  have e1 : ([1, 1] : List ℕ).toFinset = ({1} : Finset ℕ) := by decide
  have e2 : ([1, 2] : List ℕ).toFinset = ({1, 2} : Finset ℕ) := by decide
  have eR : ([a, b]).toFinset = {a, b} := by simp [List.toFinset_cons]
  -- The parenthesized triple binder `∏ (Rᵢ ∈ _) (fᵢ ∈ _) (eᵢ ∈ _), …` desugars to a single
  -- product over the Cartesian (`×ˢ`) finset `{a,b} ×ˢ {1} ×ˢ {1,2}`; split it back out.
  rw [eR, e1, e2, Finset.prod_product]
  simp_rw [Finset.prod_product]
  rw [Finset.prod_pair hab]
  simp only [Finset.prod_singleton]
  rw [Finset.prod_pair (show (1 : ℕ) ≠ 2 by decide),
      Finset.prod_pair (show (1 : ℕ) ≠ 2 by decide)]
  simp only [pow_one, comp_X]
  ring

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Strong-separability is unsatisfiable for genuinely-arising factors* — the verified
defect (bug #18) in the separability conjunct of `irreducible_factorization_of_gs_solution`.

The conjunct `∀ Rᵢ ∈ R, Rᵢ.Separable` uses `Polynomial.Separable` over the **coefficient ring**
`F[Z][X]`, which is *not a field*. By `separable_def`, `Rᵢ.Separable` unfolds to a Bézout
identity `a · Rᵢ + b · Rᵢ.derivative = 1` with `a, b : F[Z][X][Y]` — i.e. coprimality *in the
polynomial ring* `F[Z][X][Y]`, an extremely strong condition. It is **not** the paper's intended
separability of `Rᵢ` over the fraction field `F(Z,X)` (equivalently, nonvanishing of `discr_y`,
the form actually consumed by Claim 5.6 `discr_of_irred_components_nonzero`).

Concretely the factor `r = Y² − X` (here `X = C (C X) : F[Z][X][Y]`, a *prime* element of the
coefficient ring) is exactly the kind of irreducible factor a `ModifiedGuruswami` solution
produces: it is irreducible over `F[Z][X]`, squarefree, and **separable over the fraction field**
`F(Z,X)` (its two roots `±√X` are distinct in char ≠ 2). Yet it is **not** `Separable` over
`F[Z][X]`: separability is preserved by every coefficient ring hom (`Separable.map`), so mapping
the coefficient ring `F[Z][X] →+* F` by `Z, X ↦ 0` would send `r` to `Y²`, which is not even
squarefree. Hence no choice of witnesses can satisfy the strong conjunct together with
irreducibility once a factor of `Y`-degree ≥ 2 over a non-square coefficient appears — and the
`ModifiedGuruswami` `Y`-degree budget `D_Y Q < D_X / k` permits exactly such factors. -/
lemma eq512_strong_separable_unsat
    (g : F[Z][X] →+* F) (hgX : g (Polynomial.C (Polynomial.X : Polynomial F) : F[Z][X]) = 0) :
    ¬ (((Polynomial.X : F[Z][X][Y]) ^ 2
        - Polynomial.C (Polynomial.C (Polynomial.X : Polynomial F) : F[Z][X])).Separable) := by
  classical
  intro hsep
  -- separability transfers along the coefficient ring hom `g : F[Z][X] →+* F`.
  have hmap := hsep.map (f := g)
  -- the image is `Y² - C (g (C X)) = Y² - C 0 = Y²`.
  have himg :
      (((Polynomial.X : F[Z][X][Y]) ^ 2
          - Polynomial.C (Polynomial.C (Polynomial.X : Polynomial F) : F[Z][X])).map g)
        = (Polynomial.X : F[X]) ^ 2 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hgX,
      Polynomial.C_0, sub_zero]
  rw [himg] at hmap
  -- but `Y²` is not squarefree, contradicting `Separable.squarefree`.
  have hsq : Squarefree ((Polynomial.X : F[X]) ^ 2) := hmap.squarefree
  have hYY : (Polynomial.X : F[X]) * (Polynomial.X : F[X]) ∣ (Polynomial.X : F[X]) ^ 2 := by
    rw [pow_two]
  have hunit : IsUnit (Polynomial.X : F[X]) := hsq _ hYY
  exact (Polynomial.prime_X (R := F)).not_unit hunit

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Separable contraction over the fraction field* — the field-side core of the proof of
`irreducible_factorization_of_gs_solution` (= [BCIKS20, Eq. 5.12]).

For every positive-`Y`-degree irreducible factor `g : F[Z][X][Y]` of a `ModifiedGuruswami`
solution `Q`, its image over the fraction field `K := FractionRing (F[Z][X]) = F(Z,X)` admits a
*separable contraction*: there is a separable `sK : K[Y]` and an exponent `m` with
`expand K (q^m) sK = g.map (algebraMap …)`, where `q` is the exponential characteristic.
Equivalently (`expand_eq_comp_X_pow`), `sK.comp (Y^(q^m))` equals the `K`-image of `g`.

This is the step that genuinely needs a *field*: it composes the exponential-characteristic
transfer `F → F(Z,X)` (`expChar_of_injective_algebraMap` along the injective fraction-field map —
no obstruction, contrary to the earlier OBSTRUCTION note), Gauss's lemma for irreducibility over
the fraction field (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`, the idiom of
`RationalFunctions.lean`), and Mathlib's separable contraction over a field
(`Irreducible.hasSeparableContraction`). The remaining open content of Eq. 5.12 is the *descent*
of this `K`-side contraction back to a primitive separable factor over `F[Z][X]` (a Gauss /
`integerNormalization` content argument with no direct Mathlib transfer lemma), plus the
multiplicity bookkeeping that assembles the factors into the zipped `(R, f, e)` lists. -/
lemma eq512_separable_contraction_over_fraction_field
    (g : F[Z][X][Y]) (hg : Irreducible g) (hdeg : g.natDegree ≠ 0) :
    ∃ (sK : Polynomial (FractionRing (F[Z][X]))) (m : ℕ),
      sK.Separable ∧
      Polynomial.expand (FractionRing (F[Z][X]))
          (ringExpChar F ^ m) sK
        = g.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X]))) := by
  classical
  set K := FractionRing (F[Z][X])
  set q := ringExpChar F with hq
  haveI hF : ExpChar F q := ringExpChar.expChar F
  -- exponential characteristic transfers along the injective fraction-field embedding.
  haveI : ExpChar K q :=
    expChar_of_injective_algebraMap (IsFractionRing.injective (F[Z][X]) K) q
  -- a positive-degree irreducible in the UFD-polynomial ring is primitive.
  have hgprim : g.IsPrimitive := hg.isPrimitive hdeg
  -- Gauss: irreducibility transfers to the fraction field.
  have hgK_irr : Irreducible (g.map (algebraMap (F[Z][X]) K)) :=
    (hgprim.irreducible_iff_irreducible_map_fraction_map).mp hg
  -- separable contraction of an irreducible over the field `K`.
  obtain ⟨sK, hsep, m, hexp⟩ := hgK_irr.hasSeparableContraction q
  exact ⟨sK, m, hsep, hexp⟩

/-- *Content is invariant under `expand`* (for `n ≥ 1`): the coefficients of `expand R n r`
are exactly those of `r`, spread out at multiples of `n` and padded with zeros, so the gcd of
the coefficients (the `content`) is unchanged. A small UFD helper used in the Eq-5.12 descent. -/
theorem eq512_content_expand {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {r : R[X]} {n : ℕ} (hn : 0 < n) :
    (Polynomial.expand R n r).content = r.content := by
  classical
  have key : ∀ s : R, Polynomial.C s ∣ (Polynomial.expand R n r) ↔ Polynomial.C s ∣ r := by
    intro s
    constructor
    · intro hdvd
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd ⊢
      intro i
      have := hdvd (n * i)
      rwa [Polynomial.coeff_expand_mul' hn] at this
    · intro hdvd
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd ⊢
      intro i
      rw [Polynomial.coeff_expand hn]
      split_ifs with h
      · exact hdvd _
      · exact dvd_zero _
  have h1 : (Polynomial.expand R n r).content ∣ r.content :=
    (Polynomial.dvd_content_iff_C_dvd).mpr ((key _).mp (Polynomial.C_content_dvd _))
  have h2 : r.content ∣ (Polynomial.expand R n r).content :=
    (Polynomial.dvd_content_iff_C_dvd).mpr ((key _).mpr (Polynomial.C_content_dvd _))
  calc (Polynomial.expand R n r).content
      = normalize (Polynomial.expand R n r).content := (Polynomial.normalize_content).symm
    _ = normalize r.content := (normalize_eq_normalize_iff).mpr ⟨h1, h2⟩
    _ = r.content := Polynomial.normalize_content

/-- `expand` preserves primitivity (for `n ≥ 1`): immediate from `eq512_content_expand`. -/
theorem eq512_isPrimitive_expand {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {r : R[X]} (hr : r.IsPrimitive) {n : ℕ} (hn : 0 < n) :
    (Polynomial.expand R n r).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one] at hr ⊢
  rw [eq512_content_expand hn, hr]

/-- *Descent of the field-side separable contraction back to the UFD `R[X]`* — the first of the
two pieces of [BCIKS20, Eq. 5.12] flagged as remaining. Given an irreducible primitive `g : R[X]`
(`R` a UFD with fraction field `K`) and a `K`-side separable contraction
`expand K n sK = g.map (algebraMap R K)` (`n ≥ 1`, e.g. `n = q^m` from
`eq512_separable_contraction_over_fraction_field`), there is a primitive irreducible `r : R[X]`
whose `K`-image is separable, and an `R`-unit `u`, with `g = C u * expand R n r`.

The witness is `r := (integerNormalization R⁰ sK).primPart`. Clearing denominators
(`IsLocalization.integerNormalization_spec`) and splitting off the content
(`eq_C_content_mul_primPart`) shows `r.map (algebraMap R K) = C c * sK` with `c` a `K`-unit; this
gives separability of the `K`-image (`Separable.unit_mul`). Applying `expand K n` and using
`map_expand` yields `(expand R n r).map = C c * g.map`, so the primitive polynomials `expand R n r`
and `g` have associated `K`-images, hence are associated in `R[X]` (Gauss's
`IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`, both directions). The associating unit is `C u`
with `u` an `R`-unit (`Polynomial.isUnit_iff`), and `r` is irreducible because `expand R n r` is
(its associate `g` is) and `expand` reflects irreducibility (`Polynomial.of_irreducible_expand`). -/
theorem eq512_descent_of_fraction_field_contraction
    {R : Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (g : R[X]) (hg : Irreducible g) (hgprim : g.IsPrimitive)
    (sK : K[X]) (n : ℕ) (hn : 0 < n)
    (hsep : sK.Separable)
    (hexp : Polynomial.expand K n sK = g.map (algebraMap R K)) :
    ∃ (r : R[X]) (u : R), Irreducible r ∧ (r.map (algebraMap R K)).Separable ∧
      IsUnit u ∧ g = Polynomial.C u * (Polynomial.expand R n r) := by
  classical
  set φ := algebraMap R K with hφ
  have hsK0 : sK ≠ 0 := hsep.ne_zero
  obtain ⟨b, hb, hbspec⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) sK
  set N := IsLocalization.integerNormalization (nonZeroDivisors R) sK with hN
  set r := N.primPart with hr
  have hrprim : r.IsPrimitive := N.isPrimitive_primPart
  have hNfact : N = Polynomial.C N.content * r := N.eq_C_content_mul_primPart
  have hmap : N.map φ = Polynomial.C (φ N.content) * r.map φ := by
    conv_lhs => rw [hNfact]
    rw [Polynomial.map_mul, Polynomial.map_C]
  have hbsmul : N.map φ = Polynomial.C (φ b) * sK := by
    rw [hbspec, Algebra.smul_def, Polynomial.C_eq_algebraMap]; rfl
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hNne : N ≠ 0 := by
    rw [hN, Ne,
      IsLocalization.integerNormalization_eq_zero_iff (M := nonZeroDivisors R) (le_refl _)]
    exact hsK0
  have hcontent0 : N.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hφc : φ N.content ≠ 0 :=
    fun h => hcontent0 (IsFractionRing.injective R K (by rwa [map_zero]))
  have hφb : φ b ≠ 0 := fun h => hb0 (IsFractionRing.injective R K (by rwa [map_zero]))
  have heq : Polynomial.C (φ N.content) * r.map φ = Polynomial.C (φ b) * sK :=
    hmap.symm.trans hbsmul
  set c := φ b * (φ N.content)⁻¹ with hc
  have hcunit : IsUnit c := IsUnit.mul (Ne.isUnit hφb) (IsUnit.inv (Ne.isUnit hφc))
  have hrmap : r.map φ = Polynomial.C c * sK := by
    rw [hc, show (Polynomial.C (φ b * (φ N.content)⁻¹) : K[X])
          = Polynomial.C (φ b) * Polynomial.C ((φ N.content)⁻¹) by
          rw [← Polynomial.C_mul], mul_assoc]
    have hstep : r.map φ = Polynomial.C ((φ N.content)⁻¹) * (Polynomial.C (φ b) * sK) := by
      rw [← heq, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hφc, Polynomial.C_1,
        one_mul]
    rw [hstep]; ring
  have hrmap_sep : (r.map φ).Separable := by
    rw [hrmap]; exact hsep.unit_mul (Polynomial.isUnit_C.mpr hcunit)
  have hexpand_map : (Polynomial.expand R n r).map φ = Polynomial.C c * (g.map φ) := by
    rw [Polynomial.map_expand, hrmap, map_mul, Polynomial.expand_C, hexp]
  have hEprim : (Polynomial.expand R n r).IsPrimitive := eq512_isPrimitive_expand hrprim hn
  have hdvd1 : (Polynomial.expand R n r).map φ ∣ g.map φ := by
    rw [hexpand_map]
    exact (associated_unit_mul_left _ _ (Polynomial.isUnit_C.mpr hcunit)).dvd
  have hdvd2 : g.map φ ∣ (Polynomial.expand R n r).map φ := by
    rw [hexpand_map]; exact Dvd.intro_left _ rfl
  have hd1R : (Polynomial.expand R n r) ∣ g :=
    (hEprim.dvd_iff_fraction_map_dvd_fraction_map (K := K) hgprim).mpr hdvd1
  have hd2R : g ∣ (Polynomial.expand R n r) :=
    (hgprim.dvd_iff_fraction_map_dvd_fraction_map (K := K) hEprim).mpr hdvd2
  have hassoc : Associated (Polynomial.expand R n r) g := associated_of_dvd_dvd hd1R hd2R
  have hE_irr : Irreducible (Polynomial.expand R n r) := hassoc.symm.irreducible hg
  have hr_irr : Irreducible r := Polynomial.of_irreducible_expand hn.ne' hE_irr
  obtain ⟨w, hw⟩ := hassoc
  have hwunit : IsUnit (↑w : R[X]) := w.isUnit
  rw [Polynomial.isUnit_iff] at hwunit
  obtain ⟨u, hu_unit, hu_eq⟩ := hwunit
  exact ⟨r, u, hr_irr, hrmap_sep, hu_unit, by rw [← hw, hu_eq, mul_comm]⟩

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- *Per-factor descent for Eq. 5.12*: composes the field-side separable contraction
(`eq512_separable_contraction_over_fraction_field`) with the UFD descent
(`eq512_descent_of_fraction_field_contraction`). For a positive-`Y`-degree irreducible factor `g`
of a `ModifiedGuruswami` solution, it yields a primitive irreducible `r : F[Z][X][Y]` with separable
`K`-image, a contraction exponent `nn = q^m` (`q` the exponential characteristic), and an `R`-unit
`u`, satisfying `g = C u * expand R nn r`. -/
theorem eq512_factor_descent (g : F[Z][X][Y]) (hg : Irreducible g) (hdeg : g.natDegree ≠ 0) :
    ∃ (r : F[Z][X][Y]) (nn : ℕ) (u : F[Z][X]),
      Irreducible r ∧
      (r.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable ∧
      IsUnit u ∧ g = Polynomial.C u * (Polynomial.expand (F[Z][X]) nn r) := by
  obtain ⟨sK, mm, hsep, hexp⟩ := eq512_separable_contraction_over_fraction_field g hg hdeg
  set q := ringExpChar F with hq
  haveI hF : ExpChar F q := ringExpChar.expChar F
  have hn : 0 < q ^ mm := expChar_pow_pos F q mm
  have hgprim : g.IsPrimitive := hg.isPrimitive hdeg
  obtain ⟨r, u, hr_irr, hr_sep, hu_unit, heq⟩ :=
    eq512_descent_of_fraction_field_contraction g hg hgprim sK (q ^ mm) hn hsep hexp
  exact ⟨r, q ^ mm, u, hr_irr, hr_sep, hu_unit, heq⟩

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Zipped-list product bridge* for the Eq-5.12 assembly: a triple-list `L` of
`(factor, exponent, multiplicity)` yields three parallel lists (via the projections) whose zipped
indexed product over `Finset.range L.length` equals the `Multiset/List.prod` of the per-triple
bodies `(t.1.comp (X ^ t.2.1)) ^ t.2.2`. Proved by induction on `L`, peeling the head with
`Finset.prod_range_succ'` and `List.getD_cons_succ`. -/
theorem eq512_prod_range_triple_list (L : List (F[Z][X][Y] × ℕ × ℕ)) :
    (∏ i ∈ Finset.range (L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1)).length,
        (((L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1)).getD i 1).comp
            ((Polynomial.X : F[Z][X][Y]) ^
              ((L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.1)).getD i 0)))
          ^ ((L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.2)).getD i 0))
      = (L.map (fun t : F[Z][X][Y] × ℕ × ℕ =>
          (t.1.comp ((Polynomial.X : F[Z][X][Y]) ^ t.2.1)) ^ t.2.2)).prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.length_cons, List.prod_cons]
    rw [Finset.prod_range_succ']
    simp only [List.getD_cons_zero]
    have hstep :
        (∏ i ∈ Finset.range (t.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1)).length,
            (((a.1 :: t.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1)).getD (i+1) 1).comp
              ((Polynomial.X : F[Z][X][Y]) ^
                ((a.2.1 :: t.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.1)).getD (i+1) 0)))
              ^ ((a.2.2 :: t.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.2)).getD (i+1) 0))
          = (t.map (fun t : F[Z][X][Y] × ℕ × ℕ =>
              (t.1.comp ((Polynomial.X : F[Z][X][Y]) ^ t.2.1)) ^ t.2.2)).prod := by
      rw [← ih]
      apply Finset.prod_congr rfl
      intro i _
      rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    rw [hstep]
    exact mul_comm (t.map (fun t : F[Z][X][Y] × ℕ × ℕ =>
      (t.1.comp ((Polynomial.X : F[Z][X][Y]) ^ t.2.1)) ^ t.2.2)).prod
      ((a.1.comp ((Polynomial.X : F[Z][X][Y]) ^ a.2.1)) ^ a.2.2)

omit [DecidableEq (RatFunc F)] [Finite F] in
/-- Equation 5.12 from [BCIKS20].

NOTE (statement repair): the original formulation of this lemma was *vacuous*.
Because `∧` binds tighter than the bounded quantifier `∀ _ ∈ _,`, the entire
payload — separability of each `Rᵢ`, irreducibility of each `Rᵢ`, and the
factorization equation `Q = C · ∏ (Rᵢ.comp Xᶠ)^eᵢ` — was trapped inside the
`∀ eᵢ ∈ e, …` (and the nested `∀ Rᵢ ∈ R, …`) binders. The statement was then
satisfiable by the empty witnesses `C = …, R = [], f = [], e = []` (all three
length equalities collapse to `0 = 0` and `∀ eᵢ ∈ [], …` is vacuously true),
carrying no mathematical content whatsoever.

This re-parenthesizes to the intended reading of [BCIKS20, Eq. 5.12]: each
bounded quantifier and the final factorization equation is now a *separate*
top-level conjunct, so the factorization holds outside all of the binders.
No conjunct has been dropped or weakened; only the scoping was corrected.

OBSTRUCTION (statement still mis-specified — see `eq512_cartesian_product_blowup`).
After the scoping repair the lemma remains **unprovable as written** for a general
`ModifiedGuruswami` solution `Q`, for two independent reasons:

* *Cartesian (not zipped) product indexing.* The factorization conjunct is
  `Q = C · ∏ (Rᵢ ∈ R.toFinset) (fᵢ ∈ f.toFinset) (eᵢ ∈ e.toFinset), (Rᵢ.comp Xᶠⁱ)^eᵢ`,
  i.e. a product over the **Cartesian product** of three independent finsets, rather
  than the intended single index `∏ᵢ (Rᵢ.comp X^(f i))^(e i)` of [BCIKS20, Eq. 5.12]
  that *pairs* the `i`-th factor, exponent and multiplicity. Consequently each factor
  `Rᵢ` is forced to the common power `∑ (eᵢ ∈ e.toFinset)` and replicated across every
  `fᵢ ∈ f.toFinset`, so the equation can only reproduce a `Q` whose distinct irreducible
  factors share a single multiplicity and a single contraction exponent. The companion
  lemma `eq512_cartesian_product_blowup` (below) makes this concrete: the *intended*
  witnesses `R = [a, b]`, `f = [1, 1]`, `e = [1, 2]` for `Q = a · b²` instead evaluate
  the displayed product to `a³ · b³`. No choice of `C, R, f, e` satisfying the
  separability and irreducibility conjuncts reproduces a general factored `Q` (e.g.
  `g · h²` with `g ≠ h` distinct separable irreducibles).

* *Separability over the wrong ring (VERIFIED defect, bug #18 — see
  `eq512_strong_separable_unsat`).* The original conjunct `∀ Rᵢ ∈ R, Rᵢ.Separable` applied
  `Polynomial.Separable` to `Rᵢ : F[Z][X][Y]` over the **coefficient ring** `F[Z][X]`, which
  is *not a field*. By `separable_def`, this unfolds to a Bézout identity
  `a · Rᵢ + b · Rᵢ.derivative = 1` with `a, b : F[Z][X][Y]` — coprimality *in the polynomial
  ring* — which is **unsatisfiable** for genuinely-arising irreducible factors: the companion
  witness `eq512_strong_separable_unsat` proves that `Y² − X` (an irreducible, squarefree,
  fraction-field-separable factor of the shape a `ModifiedGuruswami` solution produces, since
  `D_Y Q < D_X / k` permits `Y`-degree ≥ 2) is **not** `Separable` over `F[Z][X]`, because
  `Separable.map` would force its `Z, X ↦ 0` image `Y²` to be squarefree. The paper means
  separability of `Rᵢ` over the *fraction field* `F(Z,X)`, equivalently nonvanishing of
  `discr_y` — precisely the form consumed by Claim 5.6 (`discr_of_irred_components_nonzero`,
  which evaluates `Bivariate.discr_y R`). This is the **repaired** conjunct below:
  `(Rᵢ.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable`. The binder structure
  `(C, R, f, e)` and conjunct count are unchanged, so all `.choose`/`.choose_spec.choose`
  consumers (Claim 5.6, Claim 5.7 in `Agreement.lean`) are unaffected.

The factorization conjunct uses the **zipped** indexed product
`∏ i ∈ Finset.range R.length, (Rᵢ.comp X^fᵢ)^eᵢ` (paper-faithful), repairing the earlier
Cartesian-product mis-indexing witnessed by `eq512_cartesian_product_blowup`. The separability
conjunct now reads over `FractionRing (F[Z][X])`, repairing the non-field-separability defect
witnessed by `eq512_strong_separable_unsat`.

PROOF (now complete). For each positive-`Y`-degree distinct irreducible factor `g` of `Q`
(`Q ≠ 0`, `UniqueFactorizationMonoid.normalizedFactors`), the field-side separable contraction
(`eq512_separable_contraction_over_fraction_field`, via `Irreducible.hasSeparableContraction` over
`K := FractionRing (F[Z][X])`) is descended back to a primitive irreducible `r : F[Z][X][Y]` with
separable `K`-image, exponent `nn = q^m`, and `R`-unit `u` such that `g = C u * expand R nn r`
(`eq512_factor_descent`, built from `eq512_descent_of_fraction_field_contraction`). The lists
`(R, f, e)` are read off the distinct positive-degree factors with `eᵢ` the UFD multiplicity
`normalizedFactors.count g ≥ 1`; the degree-0 normalized factors (each `C` of a prime), the unit
from `prod_normalizedFactors`, and the per-factor units `u` all fold into the single constant `C`.
The zipped indexed product is matched to the multiset product via `eq512_prod_range_triple_list`
and `Finset.prod_to_list`/`Finset.prod_multiset_count`. -/
lemma irreducible_factorization_of_gs_solution
    {k : ℕ}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (C : F[Z][X]) (R : List F[Z][X][Y]) (f : List ℕ) (e : List ℕ),
    R.length = f.length ∧
    f.length = e.length ∧
    (∀ eᵢ ∈ e, 1 ≤ eᵢ) ∧
    (∀ Rᵢ ∈ R,
        (Rᵢ.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable) ∧
    (∀ Rᵢ ∈ R, Irreducible Rᵢ) ∧
    Q = (Polynomial.C C) *
        ∏ i ∈ Finset.range R.length,
          ((R.getD i 1).comp ((Polynomial.X : F[Z][X][Y]) ^ f.getD i 0)) ^ e.getD i 0
    := by
  classical
  have hQ0 : Q ≠ 0 := h_gs.Q_ne_0
  set S : Multiset (F[Z][X][Y]) := UniqueFactorizationMonoid.normalizedFactors Q with hS
  -- positive-degree distinct factors
  set P : Finset (F[Z][X][Y]) := S.toFinset.filter (fun g => 0 < g.natDegree) with hP
  -- pick data
  have hpick : ∀ g : F[Z][X][Y],
      ∃ (r : F[Z][X][Y]) (nn : ℕ) (u : F[Z][X]),
        g ∈ P →
        (Irreducible r ∧
        (r.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable ∧
        IsUnit u ∧ g = Polynomial.C u * (Polynomial.expand (F[Z][X]) nn r)) := by
    intro g
    by_cases hg : g ∈ P
    · rw [hP, Finset.mem_filter] at hg
      obtain ⟨hgS, hgd⟩ := hg
      have hgmem : g ∈ S := Multiset.mem_toFinset.1 hgS
      have hg_irr : Irreducible g :=
        UniqueFactorizationMonoid.irreducible_of_normalized_factor (a := Q) g (hS ▸ hgmem)
      obtain ⟨r, nn, u, h1, h2, h3, h4⟩ := eq512_factor_descent g hg_irr hgd.ne'
      exact ⟨r, nn, u, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, 0, 1, fun hc => absurd hc hg⟩
  -- choice functions (total)
  choose rr nn uu hspec using hpick
  -- the unit-content z₀ from degree-0 factors
  have hdeg0 : ∃ z : F[Z][X],
      ∏ g ∈ S.toFinset.filter (fun g => ¬ 0 < g.natDegree), g ^ (S.count g)
        = Polynomial.C z := by
    refine ⟨∏ g ∈ S.toFinset.filter (fun g => ¬ 0 < g.natDegree),
      (g.coeff 0) ^ (S.count g), ?_⟩
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro g hg
    rw [Finset.mem_filter] at hg
    rw [map_pow]
    congr 1
    exact Polynomial.eq_C_of_natDegree_eq_zero (by omega)
  obtain ⟨z₀, hz₀⟩ := hdeg0
  -- positive-degree product split
  have hposprod :
      ∏ g ∈ P, g ^ (S.count g)
        = Polynomial.C (∏ g ∈ P, (uu g) ^ (S.count g))
          * ∏ g ∈ P, ((rr g).comp ((Polynomial.X : F[Z][X][Y]) ^ (nn g))) ^ (S.count g) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g hg
    have hgd := (hspec g hg).2.2.2
    nth_rewrite 1 [hgd]
    rw [Polynomial.expand_eq_comp_X_pow, map_pow]; ring
  -- S.prod = ∏ over toFinset
  have hSprod : S.prod = ∏ g ∈ S.toFinset, g ^ (S.count g) :=
    Finset.prod_multiset_count S
  -- split toFinset into P and complement
  have hsplit : ∏ g ∈ S.toFinset, g ^ (S.count g)
      = (∏ g ∈ P, g ^ (S.count g))
        * (∏ g ∈ S.toFinset.filter (fun g => ¬ 0 < g.natDegree), g ^ (S.count g)) := by
    rw [hP]
    exact (Finset.prod_filter_mul_prod_filter_not S.toFinset (fun g => 0 < g.natDegree)
      (fun g => g ^ (S.count g))).symm
  -- association Q = C w * S.prod
  have hassoc : Associated S.prod Q := by
    rw [hS]; exact UniqueFactorizationMonoid.prod_normalizedFactors hQ0
  obtain ⟨w, hw⟩ := hassoc  -- S.prod * ↑w = Q
  have hwunit : IsUnit (↑w : F[Z][X][Y]) := w.isUnit
  rw [Polynomial.isUnit_iff] at hwunit
  obtain ⟨wc, hwc_unit, hwc_eq⟩ := hwunit
  -- build the triple list from P.toList
  set L : List (F[Z][X][Y] × ℕ × ℕ) :=
    P.toList.map (fun g => (rr g, nn g, S.count g)) with hL
  refine ⟨wc * z₀ * (∏ g ∈ P, (uu g) ^ (S.count g)),
    L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1),
    L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.1),
    L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.2),
    by simp only [List.length_map],
    by simp only [List.length_map],
    ?_, ?_, ?_, ?_⟩
  · -- ∀ eᵢ ∈ e, 1 ≤ eᵢ
    intro eᵢ hmem
    rw [hL] at hmem
    simp only [List.map_map, List.mem_map, Finset.mem_toList] at hmem
    obtain ⟨g, hgP, rfl⟩ := hmem
    simp only [Function.comp]
    have hgmem : g ∈ S := by
      rw [hP, Finset.mem_filter] at hgP
      exact Multiset.mem_toFinset.1 hgP.1
    exact Multiset.count_pos.2 hgmem
  · -- separable
    intro Rᵢ hmem
    rw [hL] at hmem
    simp only [List.map_map, List.mem_map, Finset.mem_toList] at hmem
    obtain ⟨g, hgP, rfl⟩ := hmem
    simp only [Function.comp]
    exact (hspec g hgP).2.1
  · -- irreducible
    intro Rᵢ hmem
    rw [hL] at hmem
    simp only [List.map_map, List.mem_map, Finset.mem_toList] at hmem
    obtain ⟨g, hgP, rfl⟩ := hmem
    simp only [Function.comp]
    exact (hspec g hgP).1
  · -- the factorization equation
    -- product over range = list product (bridge) = ∏ over P of body
    have hbridge := eq512_prod_range_triple_list L
    -- list product = ∏_{g∈P} body g
    have hlistP :
        (L.map (fun t : F[Z][X][Y] × ℕ × ℕ =>
          (t.1.comp ((Polynomial.X : F[Z][X][Y]) ^ t.2.1)) ^ t.2.2)).prod
          = ∏ g ∈ P, ((rr g).comp ((Polynomial.X : F[Z][X][Y]) ^ (nn g))) ^ (S.count g) := by
      rw [hL, List.map_map]
      exact Finset.prod_map_toList P
        (fun g => ((rr g).comp ((Polynomial.X : F[Z][X][Y]) ^ (nn g))) ^ (S.count g))
    -- assemble Q
    rw [List.length_map]
    -- the range product equals ∏_P body
    have hrangeP :
        (∏ i ∈ Finset.range L.length,
          (((L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1)).getD i 1).comp
            ((Polynomial.X : F[Z][X][Y]) ^
              ((L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.1)).getD i 0)))
            ^ ((L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.2.2)).getD i 0))
          = ∏ g ∈ P, ((rr g).comp ((Polynomial.X : F[Z][X][Y]) ^ (nn g))) ^ (S.count g) := by
      have hlen : (L.map (fun t : F[Z][X][Y] × ℕ × ℕ => t.1)).length = L.length :=
        List.length_map _
      rw [← hlen]
      rw [hbridge, hlistP]
    rw [hrangeP]
    -- Q = C wc * S.prod ... build it
    have hQval : Q = S.prod * Polynomial.C wc := by rw [hwc_eq, hw]
    rw [hQval, hSprod, hsplit, hposprod, hz₀]
    rw [show wc * z₀ * (∏ g ∈ P, (uu g) ^ (S.count g))
          = (∏ g ∈ P, (uu g) ^ (S.count g)) * z₀ * wc by ring]
    rw [map_mul, map_mul]
    ring


omit [DecidableEq (RatFunc F)] in
/-- Claim 5.6 of [BCIKS20]. -/
lemma discr_of_irred_components_nonzero (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∃ x₀,
      ∀ R ∈ (irreducible_factorization_of_gs_solution _h_gs).choose_spec.choose,
      Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

noncomputable def pg_Rset (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F[Z][X][Y] :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_Rset_irreducible (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs →
      Irreducible R := by
  intro R hR
  classical
  -- unfold the definition of `pg_Rset`
  unfold pg_Rset at hR
  -- `hR` is membership in the `toFinset` of the multiset of normalized factors
  have hR' : R ∈ UniqueFactorizationMonoid.normalizedFactors Q := by
    simpa using hR
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor (a := Q) R hR'

noncomputable def pg_candidatePairs
    (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Finset (F[Z][X][Y] × F[Z][X]) :=
  let Rset := pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs
  Rset.biUnion (fun R =>
    (UniqueFactorizationMonoid.normalizedFactors
        (Bivariate.evalX (Polynomial.C x₀) R)).toFinset.image (fun H => (R, H)))

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_card_normalizedFactors_toFinset_le_natDegree (p : F[Z][X]) (hp : p.Separable) :
    #((UniqueFactorizationMonoid.normalizedFactors p).toFinset) ≤ p.natDegree := by
  classical
  let s : Multiset (F[Z][X]) := UniqueFactorizationMonoid.normalizedFactors p
  have hs0 : (0 : F[Z][X]) ∉ s := by
    simpa [s] using (UniqueFactorizationMonoid.zero_notMem_normalizedFactors p)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpos : ∀ q ∈ s, 1 ≤ q.natDegree := by
    intro q hq
    have hq' : q ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      simpa [s] using hq
    have hq_irred : Irreducible q :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq'
    have hq_dvd : q ∣ p :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq'
    have hq_sep : q.Separable :=
      Polynomial.Separable.of_dvd hp hq_dvd
    have hq_natDegree_ne_zero : q.natDegree ≠ 0 := by
      intro hdeg0
      have hconst : q = Polynomial.C (q.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hdeg0
      have hsepC : (Polynomial.C (q.coeff 0) : F[Z][X]).Separable := by
        -- rewrite `hq_sep` using `hconst`
        exact hconst ▸ hq_sep
      have hunitCoeff : IsUnit (q.coeff 0) :=
        (Polynomial.separable_C (q.coeff 0)).1 hsepC
      have hunitC : IsUnit (Polynomial.C (q.coeff 0) : F[Z][X]) :=
        (Polynomial.isUnit_C).2 hunitCoeff
      have hunit : IsUnit q := by
        -- rewrite back using `hconst`
        exact hconst.symm ▸ hunitC
      exact hq_irred.not_isUnit hunit
    exact Nat.one_le_iff_ne_zero.2 hq_natDegree_ne_zero
  have hcard_le_sum : s.card ≤ (s.map Polynomial.natDegree).sum := by
    -- prove a general statement by induction
    have : (∀ q ∈ s, 1 ≤ q.natDegree) → s.card ≤ (s.map Polynomial.natDegree).sum := by
      refine Multiset.induction_on s ?_ ?_
      · intro _
        simp
      · intro a t ih ht
        have ha : 1 ≤ a.natDegree := ht a (by simp)
        have ht' : ∀ q ∈ t, 1 ≤ q.natDegree := by
          intro q hq
          exact ht q (Multiset.mem_cons_of_mem hq)
        have ih' : t.card ≤ (t.map Polynomial.natDegree).sum := ih ht'
        have hstep : t.card + 1 ≤ (t.map Polynomial.natDegree).sum + a.natDegree :=
          Nat.add_le_add ih' ha
        -- rewrite goal
        simpa [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, Nat.add_comm] using hstep
    exact this hpos
  have hassoc : Associated s.prod p := by
    simpa [s] using (UniqueFactorizationMonoid.prod_normalizedFactors (a := p) hp0)
  have hnatDegree_prod : s.prod.natDegree = p.natDegree := by
    apply Polynomial.natDegree_eq_of_degree_eq
    exact Polynomial.degree_eq_degree_of_associated hassoc
  have hcard_le : s.card ≤ p.natDegree := by
    have hnat : s.prod.natDegree = (s.map Polynomial.natDegree).sum :=
      Polynomial.natDegree_multiset_prod (t := s) hs0
    have h1 : s.card ≤ s.prod.natDegree := by
      simpa [hnat.symm] using hcard_le_sum
    simpa [hnatDegree_prod] using h1
  have hfin : #s.toFinset ≤ p.natDegree :=
    (Multiset.toFinset_card_le (m := s)).trans hcard_le
  simpa [s] using hfin

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_evalX_eq_map_evalRingHom (x₀ : F) (R : F[Z][X][Y]) :
    Bivariate.evalX (Polynomial.C x₀) R = R.map (Polynomial.evalRingHom (Polynomial.C x₀)) := by
  classical
  ext n n'
  · simp [Bivariate.evalX, Polynomial.coeff_map]
    simp [Polynomial.coeff]

open scoped Polynomial.Bivariate in
noncomputable def pg_eval_on_Z (p : F[Z][X][Y]) (z : F) : Polynomial (Polynomial F) :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

omit [DecidableEq (RatFunc F)] in
theorem pg_exists_H_of_R_eval_zero (δ : ℚ) (x₀ : F)
    (_h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁)
  (R : F[Z][X][Y]) :
  let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  (pg_eval_on_Z (F := F) R z.1).eval P = 0 →
  Bivariate.evalX (Polynomial.C x₀) R ≠ 0 →
  ∃ H,
    H ∈ UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) ∧
    (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
  classical
  dsimp
  set P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2 with hP
  intro hR hNZ
  -- handy lemma: ArkLib's `Bivariate.evalX` agrees with `Polynomial.map` via `evalRingHom`.
  have evalX_eq_map {R : Type} [CommSemiring R] (a : R) (f : Polynomial (Polynomial R)) :
      Bivariate.evalX a f = f.map (Polynomial.evalRingHom a) := by
    ext n
    simp [Bivariate.evalX, Polynomial.coeff_map]
    simp [Polynomial.coeff]
  -- abbreviate p := evalX at x₀ (this is a bivariate poly in Z,Y)
  set p := Bivariate.evalX (Polynomial.C x₀) R with hp
  have hp_root : (Bivariate.evalX z.1 p).eval (P.eval x₀) = 0 := by
    -- evaluate the hypothesis at x₀
    have hx : ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ = 0 := by
      have := congrArg (fun g : F[X] => g.eval x₀) hR
      simpa using this
    -- set up abbreviations
    let fZ : F[X] →+* F := Polynomial.evalRingHom z.1
    let q : F[Z][X] := P.map (Polynomial.C)
    let r : F[X] := Polynomial.C x₀
    have hqmap : q.map fZ = P := by
      -- `(P.map C).map fZ = P.map (fZ.comp C)` and `fZ.comp C = id`.
      have hf : fZ.comp (Polynomial.C) = (RingHom.id F) := by
        ext a
        simp [fZ]
      -- now simplify
      simp [q, Polynomial.map_map, hf]
    have hr : fZ r = x₀ := by
      simp [fZ, r]
    -- rewrite the left-hand evaluation using `map_mapRingHom_eval_map_eval`
    have hcommZ : ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ = fZ ((R.eval q).eval r) := by
      have h := Polynomial.map_mapRingHom_eval_map_eval (f := fZ) (p := R) (q := q) r
      simpa [pg_eval_on_Z, fZ, hqmap, hr] using h
    have hfz0 : fZ ((R.eval q).eval r) = 0 := by
      -- combine `hx` and `hcommZ`
      calc
        fZ ((R.eval q).eval r) = ((pg_eval_on_Z (F := F) R z.1).eval P).eval x₀ := by
          simp [hcommZ]
        _ = 0 := hx
    -- show `fZ ((R.eval q).eval r)` is the desired evaluation of `p`
    have hp_map : p = R.map (Polynomial.evalRingHom (Polynomial.C x₀)) := by
      exact hp.trans (pg_evalX_eq_map_evalRingHom (F := F) x₀ R)
    -- commute evaluation in Y then X with evaluation in X then Y
    have hYX : (R.eval q).eval r = (p.eval (q.eval r)) := by
      have h := (Polynomial.eval₂_hom (p := R) (f := Polynomial.evalRingHom r) q)
      have h' : (R.map (Polynomial.evalRingHom r)).eval ((Polynomial.evalRingHom r) q) =
          (Polynomial.evalRingHom r) (R.eval q) := by
        simpa [Polynomial.eval₂_eq_eval_map] using h
      have h'' : (R.eval q).eval r = (R.map (Polynomial.evalRingHom r)).eval (q.eval r) := by
        simpa [Polynomial.coe_evalRingHom] using h'.symm
      simpa [hp_map, Polynomial.coe_evalRingHom] using h''
    have hfz_eq : fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := by
      have : fZ ((R.eval q).eval r) = fZ (p.eval (q.eval r)) := by
        simp [hYX]
      have h := (Polynomial.eval₂_hom (p := p) (f := fZ) (q.eval r))
      have h' : (p.map fZ).eval (fZ (q.eval r)) = fZ (p.eval (q.eval r)) := by
        simp
      simp [this]
    have hfz_q : fZ (q.eval r) = P.eval x₀ := by
      simp [fZ, q, r]
    have hp_eval_as : fZ ((R.eval q).eval r) = (Bivariate.evalX z.1 p).eval (P.eval x₀) := by
      have : Bivariate.evalX z.1 p = p.map fZ := by
        simpa [fZ] using (evalX_eq_map (R := F) z.1 p)
      calc
        fZ ((R.eval q).eval r) = (p.map fZ).eval (fZ (q.eval r)) := hfz_eq
        _ = (p.map fZ).eval (P.eval x₀) := by simp [hfz_q]
        _ = (Bivariate.evalX z.1 p).eval (P.eval x₀) := by simp [this]
    -- finish
    calc
      (Bivariate.evalX z.1 p).eval (P.eval x₀) = fZ ((R.eval q).eval r) := by
        simp [hp_eval_as]
      _ = 0 := hfz0
  -- use normalized factorization of nonzero p
  have hAssoc : Associated (UniqueFactorizationMonoid.normalizedFactors p).prod p :=
    UniqueFactorizationMonoid.prod_normalizedFactors (a := p) hNZ
  let φ : _ →+* F :=
    (Polynomial.evalRingHom (P.eval x₀)).comp (Polynomial.mapRingHom (Polynomial.evalRingHom z.1))
  have hφp : φ p = 0 := by
    -- rewrite `hp_root` using `evalX_eq_map` and unfold `φ`
    have hp_root' : (p.map (Polynomial.evalRingHom z.1)).eval (P.eval x₀) = 0 := by
      simpa [evalX_eq_map (R := F) z.1 p] using hp_root
    simpa [φ] using hp_root'
  have hφprod : φ (UniqueFactorizationMonoid.normalizedFactors p).prod = 0 := by
    have hAssoc' : Associated (φ (UniqueFactorizationMonoid.normalizedFactors p).prod) (φ p) :=
      Associated.map (φ : _ →* F) hAssoc
    have : φ (UniqueFactorizationMonoid.normalizedFactors p).prod = 0 ↔ φ p = 0 :=
      hAssoc'.eq_zero_iff
    exact this.mpr hφp
  have hmap_prod : ((UniqueFactorizationMonoid.normalizedFactors p).map φ).prod = 0 := by
    simpa [map_multiset_prod] using hφprod
  have hmem0 : (0 : F) ∈ (UniqueFactorizationMonoid.normalizedFactors p).map φ := by
    exact (Multiset.prod_eq_zero_iff).1 hmap_prod
  rcases (Multiset.mem_map.1 hmem0) with ⟨H, hHmem, hHφ⟩
  refine ⟨H, hHmem, ?_⟩
  -- turn the `φ`-evaluation into the desired statement
  have hHφ' : (H.map (Polynomial.evalRingHom z.1)).eval (P.eval x₀) = 0 := by
    simpa [φ] using hHφ
  simpa [evalX_eq_map (R := F) z.1 H] using hHφ'

omit [DecidableEq (RatFunc F)] in
theorem pg_exists_R_of_Q_eval_zero (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
  let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  (pg_eval_on_Z (F := F) Q z.1).eval P = 0 →
  ∃ R,
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs ∧
    (pg_eval_on_Z (F := F) R z.1).eval P = 0 := by
  classical
  dsimp
  intro hQ
  set P : F[X] :=
    Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  have hQ' : (pg_eval_on_Z (F := F) Q z.1).eval P = 0 := by
    simpa [P] using hQ
  -- Define the ring hom φ : F[Z][X][Y] →+* F[X]
  let evZ : F[Z][X] →+* F[X] := Polynomial.mapRingHom (Polynomial.evalRingHom z.1)
  let evZ' : F[Z][X][Y] →+* Polynomial (Polynomial F) := Polynomial.mapRingHom evZ
  let φ : F[Z][X][Y] →+* F[X] := (Polynomial.evalRingHom P).comp evZ'
  have hφQ : φ Q = 0 := by
    simpa [φ, evZ', evZ, pg_eval_on_Z] using hQ'
  -- Use associated product of normalizedFactors
  have hassoc : Associated ((UniqueFactorizationMonoid.normalizedFactors Q).prod) Q :=
    UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) h_gs.Q_ne_0
  rcases hassoc with ⟨u, hu⟩
  -- Apply φ to the equation
  have hmul : φ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) * φ (↑u) = 0 := by
    have h := congrArg φ hu
    have h' :
        φ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) * φ (↑u) = φ Q := by
      simpa [map_mul] using h
    simpa [hφQ] using h'
  -- φ (↑u) is a unit hence nonzero, so the other factor is 0
  have hu_ne0 : φ (↑u : F[Z][X][Y]) ≠ (0 : F[X]) := by
    have hu_unit : IsUnit (φ (↑u : F[Z][X][Y])) := (RingHom.isUnit_map φ) u.isUnit
    exact IsUnit.ne_zero hu_unit
  have hprod0 : φ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_right hu_ne0
  -- rewrite φ(prod) as product over mapped factors
  have hprod0' : ((UniqueFactorizationMonoid.normalizedFactors Q).map φ).prod = 0 := by
    simpa [map_multiset_prod] using hprod0
  -- extract some factor with φ R = 0
  have hz0 : (0 : F[X]) ∈ (UniqueFactorizationMonoid.normalizedFactors Q).map φ := by
    exact (Multiset.prod_eq_zero_iff).1 hprod0'
  rcases (Multiset.mem_map.1 hz0) with ⟨R, hRmem, hR0⟩
  refine ⟨R, ?_, ?_⟩
  · -- show R ∈ pg_Rset = (normalizedFactors Q).toFinset
    dsimp [pg_Rset]
    exact (Multiset.mem_toFinset).2 hRmem
  · -- show (pg_eval_on_Z R z.1).eval P = 0
    simpa [φ, evZ', evZ, pg_eval_on_Z] using hR0

omit [DecidableEq (RatFunc F)] in
theorem pg_exists_pair_for_z (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (hx0 : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs →
      Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
  (z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁) :
  let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  (pg_eval_on_Z (F := F) Q z.1).eval P = 0 →
  ∃ R H,
    (R, H) ∈ pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) x₀ h_gs ∧
    let P : F[X] := Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
    (pg_eval_on_Z (F := F) R z.1).eval P = 0 ∧
    (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
  classical
  -- Unfold the outer `let P := ...` so we can introduce the hypothesis.
  simp only
  intro hQ
  -- Name the interpolation polynomial associated to `z`.
  let P : F[X] :=
    Pz (k := k) (ωs := ωs) (δ := δ) (u₀ := u₀) (u₁ := u₁) z.2
  have hQ' : (pg_eval_on_Z (F := F) Q z.1).eval P = 0 := by
    simpa [P] using hQ
  -- 1) Extract `R ∈ pg_Rset` with the same vanishing property.
  have hRfun :=
    (pg_exists_R_of_Q_eval_zero (F := F) (k := k) (δ := δ) (h_gs := h_gs) (z := z))
  have hR' :
      ∃ R,
        R ∈
            pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁)
              h_gs ∧
          (pg_eval_on_Z (F := F) R z.1).eval P = 0 := by
    -- `hRfun` has a `let P := ...` binder; rewrite using our local `P`.
    simpa [P] using hRfun hQ'
  obtain ⟨R, hRmem, hRzero⟩ := hR'
  -- 2) Nonzeroness of `evalX` at `x₀` from the hypothesis `hx0`.
  have hNZ : Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
    hx0 R hRmem
  -- 3) Extract a normalized factor `H` of `evalX x₀ R` with the desired vanishing.
  have hHfun :=
    (pg_exists_H_of_R_eval_zero (F := F) (k := k) (δ := δ) (x₀ := x₀) (_h_gs := h_gs)
      (z := z) (R := R))
  have hH' :
      ∃ H,
        H ∈
            UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) ∧
          (Bivariate.evalX z.1 H).eval (P.eval x₀) = 0 := by
    simpa [P] using hHfun hRzero hNZ
  obtain ⟨H, hHmem, hHzero⟩ := hH'
  -- 4) Show `(R, H)` lies in `pg_candidatePairs`.
  have hPairMem :
      (R, H) ∈
        pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁)
          x₀ h_gs := by
    have h' :
        R ∈
            pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁)
              h_gs ∧
          H ∈
            UniqueFactorizationMonoid.normalizedFactors (Bivariate.evalX (Polynomial.C x₀) R) :=
      And.intro hRmem hHmem
    simpa [pg_candidatePairs] using h'
  -- 5) Package everything.
  refine ⟨R, H, hPairMem, ?_⟩
  -- Discharge the inner `let P := ...` binder using our local `P`.
  simpa [P] using And.intro hRzero hHzero


omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_natDegree_evalX_le_natDegreeY (x₀ : F) (R : F[Z][X][Y]) :
    (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ Bivariate.natDegreeY R := by
  classical
  -- Rewrite `evalX` in terms of `map`.
  rw [pg_evalX_eq_map_evalRingHom (x₀ := x₀) (R := R)]
  -- `natDegreeY` is definitional.
  unfold Bivariate.natDegreeY
  -- Apply the standard degree bound for `Polynomial.map`.
  simpa using
    (Polynomial.natDegree_map_le (p := R)
      (f := Polynomial.evalRingHom (Polynomial.C x₀)))

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_sum_natDegreeY_Rset_le_natDegreeY_Q (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Finset.sum (pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs)
      (fun R => Bivariate.natDegreeY R)
    ≤ Bivariate.natDegreeY Q := by
  classical
  -- Unfold the definition of `pg_Rset`.
  simp only [pg_Rset]
  -- Abbreviate the multiset of normalized factors.
  set s : Multiset F[Z][X][Y] := UniqueFactorizationMonoid.normalizedFactors Q with hs
  -- Rewrite the goal in terms of `s`.
  simp only [hs, ge_iff_le]
  have hQ0 : Q ≠ 0 := h_gs.Q_ne_0
  have hs0 : (0 : F[Z][X][Y]) ∉ s := by
    simpa [hs] using (UniqueFactorizationMonoid.zero_notMem_normalizedFactors (x := Q))
  have hsum_le :
      Finset.sum s.toFinset (fun R => Bivariate.natDegreeY R)
        ≤ Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R) := by
    refine Finset.sum_le_sum ?_
    intro R hR
    have hmem : R ∈ s := (Multiset.mem_toFinset.1 hR)
    have hcount : 0 < s.count R := (Multiset.count_pos.2 hmem)
    exact Nat.le_mul_of_pos_left (Bivariate.natDegreeY R) hcount
  have hsum_count :
      Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R) =
        (s.map fun R => Bivariate.natDegreeY R).sum := by
    simpa [Nat.nsmul_eq_mul] using
      (Finset.sum_multiset_map_count (s := s) (f := fun R => Bivariate.natDegreeY R)).symm
  have hdeg_prod :
      (s.map fun R => Bivariate.natDegreeY R).sum = Bivariate.natDegreeY s.prod := by
    simpa [Bivariate.natDegreeY] using
      (Polynomial.natDegree_multiset_prod (t := s) hs0).symm
  have hfinset_eq_prod :
      Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R) =
        Bivariate.natDegreeY s.prod := by
    calc
      Finset.sum s.toFinset (fun R => s.count R * Bivariate.natDegreeY R)
          = (s.map fun R => Bivariate.natDegreeY R).sum := hsum_count
      _ = Bivariate.natDegreeY s.prod := hdeg_prod
  have hleft_le_prod :
      Finset.sum s.toFinset (fun R => Bivariate.natDegreeY R) ≤ Bivariate.natDegreeY s.prod := by
    simpa [hfinset_eq_prod] using hsum_le
  have hassoc : Associated s.prod Q := by
    -- `prod_normalizedFactors` gives association between the product of normalized factors and `Q`.
    simpa [hs] using (UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ0)
  have hdeg_assoc : (s.prod).degree = Q.degree :=
    Polynomial.degree_eq_degree_of_associated hassoc
  have hnat_assoc : (s.prod).natDegree = Q.natDegree :=
    Polynomial.natDegree_eq_natDegree (p := s.prod) (q := Q) hdeg_assoc
  have hnatY_assoc : Bivariate.natDegreeY s.prod = Bivariate.natDegreeY Q := by
    simp [Bivariate.natDegreeY, hnat_assoc]
  simpa [hnatY_assoc] using hleft_le_prod

omit [DecidableEq (RatFunc F)] [Finite F] in
theorem pg_card_candidatePairs_le_natDegreeY (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hsep : ∀ R : F[Z][X][Y],
    R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs →
      (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    :
  #(pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
      (u₀ := u₀) (u₁ := u₁) x₀ h_gs) ≤ Bivariate.natDegreeY Q := by
  classical
  -- Shorthands for the set of candidate polynomials `R` and the corresponding set of
  -- pairs for each `R`.
  set Rset : Finset F[Z][X][Y] :=
    pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs with hRset
  set t : F[Z][X][Y] → Finset (F[Z][X][Y] × F[Z][X]) := fun R =>
    (UniqueFactorizationMonoid.normalizedFactors
        (Bivariate.evalX (Polynomial.C x₀) R)).toFinset.image (fun H => (R, H)) with ht
  -- Unfold `pg_candidatePairs` as a `biUnion` over `Rset`.
  have hcp :
      pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) x₀ h_gs
        = Rset.biUnion t := by
    simp [pg_candidatePairs, pg_Rset, hRset, ht]
  -- Cardinality bound for a `biUnion`.
  have hcard_biUnion :
      #(pg_candidatePairs (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) x₀ h_gs)
        ≤ ∑ R ∈ Rset, #(t R) := by
    simpa [hcp] using (Finset.card_biUnion_le (s := Rset) (t := t))
  -- Pointwise bound: for each `R ∈ Rset`, `#(t R)` is bounded by `natDegreeY R`.
  have hpoint : ∀ R : F[Z][X][Y], R ∈ Rset → #(t R) ≤ Bivariate.natDegreeY R := by
    intro R hR
    -- `t R` is an injective image of the factor set.
    have hinj : Function.Injective (fun H : F[Z][X] => (R, H)) := by
      intro H1 H2 h
      simpa using congrArg Prod.snd h
    have hcard_image :
        #(t R) =
          #((UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset) := by
      simpa [ht] using
        (Finset.card_image_of_injective
          (s := (UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset)
          (f := fun H : F[Z][X] => (R, H)) hinj)
    have hR' : R ∈
        pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs := by
      simpa [hRset] using hR
    have hcard_nf :
        #((UniqueFactorizationMonoid.normalizedFactors
            (Bivariate.evalX (Polynomial.C x₀) R)).toFinset)
          ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree :=
      pg_card_normalizedFactors_toFinset_le_natDegree (F := F)
        (p := (Bivariate.evalX (Polynomial.C x₀) R)) (hp := hsep R hR')
    have hdeg : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ Bivariate.natDegreeY R :=
      pg_natDegree_evalX_le_natDegreeY (F := F) x₀ R
    -- Combine the bounds.
    calc
      #(t R) =
          #((UniqueFactorizationMonoid.normalizedFactors
              (Bivariate.evalX (Polynomial.C x₀) R)).toFinset) := hcard_image
      _ ≤ (Bivariate.evalX (Polynomial.C x₀) R).natDegree := hcard_nf
      _ ≤ Bivariate.natDegreeY R := hdeg
  have hsum : (∑ R ∈ Rset, #(t R)) ≤ ∑ R ∈ Rset, Bivariate.natDegreeY R := by
    refine Finset.sum_le_sum ?_
    intro R hR
    exact hpoint R hR
  have hsum_Rset_le : (∑ R ∈ Rset, Bivariate.natDegreeY R) ≤ Bivariate.natDegreeY Q := by
    -- This is exactly the provided degree bound, after rewriting `Rset`.
    simpa [hRset] using
      (pg_sum_natDegreeY_Rset_le_natDegreeY_Q (m := m) (n := n) (k := k)
        (ωs := ωs) (Q := Q) (u₀ := u₀) (u₁ := u₁) h_gs)
  -- Put everything together.
  exact (hcard_biUnion.trans (hsum.trans hsum_Rset_le))

end BCIKS20ProximityGapSection5

end ProximityGap
