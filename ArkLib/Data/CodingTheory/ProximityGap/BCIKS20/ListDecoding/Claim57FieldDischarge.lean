/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.Claim57Supply
import ArkLib.ToMathlib.Section5ConcreteJohnson

/-!
# Claim 5.7 residual bundle — per-field discharge brick (BCIKS20 §5)

`ProximityGap.Claim57Residuals` (`Agreement.lean`) is the typed input bundle gating the BCIKS20
Claim-5.7 keystone.  Its eight fields are
`hx0`, `hsep`, `hS_nonempty`, `A`, `hA`, `hcount`, `hlarge`, `hfactor`.  This file is the *honest
per-field discharge brick*: for each field it either supplies a genuine proof from in-tree
substrate, reduces it to a strictly more primitive named §5 hypothesis (with citation), or records
the precise structural reason the field is *not* dischargeable outright.

Two upstream supply files already did substantial work, which this brick builds on rather than
duplicates:

* `Claim57Supply.lean` (`claim57Residuals_of_johnson` /
  `claim57Residuals_of_natCeil_johnson`) canonicalises `A := matching_coords_for_z`, making `hA`
  automatic, derives `hS_nonempty` from `hlarge`, and reduces `hcount` to the per-`z` Johnson
  counting inequality.
* `Section5ConcreteJohnson.lean` (`claim57Residuals_of_gsInterpolant`) further reduces the per-`z`
  `hcount` to the **single** `z`-independent Johnson budget `hJohnson` on the GS interpolant via
  `BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le`.

So `A`/`hA`/`hcount`/`hS_nonempty` are **already discharged** upstream.  The genuinely-remaining
inputs that those assemblers carry as raw hypotheses are exactly `hx0`, `hsep`, `hlarge`, and
`hfactor`.  This file addresses those:

## Per-field verdict

* **`hfactor`** — *reduced to a named hypothesis with a structural impossibility note; the provable
  fragment is supplied.*  `pg_Rset h_gs = (normalizedFactors Q).toFinset`
  (`Extraction.pg_Rset`), whereas `(irreducible_factorization_of_gs_solution h_gs).choose_spec.choose`
  is the list of **descended primitive separable** factors `r` produced by `eq512_factor_descent`,
  where each *positive-degree* normalized factor `g` satisfies `g = C u · expand nn r`.  These two
  factor families coincide only when every factor is separable with `nn = 1` (e.g. characteristic
  `0`); in characteristic `p` an inseparable normalized factor `g` is a proper `p`-power image of
  its descended root `r ≠ g`, and degree-`0` normalized factors are dropped entirely.  Hence
  `hfactor` (`R ∈ pg_Rset → R ∈ descended list`) is **not provable outright**.  We supply the
  honestly-provable fragment `claim57_hfactor_irreducible_of_pg_Rset` (every `pg_Rset` member is
  irreducible) and keep `hfactor` itself as the documented bridge hypothesis.

* **`hx0` / `hsep`** — *reduced to the discriminant-nonvanishing substrate plus a named separability
  bridge.*  `exists_good_x₀_evalX_discr_y_ne` proves, **outright**, the Claim-5.6 specialization
  step over `pg_Rset`: under the honest per-factor side conditions that each `pg_Rset` factor is
  positive-`Y`-degree and fraction-field separable (the inseparability side condition flagged in
  the issue, exposed rather than faked), and a field-size bound, there exists `x₀ : F` with
  `evalX x₀ (discr_y R) ≠ 0` for every `R ∈ pg_Rset`.  The final step turning
  `evalX x₀ (discr_y R) ≠ 0` into the `hx0`/`hsep` field shapes
  (`evalX (C x₀) R ≠ 0` and `(evalX (C x₀) R).Separable`) needs the discriminant/specialization
  commutation `discr (evalX (C x₀) R) = evalX x₀ (discr_y R)` together with the
  `discr ≠ 0 ⟹ Separable` converse, neither of which is currently available in tree (only the
  forward `discr_ne_zero_of_separable_field` is); these are exposed as the named bridge hypotheses
  `hx0`/`hsep` themselves.

* **`hcount` / `hA` / `A`** — *already discharged upstream* (`Claim57Supply.lean`).  Re-exported
  here only through the assembled constructor.

* **`hS_nonempty` / `hlarge`** — *`hS_nonempty` already derived from `hlarge`*
  (`coeffs_of_close_proximity_nonempty_of_large_natdiv`); `hlarge` is the genuine §5 close-set
  largeness / field-size-budget input (the `Pr > ε` contrapositive datum) and stays a named
  hypothesis, matching the consuming shape in `CurvesBridge`/`Section5ConcreteJohnson`.

* **Assembly** — `Claim57Residuals.ofInTree` collects the minimal honest remaining hypotheses
  (`hx0`, `hsep`, the single Johnson budget `hJohnson`, `hlarge`, `hfactor`) into the full bundle
  via the proven upstream `claim57Residuals_of_gsInterpolant`.

No `sorry`/`axiom`/`native_decide`.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (Claim 5.6 — good specialization point; Claim 5.7 — graph extraction; Lemma 5.3 —
  Johnson-radius GS parameter bound; Eq. 5.12 — separable factorization of the GS solution).
-/

-- Documentation-heavy file (BCIKS §5 prose in the docstrings); the long-line style linter is
-- disabled locally, matching the sibling supply files.
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

/-! ## Field `hfactor` — the provable fragment

`pg_Rset` membership gives irreducibility (the only part of the `hfactor` story that survives the
`normalizedFactors`-vs-descended-list mismatch documented above).  This is a thin re-export of
`Extraction.pg_Rset_irreducible` under a Claim-5.7-named handle, so downstream code that needs the
irreducibility of a `pg_Rset` factor does not have to thread `hfactor` (which is about list
membership, not irreducibility). -/

omit [DecidableEq (RatFunc F)] in
/-- **`hfactor`, provable fragment.**  Every member of `pg_Rset h_gs` is irreducible.

This is the genuinely-true content extractable from `pg_Rset`.  The full `hfactor` field of
`Claim57Residuals` — membership of a `pg_Rset` factor in the descended Eq-5.12 separable factor
list — is *not* provable outright (see the module docstring: `normalizedFactors Q` and the descended
primitive list differ under inseparability / for degree-`0` factors), and is therefore kept as a
named bridge hypothesis. -/
theorem claim57_hfactor_irreducible_of_pg_Rset
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (R : F[Z][X][Y])
    (hR : R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs) :
    Irreducible R :=
  pg_Rset_irreducible (F := F) (m := m) (n := n) (k := k) (Q := Q)
    (ωs := ωs) (u₀ := u₀) (u₁ := u₁) h_gs R hR

/-! ## Fields `hx0` / `hsep` — the Claim-5.6 specialization substrate over `pg_Rset`

Claim 5.6 of [BCIKS20] picks a specialization point `x₀` avoiding the discriminant locus of every
factor.  The in-tree `Extraction.discr_of_irred_components_nonzero` does this over the *descended*
Eq-5.12 list; the field `Claim57Residuals.hx0`/`hsep` instead range over `pg_Rset`.  Here we replay
the same avoidance argument directly over `pg_Rset`, under the **honest** per-factor side conditions
that each `pg_Rset` factor is positive-`Y`-degree and fraction-field separable.

These side conditions are genuine, not free: `pg_Rset` is the *full* normalized-factor set, which in
characteristic `p` can contain inseparable factors (`discr_y = 0`) and degree-`0` factors
(`discr_y` undefined / vanishing), for which no good `x₀` of this discriminant form exists.  We
expose them as explicit hypotheses (`hpos`/`hsepFF`) exactly as the issue requires, rather than
silently assuming separability of the GS solution. -/

/-- *Bad specialization set for a single `pg_Rset` factor.*  The values of `x₀ : F` at which the
`X`-specialized discriminant `evalX x₀ (discr_y R)` vanishes. -/
noncomputable def claim57_badX (R : F[Z][X][Y]) : Finset F :=
  Finset.univ.filter (fun x₀ : F => Bivariate.evalX x₀ (Bivariate.discr_y R) = 0)

omit [DecidableEq (RatFunc F)] in
/-- **Claim-5.6 specialization step over `pg_Rset` (discriminant-nonvanishing form).**

Under the honest per-factor side conditions
* `hpos` — each `pg_Rset` factor has positive `Y`-degree, and
* `hsepFF` — each `pg_Rset` factor is separable over the fraction field `FractionRing (F[Z][X])`,

and the field-size budget `hcard` (the total discriminant-locus size is `< |F|`, the genuine
[BCIKS20] large-field requirement, cf. `Extraction.discr_of_irred_components_nonzero`), there is a
specialization point `x₀ : F` with `evalX x₀ (discr_y R) ≠ 0` for **every** `R ∈ pg_Rset`.

This is the discriminant-nonvanishing substrate of the `hx0`/`hsep` fields.  Converting it to the
exact field shapes (`evalX (C x₀) R ≠ 0`, `(evalX (C x₀) R).Separable`) requires the
discriminant/specialization commutation and the `discr ≠ 0 ⟹ Separable` converse (not yet in
tree); those are the residual bridges kept as the `hx0`/`hsep` hypotheses of `ofInTree`. -/
theorem exists_good_x₀_evalX_discr_y_ne [Fintype F]
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hpos : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        0 < R.natDegree)
    (hsepFF : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (R.map (algebraMap (F[Z][X]) (FractionRing (F[Z][X])))).Separable)
    (hcard :
      (((pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs).toList).map
        (fun R => (Bivariate.discr_y R).leadingCoeff.natDegree)).sum < Fintype.card F) :
    ∃ x₀ : F,
      ∀ R : F[Z][X][Y],
        R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
            (u₀ := u₀) (u₁ := u₁) h_gs →
          Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by
  classical
  set L : List F[Z][X][Y] :=
    (pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
        (u₀ := u₀) (u₁ := u₁) h_gs).toList with hLdef
  -- membership in `L` is exactly membership in `pg_Rset`
  have hmem : ∀ R, R ∈ L ↔
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs := by
    intro R; rw [hLdef]; exact Finset.mem_toList
  -- per-factor: discriminant nonzero, hence bad-set bounded by its leading-coeff degree
  set bad : F[Z][X][Y] → Finset F := claim57_badX with hbad
  have hbad_card : ∀ R ∈ L, (bad R).card ≤ (Bivariate.discr_y R).leadingCoeff.natDegree := by
    intro R hR
    have hRpg := (hmem R).1 hR
    have hdy : Bivariate.discr_y R ≠ 0 :=
      discr_y_ne_zero_of_sep R (hsepFF R hRpg) (hpos R hRpg)
    exact c56_evalX_bad_set_card_le (Bivariate.discr_y R) hdy
  -- sum of bad-set cards ≤ hypothesised sum < |F|
  have hsum_le :
      (L.map (fun R => (bad R).card)).sum
        ≤ (L.map (fun R => (Bivariate.discr_y R).leadingCoeff.natDegree)).sum :=
    List.sum_le_sum hbad_card
  have hsum_lt : (L.map (fun R => (bad R).card)).sum < Fintype.card F :=
    lt_of_le_of_lt hsum_le hcard
  -- avoidance: a field element outside every bad set
  obtain ⟨x₀, hx₀⟩ := c56_exists_avoiding L bad hsum_lt
  refine ⟨x₀, fun R hR => ?_⟩
  have hRL : R ∈ L := (hmem R).2 hR
  have := hx₀ R hRL
  rw [hbad, claim57_badX] at this
  simpa [Finset.mem_filter] using this

/-! ## Assembly — `Claim57Residuals.ofInTree`

The full residual bundle from the minimal honest remaining hypotheses, assembled through the proven
upstream `claim57Residuals_of_gsInterpolant` (which discharges `A`/`hA`/`hcount`/`hS_nonempty`).
Each retained hypothesis is documented with its per-field verdict above. -/

/-- **`Claim57Residuals` from the minimal honest in-tree inputs.**

Assembles `ProximityGap.Claim57Residuals k δ x₀ h_gs` from:

* `hx0` / `hsep` — the Claim-5.6 specialization side conditions (their discriminant-nonvanishing
  substrate over `pg_Rset` is proven by `exists_good_x₀_evalX_discr_y_ne`; the residual is the
  discriminant→separability bridge, kept named);
* `hJohnson` — the **single** Johnson-budget inequality
  `natWeightedDegree Q 1 k < m·(n − ⌈δ·n⌉)` (genuine Johnson-radius parameter condition; `A`/`hA`/
  `hcount`/`hS_nonempty` are discharged from it upstream);
* `hlarge` — the close-set largeness / field-size-budget input (also discharges `hS_nonempty`);
* `hfactor` — the documented `pg_Rset ⟹ descended-Eq-5.12-list` bridge, not provable outright (see
  module docstring; the provable irreducibility fragment is `claim57_hfactor_irreducible_of_pg_Rset`).

This is the honest minimal-hypothesis front door to the Claim-5.7 keystone. -/
@[reducible]
noncomputable def Claim57Residuals.ofInTree
    [NeZero n] [DecidableEq (Polynomial F)] (δ : ℚ) (x₀ : F)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hx0 : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        Bivariate.evalX (Polynomial.C x₀) R ≠ 0)
    (hsep : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        (Bivariate.evalX (Polynomial.C x₀) R).Separable)
    (hJohnson : Bivariate.natWeightedDegree Q 1 k < m * (n - ⌈δ * (n : ℚ)⌉₊))
    (hlarge :
      #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
        2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q)
    (hfactor : ∀ R : F[Z][X][Y],
      R ∈ pg_Rset (m := m) (n := n) (k := k) (ωs := ωs) (Q := Q)
          (u₀ := u₀) (u₁ := u₁) h_gs →
        R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose) :
    Claim57Residuals (F := F) (m := m) (n := n) (Q := Q) (ωs := ωs)
      (u₀ := u₀) (u₁ := u₁) k δ x₀ h_gs :=
  claim57Residuals_of_gsInterpolant (F := F) (m := m) (n := n) (k := k)
    (Q := Q) (ωs := ωs) (u₀ := u₀) (u₁ := u₁) δ x₀ h_gs hx0 hsep hJohnson hlarge hfactor

end ProximityGap

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ProximityGap.claim57_hfactor_irreducible_of_pg_Rset
#print axioms ProximityGap.exists_good_x₀_evalX_discr_y_ne
#print axioms ProximityGap.Claim57Residuals.ofInTree
