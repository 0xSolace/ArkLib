/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Extraction
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Polynomial.Trivariate

namespace ProximityGap

open Polynomial Polynomial.Bivariate NNReal Finset Function ProbabilityTheory Code Trivariate
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}
variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}

-- `DecidableEq (RatFunc F)` is threaded through the section for the Appendix A machinery;
-- several statement-level extractions do not mention it directly.
set_option linter.unusedDecidableInType false

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
/-- *Accessible twin of the sealed `eval_on_Z`.*  The per-`z` `Z`-specialization used throughout
the proven Claim-5.7 machinery in `Extraction.lean` is `pg_eval_on_Z`, and it reduces, by `rfl`,
to exactly the definitional body of `Trivariate.eval_on_Z`, namely
`p.map (mapRingHom (evalRingHom z))`.

This lemma is the *positive half* of the verified obstruction recorded on
`exists_factors_with_large_common_root_set` below: every fact the proof needs
(`pg_exists_pair_for_z`, `pg_card_candidatePairs_le_natDegreeY`, the per-`z` factor/`H`
extraction) is phrased for `pg_eval_on_Z`, and `pg_eval_on_Z = (·.map (mapRingHom (evalRingHom z)))`
holds definitionally — whereas the *same body* wrapped in `Trivariate.eval_on_Z` (which the Claim-5.7
statement uses) is `opaque` and hence provably inaccessible: not `eval_on_Z 0 z = 0`, not additivity,
and not `eval_on_Z p z = pg_eval_on_Z p z` is derivable (all fail with "made no progress" / `rfl`
failure, since `opaque` blocks delta-reduction). -/
lemma c57_pg_eval_on_Z_body (p : F[Z][X][Y]) (z : F) :
    pg_eval_on_Z (F := F) p z = p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
  rfl

open Trivariate in
open Bivariate in
/-- Claim 5.7 of [BCIKS20].

OBSTRUCTION (statement unprovable as formalized — verified defect, the 6th in this tree).
There are two independent blockers; the first is fatal on its own.

* *Sealed `eval_on_Z` (Gap A — verified, see `c57_pg_eval_on_Z_body`).*  The first cardinality
  conjunct lower-bounds `#S'`, where `S'` is the subset of `S = coeffs_of_close_proximity` cut out
  by the predicate `(Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧ …`.  But `Trivariate.eval_on_Z`
  (`Trivariate.lean`) is declared `opaque`, so **no** property of `eval_on_Z R z.1` is derivable:
  one cannot prove `eval_on_Z 0 z = 0`, nor additivity, nor `eval_on_Z p z = pg_eval_on_Z p z`
  (the last fails `rfl` *despite identical definitional bodies* — `opaque` blocks delta-reduction).
  Consequently the membership predicate of `S'` can be established for **no** `z`, so `#S'` cannot be
  bounded below.  Meanwhile every proven ingredient of the argument
  (`pg_exists_pair_for_z`, `pg_card_candidatePairs_le_natDegreeY`,
  `pg_card_normalizedFactors_toFinset_le_natDegree`) is phrased for the accessible twin
  `pg_eval_on_Z`, whose body is `c57_pg_eval_on_Z_body`.  The faithful, binder-preserving repair is
  to replace `Trivariate.eval_on_Z` by `pg_eval_on_Z` in the `S'` predicate (the
  `R`/`H`/`Irreducible H` consumers — `R`, `H`, `irreducible_H`, Claims 5.8–5.11 — read only
  `.choose`, `.choose_spec.choose`, and `.choose_spec.choose_spec.2.1`, so they are unaffected); or,
  upstream, to de-seal `eval_on_Z` (drop `opaque`, or expose an `eval_on_Z_def` equation lemma).

* *Missing GS-multiplicity → close-codeword-graph vanishing (Gap B — residual).*  Even after the
  Gap-A repair, the pigeonhole needs, for each `z ∈ S`, the vanishing
  `(pg_eval_on_Z Q z.1).eval (Pz z.2) = 0` — the formal content of "`Q` vanishes on the graphs of
  the `δ`-close codewords", obtained from the `ModifiedGuruswami` multiplicity field `Q_multiplicity`
  together with the `Pz`-matching data of Proposition 5.5.  No lemma in `Guruswami.lean` /
  `Extraction.lean` connects `Q_multiplicity` (an order-`≥ m` root-multiplicity over `F[Z]` at the
  curve points `(C ωᵢ, C(u₀ᵢ) + X·C(u₁ᵢ))`) to this evaluation-zero fact, and the upstream
  Proposition 5.5 (`exists_a_set_and_a_matching_polynomial`, which supplies the matching `P`/`Pz`
  data) is itself still `sorry`.  Building this bridge — the trivariate analogue of the bivariate
  `GuruswamiSudan.dvd_eval_of_rootMultiplicity_zero` / `proximity_gap_divisibility` — is the precise
  residual mathematical content once Gap A is unsealed.

Given Gap A alone makes `#S'` unbounded-below for the `opaque` predicate, the conjunction is
unprovable; the `sorry` is retained.  The binder structure
`∃ R H, R ∈ … ∧ Irreducible H ∧ …` is preserved so the downstream extractors stay well-typed. -/
lemma exists_factors_with_large_common_root_set (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ 0 < H.natDegree ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    (Bivariate.evalX (Polynomial.C x₀) R).Separable ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0}
        (@Fintype.ofFinite _ Subtype.finite))
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- Claim 5.7 establishes existens of a polynomial `R`. his is the extraction of this polynomial. -/
noncomputable def R (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X][Y] :=
 (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose

/-- Claim 5.7 establishes existens of a polynomial `H`. This is the extraction of this polynomial.
-/
noncomputable def H (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : F[Z][X] :=
(exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose

/-- An important property of the polynomial `H` extracted from Claim 5.7 is that it is irreducible.
-/
lemma irreducible_H (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Irreducible (H k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.1

/-- The factor `H` extracted from Claim 5.7 has positive degree in the `Y` variable, matching the
Appendix A hypotheses needed for the function field construction. -/
lemma natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    0 < (H k δ x₀ h_gs).natDegree :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.1

/-- The `Fact` form of `natDegree_H_pos`, for downstream declarations that take the
positivity as an instance. -/
instance fact_natDegree_H_pos (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Fact (0 < (H k δ x₀ h_gs).natDegree) :=
  ⟨natDegree_H_pos k h_gs⟩

/-- The extracted `H` divides `R(x₀, Y, Z)`, as required for the Hensel setup in Claim A.2. -/
lemma H_dvd_evalX_R (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    H k δ x₀ h_gs ∣ Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs) :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.2.1

/-- The specialization `R(x₀, Y, Z)` is separable in `Y`, as required for Claim A.2. -/
lemma evalX_R_separable (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    (Bivariate.evalX (Polynomial.C x₀) (R k δ x₀ h_gs)).Separable :=
  (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose_spec.2.2.2.2.1

open BCIKS20AppendixA.ClaimA2 in
/-- The Claim A.2 hypotheses satisfied by the `R,H` pair extracted from Claim 5.7. -/
lemma claimA2_hypotheses (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    Hypotheses x₀ (R k δ x₀ h_gs) (H k δ x₀ h_gs) :=
  ⟨H_dvd_evalX_R k h_gs, evalX_R_separable k h_gs⟩

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution. This version of the claim is stated in
terms of coefficients. -/
lemma approximate_solution_is_exact_solution_coeffs
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    : ∀ t ≥ k,
    α'
      x₀
      (R k δ x₀ h_gs)
      (irreducible_H k h_gs)
      (natDegree_H_pos k h_gs)
      (claimA2_hypotheses k h_gs)
      t
    =
    (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
    := by sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.8 from [BCIKS20].
States that the approximate solution is actually a solution.
This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) (natDegree_H_pos k h_gs)
        (claimA2_hypotheses k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : BCIKS20AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff t
            (γ'
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs)
              (natDegree_H_pos k h_gs)
              (claimA2_hypotheses k h_gs))) := by
   sorry

open BCIKS20AppendixA.ClaimA2 in
/-- Claim 5.9 from [BCIKS20].
States that the solution `γ` is linear in the variable `Z`. -/
lemma solution_gamma_is_linear_in_Z
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
      (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
      (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
        BCIKS20AppendixA.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear represenation of the solution `γ` extracted from Claim 5.9. -/
noncomputable def P (δ : ℚ) (x₀ : F) (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)] : F[Z][X] :=
  let v₀ := Classical.choose (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  let v₁ := Classical.choose
    (Classical.choose_spec <| solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open BCIKS20AppendixA.ClaimA2 in
/-- The extracted `P` from Claim 5.9 equals `γ`. -/
lemma gamma_eq_P (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs)
    (natDegree_H_pos k (x₀ := x₀) (δ := δ) h_gs)
    (claimA2_hypotheses k (x₀ := x₀) (δ := δ) h_gs) =
  BCIKS20AppendixA.polyToPowerSeries𝕃 _
    (P k δ x₀ h_gs) :=
  Classical.choose_spec
    (Classical.choose_spec (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs))

/-- The set `S'_x` from [BCIKS20] (just before Claim 5.10). The set of all `z ∈ S'` such that
`w(x,z)` matches `P_z(x)`. -/
noncomputable def matching_set_at_x
    (δ : ℚ)
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (x : Fin n)
    : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs,
    u₀ x + z * u₁ x =
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h)).eval (ωs x)}
      (@Fintype.ofFinite _ Subtype.finite)

/-- Claim 5.10 of [BCIKS20].
Needed to prove Claim 5.9. This claim states that `γ(x) = w(x,Z)` if the cardinality `|S'_x|` is big
enough. -/
lemma solution_gamma_matches_word_if_subset_large
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    [Fact (0 < (H k δ x₀ h_gs).natDegree)]
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    (hx : (matching_set_at_x k δ h_gs x).card >
      (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D)
    : (P k δ x₀ h_gs).eval (Polynomial.C (ωs x)) =
      (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X
    := by sorry

/-- Claim 5.11 from [BCIKS20].
There exists a set of points `{x₀,...,x_{k+1}}` such that the sets S_{x_j} satisfy the condition in
Claim 5.10. -/
lemma exists_points_with_large_matching_subset
    {ωs : Fin n ↪ F}
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    {x : Fin n}
    {D : ℕ}
    (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
    :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by sorry

end BCIKS20ProximityGapSection5

end ProximityGap
