/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import Mathlib.LinearAlgebra.Lagrange

/-!
# Issue #304 — the small-good-set sector of `StrictCoeffPolysResidual` is free

`ProximityGap.StrictCoeffPolysResidual` ([BCIKS20] §5, strict Johnson branch) demands, for every
decoded family `P` on the good-coefficient set `S = RS_goodCoeffsCurve u δ`, coefficient
polynomials `B j` with `natDegree < k + 1` matching `(P z).coeff j` on `S`.

When `S.card ≤ k + 1` this demand is **unconditionally satisfiable** for *any* family `P`
whatsoever: Lagrange interpolation through at most `k + 1` field points produces a polynomial of
degree `≤ k`.  No list-decoding, counting, or Guruswami–Sudan input is needed in that sector.
The cutoff is exact: at `S.card = k + 2` a generic coefficient function is *not* degree-`≤ k`
interpolable (numerical control in `scripts/probes/probe_strict_coeff_smallset.py`,
1861/2000 generic failures over GF(13), matching the expected `(p-1)/p` rate).

Consequently the residual is **equivalent** to its restriction to large good-coefficient sets
(`k + 1 < S.card`), where the genuine [BCIKS20] §5 content lives.  Producers (the `betaRec` /
Hensel / curve-extraction lanes of `KeystoneStrictResidual`, `CurveFamilyHensel`,
`FaithfulCurveExtraction`, `OffcentreKeystoneAssembly`, `StrictCoeffProducer`) may henceforth
assume `k + 1 < S.card` for free — in particular every per-`(u, P)` counting hypothesis of the
form "the matching set is large" is now only ever demanded in a regime where the good set
itself is large.

Main results:
* `exists_coeff_interpolant_of_card_le` — the Lagrange brick (any field, any finset, any target).
* `strictCoeffPolys_of_card_le` — the coefficient-family form demanded by the residual.
* `StrictCoeffPolysResidualLarge` — the residual restricted to `k + 1 < S.card`.
* `strictCoeffPolysResidual_iff_large` — the equivalence (the reduction, both directions).
* `correlatedAgreement_affine_curves_of_largeResidual` — the keystone front door consuming the
  large-sector residual plus the boundary residual.
* `correlatedAgreement_affine_curves_strict_of_largeResidual` — the strict-interior front door,
  where the documented-false boundary residual is unreachable and is not an assumption.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5, §6.2.
-/

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Polynomial Code
open scoped BigOperators LinearCode ProbabilityTheory ENNReal

section Interpolation

variable {F : Type} [Field F] [DecidableEq F]

/-- **The Lagrange brick.**  Any target function on a finset of at most `k + 1` field points is
matched exactly by a polynomial of `natDegree < k + 1`. -/
theorem exists_coeff_interpolant_of_card_le (k : ℕ) (S : Finset F) (hS : S.card ≤ k + 1)
    (c : F → F) :
    ∃ B : Polynomial F, B.natDegree < k + 1 ∧ ∀ z ∈ S, B.eval z = c z := by
  classical
  refine ⟨Lagrange.interpolate S id c, ?_, ?_⟩
  · by_cases h0 : Lagrange.interpolate S id c = 0
    · simp [h0]
    · have hdeg : (Lagrange.interpolate S id c).degree < (S.card : WithBot ℕ) :=
        Lagrange.degree_interpolate_lt (v := id) (r := c) Function.injective_id.injOn
      have hdeg' : (Lagrange.interpolate S id c).degree < ((k + 1 : ℕ) : WithBot ℕ) :=
        lt_of_lt_of_le hdeg (by exact_mod_cast hS)
      exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg'
  · intro z hz
    simpa using
      Lagrange.eval_interpolate_at_node (v := id) (r := c) Function.injective_id.injOn hz

/-- **Small-sector coefficient-family discharge.**  On a good set of at most `k + 1` points, the
coefficient-polynomial family demanded by `StrictCoeffPolysResidual` exists for *every* decoded
family `P`, with no hypotheses on `P` at all. -/
theorem strictCoeffPolys_of_card_le (k deg : ℕ) (S : Finset F) (hS : S.card ≤ k + 1)
    (P : F → Polynomial F) :
    ∃ B : ℕ → Polynomial F,
      (∀ j < deg, (B j).natDegree < k + 1) ∧
        ∀ z ∈ S, ∀ j < deg, (P z).coeff j = (B j).eval z := by
  classical
  choose B hBdeg hBeval using fun j : ℕ =>
    exists_coeff_interpolant_of_card_le (F := F) k S hS (fun z => (P z).coeff j)
  exact ⟨B, fun j _ => hBdeg j, fun z hz j _ => (hBeval j z hz).symm⟩

end Interpolation

section Residual

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `StrictCoeffPolysResidual` restricted to the large-good-set sector
`k + 1 < (RS_goodCoeffsCurve u δ).card`.  By `strictCoeffPolysResidual_iff_large` this carries
the *entire* content of the residual: the complementary sector is discharged unconditionally by
Lagrange interpolation. -/
def StrictCoeffPolysResidualLarge {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} : Prop :=
  ∀ (_hk : 0 < k) (u : WordStack F (Fin (k + 1)) ι),
    Pr_{
      let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
        ReedSolomon.code domain deg) ≤ δ] >
        ((k : ENNReal) * (errorBound δ deg domain : ENNReal)) →
    (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ →
    δ < 1 - ReedSolomon.sqrtRate deg domain →
    k + 1 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card →
    ∀ P : F → Polynomial F,
      (∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
        (P z).natDegree < deg ∧
          δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
            (P z).eval ∘ domain) ≤ δ) →
        ∃ B : ℕ → Polynomial F,
          (∀ j < deg, (B j).natDegree < k + 1) ∧
            ∀ z ∈ RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ,
              ∀ j < deg, (P z).coeff j = (B j).eval z

omit [Nonempty ι] [DecidableEq ι] in
/-- **The reduction.**  The large-sector residual discharges the full residual: on small
good-coefficient sets (`card ≤ k + 1`) the coefficient family is produced unconditionally by
Lagrange interpolation. -/
theorem strictCoeffPolysResidual_of_large {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hLarge :
      StrictCoeffPolysResidualLarge (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  by_cases hcard :
      k + 1 < (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ).card
  · exact hLarge hk u hprob hJ hsqrt hcard P hP
  · exact strictCoeffPolys_of_card_le (F := F) k deg
      (RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ)
      (Nat.le_of_not_lt hcard) P

omit [Nonempty ι] [DecidableEq ι] in
/-- The trivial converse: the full residual restricts to the large sector. -/
theorem strictCoeffPolysResidualLarge_of_residual {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hRes : StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    StrictCoeffPolysResidualLarge (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  fun hk u hprob hJ hsqrt _hcard P hP => hRes hk u hprob hJ hsqrt P hP

omit [Nonempty ι] [DecidableEq ι] in
/-- **`StrictCoeffPolysResidual` is equivalent to its large-good-set restriction.**  The
small-good-set sector of the [BCIKS20] §5 strict Johnson extraction carries no mathematical
content: it is pure interpolation. -/
theorem strictCoeffPolysResidual_iff_large {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) ↔
      StrictCoeffPolysResidualLarge (k := k) (deg := deg) (domain := domain) (δ := δ) :=
  ⟨strictCoeffPolysResidualLarge_of_residual, strictCoeffPolysResidual_of_large⟩

/-- **Keystone front door for the large sector.**  [BCIKS20] Theorem 1.5 (correlated agreement
for low-degree parameterised curves) from the large-sector strict residual and the boundary
residual — producers never have to consider good sets of size `≤ k + 1`. -/
theorem correlatedAgreement_affine_curves_of_largeResidual {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hLarge :
      StrictCoeffPolysResidualLarge (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hBoundary :
      BoundaryProbabilityResidual (k := k) (deg := deg) (domain := domain) (δ := δ))
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves (k := k) (deg := deg) (domain := domain) (δ := δ)
    (strictCoeffPolysResidual_of_large hLarge) hBoundary hδ

/-- **Strict-interior large-sector front door.**  If `δ < 1 − sqrtRate`, the boundary branch in
`correlatedAgreement_affine_curves_of_largeResidual` is unreachable, so the large-sector residual
alone gives the curve correlated-agreement theorem. -/
theorem correlatedAgreement_affine_curves_strict_of_largeResidual {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg]
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hLarge :
      StrictCoeffPolysResidualLarge (k := k) (deg := deg) (domain := domain) (δ := δ)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) :=
  correlatedAgreement_affine_curves_of_largeResidual (k := k) (deg := deg)
    (domain := domain) (δ := δ) hLarge
    (fun _hk _u _hprob _hJ hnot => absurd hδ hnot) hδ.le

end Residual

end ProximityGap

#print axioms ProximityGap.correlatedAgreement_affine_curves_strict_of_largeResidual
