/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, Frantisek Silvasi, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Guruswami

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory ENNReal
open Code

section BCIKS20ProximityGapSection5To6Bridge

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- For degree-one curves through two words, the §6 close-parameter set is the
same set as the §5 affine-line close-proximity set. -/
theorem coeffs_of_close_proximity_curve_finMapTwoWords_eq_close_proximity
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) :
    coeffs_of_close_proximity_curve (F := F) (n := n) (l := 2)
        δ (Code.finMapTwoWords u₀ u₁) (ReedSolomon.toFinset ωs (k + 1)) =
      coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ := by
  classical
  apply Finset.ext
  intro z
  simp only [coeffs_of_close_proximity_curve, coeffs_of_close_proximity,
    ReedSolomon.toFinset, ReedSolomon.RScodeSet, Set.mem_toFinset, Set.mem_setOf_eq,
    polynomialCurveEval_eq_sum_smul]
  rw [sum_finMapTwoWords_eq]
  constructor
  · intro hz
    have hz' :
        δᵣ(u₀ + z • u₁,
            (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
              Set (Fin n → F))) ≤ ((δ : ℝ≥0) : ENNReal) := by
      simpa [ENNReal.coe_nnratCast] using hz
    obtain ⟨v, hv_mem, hv_close⟩ :=
      (relCloseToCode_iff_relCloseToCodeword_of_minDist
        (C := (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
          Set (Fin n → F)))
        (u := u₀ + z • u₁) (δ := (δ : ℝ≥0))).mp hz'
    have hv_code : v ∈ ReedSolomon.code ωs (k + 1) := by
      simpa using hv_mem
    exact ⟨⟨v, hv_code⟩, by simpa [ENNReal.coe_nnratCast] using hv_close⟩
  · rintro ⟨v, hv_close⟩
    have hv_fin :
        (v : Fin n → F) ∈
          (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
            Set (Fin n → F)) := by
      simp
    have hclose :
        δᵣ(u₀ + z • u₁,
            (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
              Set (Fin n → F))) ≤ ((δ : ℝ≥0) : ENNReal) :=
      (relCloseToCode_iff_relCloseToCodeword_of_minDist
        (C := (↑(Set.toFinset (ReedSolomon.code ωs (k + 1) : Set (Fin n → F))) :
          Set (Fin n → F)))
        (u := u₀ + z • u₁) (δ := (δ : ℝ≥0))).mpr
        ⟨v, hv_fin, by simpa [ENNReal.coe_nnratCast] using hv_close⟩
    simpa [ENNReal.coe_nnratCast] using hclose

/-- Direct §5-to-§6 specialization: the affine-line close-proximity set from
the list-decoding section is exactly the degree-one `RS_goodCoeffsCurve` set. -/
theorem coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) :
    coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ =
      RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
  rw [← coeffs_of_close_proximity_curve_finMapTwoWords_eq_close_proximity
    (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁]
  exact coeffs_of_close_proximity_curve_RS_toFinset_eq_goodCoeffsCurve
    (F := F) (n := n) (k := 1) (deg := k + 1) (domain := ωs) δ
    (Code.finMapTwoWords u₀ u₁)

/-- Membership form of
`coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords`. -/
theorem coeffs_of_close_proximity_mem_iff_goodCoeffsCurve_finMapTwoWords
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) (z : F) :
    z ∈ coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁ ↔
      z ∈ RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0) := by
  rw [coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords
    (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁]

/-- Cardinality form of
`coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords`. -/
theorem coeffs_of_close_proximity_card_eq_goodCoeffsCurve_finMapTwoWords
    {k : ℕ} {ωs : Fin n ↪ F} (δ : ℚ≥0) (u₀ u₁ : Fin n → F) :
    (coeffs_of_close_proximity (F := F) k ωs (δ : ℚ) u₀ u₁).card =
      (RS_goodCoeffsCurve (k := 1) (deg := k + 1) (domain := ωs)
        (Code.finMapTwoWords u₀ u₁) (δ : ℝ≥0)).card := by
  rw [coeffs_of_close_proximity_eq_goodCoeffsCurve_finMapTwoWords
    (F := F) (n := n) (k := k) (ωs := ωs) δ u₀ u₁]

end BCIKS20ProximityGapSection5To6Bridge

end ProximityGap
