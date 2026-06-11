/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24NonzeroMinor
import ArkLib.Data.CodingTheory.AGL24DetDegree
import ArkLib.Data.CodingTheory.AGL24UnionBound
import ArkLib.Data.MvPolynomial.Interpolation

/-!
# [AGL24] discharging the probabilistic residual via Schwartz–Zippel (issue #354, stage 2)

**`RIMFullRankFailureProbResidual` is discharged at the Schwartz–Zippel bound, conditional
only on `SymbolicFullRankResidual`** — collapsing issue #354's two residuals into one. The
route (the paper's own "quadratic alphabet" shortcut, made formal): the symbolic interface
yields a nonzero polynomial minor (stage 1); a rank-deficit evaluation kills that minor; the
minor's determinant has per-variable degree at most `(k−1)·fiber` summing to `tk(k−1)`
(brick 16); Schwartz–Zippel prices the zero set under the uniform evaluation distribution.

* `rank_deficit_subset_minor_zero` — the event inclusion;
* `rimFailureProb_of_minor_zero_bound` — the generic monotonicity wrapper from a
  minor-zero probability bound to the named residual;
* `sum_degreeOf_minor_le` — the total per-variable degree budget `tk(k−1)`;
* `rimFailureProb_of_symbolic` — **the discharge**.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A rank-deficit evaluation kills every minor: the event is inside the minor's zero set. -/
theorem rank_deficit_subset_minor_zero {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (rows : Fin t × Fin k → RIMRowIdx e) :
    {α : ι → F | ∃ v : Fin t × Fin k → F, v ≠ 0 ∧
        ((RIM F e).map (MvPolynomial.eval α)).mulVec v = 0}
      ⊆ {α : ι → F |
          MvPolynomial.eval α (((RIM F e).submatrix rows id).det) = 0} := by
  intro α hα
  obtain ⟨v, hv, hker⟩ := hα
  rw [Set.mem_setOf_eq]
  by_contra hdet
  -- The evaluated minor is invertible; its kernel is trivial.
  apply hv
  have hdet' : (((RIM F e).submatrix rows id).map (MvPolynomial.eval α)).det ≠ 0 := by
    rw [show (((RIM F e).submatrix rows id).map (MvPolynomial.eval α)).det
        = MvPolynomial.eval α (((RIM F e).submatrix rows id).det) from by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]]
    exact hdet
  have hker_minor : (((RIM F e).submatrix rows id).map (MvPolynomial.eval α)).mulVec v
      = 0 := by
    funext c
    exact congrFun hker (rows c)
  have hunit : IsUnit (((RIM F e).submatrix rows id).map (MvPolynomial.eval α)).det :=
    isUnit_iff_ne_zero.mpr hdet'
  calc v = (((RIM F e).submatrix rows id).map (MvPolynomial.eval α))⁻¹.mulVec
        ((((RIM F e).submatrix rows id).map (MvPolynomial.eval α)).mulVec v) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  _ = 0 := by rw [hker_minor, Matrix.mulVec_zero]

/-- A probability bound for the zero set of a chosen square RIM minor implies the named
RIM full-rank failure residual at the same bound. This is the reusable monotonicity wrapper
around `rank_deficit_subset_minor_zero`; the actual bound can come from Schwartz-Zippel or
from a sharper certificate estimate. -/
theorem rimFailureProb_of_minor_zero_bound (D : PMF (ι → F)) {t k : ℕ}
    (e : ι → Finset (Fin (t + 1))) (rows : Fin t × Fin k → RIMRowIdx e)
    (bound : ENNReal)
    (hzero :
      D.toOuterMeasure
        {α | MvPolynomial.eval α (((RIM F e).submatrix rows id).det) = 0} ≤ bound) :
    RIMFullRankFailureProbResidual (F := F) (k := k) D e bound := by
  unfold RIMFullRankFailureProbResidual
  exact le_trans (D.toOuterMeasure.mono (rank_deficit_subset_minor_zero e rows)) hzero

/-- The total per-variable degree budget: the minor's determinant has
`∑ᵢ degreeOf i ≤ tk(k−1)` (each of the `tk` rows feeds one fiber). -/
theorem sum_degreeOf_minor_le {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (rows : Fin t × Fin k → RIMRowIdx e) :
    ∑ i : ι, MvPolynomial.degreeOf i (((RIM F e).submatrix rows id).det)
      ≤ t * k * (k - 1) := by
  classical
  calc ∑ i : ι, MvPolynomial.degreeOf i (((RIM F e).submatrix rows id).det)
      ≤ ∑ i : ι, (Finset.univ.filter (fun c => (rows c).1 = i)).card * (k - 1) :=
        Finset.sum_le_sum fun i _ => degreeOf_RIM_submatrix_det_le e i rows
  _ = (∑ i : ι, (Finset.univ.filter (fun c => (rows c).1 = i)).card) * (k - 1) := by
        rw [Finset.sum_mul]
  _ = (Fintype.card (Fin t × Fin k)) * (k - 1) := by
        congr 1
        rw [← Finset.card_univ]
        exact (Finset.card_eq_sum_card_fiberwise
          (f := fun c => (rows c).1) (t := Finset.univ)
          (fun c _ => Finset.mem_univ _)).symm
  _ = t * k * (k - 1) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- **The discharge** (issue #354): under the symbolic Theorem 2.11 interface, the
probabilistic residual `RIMFullRankFailureProbResidual` holds for the uniform evaluation
distribution at the Schwartz–Zippel bound `tk(k−1)/|F|`. -/
theorem rimFailureProb_of_symbolic {k : ℕ}
    (hsym : SymbolicFullRankResidual (ι := ι) F k)
    {t : ℕ} (ht : 1 ≤ t) (e : ι → Finset (Fin (t + 1)))
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e) :
    RIMFullRankFailureProbResidual (F := F) (k := k)
      (PMF.uniformOfFintype (ι → F)) e
      ((t * k * (k - 1) : ℕ) / (Fintype.card F : ENNReal)) := by
  classical
  unfold RIMFullRankFailureProbResidual
  -- The nonzero polynomial minor.
  obtain ⟨rows, hinj, hdet⟩ := exists_nonzero_poly_minor hsym ht e hwpc
  set p := ((RIM F e).submatrix rows id).det with hp
  set Z := Finset.univ.filter (fun α : ι → F => MvPolynomial.eval α p = 0) with hZ
  -- Event inclusion.
  refine le_trans ((PMF.uniformOfFintype (ι → F)).toOuterMeasure.mono
    (rank_deficit_subset_minor_zero e rows)) ?_
  rw [← hp]
  -- The uniform measure of the zero set is card/total.
  have hmeasure : (PMF.uniformOfFintype (ι → F)).toOuterMeasure
      {α : ι → F | MvPolynomial.eval α p = 0}
      = (Z.card : ENNReal) / (Fintype.card (ι → F) : ENNReal) := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype]
    have hterm : ∀ α : ι → F, Set.indicator {α : ι → F | MvPolynomial.eval α p = 0}
        (⇑(PMF.uniformOfFintype (ι → F))) α
        = if MvPolynomial.eval α p = 0
            then (Fintype.card (ι → F) : ENNReal)⁻¹ else 0 := by
      intro α
      rw [Set.indicator_apply]
      by_cases hα : MvPolynomial.eval α p = 0
      · rw [if_pos hα, if_pos (Set.mem_setOf_eq ▸ hα), PMF.uniformOfFintype_apply]
      · rw [if_neg hα, if_neg (by rw [Set.mem_setOf_eq]; exact hα)]
    rw [Finset.sum_congr rfl fun α _ => hterm α]
    rw [← Finset.sum_filter]
    rw [← hZ, Finset.sum_const, nsmul_eq_mul]
    rw [div_eq_mul_inv]
  show (PMF.uniformOfFintype (ι → F)).toOuterMeasure
    {α : ι → F | MvPolynomial.eval α p = 0} ≤ _
  rw [hmeasure]
  -- The Schwartz–Zippel count (ℚ≥0), specialized to all-universe boxes.
  have hsz := MvPolynomial.schwartz_zippel_of_fintype (p := p) hdet
    (fun _ : ι => (Finset.univ : Finset F))
  simp only [Fintype.piFinset_univ, Finset.card_univ, Finset.prod_const] at hsz
  -- Fold the degree sum and bound it.
  have hsum : ∑ i : ι, ((MvPolynomial.degreeOf i p : ℚ≥0) / (Fintype.card F : ℚ≥0))
      ≤ ((t * k * (k - 1) : ℕ) : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    rw [← Finset.sum_div]
    gcongr
    exact_mod_cast sum_degreeOf_minor_le e rows
  have hq : (Z.card : ℚ≥0) / ((Fintype.card F : ℚ≥0) ^ Fintype.card ι)
      ≤ ((t * k * (k - 1) : ℕ) : ℚ≥0) / (Fintype.card F : ℚ≥0) :=
    le_trans hsz hsum
  -- Cross-multiply into ℕ.
  have hFpos : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hFnpos : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) ^ Fintype.card ι := pow_pos hFpos _
  rw [div_le_div_iff₀ hFnpos hFpos] at hq
  have hnat : Z.card * Fintype.card F
      ≤ (t * k * (k - 1)) * (Fintype.card F) ^ Fintype.card ι := by
    exact_mod_cast hq
  -- Conclude in ENNReal.
  have hcardfun : (Fintype.card (ι → F) : ENNReal)
      = ((Fintype.card F) ^ (Fintype.card ι) : ℕ) := by
    rw [Fintype.card_fun]
  rw [hcardfun]
  have hB0 : (((Fintype.card F) ^ (Fintype.card ι) : ℕ) : ENNReal) ≠ 0 := by
    have : (0 : ℕ) < (Fintype.card F) ^ (Fintype.card ι) := by positivity
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hBtop : (((Fintype.card F) ^ (Fintype.card ι) : ℕ) : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hD0 : ((Fintype.card F : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hDtop : ((Fintype.card F : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hB0 hBtop]
  rw [show ((t * k * (k - 1) : ℕ) : ENNReal) / ((Fintype.card F : ℕ) : ENNReal)
      * (((Fintype.card F) ^ (Fintype.card ι) : ℕ) : ENNReal)
      = ((t * k * (k - 1) : ℕ) : ENNReal)
        * (((Fintype.card F) ^ (Fintype.card ι) : ℕ) : ENNReal)
        / ((Fintype.card F : ℕ) : ENNReal) from by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDtop)]
  exact_mod_cast hnat

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.rank_deficit_subset_minor_zero
#print axioms AGL24.rimFailureProb_of_minor_zero_bound
#print axioms AGL24.sum_degreeOf_minor_le
#print axioms AGL24.rimFailureProb_of_symbolic
