/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.JointAgreement
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound

/-!
# Correlated agreement for parameterized curves — unique-decoding regime

[BCIKS20] Theorem 6.1 (the unique-decoding case of Theorem 1.5): if a random
point on the degree-`k` parameterized curve through `u 0, …, u k` is `δ`-close
to the Reed–Solomon code with probability exceeding `k · (n/q)`, then the
words have correlated (joint) agreement. Curves analogue of
`AffineLines/UniqueDecoding.lean`; consumes the Curves GoodCoeffs +
JointAgreement chain. The list-decoding regime (Theorem 6.2) remains open
(§5 chain).
-/

namespace ProximityGap

-- Decidability/Fintype instances are threaded through the section; the
-- statement-level theorem does not mention them directly.
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

section CoreResults
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Correlated agreement for low-degree parameterized curves, unique-decoding
regime** ([BCIKS20] Theorem 6.1 / the UDR case of Theorem 1.5): curves analogue
of `RS_correlatedAgreement_affineLines_uniqueDecodingRegime`. -/
theorem RS_correlatedAgreement_curves_uniqueDecodingRegime {k deg : ℕ}
    {domain : ι ↪ F} {δ : ℝ≥0} [NeZero deg] (hk : 0 < k)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementCurves
  intro u hprob
  have hkε : (k : ℝ≥0) * errorBound δ deg domain
      = ((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    rw [errorBound_eq_n_div_q_of_le_relUDR (deg := deg) (domain := domain) (δ := δ) hδ]
    push_cast
    ring
  have hprob' :
      Pr_{let z ← $ᵖ F}[δᵣ(∑ t : Fin (k + 1), (z ^ (t : ℕ)) • u t,
          ReedSolomon.code domain deg) ≤ δ]
        > ((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
    have hqne : ((Fintype.card F : ℝ≥0)) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    calc ((((k * Fintype.card ι : ℕ) : ℝ≥0) : ENNReal) / (((Fintype.card F : ℝ≥0)) : ENNReal))
        = ((((k * Fintype.card ι : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) :=
          (ENNReal.coe_div hqne).symm
      _ = (((k : ℝ≥0) * errorBound δ deg domain : ℝ≥0) : ENNReal) := by rw [hkε]
      _ = (k : ENNReal) * (errorBound δ deg domain : ENNReal) := by
          rw [ENNReal.coe_mul, ENNReal.coe_natCast]
      _ < _ := by simpa using hprob
  have hS := card_RS_goodCoeffsCurve_gt_of_prob_gt_kn_div_q (k := k) (deg := deg)
    (domain := domain) (δ := δ) u (by exact_mod_cast hprob')
  exact RS_jointAgreement_of_goodCoeffsCurve_card_gt (k := k) (deg := deg)
    (domain := domain) (δ := δ) hk hδ u hS

/-- The `k = 0` corner of curves correlated agreement: a degree-0 "curve" is the
constant word `u 0`, so any positive probability of closeness gives the plain
closeness fact, and joint agreement follows from unique decoding. -/
theorem RS_correlatedAgreement_curves_k_zero {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    [NeZero deg]
    (_hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code domain deg)) :
    δ_ε_correlatedAgreementCurves (k := 0) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  classical
  unfold δ_ε_correlatedAgreementCurves
  intro u hprob
  -- the curve is constant: ∑ t : Fin 1, r^t • u t = u 0
  have hconst : ∀ r : F, (∑ t : Fin (0 + 1), (r ^ (t : ℕ)) • u t) = u 0 := by
    intro r
    simp
  -- positive probability ⇒ nonempty good set (bridge at k = 0) ⇒ the constant fact
  have hS := card_RS_goodCoeffsCurve_gt_of_prob_gt_kn_div_q (k := 0) (deg := deg)
    (domain := domain) (δ := δ) u (by simpa using hprob)
  have hclose : δᵣ(u 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ δ := by
    have hne : (RS_goodCoeffsCurve (k := 0) (deg := deg) (domain := domain) u δ).Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨z, hz⟩ := hne
    have hz' := hz
    simp only [RS_goodCoeffsCurve] at hz'
    by_contra hp
    simp [hp] at hz' 
  -- unique-decode and collect the agreement set
  set e : ℕ := Nat.floor (δ * Fintype.card ι) with he
  have hdist : Δ₀(u 0, (ReedSolomon.code domain deg : Set (ι → F))) ≤ (e : ℕ∞) := by
    have h := (Code.relDistFromCode_le_iff_distFromCode_le
        (u := u 0) (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ)).1 hclose
    simpa [e] using h
  rcases (Code.closeToCode_iff_closeToCodeword_of_minDist
        (u := u 0) (C := (ReedSolomon.code domain deg : Set (ι → F))) (e := e)).1 hdist with
    ⟨w, hwC, hwdist⟩
  obtain ⟨T, hT_card, hT_agree⟩ :=
    (Code.closeToWord_iff_exists_agreementCols (u := u 0) (v := w) (e := e)).1 hwdist
  refine ⟨T, ?_, fun _ => w, ?_⟩
  · have hnat : Fintype.card ι - e ≤ T.card := hT_card
    simpa [e] using
      (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) T.card δ).mp
        (by simpa [e] using hnat)
  · intro t
    refine ⟨hwC, ?_⟩
    intro j hj
    have := (hT_agree j).1 hj
    have ht0 : t = 0 := Fin.fin_one_eq_zero t
    subst ht0; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact this.symm


end CoreResults

end ProximityGap
