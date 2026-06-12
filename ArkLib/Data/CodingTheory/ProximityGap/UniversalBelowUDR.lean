/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralKMultiplicity
import ArkLib.Data.CodingTheory.ProximityGap.SparseDirectionGeneralK
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# The universal below-UDR law, all rates (#371): the assembly

The general-rate analogue of the `k = 1` universal law: for **every** stack and
every radius `δ ≤ w/n` with `2w + 2k ≤ n`,

  **`#bad · (n − 2w − 2k + 1)^k ≤ n^{k+1}`**.

The dichotomy on the direction's maximum codeword agreement `a*`:

* `a* ≤ n − w − k − 1`: the general-`k` multiplicity theorem applies, and its
  factor dominates `(n−2w−2k+1)^k` (descending factorial ≥ the power);
* `a* ≥ n − w − k`: the direction is within `w + k` of a codeword; translation
  equivariance reduces to a sparse direction with support `≤ w + k`, and the
  general-`k` sparse bound's factor is exactly `(n−2w−2k+1)^k`.

No class hypotheses.  Mass `≤ n^{k+1}/((n−2w−2k+1)^k·q)` — polynomial in `n` at
every fixed rate, production-silent throughout the covered range, which reaches
within `k/n` of the unique-decoding radius.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- **THE UNIVERSAL BELOW-UDR LAW, ALL RATES**: every stack, every radius
`δ ≤ w/n` with `2w + 2k ≤ n`:  `#bad · (n−2w−2k+1)^k ≤ n^{k+1}`. -/
theorem generalK_badScalars_card_mul_le_universal (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + 2 * k ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (u₀ u₁ : Fin n → F) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      * (n - 2 * w - 2 * k + 1) ^ k ≤ n ^ (k + 1) := by
  by_cases hcase : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ n - w - k - 1
  · -- multiplicity regime
    have hmult := badScalars_card_mul_le_of_agreement dom hk hδn
      (u₀ := u₀) (u₁ := u₁) hcase
    have hcardfun : Fintype.card (Fin (k + 1) → Fin n) = n ^ (k + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [hcardfun] at hmult
    refine le_trans (Nat.mul_le_mul_left _ ?_) hmult
    -- (n−2w−2k+1)^k ≤ descFactorial · (n−w−k−μ) with μ = n−w−k−1
    have hfac : n - w - k - (n - w - k - 1) = 1 ∨ n - w - k = 0 := by omega
    have h1 : 1 ≤ n - w - k - (n - w - k - 1) := by omega
    calc (n - 2 * w - 2 * k + 1) ^ k
        ≤ ((n - w) + 1 - k) ^ k := by
          refine Nat.pow_le_pow_left ?_ k
          omega
      _ ≤ (n - w).descFactorial k := Nat.pow_sub_le_descFactorial _ _
      _ = (n - w).descFactorial k * 1 := (mul_one _).symm
      _ ≤ (n - w).descFactorial k * (n - w - k - (n - w - k - 1)) :=
          Nat.mul_le_mul_left _ h1
  · -- near-codeword regime: translate and use the general-k sparse bound
    push Not at hcase
    obtain ⟨c, hcC, hagree⟩ := hcase
    have haN : n - w - k ≤ (agreeSet c u₁).card := by omega
    set ε : Fin n → F := u₁ - c with hε
    -- support of ε = complement of the agreement set
    have hsupp : (Finset.univ.filter (fun i => ε i ≠ 0)).card ≤ w + k := by
      have hcompl : Finset.univ.filter (fun i => ε i ≠ 0)
          = Finset.univ.filter (fun i => ¬ c i = u₁ i) := by
        refine Finset.filter_congr fun i _ => ?_
        rw [hε]
        simp [sub_eq_zero, eq_comm]
      rw [hcompl]
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => c i = u₁ i)
      have huniv : (Finset.univ : Finset (Fin n)).card = n := by
        rw [Finset.card_univ, Fintype.card_fin]
      have hagreecard : (agreeSet c u₁).card
          = (Finset.univ.filter (fun i => c i = u₁ i)).card := rfl
      omega
    -- translation: the bad sets agree
    have hfilter : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ))
        = (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)) := by
      refine Finset.filter_congr fun γ _ => ?_
      have h := ProximityGap.MCAEquivariance.mcaEvent_translate
        (rsCode dom k : Submodule F (Fin n → F)) (δ := δ)
        (u₀ := u₀) (u₁ := ε)
        (c₀ := 0) (c₁ := c)
        ((rsCode dom k : Submodule F (Fin n → F)).zero_mem) hcC γ
      have he0 : u₀ + 0 = u₀ := by funext i; simp
      have he1 : ε + c = u₁ := by
        funext i
        rw [hε]
        simp
      rw [he0, he1] at h
      rw [h]
    rw [hfilter]
    have hmk' : k ≤ n - w - (w + k) := by omega
    have hsparse := sparse_direction_badScalars_card_le_generalK dom
      (w := w) (e := w + k) hδn hmk' (u₀ := u₀) (ε := ε) hsupp
    have hfaceq : (n - w - (w + k)) + 1 - k = n - 2 * w - 2 * k + 1 := by omega
    rw [hfaceq] at hsparse
    calc (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ ε γ)).card
          * (n - 2 * w - 2 * k + 1) ^ k
        ≤ n ^ k * (w + k) := hsparse
      _ ≤ n ^ k * n := Nat.mul_le_mul_left _ (by omega)
      _ = n ^ (k + 1) := by rw [pow_succ]

open Classical in
/-- **The probability form**: `ε_mca(RS_k, δ) ≤ n^{k+1}/((n−2w−2k+1)^k·q)` for
every `δ ≤ w/n` with `2w + 2k ≤ n` — the universal below-UDR law at all rates. -/
theorem generalK_epsMCA_le_universal (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + 2 * k ≤ n)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ ((n ^ (k + 1) / (n - 2 * w - 2 * k + 1) ^ k : ℕ) : ℝ≥0∞)
        / (Fintype.card F : ℝ≥0∞) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  have h := generalK_badScalars_card_mul_le_universal dom hk hn hδn (u 0) (u 1)
  have hpos : 0 < (n - 2 * w - 2 * k + 1) ^ k := by positivity
  have hdiv : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
      ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ (u 0) (u 1)
      γ)).card ≤ n ^ (k + 1) / (n - 2 * w - 2 * k + 1) ^ k :=
    Nat.le_div_iff_mul_le hpos |>.mpr h
  exact_mod_cast hdiv

open Classical in
/-- **The unconditional production floor**: `δ* ≥ δ` for every radius `δ ≤ w/n`
with `2w + 2k ≤ n`, whenever the polynomial mass fits the budget — for low rates
this floor `≈ 1/2 − ρ` strictly improves the ladder reach `(1−ρ)/3`, with NO
named residual. -/
theorem le_mcaDeltaStar_universal (dom : Fin n ↪ F)
    {k w : ℕ} (hk : 1 ≤ k) (hn : 2 * w + 2 * k ≤ n)
    {δ : ℝ≥0} (hδ1 : δ ≤ 1) (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {εstar : ℝ≥0∞}
    (hbudget : ((n ^ (k + 1) / (n - 2 * w - 2 * k + 1) ^ k : ℕ) : ℝ≥0∞)
      / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (generalK_epsMCA_le_universal dom hk hn hδn) hbudget)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.generalK_badScalars_card_mul_le_universal
#print axioms ProximityGap.Ownership.generalK_epsMCA_le_universal
#print axioms ProximityGap.Ownership.le_mcaDeltaStar_universal
