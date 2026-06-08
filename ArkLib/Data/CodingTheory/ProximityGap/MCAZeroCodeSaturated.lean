/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAZeroCodeLowerBound

/-!
# The saturated regime: `ε_mca(⊥, δ) = 1` once `|F| ≤ ⌊δn⌋ + 1`

This finishes the characterization of the zero code's MCA error across the whole range
`δ ∈ [0,1]`. `MCAZeroCodeUpperBound`/`MCAZeroCodeLowerBound` give
`ε_mca(⊥, δ) = (⌊δn⌋+1)/|F|` in the **sub-saturated** regime `⌊δn⌋+1 ≤ min(n, |F|)`. Here we handle
the **saturated** regime: when `|F| ≤ ⌊δn⌋ + 1` (and `|F| ≤ n`), *every* scalar is bad, so

  `ε_mca(⊥, δ) = 1`.

The construction reuses `mcaEvent_slopeStack`: take `A ⊆ ι` of size `|F|` and `φ` a **bijection**
`A ≃ F`. Every `γ ∈ F` equals `φ i₀` for some `i₀ ∈ A`, so `mcaEvent` fires at every `γ`; the bad
set is all of `F`, giving `Pr_γ = 1` and `ε_mca = 1`.

Combining all three files: for `δ ∈ [0,1]`,
`ε_mca(⊥, δ) = min(⌊δn⌋+1, |F|)/|F|`.

## References
- Completes `ProximityGap.MCAZeroCode` characterization. Issue #140 / #171.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MCAZeroCode

open scoped NNReal ProbabilityTheory ENNReal
open ProximityGap Code

section Saturated

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Saturated regime: `ε_mca(⊥, δ) = 1`.** When `|F| ≤ ⌊δn⌋ + 1 ≤ n`, every scalar is bad. -/
theorem epsMCA_bot_eq_one_of_saturated {δ : ℝ≥0}
    (hFn : Fintype.card F ≤ Fintype.card ι)
    (hsat : Fintype.card F ≤ ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ + 1) :
    epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ = 1 := by
  -- `ε_mca ≤ 1`.
  have hle1 : epsMCA (F := F) (A := F) (Cbot : Set (ι → F)) δ ≤ 1 := by
    unfold epsMCA
    exact iSup_le fun u => Pr_le_one _ _
  refine le_antisymm hle1 ?_
  -- Build `A ⊆ ι` of size `|F|` and a bijection `φ : A ≃ F`.
  obtain ⟨A, _hAsub, hAcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := Fintype.card F)
      (by simpa [Finset.card_univ] using hFn)
  have hcardeq : Fintype.card {x // x ∈ A} = Fintype.card F := by
    rw [Fintype.card_coe, hAcard]
  let e : {x // x ∈ A} ≃ F := Fintype.equivOfCardEq hcardeq
  let φ : ι → F := fun i => if h : i ∈ A then e ⟨i, h⟩ else 0
  have hAcard_le : ((A.card : ℝ)) ≤ (δ : ℝ) * (Fintype.card ι : ℝ) + 1 := by
    rw [hAcard]
    have hfloor := Nat.floor_le (show (0:ℝ) ≤ (δ:ℝ) * (Fintype.card ι:ℝ) by positivity)
    have : (Fintype.card F : ℝ) ≤ (⌊(δ:ℝ) * (Fintype.card ι:ℝ)⌋₊ : ℝ) + 1 := by exact_mod_cast hsat
    linarith
  -- Every scalar fires.
  have hall : ∀ γ : F, mcaEvent (F := F) (Cbot : Set (ι → F)) δ
      (slopeStack A φ 0) (slopeStack A φ 1) γ := by
    intro γ
    have hi₀ : (↑(e.symm γ) : ι) ∈ A := (e.symm γ).2
    have hφ : φ (↑(e.symm γ) : ι) = γ := by
      have hd : φ (↑(e.symm γ) : ι) = e ⟨(↑(e.symm γ) : ι), hi₀⟩ := dif_pos hi₀
      rw [hd]
      exact Equiv.apply_symm_apply e γ
    rw [← hφ]
    exact mcaEvent_slopeStack hAcard_le hi₀
  -- `Pr_γ[mcaEvent] = 1`, hence `ε_mca ≥ 1`.
  have hcardF_pos : (0 : ℕ) < Fintype.card F := Fintype.card_pos
  have hPr1 : Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (Cbot : Set (ι → F)) δ
      (slopeStack A φ 0) (slopeStack A φ 1) γ] = 1 := by
    rw [prob_uniform_eq_card_filter_div_card,
      Finset.filter_true_of_mem (fun γ _ => hall γ), Finset.card_univ]
    simp only [ENNReal.coe_natCast]
    exact ENNReal.div_self (by exact_mod_cast hcardF_pos.ne') (ENNReal.natCast_ne_top _)
  rw [← hPr1]
  unfold epsMCA
  exact le_iSup (fun u : WordStack F (Fin 2) ι =>
    Pr_{let γ ← $ᵖ F}[mcaEvent (F := F) (Cbot : Set (ι → F)) δ (u 0) (u 1) γ])
    (slopeStack A φ)

end Saturated

/-! ## Source audit -/

#print axioms epsMCA_bot_eq_one_of_saturated

end ProximityGap.MCAZeroCode
