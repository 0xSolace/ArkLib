/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Johnson

/-!
# Hab25 §3 Step S11 — the numeric edge, reduced to per-stack covers + closed-form arithmetic

`Hab25Johnson.lean` left the final step S11 as the *atomic* residual `JohnsonNumericBound`
(`ε_mca(RS, δ) ≤ ofReal (johnsonBoundReal …)`). This file **opens that residual up**: the
probability side is pure counting, so the Johnson MCA bound follows from

1. a **per-stack Theorem-2 cover** (the S10-shape data: for every word pair `u`, the bad
   scalars are covered by `≤ L` per-factor sets, each pinned by the affine-functional
   improvement property) — discharged internally by the *proven* integer endgame
   `claim1_theorem2_integer` (`|E_u| ≤ L·n`); and
2. one **closed-form real inequality** `L·n / |F| ≤ johnsonBoundReal …` (pure parameter
   arithmetic, no probability and no algebra).

Main results:

* `epsMCA_le_card_div_card` — the S11 probability step is *counting*: if every stack's bad
  scalar set has `≤ N` elements then `ε_mca ≤ N / |F|`
  (via `prob_uniform_eq_card_filter_div_card`);
* `johnsonNumericBound_of_count` — `JohnsonNumericBound` from a per-stack count plus the
  real edge `N/|F| ≤ johnsonBoundReal`;
* `johnsonNumericBound_of_per_stack_cover` / `mca_johnson_of_per_stack_cover` — the
  capstone: per-stack S10 covers (factor index of size `≤ L`, affine-pair difference
  vectors, cover, improvement) **+** the closed-form inequality imply the Johnson-range
  MCA bound. The count `|E_u| ≤ L·n` is supplied by the proven combinatorial endgame —
  no counting residual remains.

After this file, the entire Hab25 §3 chain S1–S11 for the Johnson MCA bound is proven
modulo exactly two inputs: the per-stack S10 cover data (whose divisibility skeleton is the
proven `GSIntegerRepresentative`/`GSSpecializedConditions` bridge) and one parameter
inequality. Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable {A₀ : Type} [Fintype A₀] [DecidableEq A₀] [AddCommGroup A₀] [Module F₀ A₀]

open Classical in
/-- **The S11 probability step is counting.** If for every word stack `u` the set of bad
scalars (those triggering the `mcaEvent`) has at most `N` elements, then
`ε_mca(C, δ) ≤ N / |F|`: each summand of the `ε_mca` sup is a uniform probability, which
is exactly `(#bad)/|F|`. -/
theorem epsMCA_le_card_div_card (C : Set (ι₀ → A₀)) (δ : ℝ≥0) (N : ℕ)
    (hcount : ∀ u : WordStack A₀ (Fin 2) ι₀,
      (Finset.univ.filter
        (fun γ : F₀ => mcaEvent (F := F₀) C δ (u 0) (u 1) γ)).card ≤ N) :
    epsMCA (F := F₀) C δ ≤ (N : ENNReal) / (Fintype.card F₀ : ENNReal) := by
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  have hden : (((Fintype.card F₀ : ℝ≥0)) : ENNReal) = (Fintype.card F₀ : ENNReal) := by
    simp [ENNReal.coe_natCast]
  rw [hden]
  refine ENNReal.div_le_div_right ?_ _
  have h := hcount u
  calc (((Finset.univ.filter
        (fun γ : F₀ => mcaEvent (F := F₀) C δ (u 0) (u 1) γ)).card : ℝ≥0) : ENNReal)
      = ((Finset.univ.filter
        (fun γ : F₀ => mcaEvent (F := F₀) C δ (u 0) (u 1) γ)).card : ENNReal) := by
        simp [ENNReal.coe_natCast]
    _ ≤ (N : ENNReal) := by exact_mod_cast h

open Classical in
/-- **`JohnsonNumericBound` from a per-stack count.** The S11 residual follows from a
uniform per-stack bad-scalar count `N` together with the closed-form real inequality
`N/|F| ≤ johnsonBoundReal` — no probability content remains. -/
theorem johnsonNumericBound_of_count
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (N : ℕ)
    (hcount : ∀ u : WordStack F₀ (Fin 2) ι₀,
      (Finset.univ.filter
        (fun γ : F₀ => mcaEvent (F := F₀)
          ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)).card ≤ N)
    (hreal : (N : ℝ) / (Fintype.card F₀ : ℝ) ≤ johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ := by
  rw [JohnsonNumericBound]
  refine le_trans
    (epsMCA_le_card_div_card ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ N hcount) ?_
  have hpos : (0 : ℝ) < (Fintype.card F₀ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h1 : (N : ENNReal) / (Fintype.card F₀ : ENNReal) =
      ENNReal.ofReal ((N : ℝ) / (Fintype.card F₀ : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [h1]
  exact ENNReal.ofReal_le_ofReal hreal

open Classical in
/-- **The S11 capstone: per-stack Theorem-2 covers + closed-form arithmetic ⟹
`JohnsonNumericBound`.**

If for **every** word stack `u` there is S10-shape data — a factor index set of size `≤ L`,
per-factor affine-pair difference vectors `(d₀, d₁)`, a cover of the bad scalars by the
per-factor sets, and the affine-functional improvement property — then the *proven*
combinatorial endgame `claim1_theorem2_integer` bounds every stack's bad set by `L·n`, and
the single real inequality `L·n/|F| ≤ johnsonBoundReal` closes S11. The previously-atomic
probability residual is gone. -/
theorem johnsonNumericBound_of_per_stack_cover
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
        (d₀ d₁ : Idx → ι₀ → F₀) (Efactor : Idx → Finset F₀),
        Index.card ≤ L ∧
        (Finset.univ.filter
          (fun γ : F₀ => mcaEvent (F := F₀)
            ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)) ⊆
          Index.biUnion Efactor ∧
        ∀ ij ∈ Index, ∀ z ∈ Efactor ij,
          ∃ x ∈ disagreeSet (d₀ ij) (d₁ ij), affineGap (d₀ ij) (d₁ ij) z x = 0)
    (hreal : ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ) :
    JohnsonNumericBound domain k η δ := by
  refine johnsonNumericBound_of_count domain k η δ (L * Fintype.card ι₀) ?_ hreal
  intro u
  obtain ⟨Idx, _, Index, d₀, d₁, Efactor, hL, hcov, hImp⟩ := hdata u
  exact le_trans
    (claim1_theorem2_integer _ Index Efactor L d₀ d₁ hL hcov hImp) (le_refl _)

open Classical in
/-- **The Johnson-range MCA bound from per-stack covers (no numeric residual).**

The headline composition: per-stack S10 cover data + the closed-form parameter inequality
imply `ε_mca(RS[F, D, k], δ) ≤ ofReal (johnsonBoundReal …)` directly — the conclusion of
`mca_johnson_of_residuals`, with the `hNumeric` field *derived* instead of assumed. -/
theorem mca_johnson_of_per_stack_cover
    (domain : ι₀ ↪ F₀) (k : ℕ) (η δ : ℝ≥0) (L : ℕ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
        (d₀ d₁ : Idx → ι₀ → F₀) (Efactor : Idx → Finset F₀),
        Index.card ≤ L ∧
        (Finset.univ.filter
          (fun γ : F₀ => mcaEvent (F := F₀)
            ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)) ⊆
          Index.biUnion Efactor ∧
        ∀ ij ∈ Index, ∀ z ∈ Efactor ij,
          ∃ x ∈ disagreeSet (d₀ ij) (d₁ ij), affineGap (d₀ ij) (d₁ ij) z x = 0)
    (hreal : ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ) :
    epsMCA (F := F₀) (A := F₀) ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ ≤
      ENNReal.ofReal (johnsonBoundReal domain k η δ) :=
  johnsonNumericBound_of_per_stack_cover domain k η δ L hdata hreal

open Classical in
/-- A per-stack cover also upgrades any algebraic-data bundle to the full residual bundle:
the previously-assumed `hNumeric` field is now derived. -/
def Hab25JohnsonResiduals.ofAlgebraicDataAndCover
    {domain : ι₀ ↪ F₀} {k : ℕ} {η δ : ℝ≥0}
    {hη : 0 < η} {hδ : InJohnsonRange domain k η δ}
    (A : Hab25JohnsonAlgebraicData domain k η δ hη hδ) (L : ℕ)
    (hdata : ∀ u : WordStack F₀ (Fin 2) ι₀,
      ∃ (Idx : Type) (_ : DecidableEq Idx) (Index : Finset Idx)
        (d₀ d₁ : Idx → ι₀ → F₀) (Efactor : Idx → Finset F₀),
        Index.card ≤ L ∧
        (Finset.univ.filter
          (fun γ : F₀ => mcaEvent (F := F₀)
            ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)) ⊆
          Index.biUnion Efactor ∧
        ∀ ij ∈ Index, ∀ z ∈ Efactor ij,
          ∃ x ∈ disagreeSet (d₀ ij) (d₁ ij), affineGap (d₀ ij) (d₁ ij) z x = 0)
    (hreal : ((L * Fintype.card ι₀ : ℕ) : ℝ) / (Fintype.card F₀ : ℝ) ≤
      johnsonBoundReal domain k η δ) :
    Hab25JohnsonResiduals domain k η δ hη hδ :=
  Hab25JohnsonResiduals.ofAlgebraicData A
    (johnsonNumericBound_of_per_stack_cover domain k η δ L hdata hreal)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.epsMCA_le_card_div_card
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_count
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.johnsonNumericBound_of_per_stack_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mca_johnson_of_per_stack_cover
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonResiduals.ofAlgebraicDataAndCover
