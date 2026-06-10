/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSCellProduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonCountWiring

/-!
# Cells to dichotomy bundles — the GS production wired into the Johnson endgame

`exists_cell_production_total` (in-tree, no production hypothesis) decomposes each word
stack's bad scalars into a degenerate cell (explicitly bounded) plus per-irreducible-factor
cells with uniform decode families.  This file converts that cell structure into a
`Hab25JohnsonDichotomyData` bundle — the residual shape of the dichotomy funnel — given
exactly one per-cell input: **each factor cell is small or admits an improving affine
pair** ([Hab25] Claim 1, the K4/Hensel dichotomy).

The degenerate cell takes the small branch outright (its explicit bound is below the
threshold `T` by hypothesis); factor cells take whichever branch the per-cell input
provides.  The bundle's proven counting theorem (`disagree_card_le`) then bounds the
stack's bad scalars by `ℓ · max T n` with `ℓ = |Index|` — narrowing the dichotomy-funnel
obligation of `Hab25JohnsonDischarge` to the per-cell Hensel dichotomy in the cell
vocabulary the GS lane actually produces.

## References

* [Hab25] U. Haböck, *A note on mutual correlated agreement for Reed–Solomon codes*,
  ePrint 2025/2110.
* [BCIKS20] ePrint 2020/654, §5 (Claim 5.7 cells; Steps 5–7 dichotomy).
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open Polynomial Polynomial.Bivariate GuruswamiSudan.OverRatFunc
open _root_.ProximityGap Code
open scoped NNReal ENNReal

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

open Classical in
/-- **Cells to dichotomy bundle.**  The in-tree cell production, together with the
per-factor-cell dichotomy (small or improving pair — [Hab25] Claim 1), yields a
`Hab25JohnsonDichotomyData` bundle whose disagreement set is exactly the stack's bad
scalars and whose threshold is `T`. -/
theorem exists_dichotomyData_of_cell_improvement
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (hη : 0 < η) (hδr : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (T : ℕ)
    (hT : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (himpr : ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    ∃ A : Hab25JohnsonDichotomyData domain k η δ hη hδr,
      A.Edis = Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ) ∧
      A.T = T := by
  obtain ⟨Q₀, Index, Ecell, P, hQ₀, hcard, hcover, hdecode, hnone, hnonecard, hfactor⟩ :=
    exists_cell_production_total domain u δ hk1 hkn hm hδ1 hδJ
  refine ⟨⟨Option ((F₀[X])[X][Y]), inferInstance, Index, Index.card, T,
    le_refl _,
    Finset.univ.filter (fun γ : F₀ =>
      mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ),
    Ecell, hcover, ?_⟩, rfl, rfl⟩
  intro ij hij
  match ij with
  | none =>
      exact Or.inl (le_trans hnonecard hT)
  | some R =>
      obtain ⟨hRfac, hRdata⟩ := hfactor R hij
      have hRirr : Irreducible R :=
        UniqueFactorizationMonoid.irreducible_of_factor R
          (Multiset.mem_toFinset.mp hRfac)
      exact himpr R (Ecell (some R)) P hRirr
        (fun γ hγ => hdecode (some R) hij γ hγ)
        (fun γ hγ => (hRdata γ hγ).2)

open Classical in
/-- **The per-stack count from cells.**  Under the per-cell dichotomy, the stack's bad
scalars are bounded by `ℓ · max T n` for the bundle produced from the cell structure —
the dichotomy counting theorem instantiated at the GS cells. -/
theorem badCount_le_of_cell_improvement
    {n k m : ℕ} [NeZero n] (domain : Fin n ↪ F₀)
    (η δ : ℝ≥0) (hη : 0 < η) (hδr : InJohnsonRange domain k η δ)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (hk1 : 1 < k) (hkn : k + 1 ≤ n) (hm : 1 ≤ m)
    (hδ1 : δ ≤ 1) (hδJ : (δ : ℝ) < gs_johnson k n m)
    (T : ℕ)
    (hT : n * (GuruswamiSudan.constraintIndices m).card * gs_degree_bound k n m ≤ T)
    (himpr : ∀ (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X]),
      Irreducible R →
      (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
      (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
          R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
      E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
        ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    ∃ ℓ : ℕ,
      (Finset.univ.filter (fun γ : F₀ =>
        mcaEvent ((ReedSolomon.code domain k : Set (Fin n → F₀))) δ (u 0) (u 1) γ)).card
        ≤ ℓ * max T (Fintype.card (Fin n)) := by
  obtain ⟨A, hEdis, hAT⟩ := exists_dichotomyData_of_cell_improvement domain η δ hη hδr u
    hk1 hkn hm hδ1 hδJ T hT himpr
  refine ⟨A.ℓ, ?_⟩
  have h := A.disagree_card_le
  rw [hEdis, hAT] at h
  exact h

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_dichotomyData_of_cell_improvement
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.badCount_le_of_cell_improvement
