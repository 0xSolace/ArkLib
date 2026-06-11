/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability

/-!
# [Jo26] marked curve decodability and the easy transfer legs (issue #334, K5, brick T1)

The marked half of [Jo26] (ePrint 2026/891) §5.1 over the landed [GG25] definitional brick
(`GG25CurveDecodability.lean`), plus the two elementary legs of the transfer chain:

* `MarkedCurveDecodable` — **[Jo26] Definition 5.1**: the close set is *specified in advance*
  (a set `A₀` of exactly `a` seeds, all `δ`-close), and the curve witness must live inside
  `A₀`.  This is the formulation the row-combination proof of the interleaving transfer
  needs: projections can create additional close points, and a witness using projected-only
  close points would not be a witness for the interleaved instance.
* `CurveDecodable.of_marked` — the **easy direction of [Jo26] Theorem 5.5**: marked
  decodability implies [GG25] decodability (choose any `a`-subset of the full close set;
  a marked witness inside it is a witness inside the close set).
* `mem_curveCloseSet_map_of_mem` / `curveCloseSet_subset_map` — **[Jo26] Lemma 5.6**
  (projection does not increase distance), in the generic linear form: for any `F`-linear
  `g : A →ₗ[F] A'`, a seed `δ`-close for the stack `u` and `f` is `δ`-close for the
  pointwise-projected stack `g ∘ u` and `g ∘ f` — coordinates where the symbols agree still
  agree after projecting, and `g` commutes with the curve combination.  Instantiating `g`
  with the row-combination functionals `λ·(−) : (Fin s → A) →ₗ[F] A` of the interleaved code
  gives the paper's statement.

The remaining legs — the interpolation regime (Lemma 5.2), the non-covering condition
(Lemma 5.4) with the hard converse of Theorem 5.5, and the covering-argument transfer
(Theorem 5.7, consuming `exists_nonzero_notMem_of_proper_family`) — are follow-up bricks
T2/T3; nothing here claims them.
-/

open Finset Code
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **[Jo26] Definition 5.1 (marked curve decodability).** `C` is marked
`(ℓ, δ, a, b)`-curve-decodable if for every stack `u`, every codeword-valued `f`, and every
*specified* seed set `A₀` of exactly `a` seeds all of which are `δ`-close, some codeword curve
explains `f` on at least `b` seeds **inside `A₀`**. -/
def MarkedCurveDecodable (C : Set (ι → A)) (ℓ : ℕ) (δ : ℝ≥0) (a b : ℕ) : Prop :=
  ∀ (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A), (∀ α, f α ∈ C) →
    ∀ A₀ : Finset F, A₀.card = a →
    (∀ α ∈ A₀,
      (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ) →
    ∃ cs : Fin (ℓ + 1) → ι → A, (∀ j, cs j ∈ C) ∧
      b ≤ (A₀.filter
        (fun α => f α = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • cs j i)).card

/-- Members of the close set satisfy the distance bound (definitional unpacking). -/
theorem dist_le_of_mem_curveCloseSet {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {α : F}
    (hα : α ∈ curveCloseSet δ u f) :
    (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ := by
  simpa [curveCloseSet] using hα

/-- **The easy direction of [Jo26] Theorem 5.5**: marked curve decodability implies [GG25]
curve decodability.  Given a close set of size at least `a`, pick any `a`-subset as the
specified `A₀`; its seeds are `δ`-close, and a marked witness inside `A₀` is a witness inside
the full close set. -/
theorem CurveDecodable.of_marked {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b : ℕ}
    (h : MarkedCurveDecodable (F := F) C ℓ δ a b) :
    CurveDecodable (F := F) C ℓ δ a b := by
  intro u f hf hclose
  obtain ⟨A₀, hsub, hcard⟩ := Finset.exists_subset_card_eq hclose
  obtain ⟨cs, hcs, hcount⟩ := h u f hf A₀ hcard
    (fun α hα => dist_le_of_mem_curveCloseSet (hsub hα))
  exact ⟨cs, hcs, le_trans hcount (Finset.card_le_card
    (Finset.filter_subset_filter _ hsub))⟩

section Projection

variable {A' : Type} [Fintype A'] [DecidableEq A'] [AddCommGroup A'] [Module F A']

/-- Pointwise application of a map does not increase the relative Hamming distance:
coordinates where the words agree still agree after mapping. -/
theorem relHammingDist_map_le (g : A → A') (x y : ι → A) :
    δᵣ( (fun i => g (x i)), (fun i => g (y i)) ) ≤ δᵣ(x, y) := by
  unfold relHammingDist
  refine div_le_div_of_nonneg_right ?_ (by positivity) |>.trans le_rfl
  · norm_cast
    unfold hammingDist
    refine Finset.card_le_card fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hxy
    exact hi (by rw [hxy])

/-- A linear map commutes with the curve combination. -/
theorem linearMap_curveComb (g : A →ₗ[F] A') {ℓ : ℕ} (u : Fin (ℓ + 1) → ι → A)
    (α : F) (i : ι) :
    g (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i)
      = ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • g (u j i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => g.map_smul _ _

/-- **[Jo26] Lemma 5.6 (projection does not increase distance), generic linear form.**  A
seed in the close set of `(u, f)` is in the close set of the pointwise-projected instance
`(g ∘ u, g ∘ f)`, for any `F`-linear `g`. Instantiating `g := λ·(−)` (the row-combination
functional of the interleaved code) gives the paper's statement. -/
theorem mem_curveCloseSet_map_of_mem (g : A →ₗ[F] A') {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {α : F}
    (hα : α ∈ curveCloseSet δ u f) :
    α ∈ curveCloseSet δ (fun j i => g (u j i)) (fun β i => g (f β i)) := by
  simp only [curveCloseSet, mem_filter, mem_univ, true_and] at hα ⊢
  refine le_trans ?_ hα
  have hcomb : (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • g (u j i))
      = fun i => g (∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i) := by
    funext i
    exact (linearMap_curveComb g u α i).symm
  rw [hcomb]
  exact_mod_cast relHammingDist_map_le (fun x => g x)
    (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i) (f α)

/-- Set form of the projection lemma: the close set of `(u, f)` is contained in the close
set of the projected instance. -/
theorem curveCloseSet_subset_map (g : A →ₗ[F] A') (δ : ℝ≥0) {ℓ : ℕ}
    (u : Fin (ℓ + 1) → ι → A) (f : F → ι → A) :
    curveCloseSet δ u f
      ⊆ curveCloseSet δ (fun j i => g (u j i)) (fun β i => g (f β i)) :=
  fun _ hα => mem_curveCloseSet_map_of_mem g hα

/-- **The marked instance survives projection** ([Jo26] Lemma 5.6 in the form Theorem 5.7
consumes): if every seed of the specified `A₀` is `δ`-close for `(u, f)`, then every seed of
`A₀` is `δ`-close for the projected instance — *the same* `A₀`, which is exactly why the
marked formulation is the right one for the row-combination argument. -/
theorem marked_dist_le_map (g : A →ₗ[F] A') {δ : ℝ≥0} {ℓ : ℕ}
    {u : Fin (ℓ + 1) → ι → A} {f : F → ι → A} {A₀ : Finset F}
    (h : ∀ α ∈ A₀,
      (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • u j i), f α ) : ℝ≥0) ≤ δ) :
    ∀ α ∈ A₀,
      (δᵣ( (fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • g (u j i)),
        (fun i => g (f α i)) ) : ℝ≥0) ≤ δ := by
  intro α hα
  have hmem : α ∈ curveCloseSet δ u f := by
    simp only [curveCloseSet, mem_filter, mem_univ, true_and]
    exact h α hα
  have := mem_curveCloseSet_map_of_mem g hmem
  simpa [curveCloseSet] using this

end Projection

/-- Marked decodability is monotone exactly like the unmarked form. -/
theorem MarkedCurveDecodable.mono {C : Set (ι → A)} {ℓ : ℕ} {δ : ℝ≥0} {a b b' : ℕ}
    (h : MarkedCurveDecodable (F := F) C ℓ δ a b) (hb : b' ≤ b) :
    MarkedCurveDecodable (F := F) C ℓ δ a b' := by
  intro u f hf A₀ hcard hdist
  obtain ⟨cs, hcs, hcount⟩ := h u f hf A₀ hcard hdist
  exact ⟨cs, hcs, le_trans hb hcount⟩

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.CurveDecodable.of_marked
#print axioms ProximityGap.mem_curveCloseSet_map_of_mem
#print axioms ProximityGap.curveCloseSet_subset_map
#print axioms ProximityGap.marked_dist_le_map
#print axioms ProximityGap.MarkedCurveDecodable.mono
