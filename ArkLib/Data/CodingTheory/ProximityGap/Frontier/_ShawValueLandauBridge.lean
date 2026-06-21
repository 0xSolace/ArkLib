/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueCapstone
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Door (iv) Lane-2 — the Shaw value `O(1)` predicate IS Mathlib's Landau `=O[atTop] 1`

The Shaw-value capstone (`ShawValueCapstone`) packages the prize reduction
`prize ⇔ Sh(n)=O(1)` using the predicate

  `ShawOOneOn q n M  :=  ∃ C ≥ 0, ∀ i, shawValue (q i) (n i) (M i) ≤ C`

i.e. "one absolute constant bounds the Shaw value over the whole family". That `∃`-uniform-constant
form is the *mathematically correct* reading of the prose slogan `Sh(n)=O(1)`, but it is stated in
elementary `∀/∃` language. A referee citing the capstone will expect the slogan in **Mathlib's
official Landau notation** `Asymptotics.IsBigO`. This file proves that the campaign's `ShawOOneOn`
predicate is *literally* the Landau statement

  `(fun i => shawValue (q i) (n i) (M i)) =O[atTop] (fun _ => (1 : ℝ))`

for an `ℕ`-indexed prize family, closing the notational gap between the campaign's elementary
predicate and the symbol a number theorist would write.

Two honest subtleties, both handled:

* `=O[atTop] 1` is an *eventual* (cofinite) bound; `ShawOOneOn` is a *global* `∀`-bound. Over `ℕ`
  the two coincide **only when `shawValue` is nonnegative on the family** (which it is in the prize
  regime, `M ≥ 0` and a positive scale), because then the finitely many small-index terms have a
  finite maximum that can be absorbed into the constant. We therefore state the full equivalence
  under a pointwise `0 ≤ shawValue` hypothesis, and give the unconditional forward implication
  (`ShawOOneOn → IsBigO`) separately.
* `IsBigO ... 1` is phrased through `‖·‖`. We discharge `‖shawValue ...‖ = shawValue ...` from the
  nonnegativity hypothesis.

Nothing here proves the open Gauss-period bound. It is a pure notation bridge for the citable
Lane-2 capstone: it asserts no new analytic estimate. CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Asymptotics Filter

namespace ProximityGap.Frontier.ShawValueCapstone

/-- The `ℕ`-indexed Shaw-value sequence of a prize family, as a function for Landau notation. -/
noncomputable def shawSeq (q n M : ℕ → ℝ) : ℕ → ℝ :=
  fun i => shawValue (q i) (n i) (M i)

/-- **Forward bridge.**  Under pointwise nonnegativity of the Shaw value (the prize regime), a global
uniform Shaw bound `Sh ≤ C` over the whole `ℕ` family is in particular a Landau `O(1)` bound: the
Shaw sequence is `=O[atTop] 1`.  (Nonnegativity is needed only to control the `‖·‖` lower side; without
it a value `≤ C` could still have large norm by being very negative.) -/
theorem shawSeq_isBigO_one_of_shawOOneOn {q n M : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i))
    (h : ShawOOneOn q n M) :
    (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨C, _hC, hbound⟩ := h
  rw [isBigO_one_iff]
  refine ⟨C, ?_⟩
  rw [eventually_map]
  filter_upwards with i
  -- `‖shawSeq i‖ = shawSeq i ≤ C` from nonnegativity and the global bound.
  rw [show ‖shawSeq q n M i‖ = shawSeq q n M i from abs_of_nonneg (hnn i)]
  exact hbound i

/-- **Backward bridge (needs nonnegativity).**  If the Shaw value is pointwise nonnegative on the
family (the prize-regime situation `M ≥ 0`, positive scale), then a Landau `O(1)` bound on the Shaw
sequence upgrades to a *global* uniform Shaw bound `ShawOOneOn`.  The cofinite-to-global step uses
that, over `ℕ`, the finitely many sub-threshold indices have a finite maximum. -/
theorem shawOOneOn_of_shawSeq_isBigO_one {q n M : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i))
    (h : (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ))) :
    ShawOOneOn q n M := by
  rw [isBigO_one_iff] at h
  obtain ⟨B, hB⟩ := h
  rw [eventually_map, eventually_atTop] at hB
  obtain ⟨N, hN⟩ := hB
  classical
  -- Prefix budget: each sub-threshold value is `≤ ∑_{j<N} shawSeq j` because every term is `≥ 0`.
  set P : ℝ := ∑ j ∈ Finset.range N, shawSeq q n M j with hP
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun j _ => hnn j)
  have hBnn : 0 ≤ B := by
    have := hN N (le_refl N)
    exact le_trans (abs_nonneg _) (by simpa using this)
  -- Constant: max of the eventual bound `B` and the finite prefix budget `P`.
  refine ⟨max B P, le_max_of_le_left hBnn, ?_⟩
  · intro i
    rcases le_or_gt N i with hi | hi
    · -- eventual regime: `shawSeq i = ‖shawSeq i‖ ≤ B ≤ max B P`
      have h1 : shawValue (q i) (n i) (M i) ≤ B := by
        have := hN i hi
        simpa [shawSeq, abs_of_nonneg (hnn i)] using this
      exact le_trans h1 (le_max_left _ _)
    · -- prefix regime: `shawSeq i ≤ ∑_{j<N} shawSeq j = P ≤ max B P`
      have hmem : i ∈ Finset.range N := Finset.mem_range.2 hi
      have h2 : shawSeq q n M i ≤ P := by
        rw [hP]
        exact Finset.single_le_sum (fun j _ => hnn j) hmem
      exact le_trans h2 (le_max_right _ _)

/-- **Landau capstone (Lane-2).**  On an `ℕ`-indexed prize family with pointwise nonnegative Shaw
value, the campaign predicate `ShawOOneOn` is *literally* Mathlib's Landau statement
`shawSeq =O[atTop] 1`.  This is the notation bridge: the prose slogan `Sh(n)=O(1)` and the campaign's
`∃`-uniform-constant predicate are the same `Asymptotics.IsBigO` object a number theorist would cite.
No new analytic bound; CORE stays OPEN. -/
theorem shawOOneOn_iff_shawSeq_isBigO_one {q n M : ℕ → ℝ}
    (hnn : ∀ i, 0 ≤ shawValue (q i) (n i) (M i)) :
    ShawOOneOn q n M ↔ (shawSeq q n M) =O[atTop] (fun _ => (1 : ℝ)) :=
  ⟨shawSeq_isBigO_one_of_shawOOneOn hnn, shawOOneOn_of_shawSeq_isBigO_one hnn⟩

end ProximityGap.Frontier.ShawValueCapstone
