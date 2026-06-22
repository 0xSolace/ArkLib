/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_EX_E4f_PathCalibrate

/-!
# BSG `E4g` — the second-fibre choice by apex-averaging on the cherry double-count

This file proves, axiom-clean, the **second-fibre choice** that every prior plan for
`PrunedFibreWithEnergy` identified as the first genuine sub-lemma of Tao–Vu Lemma 2.30: from
cherry-richness, produce a second popular fibre `b₁ ∈ A` whose left-neighbourhood
`N₁ = leftNbhd A G b₁` carries a large share of the *good-pair* common-neighbour mass.

## The mechanism (apex averaging on cherry mass)

Recall (from `_BSG_DRC1`) the cherry double-count
`∑_b rDeg b ^ 2 = ∑_{p ∈ A×A} cn(p)`, and the good-pair Markov split
`sum_commonNeighbors_goodPairs_ge`, which lower-bounds the *good-pair mass* (pairs with
`t ≤ cn`) by `(∑_b rDeg b ^ 2) − #(A×A)·t`.

The new identity here is a **third** double-count. For a fibre `b`, let

  `goodFibre t b := #{p ∈ A×A | t ≤ cn(p) ∧ (p.1,b) ∈ G ∧ (p.2,b) ∈ G}`

count the good pairs *both of whose endpoints lie in* `leftNbhd A G b`. Then, summing over the
apex `b`,

  `∑_{b ∈ A} goodFibre t b = ∑_{good p} cn(p) = goodMass`,

because for a fixed good pair `p`, the `b`'s with `(p.1,b),(p.2,b) ∈ G` are exactly its common
neighbours, of which there are `cn(p)`. Pigeonhole over the apex `b ∈ A` (phrased contrapositively
as in `exists_rDeg_ge_avg`) then yields a fibre `b₁ ∈ A` with

  `goodMass ≤ #A · goodFibre t b₁`.

Since the good pairs counted by `goodFibre t b₁` all live inside `N₁ × N₁`, we get
`goodFibre t b₁ ≤ #N₁ ^ 2`, so `N₁` is large whenever `goodMass` is.

## What this is and is not

This is the apex-averaging step **only** — the choice of `b₁` and the large-`N₁`/large-good-mass
guarantee. The remaining content of `PrunedFibreWithEnergy` (per-`a` Markov pruning of
`A'' ⊆ leftNbhd A G b₀`, every-pair richness against `N₁`, and the relative-difference energy
clause) is *not* in this file; it is left to the downstream residual. As all four prior plans
established, the `PrunedFibreWithEnergy` energy clause as written is not deliverable by genuine
averaging, so this file makes **no** claim to close BSG — it proves the one sub-lemma it targets
and names the rest honestly.

## Status

`PROVES-SUBLEMMA` — `exists_secondFibre_goodMass`, `exists_secondFibre_largeNbhd`, and
`exists_secondFibre_of_cherry` are proven axiom-clean. They do not, by themselves, supply
`PrunedFibreWithEnergy`.

## References
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Lemma 2.30.
* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## The good-pairs-in-a-fibre count and the apex double-count -/

/-- **Good pairs carried by the fibre `b`.** The number of left-pairs `(a,a') ∈ A×A` that are
*good* (have `≥ t` common neighbours) and *both of whose endpoints are adjacent to `b`* (i.e. both
lie in `leftNbhd A G b`). Apex-averaging this over `b ∈ A` recovers the good-pair mass. -/
noncomputable def goodFibre (A : Finset α) (G : Finset (α × α)) (t : ℕ) (b : α) : ℕ :=
  #{p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G}

/-- `goodFibre` as a sum of `{0,1}` indicators over the pairs. -/
lemma goodFibre_eq_sum_indicator (A : Finset α) (G : Finset (α × α)) (t : ℕ) (b : α) :
    goodFibre A G t b
      = ∑ p ∈ A ×ˢ A,
          (if t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G then 1 else 0) := by
  classical
  rw [goodFibre, Finset.card_filter]

/-- **Apex double-count of the good-pair mass.** Summing `goodFibre t b` over apexes `b ∈ A`
recovers the total common-neighbour mass on good pairs:
`∑_{b ∈ A} goodFibre t b = ∑_{good p} cn(p)`.

Both sides count ordered triples `(p.1, p.2, b)` with `p` a good pair and `b` a common neighbour of
`p`; the LHS sums first over `b`, the RHS first over `p`. -/
theorem sum_goodFibre_eq_goodMass (A : Finset α) (G : Finset (α × α)) (t : ℕ) :
    ∑ b ∈ A, goodFibre A G t b
      = ∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2 := by
  classical
  -- LHS as a double sum over `b, p`.
  have hL : ∑ b ∈ A, goodFibre A G t b
      = ∑ b ∈ A, ∑ p ∈ A ×ˢ A,
          (if t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G then 1 else 0) := by
    exact Finset.sum_congr rfl (fun b _ => goodFibre_eq_sum_indicator A G t b)
  rw [hL, Finset.sum_comm]
  -- Now `∑_p ∑_b [good p ∧ p.1,b∈G ∧ p.2,b∈G]`; restrict to good pairs and identify the inner sum
  -- with `cn(p)`.
  rw [← Finset.sum_filter_add_sum_filter_not (A ×ˢ A)
        (fun p => t ≤ commonNeighbors A G p.1 p.2)
        (fun p => ∑ b ∈ A,
          (if t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G then 1 else 0))]
  -- The "not good" block vanishes: each inner indicator is 0.
  have hbad : ∑ p ∈ {p ∈ A ×ˢ A | ¬ t ≤ commonNeighbors A G p.1 p.2}, ∑ b ∈ A,
        (if t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G then 1 else 0) = 0 := by
    refine Finset.sum_eq_zero (fun p hp => ?_)
    rw [mem_filter] at hp
    refine Finset.sum_eq_zero (fun b _ => ?_)
    rw [if_neg]
    exact fun h => hp.2 h.1
  rw [hbad, add_zero]
  -- The "good" block: inner sum over `b` of `[p.1,b∈G ∧ p.2,b∈G]` is `cn(p)` (the good-pair
  -- predicate is now known true, so it drops out of the indicator).
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [mem_filter] at hp
  have hgp : t ≤ commonNeighbors A G p.1 p.2 := hp.2
  -- First rewrite ONLY the RHS `cn(p)` as its indicator sum (leaving the LHS condition intact).
  conv_rhs => rw [commonNeighbors_eq_sum_indicator A G p.1 p.2]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- Goal: `(if t ≤ cn ∧ (p.1,b)∈G ∧ (p.2,b)∈G then 1 else 0) = (if (p.1,b)∈G ∧ (p.2,b)∈G then 1 else 0)`
  by_cases h1 : (p.1, b) ∈ G
  · by_cases h2 : (p.2, b) ∈ G
    · rw [if_pos ⟨hgp, h1, h2⟩, if_pos ⟨h1, h2⟩]
    · rw [if_neg (fun h => h2 h.2.2), if_neg (fun h => h2 h.2)]
  · rw [if_neg (fun h => h1 h.2.1), if_neg (fun h => h1 h.1)]

/-! ## The second-fibre choice (apex averaging / pigeonhole) -/

/-- **Second-fibre choice — apex averaging (PROVEN).** There is a fibre `b₁ ∈ A` whose good-pair
count is at least the apex-average: `goodMass ≤ #A · goodFibre t b₁`, where
`goodMass = ∑_{good p} cn(p)`.

This is the second-fibre pigeonhole: if every `#A · goodFibre t b < goodMass`, summing over the
`#A` apexes gives `#A · goodMass = ∑_b (#A · goodFibre t b) < #A · goodMass` by the apex
double-count, a contradiction. -/
theorem exists_secondFibre_goodMass (A : Finset α) (G : Finset (α × α)) (t : ℕ)
    (hA : A.Nonempty) :
    ∃ b₁ ∈ A,
      (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
        ≤ #A * goodFibre A G t b₁ := by
  classical
  by_contra h
  push_neg at h
  -- h : ∀ b ∈ A, #A * goodFibre A G t b < goodMass
  have hlt :
      ∑ b ∈ A, #A * goodFibre A G t b
        < ∑ _b ∈ A,
            (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2},
              commonNeighbors A G p.1 p.2) :=
    Finset.sum_lt_sum_of_nonempty hA h
  rw [Finset.sum_const, ← Finset.mul_sum, sum_goodFibre_eq_goodMass A G t,
    smul_eq_mul] at hlt
  -- hlt : #A * goodMass < #A * goodMass
  omega

/-- **The chosen second fibre `b₁` has a large left-neighbourhood (PROVEN).** Continuing the apex
average: the good pairs counted by `goodFibre t b₁` all lie inside `N₁ × N₁`
(`N₁ = leftNbhd A G b₁`), so `goodFibre t b₁ ≤ #N₁ ^ 2`. Combined with
`exists_secondFibre_goodMass`, this gives `goodMass ≤ #A · #N₁ ^ 2`: the good-pair mass controls the
square of the second fibre's neighbourhood, so `N₁` is large whenever the cherry-rich good mass is. -/
theorem exists_secondFibre_largeNbhd (A : Finset α) (G : Finset (α × α)) (t : ℕ)
    (hA : A.Nonempty) :
    ∃ b₁ ∈ A,
      (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
        ≤ #A * #(leftNbhd A G b₁) ^ 2 := by
  classical
  obtain ⟨b₁, hb₁A, hb₁⟩ := exists_secondFibre_goodMass A G t hA
  refine ⟨b₁, hb₁A, ?_⟩
  -- goodFibre t b₁ ≤ #(N₁ ×ˢ N₁) = #N₁ ^ 2, by inclusion of the good-fibre pairs into N₁ × N₁.
  have hincl :
      ({p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b₁) ∈ G ∧ (p.2, b₁) ∈ G}
        : Finset (α × α))
        ⊆ (leftNbhd A G b₁) ×ˢ (leftNbhd A G b₁) := by
    intro p hp
    rw [mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, _, hg1, hg2⟩ := hp
    rw [Finset.mem_product]
    exact ⟨by rw [leftNbhd, mem_filter]; exact ⟨hp1, hg1⟩,
           by rw [leftNbhd, mem_filter]; exact ⟨hp2, hg2⟩⟩
  have hcard : goodFibre A G t b₁ ≤ #(leftNbhd A G b₁) ^ 2 := by
    rw [goodFibre]
    calc #{p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2 ∧ (p.1, b₁) ∈ G ∧ (p.2, b₁) ∈ G}
        ≤ #((leftNbhd A G b₁) ×ˢ (leftNbhd A G b₁)) := Finset.card_le_card hincl
      _ = #(leftNbhd A G b₁) ^ 2 := by rw [Finset.card_product]; ring
  calc (∑ p ∈ {p ∈ A ×ˢ A | t ≤ commonNeighbors A G p.1 p.2}, commonNeighbors A G p.1 p.2)
      ≤ #A * goodFibre A G t b₁ := hb₁
    _ ≤ #A * #(leftNbhd A G b₁) ^ 2 := Nat.mul_le_mul_left _ hcard

/-! ## Wiring the cherry-richness lower bound on the good mass

`sum_commonNeighbors_goodPairs_ge` gives `(∑_b rDeg b ^ 2) ≤ goodMass + #(A×A)·t`, i.e.
`goodMass ≥ (∑_b rDeg b ^ 2) − #(A×A)·t`. We package the second-fibre choice directly against the
cherry count, eliminating the intermediate `goodMass`: there is `b₁ ∈ A` with
`(∑_b rDeg b ^ 2) ≤ #A · #N₁ ^ 2 + #(A×A)·t`. -/

/-- **Second fibre against the raw cherry count (PROVEN).** Combining the apex average
`exists_secondFibre_largeNbhd` with the good-pair Markov split `sum_commonNeighbors_goodPairs_ge`:
there is a fibre `b₁ ∈ A` with

  `(∑_b rDeg b ^ 2) ≤ #A · #(leftNbhd A G b₁) ^ 2 + #(A ×ˢ A) · t`.

So once the cherry count `∑_b rDeg b ^ 2` exceeds `#(A×A)·t` (which cherry-richness guarantees for a
threshold `t` below the cherry average), the second fibre's neighbourhood square is forced large. -/
theorem exists_secondFibre_of_cherry (A : Finset α) (G : Finset (α × α)) (t : ℕ)
    (hA : A.Nonempty) :
    ∃ b₁ ∈ A,
      (∑ b ∈ A, rDeg A G b ^ 2) ≤ #A * #(leftNbhd A G b₁) ^ 2 + #(A ×ˢ A) * t := by
  classical
  obtain ⟨b₁, hb₁A, hb₁⟩ := exists_secondFibre_largeNbhd A G t hA
  refine ⟨b₁, hb₁A, ?_⟩
  have hgood := sum_commonNeighbors_goodPairs_ge A G t
  -- hgood : (∑_b rDeg^2) ≤ goodMass + #(A×A)·t ;  hb₁ : goodMass ≤ #A·#N₁^2
  omega

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.sum_goodFibre_eq_goodMass
#print axioms Finset.BSG.exists_secondFibre_goodMass
#print axioms Finset.BSG.exists_secondFibre_largeNbhd
#print axioms Finset.BSG.exists_secondFibre_of_cherry
