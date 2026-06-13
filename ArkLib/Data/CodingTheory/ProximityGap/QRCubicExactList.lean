/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.QRCubicSupplyLower

/-!
# The orbit map onto the sum-zero 3-subsets is surjective (#389)

A step toward the EXACT QR cubic list size: the orbit map `(a,b,c) ↦ {a,b,c}` from the
distinct-entry zero-sum triples onto the sum-zero `3`-subsets is surjective (every such
subset is the image of any ordering of its three elements).  Together with the in-tree
`fiber_card_le` (each fiber `≤ 27`) this re-derives the `Θ(n²)` bound of
`qr_cubic_supply_lower`.  The exact orbit factor (each fiber `= 6`, giving the exact
constant `(q−1)(q−5)/48`) is a documented follow-up.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The orbit map `(a,b,c) ↦ {a,b,c}` is surjective onto the sum-zero `3`-subsets: every
such subset is the image of one of its orderings. -/
theorem image_tripleSet_eq :
    (qrDistinctTriples (F := F)).image tripleSet = qrSumZeroSubsets := by
  apply Finset.Subset.antisymm image_tripleSet_subset
  intro T hT
  rw [qrSumZeroSubsets, Finset.mem_filter, Finset.mem_powersetCard] at hT
  obtain ⟨⟨hsub, hcard⟩, hsum⟩ := hT
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
  rw [Finset.mem_image]
  refine ⟨(x, y, z), ?_, rfl⟩
  rw [qrDistinctTriples, Finset.mem_filter, mem_qrZeroSumTriples]
  refine ⟨⟨hsub (by simp), hsub (by simp), hsub (by simp), ?_⟩, hxy, hxz, hyz⟩
  rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton] at hsum
  linear_combination hsum

end ProximityGap.PairRank
