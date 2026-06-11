/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24Orientation
import ArkLib.Data.CodingTheory.AGL24CutSupply

/-!
# [AGL24]/Frank: submodularity of the entering-border count (issue #354, Frank brick F2)

The uncrossing engine of the orientation theorem: for any head orientation, the count of
edges entering a vertex set (head inside, vertices not contained) is **submodular**. This is
what makes the family of deficient sets closed under union/intersection in the
reorientation argument (F3), exactly as in the digraph case — the hypergraph head-model
preserves it.

* `headBorderEdges` / `inBorder` — the entering-border set and count;
* `cutDeficiency` — the positive part of the missing entering-border count;
* `inBorder_submodular` — `in(T∪S) + in(T∩S) ≤ in(T) + in(S)` (per-edge case analysis:
  the only nontrivial case is a head in `T∩S` with the edge inside `T∪S` but not `T∩S`,
  where the right side picks up the crossing of whichever of `T, S` the edge escapes).
* `exists_updateHead_decreases_positive_deficiency_cut` — the local one-cut reorientation
  decrease used by the eventual Frank sufficiency proof.
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- The cut-crossing edges whose current orientation head lies in `T`. -/
noncomputable def headBorderEdges {e : ι → Finset V} (O : HeadOrientation e)
    (T : Finset V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)

omit [DecidableEq ι] [Fintype V] in
@[simp] theorem mem_headBorderEdges {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (i : ι) :
    i ∈ headBorderEdges O T ↔ O.head i ∈ T ∧ ¬ e i ⊆ T := by
  classical
  simp [headBorderEdges]

/-- The entering-border count of an oriented hypergraph at a vertex set: edges whose head
lies inside but whose vertex set is not contained. -/
def inBorder {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V) : ℕ :=
  (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card

omit [DecidableEq ι] [Fintype V] in
theorem inBorder_eq_card_headBorderEdges {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) :
    inBorder O T = (headBorderEdges O T).card := by
  classical
  simp [inBorder, headBorderEdges]

/-- The positive part of the missing head-border count for a Frank cut. -/
def cutDeficiency {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V)
    (k : ℕ) : ℕ :=
  k - inBorder O T

omit [DecidableEq ι] [Fintype V] in
theorem headBorderEdges_subset_borderEdges {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (hne : ∀ i, (e i).Nonempty) :
    headBorderEdges O T ⊆ borderEdges e T := by
  intro i hi
  rw [mem_headBorderEdges] at hi
  rw [mem_borderEdges, edgeCrosses]
  exact ⟨⟨O.head i, Finset.mem_inter.mpr ⟨O.head_mem i (hne i), hi.1⟩⟩, hi.2⟩

omit [DecidableEq ι] [Fintype V] in
theorem headBorderEdges_card_le_borderEdges_card {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (hne : ∀ i, (e i).Nonempty) :
    (headBorderEdges O T).card ≤ (borderEdges e T).card :=
  Finset.card_le_card (headBorderEdges_subset_borderEdges O T hne)

omit [DecidableEq ι] [Fintype V] in
theorem cutDeficiency_pos_iff {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) (k : ℕ) :
    0 < cutDeficiency O T k ↔ inBorder O T < k := by
  rw [cutDeficiency, Nat.sub_pos_iff_lt]

omit [DecidableEq ι] [Fintype V] in
theorem cutDeficiency_eq_zero_of_le {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {k : ℕ}
    (h : k ≤ inBorder O T) :
    cutDeficiency O T k = 0 := by
  rw [cutDeficiency, Nat.sub_eq_zero_of_le h]

omit [DecidableEq ι] [Fintype V] in
/-- **Submodularity of the entering-border count** (the uncrossing engine of Frank's
orientation theorem). -/
theorem inBorder_submodular {e : ι → Finset V} (O : HeadOrientation e) (T S : Finset V) :
    inBorder O (T ∪ S) + inBorder O (T ∩ S) ≤ inBorder O T + inBorder O S := by
  classical
  unfold inBorder
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  -- Per-edge case analysis.
  by_cases h1 : O.head i ∈ T <;> by_cases h2 : O.head i ∈ S <;>
    by_cases h3 : e i ⊆ T <;> by_cases h4 : e i ⊆ S <;>
      by_cases h5 : e i ⊆ T ∪ S
  all_goals (
    have hu1 : e i ⊆ T → e i ⊆ T ∪ S := fun h => h.trans Finset.subset_union_left
    have hu2 : e i ⊆ S → e i ⊆ T ∪ S := fun h => h.trans Finset.subset_union_right
    have hm1 : O.head i ∈ T → O.head i ∈ T ∪ S := fun h => Finset.mem_union_left _ h
    have hm2 : O.head i ∈ S → O.head i ∈ T ∪ S := fun h => Finset.mem_union_right _ h
    simp_all [Finset.mem_union, Finset.mem_inter, Finset.subset_inter_iff])

omit [DecidableEq ι] [Fintype V] in
theorem mem_headBorderEdges_updateHead_iff {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {i₀ : ι} {v : V}
    (hv : v ∈ e i₀) (hvT : v ∈ T) (hnotSub : ¬ e i₀ ⊆ T) (j : ι) :
    j ∈ headBorderEdges (O.updateHead i₀ v hv) T ↔
      j = i₀ ∨ j ∈ headBorderEdges O T := by
  classical
  by_cases hji : j = i₀
  · subst hji
    rw [mem_headBorderEdges]
    simp [HeadOrientation.updateHead, hnotSub, hvT]
  · simp [headBorderEdges, hji]

omit [DecidableEq ι] [Fintype V] in
theorem headBorderEdges_card_updateHead_eq_succ {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {i₀ : ι} {v : V}
    (hv : v ∈ e i₀) (hvT : v ∈ T) (hnotSub : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T) :
    (headBorderEdges (O.updateHead i₀ v hv) T).card =
      (headBorderEdges O T).card + 1 := by
  classical
  have hnotMem : i₀ ∉ headBorderEdges O T := by
    rw [mem_headBorderEdges]
    exact fun h => hhead h.1
  have hset : headBorderEdges (O.updateHead i₀ v hv) T =
      insert i₀ (headBorderEdges O T) := by
    ext j
    rw [mem_headBorderEdges_updateHead_iff O T hv hvT hnotSub j]
    simp [Finset.mem_insert]
  rw [hset, Finset.card_insert_of_notMem hnotMem]

omit [DecidableEq ι] [Fintype V] in
theorem cutDeficiency_updateHead_lt {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V) {i₀ : ι} {v : V} {k : ℕ}
    (hv : v ∈ e i₀) (hvT : v ∈ T) (hnotSub : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T) (hdef : inBorder O T < k) :
    cutDeficiency (O.updateHead i₀ v hv) T k < cutDeficiency O T k := by
  have hcard := headBorderEdges_card_updateHead_eq_succ O T hv hvT hnotSub hhead
  have hin : inBorder (O.updateHead i₀ v hv) T = inBorder O T + 1 := by
    rw [inBorder_eq_card_headBorderEdges, inBorder_eq_card_headBorderEdges]
    exact hcard
  rw [cutDeficiency, cutDeficiency, hin]
  omega

omit [DecidableEq ι] [Fintype V] in
/-- If the head-border count is strictly smaller than the full border count, some border
edge has not yet been headed into the cut. -/
theorem exists_border_not_head_of_headBorder_lt_border {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V)
    (hlt : (headBorderEdges O T).card < (borderEdges e T).card) :
    ∃ i, i ∈ borderEdges e T ∧ i ∉ headBorderEdges O T := by
  classical
  by_contra h
  push Not at h
  have hsub : borderEdges e T ⊆ headBorderEdges O T := by
    intro i hi
    exact h i hi
  have := Finset.card_le_card hsub
  omega

omit [DecidableEq ι] in
/-- A strictly deficient proper WPC cut has a crossing edge whose head lies outside the cut.
This is the immediate cut supply consumed by later Frank reorientation/uncrossing steps. -/
theorem exists_border_head_outside_of_deficient_cut {k : ℕ} {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V)
    (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hdef : inBorder O T < k) :
    ∃ i, (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T ∧ O.head i ∉ T := by
  classical
  have hborder : k ≤ (borderEdges e T).card := wpc_border_ge e T hT hTne hwpc
  have hdef' : (headBorderEdges O T).card < k := by
    rwa [← inBorder_eq_card_headBorderEdges]
  obtain ⟨i, hiborder, hihead⟩ :=
    exists_border_not_head_of_headBorder_lt_border O T (lt_of_lt_of_le hdef' hborder)
  rw [mem_borderEdges, edgeCrosses] at hiborder
  rw [mem_headBorderEdges] at hihead
  refine ⟨i, hiborder.1, hiborder.2, ?_⟩
  intro hhead
  exact hihead ⟨hhead, hiborder.2⟩

omit [DecidableEq ι] in
/-- Positive `cutDeficiency` form of `exists_border_head_outside_of_deficient_cut`. -/
theorem exists_border_head_outside_of_positive_deficiency {k : ℕ} {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V)
    (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hdef : 0 < cutDeficiency O T k) :
    ∃ i, (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T ∧ O.head i ∉ T := by
  exact exists_border_head_outside_of_deficient_cut O T hT hTne hwpc
    ((cutDeficiency_pos_iff O T k).mp hdef)

omit [DecidableEq ι] [Fintype V] in
theorem exists_updateHead_decreases_cutDeficiency_of_border_head_outside
    {k : ℕ} {e : ι → Finset V} (O : HeadOrientation e) (T : Finset V) {i₀ : ι}
    (hitouch : (e i₀ ∩ T).Nonempty) (hnotSub : ¬ e i₀ ⊆ T)
    (hhead : O.head i₀ ∉ T) (hdef : inBorder O T < k) :
    ∃ O' : HeadOrientation e,
      inBorder O' T = inBorder O T + 1 ∧
        cutDeficiency O' T k < cutDeficiency O T k := by
  obtain ⟨v, hv⟩ := hitouch
  rw [Finset.mem_inter] at hv
  refine ⟨O.updateHead i₀ v hv.1, ?_, ?_⟩
  · rw [inBorder_eq_card_headBorderEdges, inBorder_eq_card_headBorderEdges]
    exact headBorderEdges_card_updateHead_eq_succ O T hv.1 hv.2 hnotSub hhead
  · exact cutDeficiency_updateHead_lt O T hv.1 hv.2 hnotSub hhead hdef

omit [DecidableEq ι] in
/-- Positive-deficiency local reorientation step for a single cut. This is only the one-cut
decrease brick; it does not assert that other cuts remain nondeficient or prove termination. -/
theorem exists_updateHead_decreases_positive_deficiency_cut {k : ℕ} {e : ι → Finset V}
    (O : HeadOrientation e) (T : Finset V)
    (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (hwpc : WeaklyPartitionConnected k (Finset.univ : Finset V) e)
    (hdef : 0 < cutDeficiency O T k) :
    ∃ O' : HeadOrientation e,
      inBorder O' T = inBorder O T + 1 ∧
        cutDeficiency O' T k < cutDeficiency O T k := by
  have hlt : inBorder O T < k := (cutDeficiency_pos_iff O T k).mp hdef
  obtain ⟨i, hitouch, hnotSub, hhead⟩ :=
    exists_border_head_outside_of_deficient_cut O T hT hTne hwpc hlt
  exact exists_updateHead_decreases_cutDeficiency_of_border_head_outside
    O T hitouch hnotSub hhead hlt

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.inBorder_submodular
#print axioms AGL24.exists_border_head_outside_of_positive_deficiency
#print axioms AGL24.exists_updateHead_decreases_positive_deficiency_cut
