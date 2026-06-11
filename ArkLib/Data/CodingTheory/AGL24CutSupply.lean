/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24WeakPartition

/-!
# [AGL24]/Frank: the cut supply — every cut of a WPC hypergraph has `k` border edges
# (issue #354, Frank front, brick F1)

The first brick of the `FrankOrientationResidual` campaign: weak partition connectivity
applied to a **two-cell partition** `{T, Tᶜ}` yields the cut condition that Frank's
orientation theorem consumes — every proper nonempty vertex subset is crossed by at least
`k` edges. (This is the *necessary* side of the orientation theorem and the supply that any
greedy/uncrossing construction of the crossing-orientation must draw on; it also subsumes
brick 21's vertex-degree bound as the `T = {j}` case.)

* `twoCellPartition` — the partition `{T, Tᶜ}` of a proper nonempty subset;
* `edgeCrosses` / `borderEdges` — named cut-crossing objects;
* `wpc_border_ge` — **the cut supply**: `k ≤ #{i | eᵢ touches both T and Tᶜ}`.
-/

open Finset

namespace AGL24

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A single edge crosses the cut `T` when it touches `T` and is not contained in `T`. -/
def edgeCrosses (E T : Finset V) : Prop :=
  (E ∩ T).Nonempty ∧ ¬ E ⊆ T

/-- The edges crossing the cut `T`: they touch `T` and are not contained in `T`. -/
noncomputable def borderEdges {ι : Type*} [Fintype ι] (e : ι → Finset V)
    (T : Finset V) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T)

omit [Fintype V] in
@[simp] theorem mem_borderEdges {ι : Type*} [Fintype ι] (e : ι → Finset V)
    (T : Finset V) (i : ι) :
    i ∈ borderEdges e T ↔ edgeCrosses (e i) T := by
  classical
  simp [borderEdges, edgeCrosses]

/-- The two-cell partition `{T, univ \ T}` of a proper nonempty subset `T`. -/
def twoCellPartition (T : Finset V) (hT : T.Nonempty) (hTne : T ≠ Finset.univ) :
    Finpartition (Finset.univ : Finset V) where
  parts := {T, Finset.univ \ T}
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro c₁ hc₁ c₂ hc₂ hne
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hc₁ hc₂
    rcases hc₁ with rfl | rfl <;> rcases hc₂ with rfl | rfl
    · exact absurd rfl hne
    · exact Finset.disjoint_sdiff
    · exact Finset.sdiff_disjoint
    · exact absurd rfl hne
  sup_parts := by
    rw [Finset.sup_insert, Finset.sup_singleton]
    rw [Finset.sup_eq_union]
    show id T ∪ id (Finset.univ \ T) = Finset.univ
    rw [id, id]
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ T)]
  bot_notMem := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    push Not
    constructor
    · intro h
      obtain ⟨x, hx⟩ := hT
      rw [← h] at hx
      exact absurd hx (Finset.notMem_empty x)
    · intro h
      obtain ⟨x, hx⟩ : ∃ x, x ∉ T := by
        by_contra hall
        push Not at hall
        exact hTne (Finset.eq_univ_iff_forall.mpr hall)
      have : x ∈ Finset.univ \ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [← h] at this
      exact absurd this (Finset.notMem_empty x)

/-- **The cut supply** (the necessary side of Frank's orientation theorem): every proper
nonempty vertex subset of a `k`-weakly-partition-connected family is crossed by at least `k`
edges. -/
theorem wpc_border_ge {ι : Type*} [Fintype ι] {k : ℕ}
    (e : ι → Finset V) (T : Finset V) (hT : T.Nonempty) (hTne : T ≠ Finset.univ)
    (h : WeaklyPartitionConnected k (Finset.univ : Finset V) e) :
    k ≤ (borderEdges e T).card := by
  classical
  have hP := h (twoCellPartition T hT hTne)
  -- The partition has two parts.
  have hTT : T ≠ Finset.univ \ T := by
    intro heq
    obtain ⟨x, hx⟩ := hT
    have := heq ▸ hx
    exact absurd hx (Finset.mem_sdiff.mp this).2
  have hcard : (twoCellPartition T hT hTne).parts.card = 2 := by
    unfold twoCellPartition
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact hTT), Finset.card_singleton]
  rw [hcard] at hP
  -- Per edge: touched − 1 ≤ border indicator.
  have hper : ∀ i, (touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ)).card - 1
      ≤ (if (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T then 1 else 0) := by
    intro i
    by_cases hborder : (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T
    · rw [if_pos hborder]
      have : (touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ)).card ≤ 2 := by
        refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
        rw [hcard]
      omega
    · rw [if_neg hborder]
      rw [not_and_or] at hborder
      -- The edge misses one of the two cells: at most one touched cell.
      have hsub : ∃ c₀ : Finset V,
          touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ) ⊆ {c₀} := by
        rcases hborder with hmiss | hsub
        · -- e i misses T: only the complement cell can be touched.
          refine ⟨Finset.univ \ T, fun c hc => ?_⟩
          unfold touchedCells at hc
          rw [Finset.mem_filter] at hc
          obtain ⟨hcparts, x, hx⟩ := hc
          unfold twoCellPartition at hcparts
          rw [Finset.mem_insert, Finset.mem_singleton] at hcparts
          rcases hcparts with rfl | rfl
          · exfalso
            apply hmiss
            rw [Finset.mem_inter, Finset.mem_inter] at hx
            exact ⟨x, Finset.mem_inter.mpr ⟨hx.1.1, hx.2⟩⟩
          · exact Finset.mem_singleton_self _
        · -- e i ⊆ T: only the T cell can be touched.
          rw [not_not] at hsub
          refine ⟨T, fun c hc => ?_⟩
          unfold touchedCells at hc
          rw [Finset.mem_filter] at hc
          obtain ⟨hcparts, x, hx⟩ := hc
          unfold twoCellPartition at hcparts
          rw [Finset.mem_insert, Finset.mem_singleton] at hcparts
          rcases hcparts with rfl | rfl
          · exact Finset.mem_singleton_self _
          · exfalso
            rw [Finset.mem_inter, Finset.mem_inter] at hx
            obtain ⟨⟨hxe, -⟩, hxc⟩ := hx
            exact (Finset.mem_sdiff.mp hxc).2 (hsub hxe)
      obtain ⟨c₀, hc₀⟩ := hsub
      have := Finset.card_le_card hc₀
      rw [Finset.card_singleton] at this
      omega
  calc k = k * (2 - 1) := by omega
  _ ≤ ∑ i, ((touchedCells (twoCellPartition T hT hTne) (e i ∩ Finset.univ)).card - 1) := hP
  _ ≤ ∑ i, (if (e i ∩ T).Nonempty ∧ ¬ e i ⊆ T then 1 else 0) :=
      Finset.sum_le_sum fun i _ => hper i
  _ = (borderEdges e T).card := by
      rw [borderEdges, Finset.card_filter]

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.mem_borderEdges
#print axioms AGL24.wpc_border_ge
