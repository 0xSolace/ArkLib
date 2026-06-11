/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24CutSupply

/-!
# [AGL24]/Frank: submodularity of the entering-border count (issue #354, Frank brick F2)

The uncrossing engine of the orientation theorem: for any head orientation, the count of
edges entering a vertex set (head inside, vertices not contained) is **submodular**. This is
what makes the family of deficient sets closed under union/intersection in the
reorientation argument (F3), exactly as in the digraph case — the hypergraph head-model
preserves it.

* `inBorder` — the entering-border count, matching `headBorderEdges.card` from
  `AGL24CutSupply`;
* `inBorder_submodular` — `in(T∪S) + in(T∩S) ≤ in(T) + in(S)` (per-edge case analysis:
  the only nontrivial case is a head in `T∩S` with the edge inside `T∪S` but not `T∩S`,
  where the right side picks up the crossing of whichever of `T, S` the edge escapes).
-/

open Finset

namespace AGL24

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]

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

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.inBorder_submodular
