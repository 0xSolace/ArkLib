/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.Jo26GeneratorDichotomy

/-!
# The dichotomy's sharpness side: uniform obstruction genuinely fails (issue #334, A3)

`Jo26GeneratorDichotomy.lean` proves the removable-factor side: an `F`-indexed proper cover of
the per-seed obstructions removes the `A(q,s)` factor. This file proves the **obstruction-level
sharpness**: the covering hypothesis is not free — already at `s = 2` there are `q + 1`
pairwise-distinct directions (the projective line of `F²`), each spanning a 1-dimensional
obstruction, and **no `F`-indexed family of proper subspaces can absorb them all**:

* `not_mem_proper_of_pair` — *the pigeonhole core*: two non-proportional vectors cannot lie in
  a common proper subspace of `F²` (they span the plane);
* `projLine` / `projLine_card` — the `q + 1` canonical direction representatives, pairwise
  non-proportional;
* `exists_direction_escaping_cover` — **the sharpness theorem**: for every `F`-indexed family
  of proper subspaces of `F²`, some canonical direction lies in *no* member. Hence a seed
  family realizing all `q+1` directions as its Lemma-4.1 obstructions defeats every candidate
  `UniformObstruction` cover — the `A(q,s)` averaging route of [Jo26] Theorem 4.2 is then the
  only one available, and by `SubspaceAvoidance.card_linearForm_kernel_eq` its constant is
  exact at codimension-1 obstructions.

**Honest scope.** This is sharpness at the *subspace/cover* level — the precise statement that
the `UniformObstruction` hypothesis has genuine content. Producing a code/stack/generator whose
Lemma-4.1 obstructions realize all `q+1` directions (the *MCA-level* matching instance) is the
remaining open construction, recorded on the issue; nothing here claims it.
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The pigeonhole core**: two vectors of `F²` that are not proportional (neither is a scalar
multiple of the other, and the first is nonzero) cannot lie in a common **proper** subspace —
they are linearly independent, so any subspace containing both has rank 2 and is everything. -/
theorem not_mem_proper_of_pair {x y : Fin 2 → F} (hx : x ≠ 0)
    (hxy : ∀ a : F, y ≠ a • x)
    {K : Submodule F (Fin 2 → F)} (hK : K ≠ ⊤) (hxK : x ∈ K) (hyK : y ∈ K) : False := by
  classical
  have hindep : LinearIndependent F ![x, y] :=
    (LinearIndependent.pair_iff' hx).mpr (fun a h => hxy a h.symm)
  have hspan : Submodule.span F (Set.range ![x, y]) ≤ K := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    fin_cases i
    · exact hxK
    · exact hyK
  have hindep' : LinearIndependent F (fun i : Fin 2 =>
      (⟨![x, y] i, hspan (Submodule.subset_span ⟨i, rfl⟩)⟩ : K)) := by
    apply LinearIndependent.of_comp K.subtype
    convert hindep using 1
  have hle : Module.finrank F (Fin 2 → F) ≤ Module.finrank F K := by
    calc Module.finrank F (Fin 2 → F) = 2 := by simp
    _ = Fintype.card (Fin 2) := by simp
    _ ≤ Module.finrank F K := hindep'.fintype_card_le_finrank
  exact hK (Submodule.eq_top_of_finrank_eq
    (le_antisymm (Submodule.finrank_le K) hle))

/-- The `q + 1` canonical direction representatives of `F²` (the projective line): `(1, c)` for
`c : F`, and the vertical direction `(0, 1)` at `none`. -/
def projLine : Option F → Fin 2 → F
  | none => fun i => if i = 0 then 0 else 1
  | some c => fun i => if i = 0 then 1 else c

/-- Every canonical direction is nonzero. -/
theorem projLine_ne_zero (o : Option F) : projLine (F := F) o ≠ 0 := by
  cases o with
  | none =>
    intro h
    have := congrFun h 1
    simp [projLine] at this
  | some c =>
    intro h
    have := congrFun h 0
    simp [projLine] at this

/-- **Pairwise non-proportionality** of the canonical directions: for `o ≠ o'`, the direction
`projLine o'` is not a scalar multiple of `projLine o`. -/
theorem projLine_not_smul {o o' : Option F} (h : o ≠ o') (a : F) :
    projLine (F := F) o' ≠ a • projLine (F := F) o := by
  intro heq
  cases o with
  | none =>
    cases o' with
    | none => exact h rfl
    | some c' =>
      -- (1, c') = a • (0, 1): first coordinate gives 1 = 0.
      have h0 := congrFun heq 0
      simp [projLine] at h0
  | some c =>
    cases o' with
    | none =>
      -- (0, 1) = a • (1, c): first coordinate gives a = 0, then second gives 1 = 0.
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      simp [projLine] at h0 h1
      rw [← h0] at h1
      simp at h1
    | some c' =>
      -- (1, c') = a • (1, c): first coordinate gives a = 1, second gives c' = c.
      have h0 := congrFun heq 0
      have h1 := congrFun heq 1
      simp [projLine] at h0 h1
      rw [← h0] at h1
      simp at h1
      exact h (by rw [h1])

/-- **The sharpness theorem (subspace level)**: no `F`-indexed family of proper subspaces of
`F²` absorbs all `q + 1` canonical directions — some direction lies in no member. The
`UniformObstruction` covering hypothesis of the dichotomy therefore has genuine content: a
seed family realizing every direction of the projective line as its Lemma-4.1 obstruction
defeats every candidate cover. -/
theorem exists_direction_escaping_cover
    (K : F → Submodule F (Fin 2 → F)) (hK : ∀ γ, K γ ≠ ⊤) :
    ∃ o : Option F, ∀ γ : F, projLine (F := F) o ∉ K γ := by
  classical
  by_contra hcon
  push Not at hcon
  -- Choose, for each direction, a cover member containing it.
  choose g hg using hcon
  -- Pigeonhole: q+1 directions into q members forces a collision.
  have hcard : Fintype.card F < Fintype.card (Option F) := by
    simp
  obtain ⟨o, o', hne, hgo⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  -- Two distinct directions in one proper member: the pigeonhole core fires.
  exact not_mem_proper_of_pair (projLine_ne_zero o)
    (projLine_not_smul hne) (hK (g o)) (hg o) (hgo ▸ hg o')

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.not_mem_proper_of_pair
#print axioms ProximityGap.projLine_not_smul
#print axioms ProximityGap.exists_direction_escaping_cover
