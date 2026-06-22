/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic

/-!
# BSG DRC1 minimal fibre definitions

This module restores the small fibre definitions used by the `E1` and `E2c` dependent-random-choice
sublemmas. It is only bookkeeping: right degree, left neighbourhood, common-neighbour count, and the
cardinality identity for the left neighbourhood.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- Right-degree of `b`: the number of left vertices `a ∈ A` with `(a,b) ∈ G`. -/
noncomputable def rDeg (A : Finset α) (G : Finset (α × α)) (b : α) : ℕ :=
  #{a ∈ A | (a, b) ∈ G}

/-- Left-neighbourhood of `b` inside `A`. -/
noncomputable def leftNbhd (A : Finset α) (G : Finset (α × α)) (b : α) : Finset α :=
  {a ∈ A | (a, b) ∈ G}

/-- The left-neighbourhood cardinality is the right-degree. -/
theorem card_leftNbhd (A : Finset α) (G : Finset (α × α)) (b : α) :
    #(leftNbhd A G b) = rDeg A G b := by
  rfl

/-- Common neighbours of a pair `(a,a')` on the right side `A`. -/
noncomputable def commonNeighbors (A : Finset α) (G : Finset (α × α)) (a a' : α) : ℕ :=
  #{b ∈ A | (a, b) ∈ G ∧ (a', b) ∈ G}

#print axioms Finset.BSG.rDeg
#print axioms Finset.BSG.leftNbhd
#print axioms Finset.BSG.card_leftNbhd
#print axioms Finset.BSG.commonNeighbors

end Finset.BSG
