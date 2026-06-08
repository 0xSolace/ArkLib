/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming

/-!
# Sphere-packing (Hamming) bound

A self-contained (Mathlib-only) proof of the disjoint-balls counting bound underlying the classical
Hamming / sphere-packing bound: if the codewords of `C` are pairwise at Hamming distance `> 2t`,
the closed Hamming balls of radius `t` around them are pairwise disjoint, so the total number of
points they cover is at most the size of the whole space `|F|^|ι|`.

`sum_hammingBall_card_le`: `∑_{c ∈ C} |B(c,t)| ≤ |F|^|ι|`.

Combined with sphere uniformity (`|B(c,t)|` independent of `c`), this yields the usual
`|C| · V(t) ≤ q^n` Hamming bound. Here we prove the disjoint-cover inequality, which is the
combinatorial core; it is a packing/impossibility statement (an upper bound on code size from
minimum distance), the same family as the average-radius Plotkin bound.
-/

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Fintype F] [DecidableEq F]

namespace CodingTheory

/-- **Sphere-packing (Hamming) bound, disjoint-cover form.** If the codewords of `C` are pairwise
at Hamming distance `> 2t`, then the closed Hamming balls of radius `t` around them are disjoint,
so `∑_{c ∈ C} |B(c,t)| ≤ |F|^|ι|`. -/
theorem sum_hammingBall_card_le (C : Finset (ι → F)) (t : ℕ)
    (hpw : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * t < hammingDist c c') :
    ∑ c ∈ C, (univ.filter (fun x => hammingDist c x ≤ t)).card ≤ Fintype.card (ι → F) := by
  classical
  have hdisj : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      Disjoint (univ.filter (fun x => hammingDist c x ≤ t))
               (univ.filter (fun x => hammingDist c' x ≤ t)) := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    have hcc : 2 * t < hammingDist c c' := hpw c hc c' hc' hne
    have htri : hammingDist c c' ≤ hammingDist c x + hammingDist x c' := hammingDist_triangle c x c'
    have hsymm : hammingDist x c' = hammingDist c' x := hammingDist_comm x c'
    omega
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_univ _

end CodingTheory

#print axioms CodingTheory.sum_hammingBall_card_le
