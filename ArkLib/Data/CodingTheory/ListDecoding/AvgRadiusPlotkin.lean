/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Average-radius Plotkin bound (the impossibility side of list decoding)

This is a genuinely-proved (sorry-free, axiom-clean) limitation theorem foundational to the
list-decoding / higher-order-MDS theory tracked by the #141 blueprint
(`docs/kb/audits/proximity-prize/higher-order-mds-formalization-blueprint.md`).

`avg_radius_plotkin`: for any finite set `T` of words whose pairwise Hamming distance is `≥ d`,
and any center `y`,
`(|T| - 1) · d ≤ 2 · ∑_{c ∈ T} Δ₀(c, y)`.

In words: minimum distance limits how many codewords can cluster (in average radius) around a
single word — the *impossibility* direction of list decoding (you cannot list-decode arbitrarily
many codewords inside a small ball). It is the elementary, code-structure-free cousin of the
generalized Singleton bound; the *achievability* of capacity (generic Reed–Solomon are higher-order
MDS) is the genuinely-open frontier and is **not** addressed here.

Proof: double-count `∑_{c,c'} Δ₀(c,c')`. The triangle inequality bounds it above by
`2|T| ∑_c Δ₀(c,y)`; the pairwise hypothesis bounds it below by `|T|(|T|-1)d`; cancel `|T|`.
-/

open Finset

variable {ι : Type*} [Fintype ι] {F : Type*} [DecidableEq F]

namespace CodingTheory

/-- **Average-radius Plotkin bound.** For a set `T` of words pairwise at Hamming distance `≥ d`,
and any center `y`, `(|T| - 1) · d ≤ 2 · ∑_{c ∈ T} Δ₀(c, y)`. Minimum distance limits how many
codewords can cluster (in average radius) near a single word — the impossibility side of list
decoding. -/
theorem avg_radius_plotkin (T : Finset (ι → F)) (y : ι → F) (d : ℕ)
    (hpair : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → d ≤ hammingDist c c') :
    (T.card - 1) * d ≤ 2 * ∑ c ∈ T, hammingDist c y := by
  classical
  -- Triangle inequality, summed twice:  ∑∑ Δ(c,c') ≤ ∑∑ (Δ(c,y)+Δ(y,c')).
  have htri : ∑ c ∈ T, ∑ c' ∈ T, hammingDist c c'
      ≤ ∑ c ∈ T, ∑ c' ∈ T, (hammingDist c y + hammingDist y c') := by
    refine Finset.sum_le_sum ?_
    intro c _
    refine Finset.sum_le_sum ?_
    intro c' _
    exact hammingDist_triangle c y c'
  -- The RHS double sum equals 2·|T|·∑_c Δ(c,y).
  have hrhs : ∑ c ∈ T, ∑ c' ∈ T, (hammingDist c y + hammingDist y c')
      = 2 * T.card * ∑ c ∈ T, hammingDist c y := by
    simp_rw [Finset.sum_add_distrib]
    have h1 : ∑ c ∈ T, ∑ _c' ∈ T, hammingDist c y = T.card * ∑ c ∈ T, hammingDist c y := by
      simp_rw [Finset.sum_const, smul_eq_mul]
      rw [Finset.mul_sum]
    have h2 : ∑ _c ∈ T, ∑ c' ∈ T, hammingDist y c' = T.card * ∑ c ∈ T, hammingDist c y := by
      rw [Finset.sum_const, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro c' _
      exact hammingDist_comm y c'
    rw [h1, h2]; ring
  -- The LHS double sum is at least |T|·((|T|-1)·d).
  have hstep : ∀ c ∈ T, (T.card - 1) * d ≤ ∑ c' ∈ T, hammingDist c c' := by
    intro c hc
    have hsub : ∑ _c' ∈ T.erase c, d ≤ ∑ c' ∈ T.erase c, hammingDist c c' := by
      refine Finset.sum_le_sum ?_
      intro c' hc'
      exact hpair c hc c' (Finset.mem_of_mem_erase hc') ((Finset.ne_of_mem_erase hc').symm)
    calc (T.card - 1) * d
        = (T.erase c).card * d := by rw [Finset.card_erase_of_mem hc]
      _ = ∑ _c' ∈ T.erase c, d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c' ∈ T.erase c, hammingDist c c' := hsub
      _ ≤ ∑ c' ∈ T, hammingDist c c' := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  have hlhs : T.card * ((T.card - 1) * d) ≤ ∑ c ∈ T, ∑ c' ∈ T, hammingDist c c' := by
    calc T.card * ((T.card - 1) * d)
        = ∑ _c ∈ T, (T.card - 1) * d := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c ∈ T, ∑ c' ∈ T, hammingDist c c' := Finset.sum_le_sum hstep
  -- Combine and cancel |T|.
  have hcomb : T.card * ((T.card - 1) * d) ≤ T.card * (2 * ∑ c ∈ T, hammingDist c y) := by
    calc T.card * ((T.card - 1) * d)
        ≤ ∑ c ∈ T, ∑ c' ∈ T, hammingDist c c' := hlhs
      _ ≤ 2 * T.card * ∑ c ∈ T, hammingDist c y := by rw [← hrhs]; exact htri
      _ = T.card * (2 * ∑ c ∈ T, hammingDist c y) := by ring
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · simp [Finset.card_eq_zero.mp h0]
  · exact Nat.le_of_mul_le_mul_left hcomb hpos

/-- **List-size bound from minimum distance.** If `T` is a set of words pairwise at Hamming
distance `≥ d`, all within Hamming distance `r` of a center `y`, then `|T|·d ≤ 2·|T|·r + d`.
In particular when `2r < d` (the unique/near-unique-decoding regime `r < d/2`) this forces `|T|`
to be small: a ball of radius `r` contains few pairwise-far codewords. A direct corollary of the
average-radius Plotkin bound — the list-decoding payoff. -/
theorem card_le_of_pairwise_dist_in_ball (T : Finset (ι → F)) (y : ι → F) (d r : ℕ)
    (hpair : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → d ≤ hammingDist c c')
    (hball : ∀ c ∈ T, hammingDist c y ≤ r) :
    T.card * d ≤ 2 * (T.card * r) + d := by
  have hP := avg_radius_plotkin T y d hpair
  have hballsum : ∑ c ∈ T, hammingDist c y ≤ T.card * r := by
    calc ∑ c ∈ T, hammingDist c y
        ≤ ∑ _c ∈ T, r := Finset.sum_le_sum (fun c hc => hball c hc)
      _ = T.card * r := by rw [Finset.sum_const, smul_eq_mul]
  have key : (T.card - 1) * d ≤ 2 * (T.card * r) := le_trans hP (by gcongr)
  have e1 : (T.card - 1) * d = T.card * d - d := by rw [Nat.sub_mul, one_mul]
  omega

end CodingTheory

#print axioms CodingTheory.avg_radius_plotkin
#print axioms CodingTheory.card_le_of_pairwise_dist_in_ball
