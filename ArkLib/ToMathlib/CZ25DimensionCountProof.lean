/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import Mathlib.InformationTheory.Hamming

/-!
# CZ25 dimension-count: reusable agreement-coordinate bricks (issue #93)

Reusable sub-bricks toward the greedy-chain argument of `CodingTheory.CZ25DimensionCount`
(`ListDecoding/CZ25DesignToLambda.lean:152`), the per-received-word real bound
`|closeCodewordsRel C f δ| ≤ (1 - τ(r₀))/η` against an `IsSubspaceDesign` budget.

The genuine core is the Guruswami-Wang iterative charge, which `CZ25SpanDimension.lean`
documents as having no shortcut over the design budget (the naive single-base-point witnesses
are *provably false* there). This file lands the genuinely-reusable, axiom-clean ingredients
that the greedy chain (step 1 of the issue-#93 proof architecture) consumes:

* **agreement-coordinate lower bound** — for `c ∈ closeCodewordsRel C f δ`, the number of
  block coordinates `i : ι` where `c i = f i` is at least `(1 - δ)·n`. Equivalently, the
  disagreement count is at most `δ·n`. This is the "agreement ≥ (τ(r₀)+η)·n" datum that
  the greedy chain's step-1 charge consumes.

All results are stated for the block alphabet `Fin s → F` (so `α = Fin s → F`, not a field),
matching the subspace-design coordinate structure, and are `sorry`-free / axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami-Wang. *Linear-algebraic list decoding of folded Reed-Solomon codes.*
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section AgreementCount

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

/-- **Disagreement count as a `Finset.filter` cardinality.** The Hamming distance
`hammingDist f c = #{i | f i ≠ c i}` equals the cardinality of the filtered universe of
coordinates on which `f` and `c` disagree. This is the `Finset.filter`-form of the Mathlib
definition `hammingDist x y = #{i | x i ≠ y i}`, made explicit so downstream agreement
counts can split the universe into agreeing/disagreeing parts. -/
lemma hammingDist_eq_card_filter_ne (f c : ι → α) :
    hammingDist f c = (Finset.univ.filter (fun i => f i ≠ c i)).card := by
  classical
  rw [hammingDist]

/-- **Agreement count = `n − hammingDist`.** The number of block coordinates on which `f`
and `c` *agree* is `n − hammingDist f c`. Splits the universe of coordinates into the
agreeing and disagreeing parts. -/
lemma card_agree_eq (f c : ι → α) :
    (Finset.univ.filter (fun i => f i = c i)).card =
      Fintype.card ι - hammingDist f c := by
  classical
  rw [hammingDist_eq_card_filter_ne]
  have hsplit : (Finset.univ.filter (fun i => f i = c i)).card +
      (Finset.univ.filter (fun i => f i ≠ c i)).card = Fintype.card ι := by
    simpa [Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
        (p := fun i : ι => f i = c i)
  omega

/-- **Real-valued disagreement bound from a relative-distance radius.** If the *real* relative
Hamming distance is bounded by `δ`, i.e. `(δᵣ(f, c) : ℝ) ≤ δ`, then the disagreement count is
bounded by `δ·n`:

  `(#{i : f i ≠ c i} : ℝ) ≤ δ · n`.

This unfolds `relHammingDist = hammingDist / n` and clears the (positive) denominator `n`. -/
lemma card_disagree_le_of_relHammingDist_le
    (f c : ι → α) {δ : ℝ}
    (hδ : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    ((Finset.univ.filter (fun i => f i ≠ c i)).card : ℝ) ≤ δ * Fintype.card ι := by
  classical
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  -- `relHammingDist f c = hammingDist f c / n`, cast to ℝ.
  have hrel : ((Code.relHammingDist f c : ℚ≥0) : ℝ)
      = (hammingDist f c : ℝ) / Fintype.card ι := by
    rw [Code.relHammingDist]
    push_cast
    ring
  rw [hrel, div_le_iff₀ hn_pos] at hδ
  rw [hammingDist_eq_card_filter_ne] at hδ
  linarith

/-- **Agreement-coordinate lower bound (the greedy-chain step-1 datum).** For a codeword
`c ∈ closeCodewordsRel C f δ` (`c ∈ C` and `δᵣ(f, c) ≤ δ`), the number of block coordinates
on which `c` agrees with `f` is at least `(1 - δ)·n`:

  `(1 - δ) · n ≤ (#{i : f i = c i} : ℝ)`.

This is the per-element agreement bound that the CZ25 / Guruswami-Wang greedy chain consumes
in step 1 ("each candidate agrees with `f` on `≥ (τ(r₀)+η)·n` coordinates"): at the capacity
radius `δ = 1 - τ(r₀) - η`, the right-hand floor is `(τ(r₀)+η)·n`. Proven from the
relative-distance membership alone; no design / iterative-charge content. -/
lemma card_agree_ge_of_mem_closeCodewordsRel
    (C : Set (ι → α)) (f c : ι → α) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ) :
    (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => f i = c i)).card : ℝ) := by
  classical
  rw [mem_closeCodewordsRel_iff_real] at hc
  have hdis := card_disagree_le_of_relHammingDist_le f c hc.2
  have hle : hammingDist f c ≤ Fintype.card ι := hammingDist_le_card_fintype
  -- `#agree = n - hammingDist`, cast to ℝ.
  have hagree : ((Finset.univ.filter (fun i => f i = c i)).card : ℝ)
      = (Fintype.card ι : ℝ) - hammingDist f c := by
    rw [card_agree_eq]
    push_cast [Nat.cast_sub hle]
    ring
  rw [hagree]
  rw [hammingDist_eq_card_filter_ne] at hle ⊢
  -- From `#disagree ≤ δ·n`, get `n - #disagree ≥ n - δ·n = (1-δ)·n`.
  nlinarith [hdis]

end AgreementCount

/-! ### `#print axioms` verification anchors -/

section AxiomCheck

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {α : Type} [DecidableEq α]

example (f c : ι → α) :
    hammingDist f c = (Finset.univ.filter (fun i => f i ≠ c i)).card :=
  hammingDist_eq_card_filter_ne f c

example (C : Set (ι → α)) (f c : ι → α) {δ : ℝ}
    (hc : c ∈ closeCodewordsRel C f δ) :
    (1 - δ) * Fintype.card ι ≤
      ((Finset.univ.filter (fun i => f i = c i)).card : ℝ) :=
  card_agree_ge_of_mem_closeCodewordsRel C f c hc

end AxiomCheck

end CodingTheory

#print axioms CodingTheory.hammingDist_eq_card_filter_ne
#print axioms CodingTheory.card_agree_eq
#print axioms CodingTheory.card_disagree_le_of_relHammingDist_le
#print axioms CodingTheory.card_agree_ge_of_mem_closeCodewordsRel
