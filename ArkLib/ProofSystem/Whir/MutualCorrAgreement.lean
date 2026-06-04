/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks, Petar Maksimović
-/

import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ProofSystem.Whir.ProximityGen


/-!
# Mutual Correlated Agreement for Proximity Generators

This file formalizes the notion of mutual correlated agreement for proximity generators,
introduced in Section 4 of [ACFY24].

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes

The reference paper is phrased in terms of a minimum distance,
which should be understood as being the minimum relative hamming distance, which is used here.

## Tags
Open question: should we aim to add tags?
-/

namespace MutualCorrAgreement

open NNReal Generator ProbabilityTheory ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
          {ι parℓ : Type} [Fintype ι] [Nonempty ι] [Fintype parℓ] [Nonempty parℓ]

/-- For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽`
    and linear code `C` the predicate `proximityCondition(r)` is true, if `∃ S ⊆ ι`, s.t.
    the following three conditions hold
      (i) `|S| ≥ (1-δ)*|ι|`
      (ii) `∃ u ∈ C, u(S) = ∑ j : parℓ, rⱼ * fⱼ(S)`
      (iii) `∃ i : parℓ, ∀ u' ∈ C, u'(S) ≠ fᵢ(S)` -/
def proximityCondition (f : parℓ → ι → F) (δ : ℝ≥0) (r : parℓ → F)
    (C : LinearCode ι F) : Prop :=
  ∃ S : Finset ι,
    (S.card : ℝ≥0) ≥ (1-δ) * Fintype.card ι ∧
    ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : parℓ, r j * f j s ∧
    ∃ i : parℓ, ∀ u' ∈ C, ∃ s ∈ S, u' s ≠ f i s

/-- Definition 4.9
  Let `C` be a linear code, then Gen is a proximity generator with mutual correlated agreement,
  if for `parℓ` functions `fᵢ : ι → F` and distance `δ < 1 - BStar(C,parℓ)`,
  `Pr_{ r ← F } [ proximityCondition(r) ] ≤ errStar(δ)`.

  Note that there is a typo in the paper:
  it should `δ < 1 - BStar(C,parℓ)` in place of `δ < 1 - B(C,parℓ)`
-/
noncomputable def hasMutualCorrAgreement
  (Gen : ProximityGenerator ι F) [Fintype Gen.parℓ]
  (BStar : ℝ) (errStar : ℝ → ENNReal) :=
    haveI := Gen.Gen_nonempty
    ∀ (f : Gen.parℓ → ι → F) (δ : ℝ≥0) (_hδ : 0 < δ ∧ δ < 1 - BStar),
    Pr_{let r ←$ᵖ Gen.Gen}[ proximityCondition f δ r Gen.C ] ≤ errStar δ

section

open ListDecodable

/-- For `parℓ` functions `{f₀,..,f_{parℓ - 1}}`,
  `IC` be the `parℓ`-interleaved code from a linear code C,
  with `Gen` as a proximity generator with mutual correlated agreement,
  `proximityListDecodingCondition(r)` is true if,
  `List(C, ∑ⱼ rⱼ * fⱼ, δ) ≠ `
  `{ ∑ⱼ rⱼ * uⱼ, where {u₀,..u_{parℓ-1}} ∈ Λᵢ({f₀,..,f_{parℓ-1}}, IC, δ) }` -/
def proximityListDecodingCondition (C : LinearCode ι F)
  [Fintype ι] [Nonempty ι]
  (r : parℓ → F) [Fintype parℓ]
  (δ : ℝ≥0) (fs : Matrix parℓ ι F) : Prop := -- fs is a WordStack
      let f_r := fun x => ∑ j, r j * fs j x
      let listHamming := closeCodewordsRel C f_r δ
      let listIC := { fun x => ∑ j, r j * (us.val j x) | us ∈ Λᵢ(fs, (C : Set (ι → F)), δ)}
      listHamming ≠ listIC


end

end MutualCorrAgreement
