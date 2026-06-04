/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks, Petar Maksimović
-/

import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.Errors
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
      (iii) `∃ i : parℓ, ∀ u' ∈ C, u'(S) ≠ fᵢ(S)`

  **Asymmetry with ABF26 `mcaEvent`.** Clause (iii) here is *per-row* — "some `fᵢ` is
  unmatched by any single codeword on `S`". The ABF26 `mcaEvent` (Def 4.3) instead asks
  *jointly* that "no pair `(v₀, v₁)` of codewords agrees with `(f 0, f 1)` on `S`". The
  per-row failure implies the joint failure (an unmatched row forces no joint pair) but
  not the converse: the rows could each match different codewords with no consistent
  pair. So `WHIR-event ⊆ ABF26-event` and `Pr[WHIR-event] ≤ Pr[ABF26-event]`. See
  `proximityCondition_imp_mcaEvent_affineLine` below for the predicate-level bridge. -/
def proximityCondition (f : parℓ → ι → F) (δ : ℝ≥0) (r : parℓ → F)
    (C : LinearCode ι F) : Prop :=
  ∃ S : Finset ι,
    (S.card : ℝ≥0) ≥ (1-δ) * Fintype.card ι ∧
    ∃ u ∈ C, ∀ s ∈ S, u s = ∑ j : parℓ, r j * f j s ∧
    ∃ i : parℓ, ∀ u' ∈ C, ∃ s ∈ S, u' s ≠ f i s

omit [Fintype F] [DecidableEq F] in
/-- **One-way bridge: WHIR `proximityCondition` ⟹ ABF26 `mcaEvent` (affine-line case).**

When `parℓ = Fin 2` and `r = (1, γ)` (the affine-line generator: `r 0 = 1`, `r 1 = γ`),
the WHIR event implies the ABF26 event. As a consequence
`Pr[WHIR-event] ≤ Pr[ABF26-event]`, so any bound `epsMCA C δ ≤ ε` (ABF26-side)
transfers to a bound on WHIR's `Pr[proximityCondition]` and hence to
`hasMutualCorrAgreement (affine-line generator) BStar (fun _ => ε)`.

The converse implication does **not** hold (per-row failure is strictly stronger than
joint failure), so this bridge is one-way only. See `proximityCondition` for the
predicate-mismatch discussion.

The `δ < 1` hypothesis avoids the degenerate case where `(1 - δ)·n ≤ 0` permits an
empty witness set `S` — `proximityCondition` becomes vacuously satisfiable (its `∃ i`
clause sits inside `∀ s ∈ S` so empty `S` makes the bridge fail). -/
lemma proximityCondition_imp_mcaEvent_affineLine
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1)
    (f : Fin 2 → ι → F) (γ : F)
    (h : proximityCondition (parℓ := Fin 2) f δ (fun j ↦ if j = 0 then 1 else γ)
      C) :
    ProximityGap.mcaEvent (F := F) (A := F) ((C : Set (ι → F))) δ (f 0) (f 1) γ := by
  obtain ⟨S, hS_card, u, hu_mem, h_inner⟩ := h
  -- `S` is nonempty: `S.card ≥ (1-δ)·n` with `δ < 1` and `n > 0`.
  have hn_pos : (0 : ℝ≥0) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h_pos : (0 : ℝ≥0) < (1 - δ) * Fintype.card ι :=
    mul_pos (tsub_pos_of_lt hδ) hn_pos
  have hS_nonempty : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with hempty | hne
    · subst hempty
      simp only [Finset.card_empty, Nat.cast_zero] at hS_card
      exact absurd hS_card (not_le.mpr h_pos)
    · exact hne
  obtain ⟨s₀, hs₀⟩ := hS_nonempty
  obtain ⟨_, i, h_unmatched⟩ := h_inner s₀ hs₀
  refine ⟨S, hS_card, ⟨u, hu_mem, ?_⟩, ?_⟩
  · -- Clause (ii): `u s = f 0 s + γ • f 1 s` from `u s = 1 * f 0 s + γ * f 1 s`.
    intro s hs
    obtain ⟨hu_eq, _⟩ := h_inner s hs
    simp [Fin.sum_univ_two, smul_eq_mul] at hu_eq ⊢
    exact hu_eq
  · -- Clause (iii): no joint pair, because row `i` is unmatched.
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    have := h_unmatched (if i = 0 then v₀ else v₁)
        (by split_ifs <;> assumption)
    obtain ⟨s, hs, hne⟩ := this
    have hag := hagree s hs
    split_ifs at hne with hi
    · -- i = 0
      rw [hi] at hne
      exact hne hag.1
    · -- i = 1 (the only other Fin 2)
      have hi1 : i = 1 := by omega
      rw [hi1] at hne
      exact hne hag.2

/-- **Probability-level corollary of the predicate bridge.** For any pair `(f 0, f 1)`,
the probability over `γ ←$ᵖ F` of WHIR's `proximityCondition` (with affine-line `r =
(1, γ)`) is bounded by ABF26's `epsMCA C δ`. Direct consequence of
`proximityCondition_imp_mcaEvent_affineLine` (predicate-level inclusion) plus the
`iSup`-definition of `epsMCA`.

Lets downstream WHIR proofs cite an ABF26-style `epsMCA C δ ≤ ε_target` bound to
discharge the WHIR `Pr_{r ←$ᵖ Gen.Gen}[proximityCondition ...] ≤ errStar δ` obligation
for the affine-line generator (where `Gen.Gen` is uniformly distributed over `F`). -/
lemma Pr_proximityCondition_le_epsMCA
    {C : LinearCode ι F} {δ : ℝ≥0} (hδ : δ < 1)
    (f : Fin 2 → ι → F) :
    Pr_{let γ ←$ᵖ F}[proximityCondition (parℓ := Fin 2) f δ
        (fun j ↦ if j = 0 then 1 else γ) C]
      ≤ ProximityGap.epsMCA (F := F) (A := F) ((C : Set (ι → F))) δ := by
  refine le_trans ?_ (le_iSup
    (fun u : Code.WordStack F (Fin 2) ι ↦
      Pr_{let γ ←$ᵖ F}[ProximityGap.mcaEvent (F := F) (A := F)
        ((C : Set (ι → F))) δ (u 0) (u 1) γ]) f)
  exact Pr_le_Pr_of_implies _ _ _
    (fun γ h ↦ proximityCondition_imp_mcaEvent_affineLine hδ f γ h)

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
