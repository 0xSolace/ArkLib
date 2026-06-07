/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2GCXK25

/-!
# GKL24 first-moment bad-witness cardinality bound (#67)

The genuine first-moment content behind `GKL24FirstMomentResidual`: for a *fixed* candidate
codeword `w`, the set of "bad" combining scalars `γ` (those for which `w` witnesses the MCA event
on some large agreement set) is bounded in cardinality by the Hamming weight of `u₁`.

## The mathematics (coordinate-injectivity / first moment)

For each bad scalar `γ` there is a set `S_γ` with `|S_γ| ≥ (1-δ)n` on which `w = u₀ + γ • u₁`.
At any coordinate `i` with `u₁ i ≠ 0`, the equation `w i = u₀ i + γ • u₁ i` determines `γ` **uniquely**
(`γ • u₁ i = γ' • u₁ i ∧ u₁ i ≠ 0 ⟹ γ = γ'`, by `NoZeroSMulDivisors`).  Hence each weight-coordinate
of `u₁` lies in `S_γ` for **at most one** bad `γ`: the sets `{S_γ ∩ supp(u₁)}` are pairwise disjoint.

Counting: their disjoint union sits inside `supp(u₁)`, so
`∑_γ |S_γ ∩ supp(u₁)| ≤ |supp(u₁)|`.  Each term is `≥ |S_γ| - |supp(u₁)ᶜ| ≥ wt(u₁) - δ·n`.  Therefore

  **`|mcaBadWitness| · (wt(u₁) - δ·n) ≤ wt(u₁)`**     (`mcaBadWitness_card_mul_le`)

the first-moment bound: when `u₁` is far from `0` (`wt(u₁) > δ·n`) the bad-scalar count is small,
`|mcaBadWitness| ≤ wt(u₁) / (wt(u₁) - δ·n)`.

This is the reconstructed GKL24/GCXK25 first-moment count, the analogue of the radius-`1/n` J1 cap
(`GrandChallengeJ1Cap.not_three_j1_ratioConstraints`), here at a general agreement radius `δ`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open Finset
open scoped NNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Coordinate-injectivity of the combining scalar.**  At a coordinate where `u₁` is nonzero, the
line value `u₀ + γ • u₁` determines `γ` uniquely. -/
theorem scalar_unique_of_smul_eq [NoZeroSMulDivisors F A]
    {a : A} (ha : a ≠ 0) {γ γ' : F} (h : γ • a = γ' • a) : γ = γ' := by
  have hz : (γ - γ') • a = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 ha

/-- The support (weight coordinates) of `u₁`. -/
noncomputable def supp₁ (u₁ : ι → A) : Finset ι := Finset.univ.filter (fun i => u₁ i ≠ 0)

@[simp] theorem mem_supp₁ {u₁ : ι → A} {i : ι} : i ∈ supp₁ u₁ ↔ u₁ i ≠ 0 := by
  simp [supp₁]

open Classical in
/-- A witness agreement set for a bad combining scalar `γ`: chosen via `mcaBadWitness`'s defining
existential when `γ` is bad, and `∅` otherwise. -/
noncomputable def badWitnessSet (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ w : ι → A) (γ : F) :
    Finset ι :=
  if h : ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧ ¬ pairJointAgreesOn C S u₀ u₁
    then h.choose else ∅

open Classical in
/-- For a bad scalar, `badWitnessSet` is large and `w` agrees with the line on it. -/
theorem badWitnessSet_spec {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ w : ι → A} {γ : F}
    (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) :
    ((badWitnessSet C δ u₀ u₁ w γ).card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
      (∀ i ∈ badWitnessSet C δ u₀ u₁ w γ, w i = u₀ i + γ • u₁ i) := by
  rw [mcaBadWitness, mem_filter] at hγ
  have hex := hγ.2
  unfold badWitnessSet
  rw [dif_pos hex]
  exact ⟨hex.choose_spec.1, hex.choose_spec.2.1⟩

open Classical in
/-- **Pairwise disjointness on the support.**  Distinct bad scalars have witness sets that are
disjoint on `supp(u₁)`: a weight coordinate uniquely determines the combining scalar. -/
theorem badWitnessSet_inter_supp_disjoint [NoZeroSMulDivisors F A]
    {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ w : ι → A} {γ γ' : F}
    (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w)
    (hγ' : γ' ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) (hne : γ ≠ γ') :
    Disjoint (badWitnessSet C δ u₀ u₁ w γ ∩ supp₁ u₁)
      (badWitnessSet C δ u₀ u₁ w γ' ∩ supp₁ u₁) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  rw [Finset.mem_inter] at hi hi'
  have hu₁ : u₁ i ≠ 0 := mem_supp₁.mp hi.2
  have hw := (badWitnessSet_spec hγ).2 i hi.1
  have hw' := (badWitnessSet_spec hγ').2 i hi'.1
  -- u₀ i + γ • u₁ i = w i = u₀ i + γ' • u₁ i ⟹ γ • u₁ i = γ' • u₁ i ⟹ γ = γ'
  have hsmul : γ • u₁ i = γ' • u₁ i := by
    have : u₀ i + γ • u₁ i = u₀ i + γ' • u₁ i := by rw [← hw, ← hw']
    exact add_left_cancel this
  exact hne (scalar_unique_of_smul_eq hu₁ hsmul)

/-- Each bad witness set, intersected with `supp(u₁)`, has at least `wt(u₁) - δ·n` coordinates
(inclusion–exclusion against the `≥ (1-δ)n` size bound). -/
theorem card_badWitnessSet_inter_supp_ge {C : Set (ι → A)} {δ : ℝ≥0} (hδ : δ ≤ 1)
    {u₀ u₁ w : ι → A} {γ : F} (hγ : γ ∈ mcaBadWitness (F := F) C δ u₀ u₁ w) :
    ((supp₁ u₁).card : ℝ) - δ * Fintype.card ι ≤
      ((badWitnessSet C δ u₀ u₁ w γ ∩ supp₁ u₁).card : ℝ) := by
  set S := badWitnessSet C δ u₀ u₁ w γ
  set T := supp₁ u₁
  -- |S ∩ T| + |S ∪ T| = |S| + |T|, and |S ∪ T| ≤ n
  have hie : (S ∩ T).card + (S ∪ T).card = S.card + T.card :=
    Finset.card_inter_add_card_union S T
  have hunion : (S ∪ T).card ≤ Fintype.card ι := Finset.card_le_univ _
  -- |S| ≥ (1-δ)n in ℝ
  have hScardNN : ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := (badWitnessSet_spec hγ).1
  have hScardR : (1 - (δ : ℝ)) * Fintype.card ι ≤ (S.card : ℝ) := by
    have := (NNReal.coe_le_coe).mpr hScardNN
    push_cast [NNReal.coe_sub hδ] at this
    linarith [this]
  -- combine: |S ∩ T| = |S| + |T| - |S ∪ T| ≥ (1-δ)n + |T| - n = |T| - δn
  have hieR : ((S ∩ T).card : ℝ) + (S ∪ T).card = S.card + T.card := by exact_mod_cast hie
  have hunionR : ((S ∪ T).card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hunion
  nlinarith [hieR, hunionR, hScardR]

open Classical in
/-- **GKL24 first-moment bad-witness cardinality bound (#67).**

For a fixed candidate codeword `w`, the bad combining scalars are capped by the Hamming weight of
`u₁`:
`|mcaBadWitness| · (wt(u₁) - δ·n) ≤ wt(u₁)`.  When `u₁` is far from `0` (`wt(u₁) > δ·n`) this
forces `|mcaBadWitness| ≤ wt(u₁) / (wt(u₁) - δ·n)`.  Proven by the coordinate-injectivity / first
moment argument: the bad witness sets are pairwise disjoint on `supp(u₁)`, their disjoint union sits
in `supp(u₁)`, and each contributes `≥ wt(u₁) - δ·n` coordinates. -/
theorem mcaBadWitness_card_mul_le [NoZeroSMulDivisors F A]
    (C : Set (ι → A)) (δ : ℝ≥0) (hδ : δ ≤ 1) (u₀ u₁ w : ι → A) :
    ((mcaBadWitness (F := F) C δ u₀ u₁ w).card : ℝ) *
        ((supp₁ u₁).card - δ * Fintype.card ι) ≤ (supp₁ u₁).card := by
  set bad := mcaBadWitness (F := F) C δ u₀ u₁ w with hbad
  set T := supp₁ u₁ with hT
  -- disjoint union of the (witness ∩ supp) sets equals the sum of cards
  have hdisj : ∀ γ ∈ bad, ∀ γ' ∈ bad, γ ≠ γ' →
      Disjoint (badWitnessSet C δ u₀ u₁ w γ ∩ T) (badWitnessSet C δ u₀ u₁ w γ' ∩ T) :=
    fun γ hγ γ' hγ' hne => badWitnessSet_inter_supp_disjoint hγ hγ' hne
  have hsum_eq : (bad.biUnion (fun γ => badWitnessSet C δ u₀ u₁ w γ ∩ T)).card =
      ∑ γ ∈ bad, (badWitnessSet C δ u₀ u₁ w γ ∩ T).card :=
    Finset.card_biUnion hdisj
  -- the union sits inside T
  have hsub : bad.biUnion (fun γ => badWitnessSet C δ u₀ u₁ w γ ∩ T) ⊆ T := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨γ, _, hγi⟩ := hi
    exact (Finset.mem_inter.mp hγi).2
  -- hence ∑ |witness ∩ T| ≤ |T|
  have hsum_le : (∑ γ ∈ bad, (badWitnessSet C δ u₀ u₁ w γ ∩ T).card) ≤ T.card := by
    rw [← hsum_eq]; exact Finset.card_le_card hsub
  have hsum_leR : (∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ)) ≤ (T.card : ℝ) := by
    have : ((∑ γ ∈ bad, (badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℕ) : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast hsum_le
    push_cast at this; exact this
  -- each term ≥ |T| - δn
  have hterm : ∀ γ ∈ bad, ((T.card : ℝ) - δ * Fintype.card ι) ≤
      ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) :=
    fun γ hγ => card_badWitnessSet_inter_supp_ge hδ hγ
  -- sum the lower bounds: |bad|·(|T| - δn) ≤ ∑ ≤ |T|
  have hlb : (bad.card : ℝ) * ((T.card : ℝ) - δ * Fintype.card ι) ≤
      ∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) := by
    rw [← Finset.sum_const, Finset.sum_le_sum_iff_of_nonneg] <;>
      · first
        | exact hterm
        | (intro γ hγ; exact hterm γ hγ)
  calc (bad.card : ℝ) * ((T.card : ℝ) - δ * Fintype.card ι)
      ≤ ∑ γ ∈ bad, ((badWitnessSet C δ u₀ u₁ w γ ∩ T).card : ℝ) := hlb
    _ ≤ (T.card : ℝ) := hsum_leR

end ProximityGap

