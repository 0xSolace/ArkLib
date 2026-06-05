/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.CodeGeometry

/-!
# ABF26 §3.1 — Johnson family `J_{q,ℓ}, J_q, J` and Theorem 3.2 / Corollary 3.3

Extensions to `JohnsonBound/Basic.lean` matching the paper-shaped statements from
ABF26 §3.1 (Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026).

The existing `JohnsonBound.J q δ : ℝ` matches the paper's `J_q(δ)`. This file adds:

- `JohnsonBound.Jqℓ q ℓ δ` — paper's `J_{q,ℓ}(δ)`, with the additional `ℓ/(ℓ-1)` factor
  inside the square root.
- `JohnsonBound.Jcap δ` — paper's asymptotic Johnson bound `J(δ) := 1 - √(1 - δ)`.

The three are related by `J_{q,ℓ}(δ) →_{ℓ → ∞} J_q(δ) →_{q → ∞} J(δ)`; we state the
limit relationships in docstrings but do not formalise the limits (the paper does
not prove them either).

The file also states the paper-shaped versions of:

- `johnson_bound_lambda_le_ell` — ABF26 Theorem 3.2 [Joh62]:
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`.
- `mds_johnson_lambda_le` — ABF26 Corollary 3.3:
  for any MDS code `C` of rate `ρ` and `η > 0`, `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.

Both are admitted as external results (T3.2 has an existing in-tree proof via
`johnson_bound` / `johnson_bound_alphabet_free` in `JohnsonBound/Basic.lean` that
needs porting from the absolute-distance form to ABF26's `Lambda` form; C3.3
follows from L2.6 + T3.2, but uses the asymptotic Johnson radius which crosses
ArkLib's existing rate/distance bridge).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Joh62] Johnson. (Original Johnson bound paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace JohnsonBound

open Real
open Finset

/-- **ABF26 Definition 3.1, `J_{q,ℓ}`.** Paper's q-ary ℓ-radius Johnson function:

  `J_{q,ℓ}(δ) := (1 - 1/q) · (1 - √(1 - q/(q-1) · ℓ/(ℓ-1) · δ))`

For `ℓ = 2` this is the binary Johnson radius; as `ℓ → ∞`, `Jqℓ q ℓ δ → J q δ`
(the existing `JohnsonBound.J`). The `ℓ` parameter is the target list size. -/
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ :=
  let frac : ℚ := q / (q - 1)
  let lFac : ℚ := ℓ / (ℓ - 1)
  ((1 - 1 / q) : ℚ) * (1 - √(1 - frac * lFac * δ))

/-- Reciprocal finite-list Johnson radius reached by the current quadratic-cap
route, stated over reals for direct use with `Code.minDist C / n`.

This is deliberately distinct from paper-facing `Jqℓ`: it uses
`(ℓ-1)/ℓ` rather than `ℓ/(ℓ-1)`. -/
noncomputable def JqℓRecipReal (q ℓ δ : ℝ) : ℝ :=
  (1 - 1 / q) *
    (1 - √(1 - (1 / (1 - 1 / q)) * ((ℓ - 1) / ℓ) * δ))

/-- **ABF26 Definition 3.1, `J`.** Paper's asymptotic Johnson bound:

  `J(δ) := 1 - √(1 - δ)`

Equals the `q → ∞` limit of `J_q(δ)` and the `q, ℓ → ∞` limit of `J_{q,ℓ}(δ)`.
This is also the binary Johnson bound (q = 2, ℓ → ∞).

Distinct from the existing `JohnsonBound.J q δ`, which is the paper's `J_q(δ)`
(the q-ary limit, parametrised by `q`). To avoid renaming the existing `J`, we
name this `Jcap` (Johnson — *cap*acity). -/
noncomputable def Jcap (δ : ℝ) : ℝ := 1 - √(1 - δ)

@[simp]
lemma Jcap_zero : Jcap 0 = 0 := by simp [Jcap]

@[simp]
lemma Jcap_one : Jcap 1 = 1 := by simp [Jcap]

/-- Indexed q-ary Plotkin average-distance upper bound, with the same ordered-pair
normalisation as `JohnsonBound.d`.

This packages the simplex-embedding PSD bound from `CodeGeometry` into the
Johnson-bound denominator shape:
`2 * choose_2 M = M * (M - 1)`.

The statement is intentionally indexed by `Fin M`; the separate translation to
`Finset` images is the mechanical bridge needed by `johnson_bound_lambda_le_ell`. -/
theorem indexed_averageDist_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {M : ℕ} (c : Fin M → ι → α) (hM : 1 < M) (hq : 0 < Fintype.card α) :
    (1 : ℝ) / (2 * ((choose_2 (M : ℚ)) : ℝ)) *
        (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤
      (M : ℝ) / ((M : ℝ) - 1) *
        (Fintype.card ι : ℝ) *
          (1 - 1 / (Fintype.card α : ℝ)) := by
  classical
  let C0 : ℝ :=
    (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))
  have htotal := CodeGeometry.sum_sum_hammingDist_le (ι := ι) (α := α) c hq
  have hoff_le_total :
      (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤
        (∑ i : Fin M, ∑ j : Fin M,
          (hammingDist (c i) (c j) : ℝ)) := by
    refine Finset.sum_le_sum fun i _ => ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro j hj
      exact Finset.mem_univ j
    · intro j _ _
      exact_mod_cast Nat.zero_le (hammingDist (c i) (c j))
  have hoff_bound :
      (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ)) ≤ (M : ℝ) * (M : ℝ) * C0 :=
    le_trans hoff_le_total htotal
  have hden :
      2 * (((choose_2 (M : ℚ)) : ℚ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
    norm_num [choose_2]
    ring
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hM
  have hMsub_pos : 0 < (M : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast hM)
  have hden_nonneg : 0 ≤ 1 / ((M : ℝ) * ((M : ℝ) - 1)) := by
    positivity
  rw [hden]
  calc
    (1 : ℝ) / ((M : ℝ) * ((M : ℝ) - 1)) *
        (∑ i : Fin M, ∑ j ∈ Finset.univ.erase i,
          (hammingDist (c i) (c j) : ℝ))
        ≤ (1 : ℝ) / ((M : ℝ) * ((M : ℝ) - 1)) *
            ((M : ℝ) * (M : ℝ) * C0) :=
          mul_le_mul_of_nonneg_left hoff_bound hden_nonneg
    _ = (M : ℝ) / ((M : ℝ) - 1) * C0 := by
          field_simp [hMpos.ne', hMsub_pos.ne']
    _ = (M : ℝ) / ((M : ℝ) - 1) *
        (Fintype.card ι : ℝ) *
          (1 - 1 / (Fintype.card α : ℝ)) := by
          simp [C0, mul_assoc]

/-- Rewrites the indexed off-diagonal ordered-pair sum as a product-filter sum. -/
private lemma offdiag_sum_eq_product {M : ℕ} (f : Fin M → Fin M → ℝ) :
    (∑ i : Fin M, ∑ j ∈ (Finset.univ : Finset (Fin M)).erase i, f i j) =
      ∑ p ∈ (Finset.univ : Finset (Fin M × Fin M)) with p.1 ≠ p.2, f p.1 p.2 := by
  rw [Finset.sum_filter]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (∑ y : Fin M, if (i, y).1 ≠ (i, y).2 then f (i, y).1 (i, y).2 else 0) =
      ∑ y : Fin M, if i ≠ y then f i y else 0 by rfl]
  rw [← Finset.sum_erase (s := (Finset.univ : Finset (Fin M))) (a := i)
      (f := fun y => if i ≠ y then f i y else 0) (by simp)]
  refine Finset.sum_congr rfl ?_
  intro y hy
  have hyne : i ≠ y := (Finset.mem_erase.mp hy).1.symm
  simp [hyne]

/-- Transports an indexed off-diagonal sum along `Finset.equivFin`. -/
private lemma offdiag_sum_equivFin
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α] (B : Finset (ι → α)) :
    (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
      (hammingDist ((Finset.equivFin B).symm i).1 ((Finset.equivFin B).symm j).1 : ℝ)) =
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
  rw [offdiag_sum_eq_product]
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let s : Finset (Fin B.card × Fin B.card) :=
    (Finset.univ : Finset (Fin B.card × Fin B.card)).filter (fun p => p.1 ≠ p.2)
  let t : Finset ((ι → α) × (ι → α)) := (B ×ˢ B).filter (fun x => x.1 ≠ x.2)
  change (∑ p ∈ s, (hammingDist (e p.1).1 (e p.2).1 : ℝ)) =
    ∑ x ∈ t, (hammingDist x.1 x.2 : ℝ)
  refine Finset.sum_bij (fun p _hp => ((e p.1).1, (e p.2).1)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [t, mem_filter, mem_product]
    have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    refine ⟨⟨(e p.1).2, (e p.2).2⟩, ?_⟩
    intro hval
    apply hpne
    exact e.injective (Subtype.ext hval)
  · intro p _hp q _hq h
    simp only [Prod.mk.injEq] at h
    cases p with
    | mk p₁ p₂ =>
      cases q with
      | mk q₁ q₂ =>
        simp only at h
        have h₁ : p₁ = q₁ := e.injective (Subtype.ext h.1)
        have h₂ : p₂ = q₂ := e.injective (Subtype.ext h.2)
        simp [h₁, h₂]
  · intro x hx
    simp only [t, mem_filter, mem_product] at hx
    let a : B := ⟨x.1, hx.1.1⟩
    let b : B := ⟨x.2, hx.1.2⟩
    refine ⟨(e.symm a, e.symm b), ?_, ?_⟩
    · simp only [s, mem_filter, mem_univ, true_and]
      intro hidx
      apply hx.2
      have hsub : a = b := e.symm.injective hidx
      exact congrArg Subtype.val hsub
    · simp [e, a, b]
  · intro p _hp
    rfl

/-- Ordered-pair average distance for a finite family over an arbitrary finite index type.

This is `JohnsonBound.d` without the historical `Fin n` restriction. -/
noncomputable def averageDistOn
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α] (B : Finset (ι → α)) : ℚ :=
  (1 : ℚ) / (2 * choose_2 B.card) *
    ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2)

/-- Average absolute distance from a fixed center to a finite family. -/
noncomputable def averageDistToOn
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    (B : Finset (ι → α)) (f : ι → α) : ℚ :=
  (1 : ℚ) / B.card * ∑ x ∈ B, Δ₀(f, x)

/-- If every word in a finite family has absolute distance at most `r` from `f`,
then its average absolute distance from `f` is at most `r`. -/
theorem averageDistToOn_real_le_of_forall_dist_le
    {ι : Type} [Fintype ι]
    {α : Type} [DecidableEq α]
    {B : Finset (ι → α)} {f : ι → α} {r : ℝ}
    (hB : 0 < B.card)
    (hdist : ∀ x ∈ B, (hammingDist f x : ℝ) ≤ r) :
    ((averageDistToOn B f : ℚ) : ℝ) ≤ r := by
  unfold averageDistToOn
  have hsum : (∑ x ∈ B, (hammingDist f x : ℝ)) ≤
      ∑ x ∈ B, r :=
    Finset.sum_le_sum hdist
  have hcard_pos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast hB
  calc
    ((1 : ℚ) / B.card * ∑ x ∈ B, Δ₀(f, x) : ℚ) =
        (1 : ℝ) / B.card * ∑ x ∈ B, (hammingDist f x : ℝ) := by
          simp [Nat.cast_sum]
    _ ≤ (1 : ℝ) / B.card * ∑ x ∈ B, r :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = r := by
          rw [sum_const, nsmul_eq_mul]
          field_simp [hcard_pos.ne']

/-- A relative-distance bound gives the corresponding absolute Hamming-distance
bound after multiplying by the block length. -/
lemma hammingDist_real_le_of_relHammingDist_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [DecidableEq α] {f c : ι → α} {δ : ℝ}
    (h : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    (hammingDist f c : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at h
  simp only [NNRat.cast_div, NNRat.cast_natCast] at h
  rw [div_le_iff₀ hn_pos] at h
  exact h

/-- A relative-distance bound also gives the corresponding integer absolute
Hamming-distance bound by flooring `δ · n`. -/
lemma hammingDist_le_floor_mul_card_of_relHammingDist_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [DecidableEq α] {f c : ι → α} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ((Code.relHammingDist f c : ℚ≥0) : ℝ) ≤ δ) :
    hammingDist f c ≤ ⌊δ * (Fintype.card ι : ℝ)⌋₊ := by
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at h
  simp only [NNRat.cast_div, NNRat.cast_natCast] at h
  rw [div_le_iff₀ hn_pos] at h
  exact (Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg _))).mpr h

/-- Elements of a finite point-list are within absolute radius `δ · n` of the
received word. -/
lemma hammingDist_real_le_of_mem_closeCodewordsRelFinset
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f c : ι → α} {δ : ℝ}
    (h : c ∈ ListDecodable.closeCodewordsRelFinset C f δ) :
    (hammingDist f c : ℝ) ≤ δ * (Fintype.card ι : ℝ) := by
  have hrel := (ListDecodable.mem_closeCodewordsRelFinset.mp h).2
  simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at hrel
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at hrel
  simp only [NNRat.cast_div, NNRat.cast_natCast] at hrel
  rw [div_le_iff₀ hn_pos] at hrel
  convert hrel using 1
  congr

/-- Elements of a finite point-list are within integer radius
`⌊δ · n⌋₊` of the received word. -/
lemma hammingDist_le_floor_mul_card_of_mem_closeCodewordsRelFinset
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f c : ι → α} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : c ∈ ListDecodable.closeCodewordsRelFinset C f δ) :
    hammingDist f c ≤ ⌊δ * (Fintype.card ι : ℝ)⌋₊ := by
  have hrel := (ListDecodable.mem_closeCodewordsRelFinset.mp h).2
  simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at hrel
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold Code.relHammingDist at hrel
  simp only [NNRat.cast_div, NNRat.cast_natCast] at hrel
  rw [div_le_iff₀ hn_pos] at hrel
  apply (Nat.le_floor_iff (mul_nonneg hδ (Nat.cast_nonneg _))).mpr
  convert hrel using 1
  congr

/-- A close-list word agrees with the received word on at least
`n - ⌊δ · n⌋₊` coordinates. -/
lemma card_sub_floor_mul_card_le_agree_of_mem_closeCodewordsRelFinset
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f c : ι → α} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (h : c ∈ ListDecodable.closeCodewordsRelFinset C f δ) :
    Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ ≤ CodeGeometry.agree c f := by
  have hdist := hammingDist_le_floor_mul_card_of_mem_closeCodewordsRelFinset hδ h
  have hsum := CodeGeometry.agree_add_hammingDist c f
  have hdist_symm : hammingDist c f = hammingDist f c := by
    unfold hammingDist
    simp_rw [ne_comm]
  rw [hdist_symm] at hsum
  omega

/-- The finite point-list average distance to its received word is bounded by
the relative radius times the block length. -/
theorem averageDistToOn_closeCodewordsRelFinset_le_radius_mul_card
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    (hB : 0 < (ListDecodable.closeCodewordsRelFinset C f δ).card) :
    ((averageDistToOn (ListDecodable.closeCodewordsRelFinset C f δ) f : ℚ) : ℝ) ≤
      δ * (Fintype.card ι : ℝ) := by
  apply averageDistToOn_real_le_of_forall_dist_le hB
  intro x hx
  exact hammingDist_real_le_of_mem_closeCodewordsRelFinset hx

/-- Any two distinct members of a code are separated by at least `Code.minDist`. -/
lemma minDist_le_hammingDist_of_mem_ne
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    {C : Set (ι → α)} {u v : ι → α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    Code.minDist C ≤ hammingDist u v := by
  unfold Code.minDist
  apply Nat.sInf_le
  exact ⟨u, hu, v, hv, hne, rfl⟩

/-- The ordered off-diagonal pair count matches the Johnson `choose_2`
normalisation. -/
private lemma two_mul_choose_two_card_eq_offdiag_card
    {β : Type} [DecidableEq β] (B : Finset β) :
    2 * choose_2 (B.card : ℚ) = (({ x ∈ B ×ˢ B | x.1 ≠ x.2 }.card : ℕ) : ℚ) := by
  simp only [ne_eq]
  unfold choose_2
  ring_nf
  have BBcard : (B ×ˢ B).card = B.card ^ 2 := by rw [card_product, sq]
  have BBdiagcard : { x ∈ B ×ˢ B | x.1 = x.2 }.card = B.card := by simp
  have BBdisjoint : { x ∈ B ×ˢ B | x.1 = x.2 } ∩
      { x ∈ B ×ˢ B | x.1 ≠ x.2 } = ∅ := by
    grind only [= mem_inter, ← notMem_empty, = mem_filter]
  have BBunion : B ×ˢ B =
      { x ∈ B ×ˢ B | x.1 = x.2 } ∪ { x ∈ B ×ˢ B | x.1 ≠ x.2 } := by
    grind only [= mem_union, = mem_filter]
  have BBcount : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card =
      (B ×ˢ B).card - { x ∈ B ×ˢ B | x.1 = x.2 }.card := by
    grind only [usr card_filter_le, usr card_union_add_card_inter, = Finset.card_empty]
  rw [BBcount, BBcard, BBdiagcard, Nat.cast_sub]
  · grind only
  · grind only [usr card_filter_le]

/-- A finite sublist of a code has average pairwise distance at least the code
minimum distance. -/
theorem minDist_le_averageDistOn_of_subset
    {ι : Type} [Fintype ι] {α : Type} [DecidableEq α]
    {C : Set (ι → α)} {B : Finset (ι → α)}
    (hB : 1 < B.card) (hsub : ∀ x ∈ B, x ∈ C) :
    (Code.minDist C : ℚ) ≤ averageDistOn B := by
  unfold averageDistOn
  let dmin : ℚ := Code.minDist C
  have h_d : ∀ x ∈ { x ∈ B ×ˢ B | x.1 ≠ x.2 }, dmin ≤ Δ₀(x.1, x.2) := by
    intro x hx
    simp only [ne_eq, mem_filter, mem_product] at hx
    dsimp [dmin]
    exact_mod_cast minDist_le_hammingDist_of_mem_ne
      (hsub x.1 hx.1.1) (hsub x.2 hx.1.2) hx.2
  have B2_card :
      2 * choose_2 (B.card : ℚ) =
        (({ x ∈ B ×ˢ B | x.1 ≠ x.2 }.card : ℕ) : ℚ) :=
    two_mul_choose_two_card_eq_offdiag_card B
  have B2_card_pos : 0 < { x ∈ B ×ˢ B | x.1 ≠ x.2 }.card := by
    have ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hB
    have : { x ∈ B ×ˢ B | x.1 ≠ x.2 }.Nonempty := by
      use ⟨u, v⟩
      simp [hu, hv, huv]
    exact card_pos.mpr this
  have h_bound : ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, dmin ≤
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2) :=
    by simpa [Nat.cast_sum] using sum_le_sum h_d
  have h_eq : dmin =
      1 / (2 * choose_2 (B.card : ℚ)) *
        ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, dmin := by
    rw [sum_const, B2_card]
    simp only [ne_eq, one_div]
    set c := ({ x ∈ B ×ˢ B | ¬x.1 = x.2 }.card : ℚ) with hc
    have c_pos : 0 < c := by
      unfold c
      exact_mod_cast B2_card_pos
    rw [nsmul_eq_mul]
    change dmin = c⁻¹ * (c * dmin)
    field_simp [ne_of_gt c_pos]
  change dmin ≤ 1 / (2 * choose_2 (B.card : ℚ)) *
    ↑(∑ x ∈ B ×ˢ B with x.1 ≠ x.2, Δ₀(x.1, x.2))
  rw [h_eq]
  have c2_nonneg : 0 ≤ (1 / (2 * choose_2 (B.card : ℚ)) : ℚ) := by
    have c2_pos : 0 < (2 * choose_2 (B.card : ℚ) : ℚ) := by
      rw [B2_card]
      exact_mod_cast B2_card_pos
    positivity
  exact mul_le_mul_of_nonneg_left h_bound c2_nonneg

/-- Arbitrary-index q-ary Plotkin average-distance upper bound. -/
theorem averageDistOn_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset (ι → α)) (hB : 2 ≤ B.card) (hq : 0 < Fintype.card α) :
    ((averageDistOn B : ℚ) : ℝ) ≤
      (B.card : ℝ) / ((B.card : ℝ) - 1) * (Fintype.card ι : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ)) := by
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let c : Fin B.card → ι → α := fun i => (e i).1
  have hM : 1 < B.card := by omega
  have hplot := indexed_averageDist_le_plotkin (ι := ι) (α := α)
    (M := B.card) c hM hq
  have hsum :
      (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
        (hammingDist (c i) (c j) : ℝ)) =
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
    simpa [c, e] using offdiag_sum_equivFin B
  rw [hsum] at hplot
  unfold averageDistOn
  simpa [Nat.cast_sum] using hplot

/-- Finset form of the q-ary Plotkin average-distance upper bound for
`JohnsonBound.d`.

This is the theorem needed to connect the simplex PSD development in
`CodeGeometry` to the existing Johnson-bound average-distance notation. -/
theorem averageDist_le_plotkin
    {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (B : Finset (Fin n → α)) (hB : 2 ≤ B.card) (hq : 0 < Fintype.card α) :
    ((d B : ℚ) : ℝ) ≤
      (B.card : ℝ) / ((B.card : ℝ) - 1) * (n : ℝ) *
        (1 - 1 / (Fintype.card α : ℝ)) := by
  let e : Fin B.card ≃ B := (Finset.equivFin B).symm
  let c : Fin B.card → Fin n → α := fun i => (e i).1
  have hM : 1 < B.card := by omega
  have hplot := indexed_averageDist_le_plotkin (ι := Fin n) (α := α)
    (M := B.card) c hM hq
  have hsum :
      (∑ i : Fin B.card, ∑ j ∈ (Finset.univ : Finset (Fin B.card)).erase i,
        (hammingDist (c i) (c j) : ℝ)) =
      ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (hammingDist x.1 x.2 : ℝ) := by
    simpa [c, e] using offdiag_sum_equivFin B
  rw [hsum] at hplot
  unfold d
  simpa [Nat.cast_sum] using hplot

/-- A finite point-list `Λ(C,δ,f)` has average pairwise distance at least the
minimum distance of `C`, provided it contains at least two words. -/
theorem minDist_le_averageDistOn_closeCodewordsRelFinset
    {ι : Type} [Fintype ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    (hB : 1 < (ListDecodable.closeCodewordsRelFinset C f δ).card) :
    (Code.minDist C : ℚ) ≤
      averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) := by
  apply minDist_le_averageDistOn_of_subset hB
  intro x hx
  exact (ListDecodable.mem_closeCodewordsRelFinset.mp hx).1

/-- Distinct codewords agree in at most `n - minDist(C)` coordinates. -/
lemma agree_le_card_sub_minDist_of_mem_ne
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : Set (ι → α)} {u v : ι → α}
    (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    CodeGeometry.agree u v ≤ Fintype.card ι - Code.minDist C := by
  have hsum := CodeGeometry.agree_add_hammingDist u v
  have hmin := minDist_le_hammingDist_of_mem_ne hu hv hne
  omega

/-- Pairwise agreement upper bound for finite point-lists, derived from the
ambient code minimum distance. -/
lemma closeCodewordsRelFinset_pairwise_agree_le_card_sub_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    {C : ListDecodable.Code ι α} {f : ι → α} {δ : ℝ}
    {u v : ι → α}
    (hu : u ∈ ListDecodable.closeCodewordsRelFinset C f δ)
    (hv : v ∈ ListDecodable.closeCodewordsRelFinset C f δ)
    (hne : u ≠ v) :
    CodeGeometry.agree u v ≤ Fintype.card ι - Code.minDist C := by
  exact agree_le_card_sub_minDist_of_mem_ne
    (ListDecodable.mem_closeCodewordsRelFinset.mp hu).1
    (ListDecodable.mem_closeCodewordsRelFinset.mp hv).1 hne

/-- The minimum distance of a code is at most the block length. -/
lemma minDist_le_card
    {ι : Type} [Fintype ι]
    {α : Type} [DecidableEq α]
    (C : ListDecodable.Code ι α) :
    Code.minDist C ≤ Fintype.card ι := by
  rw [← Code.dist_eq_minDist]
  exact Code.dist_le_card C

/-- Close-list wrapper for the radical-free `CodeGeometry` Johnson cap.

This converts the finite point-list into an indexed family via `Finset.equivFin`.
The remaining hypotheses are exactly the agreement lower bound to the received
word, the pairwise agreement upper bound from the code distance, and the
radical-free Johnson algebra side condition. -/
theorem closeCodewordsRelFinset_card_le_of_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    {A B ℓ : ℕ} {β : ℝ}
    (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hA : ∀ x ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      A ≤ CodeGeometry.agree x f)
    (hB : ∀ u ∈ ListDecodable.closeCodewordsRelFinset C f δ,
      ∀ v ∈ ListDecodable.closeCodewordsRelFinset C f δ,
        u ≠ v → CodeGeometry.agree u v ≤ B)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * (((B : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * ((A : ℝ) - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    (ListDecodable.closeCodewordsRelFinset C f δ).card ≤ ℓ := by
  classical
  let S := ListDecodable.closeCodewordsRelFinset C f δ
  by_cases hS : S.card = 0
  · simp [S, hS]
  · have hSpos : 0 < S.card := Nat.pos_of_ne_zero hS
    let e : Fin S.card ≃ S := (Finset.equivFin S).symm
    let c : Fin S.card → ι → α := fun i => (e i).1
    have hAidx : ∀ i, A ≤ CodeGeometry.agree (c i) f := by
      intro i
      exact hA (c i) (e i).2
    have hBidx : ∀ i j, i ≠ j → CodeGeometry.agree (c i) (c j) ≤ B := by
      intro i j hij
      apply hB (c i) (e i).2 (c j) (e j).2
      intro hval
      apply hij
      exact e.injective (Subtype.ext hval)
    exact CodeGeometry.card_le_of_johnson_condition hq hSpos f c ℓ hAidx hBidx hβ hcond

/-- Close-list Johnson cap with the canonical agreement parameters:

* `A = n - ⌊δ·n⌋₊`, forced by membership in the radius-`δ` close-list;
* `B = n - minDist(C)`, forced by pairwise separation inside the code.

This leaves only the nonnegativity/field-size assumptions, the shift parameter,
and the radical-free Johnson algebra condition. -/
theorem closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) (f : ι → α) (δ : ℝ)
    {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    (ListDecodable.closeCodewordsRelFinset C f δ).card ≤ ℓ := by
  apply closeCodewordsRelFinset_card_le_of_johnson_condition
      (C := C) (f := f) (δ := δ)
      (A := Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊)
      (B := Fintype.card ι - Code.minDist C)
      (ℓ := ℓ) (β := β) hq hβ
  · intro x hx
    exact card_sub_floor_mul_card_le_agree_of_mem_closeCodewordsRelFinset hδ hx
  · intro u hu v hv hne
    exact closeCodewordsRelFinset_pairwise_agree_le_card_sub_minDist hu hv hne
  · exact hcond

/-- Lambda-level Johnson cap with the canonical close-list agreement parameters.

This is the pointwise close-list cap packaged through the maximised
`ListDecodable.Lambda`; the remaining obligation is the same radical-free
Johnson algebra condition, independent of the received word. -/
theorem Lambda_le_of_floor_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply ListDecodable.Lambda_le_natCast_of_forall_closeFinset_card_le
  intro f
  exact closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition
    C f δ hδ hq hβ hcond

/-- Lambda-level Johnson cap with the close-list radius side condition written
using the real radius `n - δ*n` instead of the floored integer radius.

The floored agreement lower bound is at least this real quantity, and the
radical-free Johnson expression is monotone decreasing in that agreement
parameter when `β ≥ 0`. -/
theorem Lambda_le_of_real_radius_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_floor_minDist_johnson_condition C hδ hq hβ
  have hx_nonneg : 0 ≤ δ * (Fintype.card ι : ℝ) := by positivity
  have hfloor_le :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) ≤ δ * (Fintype.card ι : ℝ) :=
    Nat.floor_le hx_nonneg
  have hA_le :
      (Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ) ≤
        (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)) := by
    by_cases hf : ⌊δ * (Fintype.card ι : ℝ)⌋₊ ≤ Fintype.card ι
    · rw [Nat.cast_sub hf]
      linarith
    · have hlt : Fintype.card ι < ⌊δ * (Fintype.card ι : ℝ)⌋₊ :=
        Nat.lt_of_not_ge hf
      have hxgt : (Fintype.card ι : ℝ) < δ * (Fintype.card ι : ℝ) :=
        lt_of_lt_of_le (by exact_mod_cast hlt) hfloor_le
      have hsub : Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ = 0 := by omega
      rw [hsub]
      linarith
  have hℓ_nonneg : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  have hcenter_le :
      -2 * β * ((((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        ≤ -2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)) := by
    nlinarith [hA_le, hβ]
  have hcenter_scaled_le :
      (ℓ : ℝ) * (-2 * β *
          ((((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ))
            - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
        ≤ (ℓ : ℝ) * (-2 * β *
          (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
            - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))) :=
    mul_le_mul_of_nonneg_left hcenter_le hℓ_nonneg
  apply lt_of_le_of_lt ?_ hcond
  nlinarith [hcenter_le, hcenter_scaled_le]

/-- Lambda-level Johnson cap with both canonical agreement parameters written
as real-valued expressions: `n - δ*n` for the center agreement and
`n - minDist(C)` for pairwise agreement.

This is the algebra-facing form for the final `Jqℓ` radius calculation. -/
theorem Lambda_le_of_real_radius_real_minDist_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι : ℝ) - (Code.minDist C : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        - 2 * β * (((Fintype.card ι : ℝ) - δ * (Fintype.card ι : ℝ))
          - (Fintype.card ι : ℝ) / (Fintype.card α : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_real_radius_minDist_johnson_condition C hδ hq hβ
  have hmin_le : Code.minDist C ≤ Fintype.card ι := minDist_le_card C
  have hB :
      (((Fintype.card ι - Code.minDist C : ℕ) : ℝ)) =
        (Fintype.card ι : ℝ) - (Code.minDist C : ℝ) := by
    rw [Nat.cast_sub hmin_le]
  simpa [hB] using hcond

/-- Lambda-level Johnson cap with the algebraic side condition divided by the
block length. This relative-distance form is the natural target for the
`Jqℓ` radius algebra: the minimum distance appears as `minDist(C)/n`, and the
close-list radius appears as `δ` rather than `δ*n`. -/
theorem Lambda_le_of_normalized_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond : ((1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
        - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ)))
      + (ℓ : ℝ) * (((1 - (Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
          - 1 / (Fintype.card α : ℝ))
        - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ))
        + β ^ 2 * (1 - 1 / (Fintype.card α : ℝ))) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_real_radius_real_minDist_johnson_condition C hδ hq hβ
  have hn_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hscaled :
      (Fintype.card ι : ℝ) *
        (((1 - 1 / (Fintype.card α : ℝ)) * (1 + β ^ 2)
          - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ)))
        + (ℓ : ℝ) * (((1 - (Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
            - 1 / (Fintype.card α : ℝ))
          - 2 * β * ((1 - δ) - 1 / (Fintype.card α : ℝ))
          + β ^ 2 * (1 - 1 / (Fintype.card α : ℝ)))) < 0 :=
    mul_neg_of_pos_of_neg hn_pos hcond
  convert hscaled using 1
  field_simp [hn_pos.ne']

/-- Compact relative-distance version of `Lambda_le_of_normalized_johnson_condition`.

Writing `γ = 1 - 1/q` and `drel = minDist(C)/n`, the Johnson side condition is
the scalar quadratic
`γ(1+β²) - 2β(γ-δ) + ℓ((γ-drel) - 2β(γ-δ) + β²γ) < 0`. -/
theorem Lambda_le_of_gamma_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card α) (hβ : 0 ≤ β)
    (hcond :
      let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
      let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
      γ * (1 + β ^ 2) - 2 * β * (γ - δ)
        + (ℓ : ℝ) * ((γ - drel) - 2 * β * (γ - δ) + β ^ 2 * γ) < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_normalized_johnson_condition C hδ hq hβ
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcond

/-- Gamma-form Johnson cap specialized to the quadratic minimizer
`β = (γ - δ)/γ`.

This is the Lean-facing algebra target for the final `Jqℓ` instantiation: after
showing the radius lies below `γ` and the displayed scalar expression is
negative, the Lambda bound follows. -/
theorem Lambda_le_of_gamma_optimal_johnson_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ : 0 ≤ δ) (hq_one : 1 < Fintype.card α)
    (hδ_le_gamma : δ ≤ 1 - 1 / (Fintype.card α : ℝ))
    (hcond :
      let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
      let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
      γ + (ℓ : ℝ) * (γ - drel) - ((ℓ : ℝ) + 1) * (γ - δ) ^ 2 / γ < 0) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
  let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
  have hq : 0 < Fintype.card α := lt_trans Nat.zero_lt_one hq_one
  have hq_real : 1 < (Fintype.card α : ℝ) := by exact_mod_cast hq_one
  have hq_real_pos : 0 < (Fintype.card α : ℝ) := lt_trans zero_lt_one hq_real
  have hγ_pos : 0 < γ := by
    have hfrac_pos :
        0 < ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) :=
      div_pos (sub_pos.mpr hq_real) hq_real_pos
    have hγ_eq :
        γ = ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) := by
      dsimp [γ]
      field_simp [hq_real_pos.ne']
    rw [hγ_eq]
    exact hfrac_pos
  have hβ_nonneg : 0 ≤ (γ - δ) / γ := by
    exact div_nonneg (sub_nonneg.mpr (by simpa [γ] using hδ_le_gamma)) hγ_pos.le
  apply Lambda_le_of_gamma_johnson_condition C hδ hq hβ_nonneg
  change γ * (1 + ((γ - δ) / γ) ^ 2) - 2 * ((γ - δ) / γ) * (γ - δ)
      + (ℓ : ℝ) * ((γ - drel) - 2 * ((γ - δ) / γ) * (γ - δ)
        + ((γ - δ) / γ) ^ 2 * γ) < 0
  have hquad :
      γ * (1 + ((γ - δ) / γ) ^ 2) - 2 * ((γ - δ) / γ) * (γ - δ)
          + (ℓ : ℝ) * ((γ - drel) - 2 * ((γ - δ) / γ) * (γ - δ)
            + ((γ - δ) / γ) ^ 2 * γ)
        = γ + (ℓ : ℝ) * (γ - drel) - ((ℓ : ℝ) + 1) * (γ - δ) ^ 2 / γ := by
    field_simp [hγ_pos.ne']
    ring
  rw [hquad]
  simpa [γ, drel] using hcond

/-- Gamma-form optimal-beta Johnson cap with the remaining condition stated as
a square lower bound.

This is the most compact handoff to radius algebra: prove that the squared
gap from the alphabet cap dominates the affine distance term, and the Lambda
bound follows. -/
theorem Lambda_le_of_gamma_square_condition
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ : 0 ≤ δ) (hq_one : 1 < Fintype.card α)
    (hδ_le_gamma : δ ≤ 1 - 1 / (Fintype.card α : ℝ))
    (hsquare :
      let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
      let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
      γ + (ℓ : ℝ) * (γ - drel) <
        ((ℓ : ℝ) + 1) * (γ - δ) ^ 2 / γ) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  apply Lambda_le_of_gamma_optimal_johnson_condition C hδ hq_one hδ_le_gamma
  simpa using sub_neg.mpr hsquare

/-- Johnson Lambda cap at the reciprocal finite-list radius reached by the
current quadratic-cap route.

This uses the factor `(ℓ-1)/ℓ`, not the paper-facing `Jqℓ` factor
`ℓ/(ℓ-1)`. The strict inequality requires positive minimum distance; when
`minDist(C) = 0`, the square condition degenerates to equality. -/
theorem Lambda_le_of_reciprocal_johnson_radius
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hrad :
      0 ≤ 1
        - (1 / (1 - 1 / (Fintype.card α : ℝ)))
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
          * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) :
    ListDecodable.Lambda C
      ((1 - 1 / (Fintype.card α : ℝ)) *
        (1 - Real.sqrt
          (1
            - (1 / (1 - 1 / (Fintype.card α : ℝ)))
              * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
              * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))))) ≤
        (ℓ : ℕ∞) := by
  let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
  let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
  let L : ℝ := ((ℓ : ℝ) - 1) / (ℓ : ℝ)
  let z : ℝ := 1 - (1 / γ) * L * drel
  have hq_real : 1 < (Fintype.card α : ℝ) := by exact_mod_cast hq_one
  have hq_real_pos : 0 < (Fintype.card α : ℝ) := lt_trans zero_lt_one hq_real
  have hγ_pos : 0 < γ := by
    have hfrac_pos :
        0 < ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) :=
      div_pos (sub_pos.mpr hq_real) hq_real_pos
    have hγ_eq :
        γ = ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) := by
      dsimp [γ]
      field_simp [hq_real_pos.ne']
    rw [hγ_eq]
    exact hfrac_pos
  have hℓ_real_pos : 0 < (ℓ : ℝ) := by
    have : (0 : ℕ) < ℓ := lt_of_lt_of_le (by norm_num) hℓ
    exact_mod_cast this
  have hL_nonneg : 0 ≤ L := by
    have hℓ_real_ge_one : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (le_trans (by norm_num) hℓ)
    dsimp [L]
    exact div_nonneg (sub_nonneg.mpr hℓ_real_ge_one) hℓ_real_pos.le
  have hdrel_pos : 0 < drel := by
    have hn_real_pos : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    dsimp [drel]
    exact div_pos (by exact_mod_cast hmin_pos) hn_real_pos
  have hz : 0 ≤ z := by
    simpa [γ, drel, L, z] using hrad
  have hz_le_one : z ≤ 1 := by
    have hterm_nonneg : 0 ≤ (1 / γ) * L * drel := by positivity
    dsimp [z]
    linarith
  have hsqrt_le_one : Real.sqrt z ≤ 1 := by
    calc
      Real.sqrt z ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hz_le_one
      _ = 1 := by norm_num
  have hδ_nonneg : 0 ≤ γ * (1 - Real.sqrt z) :=
    mul_nonneg hγ_pos.le (sub_nonneg.mpr hsqrt_le_one)
  have hδ_le_gamma : γ * (1 - Real.sqrt z) ≤ γ := by
    nlinarith [hγ_pos, Real.sqrt_nonneg z]
  apply Lambda_le_of_gamma_square_condition C hδ_nonneg hq_one
      (by simpa [γ, z] using hδ_le_gamma)
  dsimp [γ, drel, L, z]
  have hsq : (Real.sqrt (1 - (1 / γ) * L * drel)) ^ 2 =
      1 - (1 / γ) * L * drel := by
    exact Real.sq_sqrt hz
  have htarget :
      γ + (ℓ : ℝ) * (γ - drel) <
        ((ℓ : ℝ) + 1) *
          (γ - γ * (1 - Real.sqrt (1 - (1 / γ) * L * drel))) ^ 2 / γ := by
    have hdrel_div_pos : 0 < drel / (ℓ : ℝ) := div_pos hdrel_pos hℓ_real_pos
    have hgap :
        γ - γ * (1 - Real.sqrt (1 - (1 / γ) * L * drel)) =
          γ * Real.sqrt (1 - (1 / γ) * L * drel) := by
      ring
    rw [hgap]
    rw [show (γ * Real.sqrt (1 - (1 / γ) * L * drel)) ^ 2 =
        γ ^ 2 * (Real.sqrt (1 - (1 / γ) * L * drel)) ^ 2 by ring]
    rw [hsq]
    have hrhs_eq :
        ((ℓ : ℝ) + 1) * (γ ^ 2 * (1 - (1 / γ) * L * drel)) / γ =
          ((ℓ : ℝ) + 1) * (γ - drel * L) := by
      field_simp [hγ_pos.ne']
    rw [hrhs_eq]
    dsimp [L]
    field_simp [hℓ_real_pos.ne']
    nlinarith [hdrel_pos, hℓ_real_pos]
  simpa [γ, drel, L, z] using htarget

/-- Named-radius wrapper for `Lambda_le_of_reciprocal_johnson_radius`. -/
theorem Lambda_le_of_JqℓRecipReal_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hrad :
      0 ≤ 1
        - (1 / (1 - 1 / (Fintype.card α : ℝ)))
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
          * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) :
    ListDecodable.Lambda C
      (JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
        ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) ≤
        (ℓ : ℕ∞) := by
  simpa [JqℓRecipReal] using
    Lambda_le_of_reciprocal_johnson_radius C hℓ hq_one hmin_pos hrad

/-- Monotone-radius corollary of the named reciprocal Johnson radius bound. -/
theorem Lambda_le_of_le_JqℓRecipReal_minDist
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ_le : δ ≤ JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
      ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ)))
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hrad :
      0 ≤ 1
        - (1 / (1 - 1 / (Fintype.card α : ℝ)))
          * (((ℓ : ℝ) - 1) / (ℓ : ℝ))
          * ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  exact le_trans (ListDecodable.Lambda_mono (C := C) hδ_le)
    (Lambda_le_of_JqℓRecipReal_minDist C hℓ hq_one hmin_pos hrad)

/-- Named reciprocal Johnson bound with the radicand hypothesis expressed as
the scaled-distance condition `((ℓ-1)/ℓ) * drel ≤ γ`. -/
theorem Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hscaled :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) *
          ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
        ≤ 1 - 1 / (Fintype.card α : ℝ)) :
    ListDecodable.Lambda C
      (JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
        ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))) ≤
        (ℓ : ℕ∞) := by
  apply Lambda_le_of_JqℓRecipReal_minDist C hℓ hq_one hmin_pos
  let γ : ℝ := 1 - 1 / (Fintype.card α : ℝ)
  let drel : ℝ := (Code.minDist C : ℝ) / (Fintype.card ι : ℝ)
  have hq_real : 1 < (Fintype.card α : ℝ) := by exact_mod_cast hq_one
  have hq_real_pos : 0 < (Fintype.card α : ℝ) := lt_trans zero_lt_one hq_real
  have hγ_pos : 0 < γ := by
    have hfrac_pos :
        0 < ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) :=
      div_pos (sub_pos.mpr hq_real) hq_real_pos
    have hγ_eq :
        γ = ((Fintype.card α : ℝ) - 1) / (Fintype.card α : ℝ) := by
      dsimp [γ]
      field_simp [hq_real_pos.ne']
    rw [hγ_eq]
    exact hfrac_pos
  change 0 ≤ 1 - (1 / γ) * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * drel
  have hscaled' :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) * drel ≤ γ := by
    simpa [γ, drel] using hscaled
  rw [sub_nonneg]
  have hmul :
      (1 / γ) * ((((ℓ : ℝ) - 1) / (ℓ : ℝ)) * drel) ≤ (1 / γ) * γ :=
    mul_le_mul_of_nonneg_left hscaled' (by positivity)
  have hcancel : (1 / γ) * γ = 1 := by
    field_simp [hγ_pos.ne']
  nlinarith

/-- Monotone-radius version of
`Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le`. -/
theorem Lambda_le_of_le_JqℓRecipReal_minDist_of_scaled_distance_le
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hδ_le : δ ≤ JqℓRecipReal (Fintype.card α : ℝ) (ℓ : ℝ)
      ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ)))
    (hℓ : 2 ≤ ℓ) (hq_one : 1 < Fintype.card α)
    (hmin_pos : 0 < Code.minDist C)
    (hscaled :
      (((ℓ : ℝ) - 1) / (ℓ : ℝ)) *
          ((Code.minDist C : ℝ) / (Fintype.card ι : ℝ))
        ≤ 1 - 1 / (Fintype.card α : ℝ)) :
    ListDecodable.Lambda C δ ≤ (ℓ : ℕ∞) := by
  exact le_trans (ListDecodable.Lambda_mono (C := C) hδ_le)
    (Lambda_le_of_JqℓRecipReal_minDist_of_scaled_distance_le C hℓ hq_one hmin_pos hscaled)

/-- A violated finite `Lambda` bound produces a concrete point-list whose average
distance is controlled by the q-ary Plotkin bound.

This is the contradiction-entry bridge for `johnson_bound_lambda_le_ell`: after
assuming `ℓ < Lambda C δ`, one can work with the finite close-list around a
specific received word. -/
theorem exists_closeList_gt_and_averageDistOn_le_plotkin_of_natCast_lt_Lambda
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hq : 0 < Fintype.card α)
    (hΛ : (ℓ : ℕ∞) < ListDecodable.Lambda C δ) :
    ∃ f : ι → α,
      ℓ < (ListDecodable.closeCodewordsRelFinset C f δ).card ∧
        ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ≤
          ((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) /
              (((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) - 1) *
            (Fintype.card ι : ℝ) *
              (1 - 1 / (Fintype.card α : ℝ)) := by
  rcases ListDecodable.exists_closeFinset_card_gt_of_natCast_lt_Lambda hΛ with ⟨f, hf⟩
  refine ⟨f, hf, ?_⟩
  exact averageDistOn_le_plotkin (ListDecodable.closeCodewordsRelFinset C f δ)
    (by omega) hq

/-- A violated finite `Lambda` bound produces one concrete close-list carrying
both sides of the average-distance squeeze: its average distance is at least
`Code.minDist C`, and at most the q-ary Plotkin expression. -/
theorem exists_closeList_gt_and_minDist_le_averageDistOn_and_averageDistOn_le_plotkin
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hq : 0 < Fintype.card α)
    (hΛ : (ℓ : ℕ∞) < ListDecodable.Lambda C δ) :
    ∃ f : ι → α,
      ℓ < (ListDecodable.closeCodewordsRelFinset C f δ).card ∧
        ((Code.minDist C : ℚ) : ℝ) ≤
          ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ∧
        ((averageDistOn (ListDecodable.closeCodewordsRelFinset C f δ) : ℚ) : ℝ) ≤
          ((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) /
              (((ListDecodable.closeCodewordsRelFinset C f δ).card : ℝ) - 1) *
            (Fintype.card ι : ℝ) *
              (1 - 1 / (Fintype.card α : ℝ)) := by
  rcases exists_closeList_gt_and_averageDistOn_le_plotkin_of_natCast_lt_Lambda
      C hℓ hq hΛ with ⟨f, hf_card, hf_plotkin⟩
  refine ⟨f, hf_card, ?_, hf_plotkin⟩
  exact_mod_cast minDist_le_averageDistOn_closeCodewordsRelFinset C f δ (by omega)

end JohnsonBound

namespace CodingTheory

open scoped NNReal
open ListDecodable JohnsonBound

/-- **ABF26 Theorem 3.2 [Joh62].** Johnson bound on list size. For any code
`C ⊆ Σ^n` with `|Σ| = q`,

  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`

where `δ_min(C) = minDist(C) / n` is the relative minimum distance and `J_{q,ℓ}`
is the paper's q-ary ℓ-radius Johnson function. **Admitted (tagged sorry).**

**Why the in-tree `johnson_bound` does NOT reach this radius (verified, 2026-06-04).**
A prior triage suggested "plug `e/n = J_{q,ℓ}` into the in-tree `johnson_bound`; its
`JohnsonConditionStrong` then fails at the boundary, forcing `|Λ| ≤ ℓ`". This was
re-checked symbolically and is **incorrect** — there is a factor inversion that makes
the in-tree bound land at a *strictly smaller* radius. The exact computation:

Write `frac = q/(q-1)`, `t = frac·δ_min`, `L = ℓ/(ℓ-1) > 1`. The boundary identity for
`Jqℓ` is `(1 - frac·Jqℓ)² = 1 - frac·L·δ_min = 1 - L·t`. The packaged bound
[`johnson_bound`](Basic.lean) gives `B.card ≤ (frac·d/n)/Denom` with
`Denom = (1 - frac·e/n)² - (1 - frac·d/n)`. Setting `e/n = Jqℓ`, `d/n = δ_min`:
`Denom = (1 - L·t) - (1 - t) = t·(1 - L) = -t/(ℓ-1) < 0`. So `JohnsonConditionStrong`
(`Denom > 0`) is *false* and the bound is unusable — but the failure does **not** force
`|Λ| ≤ ℓ`: the raw [`johnson_bound_lemma`](Lemmas.lean), which holds unconditionally
(`n>0`, `|B|≥2`, `|F|≥2`), reads `B.card · Denom ≤ frac·d/n`, and with `Denom < 0` this
is a *negative lower* bound on `B.card` — vacuous as an upper bound.

Inverting the packaging the other way: `johnson_bound` yields `B.card ≤ ℓ` exactly when
`Denom ≥ (frac·d/n)/ℓ = t/ℓ`, i.e. `(1 - frac·e/n)² ≥ 1 - t·(ℓ-1)/ℓ = 1 - t/L`, i.e.
`e/n ≤ (1/frac)·(1 - √(1 - frac·δ_min/L))`. That radius uses the factor `1/L = (ℓ-1)/ℓ`,
the **reciprocal** of the `L = ℓ/(ℓ-1)` factor inside `Jqℓ`. Since `L > 1`, the in-tree
radius is strictly *smaller* than the paper's `Jqℓ`. The paper's larger (tight) list-of-ℓ
radius is the Plotkin-refined Johnson radius and is not reachable from the second-moment
`johnson_bound` alone.

**Exact missing ingredient (citation upgrade).** Closing T3.2 at the paper's `Jqℓ`
requires the *q-ary Plotkin average-distance upper bound*

  `d(B') ≤ frac · n · M/(M-1)`     where `M = |B'|`, `frac = q/(q-1)`,

i.e. the convex *dual* of the in-tree `almost_johnson` (which lower-bounds
`∑_α C₂(K_i(α))`; the Plotkin step instead lower-bounds `∑_α K_i(α)² ≥ M²/q` by
Cauchy–Schwarz / power-mean, giving an *upper* bound on the average distance).
The Plotkin piece is now in-tree as `indexed_averageDist_le_plotkin`,
`averageDistOn_le_plotkin`, and the `Fin n` specialization `averageDist_le_plotkin`.
Combining this bound with the remaining Johnson-radius algebra and a pointwise list
construction is the next step toward T3.2.

**Remaining mechanical gaps**:
- *Alphabet*: this statement is over a bare alphabet `α` (`Fintype + DecidableEq`, no
  `Field`), but every in-tree Johnson lemma — including `johnson_bound_alphabet_free` —
  carries `[Field F]`. The Plotkin bridge itself is alphabet-generic, but the older
  `johnson_bound_lemma` route is field-shaped.
- *List packaging*: a pointwise finite-list bound must be constructed for
  `closeCodewordsRel C f (Jqℓ q ℓ δ_min)` and then passed through
  `ListDecodable.Lambda_le_natCast_of_forall_ncard_le`.
- *Radius algebra*: the final `Jqℓ` inequality still has to be expressed in the exact
  rational/real shape consumed by the Johnson proof skeleton.

Tracked in `docs/kb/ABF26_PLAN.md` and the audit log.

**Alphabet generality.** Stated over an arbitrary alphabet `α` (not necessarily a
field), matching the paper's `Σ`. The Johnson bound is a purely combinatorial fact
about Hamming distance — it does not need field structure. -/
theorem johnson_bound_lambda_le_ell
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  -- ABF26-T3.2; external admit. The ONLY nontrivial gap is the q-ary Plotkin
  -- average-distance upper bound `d(B') ≤ frac·n·M/(M-1)` (see docstring). Four
  -- attempted in-tree routes, each blocked at a precisely-identified step:
  --
  -- SKELETON 1 (direct `johnson_bound`, the route the docstring refutes).
  --   intro q δ_min; refine iSup_le fun f => ?_;  set B' := closeCodewordsRel C f _
  --   Transport B' to a `Finset (Fin n → α)`; apply `johnson_bound` to get
  --   `B'.card ≤ (frac·d/n)/Denom`.  BLOCKED: at `e/n = Jqℓ`, `Denom = -t/(ℓ-1) < 0`,
  --   so `JohnsonConditionStrong` is false; no `B'.card ≤ ℓ` follows (factor inversion).
  --
  -- SKELETON 2 (raw `johnson_bound_lemma` + Plotkin — the CORRECT route).
  --   From `johnson_bound_lemma`: `M·Denom ≤ frac·d_avg/n`, holds unconditionally.
  --   Need: q-ary Plotkin `d_avg ≤ frac·n·M/(M-1)` ⇒ substitute and solve for M.
  --   STATUS: the Plotkin bound is now in-tree (`averageDistOn_le_plotkin` /
  --   `averageDist_le_plotkin`). Remaining work is the algebraic substitution into the
  --   Johnson skeleton and the `closeCodewordsRel`/`Lambda` packaging.
  --
  -- SKELETON 3 (`johnson_bound_alphabet_free` ⇒ `q·d·n`).
  --   `johnson_bound_alphabet_free` gives `(B ∩ ball e).card ≤ q·d·n` under
  --   `e ≤ n - √(n·(n-d))`.  BLOCKED twice: (a) the bound `q·d·n` is far weaker than `ℓ`
  --   (it is the alphabet-free coarse form, not list-of-ℓ); (b) its radius hypothesis is
  --   the `J_q` (ℓ→∞) radius, not `Jqℓ` — wrong both in tightness and in the ℓ-factor.
  --
  -- SKELETON 4 (Lambda_mono down to the in-tree reachable radius `1/L`).
  --   By the docstring, `johnson_bound` *does* give `|Λ(C, R₀)| ≤ ℓ` at
  --   `R₀ = (1/frac)(1 - √(1 - frac·δ_min/L))`.  `Lambda_mono` needs `Jqℓ ≤ R₀` to
  --   transport ℓ from `R₀` up to `Jqℓ`.  BLOCKED: `Jqℓ > R₀` (since `L > 1/L`), so
  --   monotonicity runs the WRONG way — it would only give `|Λ(C, Jqℓ)| ≥ |Λ(C, R₀)|`.
  --   This is the formal restatement of the factor inversion: the in-tree bound is
  --   strictly inside the paper's radius, and Lambda is monotone INCREASING in radius.
  --
  -- Tagged sorry until the Johnson-radius algebra and list-packaging layer land.
  sorry

/-- Pure-algebra engine for `mds_johnson_lambda_le`: the `β = √ρ` Johnson cap
`2·η·T²·(Dd − Do) ≤ −Do` after clearing the field-size denominator `Q = q`.

Here `T = √ρ`, `S = A − N·(T+η) ≥ 0` is the slack in the agreement lower bound,
`N` is the block length, and the two Gram quantities are written in closed form
(`−Do` and `Dd − Do`). The decisive use of the radius constraint `η ≤ 1 − T`
(equivalent to `1 − √ρ − η ≥ 0`) appears via `hEle`. -/
private lemma mds_core_ineq
    (N Q T E S : ℝ) (hN : 1 ≤ N) (hQ : 0 < Q) (hT0 : 0 < T) (hT1 : T < 1)
    (hE : 0 < E) (hEle : E ≤ 1 - T) (hS : 0 ≤ S) :
    2 * E * T ^ 2 * (N * (1 - 1 / Q) - (T ^ 2 * N - 1) + N / Q)
      ≤ (2 * T) * S + 1 + 2 * N * T * E + N * (1 / Q) * (1 - T) ^ 2 := by
  -- `F := 2QE(NT(T³−T+1) − T²) + N(1−T)² + Q ≥ 0`, the heart of the bound.
  have hcube : 0 ≤ T ^ 3 - T + 1 := by
    nlinarith [sq_nonneg (T - 1), hT0, hT1, mul_pos hT0 hT0]
  have ht2 : 2 * T ^ 2 * (1 - T) ≤ 1 := by
    nlinarith [sq_nonneg (3 * T - 2), hT0, hT1,
      mul_nonneg (sq_nonneg T) (le_of_lt (by linarith : (0 : ℝ) < 1 - T))]
  have p1 : 0 ≤ 2 * Q * E * N * T * (T ^ 3 - T + 1) := by positivity
  have p2 : 0 ≤ N * (1 - T) ^ 2 := by positivity
  have p3 : 0 ≤ 2 * Q * T ^ 2 * (1 - T - E) :=
    mul_nonneg (by positivity) (by linarith)
  have p4 : 0 ≤ Q * (1 - 2 * T ^ 2 * (1 - T)) :=
    mul_nonneg (le_of_lt hQ) (by linarith)
  have hF : 0 ≤ 2 * Q * E * (N * T * (T ^ 3 - T + 1) - T ^ 2) + N * (1 - T) ^ 2 + Q := by
    nlinarith [p1, p2, p3, p4]
  have hST : 0 ≤ 2 * Q * S * T := by positivity
  -- Clear the `1/Q` denominators and finish from `2QST + F ≥ 0`.
  rw [← sub_nonneg]
  have hid :
      ((2 * T) * S + 1 + 2 * N * T * E + N * (1 / Q) * (1 - T) ^ 2)
        - 2 * E * T ^ 2 * (N * (1 - 1 / Q) - (T ^ 2 * N - 1) + N / Q)
      = (2 * Q * S * T
          + (2 * Q * E * (N * T * (T ^ 3 - T + 1) - T ^ 2) + N * (1 - T) ^ 2 + Q)) / Q := by
    field_simp; ring
  rw [hid]
  exact div_nonneg (by linarith [hF, hST]) (le_of_lt hQ)

/-- **ABF26 Corollary 3.3.** MDS coarse Johnson corollary. For every MDS code `C` with
rate `ρ := dim C / n` and `η > 0`:

  `|Λ(C, 1 - √ρ - η)| ≤ 1 / (2 · η · ρ)`

Machine-checked via the radical-free simplex Johnson quadratic cap
(`CodeGeometry.johnson_quadratic_cap`) with shift parameter `β = √ρ`, the MDS
Singleton equation (`LinearCode.IsMDS_iff_rate_distance`, giving
`d_min = n - k + 1`), and the algebra lemma `mds_core_ineq`. This route does not
go through `johnson_bound_lambda_le_ell` (ABF26 T3.2).

**Rate derivation.** `ρ` is bound inline as `(Module.finrank F C : ℝ) / Fintype.card ι`
rather than passed as a separate parameter — this matches the upstream `IsMDS`
signature (additive Nat form, no rate parameter) and lets call sites use
`IsMDS_iff_rate_distance` to extract the rate-distance equation when needed. -/
theorem mds_johnson_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (η : ℝ) (_hη_pos : 0 < η)
    (_h_mds : LinearCode.IsMDS C) :
    let ρ : ℝ := (Module.finrank F C : ℝ) / Fintype.card ι
    (Lambda ((C : Set (ι → F))) (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  -- ABF26-C3.3. Full machine-checked proof via the radical-free Johnson quadratic
  -- cap (`CodeGeometry.johnson_quadratic_cap`) with shift parameter `β = √ρ`.
  --
  -- For each received word `f`, every codeword in the close list
  -- `Λ(C, 1-√ρ-η, f)` agrees with `f` on at least `A = n - ⌊δ·n⌋ ≥ n(√ρ+η)`
  -- coordinates, and distinct codewords pairwise agree on at most `B = n - d_min`
  -- coordinates. MDS gives `d_min = n - k + 1`, hence `B = k - 1`. The simplex
  -- Gram cap with `β = √ρ` then yields, for the list size `M`,
  --   `(M-1)·(-Do) ≤ Dd`,
  -- and the algebra `Dd ≤ (1/(2ηρ) - 1)·(-Do)` (with `-Do > 0`) closes
  -- `M ≤ 1/(2ηρ)`. Empty/degenerate radius cases (`δ < 0`) give `Λ = ∅`.
  classical
  intro ρ
  -- Basic facts about `n`, `k`, `ρ`.
  set n : ℕ := Fintype.card ι with hn_def
  set k : ℕ := Module.finrank F C with hk_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  -- MDS forces `1 ≤ k` (otherwise `d_min = n + 1 > n`, impossible).
  have hmin_eq : (Code.minDist ((C : Set (ι → F))) : ℝ) = (n : ℝ) - (k : ℝ) + 1 := by
    have h := (LinearCode.IsMDS_iff_rate_distance C).mp _h_mds
    have hk_le : k ≤ n := by
      rw [hk_def, hn_def]
      have := Submodule.finrank_le (R := F) (M := ι → F) C
      simpa [Module.finrank_fintype_fun_eq_card] using this
    -- `IsMDS_iff_rate_distance` gives the divided form; clear the denominator.
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
    rw [hn_def, hk_def] at *
    field_simp at h
    linarith
  have hmin_le : Code.minDist ((C : Set (ι → F))) ≤ n := by
    rw [hn_def]; exact minDist_le_card _
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have : (Code.minDist ((C : Set (ι → F))) : ℝ) = (n : ℝ) + 1 := by
      rw [hmin_eq, hk0']; push_cast; ring
    have hle : (Code.minDist ((C : Set (ι → F))) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmin_le
    linarith
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hρ_pos : 0 < ρ := by
    show 0 < (k : ℝ) / (n : ℝ)
    positivity
  set δ : ℝ := 1 - Real.sqrt ρ - η with hδ_def
  -- `q = card F ≥ 2`.
  have hq_pos : 0 < Fintype.card F := Fintype.card_pos
  -- Reduce to the empty-or-bounded case on the radius sign.
  by_cases hδ_neg : δ < 0
  · -- Radius negative: every close list is empty, so `Lambda = 0`.
    have hzero : Lambda ((C : Set (ι → F))) δ = 0 := by
      unfold Lambda
      apply le_antisymm _ (zero_le _)
      refine iSup_le fun f => ?_
      have hempty : closeCodewordsRel ((C : Set (ι → F))) f δ = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hc⟩
        simp only [ListDecodable.relHammingBall, Set.mem_setOf_eq] at hc
        exact absurd (le_trans (NNRat.cast_nonneg _) hc) (not_le.mpr hδ_neg)
      rw [hempty]; simp
    rw [hzero]; simp
  · push Not at hδ_neg
    -- Main case: `0 ≤ δ`. Pointwise bound, then lift to `Lambda`.
    -- `√ρ ≤ 1 - η`, so `ρ < 1` and `η ≤ 1 - √ρ`.
    set t : ℝ := Real.sqrt ρ with ht_def
    have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
    have ht_sq : t ^ 2 = ρ := by
      rw [ht_def, Real.sq_sqrt (le_of_lt hρ_pos)]
    have ht_pos : 0 < t := by
      rw [ht_def]; exact Real.sqrt_pos.mpr hρ_pos
    have hη_le : η ≤ 1 - t := by
      have : t ≤ 1 - η := by have := hδ_neg; rw [hδ_def] at this; linarith
      linarith
    have ht_lt_one : t < 1 := by linarith [_hη_pos, hη_le]
    -- RHS as a real number.
    have hrhs_pos : (0 : ℝ) < 1 / (2 * η * ρ) := by positivity
    -- Pointwise real bound on every close-list cardinality.
    have hpoint : ∀ f : ι → F,
        ((ListDecodable.closeCodewordsRelFinset ((C : Set (ι → F))) f δ).card : ℝ)
          ≤ 1 / (2 * η * ρ) := by
      intro f
      set S := ListDecodable.closeCodewordsRelFinset ((C : Set (ι → F))) f δ with hS_def
      set M : ℕ := S.card with hM_def
      by_cases hM0 : M = 0
      · rw [hM0]; simp only [Nat.cast_zero]; exact le_of_lt hrhs_pos
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
        -- Transport the close-list to a `Fin M`-indexed family.
        set e : Fin M ≃ S := (Finset.equivFin S).symm with he_def
        set c : Fin M → ι → F := fun i => (e i).1 with hc_def
        -- Center-agreement lower bound `A = n - ⌊δ·n⌋`.
        set A : ℕ := n - ⌊δ * (n : ℝ)⌋₊ with hA_def
        have hA : ∀ i, A ≤ CodeGeometry.agree (c i) f := by
          intro i
          have hmem : (c i) ∈ S := (e i).2
          rw [hA_def]
          exact card_sub_floor_mul_card_le_agree_of_mem_closeCodewordsRelFinset hδ_neg hmem
        -- Pairwise-agreement upper bound `B = n - d_min`.
        set B : ℕ := n - Code.minDist ((C : Set (ι → F))) with hB_def
        have hB : ∀ i j, i ≠ j → CodeGeometry.agree (c i) (c j) ≤ B := by
          intro i j hij
          have hci : (c i) ∈ S := (e i).2
          have hcj : (c j) ∈ S := (e j).2
          have hne : (c i) ≠ (c j) := by
            intro hval; apply hij; exact e.injective (Subtype.ext hval)
          rw [hB_def]
          exact closeCodewordsRelFinset_pairwise_agree_le_card_sub_minDist hci hcj hne
        -- Real values of `A`, `B`.
        have hδ_lt_one : δ < 1 := by rw [hδ_def]; linarith [ht_pos, _hη_pos]
        have hflr_le : (⌊δ * (n : ℝ)⌋₊ : ℝ) ≤ δ * (n : ℝ) :=
          Nat.floor_le (by positivity)
        have hflr_le_n : ⌊δ * (n : ℝ)⌋₊ ≤ n := by
          apply Nat.floor_le_of_le
          nlinarith [hδ_lt_one, hnR_pos, hδ_neg]
        have hAR_ge : (n : ℝ) - δ * (n : ℝ) ≤ ((A : ℝ)) := by
          rw [hA_def, Nat.cast_sub hflr_le_n]
          linarith [hflr_le]
        -- Real value of `B = k - 1`.
        have hmin_le_n : Code.minDist ((C : Set (ι → F))) ≤ n := hmin_le
        have hBR_eq : ((B : ℝ)) = (k : ℝ) - 1 := by
          rw [hB_def, Nat.cast_sub hmin_le_n]
          have : (Code.minDist ((C : Set (ι → F))) : ℝ) = (n : ℝ) - (k : ℝ) + 1 := hmin_eq
          linarith
        -- Abbreviations matching `johnson_quadratic_cap`.
        set q : ℝ := (Fintype.card F : ℝ) with hq_def
        have hqR_pos : 0 < q := by rw [hq_def]; exact_mod_cast hq_pos
        have hq_ge_one : (1 : ℝ) ≤ q := by rw [hq_def]; exact_mod_cast hq_pos
        have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
        have hinvq_pos : 0 < 1 / q := by positivity
        -- `k = ρ·n = t²·n`, and `A ≥ n·(t + η)` (since `δ = 1 - t - η`).
        have hkn : (k : ℝ) = t ^ 2 * (n : ℝ) := by
          have hkr : ρ = (k : ℝ) / (n : ℝ) := rfl
          rw [ht_sq, hkr]; field_simp
        have hAge : (n : ℝ) * (t + η) ≤ (A : ℝ) := by
          have heq : (n : ℝ) - δ * (n : ℝ) = (n : ℝ) * (t + η) := by rw [hδ_def]; ring
          linarith [hAR_ge, heq]
        have hAfac : 0 ≤ (A : ℝ) - (n : ℝ) * (t + η) := by linarith [hAge]
        -- Name the off-diagonal (`Do`) and diagonal (`Dd`) Gram bounds.
        set Do : ℝ :=
          ((B : ℝ) - (n : ℝ) / q) - 2 * t * ((A : ℝ) - (n : ℝ) / q)
            + t ^ 2 * (n : ℝ) * (1 - 1 / q) with hDo_def
        set Dd : ℝ :=
          (n : ℝ) * (1 - 1 / q) * (1 + t ^ 2) - 2 * t * ((A : ℝ) - (n : ℝ) / q)
          with hDd_def
        -- Closed forms (after `B = k-1 = t²n-1`), clearing the `1/q`.
        have hDo_id :
            Do = -(2 * t) * ((A : ℝ) - (n : ℝ) * (t + η)) - 1 - 2 * (n : ℝ) * t * η
              - (n : ℝ) * (1 / q) * (1 - t) ^ 2 := by
          rw [hDo_def, hBR_eq, hkn]; field_simp; ring
        have hDd_id :
            Dd = (n : ℝ) * (1 - 1 / q) * (1 + t ^ 2)
              - 2 * t * ((A : ℝ) - (n : ℝ) / q) := rfl
        -- Negativity of `Do`.
        have hDo_neg : Do < 0 := by
          rw [hDo_id]
          have h1 : 0 ≤ 2 * t * ((A : ℝ) - (n : ℝ) * (t + η)) :=
            mul_nonneg (by positivity) hAfac
          have h2 : 0 ≤ (n : ℝ) * (1 / q) * (1 - t) ^ 2 :=
            mul_nonneg (by positivity) (sq_nonneg _)
          have h3 : 0 ≤ 2 * (n : ℝ) * t * η := by positivity
          linarith
        have hnegDo_pos : 0 < -Do := by linarith
        -- `hcap : (M - 1) * (-Do) ≤ Dd`.
        have hcap := CodeGeometry.johnson_quadratic_cap
          (ι := ι) (α := F) hq_pos hMpos f c hA hB ht_nonneg
          (by rw [← hDo_def]; exact hDo_neg)
        rw [← hDo_def, ← hDd_def] at hcap
        -- Key algebraic inequality: `Dd ≤ (1/(2ηρ) - 1) * (-Do)`.
        have h2ηρ_pos : 0 < 2 * η * ρ := by positivity
        -- Core polynomial fact: `2·η·ρ·(Dd - Do) ≤ -Do`, from `mds_core_ineq`.
        have hN1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hcore : 2 * η * ρ * (Dd - Do) ≤ -Do := by
          have hDdDo : Dd - Do =
              (n : ℝ) * (1 - 1 / q) - ((t : ℝ) ^ 2 * (n : ℝ) - 1) + (n : ℝ) / q := by
            rw [hDd_def, hDo_def, hBR_eq, hkn]; ring
          have hnegDo_id :
              -Do = (2 * t) * ((A : ℝ) - (n : ℝ) * (t + η)) + 1 + 2 * (n : ℝ) * t * η
                + (n : ℝ) * (1 / q) * (1 - t) ^ 2 := by
            rw [hDo_id]; ring
          rw [hDdDo, hnegDo_id, ← ht_sq, show 2 * η * (t ^ 2) = 2 * η * t ^ 2 from rfl]
          exact mds_core_ineq (n : ℝ) q t η ((A : ℝ) - (n : ℝ) * (t + η))
            hN1 hqR_pos ht_pos ht_lt_one _hη_pos hη_le hAfac
        have hkey : Dd ≤ (1 / (2 * η * ρ) - 1) * (-Do) := by
          have hrw : (1 / (2 * η * ρ) - 1) * (-Do) = (-Do) / (2 * η * ρ) + Do := by
            field_simp; ring
          rw [hrw, ← sub_le_iff_le_add, le_div_iff₀ h2ηρ_pos]
          linarith [hcore]
        have hcap' : ((M : ℝ) - 1) * (-Do) ≤ (1 / (2 * η * ρ) - 1) * (-Do) :=
          le_trans hcap hkey
        have hMm1 : (M : ℝ) - 1 ≤ 1 / (2 * η * ρ) - 1 :=
          le_of_mul_le_mul_right hcap' hnegDo_pos
        linarith
    -- Lift the pointwise real bound to `Lambda ≤ ENNReal.ofReal (1/(2ηρ))`.
    -- First bound `Lambda` by the natural number `⌊1/(2ηρ)⌋₊`.
    set ℓ : ℕ := ⌊1 / (2 * η * ρ)⌋₊ with hℓ_def
    have hrhs_nonneg : (0 : ℝ) ≤ 1 / (2 * η * ρ) := by positivity
    have hΛ_le : ListDecodable.Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞) := by
      apply ListDecodable.Lambda_le_natCast_of_forall_closeFinset_card_le
      intro f
      rw [hℓ_def, Nat.le_floor_iff hrhs_nonneg]
      exact hpoint f
    -- Then convert through `ENNReal`, using `↑⌊x⌋₊ ≤ x`.
    have hcoe : (ListDecodable.Lambda ((C : Set (ι → F))) δ : ENNReal) ≤ (ℓ : ENNReal) := by
      have h := ENat.toENNReal_mono hΛ_le
      simpa using h
    refine le_trans hcoe ?_
    rw [show ((ℓ : ENNReal)) = ENNReal.ofReal (ℓ : ℝ) by
      rw [ENNReal.ofReal_natCast]]
    apply ENNReal.ofReal_le_ofReal
    rw [hℓ_def]
    exact Nat.floor_le hrhs_nonneg


end CodingTheory
