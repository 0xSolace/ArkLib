/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Two-line correlated-agreement extraction (proximity gap, linear codes)

The genuinely-linear-algebraic core of the affine-line correlated-agreement / proximity-gap
argument for **linear** codes: if two distinct scalars `z ≠ z'` both make the affine-line word
`u₀ + z • u₁` agree with a codeword (`w` on `S`, `w'` on `S'`), then `u₀` and `u₁` *themselves*
agree with codewords on the common set `S ∩ S'`.

Concretely, on `S ∩ S'` the difference `w − w' = (z − z') • u₁`, so

  `v₁ := (z − z')⁻¹ • (w − w') ∈ C`   and   `v₀ := w − z • v₁ ∈ C`

are codewords (by `Submodule` closure) with `v₁ = u₁` and `v₀ = u₀` on `S ∩ S'`.

This is the step that turns "many points of the line are close to the code" into "the pair is
jointly close": at radius `δ` each `w, w'` agrees on `≥ (1−δ)n` coordinates, so `S ∩ S'` has size
`≥ (1−2δ)n` and the pair is jointly `2δ`-close.  (Closing the factor-2 gap to the genuine radius `δ`
is the BCIKS20 *curve* argument — the codewords must be shown affine-linear in `z` — and is left to
that development; this lemma supplies the linear-extraction half unconditionally.)
-/

namespace ProximityGap

open Finset Code
open scoped NNReal

variable {ι : Type*} [DecidableEq ι] {F : Type*} [Field F]

/-- **Two-line linear extraction.**  For a linear code `C` (a submodule), if codewords `w, w'`
agree with the affine-line words `u₀ + z • u₁` and `u₀ + z' • u₁` on `S` and `S'` respectively
(with `z ≠ z'`), then there are codewords `v₀, v₁ ∈ C` agreeing with `u₀` and `u₁` on `S ∩ S'`. -/
theorem exists_joint_codewords_of_two_lines
    (C : Submodule F (ι → F)) {u₀ u₁ : ι → F} {z z' : F} (hzz' : z ≠ z')
    {w w' : ι → F} (hw : w ∈ C) (hw' : w' ∈ C) {S S' : Finset ι}
    (hwS : ∀ i ∈ S, w i = u₀ i + z • u₁ i)
    (hw'S : ∀ i ∈ S', w' i = u₀ i + z' • u₁ i) :
    ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S ∩ S', v₀ i = u₀ i ∧ v₁ i = u₁ i := by
  set v₁ : ι → F := (z - z')⁻¹ • (w - w') with hv₁def
  set v₀ : ι → F := w - z • v₁ with hv₀def
  have hsub : z - z' ≠ 0 := sub_ne_zero.mpr hzz'
  have hv₁mem : v₁ ∈ C := C.smul_mem _ (C.sub_mem hw hw')
  have hv₀mem : v₀ ∈ C := C.sub_mem hw (C.smul_mem z hv₁mem)
  refine ⟨v₀, hv₀mem, v₁, hv₁mem, ?_⟩
  intro i hi
  rw [Finset.mem_inter] at hi
  have e1 : w i = u₀ i + z * u₁ i := by simpa [smul_eq_mul] using hwS i hi.1
  have e2 : w' i = u₀ i + z' * u₁ i := by simpa [smul_eq_mul] using hw'S i hi.2
  -- on `S ∩ S'`, `w i - w' i = (z - z') u₁ i`
  have hwdiff : w i - w' i = (z - z') * u₁ i := by rw [e1, e2]; ring
  -- v₁ i = (z - z')⁻¹ (w i - w' i) = (z - z')⁻¹ (z - z') u₁ i = u₁ i
  have hv₁i : v₁ i = u₁ i := by
    simp only [hv₁def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hwdiff, inv_mul_cancel_left₀ hsub]
  -- v₀ i = w i - z · v₁ i = (u₀ i + z u₁ i) - z u₁ i = u₀ i
  have hv₀i : v₀ i = u₀ i := by
    simp only [hv₀def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv₁i, e1]
    ring
  exact ⟨hv₀i, hv₁i⟩

section JointAgreement

variable [Fintype ι] [DecidableEq F]

/-- **Two-line radius-`2δ` correlated agreement (complete proof chain).**  If two distinct scalars
`z ≠ z'` each make the affine-line word agree with a codeword on a set of size `≥ (1-δ)·n`, then the
pair `(u₀, u₁)` is jointly `2δ`-close to the linear code `C`: there are codewords matching `u₀` and
`u₁` on the common set, of size `≥ (1-2δ)·n`.  Combines the linear extraction with the
inclusion–exclusion overlap bound. -/
theorem jointAgreement_two_delta_of_two_lines
    (C : Submodule F (ι → F)) (δ : ℝ≥0) {u₀ u₁ : ι → F} {z z' : F} (hzz' : z ≠ z')
    {w w' : ι → F} (hw : w ∈ C) (hw' : w' ∈ C) {S S' : Finset ι}
    (hwS : ∀ i ∈ S, w i = u₀ i + z • u₁ i)
    (hw'S : ∀ i ∈ S', w' i = u₀ i + z' • u₁ i)
    (hScard : ((1 : ℝ) - δ) * Fintype.card ι ≤ (S.card : ℝ))
    (hS'card : ((1 : ℝ) - δ) * Fintype.card ι ≤ (S'.card : ℝ)) :
    Code.jointAgreement (↑C : Set (ι → F)) (2 * δ) (![u₀, u₁] : Fin 2 → ι → F) := by
  classical
  obtain ⟨v₀, hv₀C, v₁, hv₁C, hagree⟩ :=
    exists_joint_codewords_of_two_lines C hzz' hw hw' hwS hw'S
  refine ⟨S ∩ S', ?_, ![v₀, v₁], ?_⟩
  · -- |S ∩ S'| ≥ (1 - 2δ)·n  from inclusion–exclusion and |S∪S'| ≤ n
    have hie : (S ∩ S').card + (S ∪ S').card = S.card + S'.card :=
      Finset.card_inter_add_card_union S S'
    have hunion : (S ∪ S').card ≤ Fintype.card ι := Finset.card_le_univ _
    have hieR : ((S ∩ S').card : ℝ) + (S ∪ S').card = S.card + S'.card := by exact_mod_cast hie
    have hunionR : ((S ∪ S').card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hunion
    -- real lower bound `(1 - 2δ)·n ≤ |S ∩ S'|`
    have hreal : ((1 : ℝ) - 2 * δ) * Fintype.card ι ≤ ((S ∩ S').card : ℝ) := by nlinarith
    -- cast the `jointAgreement` NNReal goal `(1 - 2δ)·n ≤ |S ∩ S'|` through ℝ
    have hgoal : ((1 - 2 * δ : ℝ≥0) : ℝ) * Fintype.card ι ≤ ((S ∩ S').card : ℝ) := by
      rcases le_total (2 * δ) 1 with hle | hge
      · have : ((1 - 2 * δ : ℝ≥0) : ℝ) = 1 - 2 * (δ : ℝ) := by
          rw [NNReal.coe_sub hle]; push_cast; ring
        rw [this]; exact hreal
      · have : ((1 - 2 * δ : ℝ≥0) : ℝ) = 0 := by
          rw [NNReal.coe_eq_zero]; exact tsub_eq_zero_of_le hge
        rw [this, zero_mul]; positivity
    have : ((1 - 2 * δ : ℝ≥0) * Fintype.card ι : ℝ≥0) ≤ ((S ∩ S').card : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hgoal
    exact_mod_cast this
  · -- the two codewords match `u₀`, `u₁` on `S ∩ S'`
    intro k
    fin_cases k
    · refine ⟨hv₀C, ?_⟩
      intro j hj
      simpa using (hagree j hj).1
    · refine ⟨hv₁C, ?_⟩
      intro j hj
      simpa using (hagree j hj).2

end JointAgreement

/-! ### Toward the genuine radius `δ`: the many-points linearity argument

The factor-2 loss above comes from intersecting just two agreement sets.  If instead the affine-line
words agree with a *fixed* codeword pair `(v₀, v₁)` — the BCIKS20 "curve" hypothesis, available in
the unique-decoding regime where the close codeword is unique and hence affine-linear in the
combining scalar — then agreement can be read off **coordinate by coordinate**, and a single
coordinate seen by two distinct scalars already pins both `u₀` and `u₁` there.  Aggregating over many
close scalars drives the joint-agreement radius from `2δ` back toward `δ`. -/

/-- **Per-coordinate linearity.**  If at coordinate `i` the affine-line word agrees with the fixed
codeword line `v₀ + z • v₁` for two distinct scalars `z ≠ z'`, then `u₀` and `u₁` agree with `v₀`
and `v₁` at `i`.  (The two linear equations `a + z·b = 0`, `a + z'·b = 0` with `a := u₀ᵢ - v₀ᵢ`,
`b := u₁ᵢ - v₁ᵢ` force `a = b = 0`.) -/
theorem eq_at_coord_of_two_scalars
    {u₀ u₁ v₀ v₁ : ι → F} {i : ι} {z z' : F} (hzz' : z ≠ z')
    (h : u₀ i + z • u₁ i = v₀ i + z • v₁ i)
    (h' : u₀ i + z' • u₁ i = v₀ i + z' • v₁ i) :
    u₀ i = v₀ i ∧ u₁ i = v₁ i := by
  simp only [smul_eq_mul] at h h'
  -- subtract the two equations: `(z - z')·(u₁ᵢ - v₁ᵢ) = 0`
  have hb : (z - z') * (u₁ i - v₁ i) = 0 := by linear_combination h - h'
  have hu₁ : u₁ i = v₁ i := by
    rcases mul_eq_zero.mp hb with hz | hb'
    · exact absurd (sub_eq_zero.mp hz) hzz'
    · exact sub_eq_zero.mp hb'
  refine ⟨?_, hu₁⟩
  -- back-substitute to get `u₀ᵢ = v₀ᵢ`
  have hh := h
  rw [hu₁] at hh
  linear_combination hh

/-- **Many-points joint agreement on the fixed-line agreement core.**  Given a fixed codeword pair
`(v₀, v₁)` and, for each scalar `z` in a set `Z`, an agreement set `S z` on which the affine-line
word equals `v₀ + z • v₁`, every coordinate seen by *two distinct* scalars of `Z` agrees with both
`v₀` and `v₁`.  Hence the joint-agreement set is `⋃_{z≠z'} (S z ∩ S z')` — no factor-2 radius loss
per coordinate. -/
theorem eq_at_coord_of_mem_two_agree
    {u₀ u₁ v₀ v₁ : ι → F} {Z : Finset F} {S : F → Finset ι} {i : ι}
    (hagree : ∀ z ∈ Z, ∀ j ∈ S z, u₀ j + z • u₁ j = v₀ j + z • v₁ j)
    {z z' : F} (hz : z ∈ Z) (hz' : z' ∈ Z) (hzz' : z ≠ z')
    (hiz : i ∈ S z) (hiz' : i ∈ S z') :
    u₀ i = v₀ i ∧ u₁ i = v₁ i :=
  eq_at_coord_of_two_scalars hzz' (hagree z hz i hiz) (hagree z' hz' i hiz')

section DoubleCounting

variable [Fintype ι] [DecidableEq F]

/-- The set of coordinates seen by at least two scalars of `Z` (where `u₀, u₁` are pinned). -/
noncomputable def doubleHitSet (Z : Finset F) (S : F → Finset ι) : Finset ι :=
  Finset.univ.filter (fun i => 2 ≤ (Z.filter (fun z => i ∈ S z)).card)

/-- **Double-counting incidence bound.**  Summing the agreement-set sizes counts incidences
`(z, i)` with `i ∈ S z`; a coordinate not in `doubleHitSet` carries `≤ 1` incidence and one in it
carries `≤ |Z|`, so `∑_{z∈Z} |S z| ≤ |doubleHitSet|·|Z| + (n − |doubleHitSet|)`.  Combined with
`∑_{z∈Z}|S z| ≥ |Z|·(1−δ)n`, this drives the joint-agreement size toward `(1−δ)n` as `|Z|` grows. -/
theorem sum_card_le_doubleHit (Z : Finset F) (S : F → Finset ι) :
    (∑ z ∈ Z, (S z).card) ≤
      (doubleHitSet Z S).card * Z.card + (Fintype.card ι - (doubleHitSet Z S).card) := by
  classical
  set c : ι → ℕ := fun i => (Z.filter (fun z => i ∈ S z)).card with hc
  -- double count: ∑_{z∈Z} |S z| = ∑_i c i
  have hdc : (∑ z ∈ Z, (S z).card) = ∑ i : ι, c i := by
    simp only [hc, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext j; simp
  -- split the universe at the `doubleHitSet` predicate
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 2 ≤ c i) c
  have hbig : (doubleHitSet Z S).card = (Finset.univ.filter (fun i => 2 ≤ c i)).card := rfl
  -- the two pieces, bounded by `|Z|` and `1` per coordinate
  have hpart1 : (∑ i ∈ Finset.univ.filter (fun i => 2 ≤ c i), c i)
      ≤ (doubleHitSet Z S).card * Z.card := by
    rw [hbig]
    calc (∑ i ∈ Finset.univ.filter (fun i => 2 ≤ c i), c i)
        ≤ ∑ _i ∈ Finset.univ.filter (fun i => 2 ≤ c i), Z.card :=
          Finset.sum_le_sum fun i _ => Finset.card_filter_le _ _
      _ = (Finset.univ.filter (fun i => 2 ≤ c i)).card * Z.card := by
          rw [Finset.sum_const, smul_eq_mul]
  have hcompl : (Finset.univ.filter (fun i => 2 ≤ c i)).card
      + (Finset.univ.filter (fun i => ¬ 2 ≤ c i)).card = Fintype.card ι := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
  have hpart2 : (∑ i ∈ Finset.univ.filter (fun i => ¬ 2 ≤ c i), c i)
      ≤ Fintype.card ι - (doubleHitSet Z S).card := by
    have hle : (∑ i ∈ Finset.univ.filter (fun i => ¬ 2 ≤ c i), c i)
        ≤ (Finset.univ.filter (fun i => ¬ 2 ≤ c i)).card := by
      calc (∑ i ∈ Finset.univ.filter (fun i => ¬ 2 ≤ c i), c i)
          ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬ 2 ≤ c i), 1 :=
            Finset.sum_le_sum fun i hi => by
              simp only [Finset.mem_filter, not_le] at hi; omega
        _ = (Finset.univ.filter (fun i => ¬ 2 ≤ c i)).card := by simp
    rw [hbig]; omega
  rw [hdc, ← hsplit]
  omega

/-- **The double-hit set is a joint-agreement set.**  Every coordinate seen by two scalars of `Z`
agrees with both `v₀` and `v₁` (per-coordinate linearity), so `doubleHitSet ⊆ {i : u₀ i = v₀ i ∧
u₁ i = v₁ i}`.  Combined with `sum_card_le_doubleHit` and `∑|S z| ≥ |Z|(1−δ)n`, this is the
quantitative many-points correlated-agreement bound: the joint-agreement set has size
`≥ (|Z|(1−δ) − 1)/(|Z|−1)·n → (1−δ)n`. -/
theorem doubleHitSet_subset_joint
    {u₀ u₁ v₀ v₁ : ι → F} {Z : Finset F} {S : F → Finset ι}
    (hagree : ∀ z ∈ Z, ∀ j ∈ S z, u₀ j + z • u₁ j = v₀ j + z • v₁ j) :
    doubleHitSet Z S ⊆ Finset.univ.filter (fun i => u₀ i = v₀ i ∧ u₁ i = v₁ i) := by
  intro i hi
  simp only [doubleHitSet, Finset.mem_filter] at hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
  -- a coordinate hit by ≥2 scalars is hit by two *distinct* ones
  obtain ⟨z, hz, z', hz', hzz'⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le one_lt_two hi.2)
  rw [Finset.mem_filter] at hz hz'
  exact eq_at_coord_of_mem_two_agree hagree hz.1 hz'.1 hzz' hz.2 hz'.2

end DoubleCounting

section UniqueDecoding

variable [Fintype ι] [DecidableEq F]

/-- **Codewords agreeing past the minimum distance coincide.**  If a linear code `C` has minimum
distance `≥ D` (every nonzero codeword has support `≥ D`), then two codewords agreeing on a set of
size `> n − D` are equal — their difference is a codeword vanishing on more than `n − D`
coordinates, hence of support `< D`, hence zero.  This is the unique-decoding keystone behind
BCIKS20's affine-line *curve* property: it forces the close codeword of each line word to be unique
and, combined with the two-line extraction, affine-linear in the combining scalar. -/
theorem codeword_eq_of_agree
    (C : Submodule F (ι → F)) {D : ℕ}
    (hmin : ∀ a ∈ C, a ≠ 0 → D ≤ (Finset.univ.filter (fun i => a i ≠ 0)).card)
    {c c' : ι → F} (hc : c ∈ C) (hc' : c' ∈ C) {S : Finset ι}
    (hagree : ∀ i ∈ S, c i = c' i) (hScard : Fintype.card ι - D < S.card) :
    c = c' := by
  classical
  by_contra hne
  have hdiff : c - c' ∈ C := C.sub_mem hc hc'
  have hdne : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have hsupp := hmin _ hdiff hdne
  -- the support of `c - c'` avoids the agreement set `S`
  have hsub : (Finset.univ.filter (fun i => (c - c') i ≠ 0)) ⊆ Sᶜ := by
    intro i hi
    simp only [Finset.mem_filter, Pi.sub_apply] at hi
    rw [Finset.mem_compl]
    intro hiS
    exact hi.2 (sub_eq_zero.mpr (hagree i hiS))
  have hcard : (Finset.univ.filter (fun i => (c - c') i ≠ 0)).card ≤ Sᶜ.card :=
    Finset.card_le_card hsub
  rw [Finset.card_compl] at hcard
  -- `D ≤ |support| ≤ n − |S| < D`
  have key : D ≤ Fintype.card ι - S.card := le_trans hsupp hcard
  have hSle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  omega

/-- **Affine-linearity of the close codeword (BCIKS20 curve).**  In the unique-decoding regime
`3·m < D` (minimum distance `D`, agreement deficit `m := ⌊δ·n⌋`): if `v₀, v₁ ∈ C` agree with `u₀,
u₁` on a set `S₀` of size `> n − 2·(n−|S₀|)`… more simply, if a codeword `w` agrees with the line
`u₀ + z • u₁` on `S_w` and the fixed codewords `v₀, v₁` agree with `u₀, u₁` on `S₀`, with the joint
overlap exceeding `n − D`, then `w = v₀ + z • v₁`.  Hence every close codeword lies on the affine
line `{v₀ + z • v₁}`, supplying the fixed-line hypothesis the per-coordinate / double-counting
argument consumes. -/
theorem close_codeword_eq_line
    (C : Submodule F (ι → F)) {D : ℕ}
    (hmin : ∀ a ∈ C, a ≠ 0 → D ≤ (Finset.univ.filter (fun i => a i ≠ 0)).card)
    {u₀ u₁ v₀ v₁ : ι → F} (hv₀ : v₀ ∈ C) (hv₁ : v₁ ∈ C) {z : F}
    {w : ι → F} (hw : w ∈ C) {Sw S₀ : Finset ι}
    (hwS : ∀ i ∈ Sw, w i = u₀ i + z • u₁ i)
    (h₀S : ∀ i ∈ S₀, u₀ i = v₀ i ∧ u₁ i = v₁ i)
    (hcard : Fintype.card ι - D < (Sw ∩ S₀).card) :
    w = v₀ + z • v₁ := by
  classical
  refine codeword_eq_of_agree C hmin hw (C.add_mem hv₀ (C.smul_mem z hv₁)) ?_ hcard
  intro i hi
  rw [Finset.mem_inter] at hi
  obtain ⟨hu₀, hu₁⟩ := h₀S i hi.2
  -- on the overlap: `w i = u₀ i + z·u₁ i = v₀ i + z·v₁ i = (v₀ + z•v₁) i`
  rw [hwS i hi.1, hu₀, hu₁]
  simp [Pi.add_apply, Pi.smul_apply]

/-- The minimum distance lower-bounds the support of every nonzero codeword of a linear code:
`(a, 0)` is a distinct codeword pair at distance `|support a|`, so `minDist ≤ |support a|`. -/
theorem minDist_le_support_of_mem (C : Submodule F (ι → F)) {a : ι → F}
    (ha : a ∈ C) (ha0 : a ≠ 0) :
    Code.minDist (C : Set (ι → F)) ≤ (Finset.univ.filter (fun i => a i ≠ 0)).card := by
  have hsupp : (Finset.univ.filter (fun i => a i ≠ 0)).card = hammingDist a 0 := by
    rw [hammingDist]; congr 1
  rw [hsupp]
  exact Nat.sInf_le ⟨a, ha, 0, C.zero_mem, ha0, rfl⟩

/-- **Unique decoding for any linear code — complete, no side hypotheses.**  Two codewords of a
linear code `C` that agree on more than `n − minDist C` coordinates are equal.  This is the
Reed–Solomon / MDS unique-decoding statement at the level of an abstract linear code: instantiated
with `minDist (RS[n,k]) = n − k + 1` it says RS codewords agreeing on `≥ k` points coincide. -/
theorem codeword_eq_of_agree_minDist (C : Submodule F (ι → F))
    {c c' : ι → F} (hc : c ∈ C) (hc' : c' ∈ C) {S : Finset ι}
    (hagree : ∀ i ∈ S, c i = c' i)
    (hScard : Fintype.card ι - Code.minDist (C : Set (ι → F)) < S.card) :
    c = c' :=
  codeword_eq_of_agree C (fun a ha ha0 => minDist_le_support_of_mem C ha ha0) hc hc' hagree hScard

end UniqueDecoding

end ProximityGap
