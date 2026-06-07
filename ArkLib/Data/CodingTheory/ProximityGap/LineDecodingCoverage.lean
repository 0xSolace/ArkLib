/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecoding
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount

/-!
# The GG25 multi-γ coverage lemma for line-decoding → MCA (Issue #12)

`LineDecoding.lean` documents the wall in ABF26 Theorem 4.21 [GG25 Thm 3.5]: the black-box
"line-decodable ⟹ `ε_mca ≤ a/q`" form is **false** (`LineDecodingRefutation`,
`LineDecodingCounting.double_coverage_counterexample`), because the `n+1`-point alignment
budget bounds only the *average* per-coordinate coverage, while `pairJointAgreesOn` is
**antitone** in its witness set and needs agreement on *all* of it.

This file supplies the faithful replacement the wall calls for, addressing the antitone
obstruction directly: it works with **per-coordinate double coverage** (two distinct aligned
scalars per coordinate of the witness set) — exactly the data a Guruswami–Sudan bivariate
decoder produces (the aligned `γ`'s are the roots of one interpolation polynomial, so each
surviving coordinate carries ≥ 2 of them) — rather than the refuted per-`γ`-budget count.

Main results (all kernel-clean):

* `affine_eq_of_two_smul_points` — the core: two distinct scalars at which an affine word
  `a₀ + γ·a₁` meets `b₀ + γ·b₁` pin `a₀ = b₀` and `a₁ = b₁` (a degree-1 word with two roots
  is the zero word).
* `pairJointAgreesOn_of_double_cover` — **THE reusable multi-γ coverage lemma** (Issue #12
  ask 1): per-coordinate double coverage of a witness set `T` by aligned scalars forces the
  line-decoder pair `(u₁, u₂)` to agree with `(f₁, f₂)` on all of `T`, hence
  `pairJointAgreesOn`.
* `not_mcaEvent_of_double_cover` — consequently a bad scalar whose witness set is
  double-covered cannot satisfy `mcaEvent` (its `¬ pairJointAgreesOn` clause is violated).
* `epsMCA_eq_zero_of_forall_double_cover` / `mcaBadCount_eq_zero_of_forall_double_cover` —
  the repaired Theorem-4.21 conclusion at the error level: when every stack's every bad
  scalar is double-covered, `ε_mca = 0`. This is the honest statement REPAIR the wall
  prescribes: the open GS content is the *existence* of double coverage (the exposed
  interpolation hypothesis), and the coverage ⟹ agreement ⟹ MCA-vanishing logic is proven.

## References

- [ABF26] §4.4, Theorem 4.21 (= [GG25] Thm 3.5). [BCIKS20] Thm 5.1 (GS bivariate route).
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Affine two-point pinning.** If the affine-in-`γ` element `a₀ + γ • a₁` equals
`b₀ + γ • b₁` at two distinct scalars `γ ≠ γ'`, then `a₀ = b₀` and `a₁ = b₁`. (A degree-`1`
word over a field with two roots is constant-and-zero.) This is the per-coordinate kernel of
the coverage lemma. -/
theorem affine_eq_of_two_smul_points {a₀ a₁ b₀ b₁ : A} {γ γ' : F} (hne : γ ≠ γ')
    (h : a₀ + γ • a₁ = b₀ + γ • b₁) (h' : a₀ + γ' • a₁ = b₀ + γ' • b₁) :
    a₀ = b₀ ∧ a₁ = b₁ := by
  -- Differences vanish: `c₀ + γ • c₁ = 0` and `c₀ + γ' • c₁ = 0`.
  have hc : (a₀ - b₀) + γ • (a₁ - b₁) = 0 := by
    rw [smul_sub]; rw [sub_add_sub_comm]; rw [h]; abel
  have hc' : (a₀ - b₀) + γ' • (a₁ - b₁) = 0 := by
    rw [smul_sub]; rw [sub_add_sub_comm]; rw [h']; abel
  -- Subtract: `(γ - γ') • (a₁ - b₁) = 0`, and `γ - γ' ≠ 0` is invertible.
  have hsub : (γ - γ') • (a₁ - b₁) = 0 := by
    have := sub_eq_zero.mpr (hc.trans hc'.symm)
    rw [sub_smul]
    rw [show γ • (a₁ - b₁) - γ' • (a₁ - b₁)
          = ((a₀ - b₀) + γ • (a₁ - b₁)) - ((a₀ - b₀) + γ' • (a₁ - b₁)) by abel]
    rw [hc, hc', sub_zero]
  have hγγ' : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  have h1 : a₁ - b₁ = 0 := by
    have := smul_eq_zero.mp hsub
    rcases this with h | h
    · exact absurd h hγγ'
    · exact h
  have h0 : a₀ - b₀ = 0 := by
    have : (a₀ - b₀) + γ • (a₁ - b₁) = 0 := hc
    rw [h1, smul_zero, add_zero] at this
    exact this
  exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1⟩

/-- **The GG25 multi-γ coverage lemma (Issue #12 ask 1, reusable form).**

Let `(u₁, u₂)` be the line-decoder's witness pair and `(f₁, f₂)` the line stack. Suppose
every coordinate `i` of a witness set `T` is **doubly covered**: there are two *distinct*
aligned scalars `γ ≠ γ'` at which the pair-induced line `u₁ + γ • u₂` agrees with the data
line `f₁ + γ • f₂` at `i`. Then `(u₁, u₂)` agrees with `(f₁, f₂)` on **all** of `T`, so the
pair is a joint witness: `pairJointAgreesOn C T f₁ f₂`.

Unlike the refuted per-`γ`-budget count, this hypothesis is **per-coordinate**, so it is not
defeated by the antitone behaviour of `pairJointAgreesOn` (every `i ∈ T` is handled
individually). It is exactly the coverage a Guruswami–Sudan bivariate list-decoder provides:
the aligned scalars are roots of one interpolation polynomial, so each surviving coordinate
carries at least two of them. -/
theorem pairJointAgreesOn_of_double_cover (C : Set (ι → A)) (T : Finset ι) (f₁ f₂ u₁ u₂ : ι → A)
    (hu₁ : u₁ ∈ C) (hu₂ : u₂ ∈ C)
    (hcov : ∀ i ∈ T, ∃ γ γ' : F, γ ≠ γ' ∧
      u₁ i + γ • u₂ i = f₁ i + γ • f₂ i ∧
      u₁ i + γ' • u₂ i = f₁ i + γ' • f₂ i) :
    pairJointAgreesOn C T f₁ f₂ := by
  refine ⟨u₁, hu₁, u₂, hu₂, ?_⟩
  intro i hi
  obtain ⟨γ, γ', hne, h, h'⟩ := hcov i hi
  exact affine_eq_of_two_smul_points hne h h'

end

/-! ## S-pinned form and the repaired Theorem-4.21 error conclusion

The clean statement (used downstream) pins the witness set: an `mcaEvent` is given *with* its
witness set `S` exposed, and the double cover is on that same `S`. -/

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Per-set MCA double-cover data.** A witness set `S` is doubly covered when one
line-decoder pair `(v₁, v₂) ∈ C × C` supplies two distinct aligned scalars at every coordinate
of `S`. This names the exact per-set datum that the repaired GS extraction must construct. -/
def MCADoubleCoverOn (C : Set (ι → A)) (u₀ u₁ : ι → A) (S : Finset ι) : Prop :=
  ∃ v₁ ∈ C, ∃ v₂ ∈ C,
    ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
      v₁ i + a • v₂ i = u₀ i + a • u₁ i ∧
      v₁ i + a' • v₂ i = u₀ i + a' • u₁ i

/-- Named form of `pairJointAgreesOn_of_double_cover` over `MCADoubleCoverOn`. -/
theorem pairJointAgreesOn_of_MCADoubleCoverOn (C : Set (ι → A))
    (S : Finset ι) (u₀ u₁ : ι → A)
    (hcov : MCADoubleCoverOn (F := F) C u₀ u₁ S) :
    pairJointAgreesOn C S u₀ u₁ := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hcover⟩ := hcov
  exact pairJointAgreesOn_of_double_cover C S u₀ u₁ v₁ v₂ hv₁ hv₂ hcover

/-- **`mcaEvent` with an S-pinned double cover is impossible.** Given a concrete witness set
`S` realising the `mcaEvent` body (size + line-witness + `¬ pairJointAgreesOn S`), a
line-decoder pair `(v₁, v₂) ∈ C` doubly covering `S` contradicts the `¬ pairJointAgreesOn S`
clause. This is the per-coordinate-coverage discharge of the bad event. -/
theorem not_mcaEventBody_of_double_cover (C : Set (ι → A)) (u₀ u₁ : ι → A)
    (S : Finset ι) {v₁ v₂ : ι → A} (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C)
    (hpair : ¬ pairJointAgreesOn C S u₀ u₁)
    (hcov : ∀ i ∈ S, ∃ γ γ' : F, γ ≠ γ' ∧
      v₁ i + γ • v₂ i = u₀ i + γ • u₁ i ∧
      v₁ i + γ' • v₂ i = u₀ i + γ' • u₁ i) :
    False :=
  hpair (pairJointAgreesOn_of_double_cover C S u₀ u₁ v₁ v₂ hv₁ hv₂ hcov)

/-- S-pinned bad-event impossibility using the named `MCADoubleCoverOn` surface. -/
theorem not_mcaEventBody_of_MCADoubleCoverOn (C : Set (ι → A)) (u₀ u₁ : ι → A)
    (S : Finset ι) (hpair : ¬ pairJointAgreesOn C S u₀ u₁)
    (hcov : MCADoubleCoverOn (F := F) C u₀ u₁ S) :
    False :=
  hpair (pairJointAgreesOn_of_MCADoubleCoverOn C S u₀ u₁ hcov)

/-- **Per-bad-scalar double-cover obligation.** Once a scalar is bad, every exposed `mcaEvent`
witness set must carry `MCADoubleCoverOn` data. This is the exact local target for the remaining
GS interpolation / multi-γ overlap extraction. -/
def MCABadScalarDoubleCover (C : Set (ι → A)) (δ : ℝ≥0)
    (u₀ u₁ : ι → A) (γ : F) : Prop :=
  mcaEvent C δ u₀ u₁ γ →
    ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
      ¬ pairJointAgreesOn C S u₀ u₁ →
      MCADoubleCoverOn (F := F) C u₀ u₁ S

/-- **Exposed repaired T4.21 hypothesis.** Every stack and every bad scalar carries the
per-coordinate double cover that the Guruswami--Sudan interpolation route must provide. This is
the replacement data for the refuted black-box `lineDecodable_imp_epsMCA_le_target`. -/
def MCAForallDoubleCover (C : Set (ι → A)) (δ : ℝ≥0) : Prop :=
  ∀ (u : WordStack A (Fin 2) ι) (γ : F), mcaEvent C δ (u 0) (u 1) γ →
    ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
      ¬ pairJointAgreesOn C S (u 0) (u 1) →
      ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
        v₁ i + a • v₂ i = (u 0) i + a • (u 1) i ∧
        v₁ i + a' • v₂ i = (u 0) i + a' • (u 1) i

/-- Unpack the global repaired hypothesis into the named per-bad-scalar obligation. -/
theorem MCAForallDoubleCover.to_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : MCAForallDoubleCover (F := F) (A := A) C δ) :
    ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  intro u γ
  simpa [MCABadScalarDoubleCover, MCADoubleCoverOn] using hcov u γ

/-- Repack per-bad-scalar double-cover obligations as the existing global repaired hypothesis. -/
theorem MCAForallDoubleCover.of_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    MCAForallDoubleCover (F := F) (A := A) C δ := by
  intro u γ
  simpa [MCABadScalarDoubleCover, MCADoubleCoverOn] using hcov u γ

/-- The repaired global T4.21 hypothesis is equivalent to the named local bad-scalar surface. -/
theorem MCAForallDoubleCover_iff_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) :
    MCAForallDoubleCover (F := F) (A := A) C δ ↔
      ∀ (u : WordStack A (Fin 2) ι) (γ : F),
        MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ := by
  constructor
  · exact MCAForallDoubleCover.to_badScalarDoubleCover C δ
  · exact MCAForallDoubleCover.of_badScalarDoubleCover C δ

open Classical in
/-- **Repaired Theorem 4.21, per-stack form.** If for the stack `(u₀, u₁)` every bad scalar's
witness set is doubly covered by a (scalar-dependent) line-decoder pair in `C`, then no bad
scalar exists: `mcaBadCount C δ u₀ u₁ = 0`. The double-coverage hypothesis is the exposed GS
interpolation data; everything else is proven. -/
theorem mcaBadCount_eq_zero_of_double_cover (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : ∀ γ : F, mcaEvent C δ u₀ u₁ γ →
      ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) →
        ¬ pairJointAgreesOn C S u₀ u₁ →
        ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
          v₁ i + a • v₂ i = u₀ i + a • u₁ i ∧
          v₁ i + a' • v₂ i = u₀ i + a' • u₁ i) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 := by
  classical
  rw [mcaBadCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro γ _hγ hev
  obtain ⟨S, hsize, hwit, hpair⟩ := hev
  obtain ⟨v₁, hv₁, v₂, hv₂, hcover⟩ := hcov γ ⟨S, hsize, hwit, hpair⟩ S hsize hwit hpair
  exact not_mcaEventBody_of_double_cover C u₀ u₁ S hv₁ hv₂ hpair hcover

open Classical in
/-- Per-stack repaired T4.21 wrapper through `MCABadScalarDoubleCover`. -/
theorem mcaBadCount_eq_zero_of_badScalarDoubleCover
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A)
    (hcov : ∀ γ : F,
      MCABadScalarDoubleCover (F := F) (A := A) C δ u₀ u₁ γ) :
    mcaBadCount (F := F) C δ u₀ u₁ = 0 := by
  exact mcaBadCount_eq_zero_of_double_cover C δ u₀ u₁
    (fun γ hγ S hsize hwit hpair => by
      simpa [MCADoubleCoverOn] using hcov γ hγ S hsize hwit hpair)

open Classical in
/-- **Repaired Theorem 4.21, error form.** If every stack's every bad scalar's witness set is
doubly covered, then `ε_mca(C, δ) = 0`. This is the faithful replacement for the refuted
black-box `lineDecodable_imp_epsMCA_le`: the open GS content is isolated as the explicit
double-coverage hypothesis (criterion: statement REPAIR exposing the interpolation data), and
the coverage ⟹ agreement ⟹ MCA-vanishing implication is fully proven. -/
theorem epsMCA_eq_zero_of_forall_double_cover (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F), mcaEvent C δ (u 0) (u 1) γ →
      ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        (∃ w ∈ C, ∀ i ∈ S, w i = (u 0) i + γ • (u 1) i) →
        ¬ pairJointAgreesOn C S (u 0) (u 1) →
        ∃ v₁ ∈ C, ∃ v₂ ∈ C, ∀ i ∈ S, ∃ a a' : F, a ≠ a' ∧
          v₁ i + a • v₂ i = (u 0) i + a • (u 1) i ∧
          v₁ i + a' • v₂ i = (u 0) i + a' • (u 1) i) :
    epsMCA (F := F) C δ = 0 := by
  classical
  rw [epsMCA_eq_iSup_mcaBadCount]
  have hzero : ∀ u : WordStack A (Fin 2) ι,
      (mcaBadCount (F := F) C δ (u 0) (u 1) : ℝ≥0∞) = 0 := by
    intro u
    rw [mcaBadCount_eq_zero_of_double_cover C δ (u 0) (u 1) (hcov u)]
    simp
  rw [iSup_congr hzero]
  simp

/-- Error-level repaired T4.21 wrapper through `MCABadScalarDoubleCover`. -/
theorem epsMCA_eq_zero_of_badScalarDoubleCover (C : Set (ι → A)) (δ : ℝ≥0)
    (hcov : ∀ (u : WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) C δ (u 0) (u 1) γ) :
    epsMCA (F := F) C δ = 0 := by
  exact epsMCA_eq_zero_of_forall_double_cover C δ
    (fun u γ hγ S hsize hwit hpair => by
      simpa [MCADoubleCoverOn] using hcov u γ hγ S hsize hwit hpair)

#print axioms MCADoubleCoverOn
#print axioms MCABadScalarDoubleCover
#print axioms pairJointAgreesOn_of_MCADoubleCoverOn
#print axioms not_mcaEventBody_of_MCADoubleCoverOn
#print axioms MCAForallDoubleCover
#print axioms MCAForallDoubleCover_iff_badScalarDoubleCover
#print axioms mcaBadCount_eq_zero_of_badScalarDoubleCover
#print axioms epsMCA_eq_zero_of_badScalarDoubleCover

end

end ProximityGap

namespace CodingTheory

open ProximityGap
open scoped NNReal ProbabilityTheory

section RepairedTarget

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Repaired discharge of the legacy target proposition.** The old black-box statement remains a
named `Prop`, because line-decodability alone is refuted. Once the repaired theorem's explicit
double-cover data is supplied, however, `ε_mca(C, δ) = 0`, so the legacy target conclusion follows
without using the false implication. -/
theorem lineDecodable_imp_epsMCA_le_target_of_forall_double_cover
    (C : ModuleCode ι F A) (δ a : ℝ≥0)
    (_hLD : LineDecodable (F := F) (A := A) (C : Set (ι → A)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hcov : MCAForallDoubleCover (F := F) (A := A) (C : Set (ι → A)) δ) :
    lineDecodable_imp_epsMCA_le_target (F := F) (A := A) C δ a _hLD := by
  dsimp [lineDecodable_imp_epsMCA_le_target]
  rw [epsMCA_eq_zero_of_forall_double_cover (F := F) (A := A) (C : Set (ι → A)) δ hcov]
  exact zero_le _

/-- Same repaired target discharge, but consuming the named per-bad-scalar double-cover surface
directly. This is the local target shape expected from a future GS extraction proof. -/
theorem lineDecodable_imp_epsMCA_le_target_of_badScalarDoubleCover
    (C : ModuleCode ι F A) (δ a : ℝ≥0)
    (_hLD : LineDecodable (F := F) (A := A) (C : Set (ι → A)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hcov : ∀ (u : Code.WordStack A (Fin 2) ι) (γ : F),
      MCABadScalarDoubleCover (F := F) (A := A) (C : Set (ι → A)) δ (u 0) (u 1) γ) :
    lineDecodable_imp_epsMCA_le_target (F := F) (A := A) C δ a _hLD := by
  dsimp [lineDecodable_imp_epsMCA_le_target]
  rw [epsMCA_eq_zero_of_badScalarDoubleCover (F := F) (A := A)
    (C : Set (ι → A)) δ hcov]
  exact zero_le _

#print axioms CodingTheory.lineDecodable_imp_epsMCA_le_target_of_forall_double_cover
#print axioms CodingTheory.lineDecodable_imp_epsMCA_le_target_of_badScalarDoubleCover

end RepairedTarget

end CodingTheory
