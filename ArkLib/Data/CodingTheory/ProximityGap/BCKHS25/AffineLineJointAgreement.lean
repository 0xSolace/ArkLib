/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCKHS25.Interpolation
import ArkLib.Data.CodingTheory.ProximityGap.BCKHS25.CollinearProximates
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# From the [BCKHS25] joint proximate to affine-line `jointAgreement`

The Hensel-free [BCKHS25] §2 route produces a single degree-`< deg` polynomial
pair `(p₀, p₁)` whose *joint* disagreement with the line word `(u₀, u₁)` is
small (Theorem 2.2 / Claim 2.3, `BCKHS25.proximity_gap_listDecoding` /
`exists_joint_proximate`). This file converts that joint-agreement bound into
the coding-theoretic `jointAgreement` predicate (the `Fin 2`/affine-line case of
`InterleavedCode.jointAgreement`): a common large agreement set together with two
codewords of the Reed–Solomon code.

This is the consumer-side bridge: it is exactly the output shape demanded by the
list-decoding branch of `δ_ε_correlatedAgreementAffineLines`, supplied here from
the Hensel-free joint pair rather than the §5 Hensel coefficient extraction.
-/

namespace BCKHS25

set_option linter.unusedSectionVars false

open NNReal Code Polynomial
open scoped LinearCode

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The two-row word stack of a line word `(u₀, u₁)`. -/
noncomputable def lineWordStack (u₀ u₁ : ι → F) : WordStack F (Fin 2) ι :=
  Matrix.of (fun (i : Fin 2) => if i = 0 then u₀ else u₁)

@[simp] lemma lineWordStack_zero (u₀ u₁ : ι → F) : lineWordStack u₀ u₁ 0 = u₀ := rfl
@[simp] lemma lineWordStack_one (u₀ u₁ : ι → F) : lineWordStack u₀ u₁ 1 = u₁ := rfl

/-- **Joint pair ⟹ affine-line `jointAgreement`.** A degree-`< deg` polynomial
pair `(p₀, p₁)` whose joint disagreement set with the line word `(u₀, u₁)` has
at most `Nat.floor (δ · n)` points yields the `jointAgreement` predicate for the
two-row stack `(u₀, u₁)` against the Reed–Solomon code: the common agreement set
has size `≥ (1 − δ)·n`, and `p₀, p₁` give the two required codewords.

Derivation: the agreement set `S = {x | p₀(domain x) = u₀ x ∧ p₁(domain x) = u₁ x}`
is the complement of the joint disagreement set, so
`|S| = n − |disagreement| ≥ n − ⌊δ·n⌋ ≥ (1−δ)·n`; and `evalOnPoints domain pᵢ`
is an RS codeword since `degree pᵢ < deg`. -/
theorem jointAgreement_of_jointDisagreement_le {deg : ℕ} [NeZero deg]
    {domain : ι ↪ F} {δ : ℝ≥0} {u₀ u₁ : ι → F} {p₀ p₁ : F[X]}
    (hp₀ : p₀.natDegree < deg) (hp₁ : p₁.natDegree < deg)
    (hdis : (Finset.univ.filter
      (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x))).card
        ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0))) :
    jointAgreement (F := F) (κ := Fin 2) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (W := lineWordStack u₀ u₁) := by
  classical
  set n := Fintype.card ι with hn
  -- agreement set: complement of the joint disagreement set
  set Dis : Finset ι := Finset.univ.filter
    (fun x => ¬(p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x)) with hDis
  set Agr : Finset ι := Finset.univ.filter
    (fun x => p₀.eval (domain x) = u₀ x ∧ p₁.eval (domain x) = u₁ x) with hAgr
  have hsplit : Agr.card + Dis.card = n := by
    rw [hAgr, hDis, hn, Finset.card_filter_add_card_filter_not]
    simp
  -- |Agr| = n − |Dis| ≥ n − ⌊δ·n⌋
  have hAgr_card_nat : n - Nat.floor (δ * (n : ℝ≥0)) ≤ Agr.card := by
    have : Dis.card ≤ Nat.floor (δ * (n : ℝ≥0)) := by simpa [hn] using hdis
    omega
  -- cardinality lower bound in ℝ≥0: |Agr| ≥ (1 − δ)·n
  have hAgr_real : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (Agr.card : ℝ≥0) := by
    -- (1 − δ)·n ≤ n − ⌊δ·n⌋ ≤ |Agr|
    have hfloor : ((Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) ≤ δ * (n : ℝ≥0) :=
      Nat.floor_le (by positivity)
    have hstep : (1 - δ) * (n : ℝ≥0) ≤ (n : ℝ≥0) - ((Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) := by
      rw [tsub_mul, one_mul]
      exact tsub_le_tsub_left hfloor _
    refine le_trans hstep ?_
    -- n − ⌊δ·n⌋ ≤ |Agr| via the ℕ inequality, cast to ℝ≥0
    have hcast : ((n - Nat.floor (δ * (n : ℝ≥0)) : ℕ) : ℝ≥0) ≤ (Agr.card : ℝ≥0) := by
      exact_mod_cast hAgr_card_nat
    refine le_trans ?_ hcast
    -- (n : ℝ≥0) − (⌊..⌋ : ℝ≥0) ≤ ((n − ⌊..⌋ : ℕ) : ℝ≥0) : standard cast-of-sub bound
    rw [tsub_le_iff_right, ← Nat.cast_add]
    have : n ≤ (n - Nat.floor (δ * (n : ℝ≥0))) + Nat.floor (δ * (n : ℝ≥0)) := by omega
    exact_mod_cast this
  -- the two RS codewords
  have hcw₀ : (fun x => p₀.eval (domain x)) ∈ ReedSolomon.code domain deg := by
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    exact ⟨p₀, hp₀, rfl⟩
  have hcw₁ : (fun x => p₁.eval (domain x)) ∈ ReedSolomon.code domain deg := by
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    exact ⟨p₁, hp₁, rfl⟩
  refine ⟨Agr, hAgr_real, fun i => if i = 0 then (fun x => p₀.eval (domain x))
    else (fun x => p₁.eval (domain x)), ?_⟩
  intro i
  fin_cases i
  · refine ⟨by simpa using hcw₀, ?_⟩
    intro x hx
    simp only [hAgr, Finset.mem_filter] at hx
    simpa [lineWordStack] using hx.2.1
  · refine ⟨by simpa using hcw₁, ?_⟩
    intro x hx
    simp only [hAgr, Finset.mem_filter] at hx
    simpa [lineWordStack] using hx.2.2

end BCKHS25
