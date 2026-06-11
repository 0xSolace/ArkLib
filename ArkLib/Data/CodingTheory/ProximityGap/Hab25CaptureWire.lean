/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureReconcile
import ArkLib.Data.CodingTheory.ProximityGap.Hab25LaneBridge
import ArkLib.ToMathlib.ZAffineDecomposition

/-!
# The capture wire — from the lane's close decode to `AffineCaptured`

Two links of the per-stack capture chain:

* `agreement_card_of_relDist_le` (ℝ form) and its `ℝ≥0` wrapper — the reverse counting: a
  relative distance `≤ δ` leaves an agreement set of size `≥ (1-δ)·n`, the mirror of the
  lane bridge's direction.
* `affineCaptured_of_pz_affine` — the per-scalar capture: a bad scalar whose lane decode
  is the affine pencil `A₀ + γ·A₁` is captured at `(A₀, A₁)`, via the witness-set
  reconciliation.

Together with the surface-factor production (whose coherence makes the lane decode *be*
the pencil on the whole close set, via the Z-affine decomposition) these produce the
one-pair capture list for every word stack.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap Code Polynomial
open scoped NNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- **Reverse counting (ℝ form).**  Relative distance at most `δq` leaves an agreement
set of size at least `(1 - δq)·n`. -/
theorem agreement_card_real_of_relDist_le
    {n : ℕ} [NeZero n] {f g : Fin n → F} {δq : ℚ}
    (hd : ((relHammingDist f g : ℚ≥0) : ℚ) ≤ δq) :
    (1 - (δq : ℝ)) * (Fintype.card (Fin n) : ℝ)
      ≤ ((Finset.univ.filter (fun i => f i = g i)).card : ℝ) := by
  classical
  have hsplit : (Finset.univ.filter (fun i => f i = g i)).card
      + (Finset.univ.filter (fun i => ¬ f i = g i)).card = Fintype.card (Fin n) := by
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => f i = g i)
  have hn0 : (0 : ℝ) < (Fintype.card (Fin n) : ℝ) := by
    have : 0 < Fintype.card (Fin n) := Fintype.card_pos
    exact_mod_cast this
  have hdis_le : ((Finset.univ.filter (fun i => ¬ f i = g i)).card : ℝ)
      ≤ (δq : ℝ) * (Fintype.card (Fin n) : ℝ) := by
    have hdef : ((relHammingDist f g : ℚ≥0) : ℝ)
        = ((Finset.univ.filter (fun i => ¬ f i = g i)).card : ℝ)
          / (Fintype.card (Fin n) : ℝ) := by
      rw [relHammingDist]
      push_cast
      rfl
    have hdR : ((relHammingDist f g : ℚ≥0) : ℝ) ≤ (δq : ℝ) := by
      exact_mod_cast hd
    rw [hdef, div_le_iff₀ hn0] at hdR
    linarith
  have hcast : ((Finset.univ.filter (fun i => f i = g i)).card : ℝ)
      + ((Finset.univ.filter (fun i => ¬ f i = g i)).card : ℝ)
      = (Fintype.card (Fin n) : ℝ) := by
    exact_mod_cast hsplit
  nlinarith

open Classical in
/-- **Reverse counting (`ℝ≥0` form, at a rational radius).**  The agreement set meets the
`mcaEvent`-style cardinality bound at `δ := δq.toNNReal`. -/
theorem agreement_card_of_relDist_le
    {n : ℕ} [NeZero n] {f g : Fin n → F} {δq : ℚ}
    (hd : ((relHammingDist f g : ℚ≥0) : ℚ) ≤ δq) :
    ((Finset.univ.filter (fun i => f i = g i)).card : ℝ≥0)
      ≥ (1 - Real.toNNReal (δq : ℝ)) * Fintype.card (Fin n) := by
  classical
  set δ : ℝ≥0 := Real.toNNReal (δq : ℝ) with hδ
  rw [ge_iff_le, ← NNReal.coe_le_coe]
  push_cast
  rcases le_total (1 : ℝ≥0) δ with h1 | h1
  · -- `δ ≥ 1`: the truncated factor vanishes
    rw [tsub_eq_zero_of_le h1]
    simp
  · -- `δ ≤ 1`: the factor coincides with the real form
    have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
      rw [NNReal.coe_sub h1]
      simp
    rw [hcoe]
    have hδle : (δ : ℝ) ≤ (δq : ℝ) ⊔ 0 := by
      rw [hδ, Real.coe_toNNReal']
    have hmain := agreement_card_real_of_relDist_le (f := f) (g := g) hd
    have hn0 : (0 : ℝ) ≤ (Fintype.card (Fin n) : ℝ) := Nat.cast_nonneg _
    rcases le_total (0 : ℝ) ((δq : ℝ)) with h0 | h0
    · have hδeq : (δ : ℝ) = (δq : ℝ) := by
        rw [hδ, Real.coe_toNNReal _ h0]
      rw [hδeq]
      exact hmain
    · -- negative radius: distance `≤ δq ≤ 0` forces full agreement; bound is direct
      have hδ0 : (δ : ℝ) = 0 := by
        rw [hδ, Real.coe_toNNReal']
        simp [max_eq_right h0]
      rw [hδ0]
      have : (1 - (δq : ℝ)) * (Fintype.card (Fin n) : ℝ)
          ≥ (1 - 0) * (Fintype.card (Fin n) : ℝ) := by nlinarith
      nlinarith [hmain]

open Classical in
/-- **The per-scalar capture.**  A bad scalar whose lane decode is the affine pencil
`A₀ + γ·A₁` (degrees `< k`) is captured at `(A₀, A₁)`: the decode's agreement set has the
required size by reverse counting, and the witness-set reconciliation transfers capture to
the `mcaEvent` set. -/
theorem affineCaptured_of_pz_affine
    {n k : ℕ} [NeZero n] {ωs : Fin n ↪ F} {δq : ℚ} {u : WordStack F (Fin 2) (Fin n)}
    {γ : F} {A₀ A₁ : F[X]}
    (hdeg₀ : A₀.natDegree < k) (hdeg₁ : A₁.natDegree < k)
    (hbad : mcaEvent ((ReedSolomon.code ωs k : Set (Fin n → F)))
      (Real.toNNReal (δq : ℝ)) (u 0) (u 1) γ)
    (hclose : ((relHammingDist (u 0 + γ • u 1)
      (fun i => (A₀ + Polynomial.C γ * A₁).eval (ωs i)) : ℚ≥0) : ℚ) ≤ δq)
    (hreg : (k : ℝ) + 2 * ((Real.toNNReal (δq : ℝ) : ℝ≥0) : ℝ) * Fintype.card (Fin n)
      < Fintype.card (Fin n)) :
    AffineCaptured ωs k (Real.toNNReal (δq : ℝ)) u γ (A₀, A₁) := by
  classical
  refine affineCaptured_of_close_affine hdeg₀ hdeg₁ hbad
    (S₁ := Finset.univ.filter (fun i =>
      (u 0 + γ • u 1) i = (A₀ + Polynomial.C γ * A₁).eval (ωs i))) ?_ ?_ hreg
  · exact agreement_card_of_relDist_le hclose
  · intro i hi
    have := (Finset.mem_filter.mp hi).2
    simpa using this.symm

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.agreement_card_real_of_relDist_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.agreement_card_of_relDist_le
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.affineCaptured_of_pz_affine
