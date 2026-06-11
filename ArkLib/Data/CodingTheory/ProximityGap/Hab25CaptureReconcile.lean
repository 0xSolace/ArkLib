/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD
import ArkLib.Data.CodingTheory.ProximityGap.Hab25AffineCapture

/-!
# Witness-set reconciliation — capture from any close affine decode

The §5 lane proves its per-scalar affine identity against *its own* agreement set, while
`AffineCaptured` demands agreement on the `mcaEvent` witness set (which carries the
forbidden-joint-agreement clause).  In the regime `k + 2·δ·n < n` the two reconcile: the
`mcaEvent` codeword and the lane's affine polynomial agree with the fold on the
intersection of the two witness sets — more than `k` points — so degree-forcing makes
them *equal*, and the affine pair captures on the `mcaEvent` set itself.

This is the final conversion at the boundary: any per-scalar conclusion of the form
"the fold is close to `a + γ·b`" becomes `AffineCaptured` verbatim.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open _root_.ProximityGap Code Polynomial
open scoped NNReal

variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]
variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]

open Classical in
/-- **Capture from any close affine decode.**  If `γ` is `mcaEvent`-bad and the affine
polynomial `a + γ·b` (degrees `< k`) agrees with the fold on *some* witness set of size
`≥ (1-δ)·n`, then in the regime `k + 2·δ·n < n` the pair `(a, b)` captures `γ` on the
`mcaEvent` witness set itself: the two agreement sets overlap in more than `k` points,
forcing the `mcaEvent` codeword to equal `a + γ·b`. -/
theorem affineCaptured_of_close_affine
    {k : ℕ} {δ : ℝ≥0} {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀} {a b : F₀[X]}
    (hdeg_a : a.natDegree < k) (hdeg_b : b.natDegree < k)
    (hbad : mcaEvent ((ReedSolomon.code domain k : Set (ι₀ → F₀))) δ (u 0) (u 1) γ)
    {S₁ : Finset ι₀}
    (hS₁card : ((S₁.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀))
    (hS₁agree : ∀ i ∈ S₁, (a + Polynomial.C γ * b).eval (domain i) = u 0 i + γ • u 1 i)
    (hreg : (k : ℝ) + 2 * (δ : ℝ) * Fintype.card ι₀ < Fintype.card ι₀) :
    AffineCaptured domain k δ u γ (a, b) := by
  obtain ⟨S₀, hS₀card, ⟨w, hwC, hwagree⟩, hnjp⟩ := hbad
  -- the `mcaEvent` codeword as a polynomial
  obtain ⟨P, hPdeg, hPev⟩ := ReedSolomon.mem_code_iff_exists_polynomial.mp hwC
  -- the intersection is large: `|S₀ ∩ S₁| > k`
  have hN0 : (0 : ℝ) ≤ (Fintype.card ι₀ : ℝ) := Nat.cast_nonneg _
  have hcoe : ∀ S : Finset ι₀, ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι₀) →
      (1 - (δ : ℝ)) * (Fintype.card ι₀ : ℝ) ≤ (S.card : ℝ) := by
    intro S hS
    have h1δ : (1 : ℝ) - (δ : ℝ) ≤ ((1 - δ : ℝ≥0) : ℝ) := by
      rcases le_total (δ : ℝ≥0) 1 with h | h
      · rw [NNReal.coe_sub h]; simp
      · have h1 : ((1 - δ : ℝ≥0) : ℝ) = 0 := by rw [tsub_eq_zero_of_le h]; rfl
        have h2 : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h
        linarith
    have hcast : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι₀ : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hS
    nlinarith
  have hS₀ := hcoe S₀ hS₀card
  have hS₁ := hcoe S₁ hS₁card
  have hinter : (k : ℝ) < ((S₀ ∩ S₁).card : ℝ) := by
    have hunion : ((S₀ ∪ S₁).card : ℝ) ≤ (Fintype.card ι₀ : ℝ) := by
      exact_mod_cast Finset.card_le_univ _
    have hie : (S₀ ∪ S₁).card + (S₀ ∩ S₁).card = S₀.card + S₁.card :=
      Finset.card_union_add_card_inter S₀ S₁
    have hieR : ((S₀ ∪ S₁).card : ℝ) + ((S₀ ∩ S₁).card : ℝ)
        = (S₀.card : ℝ) + (S₁.card : ℝ) := by
      exact_mod_cast hie
    nlinarith
  -- degree-forcing: the codeword equals the affine polynomial
  have haff_deg : (a + Polynomial.C γ * b).natDegree < k := by
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
    rw [max_lt_iff]
    refine ⟨hdeg_a, lt_of_le_of_lt (Polynomial.natDegree_mul_le) ?_⟩
    simpa using hdeg_b
  have heq : P = a + Polynomial.C γ * b := by
    have hdiff : (P - (a + Polynomial.C γ * b)).degree < k := by
      have h1 : P.degree < k := hPdeg
      have h2 : (a + Polynomial.C γ * b).degree < k := by
        rcases eq_or_ne (a + Polynomial.C γ * b) 0 with h0 | h0
        · rw [h0, Polynomial.degree_zero]
          exact WithBot.bot_lt_coe k
        · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mp haff_deg
      exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
    have hzero : P - (a + Polynomial.C γ * b) = 0 := by
      refine eq_zero_of_degree_lt_of_vanishes_on (domain := domain) hdiff (S₀ ∩ S₁)
        (by exact_mod_cast hinter.le) fun i hi => ?_
      have hi₀ := Finset.mem_inter.mp hi |>.1
      have hi₁ := Finset.mem_inter.mp hi |>.2
      have hw : P.eval (domain i) = u 0 i + γ • u 1 i := by
        have := hwagree i hi₀
        rw [hPev] at this
        exact this
      rw [Polynomial.eval_sub, hw, hS₁agree i hi₁, sub_self]
    exact sub_eq_zero.mp hzero
  -- capture on the `mcaEvent` set
  refine ⟨S₀, hS₀card, fun i hi => ?_, hnjp⟩
  have := hwagree i hi
  rw [hPev] at this
  rw [← heq]
  exact this

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.affineCaptured_of_close_affine
