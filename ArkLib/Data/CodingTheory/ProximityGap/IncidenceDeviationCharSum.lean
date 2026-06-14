/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# The incidence-deviation bound from a uniform char-sum (Gauss-period) bound — #407

This file proves the **deviation-of-incidence brick**: the quantitative step that turns a
uniform per-frequency bound `‖η_b‖ ≤ B` (`b ≠ 0`) on the subgroup Gauss period into a bound on
how far the far-line incidence `I(s₀, s₁)` can stray from its first-moment mean `|G|`.

The mechanism is the exact term-by-term spectral identity
`IncidencePeriodBridge.lineIncidence_period_sum`:

  > `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b) · ψ(b·s₀)`.

The trivial frequency `b = 0` always satisfies `b·s₁ = 0`, contributes `conj(η₀)·ψ(0) = |G|`
(the average / first moment), and the remaining `s₁^⊥ \ {0}` frequencies carry the spectral
error.  Each error term has modulus `‖conj(η_b)·ψ(b·s₀)‖ = ‖η_b‖ · 1 ≤ B` (additive characters
have unit modulus, conjugation is an isometry), so the total deviation is bounded by

  > `|I(s₀, s₁) − |G|| ≤ (#{b ≠ 0 : b·s₁ = 0}) · B`.

**Why this is the right (√-loss-free) lane.**  The competing energy lane
(`addEnergy_le_of_worstCase`) loses a square root (`T² ≤ |G|·E`), which is *fatal* for the prize
(it only reaches sub-Johnson).  The incidence-deviation bound here is *linear* in `B`: a
power-saving bound `B ≤ n^{1−c}` feeds straight through with no square-root loss, exactly the
calibration the prize regime requires.

This is the intermediate brick consumed by the bridge theorem
`CharSumDeltaStarBridge.le_mcaDeltaStar_of_uniformCharSumBound`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); pure triangle inequality on the
term-by-term spectral identity, no field-size or regime hypotheses.  Issue #407.
-/

set_option linter.unusedSectionVars false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.IncidenceDeviationCharSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The set of **nonzero** frequencies annihilating the line direction `s₁` — the spectral
support of the incidence deviation (the `s₁^⊥` hyperplane minus the trivial frequency). -/
def deviationSupport (s₁ : F) : Finset F :=
  (Finset.univ.filter (fun b : F => b * s₁ = 0)).erase 0

omit [DecidableEq F] in
/-- An additive character has modulus `1` on every input. Over a finite field every value
`ψ a : ℂ` is a root of unity (`val_mem_rootsOfUnity`), hence a pure phase. -/
theorem norm_addChar_apply (ψ : AddChar F ℂ) (a : F) : ‖ψ a‖ = 1 := by
  have hR : 0 < ringChar F := by
    have := CharP.ringChar_ne_zero_of_finite F
    omega
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity (ψ.val_mem_rootsOfUnity a hR)
  rwa [IsUnit.unit_spec] at H

/-- **The trivial frequency contributes the first moment.** At `b = 0` the spectral term is
`conj(η₀)·ψ(0) = |G|`. -/
theorem zero_freq_term {ψ : AddChar F ℂ} (G : Finset F) (s₀ : F) :
    (starRingEnd ℂ) (eta ψ G 0) * ψ (0 * s₀) = (G.card : ℂ) := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by
    simp [eta, AddChar.map_zero_eq_one]
  rw [h0, zero_mul, AddChar.map_zero_eq_one, mul_one, map_natCast]

/-- **The incidence-deviation identity.** The far-line incidence minus its first-moment mean
`|G|` equals the sum of period terms over the *nonzero* annihilating frequencies:

  `I(s₀, s₁) − |G| = ∑_{b ∈ deviationSupport s₁} conj(η_b)·ψ(b·s₀)`.

This isolates the spectral error from the average. -/
theorem incidence_sub_mean {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) :
    (lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)
      = ∑ b ∈ deviationSupport s₁,
          (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀) := by
  classical
  have hmem : (0 : F) ∈ Finset.univ.filter (fun b : F => b * s₁ = 0) := by
    simp
  rw [lineIncidence_period_sum hψ G s₀ s₁,
    ← Finset.add_sum_erase _ _ hmem, zero_freq_term G s₀]
  unfold deviationSupport
  ring

/-- **The deviation bound from a uniform char-sum bound (modulus form).** If every nonzero
frequency has `‖η_b‖ ≤ B`, then the far-line incidence deviates from its first-moment mean by at
most the number of nonzero annihilating frequencies times `B`:

  `|I(s₀, s₁) − |G|| ≤ (#deviationSupport s₁) · B`.

Pure triangle inequality on `incidence_sub_mean`; each error term has modulus
`‖η_b‖·‖ψ(b·s₀)‖ = ‖η_b‖ ≤ B`.  This is **linear** in `B` — no square-root loss — so a
power-saving Gauss-period bound feeds straight through. -/
theorem incidence_dev_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ}
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      ≤ ((deviationSupport s₁).card : ℝ) * B := by
  classical
  rw [incidence_sub_mean hψ G s₀ s₁]
  calc ‖∑ b ∈ deviationSupport s₁, (starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)‖
      ≤ ∑ b ∈ deviationSupport s₁, ‖(starRingEnd ℂ) (eta ψ G b) * ψ (b * s₀)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _b ∈ deviationSupport s₁, B := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
        rw [norm_mul, Complex.norm_conj, norm_addChar_apply, mul_one]
        exact hB b hb0
    _ = ((deviationSupport s₁).card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The deviation support is bounded by `q`.** A coarse but unconditional cardinality bound:
`#deviationSupport s₁ ≤ #{b : b·s₁ = 0} ≤ |F| = q`.  Combined with `incidence_dev_le` this gives
the worst-case incidence bound `I ≤ |G| + q·B`; the prize's spectral support is in fact a single
hyperplane (`≤ q/|s₁-line|`), but the `≤ q` bound already suffices for the bridge calibration. -/
theorem deviationSupport_card_le (s₁ : F) :
    (deviationSupport s₁).card ≤ Fintype.card F := by
  classical
  unfold deviationSupport
  exact le_trans (Finset.card_erase_le)
    (le_trans (Finset.card_filter_le _ _) (le_of_eq (Finset.card_univ)))

/-- **Worst-case incidence upper bound from a uniform char-sum bound.** Combining the deviation
bound with the cardinality bound: under `‖η_b‖ ≤ B` (`b ≠ 0`), the (real, nonnegative) far-line
incidence satisfies

  `I(s₀, s₁) ≤ |G| + q·B`.

This is the form the bridge consumes: a small `B` (power-saving) forces the incidence close to
its mean `|G|`, hence below the budget `q·ε*`. -/
theorem lineIncidence_le_mean_add {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B) :
    (lineIncidence G s₀ s₁ : ℝ) ≤ (G.card : ℝ) + (Fintype.card F : ℝ) * B := by
  classical
  have hdev := incidence_dev_le hψ G s₀ s₁ hB
  -- Pass to the real part: ‖(I : ℂ) - |G|‖ ≥ |I - |G|| ≥ I - |G| (as reals).
  have hcast : ‖(lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ)‖
      = |(lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)| := by
    rw [show ((lineIncidence G s₀ s₁ : ℂ) - (G.card : ℂ))
          = (((lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ) : ℝ) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcast] at hdev
  have habs : (lineIncidence G s₀ s₁ : ℝ) - (G.card : ℝ)
      ≤ ((deviationSupport s₁).card : ℝ) * B :=
    le_trans (le_abs_self _) hdev
  have hcard : ((deviationSupport s₁).card : ℝ) * B ≤ (Fintype.card F : ℝ) * B := by
    apply mul_le_mul_of_nonneg_right _ hB0
    exact_mod_cast deviationSupport_card_le s₁
  linarith

end ArkLib.ProximityGap.IncidenceDeviationCharSum

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.incidence_sub_mean
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.incidence_dev_le
#print axioms ArkLib.ProximityGap.IncidenceDeviationCharSum.lineIncidence_le_mean_add
