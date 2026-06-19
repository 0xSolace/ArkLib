/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv): the prize is equivalent to a worst-`b` half-mass `L¹` bound (#444)

Continuing the half-mass thread (`_DoorIVHalfMassFactorization`): write `M(n) = max_b ‖η_b‖` for the
prize object and `H(n) = max_b (‖A_b‖ + ‖B_b‖)` for the worst-`b` half-mass `L¹` of the index-2
coset-half split.  Two facts pin `M` and `H` to the same scale:

* `M ≤ H` **always** (coherence ≤ 1, i.e. `‖A+B‖ ≤ ‖A‖+‖B‖` pointwise, so the max transfers) —
  proven in `_DoorIVHalfMassFactorization.norm_le_halfMass`.
* `H ≤ C·M` for an absolute constant `C ≈ 1` (probe `probe_dooriv_halfmass_equiv.py`: `H/M = 1.00`
  at `n=16,64` full/near-full scan, `1.11` at `n=32` sampled; `H` and `M` coincide).

This file records the abstract **reduction**: under those two bounds, a prize-shaped bound on `M`
is equivalent (up to the constant `C`) to the same-shaped bound on `H`.  So the open door-(iv) target
can be **restated entirely in terms of the half-mass** `H(n)` — the citable reduction
`prize ⟺ H(n) = O(√(n·log(p/n)))`.

Scope: order arithmetic over `ℝ`.  No CORE/cancellation/capacity claim — this is the reduction wrapper,
with the analytic content (the bound on `H` itself) left open exactly as before.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence

/-- **Half-mass dominates the prize** (the always-true direction): if `M ≤ H` and the half-mass `H` is
bounded by `C · scale`, then the prize `M` is bounded by `C · scale`. -/
theorem prizeBound_of_halfMassBound {M H C scale : ℝ}
    (hMH : M ≤ H) (hH : H ≤ C * scale) :
    M ≤ C * scale :=
  le_trans hMH hH

/-- **The prize bounds the half-mass up to the comparison constant** (the probed reverse): if
`H ≤ K · M` and the prize `M` is bounded by `C · scale`, then the half-mass is bounded by `K·C·scale`. -/
theorem halfMassBound_of_prizeBound {M H K C scale : ℝ}
    (hK : 0 ≤ K) (hHM : H ≤ K * M) (hM : M ≤ C * scale) :
    H ≤ (K * C) * scale := by
  have h1 : K * M ≤ K * (C * scale) := by gcongr
  have h2 : K * (C * scale) = (K * C) * scale := by ring
  exact le_trans hHM (h2 ▸ h1)

/-- **Prize ⟺ half-mass bound (up to constants).**  Given the always-true `M ≤ H` and the probed
reverse `H ≤ K·M` (`K ≈ 1`), the existence of an absolute prize constant is equivalent to the existence
of an absolute half-mass constant: a prize-shaped bound on `M` and the same-shaped bound on `H` imply
each other up to the factor `K`.  (Pointwise rung: for a single positive scale a `C` can be picked
trivially, so the genuine Big-O statement is the uniform-family form
`exists_prizeFamilyBound_iff_exists_halfMassFamilyBound` below, which fixes one constant across all `n`.) -/
theorem prizeBound_iff_halfMassBound {M H K scale : ℝ}
    (hMH : M ≤ H) (hHM : H ≤ K * M) (hK : 0 ≤ K) (hscale : 0 < scale) :
    (∃ C, M ≤ C * scale) ↔ (∃ C, H ≤ C * scale) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨K * C, halfMassBound_of_prizeBound hK hHM hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, prizeBound_of_halfMassBound hMH hC⟩

/-- Quantitative envelope form: `M` and `H` are sandwiched `M ≤ H ≤ K·M`, so they are within the
factor `K` of each other — the half-mass is an equivalent target, not merely an upper envelope. -/
theorem prize_halfMass_sandwich {M H K : ℝ} (hMH : M ≤ H) (hHM : H ≤ K * M) :
    M ≤ H ∧ H ≤ K * M :=
  ⟨hMH, hHM⟩


/-- **Normalized half-mass corridor.**  At any positive prize scale, the pointwise sandwich
`M ≤ H ≤ K·M` transfers unchanged to the normalized ratios: the half-mass Shaw-value ratio is between
the prize ratio and `K` times the prize ratio.  Thus normalization by `√(n log(p/n))` does not create a
new lever; it preserves exactly the same comparison constant. -/
theorem normalized_prize_halfMass_sandwich {M H K scale : ℝ}
    (hscale : 0 < scale) (hMH : M ≤ H) (hHM : H ≤ K * M) :
    M / scale ≤ H / scale ∧ H / scale ≤ K * (M / scale) := by
  constructor
  · exact div_le_div_of_nonneg_right hMH (le_of_lt hscale)
  · have h1 : H / scale ≤ (K * M) / scale :=
      div_le_div_of_nonneg_right hHM (le_of_lt hscale)
    have h2 : (K * M) / scale = K * (M / scale) := by ring
    exact h2 ▸ h1

/-! ## Uniform-family form: the genuine absolute-constant (Big-O) reduction

The pointwise `prizeBound_iff_halfMassBound` above is, for a single positive scale, satisfiable by a
pointwise `C` and so does NOT by itself capture an absolute Big-O constant.  The family forms below
require ONE constant across the whole admissible index family `ι` (the fields / subgroup sizes), which
IS the `prize ⟺ H(n)=O(scale)` statement. -/

/-- A uniform prize-family bound: one constant `C` for every index. -/
def prizeFamilyBound {ι : Type*} (M scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i ≤ C * scale i

/-- A uniform half-mass-family bound: one constant `C` for every index. -/
def halfMassFamilyBound {ι : Type*} (H scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, H i ≤ C * scale i


/-- A uniform normalized prize-family bound: one constant `C` bounds `M / scale` for every index.
This is the Shaw-value form of `prizeFamilyBound` when `scale = √(n log(p/n))`. -/
def normalizedPrizeFamilyBound {ι : Type*} (M scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i / scale i ≤ C

/-- A uniform normalized half-mass-family bound: one constant `C` bounds `H / scale` for every index. -/
def normalizedHalfMassFamilyBound {ι : Type*} (H scale : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, H i / scale i ≤ C

/-- **Normalized uniform-family half-mass reduction.**  Under one family-wide comparison constant
`K` and positive scales, bounded normalized prize ratios are equivalent to bounded normalized half-mass
ratios.  This is the Shaw-value version of
`exists_prizeFamilyBound_iff_exists_halfMassFamilyBound`: normalization by the prize scale preserves
the exact same door-(iv) reduction and adds no hidden analytic lever. -/
theorem exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, normalizedPrizeFamilyBound M scale C) ↔
      (∃ C, normalizedHalfMassFamilyBound H scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨K * C, fun i => ?_⟩
    have h1 : H i / scale i ≤ K * (M i / scale i) :=
      (normalized_prize_halfMass_sandwich (hscale i) (hMH i) (hHM i)).2
    have h2 : K * (M i / scale i) ≤ K * C :=
      mul_le_mul_of_nonneg_left (hC i) hK
    exact le_trans h1 h2
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    have h1 : M i / scale i ≤ H i / scale i :=
      (normalized_prize_halfMass_sandwich (hscale i) (hMH i) (hHM i)).1
    exact le_trans h1 (hC i)

/-- Raw prize-family bounds are equivalent to normalized prize-ratio bounds under positive scales,
with the same constant.  This is the scale-generic analogue of the Shaw-value normalization. -/
theorem prizeFamilyBound_iff_normalizedPrizeFamilyBound {ι : Type*} {M scale : ι → ℝ} {C : ℝ}
    (hscale : ∀ i, 0 < scale i) :
    prizeFamilyBound M scale C ↔ normalizedPrizeFamilyBound M scale C := by
  constructor
  · intro h i
    have hdiv : M i / scale i ≤ (C * scale i) / scale i :=
      div_le_div_of_nonneg_right (h i) (le_of_lt (hscale i))
    have hrewrite : (C * scale i) / scale i = C := by
      rw [mul_div_cancel_right₀ C (ne_of_gt (hscale i))]
    exact hrewrite ▸ hdiv
  · intro h i
    calc
      M i = (M i / scale i) * scale i := by
        rw [div_mul_cancel₀ (M i) (ne_of_gt (hscale i))]
      _ ≤ C * scale i := mul_le_mul_of_nonneg_right (h i) (le_of_lt (hscale i))

/-- Raw half-mass-family bounds are equivalent to normalized half-mass-ratio bounds under positive
scales, with the same constant. -/
theorem halfMassFamilyBound_iff_normalizedHalfMassFamilyBound {ι : Type*} {H scale : ι → ℝ} {C : ℝ}
    (hscale : ∀ i, 0 < scale i) :
    halfMassFamilyBound H scale C ↔ normalizedHalfMassFamilyBound H scale C := by
  constructor
  · intro h i
    have hdiv : H i / scale i ≤ (C * scale i) / scale i :=
      div_le_div_of_nonneg_right (h i) (le_of_lt (hscale i))
    have hrewrite : (C * scale i) / scale i = C := by
      rw [mul_div_cancel_right₀ C (ne_of_gt (hscale i))]
    exact hrewrite ▸ hdiv
  · intro h i
    calc
      H i = (H i / scale i) * scale i := by
        rw [div_mul_cancel₀ (H i) (ne_of_gt (hscale i))]
      _ ≤ C * scale i := mul_le_mul_of_nonneg_right (h i) (le_of_lt (hscale i))

/-- **Uniform-family door-(iv) reduction (the Big-O statement).**  Given, over the whole index family,
the always-true `M i ≤ H i` and the probed reverse `H i ≤ K · M i` with a SINGLE constant `K ≥ 0`, the
existence of an absolute prize constant is equivalent to the existence of an absolute half-mass
constant.  This is the honest `prize ⇔ H(n)=O(scale)`: one constant for all `n`, not pointwise. -/
theorem exists_prizeFamilyBound_iff_exists_halfMassFamilyBound {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, prizeFamilyBound M scale C) ↔ (∃ C, halfMassFamilyBound H scale C) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨K * C, fun i => ?_⟩
    exact halfMassBound_of_prizeBound hK (hHM i) (hC i)
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact prizeBound_of_halfMassBound (hMH i) (hC i)

end ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence

#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeBound_of_halfMassBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassBound_of_prizeBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeBound_iff_halfMassBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prize_halfMass_sandwich
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalized_prize_halfMass_sandwich
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound_iff_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound_iff_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
