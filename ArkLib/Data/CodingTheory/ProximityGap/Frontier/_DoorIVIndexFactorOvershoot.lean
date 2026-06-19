/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door IV index-factor overshoot: the naive incidence scale is `sqrt m` too large

This file formalizes the door-(iv) bookkeeping behind the current `hfloor` obstruction in
`PrizeConditionalPinCapstone`: the available naive `M -> epsMCA` incidence bridge carries an index
factor.  In Shaw-value units, replacing the prize scale `sqrt(n L)` by the naive incidence scale
`sqrt(n m L)` multiplies the normalized target by exactly `sqrt m`.

Scope: this is a Lane-2/Lane-3 constraint lemma.  It does **not** prove a character-sum bound, does
not discharge `hfloor`, and does not assert any cancellation.  It only records, axiom-clean, the
arithmetic loss that makes an L-infinity `M(n)` estimate insufficient for the realized-incidence
floor unless one also removes the index factor by a genuinely new door-(iv) argument.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- The naive incidence scale after the index `m = (p-1)/n` has entered the bridge:
`sqrt(n * m * L)`, rather than the prize scale `sqrt(n * L)`. -/
noncomputable def naiveIncidenceScale (n m L : ℝ) : ℝ :=
  Real.sqrt (n * m * L)

/-- Closed-form comparison of scales: the naive incidence scale is exactly `sqrt m` times the
prize scale.  This is the formal version of the observed `sqrt m` index-factor overshoot. -/
theorem naiveIncidenceScale_eq_sqrt_mul_prizeScale {n m L : ℝ}
    (hm : 0 ≤ m) :
    naiveIncidenceScale n m L = Real.sqrt m * prizeScale n L := by
  unfold naiveIncidenceScale prizeScale
  rw [show n * m * L = m * (n * L) by ring]
  rw [Real.sqrt_mul hm]

/-- Ratio form: in the positive thin regime, dividing the naive incidence scale by the prize scale
leaves exactly the index factor `sqrt m`. -/
theorem naiveIncidenceScale_div_prizeScale_eq_sqrt {n m L : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hL : 0 < L) :
    naiveIncidenceScale n m L / prizeScale n L = Real.sqrt m := by
  have hps : prizeScale n L ≠ 0 := ne_of_gt (prizeScale_pos hn hL)
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L) (le_of_lt hm)]
  field_simp [hps]

/-- Shaw-value normalization of the naive bridge: a raw bound at the naive incidence scale is exactly
a Shaw-value bound with constant multiplied by `sqrt m`.  Thus any route that only reaches
`sqrt(n*m*L)` has already lost the index factor and cannot be a constant-Shaw/prize bound for
unbounded `m`. -/
theorem naiveIncidenceBound_iff_shawValue_le_scaled {M C n m L : ℝ}
    (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 < L) :
    M ≤ C * naiveIncidenceScale n m L ↔
      shawValue M n L ≤ C * Real.sqrt m := by
  have hs : 0 < prizeScale n L := prizeScale_pos hn hL
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L) hm]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (prizeBound_iff_shawValue_le (M := M) (C := C * Real.sqrt m) (n := n) (L := L) hs)

/-- Uniform-family form of the same obstruction: pointwise naive incidence bounds normalize to a
Shaw-value family bound whose pointwise constant is multiplied by `sqrt(m i)`.  This is only scale
bookkeeping; the analytic loss remains in the hypotheses. -/
theorem shawValueFamilyBound_of_naiveIncidenceBound {ι : Type*}
    {M n m L C : ι → ℝ}
    (hn : ∀ i, 0 < n i) (hm : ∀ i, 0 ≤ m i) (hL : ∀ i, 0 < L i)
    (hraw : ∀ i, M i ≤ C i * naiveIncidenceScale (n i) (m i) (L i)) :
    ∀ i, shawValue (M i) (n i) (L i) ≤ C i * Real.sqrt (m i) := by
  intro i
  exact (naiveIncidenceBound_iff_shawValue_le_scaled
    (M := M i) (C := C i) (n := n i) (m := m i) (L := L i)
    (hn i) (hm i) (hL i)).1 (hraw i)

end ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot

#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_sqrt_mul_prizeScale
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_div_prizeScale_eq_sqrt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceBound_iff_shawValue_le_scaled
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.shawValueFamilyBound_of_naiveIncidenceBound
