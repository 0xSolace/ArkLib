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

/-- If the index factor has size at least `R^2`, then the normalized naive constant is already
at least `C * R`.  Thus in a family with unbounded `m`, the naive bridge cannot supply a uniform
constant unless some separate argument removes the index factor. -/
theorem scaledConstant_ge_linear_floor {C m R : ℝ}
    (hC : 0 ≤ C) (hm : R ^ 2 ≤ m) :
    C * R ≤ C * Real.sqrt m := by
  have hRsqrt : R ≤ Real.sqrt m := Real.le_sqrt_of_sq_le hm
  exact mul_le_mul_of_nonneg_left hRsqrt hC

/-- Family form of the lower-floor obstruction: a pointwise lower bound `R i ^ 2 ≤ m i` forces
the normalized naive constant `C i * sqrt(m i)` to dominate the growing floor `C i * R i`. -/
theorem scaledConstantFamily_ge_linear_floor {ι : Type*} {C m R : ι → ℝ}
    (hC : ∀ i, 0 ≤ C i) (hm : ∀ i, R i ^ 2 ≤ m i) :
    ∀ i, C i * R i ≤ C i * Real.sqrt (m i) := by
  intro i
  exact scaledConstant_ge_linear_floor (hC i) (hm i)

/-- Degenerate index-one endpoint: if the index factor is absent, the naive incidence scale is
exactly the prize scale.  This identifies the only endpoint where the bridge has no scale loss;
the thin prize regime has `m` growing, not `m = 1`. -/
theorem naiveIncidenceScale_eq_prizeScale_of_m_eq_one {n L : ℝ} :
    naiveIncidenceScale n 1 L = prizeScale n L := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := 1) (L := L) zero_le_one]
  simp

/-- Constant endpoint for the same degenerate case: the normalized naive constant `C√m` equals `C`
only at the index-one scale-loss-free endpoint. -/
theorem scaled_constant_eq_constant_of_m_eq_one {C : ℝ} :
    C * Real.sqrt (1 : ℝ) = C := by
  simp

/-- In the actual indexed regime `1 ≤ m`, the naive incidence scale is never smaller than the
prize scale.  Thus the bridge cannot secretly improve the Shaw normalization by the index step; it
only preserves scale at `m = 1` and overshoots afterwards. -/
theorem prizeScale_le_naiveIncidenceScale_of_one_le_m {n m L : ℝ}
    (hn : 0 < n) (hm : 1 ≤ m) (hL : 0 < L) :
    prizeScale n L ≤ naiveIncidenceScale n m L := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L)
      (le_trans zero_le_one hm)]
  have hps_nonneg : 0 ≤ prizeScale n L := le_of_lt (prizeScale_pos hn hL)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm
  nlinarith

/-- The normalized constant loss is also monotone: if the raw constant is nonnegative and `m ≥ 1`,
then the naive bridge's Shaw constant `C√m` is at least `C`.  Any constant-Shaw conclusion would
therefore need an independent argument removing this factor. -/
theorem constant_le_scaled_constant_of_one_le_m {C m : ℝ} (hC : 0 ≤ C) (hm : 1 ≤ m) :
    C ≤ C * Real.sqrt m := by
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hm
  nlinarith

/-- Strict scale form: once the index is genuinely nontrivial (`m > 1`), the naive incidence scale is
strictly larger than the prize scale.  Equality of the two scales is therefore exactly the degenerate
index-one case, not the thin prize regime. -/
theorem prizeScale_lt_naiveIncidenceScale_of_one_lt_m {n m L : ℝ}
    (hn : 0 < n) (hm : 1 < m) (hL : 0 < L) :
    prizeScale n L < naiveIncidenceScale n m L := by
  rw [naiveIncidenceScale_eq_sqrt_mul_prizeScale (n := n) (m := m) (L := L)
      (le_trans zero_le_one (le_of_lt hm))]
  have hps : 0 < prizeScale n L := prizeScale_pos hn hL
  have hsqrt_one : (1 : ℝ) < Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hm
  nlinarith

/-- Strict normalized-constant form: with a positive raw constant and a genuinely nontrivial index,
the normalized naive Shaw constant is strictly larger than the desired constant.  Thus the index
factor is a real loss, not just a weak inequality, throughout the thin indexed regime. -/
theorem constant_lt_scaled_constant_of_one_lt_m {C m : ℝ} (hC : 0 < C) (hm : 1 < m) :
    C < C * Real.sqrt m := by
  have hsqrt_one : (1 : ℝ) < Real.sqrt m := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hm
  nlinarith

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
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstant_ge_linear_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstantFamily_ge_linear_floor
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_prizeScale_of_m_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaled_constant_eq_constant_of_m_eq_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_le_naiveIncidenceScale_of_one_le_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_le_scaled_constant_of_one_le_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_of_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_of_one_lt_m
#print axioms ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.shawValueFamilyBound_of_naiveIncidenceBound
