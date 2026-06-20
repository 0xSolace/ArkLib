/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# Door IV two-piece angular-deficit identity

The door-(iv) coherence files reduce the worst-frequency obstruction to bounding
`ρ = ‖A + B‖ / (‖A‖ + ‖B‖)` (two-piece coset-half / pair coherence).  `_DoorIVHalfMassFactorization`
records the `ρ ≤ 1` ceiling and the qualitative `ρ < 1 ⟺ ‖A+B‖ < ‖A‖+‖B‖`, and
`_DoorIVCommonRayCoherence` records that the common ray saturates (`ρ = 1`).  Neither states the
**exact** quantitative law linking the coherence deficit to the angular alignment `Re(A·conj B)`.

This file fills that gap for two complex pieces.  The key object is the **angular deficit**

`angularDeficit A B = ‖A‖·‖B‖ − Re(A·conj B) ≥ 0`,

which is `0` iff `A, B` are positively collinear (same ray) and grows with the angle between them.
The exact identity

`‖A + B‖² = (‖A‖ + ‖B‖)² − 2·angularDeficit A B`

shows the squared half-mass coherence loses *exactly* twice the angular deficit, and the
Cauchy–Schwarz nonnegativity `angularDeficit ≥ 0` is precisely the triangle inequality re-derived as
a phase-alignment statement.  Thus any anti-concentration slack `ρ < 1` in a two-piece split is
*exactly* a strictly positive angular deficit — genuine phase misalignment, not mere subdivision.

Constraint/identity lemmas only: no CORE / cancellation / completion / capacity / moment claim.
-/

namespace ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit

open Complex

/-- The angular deficit of two complex pieces: `‖A‖·‖B‖ − Re(A·conj B)`.  It is `≥ 0` by
Cauchy–Schwarz and vanishes exactly when `A, B` are positively collinear. -/
noncomputable def angularDeficit (A B : ℂ) : ℝ :=
  ‖A‖ * ‖B‖ - (A * starRingEnd ℂ B).re

/-- The real part of `A·conj B` is bounded by the product of norms (Cauchy–Schwarz for ℂ);
equivalently the angular deficit is nonnegative. -/
theorem re_mul_conj_le_norm_mul (A B : ℂ) : (A * starRingEnd ℂ B).re ≤ ‖A‖ * ‖B‖ := by
  calc (A * starRingEnd ℂ B).re ≤ ‖A * starRingEnd ℂ B‖ := Complex.re_le_norm _
    _ = ‖A‖ * ‖B‖ := by rw [Complex.norm_mul, Complex.norm_conj]

/-- The angular deficit is nonnegative. -/
theorem angularDeficit_nonneg (A B : ℂ) : 0 ≤ angularDeficit A B := by
  unfold angularDeficit
  linarith [re_mul_conj_le_norm_mul A B]

/-- The squared-norm expansion of a complex sum: `‖A+B‖² = ‖A‖² + ‖B‖² + 2·Re(A·conj B)`. -/
theorem norm_add_sq (A B : ℂ) :
    ‖A + B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 + 2 * (A * starRingEnd ℂ B).re := by
  have hA : ‖A‖ ^ 2 = Complex.normSq A := (Complex.normSq_eq_norm_sq A).symm
  have hB : ‖B‖ ^ 2 = Complex.normSq B := (Complex.normSq_eq_norm_sq B).symm
  have hAB : ‖A + B‖ ^ 2 = Complex.normSq (A + B) := (Complex.normSq_eq_norm_sq (A + B)).symm
  rw [hA, hB, hAB, Complex.normSq_add]

/-- **Exact two-piece angular-deficit identity.**
`‖A + B‖² = (‖A‖ + ‖B‖)² − 2·angularDeficit A B`.

The squared half-mass coherence loses exactly twice the angular deficit.  Combined with
`angularDeficit_nonneg` this *is* the triangle inequality, now read as a phase-alignment statement:
the only loss in `‖A+B‖` vs the half-mass `‖A‖+‖B‖` is the angular misalignment of the two pieces. -/
theorem norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit (A B : ℂ) :
    ‖A + B‖ ^ 2 = (‖A‖ + ‖B‖) ^ 2 - 2 * angularDeficit A B := by
  rw [norm_add_sq, angularDeficit]
  ring

/-- A strict coherence deficit at the squared level (`‖A+B‖² < (‖A‖+‖B‖)²`) is equivalent to a
strictly positive angular deficit.  So two-piece anti-concentration slack is *exactly* genuine
angular misalignment. -/
theorem norm_add_sq_lt_halfMass_sq_iff_angularDeficit_pos (A B : ℂ) :
    ‖A + B‖ ^ 2 < (‖A‖ + ‖B‖) ^ 2 ↔ 0 < angularDeficit A B := by
  rw [norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Zero angular deficit forces saturation at the squared level (`‖A+B‖² = (‖A‖+‖B‖)²`).  This is
the two-piece common-ray saturation, matching `_DoorIVCommonRayCoherence`. -/
theorem norm_add_sq_eq_halfMass_sq_of_angularDeficit_zero {A B : ℂ}
    (h : angularDeficit A B = 0) : ‖A + B‖ ^ 2 = (‖A‖ + ‖B‖) ^ 2 := by
  rw [norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit, h]; ring

/-- Quantitative lower bound on the squared deficit from an angular-deficit floor: if
`angularDeficit A B ≥ δ` then `‖A+B‖² ≤ (‖A‖+‖B‖)² − 2δ`.  A two-piece coherence proof that
claims a drop must therefore exhibit at least the matching angular misalignment. -/
theorem norm_add_sq_le_halfMass_sq_sub_two_mul_of_angularDeficit_ge {A B : ℂ} {δ : ℝ}
    (h : δ ≤ angularDeficit A B) :
    ‖A + B‖ ^ 2 ≤ (‖A‖ + ‖B‖) ^ 2 - 2 * δ := by
  rw [norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit]
  linarith

/-! ### Multi-piece (list) angular deficit

The worst-frequency coset sum is a sum of many complex pieces, not just two.  The two-piece identity
lifts to the full list: `‖Σ z_i‖²` loses, relative to the squared half-mass `(Σ‖z_i‖)²`, exactly
twice the **total pairwise angular deficit** `Σ_{i<j} angularDeficit(z_i, z_j) ≥ 0`.  We build this
recursively via the per-element cross deficit against the rest of the list. -/

/-- Re of `z · conj(·)` is additive over a finite list (linearity of the alignment form). -/
theorem re_mul_conj_list_sum (z : ℂ) (zs : List ℂ) :
    (z * starRingEnd ℂ zs.sum).re = (zs.map (fun w => (z * starRingEnd ℂ w).re)).sum := by
  induction zs with
  | nil => simp
  | cons w zs ih =>
      simp only [List.sum_cons, map_add, mul_add, Complex.add_re, List.map_cons, ih]

/-- Cons expansion of the squared norm of a list sum:
`‖z + Σzs‖² = ‖z‖² + ‖Σzs‖² + 2·Σ_{w∈zs} Re(z·conj w)`. -/
theorem norm_cons_sum_sq (z : ℂ) (zs : List ℂ) :
    ‖z + zs.sum‖ ^ 2
      = ‖z‖ ^ 2 + ‖zs.sum‖ ^ 2 + 2 * (zs.map (fun w => (z * starRingEnd ℂ w).re)).sum := by
  rw [norm_add_sq, re_mul_conj_list_sum]

/-- Per-element **cross deficit** of `z` against a list: `Σ_{w∈zs}(‖z‖‖w‖ − Re(z·conj w)) ≥ 0`. -/
noncomputable def crossDeficit (z : ℂ) (zs : List ℂ) : ℝ :=
  (zs.map (fun w => angularDeficit z w)).sum

/-- The cross deficit is nonnegative (each summand is a pairwise angular deficit). -/
theorem crossDeficit_nonneg (z : ℂ) (zs : List ℂ) : 0 ≤ crossDeficit z zs := by
  unfold crossDeficit
  induction zs with
  | nil => simp
  | cons w zs ih =>
      simp only [List.map_cons, List.sum_cons]
      have := angularDeficit_nonneg z w
      linarith

/-- **Total pairwise angular deficit** of a list, accumulated as each new head is paired against the
remaining tail.  `totalPairDeficit zs = Σ_{i<j} angularDeficit(z_i, z_j) ≥ 0`. -/
noncomputable def totalPairDeficit : List ℂ → ℝ
  | [] => 0
  | z :: zs => crossDeficit z zs + totalPairDeficit zs

/-- Total pairwise angular deficit is nonnegative. -/
theorem totalPairDeficit_nonneg (zs : List ℂ) : 0 ≤ totalPairDeficit zs := by
  induction zs with
  | nil => simp [totalPairDeficit]
  | cons z zs ih =>
      unfold totalPairDeficit
      have := crossDeficit_nonneg z zs
      linarith

/-- `L¹` mass of a list: `Σ ‖z_i‖`. -/
noncomputable def l1Mass (zs : List ℂ) : ℝ := (zs.map norm).sum

/-- Cons expansion of the cross deficit against the squared `L¹`:
`(‖z‖ + l1Mass zs)² = ‖z‖² + l1Mass zs² + 2‖z‖·l1Mass zs`, and the cross deficit pairs `z` with the
sum-of-norms, so `2(‖z‖·l1Mass zs) − 2·crossDeficit z zs = 2·Σ Re(z·conj w)`. -/
theorem two_mul_crossDeficit_eq (z : ℂ) (zs : List ℂ) :
    2 * crossDeficit z zs
      = 2 * (‖z‖ * l1Mass zs) - 2 * (zs.map (fun w => (z * starRingEnd ℂ w).re)).sum := by
  unfold crossDeficit l1Mass angularDeficit
  induction zs with
  | nil => simp
  | cons w zs ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      have hz : ‖z‖ * (‖w‖ + (zs.map norm).sum) = ‖z‖ * ‖w‖ + ‖z‖ * (zs.map norm).sum := by ring
      nlinarith [ih]

/-- **Exact multi-piece angular-deficit identity.**
`‖Σ z_i‖² = (Σ‖z_i‖)² − 2·totalPairDeficit zs`.

The squared coherence of the worst-frequency coset sum loses, relative to the squared `L¹` half-mass,
exactly twice the total pairwise angular deficit — a sum of nonnegative phase-misalignment terms.
This is the genuine many-piece object: an anti-concentration drop is exactly an accumulation of
pairwise phase misalignments, never available from mere subdivision (which adds zero-deficit collinear
pieces). -/
theorem norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit (zs : List ℂ) :
    ‖zs.sum‖ ^ 2 = (l1Mass zs) ^ 2 - 2 * totalPairDeficit zs := by
  induction zs with
  | nil => simp [l1Mass, totalPairDeficit]
  | cons z zs ih =>
      have hcons : ‖(z :: zs).sum‖ ^ 2 = ‖z + zs.sum‖ ^ 2 := by simp [List.sum_cons]
      rw [hcons, norm_cons_sum_sq]
      unfold totalPairDeficit l1Mass
      have hl1 : ((z :: zs).map norm).sum = ‖z‖ + (zs.map norm).sum := by
        simp [List.map_cons, List.sum_cons]
      rw [hl1]
      have hcross := two_mul_crossDeficit_eq z zs
      unfold l1Mass at hcross ih
      -- goal: ‖z‖² + ‖zs.sum‖² + 2*S = (‖z‖ + L1)² - 2*(crossDeficit z zs + totalPairDeficit zs)
      -- ih: ‖zs.sum‖² = L1² - 2*totalPairDeficit zs ; hcross: 2*crossDeficit = 2*(‖z‖*L1) - 2*S
      have hsq : (‖z‖ + (zs.map norm).sum) ^ 2
          = ‖z‖ ^ 2 + (zs.map norm).sum ^ 2 + 2 * (‖z‖ * (zs.map norm).sum) := by ring
      rw [hsq]
      linarith [ih, hcross]

/-- The squared resultant norm is at most the squared `L¹` mass (multi-piece triangle inequality
recovered from the total pairwise angular deficit being nonnegative). -/
theorem norm_sum_sq_le_l1Mass_sq (zs : List ℂ) : ‖zs.sum‖ ^ 2 ≤ (l1Mass zs) ^ 2 := by
  rw [norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit]
  have := totalPairDeficit_nonneg zs
  linarith

/-! ### Door-(iv) reduction: the prize is exactly a total-angular-deficit lower bound

The worst-frequency obstruction asks for a *small* resultant `‖Σ z_i‖` (the √-cancellation).  The
exact multi-piece identity turns any squared-resultant ceiling into an exactly equivalent lower bound
on the total pairwise angular deficit: a small resultant **is** a large accumulated phase
misalignment.  This pinpoints the arithmetic input door-(iv) needs — a near-extremal total angular
deficit — with no slack. -/

/-- **Exact threshold reduction.**  For any ceiling `T`, the squared resultant satisfies
`‖Σ z_i‖² ≤ T` **iff** the total pairwise angular deficit satisfies
`totalPairDeficit zs ≥ ((l1Mass zs)² − T)/2`.  Thus a √-cancellation ceiling on the coset sum is
exactly a lower bound on the accumulated pairwise phase misalignment. -/
theorem norm_sum_sq_le_iff_totalPairDeficit_ge (zs : List ℂ) (T : ℝ) :
    ‖zs.sum‖ ^ 2 ≤ T ↔ ((l1Mass zs) ^ 2 - T) / 2 ≤ totalPairDeficit zs := by
  rw [norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Strict form of the threshold reduction. -/
theorem norm_sum_sq_lt_iff_totalPairDeficit_gt (zs : List ℂ) (T : ℝ) :
    ‖zs.sum‖ ^ 2 < T ↔ ((l1Mass zs) ^ 2 - T) / 2 < totalPairDeficit zs := by
  rw [norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- `L¹` mass is nonnegative. -/
theorem l1Mass_nonneg (zs : List ℂ) : 0 ≤ l1Mass zs := by
  unfold l1Mass
  induction zs with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons, List.sum_cons]; have := norm_nonneg z; linarith

/-- **Sharp coherence-form (un-squared) bound.**  `‖Σ z_i‖·L¹ ≤ (L¹)² − totalPairDeficit zs`.

Dividing by `L¹² > 0` this is exactly `ρ ≤ 1 − totalPairDeficit/L¹²`: a sqrt-free, division-free
upper bound on the coherence itself (not its square) from the total pairwise angular deficit.  A
coherence drop of `ε` therefore requires total angular deficit `≥ ε·L¹²`.  The slack is exactly
`(L¹ − ‖Σ z_i‖)²/2 ≥ 0`, so the bound is tight at collinearity. -/
theorem norm_sum_mul_l1Mass_le_l1Mass_sq_sub_totalPairDeficit (zs : List ℂ) :
    ‖zs.sum‖ * l1Mass zs ≤ (l1Mass zs) ^ 2 - totalPairDeficit zs := by
  have hid := norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit zs
  -- 2·(L¹² − D − ‖Σ‖·L¹) = L¹² + ‖Σ‖² − 2‖Σ‖L¹ = (L¹ − ‖Σ‖)² ≥ 0, using ‖Σ‖² = L¹² − 2D.
  nlinarith [sq_nonneg (l1Mass zs - ‖zs.sum‖), hid, norm_nonneg zs.sum, l1Mass_nonneg zs]

/-! ### Dual cap on the angular deficit (the L²-method ceiling)

The angular deficit is also bounded *above*: `angularDeficit z w ≤ 2‖z‖‖w‖` (since
`Re(z·conj w) ≥ −‖z‖‖w‖`, antipodal saturation).  Summed, this caps the total pairwise deficit and
hence gives a coherence *floor* — but for many pieces the floor is the trivial/Plancherel one and
cannot reach √-cancellation by itself.  Recording the cap pins precisely why a second-moment / L²
argument alone tops out: it controls `totalPairDeficit` only up to the antipodal bound. -/

/-- The real alignment is bounded below by minus the norm product: `−‖z‖‖w‖ ≤ Re(z·conj w)`. -/
theorem neg_norm_mul_le_re_mul_conj (z w : ℂ) : -(‖z‖ * ‖w‖) ≤ (z * starRingEnd ℂ w).re := by
  have hb : |(z * starRingEnd ℂ w).re| ≤ ‖z * starRingEnd ℂ w‖ := Complex.abs_re_le_norm _
  rw [Complex.norm_mul, Complex.norm_conj] at hb
  exact (abs_le.1 hb).1

/-- **Per-pair angular-deficit cap.**  `angularDeficit z w ≤ 2‖z‖‖w‖`, saturated at antipodal
pieces (`w = -t·z`).  This is the dual of `angularDeficit_nonneg`. -/
theorem angularDeficit_le_two_mul_norm_mul (z w : ℂ) :
    angularDeficit z w ≤ 2 * (‖z‖ * ‖w‖) := by
  unfold angularDeficit
  linarith [neg_norm_mul_le_re_mul_conj z w]

/-! ### Capstone: no-slack characterization

The whole angular-deficit story collapses to one kernel-checked equivalence: the worst-frequency
coset sum saturates the `L¹` half-mass (`‖Σ z_i‖² = (L¹)²`, i.e. coherence `ρ = 1`, no
anti-concentration slack) **iff** the total pairwise angular deficit is zero, and it has strict slack
iff that deficit is strictly positive.  Mere subdivision (adding collinear, zero-deficit pieces) never
moves the deficit, so it never creates slack. -/

/-- **No-slack iff zero total deficit.**  `‖Σ z_i‖² = (L¹)² ↔ totalPairDeficit zs = 0`. -/
theorem norm_sum_sq_eq_l1Mass_sq_iff_totalPairDeficit_eq_zero (zs : List ℂ) :
    ‖zs.sum‖ ^ 2 = (l1Mass zs) ^ 2 ↔ totalPairDeficit zs = 0 := by
  rw [norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Strict slack iff positive total deficit.**  `‖Σ z_i‖² < (L¹)² ↔ 0 < totalPairDeficit zs`.
The only source of two/multi-piece anti-concentration slack is genuine accumulated pairwise phase
misalignment. -/
theorem norm_sum_sq_lt_l1Mass_sq_iff_totalPairDeficit_pos (zs : List ℂ) :
    ‖zs.sum‖ ^ 2 < (l1Mass zs) ^ 2 ↔ 0 < totalPairDeficit zs := by
  rw [norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit]
  constructor
  · intro h; linarith
  · intro h; linarith

end ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit

#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.re_mul_conj_le_norm_mul
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.angularDeficit_nonneg
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_eq_halfMass_sq_sub_two_angularDeficit
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_lt_halfMass_sq_iff_angularDeficit_pos
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_eq_halfMass_sq_of_angularDeficit_zero
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_add_sq_le_halfMass_sq_sub_two_mul_of_angularDeficit_ge
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.re_mul_conj_list_sum
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_cons_sum_sq
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.crossDeficit_nonneg
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.totalPairDeficit_nonneg
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.two_mul_crossDeficit_eq
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_le_l1Mass_sq
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_le_iff_totalPairDeficit_ge
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_lt_iff_totalPairDeficit_gt
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.l1Mass_nonneg
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_mul_l1Mass_le_l1Mass_sq_sub_totalPairDeficit
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.neg_norm_mul_le_re_mul_conj
#print axioms ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.angularDeficit_le_two_mul_norm_mul
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_eq_l1Mass_sq_iff_totalPairDeficit_eq_zero
#print axioms
  ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit.norm_sum_sq_lt_l1Mass_sq_iff_totalPairDeficit_pos
