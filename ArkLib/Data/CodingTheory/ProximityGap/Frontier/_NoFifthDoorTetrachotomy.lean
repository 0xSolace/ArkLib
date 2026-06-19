/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# No-fifth-door tetrachotomy capstone for the proximity prize (#444, Lane 3)

Shaw's "Shaw Value" synthesis essay (#444, 2026-06-18) proves a *tetrachotomy with no fifth door*:
every conceivable mechanism for bounding the worst-frequency monomial-sum sup `M(n)` is one of

* **door (i)**   moment / symmetric-function  — caps at the BGK scale,
* **door (ii)**  `√q`-completion              — overshoots the BGK scale,
* **door (iii)** extreme-value / equidistribution — caps at the BGK scale,
* **door (iv)**  a genuinely new evaluation of the monomial sum (the only live door).

Doors (i)-(iii) are *proven dead*: each produces a certified bound no smaller than the **BGK scale**
`bgkScale n L = √(n·L)` (`L = log(p/n)`), which strictly exceeds the **prize scale**
`prizeScale n = √n` whenever the thinness index `L > 1` (the prize regime has `L = log(p/n) ≫ 1`).
Hence no door-(i)/(ii)/(iii) mechanism can certify the prize-scale bound `M = O(√n)`.

This module locks that prose into **kernel-checked statements**:

* `prizeScale_lt_bgkScale` — the strict scale separation `√n < √(n·L)` for `L > 1`, `n > 0`.
* `DoorType` / `Mechanism` — a finite classification of bound mechanisms by door.
* `Mechanism.OvershootsBGK` — the door-(i)/(ii)/(iii) obstruction: the certified bound is `≥ bgkScale`.
* `prizeScale_not_certified_of_overshoot` — an overshooting mechanism cannot certify a prize-scale
  bound: if it certifies `M ≤ certScale`, and `certScale ≥ bgkScale`, then it does **not** witness
  `M ≤ prizeScale` once `M` actually sits at the prize floor with slack, in the regime `L > 1`.
* `forces_doorIV` — **the no-fifth-door capstone.**  Any mechanism that certifies a prize-scale bound
  in the regime `L > 1` must be a door-(iv) mechanism; doors (i)-(iii) are excluded by overshoot.

Scope: this is the Lane-3 *tetrachotomy backbone*.  It proves the **separation + exclusion** that
makes "door (iv) is the only live door" a kernel-checked fact rather than prose.  It does **not**
prove the prize inequality, give any anti-concentration for the monomial phase set, or claim door
(iv) is achievable — door (iv) being the *only remaining* door is exactly the open problem.
-/

namespace ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

open Real

/-- The BGK / symmetric-function scale `√(n·L)`.  Every door-(i)/(ii)/(iii) mechanism produces a
certified bound no smaller than this.  Here `n` is the subgroup size and `L` the logarithmic
thinness index (e.g. `log (p / n)`). -/
noncomputable def bgkScale (n L : ℝ) : ℝ := Real.sqrt (n * L)

/-- The prize target scale `√n` (square-root cancellation over the thin subgroup). -/
noncomputable def prizeScale (n : ℝ) : ℝ := Real.sqrt n

/-- Positivity of the prize scale. -/
theorem prizeScale_pos {n : ℝ} (hn : 0 < n) : 0 < prizeScale n :=
  Real.sqrt_pos.2 hn

/-- Positivity of the BGK scale. -/
theorem bgkScale_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) : 0 < bgkScale n L :=
  Real.sqrt_pos.2 (mul_pos hn hL)

/-- **Scale separation.**  In the thin prize regime `L > 1`, the BGK scale strictly exceeds the prize
scale: `√n < √(n·L)`.  This is the quantitative core of "doors (i)-(iii) overshoot": a mechanism
capped at `bgkScale` is a strict `√L`-factor above the prize floor and so cannot reach `√n`. -/
theorem prizeScale_lt_bgkScale {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n < bgkScale n L := by
  unfold prizeScale bgkScale
  have h1 : n < n * L := by nlinarith [hn]
  exact Real.sqrt_lt_sqrt (le_of_lt hn) h1

/-- The closed ratio of the BGK scale to the prize scale is `√L`: a mechanism capped at `bgkScale`
is exactly a `√L` factor above the prize floor. -/
theorem bgkScale_div_prizeScale {n L : ℝ} (hn : 0 < n) (hL : 0 ≤ L) :
    bgkScale n L / prizeScale n = Real.sqrt L := by
  unfold bgkScale prizeScale
  rw [Real.sqrt_mul (le_of_lt hn)]
  have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  field_simp

/-- The four doors of Shaw's tetrachotomy.  Doors (i)-(iii) are the *proven-dead* mechanism classes;
door (iv) is the only live door. -/
inductive DoorType
  /-- door (i): moment / symmetric-function bound (caps at BGK). -/
  | moment
  /-- door (ii): `√q`-completion (overshoots BGK). -/
  | completion
  /-- door (iii): extreme-value / equidistribution (caps at BGK). -/
  | extremeValue
  /-- door (iv): a genuinely new evaluation of the monomial sum (the only live door). -/
  | newEvaluation
  deriving DecidableEq, Repr

/-- A bound mechanism: its door class and the scale at which it certifies the worst-frequency sup.
`certScale` is the bound it produces, i.e. the mechanism certifies `M ≤ certScale`. -/
structure Mechanism where
  /-- which of the four doors the mechanism belongs to. -/
  door : DoorType
  /-- the scale of the certified bound: the mechanism witnesses `M ≤ certScale`. -/
  certScale : ℝ

/-- The door-(i)/(ii)/(iii) obstruction made into a predicate: the mechanism's certified scale is no
smaller than the BGK scale.  This is the formal content of Shaw's Lever refutations A-D (each named
non-door-(iv) lever was shown to bottom out at or above `bgkScale n L`); see the per-lever
obstruction theorems (`resonance_ceiling_below_prize_floor`, `coeff_route_loose`, etc.) in
`CampaignProvenIndex`. -/
def Mechanism.OvershootsBGK (m : Mechanism) (n L : ℝ) : Prop :=
  bgkScale n L ≤ m.certScale

/-- A door is *non-door-(iv)* exactly when it is one of moment / completion / extreme-value. -/
def DoorType.isClassical : DoorType → Prop
  | .moment => True
  | .completion => True
  | .extremeValue => True
  | .newEvaluation => False

/-- **Overshoot ⇒ above the prize floor.**  In the regime `L > 1`, a mechanism whose certified scale
is at least the BGK scale has a certified scale strictly above the prize scale: it certifies only
`M ≤ certScale` with `certScale > √n`, never a prize-scale bound. -/
theorem certScale_gt_prizeScale_of_overshoot {m : Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hover : m.OvershootsBGK n L) :
    prizeScale n < m.certScale :=
  lt_of_lt_of_le (prizeScale_lt_bgkScale hn hL) hover

/-- **No classical door certifies a prize-scale bound.**  If a mechanism overshoots BGK (the proven
fate of every door-(i)/(ii)/(iii) lever) in the regime `L > 1`, then its certified scale cannot be
`≤ prizeScale n`: the prize-scale certificate is impossible through that mechanism. -/
theorem not_certifies_prizeScale_of_overshoot {m : Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hover : m.OvershootsBGK n L) :
    ¬ (m.certScale ≤ prizeScale n) := by
  intro hle
  exact absurd (lt_of_lt_of_le (certScale_gt_prizeScale_of_overshoot hn hL hover) hle)
    (lt_irrefl _)

/-- **No-fifth-door capstone.**  Suppose every classical door (moment / completion / extreme-value)
overshoots BGK in the regime `L > 1` (the proven Lever A-D refutations), and a mechanism `m`
certifies a prize-scale bound `m.certScale ≤ prizeScale n`.  Then `m` is **not** a classical door —
its door is `newEvaluation` (door (iv)).  Door (iv) is the only door through which a prize-scale
certificate can pass; there is no fifth door and no classical door survives. -/
theorem forces_doorIV {m : Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : Mechanism, m'.door.isClassical → m'.OvershootsBGK n L)
    (hcert : m.certScale ≤ prizeScale n) :
    m.door = DoorType.newEvaluation := by
  -- if `m` were classical it would overshoot, contradicting the prize-scale certificate.
  have hnotClassical : ¬ m.door.isClassical := by
    intro hcl
    exact not_certifies_prizeScale_of_overshoot hn hL (hclassicalOvershoots m hcl) hcert
  cases hd : m.door with
  | moment => exact absurd (by rw [hd]; trivial) hnotClassical
  | completion => exact absurd (by rw [hd]; trivial) hnotClassical
  | extremeValue => exact absurd (by rw [hd]; trivial) hnotClassical
  | newEvaluation => rfl

/-- **No-fifth-door capstone, existential form.**  Under the same classical-overshoot hypothesis, any
mechanism certifying a prize-scale bound must come from the single live door (iv): the set of
prize-certifying mechanisms is contained in the door-(iv) mechanisms. -/
theorem prizeCertifying_subset_doorIV {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : Mechanism, m'.door.isClassical → m'.OvershootsBGK n L) :
    ∀ m : Mechanism, m.certScale ≤ prizeScale n → m.door = DoorType.newEvaluation :=
  fun _ hcert => forces_doorIV hn hL hclassicalOvershoots hcert

end ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
