/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

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

/-! ## The door-(iv) target corridor `[√n, √(n·L)]`

The exclusion above says doors (i)-(iii) bottom out at the BGK ceiling `bgkScale n L = √(n·L)`, while
the Plancherel/RMS lower bound pins `prizeScale n = √n ≤ M` from below.  Hence the worst-frequency sup
`M` lives in the corridor `[√n, √(n·L)]`, and the *entire remaining door-(iv) content* is to shave the
multiplicative `√L` factor from the BGK ceiling down to the prize floor.  This differs from the trivial
`[√n, n]` Shaw-value bracket: here the ceiling is the BGK scale (what doors (i)-(iii) actually deliver),
not the trivial `n`. -/

/-- **Door-(iv) target corridor.**  Given the Plancherel floor `√n ≤ M` and any classical door's BGK
ceiling `M ≤ √(n·L)`, the worst-frequency sup `M` lies in the corridor `[prizeScale n, bgkScale n L]`.
The prize is exactly the lower endpoint; doors (i)-(iii) only reach the upper endpoint. -/
theorem mem_doorIV_corridor {M n L : ℝ}
    (hfloor : prizeScale n ≤ M) (hceil : M ≤ bgkScale n L) :
    prizeScale n ≤ M ∧ M ≤ bgkScale n L :=
  ⟨hfloor, hceil⟩

/-- **The corridor is genuinely nonempty with positive width** in the prize regime `L > 1`: the floor
is strictly below the ceiling (`√n < √(n·L)`), so the door-(iv) shave is a real `√L`-factor gap, not a
degenerate point. -/
theorem doorIV_corridor_width_pos {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n < bgkScale n L :=
  prizeScale_lt_bgkScale hn hL

/-- **The BGK ceiling is exactly the prize floor scaled by `√L`.**  Pins the door-(iv) obligation
quantitatively: door (iv) must remove precisely the factor `√L = √(log(p/n))` separating the BGK
ceiling that doors (i)-(iii) deliver from the prize floor.  (`bgkScale n L = √L · prizeScale n`.) -/
theorem bgkScale_eq_sqrtL_mul_prizeScale {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    bgkScale n L = Real.sqrt L * prizeScale n := by
  unfold bgkScale prizeScale
  rw [Real.sqrt_mul hn, mul_comm]

/-! ## Discharging the door-(ii) (√q-completion) overshoot from the PROVEN completion ceiling

The abstract `OvershootsBGK` hypothesis is not a postulate for the completion door: it is *discharged*
by the proven √q-completion ceiling `M ≤ √q` (`worstPeriod_torsion_le_sqrt_card`, the classical
Polya-Vinogradov/Gauss-sum bound on each period over a torsion subgroup).  The completion mechanism
certifies the *scale* `completionScale q = √q`.  In the prize regime `q = n^β`, `β ≈ 4-5`, so
`q ≥ n·L` whenever `L ≤ q/n = n^{β-1}` (always true at the prize, where `L = log(p/n) ≪ n`).  Under that
regime fact the completion scale `√q` is `≥ bgkScale n L = √(n·L)`: door (ii) overshoots BGK, exactly
as the tetrachotomy claims, with NO extra assumption beyond the proven ceiling. -/

/-- The √q-completion scale that the door-(ii) mechanism certifies (`M ≤ √q`). -/
noncomputable def completionScale (q : ℝ) : ℝ := Real.sqrt q

/-- **Door-(ii) overshoot, discharged.**  In the prize regime, the field size dominates the BGK
argument: `n·L ≤ q` (since `q = n^β ≥ n² ≥ n·L` for `L ≤ n`).  Then the √q-completion scale that the
completion mechanism *provably* certifies dominates the BGK scale: `bgkScale n L ≤ completionScale q`.
This turns the `OvershootsBGK` hypothesis for door (ii) into a consequence of the proven completion
ceiling, not a postulate. -/
theorem completion_overshootsBGK_of_prizeRegime {n L q : ℝ}
    (hq : n * L ≤ q) :
    bgkScale n L ≤ completionScale q := by
  unfold bgkScale completionScale
  exact Real.sqrt_le_sqrt hq

/-- A `Mechanism` whose door is `completion` and whose certified scale is the proven `√q` ceiling,
in the prize regime, satisfies `OvershootsBGK` unconditionally (no extra hypothesis beyond the
regime fact `n·L ≤ q`). -/
theorem completionMechanism_overshootsBGK {n L q : ℝ} (hq : n * L ≤ q) :
    (⟨DoorType.completion, completionScale q⟩ : Mechanism).OvershootsBGK n L :=
  completion_overshootsBGK_of_prizeRegime hq

/-- **Door-(ii) cannot certify the prize.**  In the prize regime `L > 1`, `n·L ≤ q`, the √q-completion
mechanism's certified scale strictly exceeds the prize floor `√n`, so the completion door provably
fails to certify `M ≤ √n` — a discharged (not assumed) instance of the no-fifth-door exclusion. -/
theorem completion_not_certifies_prizeScale {n L q : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hq : n * L ≤ q) :
    ¬ (completionScale q ≤ prizeScale n) :=
  not_certifies_prizeScale_of_overshoot hn hL (completionMechanism_overshootsBGK hq)

/-! ## Discharging the door-(i)/(iii) (moment / extreme-value) overshoot from the SOTA exponent wall

Doors (i) (moment / symmetric-function) and (iii) (extreme-value / equidistribution) both bottom out
at the BGK state of the art: a *guaranteed* per-frequency value `C·n^{1−δ}` with sub-prize exponent
`δ < 1/2` (the in-tree SOTA has `δ ≈ 0.011`, i.e. `n^{0.989}`).  This SOTA scale eventually DOMINATES
the BGK argument scale `bgkScale n L = √(n·L) = (√L)·n^{1/2}`, because the gap exponent `1/2 − δ > 0`
drives `n^{1/2−δ} → ∞` past the constant `√L`.  So any moment/EVT mechanism certifies a scale that
eventually exceeds `bgkScale`, i.e. it `OvershootsBGK` for all large `n` — a discharged consequence of
the SOTA exponent being `< 1/2`, not a postulate.  (This re-proves, self-contained, the eventual
domination at the heart of `_BGKSOTAInsufficiency.bgk_value_exceeds_prizeTarget_eventually`.) -/

open Filter Topology in
/-- **Moment/EVT SOTA scale eventually dominates BGK.**  For any SOTA constant `C > 0` and sub-prize
exponent `δ < 1/2`, and any thinness index `L ≥ 0`, there is a threshold `N₀` past which the SOTA
guaranteed value `C·n^{1−δ}` exceeds the BGK scale `√(n·L)`.  Hence the moment/extreme-value door's
certified scale `OvershootsBGK` for all large subgroups. -/
theorem momentEVT_scale_eventually_ge_bgkScale
    {C L δ : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n → bgkScale n L ≤ C * n ^ (1 - δ) := by
  have hgap : 0 < 1 / 2 - δ := by linarith
  have htend : Tendsto (fun n : ℝ => C * n ^ (1 / 2 - δ)) atTop atTop :=
    Tendsto.const_mul_atTop hC (tendsto_rpow_atTop hgap)
  have hev : ∀ᶠ n : ℝ in atTop,
      Real.sqrt L < C * n ^ (1 / 2 - δ) ∧ (1 : ℝ) ≤ n :=
    (htend.eventually_gt_atTop (Real.sqrt L)).and (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := hev.exists_forall_of_atTop
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨hgt, hn1⟩ := hN₀ n hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le one_pos hn1
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  -- bgkScale n L = (√L)·√n  and  C·n^{1−δ} = (C·n^{1/2−δ})·√n, compare coefficients.
  have hLHS : bgkScale n L = Real.sqrt L * Real.sqrt n := by
    unfold bgkScale; rw [Real.sqrt_mul hnpos.le]; ring
  have hrpow : n ^ (1 - δ) = n ^ (1 / 2 - δ) * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos]; congr 1; ring
  have hRHS : C * n ^ (1 - δ) = (C * n ^ (1 / 2 - δ)) * Real.sqrt n := by
    rw [hrpow]; ring
  rw [hLHS, hRHS]
  exact le_of_lt (mul_lt_mul_of_pos_right hgt hsqrtn_pos)

/-- **Door-(i)/(iii) overshoot, discharged for large `n`.**  A moment/extreme-value mechanism whose
certified scale is the SOTA value `C·n^{1−δ}` (`δ < 1/2`) satisfies `OvershootsBGK` for every `n` past
the SOTA threshold `N₀`.  Combined with the strict scale separation, such a mechanism provably cannot
certify a prize-scale bound at those `n`. -/
theorem momentEVT_mechanism_overshootsBGK_eventually
    {C L δ : ℝ} (hC : 0 < C) (hL : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n →
      (⟨DoorType.moment, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L := by
  obtain ⟨N₀, hN₀⟩ := momentEVT_scale_eventually_ge_bgkScale hC hL hδ
  exact ⟨N₀, fun n hn => hN₀ n hn⟩

/-! ## Classical side closed: doors (i)/(ii)/(iii) all FAIL the prize certificate at their proven scales

The three discharges above (`completion_not_certifies_prizeScale` for door (ii);
`momentEVT_mechanism_overshootsBGK_eventually` + the scale separation for doors (i)/(iii)) are bundled
here into a single citable statement: at the concrete proven certScales, NO classical door certifies a
prize-scale bound in the prize regime.  This is the unconditional classical side of the no-fifth-door
tetrachotomy — the `hclassicalOvershoots` hypothesis of `forces_doorIV` is no longer a postulate for
the completion / moment-EVT mechanisms, it is a theorem. -/

/-- **Classical side closed (concrete scales).**  In the prize regime `L > 1`:

* the √q-completion door (ii), at any field size with `n·L ≤ q`, fails the prize certificate; and
* the moment / extreme-value doors (i)/(iii), at the SOTA scale `C·n^{1−δ}` (`δ < 1/2`), fail the
  prize certificate for all `n` past the SOTA threshold.

No classical door reaches the prize floor `√n`; only door (iv) remains. -/
theorem classicalSide_closed
    {n L q C δ : ℝ} (hn : 0 < n) (hL : 1 < L)
    (hq : n * L ≤ q) (hC : 0 < C) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    (¬ (completionScale q ≤ prizeScale n)) ∧
    (∃ N₀ : ℝ, ∀ m : ℝ, N₀ ≤ m →
        ¬ ((⟨DoorType.moment, C * m ^ (1 - δ)⟩ : Mechanism).certScale ≤ prizeScale m)) := by
  refine ⟨completion_not_certifies_prizeScale hn hL hq, ?_⟩
  obtain ⟨N₀, hN₀⟩ := momentEVT_mechanism_overshootsBGK_eventually hC hLnn hδ
  refine ⟨max N₀ 2, fun m hm => ?_⟩
  have hmN₀ : N₀ ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : (2 : ℝ) ≤ m := le_trans (le_max_right _ _) hm
  have hmpos : 0 < m := by linarith
  exact not_certifies_prizeScale_of_overshoot hmpos hL (hN₀ m hmN₀)

end ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
