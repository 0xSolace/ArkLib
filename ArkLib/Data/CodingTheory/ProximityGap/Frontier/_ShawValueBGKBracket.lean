/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The SHARP (BGK-ceiling) Shaw-value bracket `[1/√L, 1]` (#444, Lane 2)

`ShawValueCapstone.lean` proves the Shaw-value bracket using the **trivial** ceiling `M ≤ n`:
`shawValue M n L ∈ [1/√L, √(n/L)]`, a bracket of *multiplicative width `√n`*
(`bracket_width_eq_sqrt`).

The no-fifth-door tetrachotomy (`_NoFifthDoorTetrachotomy.lean`) shows that *doors (i)-(iii) actually
deliver the much smaller BGK ceiling* `M ≤ √(n·L)`, not the trivial `n`.  In the Shaw normalization
`shawValue M n L = M / √(n·L)` (the same `prizeScale n L = √(n·L)`), that BGK ceiling is exactly
`shawValue ≤ 1`.  So the *real* Shaw-value corridor that doors (i)-(iii) bound is the **sharp**
bracket `[1/√L, 1]`, of multiplicative width only `√L` — a `√(n/L)`-factor improvement on the trivial
bracket.

This module records that sharp bracket and its closed-form endpoints and width.  It is pure
normalization bookkeeping built on the proven Plancherel floor (`shawValue_floor_of_plancherel_floor`)
and the proven BGK ceiling fact `M ≤ √(n·L)` (the door-(i)/(ii)/(iii) certified scale).  It asserts
**no** cancellation, anti-concentration, or capacity estimate: the open prize is exactly to collapse
this `√L`-wide normalized bracket down to an absolute constant.  In this normalization the prize
bound `M ≤ C·√n` reads `shawValue ≤ C/√L` (the lower endpoint up to the constant `C`), so the open
job is to push `shawValue` from its BGK ceiling `1` down to the floor scale `1/√L`.
-/

namespace ArkLib.ProximityGap.Frontier.ShawValueBGKBracket

open ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- **Sharp upper bracket endpoint (BGK ceiling).**  The door-(i)/(ii)/(iii) certified ceiling
`M ≤ √(n·L)` is, in the Shaw normalization, exactly `shawValue M n L ≤ 1`.  (Here `√(n·L) =
prizeScale n L`, the normalizer itself.) -/
theorem shawValue_le_one_of_bgk_ceiling {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hceil : M ≤ prizeScale n L) :
    shawValue M n L ≤ 1 := by
  unfold shawValue
  rw [div_le_one hs]
  exact hceil

/-- **Sharp two-sided Shaw-value bracket `[1/√L, 1]`.**  Under the proven Plancherel/RMS floor
`√n ≤ M` and the proven BGK ceiling `M ≤ √(n·L)` (what doors (i)-(iii) actually deliver), the
normalized Shaw value is sandwiched in `[√n/√(n·L), 1]`.  This replaces the trivial-ceiling bracket
`[1/√L, √(n/L)]` (width `√n`) with the sharp BGK bracket (width `√L`). -/
theorem shawValue_sharp_bracket {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hfloor : Real.sqrt n ≤ M) (hceil : M ≤ prizeScale n L) :
    Real.sqrt n / prizeScale n L ≤ shawValue M n L ∧ shawValue M n L ≤ 1 :=
  ⟨shawValue_floor_of_plancherel_floor hs hfloor, shawValue_le_one_of_bgk_ceiling hs hceil⟩

/-- **Sharp bracket lower endpoint closed form.**  For `0 < n`, the sharp BGK bracket's lower endpoint
is `1/√L` (the Plancherel floor, via `floor_bracket_eq`); the upper endpoint is the literal `1` (the
BGK ceiling).  Contrast the trivial ceiling endpoint `√(n/L)`. -/
theorem shawValue_sharp_bracket_lower_eq {n L : ℝ} (hn : 0 < n) :
    Real.sqrt n / prizeScale n L = 1 / Real.sqrt L :=
  floor_bracket_eq hn

/-- **Sharp bracket width is `√L`.**  The ratio of the sharp BGK upper endpoint `1` to the lower
Plancherel endpoint `√n/√(n·L) = 1/√L` equals `√L`.  So the open prize, in Shaw-value language, is
exactly to collapse this `√L`-wide normalized bracket to an absolute constant — a `√(n/L)`-factor
sharper demand than the trivial `√n`-wide bracket of `bracket_width_eq_sqrt`. -/
theorem shawValue_sharp_bracket_width {n L : ℝ} (hn : 0 < n) :
    (1 : ℝ) / (Real.sqrt n / prizeScale n L) = Real.sqrt L := by
  rw [floor_bracket_eq hn]
  rw [one_div_one_div]

/-- **The sharp bracket is genuinely narrower than the trivial bracket** in the prize regime `n > L`:
the sharp width `√L` is strictly below the trivial width `√n` exactly when `L < n` (always true at the
prize, where `L = log(p/n) ≪ n`).  This certifies the BGK ceiling is a real improvement, not a
restatement. -/
theorem sharp_width_lt_trivial_width {n L : ℝ} (hL : 0 ≤ L) (hLn : L < n) :
    Real.sqrt L < Real.sqrt n :=
  Real.sqrt_lt_sqrt hL hLn

/-! ## The prize bound in Shaw-value units, against the BGK ceiling

The prize target is `M ≤ C·√n` (square-root cancellation over the thin subgroup) — note the `√n`, NOT
the normalizer `√(n·L)`.  In Shaw-value units that reads `shawValue ≤ C/√L`, the LOWER bracket
endpoint scaled by `C`.  Together with the BGK ceiling `shawValue ≤ 1`, this pins the door-(iv)
obligation: improve `shawValue` from the BGK ceiling `1` down to `C/√L`, i.e. a multiplicative factor
`√L/C`. -/

/-- **Prize bound in Shaw-value units.**  The prize-scale bound `M ≤ C·√n` is exactly
`shawValue M n L ≤ C/√L`.  (Contrast `ShawValueCapstone.prizeBound_iff_shawValue_le`, which normalizes
the BGK-shaped bound `M ≤ C·√(n·L)` to `shawValue ≤ C`; here the genuine prize target `√n` lands at the
lower endpoint scale `C/√L`.) -/
theorem prize_iff_shawValue_le_div_sqrtL {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    M ≤ C * Real.sqrt n ↔ shawValue M n L ≤ C / Real.sqrt L := by
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hps : 0 < prizeScale n L := prizeScale_pos hn hL
  -- prizeScale n L = √n · √L
  have hpsplit : prizeScale n L = Real.sqrt n * Real.sqrt L := by
    unfold prizeScale; rw [Real.sqrt_mul hn.le]
  unfold shawValue
  rw [hpsplit, div_le_div_iff₀ (by positivity) hsL]
  constructor
  · intro h; nlinarith [h, hsL, hsn]
  · intro h; nlinarith [h, hsL, hsn]

/-- **Door-(iv) obligation, quantified in Shaw-value units.**  In the prize regime (`0 < n`, `0 < L`),
for any `M` satisfying the proven BGK ceiling `M ≤ √(n·L)` (so `shawValue ≤ 1`): the prize bound
`M ≤ C·√n` is equivalent to pushing the Shaw value all the way down to `C/√L`.  Since `C/√L < 1`
whenever `C < √L` (the thin prize regime, `√L ≫ 1`), the open job is *strictly* below the BGK ceiling:
door (iv) must shave the Shaw value by a factor `√L/C` past what doors (i)-(iii) deliver. -/
theorem doorIV_obligation_below_bgk_ceiling {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hCL : C < Real.sqrt L) (hceil : M ≤ prizeScale n L) :
    shawValue M n L ≤ 1 ∧ (M ≤ C * Real.sqrt n ↔ shawValue M n L ≤ C / Real.sqrt L) ∧
      C / Real.sqrt L < 1 := by
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  refine ⟨shawValue_le_one_of_bgk_ceiling (prizeScale_pos hn hL) hceil,
    prize_iff_shawValue_le_div_sqrtL hn hL, ?_⟩
  rw [div_lt_one hsL]; exact hCL

/-- **Exact door-(iv) shave factor.**  The BGK ceiling in Shaw units is `1`, while the genuine-prize
threshold is `C/√L`.  Their ratio is exactly `√L/C`.  This is the kernel-checked version of the
docstring phrase "door (iv) must shave by the factor `√L/C` past the BGK ceiling"; it is pure
normalization arithmetic and contains no cancellation estimate. -/
theorem doorIV_shave_factor_eq {C L : ℝ} (hC : 0 < C) (hL : 0 < L) :
    (1 : ℝ) / (C / Real.sqrt L) = Real.sqrt L / C := by
  have hsL : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have hC0 : C ≠ 0 := ne_of_gt hC
  field_simp [hsL, hC0]

/-- **The door-(iv) shave factor is genuinely larger than one** whenever the prize constant lies
below the BGK ceiling endpoint (`C < √L`).  Thus the `C/√L` target is not just below `1`; the exact
gap to close is a strict multiplicative factor `√L/C`. -/
theorem one_lt_doorIV_shave_factor {C L : ℝ} (hC : 0 < C)
    (hCL : C < Real.sqrt L) :
    1 < Real.sqrt L / C := by
  rw [one_lt_div hC]
  exact hCL

/-! ## The door-(i) resonance lever sits at the floor endpoint (floor-incapable, in Sh units)

The named door-(i) resonance / Parseval-RMS lever certifies a per-frequency value of the form
`c·√n` (see `_NamedLeverRefutationCapstone.resonanceLever_le_prizeFloor`).  In Shaw-value units that
is `shawValue (c·√n) n L = c/√L` — exactly the lower (Plancherel) bracket endpoint `1/√L` scaled by
`c`.  So for `c ≤ 1` the resonance lever lands at or below the floor endpoint and gives no separation
above it: it is *floor-incapable* in the sharp bracket, confirming the door-(i) refutation in
Shaw-value language. -/

/-- **Resonance lever in Shaw-value units.**  The door-(i) resonance certificate value `c·√n`
normalizes to `shawValue (c·√n) n L = c/√L`. -/
theorem shawValue_resonanceLever_eq {c n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    shawValue (c * Real.sqrt n) n L = c / Real.sqrt L := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  unfold shawValue prizeScale
  rw [Real.sqrt_mul hn.le]
  field_simp

/-- **The resonance lever is floor-incapable.**  For `c ≤ 1`, the door-(i) resonance lever's Shaw value
`c/√L` is at most the floor endpoint `1/√L` (`= √n/prizeScale n L`).  So the resonance / Parseval-RMS
lever never separates above the Plancherel floor in the sharp bracket; it cannot reach, let alone
shave below, the door-(iv) corridor.  (Shaw-value restatement of
`_NamedLeverRefutationCapstone.resonanceLever_le_prizeFloor`.) -/
theorem shawValue_resonanceLever_le_floor {c n L : ℝ} (hn : 0 < n) (hL : 0 < L) (hc : c ≤ 1) :
    shawValue (c * Real.sqrt n) n L ≤ Real.sqrt n / prizeScale n L := by
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  rw [shawValue_resonanceLever_eq hn hL]
  rw [show Real.sqrt n / prizeScale n L = 1 / Real.sqrt L from floor_bracket_eq hn]
  rw [div_le_div_iff₀ hsL hsL]
  nlinarith [hc, hsL]

/-! ## Uniform-family form: the GENUINE prize `prize ⇔ Sh(n) = O(1/√L)` over admissible families

`ShawValueCapstone.rawPrizeFamilyBound_iff_shawValueFamilyBound` packages the BGK-*shaped* family bound
`M ≤ C·√(n·L)` ⇔ `Sh ≤ C`.  The next rungs package the GENUINE prize family bound `M ≤ C·√n` ⇔
`Sh ≤ C/√L` at every admissible thin instance — the uniform Shaw-value capstone for the actual prize
target. -/

/-- A uniform GENUINE-prize family bound by `C` across a parameter family: `M i ≤ C·√(n i)` at each `i`
(the prize target uses `√n`, not the normalizer `√(n·L)`). -/
def genuinePrizeFamilyBound {ι : Type*} (M n : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i ≤ C * Real.sqrt (n i)

/-- **Uniform GENUINE-prize Shaw-value capstone.**  Under pointwise positive `n` and `L`, the uniform
genuine-prize family bound `M i ≤ C·√(n i)` is exactly the uniform pointwise Shaw-value bound
`shawValue (M i) (n i) (L i) ≤ C/√(L i)` at every instance.  This is the machine-checked arithmetic
core of "genuine prize ⇔ Sh(n) = O(1/√L)" — the prize landing at the lower bracket endpoint scale, not
the BGK-ceiling scale.  No cancellation estimate is hidden. -/
theorem genuinePrizeFamilyBound_iff_shawValue {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hn : ∀ i, 0 < n i) (hL : ∀ i, 0 < L i) :
    genuinePrizeFamilyBound M n C ↔
      ∀ i, shawValue (M i) (n i) (L i) ≤ C / Real.sqrt (L i) := by
  unfold genuinePrizeFamilyBound
  constructor
  · intro h i
    exact (prize_iff_shawValue_le_div_sqrtL (hn i) (hL i)).1 (h i)
  · intro h i
    exact (prize_iff_shawValue_le_div_sqrtL (hn i) (hL i)).2 (h i)

/-! ## One bundled door-(iv) corridor capstone (citable)

The single citable statement assembling the whole sharp-bracket picture on the real worst-frequency
size `M` in the thin prize regime: the Plancherel floor, the BGK ceiling (`shawValue ≤ 1`), the closed
endpoints (`1/√L` and `1`), the `√L` width, and the prize obligation (`prize ⇔ shawValue ≤ C/√L`, which
is strictly below the BGK ceiling).  Pure assembly of the proven rungs above — no new mathematics. -/

/-- **Door-(iv) sharp-corridor capstone (bundled).**  In the thin prize regime (`0 < n`, `0 < L`,
`C < √L`), given the proven Plancherel floor `√n ≤ M` and BGK ceiling `M ≤ √(n·L)`:

* `shawValue M n L ∈ [√n/√(n·L), 1]` (the sharp BGK bracket),
* its lower endpoint is `1/√L` and its width is `√L`,
* the genuine prize `M ≤ C·√n` is equivalent to `shawValue M n L ≤ C/√L`, and
* that prize level `C/√L` is *strictly below* the BGK ceiling `1`.

One citation surface for "door (iv) = collapse the `√L`-wide Shaw bracket to a constant".  Assembly
only. -/
theorem doorIV_sharp_corridor_capstone {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hC : 0 < C) (hCL : C < Real.sqrt L) (hfloor : Real.sqrt n ≤ M)
    (hceil : M ≤ prizeScale n L) :
    (Real.sqrt n / prizeScale n L ≤ shawValue M n L ∧ shawValue M n L ≤ 1) ∧
      Real.sqrt n / prizeScale n L = 1 / Real.sqrt L ∧
      (1 : ℝ) / (Real.sqrt n / prizeScale n L) = Real.sqrt L ∧
      (M ≤ C * Real.sqrt n ↔ shawValue M n L ≤ C / Real.sqrt L) ∧
      C / Real.sqrt L < 1 ∧ (1 : ℝ) / (C / Real.sqrt L) = Real.sqrt L / C := by
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  refine ⟨shawValue_sharp_bracket (prizeScale_pos hn hL) hfloor hceil,
    shawValue_sharp_bracket_lower_eq hn, shawValue_sharp_bracket_width hn,
    prize_iff_shawValue_le_div_sqrtL hn hL, ?_, ?_⟩
  · rw [div_lt_one hsL]; exact hCL
  · exact doorIV_shave_factor_eq hC hL

end ArkLib.ProximityGap.Frontier.ShawValueBGKBracket

#print axioms ArkLib.ProximityGap.Frontier.ShawValueBGKBracket.doorIV_shave_factor_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBGKBracket.one_lt_doorIV_shave_factor
#print axioms ArkLib.ProximityGap.Frontier.ShawValueBGKBracket.doorIV_sharp_corridor_capstone
