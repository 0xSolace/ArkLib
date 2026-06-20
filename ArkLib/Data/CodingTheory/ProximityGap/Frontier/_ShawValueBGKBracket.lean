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

end ArkLib.ProximityGap.Frontier.ShawValueBGKBracket
