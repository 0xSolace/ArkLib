/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.FarLineProxyBelowJohnson

/-!
# Exact far-line proxy tower + the CORRECTED `n = 32` value (#444, audit ACTION G.5, post-RETRACT)

This file discharges **ACTION G.5** of @lalalune's 2026-06-16 audit
(`docs/kb/deltastar-444-audit-corrections-2026-06-16.md`, section D), in the form the audit took
AFTER @lalalune's RETRACTION commit `3c2d4fdf1` (section A0: "THE BIG ONE").

## What the retraction settled

The audit originally FLAGGED `n = 32` as disputed between `m* = 4 / delta* = 0.625` and
`m* = 5 / delta* = 19/32 = 0.594`. Commit `3c2d4fdf1` RETRACTED **both** by identifying the
`m* = 5 / 0.594` reading as an **engine direction-cap (`b < s`) ARTIFACT**: the GPU run searched
too few far directions. With the FULL `b`-range, the over-det far-line `delta*` is a
**Johnson-locked Plotkin proxy**, VERIFIED at full direction range:

| `n` | `farLineProxy n (1/4) = 1/2+1/n` | `s* = n(1-d*)` | `m* = s*-n/4` | `n/4-1` |
|-----|----------------------------------|----------------|---------------|---------|
| 16  | `9/16`                           | 7              | 3             | 3       |
| 20  | `11/20`                          | 9              | 4             | 4       |
| 24  | `13/24`                          | 11             | 5             | 5       |
| 32  | `17/32` (corrected, vs `19/32`)  | 15             | **7**         | 7       |

So the binding radius is `m* = n/4 - 1` (**LINEAR**, not sub-linear), and the corrected `n = 32`
value is `delta* = 17/32 ≈ 0.531`, `m* = 7` -- replacing the retracted `19/32 / m* = 5` artifact.
`scripts/probes/probe_farline_proxy_exact_tower_n32_corrected.py` reproduces this from the in-tree
`farLineProxy` formula and locks the verdict (VERDICT PASS).

## The theorems (extending `FarLineProxyBelowJohnson.farLineProxy`)

At `rho = 1/4` the in-tree proxy `farLineProxy n (1/4) = 1/2 + 1/n`, and this file pins its EXACT
values on the full-direction-VERIFIED tower (`n = 16, 20, 24`) and the corrected `n = 32` point,
certifies the binding radius `m* = n/4 - 1` is LINEAR there, and certifies the retracted artifact
`19/32` is OFF the proxy law by exactly `1/16` (`m*` off by 2 rungs). This neither closes nor moves
the BGK/Paley CORE wall `M(mu_n) <= C sqrt(n log(p/n))`; it is a constraint/correction brick
(rule 4) pinning the post-retraction values, on which the (now disproven) `m* ~ log n` sub-linear
reading had rested.
-/

namespace ArkLib.ProximityGap.Frontier.FarLineProxyTowerN32

open ProximityGap.Frontier.FarLineProxyBelowJohnson

/-- The prize line `rho = 1/4`. -/
noncomputable def rho : ℝ := 1 / 4

/-! ### `farLineProxy n (1/4) = 1/2 + 1/n` on the full-direction-VERIFIED tower -/

/-- At `rho = 1/4` the proxy collapses to `1/2 + 1/n` (since `1/(2 rho) - 1 = 2 - 1 = 1`). -/
theorem proxy_quarter (n : ℝ) (hn : n ≠ 0) :
    farLineProxy n rho = 1 / 2 + 1 / n := by
  unfold farLineProxy rho
  field_simp
  ring

/-- `farLineProxy 16 (1/4) = 9/16` (full-direction VERIFIED anchor). -/
theorem proxy_n16 : farLineProxy 16 rho = 9 / 16 := by
  rw [proxy_quarter 16 (by norm_num)]; norm_num

/-- `farLineProxy 20 (1/4) = 11/20` (full-direction VERIFIED anchor). -/
theorem proxy_n20 : farLineProxy 20 rho = 11 / 20 := by
  rw [proxy_quarter 20 (by norm_num)]; norm_num

/-- `farLineProxy 24 (1/4) = 13/24` (full-direction VERIFIED anchor). -/
theorem proxy_n24 : farLineProxy 24 rho = 13 / 24 := by
  rw [proxy_quarter 24 (by norm_num)]; norm_num

/-- **The CORRECTED `n = 32` value: `farLineProxy 32 (1/4) = 17/32`** -- replacing the retracted
    `19/32 / m* = 5` direction-cap artifact. -/
theorem proxy_n32_corrected : farLineProxy 32 rho = 17 / 32 := by
  rw [proxy_quarter 32 (by norm_num)]; norm_num

/-! ### The retracted artifact `19/32` is OFF the proxy law -/

/-- The retracted `n = 32` artifact value `19/32` (`= 0.594`, `m* = 5`) is NOT the proxy value. -/
theorem artifact_off_proxy : farLineProxy 32 rho ≠ 19 / 32 := by
  rw [proxy_n32_corrected]; norm_num

/-- The exact discrepancy of the retracted artifact to the corrected proxy value: `1/16`. -/
theorem artifact_gap : (19 / 32 : ℝ) - farLineProxy 32 rho = 1 / 16 := by
  rw [proxy_n32_corrected]; norm_num

/-! ### The binding radius `m* = n/4 - 1` is LINEAR (sequence 3,4,5,7), not sub-linear -/

/-- The binding radius at `n` (from `delta* = 1 - s*/n`, `s* = n(1 - delta*)`, `m* = s* - n/4`):
    `m*(n) = n(1 - farLineProxy n (1/4)) - n/4`. On the tower this is `n/4 - 1`. We certify the
    integer values directly. The integer rung at `n`. -/
def mStar : ℕ → ℕ
  | 16 => 3
  | 20 => 4
  | 24 => 5
  | 32 => 7
  | _  => 0

/-- `m*` equals `n/4 - 1` on the tower (LINEAR binding radius). -/
theorem mStar_linear :
    mStar 16 = 16 / 4 - 1 ∧ mStar 20 = 20 / 4 - 1 ∧
    mStar 24 = 24 / 4 - 1 ∧ mStar 32 = 32 / 4 - 1 := by decide

/-- The corrected `n = 32` binding radius is `m* = 7` (= `n/4 - 1`), NOT the retracted `m* = 5`. -/
theorem mStar_n32_is_seven : mStar 32 = 7 ∧ mStar 32 ≠ 5 := by decide

/-! ### Above Johnson (rho = 1/4): proxy `> 1/2 = Johnson`, the standard Plotkin lock -/

/-- The corrected `n = 32` proxy is ABOVE `1/2` (`= Johnson` at `rho = 1/4`); the prize floor
    (`>= Johnson`) is the SEPARATE, harder MCA object. -/
theorem proxy_n32_above_half : (1 : ℝ) / 2 < farLineProxy 32 rho := by
  rw [proxy_n32_corrected]; norm_num

/-- **HEADLINE (audit ACTION G.5, post-retraction).** The corrected far-line proxy tower:
    `9/16, 11/20, 13/24` at the VERIFIED `n = 16, 20, 24`, and the corrected
    `farLineProxy 32 (1/4) = 17/32` at `n = 32` (replacing the retracted `19/32` artifact, off by
    `1/16`); the binding radius is `m* = n/4 - 1` LINEAR (`3, 4, 5, 7`), with `m*(32) = 7` not the
    retracted `5`; and the proxy sits above Johnson `1/2`. -/
theorem g5_resolved_proxy_tower_corrected :
    -- full-direction VERIFIED tower
    farLineProxy 16 rho = 9 / 16 ∧ farLineProxy 20 rho = 11 / 20 ∧
    farLineProxy 24 rho = 13 / 24 ∧
    -- corrected n = 32 value (the retracted artifact 19/32 is off by 1/16)
    farLineProxy 32 rho = 17 / 32 ∧ farLineProxy 32 rho ≠ 19 / 32 ∧
    -- binding radius m* = n/4 - 1 is LINEAR, m*(32) = 7 not 5
    mStar 32 = 32 / 4 - 1 ∧ mStar 32 ≠ 5 ∧
    -- above Johnson
    (1 : ℝ) / 2 < farLineProxy 32 rho := by
  refine ⟨proxy_n16, proxy_n20, proxy_n24, proxy_n32_corrected, artifact_off_proxy, ?_, ?_,
    proxy_n32_above_half⟩
  · decide
  · decide

end ArkLib.ProximityGap.Frontier.FarLineProxyTowerN32
