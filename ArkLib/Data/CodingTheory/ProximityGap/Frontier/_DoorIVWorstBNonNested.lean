/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) constraint: the worst frequency is NOT cross-scale nested — no recursive-ascent (#444)

At the level-`n` worst frequency `b*` (argmax of `‖η_b‖`, `η_b = Σ_{y∈μ_n} e_p(b·y)`), the subgroup
half `A_{b*} = Σ_{y∈μ_{n/2}} e_p(b*·y)` is itself a period over the thinner subgroup `μ_{n/2}`.  A
**recursive-ascent lever** would try to BUILD the level-`n` worst frequency from the level-`(n/2)`
worst frequency, assuming the worst `b` is *nested*: that `b*` (or its orbit) also maximizes the
level-`(n/2)` sub-period `‖A_b‖`.  If that nesting held, the dyadic tower's worst frequencies would be
one tower and an inductive worst-case bound could climb it.

PROBE (`scripts/probes/probe_dooriv_worstb_nesting.py`; proper `μ_n`, `p ≫ n³`, structured primes,
never `n=q-1`).  The decisive evidence is the FULL `F_p*` scans (global argmax, no sampling) at
`n=16 β=4`, `n=16 β=4.3`, `n=32 β=3.5`:
* the level-`n` worst `b*` lands at the **97.2–99.9th percentile** of the level-`(n/2)` sub-period
  magnitudes — strongly cross-scale *correlated* (it is near-top for the thinner subgroup too);
* but it is **strictly NOT the global argmax** of the level-`(n/2)` sub-period: the magnitude-transfer
  ratio `‖A_{b*}‖ / max_b‖A_b‖` is `0.951 / 0.766 / 0.931` (all `< 1`, never exact), and is smaller at
  the deeper-`β` full scan (`0.766` at `β=4.3` vs `0.951` at `β=4`, same `n=16`) — deeper `β` widens the
  gap.  (Deeper-`β` SAMPLED runs reproduce the same high-percentile/ratio`<1` pattern as a consistency
  check only — they are NOT global-argmax claims; the constraint rests on the full-scan data.)

CONSEQUENCE (this file, axiom-clean).  "Near-top percentile at every level" does NOT entail
"argmax-identity across levels": a value can be a strict upper bound on every member of a set yet be
strictly below the set's maximum.  We record this gap abstractly: if the transferred sub-period value
`a*` is strictly below the level-`(n/2)` maximum `M₂` (the probe: `‖A_{b*}‖ < max_b‖A_b‖`), then the
level-`n` worst frequency is **not** a level-`(n/2)` maximizer, so a recursive-ascent argument that
identifies the two worst frequencies is UNSOUND — there is always a frequency strictly better for the
thinner subgroup that the level-`n` worst frequency misses.  Equivalently, no `ascent` that assumes
`worst_n = worst_{n/2}` can be correct, because the witness gap `M₂ − a* > 0` is the failure.

This is a **refutation with mechanism** (a precisely-mapped dead lever), not a CORE/cancellation/capacity
claim: it does not bound `M(n)`; it shows the worst-frequency-nesting recursive-ascent shape cannot.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested

open Finset

variable {ι : Type*}

/-- A frequency `b` is a **level-`(n/2)` maximizer** of the sub-period magnitude `subMag` when no other
frequency beats it. -/
def IsSubMaximizer (subMag : ι → ℝ) (b : ι) : Prop := ∀ c, subMag c ≤ subMag b

/-- **A strictly-dominated frequency is not a maximizer.**  If some `c` has a *strictly larger*
sub-period magnitude than `b`, then `b` cannot be a level-`(n/2)` maximizer.  This is the abstract
content of the probe's `exact-argmax = False`: the level-`n` worst frequency `b*` always has a witness
`c` (the true level-`(n/2)` argmax) with `subMag c > subMag b*`. -/
theorem not_isSubMaximizer_of_lt {subMag : ι → ℝ} {b c : ι}
    (h : subMag b < subMag c) : ¬ IsSubMaximizer subMag b := by
  intro hmax
  exact absurd (hmax c) (not_le_of_gt h)

/-- **The recursive-ascent identity fails when the transfer ratio is below `1`.**  Suppose the level-`n`
worst frequency `b*` transfers sub-period magnitude `a* = subMag b*` and the level-`(n/2)` maximum is
`M₂ = subMag c` at the true sub-argmax `c`.  If the *transfer ratio* `a* / M₂ < 1` with `M₂ > 0`
(the probe: ratio `≤ 0.95`, decaying to `~0.70`), then `b* ≠ c` and `b*` is not a sub-maximizer: the
worst frequencies of the two levels are genuinely distinct. -/
theorem worstB_not_nested_of_ratio_lt_one {subMag : ι → ℝ} {b c : ι}
    (hpos : 0 < subMag c) (hratio : subMag b / subMag c < 1) :
    subMag b < subMag c ∧ ¬ IsSubMaximizer subMag b := by
  have hlt : subMag b < subMag c := by
    have := (div_lt_one hpos).mp hratio
    exact this
  exact ⟨hlt, not_isSubMaximizer_of_lt hlt⟩


/-- **Quantitative non-nesting gap from a transfer-ratio bound.**  If the transferred sub-period value
at the level-`n` worst frequency is at most an `r < 1` fraction of the true level-`(n/2)` maximum `M₂`,
then the missed-subargmax gap is at least `(1-r)M₂`.  Thus the measured ratios below `1` are not just
boolean failures of nesting; they certify a positive margin that any recursive-ascent proof would have
to absorb. -/
theorem witness_gap_ge_of_ratio_le {subMag : ι → ℝ} {b c : ι} {r : ℝ}
    (hpos : 0 < subMag c) (hratio : subMag b / subMag c ≤ r) :
    (1 - r) * subMag c ≤ subMag c - subMag b := by
  have hle : subMag b ≤ r * subMag c := by
    exact (div_le_iff₀ hpos).mp hratio
  nlinarith

/-- **The transfer ratio bound is exactly the quantitative witness gap bound.**  With a positive true
level-`(n/2)` maximum `M₂ = subMag c`, the normalized certificate `subMag b / M₂ ≤ r` is equivalent to
the raw additive gap certificate `(1-r)M₂ ≤ M₂-subMag b`.  Thus the ratios emitted by full worst-b
probes can be stored without losing the exact scale of the missed-subargmax gap. -/
theorem ratio_le_iff_witness_gap_ge {subMag : ι → ℝ} {b c : ι} {r : ℝ}
    (hpos : 0 < subMag c) :
    subMag b / subMag c ≤ r ↔ (1 - r) * subMag c ≤ subMag c - subMag b := by
  constructor
  · intro hratio
    exact witness_gap_ge_of_ratio_le (subMag := subMag) (b := b) (c := c) hpos hratio
  · intro hgap
    rw [div_le_iff₀ hpos]
    linarith

/-- **Strict non-nesting from a bounded transfer ratio.**  The empirical form of the obstruction is
often reported as `subMag b / subMag c ≤ r` for some explicit `r < 1` (for example `0.951`, `0.766`,
`0.931`).  This theorem packages that certificate directly into the boolean failure of recursive
ascent: a ratio bound below `1` forces a strictly better sub-frequency and hence `b` is not a
level-`(n/2)` maximizer. -/
theorem not_isSubMaximizer_of_ratio_le_lt_one {subMag : ι → ℝ} {b c : ι} {r : ℝ}
    (hpos : 0 < subMag c) (hratio : subMag b / subMag c ≤ r) (hr : r < 1) :
    ¬ IsSubMaximizer subMag b := by
  have hratio' : subMag b / subMag c < 1 := lt_of_le_of_lt hratio hr
  exact (worstB_not_nested_of_ratio_lt_one (subMag := subMag) (b := b) (c := c)
    hpos hratio').2

/-- **The witness gap is the obstruction.**  At the level-`n` worst frequency `b*`, the positive gap
`M₂ − a* = subMag c − subMag b* > 0` (with `c` the level-`(n/2)` argmax) is exactly the amount by which
a recursive-ascent argument that assumed `worst_n = worst_{n/2}` would be wrong: it certifies a strictly
better sub-frequency the level-`n` worst frequency misses. -/
theorem witness_gap_pos_of_lt {subMag : ι → ℝ} {b c : ι} (h : subMag b < subMag c) :
    0 < subMag c - subMag b := by linarith

/-- **Ratio gap and additive witness gap are equivalent certificates.**  With positive true
level-`(n/2)` maximum, saying the transfer ratio is strictly below `1` is exactly saying the missed
subargmax gap `M₂ - a*` is positive.  This lets probes record either the normalized ratio or the raw
magnitude gap without changing the obstruction certificate. -/
theorem ratio_lt_one_iff_witness_gap_pos {subMag : ι → ℝ} {b c : ι}
    (hpos : 0 < subMag c) :
    subMag b / subMag c < 1 ↔ 0 < subMag c - subMag b := by
  constructor
  · intro hratio
    have hlt : subMag b < subMag c := (div_lt_one hpos).mp hratio
    linarith
  · intro hgap
    have hlt : subMag b < subMag c := by linarith
    exact (div_lt_one hpos).mpr hlt

/-- **Percentile-domination does NOT give argmax-identity.**  Even if the transferred value `a*` upper-
bounds *every* sub-period magnitude *except* at the true argmax `c` (`∀ d ≠ c, subMag d ≤ a*`, the
"99.9th percentile" content) — as long as `a* < subMag c` at the single witness `c`, `b*` is still not a
maximizer.  High percentile rank and argmax-identity are genuinely different; the recursion needs the
latter and the probe shows only the former. -/
theorem high_percentile_not_argmax {subMag : ι → ℝ} {b c : ι}
    (hgap : subMag b < subMag c) :
    ¬ IsSubMaximizer subMag b :=
  not_isSubMaximizer_of_lt hgap

end ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.worstB_not_nested_of_ratio_lt_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.not_isSubMaximizer_of_lt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.witness_gap_pos_of_lt
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.ratio_lt_one_iff_witness_gap_pos
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.witness_gap_ge_of_ratio_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.ratio_le_iff_witness_gap_ge
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.not_isSubMaximizer_of_ratio_le_lt_one
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.high_percentile_not_argmax
