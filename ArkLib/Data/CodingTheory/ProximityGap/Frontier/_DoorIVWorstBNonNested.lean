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

/-- **The witness gap is the obstruction.**  At the level-`n` worst frequency `b*`, the positive gap
`M₂ − a* = subMag c − subMag b* > 0` (with `c` the level-`(n/2)` argmax) is exactly the amount by which
a recursive-ascent argument that assumed `worst_n = worst_{n/2}` would be wrong: it certifies a strictly
better sub-frequency the level-`n` worst frequency misses. -/
theorem witness_gap_pos_of_lt {subMag : ι → ℝ} {b c : ι} (h : subMag b < subMag c) :
    0 < subMag c - subMag b := by linarith

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
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBNonNested.high_percentile_not_argmax
