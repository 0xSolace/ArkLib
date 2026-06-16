/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bridge B01 (target E1) — the master gap identity `δ* = 1 − ρ − (m*−1)/n` (#444)

E1 (empirical, from `docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`) reads

  `capacity − δ* = (m*−1)/n`,   i.e.   `δ* = 1 − ρ − (m*−1)/n`,

where `ρ = k/n` is the rate, `m* = s* − k` is the binding over-determination depth, and (per the
budget-crossing pin `OpenCoreConverse.deltaStar_iff_incidence_budget`, anchor P1) the binding
radius is the granularity radius `δ* = 1 − (s* − 1)/n` — i.e. the largest window radius at which
the worst far-line incidence first drops to the budget, indexed by the binding stack size
`s* = k + m*`.

## What this bridge does (HONEST scope)

E1 is, given the *definitions*, a pure ℚ-algebra identity. We take the three definitional inputs
of P1 / the cascade indexing as named hypotheses (an honest reduction, per the directive — it is
fine to `variable`/hypothesise the definitions and discharge the algebra):

* `hρ  : ρ  = (k : ℚ) / n`            — rate is `k/n`  (`k = ρ·n`).
* `hms : (mstar : ℚ) = s - k`         — binding depth `m* = s* − k`.
* `hδ  : deltaStar = 1 - (s - 1) / n` — binding radius is the granularity radius `1 − (s*−1)/n`
                                         (the budget-crossing radius from P1's incidence pin).

From these, with `n ≠ 0`, we derive **exactly**

  `deltaStar = 1 - ρ - (mstar - 1) / n`.

This is the clean brick E1 is flagged to be ("elementary unwinding of P1 + the definition of m*").
The mathematical content that is *not* discharged here — that the budget-crossing happens at this
particular `s*` and that the worst incidence is the granularity count — is exactly P1 +
the cascade (E2), which live upstream as proven/empirical anchors; here we name the radius form
`hδ` as the hypothesis and prove the algebra is forced.

## Honesty

No `sorry`, no fake axiom. The identity is proved over `ℚ` by `field_simp`/`ring` from the three
definitional hypotheses and `n ≠ 0`. The axiom audit at the bottom must show only
`propext, Classical.choice, Quot.sound` (in fact this proof uses none of `Classical.choice`).

Issue #444.
-/

namespace ProximityGap.BridgeB01

/-- **E1 — the master gap identity (ℚ algebra brick).**

Given the rate definition `ρ = k/n`, the binding-depth definition `m* = s − k`, and the binding
radius `δ* = 1 − (s−1)/n` (the budget-crossing granularity radius, anchor P1), the master gap
identity `δ* = 1 − ρ − (m*−1)/n` is forced. -/
theorem deltaStar_master_gap_identity
    (n k s deltaStar rho mstar : ℚ) (hn : n ≠ 0)
    (hρ  : rho = k / n)
    (hms : mstar = s - k)
    (hδ  : deltaStar = 1 - (s - 1) / n) :
    deltaStar = 1 - rho - (mstar - 1) / n := by
  subst hρ hms hδ
  field_simp
  ring

/-- **E1 restated as the capacity gap.** `capacity − δ* = (m*−1)/n`, where `capacity = 1 − ρ`. -/
theorem capacity_gap_eq
    (n k s deltaStar rho mstar : ℚ) (hn : n ≠ 0)
    (hρ  : rho = k / n)
    (hms : mstar = s - k)
    (hδ  : deltaStar = 1 - (s - 1) / n) :
    (1 - rho) - deltaStar = (mstar - 1) / n := by
  have h := deltaStar_master_gap_identity n k s deltaStar rho mstar hn hρ hms hδ
  rw [h]; ring

end ProximityGap.BridgeB01

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.BridgeB01.deltaStar_master_gap_identity
#print axioms ProximityGap.BridgeB01.capacity_gap_eq
