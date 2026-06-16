/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Bridge B04 — target E1: the master gap identity `capacity − δ* = (m*−1)/n` (#444)

E1 (`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`) states the master gap
identity that pins `δ*` from the binding depth `m*`:

  `δ* = 1 − ρ − (m*−1)/n`,   equivalently   `capacity − δ* = (m*−1)/n`,

with `capacity = 1 − ρ`. The KB tags this as "elementary unwinding of P1 + the definition of `m*`"
and flags it as a clean brick.

This file makes the *arithmetic content* of E1 precise and axiom-clean. We DEFINE the two faces of
δ* — its closed form `deltaStarFormula ρ m n := 1 − ρ − (m−1)/n` and the capacity
`capacity ρ := 1 − ρ` — as rationals, and prove the equivalence is an EXACT rational identity (with
the honest non-degeneracy hypothesis `n ≠ 0` only for the division-rearranged forms).

## Honest scope

This is the *rational-arithmetic* half of E1: GIVEN the closed form `δ* = 1 − ρ − (m*−1)/n` as the
definition of `deltaStarFormula`, the gap identity `capacity − δ* = (m*−1)/n` is a ring/field
identity. The *content* of E1 that this does NOT supply is the bridge from the operational
`mcaDeltaStar` (the `sSup`-threshold of `OpenCoreConverse.lean`) to this closed form — i.e. that the
operational δ* EQUALS `deltaStarFormula ρ m* n` at the binding depth `m*`. That equality is the
genuine mathematical claim of E1 (it requires P1 + the binding-cascade pinning of `m*`); it is named
here as the residual Prop `OperationalDeltaStarEqFormula`. Everything proved below is the exact
rational rearrangement, which is unconditional ring algebra.

Issue #444.
-/

namespace ProximityGap.BridgeB04

/-- The list-decoding **capacity** as a rational: `1 − ρ`. -/
def capacity (ρ : ℚ) : ℚ := 1 - ρ

/-- The empirical **closed form** of `δ*` from binding depth `m` over block length `n`
(E1): `1 − ρ − (m−1)/n`. -/
def deltaStarFormula (ρ : ℚ) (m n : ℚ) : ℚ := 1 - ρ - (m - 1) / n

/-- **E1, gap form (exact rational identity).** `capacity − δ* = (m*−1)/n`. This is the
unconditional ring/field rearrangement of the closed form. -/
theorem capacity_sub_deltaStar (ρ m n : ℚ) :
    capacity ρ - deltaStarFormula ρ m n = (m - 1) / n := by
  unfold capacity deltaStarFormula
  ring

/-- **E1, solved form.** `δ* = 1 − ρ − (m*−1)/n` is recovered from the gap identity. -/
theorem deltaStarFormula_eq (ρ m n : ℚ) :
    deltaStarFormula ρ m n = 1 - ρ - (m - 1) / n := rfl

/-- **E1, capacity-minus-gap form.** `δ* = capacity − (m*−1)/n`. -/
theorem deltaStarFormula_eq_capacity_sub (ρ m n : ℚ) :
    deltaStarFormula ρ m n = capacity ρ - (m - 1) / n := by
  unfold capacity deltaStarFormula
  ring

/-- **E1, cleared-denominator form (honest `n ≠ 0`).** Multiplying through by `n`:
`(capacity − δ*) · n = m* − 1`, the integer-arithmetic content of the gap. -/
theorem capacity_sub_deltaStar_mul (ρ m n : ℚ) (hn : n ≠ 0) :
    (capacity ρ - deltaStarFormula ρ m n) * n = m - 1 := by
  rw [capacity_sub_deltaStar]
  field_simp

/-- **E1, depth-solved form (honest `n ≠ 0`).** The binding depth read back from the gap:
`m* = 1 + (capacity − δ*) · n`. -/
theorem bindingDepth_eq (ρ m n : ℚ) (hn : n ≠ 0) :
    m = 1 + (capacity ρ - deltaStarFormula ρ m n) * n := by
  rw [capacity_sub_deltaStar_mul ρ m n hn]; ring

/-- **The residual (named, not proved here).** The genuine content of E1 that this rational
brick does NOT supply: that the OPERATIONAL `δ*` (the `sSup`-threshold) equals the closed form
`deltaStarFormula ρ m* n` at the binding depth `m*`. Stated as a `Prop` so downstream work can
consume it as an explicit hypothesis. -/
def OperationalDeltaStarEqFormula (operationalDeltaStar : ℚ) (ρ m n : ℚ) : Prop :=
  operationalDeltaStar = deltaStarFormula ρ m n

/-- **E1 under the operational-equals-formula bridge.** GIVEN the residual, the operational δ*
obeys the master gap identity. This is the honest "reduced" statement: the gap identity holds for
the operational δ* exactly modulo `OperationalDeltaStarEqFormula`. -/
theorem capacity_sub_operationalDeltaStar
    (operationalDeltaStar ρ m n : ℚ)
    (h : OperationalDeltaStarEqFormula operationalDeltaStar ρ m n) :
    capacity ρ - operationalDeltaStar = (m - 1) / n := by
  rw [h]; exact capacity_sub_deltaStar ρ m n

end ProximityGap.BridgeB04

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.BridgeB04.capacity_sub_deltaStar
#print axioms ProximityGap.BridgeB04.capacity_sub_deltaStar_mul
#print axioms ProximityGap.BridgeB04.bindingDepth_eq
#print axioms ProximityGap.BridgeB04.capacity_sub_operationalDeltaStar
