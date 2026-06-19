/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NovelAntiConcentration

/-!
# `_DoorIVValueShiftHistogramObstruction`: the value-shift route needs a `+s`-periodic histogram (#444)

Door-(iv) Lane 3 constraint lemma. Extends `_NovelAntiConcentration`.

## Context

`_NovelAntiConcentration.charP_energy_of_shift` is the genuine `L^∞` anti-concentration mechanism
that ESCAPES the moment obstruction: IF the value map `val : T → ZMod p` admits a `ValueShift` of
additive step-order `m`, THEN the wraparound fiber is `≤ #T / m`, which at `m ≈ p` is the
prize-strength bound. Its docstring isolates the SINGLE open input as:

> "does the shift action have a large free part for `μ_n`'s value map?"

This file LOCKS that input as a constraint. It records the exact obligation a value-shift imposes —
**the fiber-cardinality histogram `a ↦ fiberCard val a` must be invariant under `+s`** — and the
contrapositive obstruction: a single pair of residues with unequal fiber mass `fiberCard val a ≠
fiberCard val (a+s)` already RULES OUT every value-shift of step `s`. Hence the spreading mechanism
can only deliver order `> 1` if the histogram is genuinely `+s`-periodic.

## Probe verdict (probe-first, reproducible)

For the prize energy value map `val(t) = Σ_{i<r} x_i − Σ_{i<r} y_i` over `t ∈ μ_n^{2r}`
(thin 2-power subgroup `μ_n ⊊ F_p^*`, `n = 2^a`, `p ≡ 1 mod n`, `p ≫ n³`, NEVER `n = q−1`):

* The value-SET `V_r` FILLS the field `ZMod p` for every `r ≥ 2` — so the value-set's additive
  stabilizer is the full field (`p` prime ⟹ stabilizer is `{0}` or all of `ZMod p`).
* BUT the fiber-cardinality histogram is NEVER `+s`-invariant for any unit `s`: it is sharply
  non-flat and non-periodic (e.g. `p=97, n=8, r=3`: fiber masses range `min=1505, max=5600`; the
  largest `+s`-period is `1` at every tested `(p,n,r)`).

So although `V_r` is `+s`-symmetric for `s` of full order, that symmetry does NOT lift to a
tuple-permutation realizing a fixed shift: a value-shift demands the strictly stronger
fiber-CARDINALITY periodicity, which fails. **The only value-shift of the prize value map is the
trivial one (`s = 0`, order `1`), and the spreading mechanism then gives `≤ #T/1 = #T` — no bound.**

VERDICT: the value-shift / free-part route of `charP_energy_of_shift` does NOT escape to a useful
bound for the prize value map. To use spreading at order `> 1` one must first exhibit a
`+s`-periodic fiber histogram, which the prize geometry refutes. No CORE, cancellation, completion,
moment-saving, or capacity claim.

## Statements

* `valueShift_histogram_periodic` : a `ValueShift` of step `s` forces `fiberCard val a =
  fiberCard val (a+s)` for all `a` (the histogram is `+s`-invariant). [packages `fiberCard_shift_eq`
  as the obstruction it really is].
* `no_valueShift_of_histogram_witness` : if some `a` has `fiberCard val a ≠ fiberCard val (a+s)`,
  then NO `ValueShift` with that step `s` exists.
* `valueShift_step_zero_of_no_periodicity` : if for every nonzero step `s` the histogram fails
  `+s`-periodicity, then every `ValueShift` has step `s = 0`.
* `shift_spreading_trivial_of_step_zero` : a step-`0` value-shift gives only the trivial spreading
  bound (`fiberCard val 0 ≤ #T`), i.e. no improvement.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction

open Finset
open ArkLib.ProximityGap.Frontier.NovelAntiConcentration

variable {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ}

/-- **A value-shift forces its fiber histogram to be `+s`-periodic.** This is exactly the obligation
a `ValueShift` imposes: the per-residue fiber mass at `a` equals the mass at `a + s`. It is the
re-packaging of `fiberCard_shift_eq` as the necessary condition for the shift to exist. -/
theorem valueShift_histogram_periodic (val : T → ZMod p) (vs : ValueShift val) (a : ZMod p) :
    fiberCard val a = fiberCard val (a + vs.s) :=
  fiberCard_shift_eq val vs a

/-- **The contrapositive obstruction.** If a single residue `a` has fiber mass differing from the
mass at `a + s`, then NO `ValueShift` whose step equals `s` can exist. A non-periodic histogram is a
kernel-checkable certificate against the value-shift route at that step. -/
theorem no_valueShift_of_histogram_witness (val : T → ZMod p) (s : ZMod p) (a : ZMod p)
    (hne : fiberCard val a ≠ fiberCard val (a + s)) :
    ¬ ∃ vs : ValueShift val, vs.s = s := by
  rintro ⟨vs, rfl⟩
  exact hne (valueShift_histogram_periodic val vs a)

/-- **No nonzero step survives a globally non-periodic histogram.** If for every nonzero candidate
step `s` there is a witness residue with unequal fiber mass at `a` and `a + s`, then every
`ValueShift` of `val` has step `s = 0`. This is the exact collapse the prize probe exhibits: the
fiber histogram is `+s`-non-periodic for all `s ≠ 0`, so the only available shift is trivial. -/
theorem valueShift_step_zero_of_no_periodicity (val : T → ZMod p)
    (hno : ∀ s : ZMod p, s ≠ 0 → ∃ a : ZMod p, fiberCard val a ≠ fiberCard val (a + s))
    (vs : ValueShift val) :
    vs.s = 0 := by
  by_contra hs
  obtain ⟨a, ha⟩ := hno vs.s hs
  exact ha (valueShift_histogram_periodic val vs a)

/-- **A step-`0` value-shift gives only the trivial spreading bound.** When the only available
value-shift has step `s = 0`, the spreading mechanism `fiberCard_zero_le_of_shift_order` runs at
order `m = 1`, yielding `fiberCard val 0 ≤ #T`, the vacuous ceiling. The anti-concentration route
delivers no improvement. -/
theorem shift_spreading_trivial_of_step_zero (val : T → ZMod p) :
    fiberCard val 0 ≤ Fintype.card T := by
  classical
  have : Fiber val 0 ⊆ (Finset.univ : Finset T) := Finset.subset_univ _
  calc fiberCard val 0 = (Fiber val 0).card := rfl
    _ ≤ (Finset.univ : Finset T).card := Finset.card_le_card this
    _ = Fintype.card T := Finset.card_univ

/-- **The full obstruction, assembled.** If the fiber histogram of `val` is `+s`-non-periodic for
every nonzero step, then every value-shift is trivial and the spreading mechanism collapses to the
vacuous ceiling `fiberCard val 0 ≤ #T`. So under the prize-geometry probe verdict, the value-shift
route of `charP_energy_of_shift` cannot produce a sub-`#T` bound on the wraparound. -/
theorem valueShift_route_vacuous_of_no_periodicity (val : T → ZMod p)
    (hno : ∀ s : ZMod p, s ≠ 0 → ∃ a : ZMod p, fiberCard val a ≠ fiberCard val (a + s))
    (vs : ValueShift val) :
    vs.s = 0 ∧ fiberCard val 0 ≤ Fintype.card T :=
  ⟨valueShift_step_zero_of_no_periodicity val hno vs, shift_spreading_trivial_of_step_zero val⟩

end ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction
#print axioms valueShift_histogram_periodic
#print axioms no_valueShift_of_histogram_witness
#print axioms valueShift_step_zero_of_no_periodicity
#print axioms shift_spreading_trivial_of_step_zero
#print axioms valueShift_route_vacuous_of_no_periodicity
end AxiomAudit
