/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarListReduction
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# E04 honest bridge: a WORST-CASE list budget pushes δ* up; the second-moment `exp(M²/n)`
  budget is AVERAGE-case (the gap is the open core) (#389)

The E04 conjecture asserts an M-bound `M(μ_n) ≤ n^{1−c}` yields a list budget
`B(M) = exp(Θ(M²/n))` that pushes the MCA threshold `δ*` past Johnson.  This file records the
**honest** version of that bridge and the precise reason E04-as-stated does not reach the prize:

* **The honest bridge (PROVEN, axiom-clean):** `le_mcaDeltaStar_of_worstCaseListBudget` —
  if EVERY word stack's bad-scalar count is `≤ B` (a *uniform / worst-case* list budget) and
  `B/|F| ≤ ε*`, then `δ ≤ mcaDeltaStar C ε*`.  This is the genuine δ* lower-bound consumer
  (a thin renaming of the in-tree `mcaDeltaStar_ge_of_uniform_mcaBad`).  Its hypothesis is the
  **worst-case** (∀-over-word-stacks) list bound.

* **Why `exp(M²/n)` does NOT discharge it:** `M = λ₂(Cay(F_q,μ_n))`, and the second-moment
  Chernoff/Paley–Zygmund object it controls is `∑_{e∈RS} I(e) = E[N²]/|RS|`
  (`CS25RSSecondMomentMGF.rs_sum_jointCoverCount_le`) — the **average over directions / a typical
  received word**.  The hypothesis of `le_mcaDeltaStar_of_worstCaseListBudget` is the **max over
  word stacks** (because `epsMCA = ⨆_u`).  An average-case `exp(M²/n)` budget is NOT a worst-case
  budget; equating them is the silent conflation in E04.  The gap
  `worst-case list / average list` is precisely the open core (worst-case list upper bound =
  BCHKS Conj 1.12).  NO discharge of the worst-case hypothesis from a second-moment M-bound is
  proven here — and the probes (`scripts/probes/probe_e04_listsize_vs_M.py`) exhibit the explicit
  ladder family whose worst-case list `exp(Θ(n))` strictly exceeds the poly(n) budget `exp(M²/n)`
  in the prize window, so no such discharge can hold.

Honest scope (contract §6B): the bridge below is a true conditional with the **worst-case** list
budget `B` as the named hypothesis.  It is the correct δ* connector.  E04's claim that an M-bound
supplies that `B` via `exp(M²/n)` is REFUTED (see DISPROOF_LOG E04): `exp(M²/n)` is average-case.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.E04Bridge

open ProximityGap ProximityGap.MCAThresholdLedger ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The honest E04 bridge: a WORST-CASE (uniform over word stacks) list budget `B` with
`B/|F| ≤ ε*` pushes `δ* ≥ δ`.**  This is the genuine δ* lower-bound connector.  The hypothesis
`hcard` is the **max over received words** bound — exactly what `mcaDeltaStar = sSup{δ : ⨆_u … ≤ ε*}`
requires.  A second-moment / `exp(M²/n)` budget does NOT supply this (it is average-case); see the
module docstring and DISPROOF_LOG E04. -/
theorem le_mcaDeltaStar_of_worstCaseListBudget
    (C : Set (Fin n → F)) {δ : ℝ≥0} (hδ : δ ≤ 1) {εstar : ℝ≥0∞} {B : ℝ}
    (hcard : ∀ u : WordStack F (Fin 2) (Fin n),
        ((mcaBad (F := F) C δ (u 0) (u 1)).card : ℝ) ≤ B)
    (hε : ENNReal.ofReal (B / Fintype.card F) ≤ εstar) :
    δ ≤ mcaDeltaStar (F := F) (A := F) C εstar :=
  mcaDeltaStar_ge_of_uniform_mcaBad C hδ hcard hε

/-- **The past-Johnson budget threshold, in closed form.**  The honest bridge clears the prize
budget at radius `δ` iff `B ≤ ε*·|F|`.  Specializing the entropy threshold: with the (worst-case)
list budget `B` and the relation `log₂ B = log₂(q·ε*)`, the implied floor is
`δ* ≥ 1 − ρ − H(ρ)/log₂ B`, which is past Johnson `1 − √ρ` exactly when
`log₂ B > H(ρ)/(√ρ − ρ)`.  This records the *threshold arithmetic* (the part of E04 that is
correct): the past-Johnson gate is `log₂ B > H(ρ)/(√ρ − ρ)`, and `Φ = H(ρ)/log₂ B`.  We state it
as the real inequality the budget must satisfy. -/
theorem pastJohnson_threshold_correct {ρ B : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hbudget : Real.binEntropy ρ / (Real.sqrt ρ - ρ) < Real.logb 2 B) :
    Real.binEntropy ρ / Real.logb 2 B < Real.sqrt ρ - ρ := by
  have hsqrt : ρ < Real.sqrt ρ := by
    have h1 : Real.sqrt ρ * Real.sqrt ρ = ρ := Real.mul_self_sqrt hρ0.le
    nlinarith [Real.sqrt_nonneg ρ, Real.sqrt_pos.mpr hρ0]
  have hden : 0 < Real.sqrt ρ - ρ := by linarith
  have hH : 0 < Real.binEntropy ρ := Real.binEntropy_pos hρ0 hρ1
  have hlog : 0 < Real.logb 2 B := lt_trans (div_pos hH hden) hbudget
  rw [div_lt_iff₀ hlog]
  rw [div_lt_iff₀ hden] at hbudget
  linarith

end ArkLib.ProximityGap.E04Bridge

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.E04Bridge.le_mcaDeltaStar_of_worstCaseListBudget
#print axioms ArkLib.ProximityGap.E04Bridge.pastJohnson_threshold_correct
