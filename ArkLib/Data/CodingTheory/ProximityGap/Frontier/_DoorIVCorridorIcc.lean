/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The door-(iv) target corridor as a genuine `Set.Icc` (#444, Lane 2 capstone packaging)

`_NoFifthDoorTetrachotomy.lean` pins the worst-frequency sup `M` to the corridor
`[prizeScale n, bgkScale n L] = [√n, √(n·L)]` via `mem_doorIV_corridor`, but that theorem returns a
bare conjunction `prizeScale n ≤ M ∧ M ≤ bgkScale n L`.  This module packages the corridor as a real
`Set.Icc`, so downstream statements can use the order-theoretic interface (`Set.mem_Icc`,
`Set.Nonempty`, `Set.Icc_subset_Icc`, monotonicity) instead of re-deriving the two-sided bound.

Contents (all axiom-clean, pure order/`Real.sqrt` bookkeeping — no analytic/CORE claim):

* `doorIVCorridor` — the interval `Set.Icc (prizeScale n) (bgkScale n L)` as a named set;
* `mem_doorIVCorridor_iff` — `M ∈ doorIVCorridor ↔ √n ≤ M ∧ M ≤ √(n·L)` (the `Set.Icc` bridge);
* `mem_doorIVCorridor_of_bounds` / `prizeScale_mem` / `not_mem_of_lt_prizeScale` — membership in/out;
* `doorIVCorridor_nonempty` — the corridor is nonempty in the prize regime `L > 1`;
* `prizeScale_lt_of_mem_of_ne` — a corridor point strictly above the floor is genuinely interior-ish;
* `doorIVCorridor_subset_of_le` — corridor monotonicity in the thinness index `L`.

**Scope / honesty.** Pure reduction/packaging of the already-proven corridor endpoints into the
`Set.Icc` interface.  No CORE / cancellation / completion / moment / anti-concentration / capacity
claim; the corridor *width* `√L` is the door-(iv) obligation and is NOT shaved here.
-/

namespace ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy Set

/-- The door-(iv) target corridor as a `Set.Icc`: the closed interval
`[prizeScale n, bgkScale n L] = [√n, √(n·L)]` in which the worst-frequency sup `M` lives. -/
noncomputable def doorIVCorridor (n L : ℝ) : Set ℝ :=
  Set.Icc (prizeScale n) (bgkScale n L)

/-- **The `Set.Icc` bridge.**  `M` is in the door-(iv) corridor exactly when it satisfies the
Plancherel floor and the BGK ceiling: `√n ≤ M ≤ √(n·L)`. -/
theorem mem_doorIVCorridor_iff {n L M : ℝ} :
    M ∈ doorIVCorridor n L ↔ prizeScale n ≤ M ∧ M ≤ bgkScale n L := by
  unfold doorIVCorridor
  exact Set.mem_Icc

/-- Build corridor membership from the two proven bounds (the `Set.Icc` form of
`mem_doorIV_corridor`). -/
theorem mem_doorIVCorridor_of_bounds {n L M : ℝ}
    (hfloor : prizeScale n ≤ M) (hceil : M ≤ bgkScale n L) :
    M ∈ doorIVCorridor n L :=
  mem_doorIVCorridor_iff.mpr ⟨hfloor, hceil⟩

/-- The prize floor itself sits in the corridor in the prize regime `L > 1` (the lower endpoint is the
prize target). -/
theorem prizeScale_mem_doorIVCorridor {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    prizeScale n ∈ doorIVCorridor n L :=
  mem_doorIVCorridor_of_bounds le_rfl (le_of_lt (prizeScale_lt_bgkScale hn hL))

/-- **Nothing below the Plancherel floor is in the corridor.**  A value strictly under `√n` cannot be
the worst-frequency sup: the prize floor is a hard lower endpoint. -/
theorem not_mem_doorIVCorridor_of_lt_prizeScale {n L M : ℝ} (hM : M < prizeScale n) :
    M ∉ doorIVCorridor n L := by
  rw [mem_doorIVCorridor_iff]
  rintro ⟨hfloor, _⟩
  exact absurd hfloor (not_le.mpr hM)

/-- **The corridor is nonempty** in the prize regime `L > 1`: its endpoints satisfy
`√n < √(n·L)`, so the closed interval is a genuine (positive-width) interval, not empty. -/
theorem doorIVCorridor_nonempty {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    (doorIVCorridor n L).Nonempty :=
  ⟨prizeScale n, prizeScale_mem_doorIVCorridor hn hL⟩

/-- A corridor point that is not the floor is strictly above it (`√n < M`): such an `M` certifies the
door-(iv) gap is partially unpaid. -/
theorem prizeScale_lt_of_mem_doorIVCorridor_of_ne {n L M : ℝ}
    (hmem : M ∈ doorIVCorridor n L) (hne : M ≠ prizeScale n) :
    prizeScale n < M :=
  lt_of_le_of_ne ((mem_doorIVCorridor_iff.mp hmem).1) (Ne.symm hne)

/-- **Corridor monotonicity in the thinness index.**  A larger thinness index `L₁ ≤ L₂` (with `0 ≤ n`)
yields a wider BGK ceiling, hence a larger corridor: `doorIVCorridor n L₁ ⊆ doorIVCorridor n L₂`.
The floor `√n` is `L`-independent; only the ceiling `√(n·L)` grows. -/
theorem doorIVCorridor_subset_of_le {n L₁ L₂ : ℝ} (hn : 0 ≤ n) (hL : L₁ ≤ L₂) :
    doorIVCorridor n L₁ ⊆ doorIVCorridor n L₂ := by
  unfold doorIVCorridor
  apply Set.Icc_subset_Icc le_rfl
  unfold bgkScale
  exact Real.sqrt_le_sqrt (by nlinarith [hn])

end ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy
