/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WeilRegimeClosure

/-!
# A RESIDUAL-FREE end-to-end instance (#389)

The general wall closure (`wall_closes_in_weil_regime`) is conditional on the standard
Weil energy bound.  This file discharges that bound *by computation* for a concrete
deployed-shape instance, giving a **fully residual-free** end-to-end Garcia–Voloch
representation bound — every hypothesis decided, no open input.

`G = μ_6 ⊆ F_37` (the 6th roots of unity, `{1,10,11,26,27,36}`): its additive energy is
`E = 90 = 3·6²−3·6`, so `energyExcess G = 0` — `μ_6` is *exactly* Sidon-modulo-negation
(matching the `n²/p → 0` prediction).  Feeding `energyExcess = 0` (i.e. `C = 0`) into
`gvRepBound_of_energyExcess_quadratic` yields, with no residual:

> **`mu6_F37_gvRepBound`** — `GVRepBound (μ_6 ⊆ F_37) 5`: every nonzero `t` has at most
> `5` additive representations, the optimal `√(3·6) ≈ 4.2` scale.

This is the complete supply-wall closure realised end-to-end on a concrete subgroup,
demonstrating that the `δ*`-pinning machinery is residual-free once the energy is known.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- `μ_6 ⊆ F_37`, the 6th roots of unity. -/
def mu6 : Finset (ZMod 37) := {1, 10, 11, 26, 27, 36}

/-- **Residual-free end-to-end Garcia–Voloch bound for `μ_6 ⊆ F_37`.**  Every hypothesis
— including the energy (excess `= 0`) — is discharged by `decide`; no open input. -/
theorem mu6_F37_gvRepBound : GVRepBound mu6 5 :=
  gvRepBound_of_energyExcess_quadratic (G := mu6) (n := 6) (C := 0) (M := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms mu6_F37_gvRepBound
