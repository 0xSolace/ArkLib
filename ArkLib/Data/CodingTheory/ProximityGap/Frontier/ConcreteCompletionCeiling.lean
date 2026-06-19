/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteMomentAssembly
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumWorstCase

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The CONCRETE √q-completion ceiling on the worst period for torsion subgroups (#444)

`SubgroupGaussSumWorstCase.norm_eta_torsion_le` proves the classical Gauss-sum **completion** bound
`‖η_b‖ ≤ √q` for EVERY nonzero frequency `b` over a `d`-torsion subgroup `μ_d = {y : y^d = 1}`
(`d ∣ q−1`) — the pointwise SOTA baseline. It was never lifted to the worst nonzero period
`M(μ_d) = max_{b≠0} ‖η_b‖ = worstPeriod ψ (torsion F d) hne`.

This file supplies that lift:

> `worstPeriod_torsion_le_sqrt_card` : `M(μ_d) ≤ √q`.

The `μ_n` of the prize regime is exactly a `2`-power torsion subgroup, so this is the named
**√q-completion ceiling** rung: the classical baseline the prize must BEAT. The prize CORE asks for
`M(μ_n) ≤ C·√(n·log(p/n))`, which in the thin regime `n = 2^a`, `q = n^β` (`β ≈ 4-5`) is
`≈ √n·√log q ≪ √q = n^{β/2}` — i.e. the prize is a SAVING of `n^{(β−1)/2}/√log` over this completion
ceiling. Lifting `norm_eta_torsion_le` to the sup is the elementary `sup'_le` step.

## Honesty (the completion ceiling is the SOTA baseline, not the prize)

`√q` is the trivial completion bound (every individual period is a completed Gauss sum of modulus
`≤ √q`); beating it on THIN smooth subgroups by the prize factor is the entire open problem. This
file is pure consolidation: it states the well-known completion ceiling at the worst-period level so
the prize SAVING can be cited against a concrete in-tree quantity. CORE `M(μ_n) ≤ C·√(n·log(p/n))`
stays OPEN — no cancellation/anti-concentration/saving is claimed here.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ProximityGap.Frontier.ConcreteMomentAssembly

namespace ProximityGap.Frontier.ConcreteCompletionCeiling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The √q-completion ceiling on the worst period.** For a `d`-torsion subgroup `μ_d` (`d ∣ q−1`,
`d > 0`) of a finite field, the worst nonzero period satisfies `M(μ_d) ≤ √q`. The worst period is a
sup' of `‖η_b‖` over nonzero `b`, each `≤ √q` by the classical completion bound `norm_eta_torsion_le`;
take the sup. The prize regime's `μ_n` is a `2`-power torsion subgroup, so this is the classical
completion ceiling that the prize CORE `M ≤ C·√(n·log(p/n))` must beat. -/
theorem worstPeriod_torsion_le_sqrt_card {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hne : (nonzeroFreqs F).Nonempty) :
    worstPeriod ψ (torsion F d) hne ≤ Real.sqrt (Fintype.card F) := by
  unfold worstPeriod
  refine Finset.sup'_le hne _ ?_
  intro b hb
  have hb0 : b ≠ 0 := by rw [← mem_nonzeroFreqs]; exact hb
  exact norm_eta_torsion_le hd hd0 hψ hb0

end ProximityGap.Frontier.ConcreteCompletionCeiling
