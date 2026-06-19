/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteCompletionCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueThinFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The normalized SOTA corridor: Shaw value of the worst period under √q-completion (#444)

`ConcreteCompletionCeiling.worstPeriod_torsion_le_sqrt_card` gives the classical √q-completion ceiling
`M(μ_d) ≤ √q` on the worst period. `ShawValueCapstone.shawValue` is the prize-normalized statistic
`Sh(M) = M / √(n·L)`. This file ties them: the SOTA completion ceiling, expressed in prize-normalized
units, is the concrete statement of "where the current best sits relative to the prize target".

> `shawValue_worstPeriod_torsion_le_sqrt_card` :
>     `Sh(M(μ_d)) ≤ √q / √(n·L)`  ( = `√(q/(n·L))` ),

over the real periods `η_b = ∑_{y∈μ_d} ψ(b·y)`. The prize CORE is `M(μ_n) ≤ C·√(n·log(p/n))`, i.e.
`Sh(M(μ_n)) ≤ C` (`O(1)`) at `L = log(p/n)`; this rung shows the unconditional baseline currently
proven is `Sh(M(μ_n)) ≤ √(q/(n·L))`, a factor `√(q/(n·L)) = n^{(β−1)/2}/√L` ABOVE the prize target in
the thin regime `n = 2^a`, `q = n^β`. The prize IS closing exactly this normalized gap.

## Honesty (this is the SOTA baseline normalized, not the prize)

Pure composition of two existing in-tree facts (the √q ceiling + the Shaw division-by-scale step).
No analytic content, no saving, no anti-concentration. CORE `Sh(M(μ_n)) = O(1)` stays OPEN; this
records the concrete normalized starting line.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteCompletionCeiling
open ProximityGap.Frontier.ConcreteShawValueThinFloor

namespace ProximityGap.Frontier.ConcreteShawCompletionCorridor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The normalized √q-completion ceiling on the Shaw value.** For a `d`-torsion subgroup `μ_d`
(`d ∣ q−1`, `d > 0`) the prize-normalized worst period satisfies `Sh(M(μ_d)) ≤ √q / scale`, where
`scale = prizeScale (|μ_d|) L = √(|μ_d|·L)`. Composes the concrete √q-completion ceiling
(`worstPeriod_torsion_le_sqrt_card`) with the Shaw division-by-scale step. At `L = log(p/n)` this is
the unconditional baseline `Sh(M(μ_n)) ≤ √(q/(n·L))` that the prize target `Sh = O(1)` tightens. -/
theorem shawValue_worstPeriod_torsion_le_sqrt_card {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hne : (nonzeroFreqs F).Nonempty) {L : ℝ}
    (hs : 0 < prizeScale ((torsion F d).card : ℝ) L) :
    shawValue (worstPeriod ψ (torsion F d) hne) ((torsion F d).card : ℝ) L
      ≤ Real.sqrt (Fintype.card F) / prizeScale ((torsion F d).card : ℝ) L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right
    (worstPeriod_torsion_le_sqrt_card hd hd0 hψ hne) (le_of_lt hs)

/-- **The normalized concrete completion corridor on the real torsion-subgroup period.**  In the
thin regime `q ≥ 2d`, the clean Plancherel floor and classical completion ceiling combine in Shaw
units as
`1 / sqrt (2L) ≤ Sh(M(μ_d)) ≤ sqrt q / sqrt(|μ_d| L)`.
This is the concrete door-(iv) starting corridor: the lower endpoint is the normalized RMS floor,
while the upper endpoint is the normalized door-(ii) completion scale.  No cancellation or
anti-concentration estimate is asserted. -/
theorem shawValue_worstPeriod_torsion_completion_corridor {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (hne : (nonzeroFreqs F).Nonempty)
    (hd1 : 1 ≤ (d : ℝ))
    (hq2d : 2 * (d : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale ((torsion F d).card : ℝ) L) :
    1 / Real.sqrt (2 * L)
        ≤ shawValue (worstPeriod ψ (torsion F d) hne) ((torsion F d).card : ℝ) L
      ∧ shawValue (worstPeriod ψ (torsion F d) hne) ((torsion F d).card : ℝ) L
        ≤ Real.sqrt (Fintype.card F) / prizeScale ((torsion F d).card : ℝ) L := by
  have hcard : ((torsion F d).card : ℝ) = (d : ℝ) := by
    rw [card_torsion hd hd0]
  refine ⟨?_, shawValue_worstPeriod_torsion_le_sqrt_card hd hd0 hψ hne hs⟩
  have hfloor := shawValue_worstPeriod_floor_clean (ψ := ψ) hψ (torsion F d) hne
    (by rwa [hcard]) (by rwa [hcard]) hs
  exact hfloor

end ProximityGap.Frontier.ConcreteShawCompletionCorridor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteShawCompletionCorridor.shawValue_worstPeriod_torsion_le_sqrt_card
#print axioms ProximityGap.Frontier.ConcreteShawCompletionCorridor.shawValue_worstPeriod_torsion_completion_corridor
