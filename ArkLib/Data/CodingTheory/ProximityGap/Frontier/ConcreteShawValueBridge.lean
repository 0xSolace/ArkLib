/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteTrivialCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Wiring the Shaw-value capstone onto the CONCRETE worst period (#444)

`ShawValueCapstone` states the normalization equivalence `prize ⇔ Sh(n)=O(1)` and the floor/ceiling
rungs on an **abstract** raw worst-frequency size `M : ℝ`. `ConcreteTrivialCeiling` /
`ConcreteParsevalLower` prove the **concrete** floor `√(n(q−n)/(q−1)) ≤ M(μ_n)` and ceiling
`M(μ_n) ≤ |G|` over the real periods `η_b = ∑_{y∈G} ψ(b·y)`, with `M(μ_n) = worstPeriod ψ G hne`.

This file is the missing CONNECTIVE rung: it instantiates the abstract capstone bookkeeping with the
concrete `worstPeriod`, so the normalized Shaw value of the REAL character sum carries an in-tree
upper bound (and the concrete RMS floor), without any caller re-discharging the `M ≤ n` hypothesis.

> `shawValue_worstPeriod_le_of_card`  : `Sh(M(μ_n)) ≤ |G| / scale`, from the concrete ceiling `M ≤ |G|`,
> `shawValue_worstPeriod_rms_floor`   : `√(n(q−n)/(q−1)) / scale ≤ Sh(M(μ_n))`, from the concrete
>                                       Parseval/RMS floor,
> `shawValue_worstPeriod_bracket`     : the two together — the concrete normalized corridor for the
>                                       real worst period.

Here `Sh(M) = shawValue M (G.card) L = M / prizeScale (G.card) L`, `prizeScale n L = √(n·L)`, the
Shaw-value normalization. The HONEST floor uses the true RMS quantity `√(n(q−n)/(q−1))` (the
unconditional Parseval value), NOT the rounded `√n` — the capstone's clean-`√n` floor rung is a
slightly stronger hypothesis that the unconditional second-moment identity does not supply.

## Honesty (the prize is the GAP, untouched)

This is pure Lane-2 INSTANTIATION: it plugs the concrete real-period bounds into the abstract
normalization bookkeeping. It adds NO analytic content — no anti-concentration, no cancellation, no
completion, no moment, no capacity claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` (equivalently
`Sh(M(μ_n)) = O(1)` at `L = log(p/n)`) stays OPEN; it lives strictly inside the proven normalized
`√((q−n)/(q−1)·L⁻¹) .. √(n/L)` corridor supplied here.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteMomentAssembly
open ProximityGap.Frontier.ConcreteParsevalLower
open ProximityGap.Frontier.ConcreteTrivialCeiling

namespace ProximityGap.Frontier.ConcreteShawValueBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Concrete normalized ceiling for the real worst period.** The Shaw value of the actual character
sum `M(μ_n) = max_{b≠0}‖η_b‖` is bounded by `|G| / scale`. Instantiates the abstract capstone rung
`shawValue_le_of_trivial_ceiling` with the concrete `M ≤ |G|` (`worstPeriod_le_card`). -/
theorem shawValue_worstPeriod_le_of_card {ψ : AddChar F ℂ} (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    shawValue (worstPeriod ψ G hne) (G.card : ℝ) L ≤ (G.card : ℝ) / prizeScale (G.card : ℝ) L :=
  shawValue_le_of_trivial_ceiling hs (worstPeriod_le_card ψ G hne)

/-- **Concrete normalized RMS floor for the real worst period.** The unconditional Parseval floor
`√(n(q−n)/(q−1)) ≤ M(μ_n)` (`worstPeriod_ge_sqrt_parseval`) passes through Shaw normalization:
`√(n(q−n)/(q−1)) / scale ≤ Sh(M(μ_n))`. Honest: uses the true RMS value, not a rounded `√n`. -/
theorem shawValue_worstPeriod_rms_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
        / prizeScale (G.card : ℝ) L
      ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right (worstPeriod_ge_sqrt_parseval hψ G hne hq1) (le_of_lt hs)

/-- **Concrete normalized corridor for the real worst period.** Both the RMS floor and the trivial
ceiling, normalized by the Shaw scale, around the Shaw value of the actual character sum
`M(μ_n) = max_{b≠0}‖η_b‖`. The prize target `Sh(M(μ_n)) = O(1)` (at `L = log(p/n)`) lives strictly
inside this proven corridor. -/
theorem shawValue_worstPeriod_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) {L : ℝ}
    (hs : 0 < prizeScale (G.card : ℝ) L) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
          / prizeScale (G.card : ℝ) L
        ≤ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ shawValue (worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ (G.card : ℝ) / prizeScale (G.card : ℝ) L :=
  ⟨shawValue_worstPeriod_rms_floor hψ G hne hq1 hs, shawValue_worstPeriod_le_of_card G hne hs⟩

end ProximityGap.Frontier.ConcreteShawValueBridge
