/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeShawTetrachotomySynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentTrappedCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentCorridor

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Grand capstone: prize ⇔ Sh=O(1), door-(iv)-only, AND the door-(iv) object is moment-trapped (#444)

This module is the single top-level citable statement of the #444 campaign's structural result. It is
the FIRST file in the repository connecting the **mechanism-level** synthesis
(`_DoorIVPrizeShawTetrachotomySynthesis`: the prize ⇔ bounded-Shaw-value reduction together with the
no-fifth-door door-(iv)-only exclusion) with the **object-level** closure
(`_DoorIVObjectMomentTrappedCapstone` + `_DoorIVObjectMomentCorridor`: the single live door-(iv) open
object is itself moment-trapped and corridor-pinned). No file imported all three before.

The campaign's prose synthesis (Shaw's "Shaw Value" essay) reads:

> "The proximity prize is exactly the demand that the normalized Shaw value be `O(1)`; the only
>  mechanism that can deliver it is door (iv) (a genuinely new evaluation of the monomial sum); and
>  even *that* sole live door's open object (the worst-frequency coset-half coherence) has, in every
>  measurement, no non-moment, non-extreme-value slack — its sup is pinned to a moment-corridor above
>  the extreme-value floor."

This capstone collects the three kernel-checked facts behind that prose into one statement, so a
citation can point at a single theorem.

## What this proves (and emphatically what it does NOT)

It packages the **conjunction** of three established, axiom-clean facts:

1. **Reduction.**  `prize ⇔ Sh(n)=O(1)` (the worst-frequency sup family is uniformly prize-bounded iff
   the normalized Shaw values are uniformly bounded).
2. **Mechanism exclusion.**  Every mechanism reaching the prize floor `√n` is a door-(iv)
   `newEvaluation` mechanism; no classical door (moment / completion / extreme-value) survives.
3. **Object trap.**  The single live door-(iv) open object's sup is *moment-trapped*: bounded below by
   the extreme-value (iid-surrogate) floor with the gap above it bounded by the additive-energy
   (moment) excess `Δ` — equivalently pinned to the corridor `[iidSup, iidSup + Δ]`.

It does **not** prove the prize inequality, does **not** give any anti-concentration / cancellation
estimate, and does **not** claim door (iv) is achievable. Facts (1)+(2) are restatements/exclusions;
fact (3) is a restatement of measured/identity facts carried as hypotheses. The open problem (a
genuinely new door-(iv) evaluation that escapes the moment corridor) is exactly as open as before. The
contribution is that the campaign's three pillars are now a single kernel-checked object: the prize is
a bounded Shaw value, deliverable only through door (iv), whose open object is — in every measurement —
moment-trapped with no non-moment slack.

Imports the three established capstones unchanged; introduces no axioms.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone

open ArkLib.ProximityGap.Frontier
open ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge
open ArkLib.ProximityGap.Frontier.DoorIVExcessIsMoment
open ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor

/-- **Grand capstone (three-pillar conjunction).**

Given the standard thin-instance positivity (`0 < prizeScale (nᵢ) (Lᵢ)`), the proven classical-
overshoot refutations at a reference instance, and the two measured/identity facts about the single
live door-(iv) object (the no-edge floor `iidSup ≤ realSup` and the excess-is-moment bound on the gap
`realSup − iidSup ≤ Δ`), all THREE pillars of the #444 campaign hold simultaneously:

1. **Reduction.**  `(∃ C ≥ 0, raw prize bound) ↔ (∃ C ≥ 0, Shaw-value bound)`.
2. **Mechanism exclusion.**  Every mechanism reaching `√nref` is door-(iv) `newEvaluation`.
3. **Object trap.**  `iidSup ≤ realSup ≤ iidSup + Δ` — the door-(iv) object's sup is pinned to a
   width-`Δ` moment-corridor above the extreme-value floor.

This is the single citable Boneh-grade structural statement: the prize is a bounded Shaw value,
deliverable only through door (iv), whose open object is moment-trapped. No cancellation /
anti-concentration estimate is asserted; CORE stays open. -/
theorem prize_iff_shawBounded_doorIV_only_and_object_moment_trapped
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref)
    {iidSup realSup Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ) :
    -- (1) reduction
    ((∃ C, 0 ≤ C ∧ ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      -- (2) door-(iv)-only mechanism exclusion
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
      -- (3) the door-(iv) object's sup is pinned to the moment-corridor
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) := by
  obtain ⟨hred, hexcl⟩ :=
    DoorIVPrizeShawTetrachotomySynthesis.prize_iff_shawBounded_nonneg_and_doorIV_only
      hs hnref hLref hclassicalOvershoots
  exact ⟨hred, hexcl, realSup_in_moment_corridor hEdge hExcess⟩

/-- **Object trap is independent of the mechanism exclusion** (modularity witness): the door-(iv)
object moment-corridor holds from the two measured facts alone, with no reference to the Shaw-value
reduction or the tetrachotomy. This records that pillar (3) is a free-standing object-level result,
not a corollary of the mechanism taxonomy — they corroborate from independent inputs. -/
theorem object_moment_trapped_independent
    {iidSup realSup Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ) :
    iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ :=
  realSup_in_moment_corridor hEdge hExcess

/-- **Both the qualitative trap and the quantitative corridor at once.**  From the two measured facts,
the door-(iv) object is moment-trapped on both sides (`¬ realSup < iidSup` and `¬ Δ < (realSup−iidSup)`)
AND pinned to the corridor `[iidSup, iidSup + Δ]`.  This is the full object-level closure in one line,
suitable to plug into pillar (3) of the grand capstone. -/
theorem object_trapped_and_corridor
    {iidSup realSup Δ : ℝ}
    (hEdge : SurrogateLeReal iidSup realSup)
    (hExcess : gap iidSup realSup ≤ Δ) :
    ((¬ realSup < iidSup) ∧ (¬ Δ < gap iidSup realSup)) ∧
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) :=
  ⟨DoorIVObjectMomentTrappedCapstone.doorIV_object_moment_trapped hEdge
      (gap_momentSourced hEdge hExcess),
   realSup_in_moment_corridor hEdge hExcess⟩

end ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone

-- Axiom audit: all theorems must be ⊆ {propext, Classical.choice, Quot.sound}
section AxiomAudit
open ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone
#print axioms prize_iff_shawBounded_doorIV_only_and_object_moment_trapped
#print axioms object_moment_trapped_independent
#print axioms object_trapped_and_corridor
end AxiomAudit
