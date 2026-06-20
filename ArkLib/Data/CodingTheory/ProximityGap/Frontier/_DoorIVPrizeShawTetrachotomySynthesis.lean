/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Lane-2 synthesis capstone: the prize is *both* a bounded Shaw value *and* a door-(iv)-only target

This module is the single citable Lane-2 synthesis for the proximity prize (#444).  It welds the two
previously *disconnected* Lane-2/3 capstones into one kernel-checked statement:

* `ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound` — the prize-family
  reduction `prize ⇔ Sh(n)=O(1)` (the worst-frequency sup family is uniformly prize-bounded iff the
  normalized Shaw values are uniformly bounded by an absolute constant); and
* `NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV` — the no-fifth-door exclusion (any mechanism
  whose certified scale reaches the prize floor `√n` must be a door-(iv) `newEvaluation` mechanism,
  given the proven classical-overshoot refutations of doors (i)-(iii)).

No file in the repository imported both before; this is the first kernel-checked bridge between the
*normalization* capstone (Shaw value) and the *mechanism-classification* capstone (tetrachotomy).

## What this module proves (and what it does NOT)

It packages the **conjunction** of the two established facts as one statement, so a citation can point
at a single theorem for the prose claim:

> "The proximity prize is exactly the demand that the normalized Shaw value be `O(1)`, and the only
>  mechanism that can deliver it is door (iv) (a genuinely new evaluation of the monomial sum)."

It does **not** prove the prize inequality, does **not** give any anti-concentration / cancellation
estimate for the monomial phase set, and does **not** claim door (iv) is achievable.  Both inputs are
pure restatements / exclusions; the open problem (a door-(iv) bound) is exactly as open as before.

Note the two namespaces use *different* normalizations on purpose, and we keep them apart:
`ShawValueCapstone.prizeScale n L = √(n·L)` is the BGK-shaped target used for the `O(1)` family
reduction; `NoFifthDoorTetrachotomy.prizeScale n = √n` is the prize *floor* used for the mechanism
exclusion.  The synthesis below references each through its own namespace so no normalization is
silently conflated.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis

open ArkLib.ProximityGap.Frontier

/-- **Synthesis capstone (conjunctive form).**

Given a parameter family of thin instances with pointwise positive Shaw-prize scale `√(nᵢ·Lᵢ)`, and
given the proven classical-overshoot refutations at a fixed reference instance `(n, L)` with `L > 1`,
the following two facts hold *simultaneously*:

1. **Reduction.**  The family admits an absolute raw prize constant `C` (`Mᵢ ≤ C·√(nᵢ·Lᵢ)` for all `i`)
   **iff** it admits an absolute Shaw-value constant `C` (`Sh(Mᵢ) ≤ C` for all `i`).  This is the
   `prize ⇔ Sh(n)=O(1)` reduction.

2. **Mechanism exclusion.**  At the reference instance, *every* mechanism whose certified scale reaches
   the prize floor `√n` is a door-(iv) `newEvaluation` mechanism; no classical door (moment /
   completion / extreme-value) survives.

This is the single Lane-2 statement behind the prose "the prize is a bounded Shaw value, deliverable
only through door (iv)."  No cancellation/anti-concentration estimate is asserted. -/
theorem prize_iff_shawBounded_and_doorIV_only
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ((∃ C, ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_⟩
  · exact ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound hs
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **Contrapositive packaging of the mechanism side.**  If, at the reference instance, the prize
family is *not* Shaw-bounded (no absolute `C`), the door-(iv) exclusion still holds verbatim: the
mechanism-classification fact is independent of whether the prize is actually achievable.  This
records that the no-fifth-door exclusion is unconditional on the (open) reduction outcome. -/
theorem doorIV_only_independent_of_reduction
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ∀ m : NoFifthDoorTetrachotomy.Mechanism,
      m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
      m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **Nonnegative-constant synthesis.**  The reduction half, in the sign-normalized constant form
usually quoted in prose (`prize iff Sh(n)=O(1)` with a *nonnegative* absolute constant), conjoined
with the same door-(iv) exclusion.  The nonnegative form is the one most directly cited. -/
theorem prize_iff_shawBounded_nonneg_and_doorIV_only
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ((∃ C, 0 ≤ C ∧ ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_⟩
  · exact
      ShawValueCapstone.exists_nonneg_rawPrizeFamilyBound_iff_exists_nonneg_shawValueFamilyBound hs
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

/-- **The remaining gap is a single `√L` factor, and it is door-(iv)-only.**  Conjoins the
quantitative door-(iv) obligation (the BGK ceiling exceeds the prize floor by exactly the factor
`√L`, so the corridor `[√n, √(n·L)]` has positive width in the regime `L > 1`) with the exclusion
(only door (iv) can shave that factor).  This is the crispest one-line statement of "what is left." -/
theorem remaining_gap_is_sqrtL_factor_doorIV_only
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (NoFifthDoorTetrachotomy.prizeScale nref < NoFifthDoorTetrachotomy.bgkScale nref Lref) ∧
      (NoFifthDoorTetrachotomy.bgkScale nref Lref =
        Real.sqrt Lref * NoFifthDoorTetrachotomy.prizeScale nref) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) := by
  refine ⟨?_, ?_, ?_⟩
  · exact NoFifthDoorTetrachotomy.doorIV_corridor_width_pos hnref hLref
  · exact NoFifthDoorTetrachotomy.bgkScale_eq_sqrtL_mul_prizeScale (le_of_lt hnref)
      (le_of_lt (lt_trans one_pos hLref))
  · exact NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hnref hLref hclassicalOvershoots

end ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis
