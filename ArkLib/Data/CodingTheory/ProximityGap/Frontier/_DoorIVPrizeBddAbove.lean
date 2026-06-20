/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassEquivalence

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv): the prize-family bound is exactly `BddAbove` of the normalized ratios (#444)

## Context

`_DoorIVHalfMassEquivalence` packages the honest door-(iv) Big-O reduction `prize ⇔ H(n)=O(scale)`
using a bespoke existential predicate
`∃ C, normalizedPrizeFamilyBound M scale C := ∃ C, ∀ i, M i / scale i ≤ C`,
i.e. "the normalized prize ratios `M i / scale i` are bounded above by some constant".

That existential is, definitionally, Mathlib's canonical `BddAbove (Set.range fun i => M i / scale i)`.
The two worst-b probes logged in `DISPROOF_LOG.md`
(`[doorIV-worstb-coherence-constant-prime-stable]`, `[doorIV-worstb-coherence-constant-n-drift-saturates]`)
measure *exactly* this object: whether the family `C(n) = ρ²(b*)·n/log(p/n)` of normalized ratios is
bounded above (the prize) or drifts to `∞` (the wall). This file welds the bespoke door-(iv) predicate
to the standard library boundedness predicate, so the door-(iv) Big-O capstone becomes interoperable
with Mathlib's `BddAbove`/`Set.range` API (and with anything stated in those terms, e.g. the empirical
`BddAbove` question the probes target).

## What this file proves (axiom-clean, no new estimate)

- `bddAbove_range_iff_exists_normalizedPrizeFamilyBound`: the `BddAbove (range (M/scale))` form is
  equivalent to the bespoke `∃ C, normalizedPrizeFamilyBound M scale C`.
- `bddAbove_range_iff_exists_normalizedHalfMassFamilyBound`: same for the half-mass ratios.
- `bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound`: with positive scales, `BddAbove` of the
  normalized prize ratios is equivalent to the RAW prize Big-O bound `∃ C, M ≤ C·scale`.
- `bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass`: the door-(iv) reduction itself,
  stated purely in `BddAbove` terms (the directly citable form: `prize ⇔ Sh_H(n)=O(1)` as boundedness
  of the half-mass Shaw value).

This is a pure restatement bridge — it proves NO arithmetic inequality, no cancellation, no CORE bound.
It only identifies the existing door-(iv) predicate with the standard `BddAbove`, which is the object the
worst-b probes empirically interrogate.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove

open ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence

/-- A family of reals is bounded above (`BddAbove` of its range) iff there is a uniform upper bound
on every member. This is the elementary unfolding of `BddAbove (Set.range f)` for `f : ι → ℝ`. -/
theorem bddAbove_range_iff_exists_forall_le {ι : Type*} (f : ι → ℝ) :
    BddAbove (Set.range f) ↔ ∃ C, ∀ i, f i ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun i => ?_⟩
    exact hC ⟨i, rfl⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro x ⟨i, rfl⟩
    exact hC i

/-- The bespoke normalized prize-family predicate is exactly `BddAbove` of the normalized prize
ratios. -/
theorem bddAbove_range_iff_exists_normalizedPrizeFamilyBound {ι : Type*} (M scale : ι → ℝ) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, normalizedPrizeFamilyBound M scale C := by
  rw [bddAbove_range_iff_exists_forall_le]
  rfl

/-- The bespoke normalized half-mass-family predicate is exactly `BddAbove` of the normalized
half-mass ratios. -/
theorem bddAbove_range_iff_exists_normalizedHalfMassFamilyBound {ι : Type*} (H scale : ι → ℝ) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, normalizedHalfMassFamilyBound H scale C := by
  rw [bddAbove_range_iff_exists_forall_le]
  rfl

/-- With positive scales, `BddAbove` of the normalized prize ratios is equivalent to the RAW prize
Big-O statement `∃ C, ∀ i, M i ≤ C · scale i`. This is the standard-library form of the door-(iv)
prize predicate the worst-b probes measure. -/
theorem bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, prizeFamilyBound M scale C := by
  rw [bddAbove_range_iff_exists_normalizedPrizeFamilyBound]
  exact (exists_prizeFamilyBound_iff_exists_normalizedPrizeFamilyBound
    (M := M) (scale := scale) hscale).symm

/-- **Door-(iv) reduction in `BddAbove` form.**  Under the family-wide half-mass comparison
(`M i ≤ H i` and `H i ≤ K · M i` with one `K ≥ 0`) and positive scales, the normalized prize ratios are
bounded above iff the normalized half-mass ratios are. This is the directly citable
`prize ⇔ Sh_H(n)=O(1)` stated entirely via Mathlib's `BddAbove`. -/
theorem bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      BddAbove (Set.range fun i => H i / scale i) := by
  rw [bddAbove_range_iff_exists_normalizedPrizeFamilyBound,
      bddAbove_range_iff_exists_normalizedHalfMassFamilyBound]
  exact exists_normalizedPrizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    (M := M) (H := H) (scale := scale) hK hscale hMH hHM

end ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove

#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_forall_le
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_normalizedPrizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_normalizedHalfMassFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_prizeFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_bddAbove_range_normalizedHalfMass
