/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CensusScalarPartition

/-!
# The MULTI-SCALAR census necessity floor (#444)

`CensusCapForbidsLargeAligned`/`CensusCapForcedBelow` force the census `#alignableSets` from below by
the subset supply of a SINGLE large aligned set: `C(|A| − (k+1), a − (k+1)) ≤ #alignableSets`.  This
file sharpens that to the **multi-scalar** floor using the exact census partition
`#alignableSets = Σ_γ #alignedSetsForScalar(γ)` (`CensusScalarPartition.alignableSets_card_eq_sum`,
the parts disjoint by `alignedSetsForScalar_disjoint`).

**The mechanism.**  Distinct bad scalars own DISJOINT families of aligned sets (a non-degenerate
aligned set pins its scalar uniquely, `Aligned.gamma_eq`).  So if `P` distinct scalars each align a
set of size `≥ a` carrying a non-degenerate `(k+1)`-tuple, their per-scalar supplies
`C(|A_γ| − (k+1), a − (k+1))` (`mult_ge_choose_of_aligned_superset`) ADD into the census:

> **`Σ_{γ∈P} C(|A_γ| − (k+1), a − (k+1)) ≤ #alignableSets`**  (`sum_choose_le_alignableSets`),

and in particular, when every witnessing set is the FULL domain (`|A_γ| = n`, the prize band),

> **`#P · C(n − (k+1), a − (k+1)) ≤ #alignableSets`**  (`card_mul_choose_le_alignableSets`).

So a census cap `K` simultaneously bounds the NUMBER of bad scalars and the SIZE of each one's
aligned set: `#P ≤ K / C(n − (k+1), a − (k+1))`.  This is the necessity-side companion to the
forward weld (`epsMCA_le_of_alignableSets_card_le`), strictly sharper than the single-set floor
because it accumulates over the disjoint scalar parts — the partition structure the census actually
has.

**Honest scope.**  Pure logical/combinatorial assembly of the proven per-scalar supply floor across
the proven disjoint census partition.  NOT a CORE closure, NOT thinness-essential, NO capacity /
beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched).  It does not bound `#alignableSets`
itself — the open `M(μ_n) ≤ C√(n·log(p/n))` CORE (equivalently `#alignableSets ≤ rm+1`) stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ}

open Classical in
/-- **The multi-scalar census supply floor.**  Given a finset `P` of scalars, and for each `γ ∈ P` a
`γ`-aligned set `A γ` of size `≥ a` carrying a non-degenerate `(k+1)`-tuple `t γ`, the per-scalar
subset supplies sum into the census: `Σ_{γ∈P} C(|A γ| − (k+1), a − (k+1)) ≤ #alignableSets`.  The
parts are DISJOINT (`alignedSetsForScalar_disjoint`), so summing the per-scalar floors
(`mult_ge_choose_of_aligned_superset`) under the partition `alignableSets_card_eq_sum` is valid. -/
theorem sum_choose_le_alignableSets (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) (hka : k + 1 ≤ a)
    (P : Finset F) (A : F → Finset (Fin n)) (t : F → Fin (k + 1) → Fin n)
    (halign : ∀ γ ∈ P, Aligned dom k u₀ u₁ γ (A γ))
    (htinj : ∀ γ ∈ P, Function.Injective (t γ))
    (htmem : ∀ γ ∈ P, ∀ b, (t γ) b ∈ A γ)
    (hnd : ∀ γ ∈ P, ¬ (residual dom k (t γ) u₀ = 0 ∧ residual dom k (t γ) u₁ = 0)) :
    ∑ γ ∈ P, ((A γ).card - (k + 1)).choose (a - (k + 1))
      ≤ (alignableSets dom k a u₀ u₁).card := by
  classical
  -- per-scalar floor ≤ per-scalar census part
  have hper : ∀ γ ∈ P, ((A γ).card - (k + 1)).choose (a - (k + 1))
      ≤ (alignedSetsForScalar dom k a u₀ u₁ γ).card := by
    intro γ hγ
    exact mult_ge_choose_of_aligned_superset dom k a u₀ u₁ γ
      (halign γ hγ) (htinj γ hγ) (htmem γ hγ) (hnd γ hγ) hka
  -- sum of per-scalar floors over P ≤ sum of per-scalar census parts over P
  have h1 : ∑ γ ∈ P, ((A γ).card - (k + 1)).choose (a - (k + 1))
      ≤ ∑ γ ∈ P, (alignedSetsForScalar dom k a u₀ u₁ γ).card :=
    Finset.sum_le_sum hper
  -- sum over P ≤ sum over all F (the parts are nonneg) = census
  have h2 : ∑ γ ∈ P, (alignedSetsForScalar dom k a u₀ u₁ γ).card
      ≤ ∑ γ : F, (alignedSetsForScalar dom k a u₀ u₁ γ).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ P)
  rw [← alignableSets_card_eq_sum dom k a u₀ u₁] at h2
  exact le_trans h1 h2

open Classical in
/-- **The full-domain multi-scalar floor (prize band).**  If `P` distinct scalars each align the
WHOLE domain `univ` (`|A γ| = n`) with a non-degenerate `(k+1)`-tuple, the census dominates
`#P · C(n − (k+1), a − (k+1))`.  Hence a census cap `K` bounds the number of such bad scalars:
`#P ≤ K / C(n − (k+1), a − (k+1))` — the cap controls BOTH the count and the per-scalar size. -/
theorem card_mul_choose_le_alignableSets (dom : Fin n ↪ F) {k a : ℕ}
    (u₀ u₁ : Fin n → F) (hka : k + 1 ≤ a)
    (P : Finset F) (t : F → Fin (k + 1) → Fin n)
    (halign : ∀ γ ∈ P, Aligned dom k u₀ u₁ γ (Finset.univ : Finset (Fin n)))
    (htinj : ∀ γ ∈ P, Function.Injective (t γ))
    (hnd : ∀ γ ∈ P, ¬ (residual dom k (t γ) u₀ = 0 ∧ residual dom k (t γ) u₁ = 0)) :
    P.card * (n - (k + 1)).choose (a - (k + 1)) ≤ (alignableSets dom k a u₀ u₁).card := by
  classical
  have hcardeq : (Finset.univ : Finset (Fin n)).card = n := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hfloor := sum_choose_le_alignableSets dom u₀ u₁ hka P
    (fun _ => (Finset.univ : Finset (Fin n))) t halign htinj
    (fun γ _ b => Finset.mem_univ _) hnd
  -- each summand is C(n - (k+1), a - (k+1)); the sum is #P times that
  have hconst : ∑ γ ∈ P, ((Finset.univ : Finset (Fin n)).card - (k + 1)).choose (a - (k + 1))
      = P.card * (n - (k + 1)).choose (a - (k + 1)) := by
    rw [Finset.sum_const, smul_eq_mul, hcardeq]
  rwa [hconst] at hfloor

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.sum_choose_le_alignableSets
#print axioms ProximityGap.Ownership.card_mul_choose_le_alignableSets
