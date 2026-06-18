/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.E2CharFreeLowerBound

/-!
# A single genuine additive quadruple forces strict `E₂` excess over the char-free floor (#444, #407)

`E2CharFreeLowerBound` proves the char-free FLOOR `E₂(S) ≥ 3|S|²−3|S|` for negation-closed `S`,
assembled from the three guaranteed families `T1` (diagonal `(a,b,a,b)`), `T2` (swap `(a,b,b,a)`),
`T3` (antipodal `(a,−a,c,−c)`).  Equality is the char-DEPENDENT near-Sidon UPPER half, which the
probes show FAILS in the deep prize regime (`scripts/probes/probe_e2_excess_*.py`): in that regime
the multiplicative subgroup `μ_n` acquires GENUINE additive coincidences — energy quadruples that
lie OUTSIDE `T1 ∪ T2 ∪ T3`.

This file makes the connection EXACT in the easy (provable, char-free) direction:

> **`E2_strictGt_of_genuineQuad`.**  If `S` is negation-closed and there exists an energy
> quadruple `q₀ ∈ energyQuads S` with `q₀ ∉ T1 ∪ T2 ∪ T3`, then `3|S|² − 3|S| < E₂(S)`.

i.e. ONE genuine additive coincidence beyond the three guaranteed families strictly lifts the
energy above the floor.  Combined with the first-Wick-step refutation (`WickStepOneEnergyThreshold`,
commit `ee4d66435`) — which shows `E₂(μ_n)` crosses its threshold exactly when this excess turns
on — this localizes the open BGK content to the EXISTENCE of a single genuine quadruple.

The proof is a one-line counting argument: `(T1 ∪ T2 ∪ T3) ∪ {q₀} ⊆ energyQuads S`, the inserted
`q₀` is new (`∉ T1∪T2∪T3`), so `E₂(S) ≥ card(T1∪T2∪T3) + 1 ≥ (3|S|²−3|S|) + 1`.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #407.
-/

open Finset

namespace ArkLib.ProximityGap.E2CharFree

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

/-- The three guaranteed families, packaged. -/
def guaranteedQuads (S : Finset F) : Finset (F × F × F × F) :=
  diagQuads S ∪ swapQuads S ∪ antiQuads S

/-- The guaranteed families are contained in the energy solution set (needs negation closure
for the antipodal `T3` term). -/
theorem guaranteedQuads_subset (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S) :
    guaranteedQuads S ⊆ energyQuads S :=
  Finset.union_subset (diag_union_swap_subset S) (antiQuads_subset S hS)

/-- The char-free floor, phrased on `guaranteedQuads`: `card (T1∪T2∪T3) ≥ 3|S|²−3|S|`.
(This is exactly the union-card bound inside `E2_ge_three_card_sq_sub_three_card`; it is purely
combinatorial — the `card`s and pairwise overlaps are char-free, so no negation-closure is needed
for the COUNT, only for the `⊆ energyQuads` membership.) -/
theorem guaranteedQuads_card_ge (S : Finset F) :
    3 * (S.card * S.card) - 3 * S.card ≤ (guaranteedQuads S).card := by
  classical
  -- Reuse the floor proof: card(guaranteed) ≤ E2, and the floor ≤ card(guaranteed) is the
  -- inclusion–exclusion bound; we re-derive it directly to keep the `card` (not `E2`) on the RHS.
  set A := diagQuads S
  set B := swapQuads S
  set C := antiQuads S
  have hAB : (A ∩ B).card ≤ S.card := diag_inter_swap_card_le S
  have hAC : (A ∩ C).card ≤ S.card := diag_inter_anti_card_le S
  have hBC : (B ∩ C).card ≤ S.card := swap_inter_anti_card_le S
  have hcardAB : (A ∪ B).card = A.card + B.card - (A ∩ B).card := Finset.card_union A B
  have hcardUC : ((A ∪ B) ∪ C).card
      = (A ∪ B).card + C.card - ((A ∪ B) ∩ C).card := Finset.card_union _ _
  have hdistrib : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have hcardABC : ((A ∪ B) ∪ C).card
      ≥ (A ∪ B).card + C.card - ((A ∩ C) ∪ (B ∩ C)).card := by
    rw [hcardUC, hdistrib]
  have hinterUnion : ((A ∩ C) ∪ (B ∩ C)).card ≤ (A ∩ C).card + (B ∩ C).card :=
    Finset.card_union_le _ _
  have hAcard : A.card = S.card * S.card := diagQuads_card S
  have hBcard : B.card = S.card * S.card := swapQuads_card S
  have hCcard : C.card = S.card * S.card := antiQuads_card S
  have hABge : (A ∪ B).card ≥ 2 * (S.card * S.card) - S.card := by
    rw [hcardAB, hAcard, hBcard]; omega
  show 3 * (S.card * S.card) - 3 * S.card ≤ (A ∪ B ∪ C).card
  omega

/-- **One genuine additive quadruple forces strict excess.**  If `S` is negation-closed and there
is an energy quadruple `q₀` outside the three guaranteed families `T1 ∪ T2 ∪ T3`, then the additive
energy strictly exceeds the char-free floor: `3|S|² − 3|S| < E₂(S)`. -/
theorem E2_strictGt_of_genuineQuad (S : Finset F) (hS : ∀ x ∈ S, -x ∈ S)
    {q₀ : F × F × F × F} (hq₀ : q₀ ∈ energyQuads S) (hq₀out : q₀ ∉ guaranteedQuads S) :
    3 * (S.card * S.card) - 3 * S.card < E2 S := by
  classical
  -- insert q₀ into the guaranteed set; it stays inside energyQuads and gains exactly one element.
  have hsub : insert q₀ (guaranteedQuads S) ⊆ energyQuads S :=
    Finset.insert_subset hq₀ (guaranteedQuads_subset S hS)
  have hcard_ins : (insert q₀ (guaranteedQuads S)).card = (guaranteedQuads S).card + 1 :=
    Finset.card_insert_of_notMem hq₀out
  have hle : (insert q₀ (guaranteedQuads S)).card ≤ E2 S := Finset.card_le_card hsub
  have hfloor : 3 * (S.card * S.card) - 3 * S.card ≤ (guaranteedQuads S).card :=
    guaranteedQuads_card_ge S
  -- E2 ≥ card(guaranteed)+1 ≥ floor + 1 > floor
  omega

end ArkLib.ProximityGap.E2CharFree

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.E2CharFree.guaranteedQuads_subset
#print axioms ArkLib.ProximityGap.E2CharFree.guaranteedQuads_card_ge
#print axioms ArkLib.ProximityGap.E2CharFree.E2_strictGt_of_genuineQuad
