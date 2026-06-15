/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AntipodalSigmaUnique
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# The super-diagonal energy LOWER bound from the disjointness engine (#407 lower companion)

`AntipodalSigmaUnique` lands the `card_biUnion` disjointness engine + the zero-sum injection:
the per-pairing generic antipodal sets are PAIRWISE DISJOINT (`genericAntipodal_pairwiseDisjoint`)
and their union over pairings injects into the zero-sum set
(`genericBiUnion_card_le_zeroSumCount`). This file WELDS those with the proven pairing census
(`pairings_card_eq_doubleFactorial` : `#{IsPairing} = (2r−1)‼`) and the negation-closure energy
bijection (`rEnergy_eq_zeroSumCount`) to deliver the explicit super-diagonal LOWER bound

> `superDiagonal_le_rEnergy` :  `(2r−1)‼ · m ≤ E_r(G)`

for any negation-closed `G`, GATED only on a uniform per-`σ` generic count `m` (`every
fixed-point-free involution `σ` has `#genericAntipodalSet G σ = m`). With `m = (n/2)_r·2^r` (the
distinct-class signed count, probe-verified) this is the full super-diagonal `(2r−1)‼·(n/2)_r·2^r`
that `NotRamanujanLowerBound.not_ramanujan_of_energy_lb` consumes at `r ≥ 6` (the part exceeding
`4^r`). This is the load-bearing composition that makes the disjointness engine actually deliver the
super-diagonal constant.

**Mechanism.** `genericBiUnion_card_eq` makes the disjoint union exact (`(#Pairs)·m`);
`genericBiUnion_card_le_zeroSumCount` injects it into the zero-sum set; the census fixes
`#Pairs = (2r−1)‼`; `rEnergy_eq_zeroSumCount` rewrites the zero-sum count as `E_r(G)`. Chaining gives
`(2r−1)‼·m ≤ E_r(G)`.

**Honest scope (rules 1, 3, 6).** The bound is conditional on the uniform per-`σ` generic count
`m` (the hypothesis `hm`). Discharging `hm` with `m = (n/2)_r·2^r` for `μ_{2^k}` (and verifying
`μ_{2^k}` realizes the `UniqueNeg` generic locus there) is the remaining analytic input, probe-verified
exact in `scripts/probes/probe_charzero_persigma_count.py` but not yet Lean-formalized for the
cyclotomic `μ_{2^k}`. Negation-closed combinatorics, NOT thinness-essential, does NOT close CORE.
Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #407.
-/

open Finset Nat

namespace ProximityGap.Frontier.GenericSuperDiagonalLower

open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ProximityGap.Frontier.AntipodalSigmaUnique

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **The super-diagonal lower bound on the zero-sum count.** For a negation-closed `G`, if every
fixed-point-free involution `σ` has generic-antipodal-set card exactly `m`, then the zero-sum
`2r`-tuple count is at least `(2r−1)‼·m`. (The pairing census fixes the number of involutions to
`(2r−1)‼`; the disjointness engine makes their generic unions sum exactly; the union injects into the
zero-sum set.) -/
theorem doubleFactorial_mul_le_zeroSumCount {r : ℕ} (G : Finset F) (m : ℕ)
    (hm : ∀ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)),
      (genericAntipodalSet G σ).card = m) :
    (2 * r - 1)‼ * m ≤ zeroSumCount G (2 * r) := by
  classical
  set Pairs := Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ) with hPairs
  have hpair : ∀ σ ∈ Pairs, IsPairing σ := fun σ hσ => (Finset.mem_filter.mp hσ).2
  have hunion : (Pairs.biUnion (genericAntipodalSet G)).card = Pairs.card * m :=
    genericBiUnion_card_eq G Pairs m hm
  have hle : (Pairs.biUnion (genericAntipodalSet G)).card ≤ zeroSumCount G (2 * r) :=
    genericBiUnion_card_le_zeroSumCount G Pairs hpair
  rw [hunion, pairings_card_eq_doubleFactorial r] at hle
  exact hle

omit [Fintype F] in
/-- **The super-diagonal energy LOWER bound.** For a negation-closed `G` with uniform per-`σ`
generic count `m`, the `r`-fold additive energy satisfies `(2r−1)‼·m ≤ E_r(G)`. This is the
super-diagonal lower companion of the proven UPPER bound `E_r(G) ≤ (2r−1)‼·n^r`, the constant
`NotRamanujanLowerBound.not_ramanujan_of_energy_lb` needs (with `m = (n/2)_r·2^r`, the bound exceeds
`4^r` at `r ≥ 6`). The disjointness engine (`AntipodalSigmaUnique`) makes the per-`σ` masses sum
exactly; the census fixes the pairing count; the negation-closure bijection ties it to `E_r`. -/
theorem superDiagonal_le_rEnergy {r : ℕ} (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G) (m : ℕ)
    (hm : ∀ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)),
      (genericAntipodalSet G σ).card = m) :
    (2 * r - 1)‼ * m ≤ rEnergy G r := by
  rw [ProximityGap.Frontier.CharZeroWickEnergy.rEnergy_eq_zeroSumCount G r hneg]
  exact doubleFactorial_mul_le_zeroSumCount G m hm

end ProximityGap.Frontier.GenericSuperDiagonalLower

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GenericSuperDiagonalLower.doubleFactorial_mul_le_zeroSumCount
#print axioms ProximityGap.Frontier.GenericSuperDiagonalLower.superDiagonal_le_rEnergy
