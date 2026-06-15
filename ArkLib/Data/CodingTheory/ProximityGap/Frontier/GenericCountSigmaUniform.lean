/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AntipodalSigmaUnique
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.GenericSuperDiagonalLower
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedPairingCount
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# The per-`σ` generic count is UNIFORM across pairings — discharging the `hm` gate (#407 lower)

`GenericSuperDiagonalLower.superDiagonal_le_rEnergy` delivers `(2r−1)‼·m ≤ E_r(G)` for a
negation-closed `G`, but is GATED on a *uniform* per-`σ` generic count

> `hm : ∀ σ, IsPairing σ → (genericAntipodalSet G σ).card = m`.

Every prior #407-lower report (czlower, persigma, sigmauniq) isolated `hm` as the remaining brick
but left it un-discharged: the per-`σ` count was probe-verified equal across `σ`, never proven in
Lean. This file lands the **field-general uniformity**:

> `genericAntipodalSet_card_conj` :  if `τ = ρ·σ·ρ⁻¹` then
>   `(genericAntipodalSet G σ).card = (genericAntipodalSet G τ).card`;
> `genericAntipodalSet_card_eq_of_isPairing` :  any two fixed-point-free involutions `σ, τ`
>   have EQUAL generic-antipodal-set card (they are conjugate by equal cycle type);
> `genericAntipodalSet_card_uniform` :  packaged as the exact `hm` shape — picking ANY one
>   reference pairing `σ₀` discharges `hm` with `m := (genericAntipodalSet G σ₀).card`.

This reduces the `hm` hypothesis of `superDiagonal_le_rEnergy` from a `∀σ` family-uniformity claim
to a SINGLE per-`σ` count: feed one reference pairing's count and uniformity propagates it to all.

**Mechanism.** All fixed-point-free involutions of `Fin (2r)` share `cycleType = replicate r 2`
(`NegationClosedPairingCount.isPairing_iff_cycleType`), hence are conjugate
(`Equiv.Perm.isConj_of_cycleType_eq`): `∃ ρ, ρ·σ·ρ⁻¹ = τ`. The reindexing `c ↦ c ∘ ρ⁻¹` is then a
bijection `genericAntipodalSet G σ → genericAntipodalSet G τ`:
* G-membership is preserved (reindexing coordinates of a tuple in `G^{2r}`);
* the antipodal relation conjugates: `d (τ i) = c (ρ⁻¹ (τ i)) = c (σ (ρ⁻¹ i)) = −c (ρ⁻¹ i) = −d i`
  (using `ρ⁻¹·τ = σ·ρ⁻¹`, equivalent to `τ = ρ·σ·ρ⁻¹`);
* `UniqueNeg` is permutation-invariant (reindex the unique witness by `ρ⁻¹`).
Its inverse is `d ↦ d ∘ ρ`, so it is a genuine bijection and the cards agree.

**Probe.** `scripts/probes/probe_generic_count_sigma_uniform.py`: `#genericAntipodalSet G σ` is the
SAME for ALL fixed-point-free involutions `σ` over abstract negation-closed `Z_n` (additive) AND
multiplicative `μ_n` (`uniform=True` in every case `n∈{4,6,8}`, `r∈{1,2,3}`); for the genuine
`μ_n` model (`neg g = g + n/2`, no fixed points) the common value is exactly `(n/2)_r·2^r`.

**Honest scope (rules 1, 3, 6).** This discharges the *uniformity* half of `hm` (the count is
`σ`-independent) for ANY negation-closed `G`, field-general, axiom-clean. It does NOT compute the
value `m = (n/2)_r·2^r` for the cyclotomic `μ_{2^k}` — that single reference count remains the
analytic input (probe-verified). What lands here is the precise reduction "`hm` for all `σ` ⟸ the
count for ONE `σ`", removing the family quantifier from the gate. Negation-closed combinatorics,
NOT thinness-essential, does NOT close CORE. Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #407.
-/

open Finset Nat

namespace ProximityGap.Frontier.GenericCountSigmaUniform

open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ProximityGap.Frontier.AntipodalSigmaUnique

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- `UniqueNeg` is invariant under reindexing a tuple by a permutation `ρ` of the coordinates:
`UniqueNeg (c ∘ ρ) ↔ UniqueNeg c`. (The unique negative-witness index just gets relabelled by `ρ`.) -/
theorem uniqueNeg_comp_perm {r : ℕ} (c : Fin (2 * r) → F) (ρ : Equiv.Perm (Fin (2 * r))) :
    UniqueNeg (c ∘ ρ) ↔ UniqueNeg c := by
  unfold UniqueNeg
  constructor
  · intro h i
    -- from the ∃! for index ρ⁻¹ i in the composed tuple, transport to index i in c
    obtain ⟨j, hj, huniq⟩ := h (ρ.symm i)
    refine ⟨ρ j, ?_, ?_⟩
    · simpa [Function.comp, Equiv.apply_symm_apply] using hj
    · intro k hk
      -- hk : c k = - c i; want ρ j = k, i.e. j is the unique witness for (c∘ρ)(ρ⁻¹ i)
      have : (c ∘ ρ) (ρ.symm k) = - (c ∘ ρ) (ρ.symm i) := by
        simp only [Function.comp, Equiv.apply_symm_apply]; exact hk
      have hjk := huniq (ρ.symm k) this
      rw [← hjk]; simp
  · intro h i
    obtain ⟨j, hj, huniq⟩ := h (ρ i)
    refine ⟨ρ.symm j, ?_, ?_⟩
    · simpa [Function.comp, Equiv.apply_symm_apply] using hj
    · intro k hk
      have : c (ρ k) = - c (ρ i) := by simpa [Function.comp] using hk
      have hjk := huniq (ρ k) this
      rw [← hjk]; simp

omit [Fintype F] in
/-- **The bijection on cards.** If `τ = ρ·σ·ρ⁻¹` then the per-`σ` and per-`τ` generic antipodal sets
have equal cardinality, via the reindexing bijection `c ↦ c ∘ ρ⁻¹` (inverse `d ↦ d ∘ ρ`). -/
theorem genericAntipodalSet_card_conj {r : ℕ} (G : Finset F)
    {σ τ ρ : Equiv.Perm (Fin (2 * r))} (hconj : ρ * σ * ρ⁻¹ = τ) :
    (genericAntipodalSet G σ).card = (genericAntipodalSet G τ).card := by
  classical
  -- forward i : c ↦ c ∘ ρ⁻¹  ; inverse j : d ↦ d ∘ ρ
  refine Finset.card_nbij' (fun c => c ∘ ⇑ρ.symm) (fun d => d ∘ ⇑ρ) ?_ ?_ ?_ ?_
  · -- MapsTo: c ∈ S_σ ⟹ c∘ρ⁻¹ ∈ S_τ
    intro c hc
    simp only [genericAntipodalSet, Finset.coe_filter, Set.mem_setOf_eq,
      Fintype.mem_piFinset] at hc ⊢
    obtain ⟨hmem, hanti, huniq⟩ := hc
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact hmem _
    · -- (c∘ρ⁻¹)(τ i) = -(c∘ρ⁻¹)(i)
      intro i
      have hτ : τ = ρ * σ * ρ⁻¹ := hconj.symm
      simp only [Function.comp]
      -- ρ⁻¹ (τ i) = σ (ρ⁻¹ i)
      have key : ρ.symm (τ i) = σ (ρ.symm i) := by
        rw [hτ]; simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      rw [key]; exact hanti _
    · have := (uniqueNeg_comp_perm c ρ.symm).mpr huniq; exact this
  · -- MapsTo inverse: d ∈ S_τ ⟹ d∘ρ ∈ S_σ
    intro d hd
    simp only [genericAntipodalSet, Finset.coe_filter, Set.mem_setOf_eq,
      Fintype.mem_piFinset] at hd ⊢
    obtain ⟨hmem, hanti, huniq⟩ := hd
    refine ⟨?_, ?_, ?_⟩
    · intro i; exact hmem _
    · intro i
      simp only [Function.comp]
      -- (d∘ρ)(σ i) = d(ρ(σ i)) ; want = -(d∘ρ)(i) = -d(ρ i)
      -- ρ (σ i) = τ (ρ i) since τ = ρ σ ρ⁻¹ ⟹ τ ρ = ρ σ
      have key : ρ (σ i) = τ (ρ i) := by
        rw [← hconj]; simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      rw [key]; exact hanti _
    · have := (uniqueNeg_comp_perm d ρ).mpr huniq; exact this
  · -- LeftInvOn: (c∘ρ.symm)∘ρ = c
    intro c _
    funext i; simp [Function.comp, Equiv.symm_apply_apply]
  · -- RightInvOn: (d∘ρ)∘ρ.symm = d
    intro d _
    funext i; simp [Function.comp, Equiv.apply_symm_apply]

omit [Fintype F] in
/-- **Uniformity across all fixed-point-free involutions.** Any two pairings `σ, τ` have equal
generic-antipodal-set cardinality. (Same `cycleType = replicate r 2`, hence conjugate.) -/
theorem genericAntipodalSet_card_eq_of_isPairing {r : ℕ} (G : Finset F)
    {σ τ : Equiv.Perm (Fin (2 * r))} (hσ : IsPairing σ) (hτ : IsPairing τ) :
    (genericAntipodalSet G σ).card = (genericAntipodalSet G τ).card := by
  -- both have cycleType = replicate r 2 ⟹ conjugate
  have hcσ := (isPairing_iff_cycleType σ).mp hσ
  have hcτ := (isPairing_iff_cycleType τ).mp hτ
  have hcyc : σ.cycleType = τ.cycleType := by rw [hcσ, hcτ]
  have hconj : IsConj σ τ := Equiv.Perm.isConj_of_cycleType_eq hcyc
  obtain ⟨ρ, hρ⟩ := isConj_iff.mp hconj
  exact genericAntipodalSet_card_conj G hρ

omit [Fintype F] in
/-- **The `hm` gate, discharged from a single reference count.** Given ANY one reference pairing
`σ₀` and the value `m := (genericAntipodalSet G σ₀).card`, every fixed-point-free involution `σ`
realizes that same count. This is exactly the `hm` hypothesis of
`GenericSuperDiagonalLower.superDiagonal_le_rEnergy`, now reduced to a single per-`σ` count. -/
theorem genericAntipodalSet_card_uniform {r : ℕ} (G : Finset F)
    {σ₀ : Equiv.Perm (Fin (2 * r))} (hσ₀ : IsPairing σ₀) :
    ∀ σ ∈ (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ)),
      (genericAntipodalSet G σ).card = (genericAntipodalSet G σ₀).card := by
  intro σ hσ
  have hσP : IsPairing σ := (Finset.mem_filter.mp hσ).2
  exact genericAntipodalSet_card_eq_of_isPairing G hσP hσ₀

omit [Fintype F] in
/-- **Load-bearing weld: the super-diagonal energy LOWER bound from a SINGLE reference count.**
The `hm` gate of `GenericSuperDiagonalLower.superDiagonal_le_rEnergy` is a `∀σ` uniformity claim;
this corollary discharges it from the count of ONE reference pairing `σ₀` (uniformity propagates).
For a negation-closed `G`, given any fixed-point-free involution `σ₀` whose generic-antipodal-set
card is `m`, the `r`-fold additive energy satisfies `(2r−1)‼·m ≤ E_r(G)`. -/
theorem superDiagonal_le_rEnergy_of_ref {r : ℕ} (G : Finset F) (hneg : ∀ g ∈ G, -g ∈ G)
    {σ₀ : Equiv.Perm (Fin (2 * r))} (hσ₀ : IsPairing σ₀) (m : ℕ)
    (hm₀ : (genericAntipodalSet G σ₀).card = m) :
    (2 * r - 1)‼ * m ≤ rEnergy G r := by
  apply ProximityGap.Frontier.GenericSuperDiagonalLower.superDiagonal_le_rEnergy G hneg m
  intro σ hσ
  rw [genericAntipodalSet_card_uniform G hσ₀ σ hσ]
  exact hm₀

omit [Fintype F] in
/-- The same weld at the level of the raw zero-sum count `Z_{2r}(G)`. -/
theorem doubleFactorial_mul_le_zeroSumCount_of_ref {r : ℕ} (G : Finset F)
    {σ₀ : Equiv.Perm (Fin (2 * r))} (hσ₀ : IsPairing σ₀) (m : ℕ)
    (hm₀ : (genericAntipodalSet G σ₀).card = m) :
    (2 * r - 1)‼ * m ≤ zeroSumCount G (2 * r) := by
  apply ProximityGap.Frontier.GenericSuperDiagonalLower.doubleFactorial_mul_le_zeroSumCount G m
  intro σ hσ
  rw [genericAntipodalSet_card_uniform G hσ₀ σ hσ]
  exact hm₀

end ProximityGap.Frontier.GenericCountSigmaUniform

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GenericCountSigmaUniform.uniqueNeg_comp_perm
#print axioms ProximityGap.Frontier.GenericCountSigmaUniform.genericAntipodalSet_card_conj
#print axioms ProximityGap.Frontier.GenericCountSigmaUniform.genericAntipodalSet_card_eq_of_isPairing
#print axioms ProximityGap.Frontier.GenericCountSigmaUniform.genericAntipodalSet_card_uniform
#print axioms ProximityGap.Frontier.GenericCountSigmaUniform.superDiagonal_le_rEnergy_of_ref
#print axioms ProximityGap.Frontier.GenericCountSigmaUniform.doubleFactorial_mul_le_zeroSumCount_of_ref
