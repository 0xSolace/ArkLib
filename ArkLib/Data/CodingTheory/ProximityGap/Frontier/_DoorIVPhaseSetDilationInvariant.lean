/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Door IV (Lane 1, the brief's verbatim small-ball target): the worst-b phase set `{b·x : x∈μ_n}` has
# DILATION-INVARIANT additive structure — the worst `b` cannot tune it, so any small-ball / Halász
# lever is b-independent and reproduces the (dead) EVT/Plancherel ceiling, never beats the wall

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_phaseset_additive_smallball.py`.

## Why this matters (the brief's literal Lane-1 question)

The brief asks verbatim: "how spread is `{b·x^m mod p}`? Any Littlewood–Offord / Halász-type
small-ball bound for this phase set that does NOT route through multiplicative energy?" This is the
ADDITIVE structure of the x-side phase-residue set `S_b = {b·x : x ∈ μ_n} ⊆ 𝔽_p` (distinct from the
b-side worst-set `ae2bc7e0b` and the complex-alignment participation `78d1df596`).

`S_b = b · μ_n` is a multiplicative DILATE of the subgroup. Its additive energy
`E⁺(S) = #{(a,b,c,d) ∈ S⁴ : a + b = c + d}` is the natural small-ball / Halász input. The probe
(PROPER `μ_n`, p≈n⁴≫n³, EXACT bignum, never n=q−1) found:

  * `E⁺(μ_n)/n²` is FLAT at a small constant (2.81, 2.91, 2.95 for n=16,32,64) — does NOT grow with
    `n`: the phase set is additively SPREAD (Sidon-like up to a constant), NOT additively structured.
  * sumset doubling `|S+S|/n ≈ n/2` (8.06, 16.03, 32.02) = the Sidon signature `|S+S| ≈ |S|²/2`.
  * the arc small-ball `ρ*` DECAYS (0.75 → 0.25 → 0.078): the residues spread, no concentration.
  * the worst-b sum sits at the EVT/Plancherel ceiling `M/√(n·log(p/n)) ≈ 1.2–1.36`.

So the Halász/small-ball bound derived from `E⁺` reproduces `|η_b| ≲ √(n·log)` = the SAME EVT ceiling
— it does NOT beat the wall and does NOT avoid the moment route. And crucially: `E⁺(b·μ_n)` does NOT
depend on `b` (dilation-invariance), so the WORST `b` cannot tune the additive structure to do better.
The additive energy of a multiplicative subgroup IS a multiplicative-energy object. Mapped wall, not
a non-moment lever.

## The formalizable kernel (this file): dilation-invariance of additive energy

The exact structural fact making the small-ball lever b-blind: for a unit `λ` (here `λ = b`),
multiplication-by-`λ` is a bijection of `𝔽_p` that preserves the additive-quadruple relation
`a + b = c + d ⟺ λ·a + λ·b = λ·c + λ·d`. Hence `E⁺(λ • S) = E⁺(S)`. We model `E⁺` as the cardinality
of the quadruple solution set inside `S⁴` and prove the dilate has the SAME count via the
mul-by-`λ⁻¹` bijection on the index `Finset`. Consequence: any bound on `|η_b|` factoring through
`E⁺(S_b)` is `b`-independent — the worst `b` inherits the typical (EVT) ceiling.
-/

namespace ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant

open Finset

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The additive-quadruple solution set of a finite set `S ⊆ F`:
`{(a,b,c,d) ∈ S⁴ : a + b = c + d}`, whose cardinality is the additive energy `E⁺(S)`. -/
def addQuadruples (S : Finset F) : Finset (F × F × F × F) :=
  (S ×ˢ S ×ˢ S ×ˢ S).filter (fun q => q.1 + q.2.1 = q.2.2.1 + q.2.2.2)

/-- Additive energy `E⁺(S) = #{(a,b,c,d) ∈ S⁴ : a+b=c+d}`. -/
def addEnergy (S : Finset F) : ℕ := (addQuadruples S).card


/-- Additive sumset `S + S`, used by the small-ball/doubling probe. -/
def addSumset (S : Finset F) : Finset F :=
  (S ×ˢ S).image (fun p => p.1 + p.2)

/-- Dilation commutes exactly with the additive sumset: `(λS)+(λS)=λ(S+S)`. -/
theorem addSumset_smul_eq_image (S : Finset F) (lam : F) :
    addSumset (S.image (fun x => lam * x)) = (addSumset S).image (fun x => lam * x) := by
  classical
  ext y
  simp [addSumset, mul_add]
  aesop

/-- Nonzero dilation preserves additive doubling cardinality.  Thus the observed `|bS+bS|/|S|`
small-ball input is also worst-frequency-blind: changing `b` cannot improve or worsen the sumset
size of the phase residue set. -/
theorem addSumset_card_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    (addSumset (S.image (fun x => lam * x))).card = (addSumset S).card := by
  classical
  rw [addSumset_smul_eq_image]
  exact Finset.card_image_of_injOn (s := addSumset S) (f := fun x => lam * x) (by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hlam hxy)

/-- Two nonzero frequency dilates have the same additive sumset cardinal.  This is the exact formal
counterpart of the probe verdict: additive-doubling/arc-small-ball data of `{b*x^m}` is a property
of the subgroup, not of the adversarial worst `b`. -/
theorem addSumset_card_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    (addSumset (S.image (fun x => b₁ * x))).card =
      (addSumset (S.image (fun x => b₂ * x))).card := by
  rw [addSumset_card_smul_eq S hb₁, addSumset_card_smul_eq S hb₂]


/-- Additive difference set `S - S`, the pair-spacing support seen by pair-collision and
Littlewood-Offord small-ball arguments. -/
def addDiffset (S : Finset F) : Finset F :=
  (S ×ˢ S).image (fun p => p.1 - p.2)

/-- Dilation commutes exactly with the additive difference set: `λS - λS = λ(S - S)`. -/
theorem addDiffset_smul_eq_image (S : Finset F) (lam : F) :
    addDiffset (S.image (fun x => lam * x)) = (addDiffset S).image (fun x => lam * x) := by
  classical
  ext y
  simp [addDiffset, mul_sub]
  aesop

/-- Nonzero dilation preserves additive difference-set cardinality.  Thus pair-spacing support of
`{b*x^m}` is also independent of the adversarial frequency. -/
theorem addDiffset_card_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    (addDiffset (S.image (fun x => lam * x))).card = (addDiffset S).card := by
  classical
  rw [addDiffset_smul_eq_image]
  exact Finset.card_image_of_injOn (s := addDiffset S) (f := fun x => lam * x) (by
    intro x _ y _ hxy
    exact mul_left_cancel₀ hlam hxy)

/-- Two nonzero frequency dilates have the same additive difference-set cardinal.  This rules out a
worst-b selector based purely on pair-spacing support or difference-set expansion. -/
theorem addDiffset_card_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    (addDiffset (S.image (fun x => b₁ * x))).card =
      (addDiffset (S.image (fun x => b₂ * x))).card := by
  rw [addDiffset_card_smul_eq S hb₁, addDiffset_card_smul_eq S hb₂]


/-- Pair-sum representation count at target `t`: `#{(a,b) in S^2 : a+b=t}`. -/
def addPairSumCount (S : Finset F) (t : F) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 + p.2 = t)).card

/-- Nonzero dilation preserves each pair-sum fiber, after dilating the target.  This is the exact
multiplicity-level version of sumset-cardinality invariance: not only the support `S+S`, but every
representation count is transported by `t ↦ λt`. -/
theorem addPairSumCount_smul_eq (S : Finset F) {lam t : F} (hlam : lam ≠ 0) :
    addPairSumCount (S.image (fun x => lam * x)) (lam * t) = addPairSumCount S t := by
  classical
  unfold addPairSumCount
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun p => (lam⁻¹ * p.1, lam⁻¹ * p.2))
    (fun p => (lam * p.1, lam * p.2))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨hp₁, hp₂⟩, hsum⟩ := hp
    obtain ⟨a, ha, hpa⟩ := hp₁
    obtain ⟨b, hb, hpb⟩ := hp₂
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [← hpa, hcdiv] using ha
    · simpa [← hpb, hcdiv] using hb
    · apply mul_left_cancel₀ hlam
      simpa [mul_add, ← hpa, ← hpb, hcmul] using hsum
  · intro p hp
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨hp₁, hp₂⟩, hsum⟩ := hp
    refine ⟨⟨⟨p.1, hp₁, rfl⟩, ⟨p.2, hp₂, rfl⟩⟩, ?_⟩
    rw [← mul_add, hsum]
  · intro p _
    simp [hcmul]
  · intro p _
    simp [hcdiv]

/-- The pair-sum multiplicity profile of two nonzero frequency dilates is identical after the obvious
rescaling of targets.  Pure pair-count/Halasz inputs therefore cannot distinguish the worst `b`. -/
theorem addPairSumCount_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ t : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addPairSumCount (S.image (fun x => b₁ * x)) (b₁ * t) =
      addPairSumCount (S.image (fun x => b₂ * x)) (b₂ * t) := by
  rw [addPairSumCount_smul_eq S hb₁, addPairSumCount_smul_eq S hb₂]

/-- Dilation by a NONZERO scalar `λ` is an additive-energy-preserving bijection on the quadruple
solution set: `(a,b,c,d) ↦ (λa,λb,λc,λd)` maps `addQuadruples S` bijectively onto
`addQuadruples (λ • S)`, because `a+b=c+d ⟺ λa+λb=λc+λd` for `λ ≠ 0`. Hence the additive energy is
dilation-invariant. -/
theorem addEnergy_smul_eq (S : Finset F) {lam : F} (hlam : lam ≠ 0) :
    addEnergy (S.image (fun x => lam * x)) = addEnergy S := by
  classical
  unfold addEnergy addQuadruples
  -- s = quadruples of (λ•S); t = quadruples of S. i divides by λ, j multiplies by λ.
  have hcdiv : ∀ z : F, lam⁻¹ * (lam * z) = z := fun z => by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcmul : ∀ z : F, lam * (lam⁻¹ * z) = z := fun z => by
    rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
  refine Finset.card_nbij'
    (fun q => (lam⁻¹ * q.1, lam⁻¹ * q.2.1, lam⁻¹ * q.2.2.1, lam⁻¹ * q.2.2.2))
    (fun q => (lam * q.1, lam * q.2.1, lam * q.2.2.1, lam * q.2.2.2))
    ?_ ?_ ?_ ?_
  · -- i : (λ•S)-quads → S-quads
    rintro ⟨a, b, c, d⟩ hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hq ⊢
    obtain ⟨⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩, ⟨c', hc', rfl⟩, ⟨d', hd', rfl⟩⟩, heq⟩ := hq
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [hcdiv] using ha'
    · simpa [hcdiv] using hb'
    · simpa [hcdiv] using hc'
    · simpa [hcdiv] using hd'
    · rw [hcdiv, hcdiv, hcdiv, hcdiv]
      have h2 := mul_left_cancel₀ hlam (by linear_combination heq :
        lam * (a' + b') = lam * (c' + d'))
      linear_combination h2
  · -- j : S-quads → (λ•S)-quads
    rintro ⟨a, b, c, d⟩ hq
    simp only [coe_filter, Set.mem_setOf_eq, mem_product, mem_image] at hq ⊢
    obtain ⟨⟨ha, hb, hc, hd⟩, heq⟩ := hq
    refine ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩⟩, ?_⟩
    linear_combination lam * heq
  · -- left inverse on s
    rintro ⟨a, b, c, d⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨hcmul a, hcmul b, hcmul c, hcmul d⟩
  · -- right inverse on t
    rintro ⟨a, b, c, d⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨hcdiv a, hcdiv b, hcdiv c, hcdiv d⟩

/-- Consequence for the small-ball lever: since `E⁺(b • S) = E⁺(S)` for every nonzero `b`, any
`|η_b|`-bound that factors through the additive energy of the phase set `S_b = b • μ_n` takes the
SAME value at the worst `b` as at a typical `b`. The worst `b` cannot tune the additive structure;
the small-ball / Halász lever is b-independent and reproduces the typical (EVT/Plancherel) ceiling.
We state it as: a uniform additive-energy `E⁺(S_b) = K` certificate is the SAME for all nonzero
dilates, so a bound `f (E⁺ (b • S))` is constant in `b`. -/
theorem addEnergy_phaseSet_indep_of_scalar
    (S : Finset F) {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    addEnergy (S.image (fun x => b₁ * x)) = addEnergy (S.image (fun x => b₂ * x)) := by
  rw [addEnergy_smul_eq S hb₁, addEnergy_smul_eq S hb₂]

end ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant

#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_smul_eq_image
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_card_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addSumset_card_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_smul_eq_image
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_card_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addDiffset_card_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount_smul_eq
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addPairSumCount_phaseSet_indep_of_scalar
#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_phaseSet_indep_of_scalar
