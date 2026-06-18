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

#print axioms ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_smul_eq
#print axioms
  ProximityGap.Frontier.DoorIVPhaseSetDilationInvariant.addEnergy_phaseSet_indep_of_scalar
