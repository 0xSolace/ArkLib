/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

set_option linter.style.longLine false

/-!
# The TWISTED monomial-graph annihilator-line energy is a COLLISION COUNT — `B`-blind (#444)

`TwoDAnnihilatorLineParseval` answered the ≥2-D realizer question for the *untwisted* annihilator
line (period `η(t·b₀)` = the in-tree subgroup Gauss sum), via the unit-multiplication bijection
`t ↦ t·b₀`.  The honest gap left there was the **twisted** monomial-graph line: in the genuine 2-D
geometry the ball is the curve `{(x, x^j) : x ∈ μ_n} ⊂ F²`, so along the annihilator line the period
is the *twisted* sum

  `ζ(t) = ∑_{x ∈ μ_n} ψ(t·φ_x)`,   `φ_x := b₀₁·x + b₀₂·x^j`,

which is **not** a reparametrization of the 1-D frequency family (the bijection `t ↦ t·b₀` no longer
suffices once `x ↦ x^j` twists the per-point phase coefficient `φ_x`).  This file closes that gap with
the genuinely-new **collision-counting Parseval**, fully general in the phase map `φ`:

> `twistedLineEnergy_eq_collisionCount` :
>   `∑_{t ∈ F} ‖∑_{x∈S} ψ(t·φ_x)‖²  =  q · #{(x,y) ∈ S×S : φ_x = φ_y}`.

The proof is the same additive-character orthogonality (`AddChar.sum_mulShift`) that drives
`subgroup_gaussSum_secondMoment`, but with an *arbitrary* phase map `φ : ι → F` summed over an index
`Finset S`.  Consequences pinning the `B`-blindness:

* `twistedLineEnergy_eq_card_of_injOn` — when `φ` is **injective on `S`** (a *non-fold* direction:
  the `n` graph points have `n` distinct phase coefficients), the collision count collapses to the
  diagonal `#S = n`, so the line energy is **exactly `q·n`** — the SAME computable Parseval total as
  the untwisted line and the global second moment, with **no `B`**.  (Probe: ~95–98% of directions
  are non-fold, energy `= p·n` EXACTLY at every prime.)

* `twistedLineEnergy_le_card_sq` — for **every** direction (folds included) the collision count is
  trivially `≤ (#S)²`, so the line energy is `≤ q·n²` — a closed COMPUTABLE ceiling, still purely a
  count, never the sup `B`.  (Probe: worst fold energy `≤ p·2n ≪ p·n²`; the bound here is loose but
  unconditional and `B`-free.)

**Conclusion (closes the twisted gap of `TwoDAnnihilatorLineParseval`).**  The twisted monomial-graph
annihilator-line energy is a pure **collision count** of the phase map `φ` — `q·n` on non-fold
directions, `≤ q·n²` always — an L²/counting quantity that is **`B`-blind in both the generic and the
worst case**.  So the genuinely-twisted ≥2-D incidence ENERGY supplies no sup-`B` realizer either; the
sup `B` stays quarantined to the per-frequency L∞ level (the original BGK/Paley wall).  This makes the
`TwoDAnnihilatorLineParseval` answer hold for the *actual* twisted graph, not just its untwisted
projection.

**Probe-corroborated** (`scripts/probes/probe_2d_annihilator_incidence_supVSavg.py`, exact `F_p`,
PROPER `μ_n` `n=2^a`, `n∣p−1`, `p≫n³`, multiple primes, monomial degrees `j=2,3`, NEVER `n=q−1`):
the twisted-line energy is `p·(collision count)`, with collision count `= n` for ~95–98% of
directions (energy `= p·n` EXACTLY at every prime) and `≤ 2n` for the rare folds; energy never sees
`B`, while the per-frequency sup along the line `= B` (ratio `1.0000`–`1.10`).

Axiom-clean; pure additive-character orthogonality over an arbitrary phase map.  No field-size or
regime hypotheses, no `μ_n`-specific structure (holds for any index `Finset` and any `φ`).  Issue #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.TwistedLineCollisionParseval

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [DecidableEq ι]

/-- **The twisted annihilator-line period at line-parameter `t`.**  For a phase map `φ : ι → F`
(modeling `x ↦ b₀₁·x + b₀₂·x^j` over the monomial graph) and index set `S`, the period read at `t`
is the twisted character sum `ζ(t) = ∑_{x∈S} ψ(t·φ_x)`. -/
noncomputable def twistedLineEta (ψ : AddChar F ℂ) (S : Finset ι) (φ : ι → F) (t : F) : ℂ :=
  ∑ x ∈ S, ψ (t * φ x)

/-- **THE TWISTED LINE PARSEVAL (genuinely new): the line energy is a COLLISION COUNT.**

  `∑_{t∈F} ‖ζ(t)‖²  =  q · #{(x,y) ∈ S×S : φ_x = φ_y}`.

Expanding `‖ζ(t)‖² = ζ(t)·conj ζ(t)` into a double sum over `(x,y) ∈ S×S` and summing over `t`
collapses each pair via additive-character orthogonality (`AddChar.sum_mulShift`): `∑_t ψ(t·(φ_x−φ_y))
= q·[φ_x = φ_y]`.  So the total energy counts (with weight `q`) exactly the pairs whose phase
coefficients collide.  This is the twisted analog of `subgroup_gaussSum_secondMoment`; the energy is a
pure **count**, manifestly independent of the sup `B`. -/
theorem twistedLineEnergy_eq_collisionCount {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) :
    ∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2
      = (Fintype.card F : ℝ) * ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- Complex identity: ∑_t ζ(t)·conj ζ(t) = q · (collision count : ℂ).
  have hcomplex : (∑ t : F, twistedLineEta ψ S φ t * (starRingEnd ℂ) (twistedLineEta ψ S φ t))
      = (Fintype.card F : ℂ) * ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card := by
    calc ∑ t : F, twistedLineEta ψ S φ t * (starRingEnd ℂ) (twistedLineEta ψ S φ t)
        = ∑ t : F, ∑ x ∈ S, ∑ y ∈ S, ψ (t * (φ x - φ y)) := by
          refine Finset.sum_congr rfl (fun t _ => ?_)
          have hconjz : (starRingEnd ℂ) (twistedLineEta ψ S φ t) = ∑ y ∈ S, ψ (-(t * φ y)) := by
            rw [twistedLineEta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (t * φ y))
          have hL : twistedLineEta ψ S φ t = ∑ x ∈ S, ψ (t * φ x) := rfl
          rw [hconjz, hL, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          refine Finset.sum_congr rfl (fun y _ => ?_)
          have harg : t * φ x + -(t * φ y) = t * (φ x - φ y) := by ring
          rw [← AddChar.map_add_eq_mul, harg]
      _ = ∑ x ∈ S, ∑ y ∈ S, ∑ t : F, ψ (t * (φ x - φ y)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun x _ => ?_); rw [Finset.sum_comm]
      _ = ∑ x ∈ S, ∑ y ∈ S, (if φ x = φ y then (Fintype.card F : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [AddChar.sum_mulShift (φ x - φ y) hψ]; simp [sub_eq_zero]
      _ = ∑ p ∈ S ×ˢ S, (if φ p.1 = φ p.2 then (Fintype.card F : ℂ) else 0) := by
          rw [← Finset.sum_product']
      _ = (Fintype.card F : ℂ) * ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card := by
          rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          by_cases h : φ p.1 = φ p.2 <;> simp [h]
  -- Cast the complex identity to the real energy.
  have hnorm : ∀ t : F,
      twistedLineEta ψ S φ t * (starRingEnd ℂ) (twistedLineEta ψ S φ t)
        = ((‖twistedLineEta ψ S φ t‖ ^ 2 : ℝ) : ℂ) := by
    intro t; rw [RCLike.mul_conj]; norm_cast
  have hcast : ((∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card F : ℂ) * ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card := by
    rw [Complex.ofReal_sum, ← hcomplex]
    exact Finset.sum_congr rfl (fun t _ => (hnorm t).symm)
  have hreal : ((∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2 : ℝ) : ℂ)
      = (((Fintype.card F : ℝ) * ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card : ℝ) : ℂ) := by
    rw [hcast]; push_cast; ring
  exact_mod_cast hreal

/-- **Non-fold direction (`φ` injective on `S`): the line energy is exactly `q·|S|` — no `B`.**
When the phase map separates the `|S| = n` graph points (the generic / non-fold direction), the only
colliding pairs are the diagonal `x = y`, so the collision count is `|S|` and the line energy is the
computable Parseval total `q·|S|`, identical to the untwisted line and the global second moment.  The
twist does **not** re-introduce the sup `B`. -/
theorem twistedLineEnergy_eq_card_of_injOn {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) (hinj : Set.InjOn φ S) :
    ∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2 = (Fintype.card F : ℝ) * S.card := by
  rw [twistedLineEnergy_eq_collisionCount hψ S φ]
  congr 1
  -- the colliding pairs are exactly the diagonal {(x,x) : x∈S}, of card |S|.
  have hfilter : (S ×ˢ S).filter (fun p => φ p.1 = φ p.2) = S.diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨h1, h2⟩, heq⟩; exact ⟨h1, hinj h1 h2 heq⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ h1⟩, by rw [h2]⟩
  rw [hfilter, Finset.diag_card]

/-- **Every direction (folds included): the line energy is `≤ q·|S|²` — a computable ceiling, no `B`.**
The collision count is trivially `≤ |S×S| = |S|²`, so the twisted line energy is bounded by the closed
computable value `q·|S|²`, with no dependence on the sup `B`.  (Loose vs the observed `≤ q·2|S|` fold
ceiling, but unconditional and `B`-free — the worst-case twisted-line energy is still a *count*.) -/
theorem twistedLineEnergy_le_card_sq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) :
    ∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2 ≤ (Fintype.card F : ℝ) * (S.card : ℝ) ^ 2 := by
  rw [twistedLineEnergy_eq_collisionCount hψ S φ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hle : ((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card ≤ (S ×ˢ S).card :=
    Finset.card_filter_le _ _
  calc (((S ×ˢ S).filter (fun p => φ p.1 = φ p.2)).card : ℝ)
      ≤ ((S ×ˢ S).card : ℝ) := by exact_mod_cast hle
    _ = (S.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring

/-- **Non-fold line-energy AVERAGE over the `q` line points is exactly `|S|` — the `√|S|` scale, no
`B`.**  Dividing the non-fold line energy `q·|S|` by the number of line points `q = |F|`: the typical
twisted line period has size `√|S| = √n`, the same average scale as the global second moment, with no
appearance of the sup `B`.  This is the explicit L²/average-measurability of the twisted annihilator-
line incidence on non-fold directions. -/
theorem twistedLineEnergy_average_of_injOn {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (S : Finset ι) (φ : ι → F) (hinj : Set.InjOn φ S) (hq : 0 < Fintype.card F) :
    (∑ t : F, ‖twistedLineEta ψ S φ t‖ ^ 2) / (Fintype.card F : ℝ) = S.card := by
  rw [twistedLineEnergy_eq_card_of_injOn hψ S φ hinj, mul_comm, mul_div_assoc,
    div_self (by exact_mod_cast hq.ne'), mul_one]

end ArkLib.ProximityGap.TwistedLineCollisionParseval

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.TwistedLineCollisionParseval.twistedLineEnergy_eq_collisionCount
#print axioms ArkLib.ProximityGap.TwistedLineCollisionParseval.twistedLineEnergy_eq_card_of_injOn
#print axioms ArkLib.ProximityGap.TwistedLineCollisionParseval.twistedLineEnergy_le_card_sq
#print axioms ArkLib.ProximityGap.TwistedLineCollisionParseval.twistedLineEnergy_average_of_injOn
