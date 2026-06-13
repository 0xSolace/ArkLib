/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineIncidenceSpectral
set_option linter.style.longLine false

/-!
# The Shaw operator: the unified unknown of the Proximity Prize (#389, #371)

Every reduction of the prize δ\* — the residual `(R) = worst − average`, the higher-order-MDS
failure-correction `κ_d`, the off-diagonal spectral error of the line–ball incidence operator, the
worst-case incomplete character sum `max|η_b|`, the higher additive energies `E_r` — collapses to a
**single** quantity. This file names it the **Shaw operator** and proves the exact identity that
makes the far-line incidence (hence δ\*) a *closed function* of it.

> **`shawError S s₀ s₁`** `:= ∑_{ψ≠0, ψ⊥s₁} ∑_{s∈S} ψ(s₀−s)` — the off-trivial spectral error of
> the line–ball incidence on direction `s₁`.
>
> **`incidence_eq_average_add_shaw`** — `#{γ : s₀+γ·s₁ ∈ S} · |V| = |F| · (|S| + 𝒮)`. The trivial
> character contributes exactly the average `|F|·|S|`; **everything else is the Shaw operator.**

So `incidence = average + (|F|/|V|)·𝒮`, exactly and unconditionally. Since
`δ* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}` (`MCAThresholdLedger`), δ\* is determined by the
worst-case value of `𝒮` over far lines — the one open input, now a single named object. Axiom-clean.
-/

open Finset
open ArkLib.ProximityGap.LineIncidenceSpectral

namespace ArkLib.ProximityGap.ShawOperator

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Fintype V] [DecidableEq V]
  [Module F V]

/-- **The Shaw operator** `𝒮(S; s₀, s₁)`: the off-trivial spectral error of the line–ball incidence
operator on direction `s₁`. The single unknown to which every prize reduction collapses. -/
noncomputable def shawError (S : Finset V) (s₀ s₁ : V) : ℂ :=
  ∑ ψ : AddChar V ℂ,
    (if directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0 then ∑ s ∈ S, ψ (s₀ - s) else 0)

/-- The trivial character of `V` restricts to the trivial character on any direction. -/
theorem directionChar_zero (s₁ : V) : directionChar (F := F) (0 : AddChar V ℂ) s₁ = 0 := by
  ext γ
  simp [directionChar_apply]

/-- **The exact incidence decomposition — the δ\*-defining identity.**
`#{γ : s₀+γ·s₁ ∈ S} · |V| = |F| · (|S| + 𝒮(S; s₀, s₁))`: incidence = average + Shaw operator. -/
theorem incidence_eq_average_add_shaw (S : Finset V) (s₀ s₁ : V) :
    ((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ) * (Fintype.card V : ℂ)
      = (Fintype.card F : ℂ) * ((S.card : ℂ) + shawError (F := F) S s₀ s₁) := by
  classical
  rw [lineIncidence_spectral]
  congr 1
  -- ∑_ψ (if dirChar=0 then ∑_s ψ(s₀−s) else 0) = |S| + 𝒮
  rw [← Finset.add_sum_erase univ
        (fun ψ : AddChar V ℂ => if directionChar (F := F) ψ s₁ = 0 then ∑ s ∈ S, ψ (s₀ - s) else 0)
        (Finset.mem_univ (0 : AddChar V ℂ))]
  congr 1
  · -- the trivial-character term is exactly |S|
    rw [if_pos (directionChar_zero (F := F) s₁)]
    rw [show (∑ s ∈ S, (0 : AddChar V ℂ) (s₀ - s)) = ∑ _s ∈ S, (1 : ℂ) from
      Finset.sum_congr rfl (fun s _ => by simp)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · -- the rest is the Shaw operator
    rw [shawError, ← Finset.add_sum_erase univ
        (fun ψ : AddChar V ℂ =>
          if directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0 then ∑ s ∈ S, ψ (s₀ - s) else 0)
        (Finset.mem_univ (0 : AddChar V ℂ))]
    rw [if_neg (by simp), zero_add]
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    have hψ0 : ψ ≠ 0 := (Finset.mem_erase.mp hψ).1
    by_cases hd : directionChar (F := F) ψ s₁ = 0
    · rw [if_pos hd, if_pos ⟨hd, hψ0⟩]
    · rw [if_neg hd, if_neg (fun h => hd h.1)]

end ArkLib.ProximityGap.ShawOperator

#print axioms ArkLib.ProximityGap.ShawOperator.incidence_eq_average_add_shaw
