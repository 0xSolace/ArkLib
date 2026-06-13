/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ShawOperator
import Mathlib

/-!
# The second moment of the Shaw operator (#389/#371)

The Shaw operator `𝒮(S; s₀, s₁)` (`ShawOperator.shawError`) is the off-trivial spectral error of the
line–ball incidence; the proximity prize is exactly the worst-case bound `max_{s₀} ‖𝒮‖ ≤ |Ball|`
(`MCAShawConjecture`).  This file computes its **second moment over the base point `s₀`** exactly, by
character orthogonality on `V` — the L²/average side of that prize bound:

> **`shawError_second_moment`** —
> `∑_{s₀} ‖𝒮(S; s₀, s₁)‖² = |V| · ∑_{ψ ≠ 0, ψ ⊥ s₁} ‖∑_{s∈S} ψ(−s)‖²`.

The right side is the `ℓ²` Fourier mass of the ball indicator on the hyperplane `ψ ⊥ s₁`; for the
prize δ-ball it is `≤ |Ball|²` in the prize regime, so **the prize bound holds on average / in L²**.
The remaining open core is precisely the worst-`s₀` excess over this average — the `Θ(√(log))`
gap that the moment method provably cannot close (cf. `ShawFlatnessRefuted`).  So this lemma isolates
the open content of the prize as a single, named, falsifiable inequality (worst vs. average), with the
average side now proven.

Supporting, reusable: `addChar_conj` (conjugation of a finite-group character value is the negation
pullback) and `char_orthogonality` (`∑_x ψ(x)·ψ'(−x) = |V|·[ψ=ψ']`).  Axiom-clean.
-/

open Finset
open ArkLib.ProximityGap.LineIncidenceSpectral
open ArkLib.ProximityGap.ShawOperator

namespace ArkLib.ProximityGap.ShawSecondMoment

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Fintype V] [DecidableEq V]
  [Module F V]

/-- Complex conjugation of a finite-group additive-character value is the negation pullback:
`conj (ψ a) = ψ (−a)` (the value is a root of unity, so `conj = inv = (−·)`-pullback). -/
theorem addChar_conj (ψ : AddChar V ℂ) (a : V) :
    (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hca : (Fintype.card V) • a = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).mp addOrderOf_dvd_card
  have hpow : ψ a ^ (Fintype.card V) = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, hca, ψ.map_zero_eq_one]
  have hnorm : ‖ψ a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (by positivity)
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj hnorm).symm

/-- The Shaw operator over the filtered character set with the `s₀`-phase factored out. -/
theorem shawError_eq_phase_sum (S : Finset V) (s₀ s₁ : V) :
    shawError (F := F) S s₀ s₁
      = ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
            directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
          ψ s₀ * (∑ s ∈ S, ψ (-s)) := by
  rw [shawError, ← Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [show s₀ - s = s₀ + (-s) by abel, AddChar.map_add_eq_mul]

/-- Character orthogonality on the finite group `V`: `∑_{x} ψ(x)·ψ'(−x) = |V|·[ψ=ψ']`. -/
theorem char_orthogonality (ψ ψ' : AddChar V ℂ) :
    (∑ x : V, ψ x * ψ' (-x)) = if ψ = ψ' then (Fintype.card V : ℂ) else 0 := by
  have hrw : ∀ x : V, ψ x * ψ' (-x) = (ψ - ψ') x := fun x => (AddChar.sub_apply ψ ψ' x).symm
  simp_rw [hrw]
  by_cases h : ψ = ψ'
  · subst h; simp [AddChar.zero_apply, Finset.card_univ]
  · rw [if_neg h]
    exact (AddChar.sum_eq_zero_iff_ne_zero).mpr (sub_ne_zero.mpr h)

/-- **The Shaw second-moment identity.** `∑_{s₀} ‖𝒮(S;s₀,s₁)‖² = |V| · ∑_{ψ≠0, ψ⊥s₁} ‖∑_{s∈S} ψ(−s)‖²`
— character orthogonality on `V` collapses the average squared Shaw operator to the `ℓ²` Fourier
mass of the ball on the hyperplane `ψ ⊥ s₁`. The L²/average side of the prize bound (it holds with
room in the prize regime); the worst-case `s₀` excess is the open core. -/
theorem shawError_second_moment (S : Finset V) (s₁ : V) :
    ∑ s₀ : V, ‖shawError (F := F) S s₀ s₁‖ ^ 2
      = (Fintype.card V : ℝ)
        * ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
              directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
            ‖∑ s ∈ S, ψ (-s)‖ ^ 2 := by
  classical
  set Ψ := univ.filter (fun ψ : AddChar V ℂ => directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0) with hΨ
  set b : AddChar V ℂ → ℂ := fun ψ => ∑ s ∈ S, ψ (-s) with hbdef
  have key : (∑ s₀ : V, shawError (F := F) S s₀ s₁ * (starRingEnd ℂ) (shawError (F := F) S s₀ s₁))
      = (Fintype.card V : ℂ) * ∑ ψ ∈ Ψ, b ψ * (starRingEnd ℂ) (b ψ) := by
    have expand : ∀ s₀ : V,
        shawError (F := F) S s₀ s₁ * (starRingEnd ℂ) (shawError (F := F) S s₀ s₁)
          = ∑ ψ ∈ Ψ, ∑ ψ' ∈ Ψ, (ψ s₀ * ψ' (-s₀)) * (b ψ * (starRingEnd ℂ) (b ψ')) := by
      intro s₀
      rw [shawError_eq_phase_sum (F := F) S s₀ s₁, ← hΨ, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun ψ _ => Finset.sum_congr rfl (fun ψ' _ => ?_))
      rw [map_mul, addChar_conj]; ring
    calc ∑ s₀ : V, shawError (F := F) S s₀ s₁ * (starRingEnd ℂ) (shawError (F := F) S s₀ s₁)
        = ∑ s₀ : V, ∑ ψ ∈ Ψ, ∑ ψ' ∈ Ψ, (ψ s₀ * ψ' (-s₀)) * (b ψ * (starRingEnd ℂ) (b ψ')) := by
          exact Finset.sum_congr rfl (fun s₀ _ => expand s₀)
      _ = ∑ ψ ∈ Ψ, ∑ ψ' ∈ Ψ, ∑ s₀ : V, (ψ s₀ * ψ' (-s₀)) * (b ψ * (starRingEnd ℂ) (b ψ')) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun ψ _ => Finset.sum_comm)
      _ = ∑ ψ ∈ Ψ, ∑ ψ' ∈ Ψ, (b ψ * (starRingEnd ℂ) (b ψ')) * (if ψ = ψ' then (Fintype.card V : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun ψ _ => Finset.sum_congr rfl (fun ψ' _ => ?_))
          rw [← Finset.sum_mul, char_orthogonality, mul_comm]
      _ = ∑ ψ ∈ Ψ, (b ψ * (starRingEnd ℂ) (b ψ)) * (Fintype.card V : ℂ) := by
          refine Finset.sum_congr rfl (fun ψ hψ => ?_)
          simp_rw [mul_ite, mul_zero]
          rw [Finset.sum_ite_eq Ψ ψ (fun ψ' => b ψ * (starRingEnd ℂ) (b ψ') * (Fintype.card V : ℂ)),
            if_pos hψ]
      _ = (Fintype.card V : ℂ) * ∑ ψ ∈ Ψ, b ψ * (starRingEnd ℂ) (b ψ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ψ _ => by ring)
  -- transfer to ℝ: `Complex.mul_conj` gives ↑normSq; `norm_cast` reals it; `normSq = ‖·‖²`
  have h := key
  simp only [Complex.mul_conj] at h
  norm_cast at h
  simp only [Complex.normSq_eq_norm_sq, hbdef] at h
  exact h

end ArkLib.ProximityGap.ShawSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ShawSecondMoment.addChar_conj
#print axioms ArkLib.ProximityGap.ShawSecondMoment.char_orthogonality
#print axioms ArkLib.ProximityGap.ShawSecondMoment.shawError_second_moment
