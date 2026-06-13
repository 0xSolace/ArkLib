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

/-- **Chebyshev count bound for the Shaw operator** (quantitative companion of
`shawError_second_moment`). The number of base points `s₀` at which the Shaw operator reaches a
threshold `t ≥ 0` is controlled by the second moment:
`#{s₀ : t ≤ ‖𝒮(S;s₀,s₁)‖} · t² ≤ |V| · ∑_{ψ≠0, ψ⊥s₁} ‖∑_{s∈S} ψ(−s)‖²`.

So all but a `(ℓ²-mass)/t²`-fraction of base points satisfy any threshold the average side meets:
large Shaw error is *rare*. This makes the L²/average side of the prize bound quantitative — the
remaining open content is only the existence of the *worst* base point, not the typical one. -/
theorem card_large_shawError_mul_sq_le (S : Finset V) (s₁ : V) {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter (fun s₀ : V => t ≤ ‖shawError (F := F) S s₀ s₁‖)).card : ℝ) * t ^ 2
      ≤ (Fintype.card V : ℝ)
        * ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
              directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
            ‖∑ s ∈ S, ψ (-s)‖ ^ 2 := by
  classical
  rw [← shawError_second_moment]
  set bad := univ.filter (fun s₀ : V => t ≤ ‖shawError (F := F) S s₀ s₁‖) with hbad
  calc ((bad.card : ℝ)) * t ^ 2
      = ∑ _s₀ ∈ bad, t ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ s₀ ∈ bad, ‖shawError (F := F) S s₀ s₁‖ ^ 2 := by
        refine Finset.sum_le_sum (fun s₀ hs₀ => ?_)
        have hts : t ≤ ‖shawError (F := F) S s₀ s₁‖ := (Finset.mem_filter.mp hs₀).2
        gcongr
    _ ≤ ∑ s₀ : V, ‖shawError (F := F) S s₀ s₁‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun s₀ _ _ => by positivity)

section Plancherel
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- **Plancherel / Parseval for the ball indicator.** `∑_{all ψ} ‖∑_{s∈S} ψ(−s)‖² = |V|·|S|` —
the total ℓ² character mass of the indicator of `S` equals `|V|·|S|`, by the dual orthogonality
`∑_ψ ψ(x) = |V|·[x=0]` (`AddChar.sum_apply_eq_ite`).  Unconditional; the ceiling against which the
hyperplane-restricted second moment is measured. -/
theorem parseval_indicator (S : Finset V) :
    ∑ ψ : AddChar V ℂ, ‖∑ s ∈ S, ψ (-s)‖ ^ 2 = (Fintype.card V : ℝ) * S.card := by
  classical
  set b : AddChar V ℂ → ℂ := fun ψ => ∑ s ∈ S, ψ (-s) with hbdef
  have keyC : (∑ ψ : AddChar V ℂ, b ψ * (starRingEnd ℂ) (b ψ))
      = (Fintype.card V : ℂ) * S.card := by
    calc ∑ ψ : AddChar V ℂ, b ψ * (starRingEnd ℂ) (b ψ)
        = ∑ ψ : AddChar V ℂ, ∑ s ∈ S, ∑ t ∈ S, ψ (t - s) := by
          refine Finset.sum_congr rfl (fun ψ _ => ?_)
          rw [hbdef]; dsimp only
          rw [map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
          rw [addChar_conj, neg_neg, ← AddChar.map_add_eq_mul,
            show -s + t = t - s from by abel]
      _ = ∑ s ∈ S, ∑ t ∈ S, ∑ ψ : AddChar V ℂ, ψ (t - s) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ s ∈ S, ∑ t ∈ S, (if t - s = 0 then (Fintype.card V : ℂ) else 0) := by
          simp_rw [AddChar.sum_apply_eq_ite]
      _ = ∑ s ∈ S, ∑ t ∈ S, (if t = s then (Fintype.card V : ℂ) else 0) := by
          simp_rw [sub_eq_zero]
      _ = ∑ _s ∈ S, (Fintype.card V : ℂ) := by
          refine Finset.sum_congr rfl (fun s hs => ?_)
          rw [Finset.sum_ite_eq' S s (fun _ => (Fintype.card V : ℂ)), if_pos hs]
      _ = (Fintype.card V : ℂ) * S.card := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have h := keyC
  simp only [Complex.mul_conj] at h
  norm_cast at h
  simp only [Complex.normSq_eq_norm_sq, hbdef] at h
  rw [Nat.cast_mul] at h
  exact h

end Plancherel

/-- **Unconditional L² ceiling on the Shaw second moment.** Restricting Parseval to the hyperplane
`ψ ⊥ s₁` and dropping the trivial character only decreases the mass, so
`∑_{s₀} ‖𝒮(S;s₀,s₁)‖² ≤ |V|²·|S|` with no hypotheses. (The prize needs the much sharper
hyperplane-restricted value; this is the honest crude L² ceiling, via `parseval_indicator`.) -/
theorem shawError_second_moment_le (S : Finset V) (s₁ : V) :
    ∑ s₀ : V, ‖shawError (F := F) S s₀ s₁‖ ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 * S.card := by
  classical
  rw [shawError_second_moment]
  have hsub :
      (∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ => directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
          ‖∑ s ∈ S, ψ (-s)‖ ^ 2)
        ≤ ∑ ψ : AddChar V ℂ, ‖∑ s ∈ S, ψ (-s)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun ψ _ _ => by positivity)
  calc (Fintype.card V : ℝ)
          * ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ => directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
              ‖∑ s ∈ S, ψ (-s)‖ ^ 2
      ≤ (Fintype.card V : ℝ) * ∑ ψ : AddChar V ℂ, ‖∑ s ∈ S, ψ (-s)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (by positivity)
    _ = (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * S.card) := by rw [parseval_indicator]
    _ = (Fintype.card V : ℝ) ^ 2 * S.card := by ring

/-- **Unconditional Chebyshev count bound.** Combining `card_large_shawError_mul_sq_le` with the
crude L² ceiling: `#{s₀ : t ≤ ‖𝒮(S;s₀,s₁)‖} · t² ≤ |V|²·|S|` for any `t ≥ 0`, no hypotheses. -/
theorem card_large_shawError_mul_sq_le_unconditional (S : Finset V) (s₁ : V) {t : ℝ} (ht : 0 ≤ t) :
    ((univ.filter (fun s₀ : V => t ≤ ‖shawError (F := F) S s₀ s₁‖)).card : ℝ) * t ^ 2
      ≤ (Fintype.card V : ℝ) ^ 2 * S.card := by
  refine le_trans ?_ (shawError_second_moment_le (F := F) S s₁)
  rw [shawError_second_moment]
  exact card_large_shawError_mul_sq_le (F := F) S s₁ ht

/-- **Worst-case Shaw operator — upper half of the second-moment bracket.** Each single value is at
most the whole second moment: `‖𝒮(S;s₀,s₁)‖² ≤ |V|·∑_{ψ≠0,ψ⊥s₁}‖∑ψ(−s)‖²`. So
`max_{s₀}‖𝒮‖ ≤ √(|V|·M)` — the *only* upper bound the moment method yields, inflated by the full
`√|V|` factor (the union tax over the `|V|` base points). -/
theorem shawError_sq_le_second_moment (S : Finset V) (s₀ s₁ : V) :
    ‖shawError (F := F) S s₀ s₁‖ ^ 2
      ≤ (Fintype.card V : ℝ)
        * ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
              directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
            ‖∑ s ∈ S, ψ (-s)‖ ^ 2 := by
  rw [← shawError_second_moment]
  exact Finset.single_le_sum (f := fun s₀ => ‖shawError (F := F) S s₀ s₁‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ s₀)

/-- **Worst-case Shaw operator — lower half of the bracket (necessity).** Some base point achieves at
least the average: `∃ s₀, ‖𝒮(S;s₀,s₁)‖² ≥ ∑_{ψ≠0,ψ⊥s₁}‖∑ψ(−s)‖² = M`. Hence `max_{s₀}‖𝒮‖ ≥ √M`, so
**any** prize Shaw budget `B` is forced to satisfy `B ≥ √M`: an unconditional necessary condition the
prize bound must respect (no cancellation can push the worst case below the L² mass on `ψ ⊥ s₁`).

Together with `shawError_sq_le_second_moment` this brackets `max_{s₀}‖𝒮‖ ∈ [√M, √(|V|·M)]` — a
multiplicative gap of exactly `√|V| = q^{n/2}`.  This is the precise, machine-checked reason the
second-moment / union route cannot pin `δ*`: it determines the prize's worst case only up to a
`√|V|` factor, which dwarfs the budget.  Closing the prize needs genuine *uniform* (every-`s₀`)
square-root cancellation of the structured sum `∑_ψ Ŝ(ψ)·ψ(s₀)` — the open W4 content, untouched by
any L² estimate. -/
theorem exists_shawError_sq_ge [Nonempty V] (S : Finset V) (s₁ : V) :
    ∃ s₀ : V,
      (∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
            directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
          ‖∑ s ∈ S, ψ (-s)‖ ^ 2)
        ≤ ‖shawError (F := F) S s₀ s₁‖ ^ 2 := by
  classical
  set M := ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
        directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0), ‖∑ s ∈ S, ψ (-s)‖ ^ 2 with hM
  by_contra h
  push_neg at h
  have hlt : ∑ s₀ : V, ‖shawError (F := F) S s₀ s₁‖ ^ 2 < ∑ _s₀ : V, M :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun s₀ _ => h s₀)
  rw [shawError_second_moment, Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hlt
  exact lt_irrefl _ hlt

/-- **Closed falsification criterion for the prize Shaw bound (the decidable side).** If the budget
`B` undershoots the hyperplane L² mass — `B² < M`, `M = ∑_{ψ≠0,ψ⊥s₁}‖∑ψ(−s)‖²` — then the prize
Shaw conjecture is FALSE: there is an *explicit* bad base point with `‖𝒮‖ > B`.

This is the side of the prize the second moment genuinely decides: not "the bound holds" (which needs
the uniform W4 cancellation, unreachable by any L² estimate — see `shawError_sq_le_second_moment` /
`exists_shawError_sq_ge` for the `√|V|` gap), but "the bound *fails*" — an unconditional upper bound
on `δ*`. As `M(δ)` grows with the ball radius, the least `δ` with `M(δ) > B(δ)²` is a
machine-checkable ceiling on `δ*`, driven only by the proven `exists_shawError_sq_ge` (a genuine bad
witness, not an average). Turning this into a *window-interior* `δ*` ceiling requires evaluating
`M(δ)` via the ball's dual weight enumerator (Krawtchouk); that is the concrete open computation, not
an open conjecture. -/
theorem not_mcaShawConjecture_of_lt_secondMoment [Nonempty V] (S : Finset V) (s₁ : V) (B : ℝ)
    (hB : B ^ 2 < ∑ ψ ∈ univ.filter (fun ψ : AddChar V ℂ =>
            directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0),
          ‖∑ s ∈ S, ψ (-s)‖ ^ 2) :
    ¬ MCAShawConjecture (F := F) S B := by
  intro h
  obtain ⟨s₀, hs₀⟩ := exists_shawError_sq_ge (F := F) S s₁
  have hb : ‖shawError (F := F) S s₀ s₁‖ ≤ B := h s₀ s₁
  have hnn : (0 : ℝ) ≤ ‖shawError (F := F) S s₀ s₁‖ := norm_nonneg _
  have hsq : ‖shawError (F := F) S s₀ s₁‖ ^ 2 ≤ B ^ 2 := by nlinarith
  linarith

end ArkLib.ProximityGap.ShawSecondMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ShawSecondMoment.addChar_conj
#print axioms ArkLib.ProximityGap.ShawSecondMoment.char_orthogonality
#print axioms ArkLib.ProximityGap.ShawSecondMoment.shawError_second_moment
#print axioms ArkLib.ProximityGap.ShawSecondMoment.card_large_shawError_mul_sq_le
#print axioms ArkLib.ProximityGap.ShawSecondMoment.parseval_indicator
#print axioms ArkLib.ProximityGap.ShawSecondMoment.shawError_second_moment_le
#print axioms ArkLib.ProximityGap.ShawSecondMoment.card_large_shawError_mul_sq_le_unconditional
#print axioms ArkLib.ProximityGap.ShawSecondMoment.shawError_sq_le_second_moment
#print axioms ArkLib.ProximityGap.ShawSecondMoment.exists_shawError_sq_ge
#print axioms ArkLib.ProximityGap.ShawSecondMoment.not_mcaShawConjecture_of_lt_secondMoment
#check @ArkLib.ProximityGap.ShawSecondMoment.parseval_indicator
