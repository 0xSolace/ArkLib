/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The spectral form of the line–ball incidence (#389): the line-sum collapse

The governing law of δ* is `mcaDeltaStar = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}`, and the
incidence is `#{γ : s₀ + γ·s₁ ∈ S_w}` for an affine line in the syndrome space (`S_w` = the
low-weight-coset set). Fourier-expanding `1_{S_w}` turns this incidence into a character sum, and
the whole expansion **collapses onto the hyperplane `s₁^⊥`** because of the elementary identity
proved here:

> **`lineSum_collapse`** — for any additive character `ψ` of an `F`-module `V` and any `s₀, s₁`,
> `∑_{γ ∈ F} ψ(s₀ + γ·s₁) = ψ(s₀) · (if ψ vanishes on the line `F·s₁` then |F| else 0)`.

The summand `ψ(s₀+γ·s₁) = ψ(s₀)·χ(γ)` factors through the additive character `χ := ψ∘(·s₁)` of
`F`, and `∑_γ χ(γ) = |F|·[χ trivial]` (`AddChar.sum_eq_ite`). The character `χ` is trivial exactly
when `ψ` annihilates the direction `s₁` (`ψ ⊥ s₁`). Consequently, in the Fourier expansion of any
indicator, **only the `s₁^⊥` frequencies survive the γ-average** — the `a=0` term is the average
incidence `q·|S_w|/q^m`, and everything else is the spectral error supported on `s₁^⊥`. This is the
exact mechanism that reduces the prize residual to "beat Parseval on the `s₁^⊥` hyperplane"
(see `docs/kb/deltastar-...`); the trivial Parseval bound `|error| ≤ √(q·|S_w|)` is W4-weak in the
prize regime, so the surviving open core is precisely the worst-case incomplete character sum.

Axiom-clean; pure character theory, no field-size or regime hypotheses.
-/

open Finset

namespace ArkLib.ProximityGap.LineIncidenceSpectral

variable {F V R : Type*} [Field F] [Fintype F] [AddCommGroup V] [Module F V]
  [CommRing R] [IsDomain R]

/-- The additive character of `F` obtained by restricting `ψ` to the line through `s₁`:
`directionChar ψ s₁ γ = ψ (γ • s₁)`. Trivial iff `ψ` annihilates `F·s₁`. -/
def directionChar (ψ : AddChar V R) (s₁ : V) : AddChar F R :=
  ψ.compAddMonoidHom ((smulAddHom F V).flip s₁)

omit [Fintype F] [IsDomain R] in
@[simp] theorem directionChar_apply (ψ : AddChar V R) (s₁ : V) (γ : F) :
    directionChar ψ s₁ γ = ψ (γ • s₁) := by
  simp [directionChar]

/-- **The line-sum collapse.** Summing an additive character along an affine line `s₀ + γ·s₁`
collapses to `ψ(s₀)·|F|` when `ψ` is trivial on the direction `s₁`, and to `0` otherwise. -/
theorem lineSum_collapse (ψ : AddChar V R) (s₀ s₁ : V)
    [Decidable (directionChar (F := F) ψ s₁ = 0)] :
    (∑ γ : F, ψ (s₀ + γ • s₁))
      = ψ s₀ * (if directionChar (F := F) ψ s₁ = 0 then (Fintype.card F : R) else 0) := by
  have hfac : ∀ γ : F, ψ (s₀ + γ • s₁) = ψ s₀ * directionChar (F := F) ψ s₁ γ := by
    intro γ
    rw [directionChar_apply, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun γ _ => hfac γ), ← Finset.mul_sum, AddChar.sum_eq_ite]

end ArkLib.ProximityGap.LineIncidenceSpectral
