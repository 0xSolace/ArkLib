/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PaleyCayleyEigenvalue

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# `η_b` is REAL on a negation-closed connection set (the N13 phase-is-a-sign constraint, #444)

**Frontier constraint brick (NON-MOMENT, EXTEND-proven).** For the prize subgroup `G = μ_n` with
`n` even we have `−1 ∈ μ_n`, hence `μ_n` is **negation-closed** (`x ∈ G ⟹ −x ∈ G`). This file
proves that on ANY negation-closed `G` the incomplete Gauss period

> `η_b = Σ_{x∈G} ψ(b·x)`   (`PaleyCayleyEigenvalue.eta`)

is **real-valued** for every frequency `b`. We prove `(starRingEnd ℂ) (η_b) = η_b`
(`eta_conj_eq_self`), equivalently `(η_b).im = 0` (`eta_im_eq_zero`), equivalently
`η_b = ((η_b).re : ℂ)` (`eta_eq_ofReal_re`).

## The math (one reindex)

`conj(η_b) = Σ_{x∈G} conj(ψ(b·x)) = Σ_{x∈G} ψ(−(b·x)) = Σ_{x∈G} ψ(b·(−x))`. Now reindex the finite
sum by the involution `x ↦ −x`, which is a bijection `G → G` precisely because `G` is
negation-closed (`Finset.sum_nbij'` with inverse itself); the summand becomes `ψ(b·x')` over
`x' ∈ G`, i.e. `η_b` again. So `conj(η_b) = η_b`, forcing `η_b ∈ ℝ`. The only field input is
`AddChar.starComp_apply` (`conj∘ψ = ψ∘neg`, needs `0 < ringChar F`), the same conjugate identity the
in-tree fourth-moment file uses.

## Why this is a frontier CONSTRAINT, not a closure (rules 3,4,6 + N13)

The census §1.3 names the **N13 phase-aware contractive transfer operator**
`(𝒯f)(b) = f(b) + e^{iθ_b} f(ζb)` (the strongest surviving "third route") whose open object is
the relative-dilation phase law `θ_b = arg(η_{ζb}) − arg(η_b)`. The issue body §3.4 records a
heuristic "`−1 ∈ μ_n` forces `η_b` real = a SIGN not a phase"; that heuristic was **never a
theorem**. This
file makes it one: on the negation-closed `μ_n`, `η_b ∈ ℝ`, so `arg(η_b) ∈ {0, π}` and the N13
"phase" `θ_b` is **quantized to a SIGN `±1`** (`eta_mem_range_ofReal` records `η_b ∈ ℝ`, i.e. the
constraint that pins the phase to the two-element set). This SHARPENS the N13 residual (the
operator's "phase" is discrete), it does NOT bound `‖η_b‖`. The `√(n log(p/n))` core is untouched
and OPEN: a real number can still be as large as `n`, so realness alone gives no cancellation
(rule 4: this is a structural constraint on the open lever, mapped precisely; not a bound on `M`).
NON-MOMENT (pure character-sum symmetry, not an additive-energy / Wick route). Holds for `n` even
(`−1 ∈ μ_n`); for `n` odd `μ_n` is NOT negation-closed and `η_b` is genuinely complex (the
hypothesis is essential, not cosmetic), but the prize regime is `n = 2^a` (even), so the hypothesis
always holds there.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open Finset AddChar
open ProximityGap.Frontier.PaleyCayleyEigenvalue

namespace ProximityGap.Frontier.EtaRealNegClosed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The conjugate-of-character identity on a finite field: `conj(ψ a) = ψ (−a)`. Same input as the
in-tree fourth-moment file (`AddChar.starComp_apply` + `AddChar.inv_apply`, needs `0 < ringChar F`,
which holds on a finite field). -/
theorem conj_addChar (ψ : AddChar F ℂ) (a : F) :
    (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  rw [AddChar.starComp_apply hchar, AddChar.inv_apply]

/-- **`η_b` is conjugation-invariant on a negation-closed `G`: `conj(η_b) = η_b`.**

`conj(η_b) = Σ_{x∈G} ψ(−(b·x)) = Σ_{x∈G} ψ(b·(−x))`; reindex `x ↦ −x` (a bijection `G → G` since `G`
is negation-closed) to recover `Σ_{x∈G} ψ(b·x) = η_b`. -/
theorem eta_conj_eq_self {ψ : AddChar F ℂ} {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by
  unfold eta
  rw [map_sum]
  -- conj(ψ(b·x)) = ψ(−(b·x)) = ψ(b·(−x)); then reindex x ↦ −x.
  have hstep : ∀ x ∈ G, (starRingEnd ℂ) (ψ (b * x)) = ψ (b * (-x)) := by
    intro x _
    rw [conj_addChar]
    congr 1
    ring
  rw [Finset.sum_congr rfl hstep]
  -- Σ_{x∈G} ψ(b·(−x)) = Σ_{x'∈G} ψ(b·x') via the involution x ↦ −x on G.
  refine Finset.sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
  · intro x hx; exact hG x hx
  · intro x hx; exact hG x hx
  · intro x _; exact neg_neg x
  · intro x _; exact neg_neg x
  · intro x _; rfl

/-- **`η_b` has zero imaginary part on a negation-closed `G`.** Immediate from
`eta_conj_eq_self` via `Complex.conj_eq_iff_im`. -/
theorem eta_im_eq_zero {ψ : AddChar F ℂ} {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    (eta ψ G b).im = 0 :=
  (Complex.conj_eq_iff_im.mp (eta_conj_eq_self hG b))

/-- **`η_b` equals the coercion of its real part** on a negation-closed `G`: `η_b = ((η_b).re : ℂ)`.
The usable "it's a real number" form. -/
theorem eta_eq_ofReal_re {ψ : AddChar F ℂ} {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    eta ψ G b = ((eta ψ G b).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [eta_im_eq_zero hG b]; simp

/-- **The N13 phase-is-a-sign constraint (rule-4 cartography).** On a negation-closed `G` the period
`η_b` lies in `ℝ` (`Set.range Complex.ofReal`), so its argument is quantized to `{0, π}` and the
N13 transfer-operator "phase" `e^{iθ_b}` is pinned to a discrete SIGN `±1`. This is a structural
constraint on the open N13 lever, NOT a bound on `‖η_b‖` (realness is `√(log)`-blind: a real `η_b`
can still be as large as `|G|`). -/
theorem eta_mem_range_ofReal {ψ : AddChar F ℂ} {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    eta ψ G b ∈ Set.range (Complex.ofReal) :=
  ⟨(eta ψ G b).re, (eta_eq_ofReal_re hG b).symm⟩

/-- **`‖η_b‖ = |(η_b).re|`** on a negation-closed `G`: the norm is the absolute value of the (real)
period. The honest companion to the constraint. It shows realness reduces the complex sup-norm `M`
to a sup of absolute values of REAL numbers, but gives NO upper bound on those values (the wall). -/
theorem eta_norm_eq_abs_re {ψ : AddChar F ℂ} {G : Finset F}
    (hG : ∀ x ∈ G, -x ∈ G) (b : F) :
    ‖eta ψ G b‖ = |(eta ψ G b).re| := by
  conv_lhs => rw [eta_eq_ofReal_re hG b]
  simp

end ProximityGap.Frontier.EtaRealNegClosed
