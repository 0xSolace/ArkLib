/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NextDifferenceVariety

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# EXTEND — the difference-variety first moment `DiffTrace` is **REAL** (#444)

**Frontier-movement extension of `_NextDifferenceVariety`.**  That file reduced the off-diagonal
*second* moment to the *first* moment of `Jphase` over the difference variety,
`DiffTrace θ Rel = Σ_T Σ_{T' ≠ T} Jphase θ (diffTuple T T')`, and named the open core
`FirstMomentDiffCancellation θ Rel S := (DiffTrace θ Rel).re ≤ S`, a bound on the **real part**.

This file proves the structural fact that makes that `.re` bound LOSE NOTHING: the off-diagonal
first moment is **real**.

## The mechanism (conjugate-swap symmetry)

For a unit additive character `θ`, each pair summand satisfies the conjugate-swap identity
```
        pairCorr(T', T)  =  Jphase θ T' · conj (Jphase θ T)
                         =  conj ( Jphase θ T · conj (Jphase θ T') )
                         =  conj ( pairCorr(T, T') ).
```
The off-diagonal index set `{(T, T') : T ∈ Rel, T' ∈ Rel.erase T}` is **symmetric** under swapping
the two summation variables (`erase_swap_iff`).  Summing the conjugate-swap identity over this
symmetric set (`Finset.sum_comm'`), the total double sum equals its own complex conjugate, hence is
real.

By `_NextDifferenceVariety.secondMoment_eq_firstMoment_diff` this off-diagonal second moment EQUALS
`DiffTrace θ Rel`, so `DiffTrace θ Rel` is real: `(DiffTrace θ Rel).im = 0` and
`((DiffTrace θ Rel).re : ℂ) = DiffTrace θ Rel`.

## Consequence for the open core

`FirstMomentDiffCancellation` bounds `(DiffTrace).re`.  Because `DiffTrace` is real, that real part
**is** the entire first moment — the `.re` projection discards nothing.  So a future Lang–Weil / Katz
equidistribution estimate that bounds the *modulus* `|DiffTrace|` (the natural output of a
character-sum estimate) immediately bounds `(DiffTrace).re` and hence discharges
`FirstMomentDiffCancellation` with the SAME slack: `|DiffTrace| ≤ S ⟹ (DiffTrace).re ≤ S`.  This is
the bridge `firstMoment_modulus_to_re` below.

## Probe

`scripts/probes/probe_dooriv_difftrace_reality.py` (proper `μ_n < F_p^*`, `p ≫ n³`, never `n=q−1`,
`n=16,32,64`, `β∈{4,4.5}`, `r∈{3,4,5}`): the full off-diagonal double sum has `|Im| ≤ 8·10⁻³⁰`
(float noise) and `|pairCorr(T',T) − conj pairCorr(T,T')| = 0` exactly across all configs.

## What this file PROVES (axiom-clean, no `sorry`)

* `pairCorr_swap_conj` — the pointwise conjugate-swap identity;
* `erase_swap_iff` — the off-diagonal index set is symmetric under the swap of summation variables;
* `secondMoment_offdiag_conj_eq_self` — the off-diagonal second moment equals its own conjugate;
* `diffTrace_conj_eq_self`, `diffTrace_im_eq_zero`, `diffTrace_ofReal_re` — `DiffTrace` is real;
* `diffTrace_norm_eq_abs_re` — because the trace is real, its complex norm is exactly
  `|(DiffTrace).re|`;
* `firstMoment_modulus_to_re` — a modulus bound `|DiffTrace| ≤ S` gives the named-core real-part
  bound `FirstMomentDiffCancellation θ Rel S`;
* `modulus_to_secondMoment_re_bound` — the same modulus estimate feeds the off-diagonal
  second-moment real-part bound directly.

NO CORE / cancellation / completion / moment-saving / capacity claim: `DiffTrace` is NOT bounded
here.  This is a structural reality lemma plus the consumer bridge from a modulus estimate.  #444.
-/

namespace ArkLib.ProximityGap.Frontier.DiffTraceReality

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ}

/-! ## §1 The pointwise conjugate-swap identity -/

/-- **`pairCorr_swap_conj`** — swapping the two relations conjugates the second-moment summand. -/
theorem pairCorr_swap_conj (T T' : Fin r → R) :
    Jphase θ T' * conj (Jphase θ T) = conj (Jphase θ T * conj (Jphase θ T')) := by
  rw [map_mul, Complex.conj_conj, mul_comm]

variable [DecidableEq (Fin r → R)]

/-! ## §2 The off-diagonal second moment is its own conjugate (hence real) -/

/-- **`erase_swap_iff`** — the off-diagonal index set `{(T,T') : T ∈ Rel, T' ∈ Rel.erase T}` is
**symmetric** under swapping the two summation variables.  This is the hypothesis fed to
`Finset.sum_comm'`. -/
theorem erase_swap_iff (Rel : Finset (Fin r → R)) (T T' : Fin r → R) :
    (T ∈ Rel ∧ T' ∈ Rel.erase T) ↔ (T ∈ Rel.erase T' ∧ T' ∈ Rel) := by
  simp only [Finset.mem_erase]; tauto

/-- **`secondMoment_offdiag_conj_eq_self`** — the conjugate of the off-diagonal second moment equals
itself.  Proof: push `conj` inside (each summand becomes the swapped pair summand by
`pairCorr_swap_conj`), then relabel the two summation variables by `Finset.sum_comm'` over the
symmetric off-diagonal index set (`erase_swap_iff`). -/
theorem secondMoment_offdiag_conj_eq_self (Rel : Finset (Fin r → R)) :
    conj (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T'))
      = ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T') := by
  -- push conj inside the double sum; each summand becomes the swapped pair summand
  rw [map_sum]
  have hinner : ∀ T ∈ Rel,
      conj (∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T'))
        = ∑ T' ∈ Rel.erase T, Jphase θ T' * conj (Jphase θ T) := by
    intro T _; rw [map_sum]
    exact Finset.sum_congr rfl (fun T' _ => (pairCorr_swap_conj T T').symm)
  rw [Finset.sum_congr rfl hinner]
  -- relabel T ↔ T' over the symmetric off-diagonal index set
  rw [Finset.sum_comm' (erase_swap_iff Rel)]

/-! ## §4 `DiffTrace` is real -/

/-- **`diffTrace_conj_eq_self`** — `conj (DiffTrace θ Rel) = DiffTrace θ Rel`.  Uses the second→first
moment identity to identify `DiffTrace` with the off-diagonal second moment, then
`secondMoment_offdiag_conj_eq_self`. -/
theorem diffTrace_conj_eq_self (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    conj (DiffTrace θ Rel) = DiffTrace θ Rel := by
  rw [diffTrace_eq_secondMoment hmul hone hunit Rel,
      secondMoment_offdiag_conj_eq_self Rel]

/-- **`diffTrace_im_eq_zero`** — the difference-variety first moment is real. -/
theorem diffTrace_im_eq_zero (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (DiffTrace θ Rel).im = 0 := by
  have h := diffTrace_conj_eq_self hmul hone hunit Rel
  have : (conj (DiffTrace θ Rel)).im = (DiffTrace θ Rel).im := by rw [h]
  rw [Complex.conj_im] at this
  linarith

/-- **`diffTrace_ofReal_re`** — `((DiffTrace θ Rel).re : ℂ) = DiffTrace θ Rel`: the real part IS the
full first moment (nothing is discarded by the `.re` in `FirstMomentDiffCancellation`). -/
theorem diffTrace_ofReal_re (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    ((DiffTrace θ Rel).re : ℂ) = DiffTrace θ Rel := by
  have him := diffTrace_im_eq_zero hmul hone hunit Rel
  apply Complex.ext <;> simp [him]

/-! ## §5 The consumer bridge: a modulus bound gives the named-core real-part bound -/

/-- **`diffTrace_norm_eq_abs_re`** — because the difference-variety first moment is real, its
complex norm is exactly the absolute value of its real part.  This pins the bookkeeping at the
Lang–Weil / Katz handoff: a modulus estimate on `DiffTrace` is not hiding any imaginary component. -/
theorem diffTrace_norm_eq_abs_re (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    ‖DiffTrace θ Rel‖ = |(DiffTrace θ Rel).re| := by
  rw [← diffTrace_ofReal_re hmul hone hunit Rel]
  simp

/-- **`firstMoment_modulus_to_re`** — a bound on the *modulus* of the first moment
(`‖DiffTrace θ Rel‖ ≤ S`, the natural output of a Lang–Weil / Katz character-sum
estimate) yields the named open core `FirstMomentDiffCancellation θ Rel S` (a `.re` bound), with the
SAME slack `S`.  This is the one-line bridge from a modulus equidistribution estimate on `V_diff` to
the off-diagonal pair-cancellation core, valid because `DiffTrace` is real. -/
theorem firstMoment_modulus_to_re (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : ‖DiffTrace θ Rel‖ ≤ S) :
    (DiffTrace θ Rel).re ≤ S :=
  le_trans (Complex.re_le_norm _) h

/-- **`modulus_to_secondMoment_re_bound`** — end-to-end consumer: a future modulus estimate on the
difference-variety first moment immediately bounds the real part of the original off-diagonal
second-moment sum.  This packages `_NextDifferenceVariety.firstMoment_to_secondMoment_bound` with
`firstMoment_modulus_to_re`, so later work can plug a Katz/Lang–Weil estimate into the variance core
without redoing the trace/second-moment bookkeeping. -/
theorem modulus_to_secondMoment_re_bound (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R))
    (S : ℝ) (h : ‖DiffTrace θ Rel‖ ≤ S) :
    (∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, Jphase θ T * conj (Jphase θ T')).re ≤ S :=
  firstMoment_to_secondMoment_bound hmul hone hunit Rel S (firstMoment_modulus_to_re Rel S h)

end ArkLib.ProximityGap.Frontier.DiffTraceReality

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.pairCorr_swap_conj
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.secondMoment_offdiag_conj_eq_self
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.diffTrace_conj_eq_self
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.diffTrace_im_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.diffTrace_ofReal_re
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.diffTrace_norm_eq_abs_re
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.firstMoment_modulus_to_re
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceReality.modulus_to_secondMoment_re_bound
