/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTracePlancherelFloor

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# EXTEND — the variance-core open bound reframed as an L² mass bound on `Σ_T Jphase θ T` (#444)

**Frontier-movement extension of `_DiffTracePlancherelFloor`.**  That file proved the Plancherel
identity `FullTrace = ‖Σ_T Jphase θ T‖²` and the exact value `DiffTrace.re = ‖Σ Jphase‖² − #Rel`.
This file uses it to give the CLEAN equivalent form of the named open core: the prize's variance-core
inequality `FirstMomentDiffCancellation` (a `.re` bound on the off-diagonal first moment) is EXACTLY
an **L² mass bound on the single linear phase sum** `Σ_T Jphase θ T`.

## The reframe — `firstMomentDiffCancellation_iff_normSq_le`

`FirstMomentDiffCancellation θ Rel S := (DiffTrace θ Rel).re ≤ S`.  By
`diffTrace_re_eq_normSq_sub_card` this is `‖Σ Jphase‖² − #Rel ≤ S`, i.e.
```
   FirstMomentDiffCancellation θ Rel S   ⟺   ‖Σ_T Jphase θ T‖²  ≤  #Rel + S.
```
So the open core is precisely: *the linear phase sum `Σ_T Jphase θ T` has squared L²-mass at most
`#Rel + S`*.  Equivalently (modulus form, `normSq_eq_norm_sq` / `Real.sqrt`):
```
   FirstMomentDiffCancellation θ Rel S   ⟺   ‖Σ_T Jphase θ T‖  ≤  Real.sqrt (#Rel + S).
```
This is one rung cleaner than even the difference-variety first moment: it is a bound on the NORM of
a SINGLE complex number `Σ_T Jphase θ T` (the aggregate linear phase), not a double sum over a
variety.  The √p is gone (each `Jphase` a unit), the pair structure is gone (Plancherel collapsed it
to one square), and what remains is the cancellation in a single character-sum-of-character-sums.

## Why this is the honest endpoint of the variance route

The chain is now fully explicit and exact:
```
   prize  ⟺  OffDiagonalPairCancellation               (_CreateWraparoundVariance)
          ⟺  (DiffTrace).re ≤ S  = FirstMomentDiffCancellation   (_NextDifferenceVariety, exact)
          ⟺  ‖Σ_T Jphase θ T‖² ≤ #Rel + S                (HERE, exact, via Plancherel)
```
Every rung is a kernel-checked equality/equivalence.  The remaining OPEN content is the single
inequality `‖Σ_T Jphase θ T‖² ≤ #Rel + S` at `r ≈ log p`, `S` sub-Poisson — a square-mean / L²
flatness statement for the aggregate iterated Jacobi phase over the relation set.  NOT proved here.

## What this file PROVES (axiom-clean, no `sorry`)

* `firstMomentDiffCancellation_iff_normSq_le` — the open core ⟺ `‖Σ Jphase‖² ≤ #Rel + S`;
* `firstMomentDiffCancellation_of_normSq_le` / `normSq_le_of_firstMomentDiffCancellation` — the two
  directions as standalone consumers;
* `firstMomentDiffCancellation_iff_norm_le_sqrt` — the modulus form
  `‖Σ Jphase‖ ≤ √(#Rel + S)` (for `0 ≤ #Rel + S`);
* `nonneg_budget_of_firstMomentDiffCancellation` / `not_firstMomentDiffCancellation_of_budget_negative`
  — the exact lower-budget guard: the open core is impossible unless `0 ≤ #Rel + S`, equivalently
  no bound with `S < -#Rel` can hold.

NO CORE / cancellation / completion / moment-saving / capacity claim: the inequality
`‖Σ Jphase‖² ≤ #Rel + S` is NOT proved.  This is an exact reframing (equivalence) of the named open
core onto the L² mass of the aggregate linear phase sum — a citable capstone of the variance route,
not a closure.  #444.
-/

namespace ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 The open core as a squared-L²-mass bound on the linear phase sum -/

/-- **`firstMomentDiffCancellation_iff_normSq_le`** — THE reframe.  The named open core
`FirstMomentDiffCancellation θ Rel S` (`(DiffTrace).re ≤ S`) holds iff the linear phase sum
`Σ_T Jphase θ T` has squared L²-mass at most `#Rel + S`:
```
   (DiffTrace θ Rel).re ≤ S   ⟺   ‖Σ_T Jphase θ T‖²  ≤  #Rel + S.
```
Exact, via the Plancherel value `DiffTrace.re = ‖Σ Jphase‖² − #Rel`. -/
theorem firstMomentDiffCancellation_iff_normSq_le (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ) :
    FirstMomentDiffCancellation θ Rel S
      ↔ Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) + S := by
  unfold FirstMomentDiffCancellation
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel]
  constructor <;> intro h <;> linarith

/-- **`firstMomentDiffCancellation_of_normSq_le`** — the producer direction: an L² mass bound on the
linear phase sum discharges the named open core. -/
theorem firstMomentDiffCancellation_of_normSq_le (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) + S) :
    FirstMomentDiffCancellation θ Rel S :=
  (firstMomentDiffCancellation_iff_normSq_le hmul hone hunit Rel S).mpr h

/-- **`normSq_le_of_firstMomentDiffCancellation`** — the consumer direction: the named open core
yields the L² mass bound on the linear phase sum. -/
theorem normSq_le_of_firstMomentDiffCancellation (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : FirstMomentDiffCancellation θ Rel S) :
    Complex.normSq (∑ T ∈ Rel, Jphase θ T) ≤ (Rel.card : ℝ) + S :=
  (firstMomentDiffCancellation_iff_normSq_le hmul hone hunit Rel S).mp h

/-! ## §2 The modulus form -/

/-- **`firstMomentDiffCancellation_iff_norm_le_sqrt`** — the modulus form of the reframe.  For
`0 ≤ #Rel + S`, the named open core holds iff the NORM of the aggregate linear phase sum is at most
`√(#Rel + S)`:
```
   (DiffTrace θ Rel).re ≤ S   ⟺   ‖Σ_T Jphase θ T‖  ≤  Real.sqrt (#Rel + S).
```
A bound on the modulus of a SINGLE complex number — the cleanest equivalent form of the variance-core
open core. -/
theorem firstMomentDiffCancellation_iff_norm_le_sqrt (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hS : 0 ≤ (Rel.card : ℝ) + S) :
    FirstMomentDiffCancellation θ Rel S
      ↔ ‖∑ T ∈ Rel, Jphase θ T‖ ≤ Real.sqrt ((Rel.card : ℝ) + S) := by
  rw [firstMomentDiffCancellation_iff_normSq_le hmul hone hunit Rel S,
      Complex.normSq_eq_norm_sq]
  rw [show ‖∑ T ∈ Rel, Jphase θ T‖ ^ 2 = ‖∑ T ∈ Rel, Jphase θ T‖ * ‖∑ T ∈ Rel, Jphase θ T‖ from sq _]
  constructor
  · intro h
    rw [← Real.sqrt_mul_self (norm_nonneg (∑ T ∈ Rel, Jphase θ T))]
    exact Real.sqrt_le_sqrt h
  · intro h
    have hn : 0 ≤ ‖∑ T ∈ Rel, Jphase θ T‖ := norm_nonneg _
    nlinarith [Real.mul_self_sqrt hS, Real.sqrt_nonneg ((Rel.card : ℝ) + S),
      mul_le_mul h h hn (Real.sqrt_nonneg ((Rel.card : ℝ) + S))]

/-! ## §3 The exact lower-budget guard -/

/-- **`nonneg_budget_of_firstMomentDiffCancellation`** — any successful variance-core budget must
satisfy `0 ≤ #Rel + S`.  This is the shifted-square floor in the reframe language: the right-hand
side of the equivalent L² mass bound cannot be negative. -/
theorem nonneg_budget_of_firstMomentDiffCancellation (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (h : FirstMomentDiffCancellation θ Rel S) :
    0 ≤ (Rel.card : ℝ) + S := by
  have hmass := normSq_le_of_firstMomentDiffCancellation hmul hone hunit Rel S h
  exact le_trans (Complex.normSq_nonneg (∑ T ∈ Rel, Jphase θ T)) hmass

/-- **`not_firstMomentDiffCancellation_of_budget_negative`** — exact lower-budget obstruction.  If
`#Rel + S < 0` (equivalently `S < -#Rel`), the named open core cannot hold.  This does not prove any
upper cancellation; it only pins the unavoidable floor for the shifted non-negative square. -/
theorem not_firstMomentDiffCancellation_of_budget_negative (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hneg : (Rel.card : ℝ) + S < 0) :
    ¬ FirstMomentDiffCancellation θ Rel S := by
  intro h
  have hnonneg := nonneg_budget_of_firstMomentDiffCancellation hmul hone hunit Rel S h
  linarith

/-- **`not_firstMomentDiffCancellation_of_lt_neg_card`** — the same obstruction stated in the
more human budget form: no first-moment cancellation bound can demand `S < -#Rel`. -/
theorem not_firstMomentDiffCancellation_of_lt_neg_card (hmul : ∀ a b, θ (a + b) = θ a * θ b)
    (hone : θ 0 = 1) (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) (S : ℝ)
    (hS : S < -(Rel.card : ℝ)) :
    ¬ FirstMomentDiffCancellation θ Rel S := by
  apply not_firstMomentDiffCancellation_of_budget_negative hmul hone hunit Rel S
  linarith

end ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.firstMomentDiffCancellation_iff_normSq_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.firstMomentDiffCancellation_of_normSq_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.normSq_le_of_firstMomentDiffCancellation
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.firstMomentDiffCancellation_iff_norm_le_sqrt
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.nonneg_budget_of_firstMomentDiffCancellation
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.not_firstMomentDiffCancellation_of_budget_negative
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceLinearSumReframe.not_firstMomentDiffCancellation_of_lt_neg_card
