/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTracePlancherelFloorAttained
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DiffTraceTrivialEnvelopeAttained

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# CAPSTONE — the variance-core trace is an exact affine image of aggregate phase coherence (#444)

**Variance-core envelope capstone.**  The chain
`_DiffTracePlancherelFloor` / `_DiffTracePlancherelFloorAttained` (floor `−#Rel`, attained ⟺ perfect
cancellation) and `_DiffTraceTrivialEnvelope` / `_DiffTraceTrivialEnvelopeAttained` (ceiling
`#Rel²−#Rel`, attained ⟺ perfect coherence) places the off-diagonal first moment in
`[−#Rel, #Rel²−#Rel]` with BOTH endpoints characterized.  This file packages the whole enclosure into
ONE citable statement and adds the structural payoff: the trace is an **order-preserving** (strictly
monotone) affine image of the aggregate coherence `‖Σ Jphase‖`.

## The exact enclosure (one statement)

```
   −#Rel ≤ (DiffTrace θ Rel).re ≤ #Rel² − #Rel,
   with  lower  attained ⟺ Σ_T Jphase θ T = 0          (perfect cancellation),
         upper  attained ⟺ ‖Σ_T Jphase θ T‖ = #Rel      (perfect coherence).
```

## The structural payoff — the trace RANKS configs by coherence

Since `(DiffTrace).re = ‖Σ Jphase‖² − #Rel` and `x ↦ x²` is strictly monotone on `[0,∞)`, at EQUAL
piece count (`#Rel₁ = #Rel₂`) the additive `−#Rel` offsets cancel:
```
   (DiffTrace θ Rel₁).re ≤ (DiffTrace θ Rel₂).re   ⟺   ‖Σ_{Rel₁} Jphase‖ ≤ ‖Σ_{Rel₂} Jphase‖.
```
(The equal-cardinality hypothesis is essential — across different piece counts the `−#Rel` offsets
differ, so the trace is NOT a bare order isomorphism of the norm.)  So at fixed piece count the
variance-core trace is an exact strictly-increasing re-encoding of aggregate phase coherence: a
higher off-diagonal first moment is EQUIVALENT to a more constructive aggregate phase sum.  This is
the door-(iv) statement that at fixed piece count the *only* lever on the trace is the coherence of `Σ Jphase` — any
prize-relevant upper saving on the trace is exactly a coherence (anti-concentration) saving on the
aggregate sum, with no other free parameter.

## What this file PROVES (axiom-clean, no `sorry`)

* `diffTrace_re_mem_envelope` — `−#Rel ≤ (DiffTrace).re ≤ #Rel²−#Rel` (both ends, one statement);
* `diffTrace_re_envelope_endpoints` — the packaged enclosure + both attainment iffs as one record;
* `diffTrace_re_le_iff_norm_le` — at `#Rel₁=#Rel₂`, the monotone bridge: trace order ⟺ coherence order;
* `diffTrace_re_lt_iff_norm_lt` — strict form (also at `#Rel₁=#Rel₂`).

NO CORE / cancellation / completion / moment-saving / capacity / sub-Poisson-upper claim: only the
closed envelope and the fixed-piece-count order-isomorphism to aggregate coherence.  The open prize content stays exactly
the upper coherence saving on `‖Σ Jphase‖`.  #444.
-/

namespace ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone

open Finset ComplexConjugate
open ArkLib.ProximityGap.Frontier.NextDifferenceVariety
open ArkLib.ProximityGap.Frontier.DiffTraceDiagonalExtraction
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloor
open ArkLib.ProximityGap.Frontier.DiffTracePlancherelFloorAttained
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelope
open ArkLib.ProximityGap.Frontier.DiffTraceTrivialEnvelopeAttained

variable {R : Type*} [AddCommGroup R] {r : ℕ} {θ : R → ℂ} [DecidableEq (Fin r → R)]

/-! ## §1 The exact enclosure, packaged -/

/-- **`diffTrace_re_mem_envelope`** — both ends of the variance-core trace enclosure in one
statement: `−#Rel ≤ (DiffTrace θ Rel).re ≤ #Rel² − #Rel`. -/
theorem diffTrace_re_mem_envelope (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    -(Rel.card : ℝ) ≤ (DiffTrace θ Rel).re
      ∧ (DiffTrace θ Rel).re ≤ (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ) :=
  ⟨diffTrace_re_ge_neg_card hmul hone hunit Rel,
    diffTrace_re_le_card_sq_sub_card hmul hone hunit Rel⟩

/-- **`diffTrace_re_envelope_endpoints`** — the full enclosure with BOTH attainment characterizations
as one record: the trace lies in `[−#Rel, #Rel²−#Rel]`; the lower end is attained iff the aggregate
phase sum perfectly cancels; the upper end iff it is maximally coherent. -/
theorem diffTrace_re_envelope_endpoints (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel : Finset (Fin r → R)) :
    (-(Rel.card : ℝ) ≤ (DiffTrace θ Rel).re
        ∧ (DiffTrace θ Rel).re ≤ (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ))
      ∧ ((DiffTrace θ Rel).re = -(Rel.card : ℝ) ↔ (∑ T ∈ Rel, Jphase θ T) = 0)
      ∧ ((DiffTrace θ Rel).re = (Rel.card : ℝ) ^ 2 - (Rel.card : ℝ)
            ↔ ‖∑ T ∈ Rel, Jphase θ T‖ = (Rel.card : ℝ)) :=
  ⟨diffTrace_re_mem_envelope hmul hone hunit Rel,
    diffTrace_re_eq_neg_card_iff_sum_eq_zero hmul hone hunit Rel,
    diffTrace_re_eq_ceiling_iff_norm_eq_card hmul hone hunit Rel⟩

/-! ## §2 The trace is a strictly monotone affine image of aggregate coherence -/

/-- **`diffTrace_re_le_iff_norm_le`** — at EQUAL piece count (`#Rel₁ = #Rel₂`) the variance-core trace
RANKS configurations exactly by aggregate phase coherence: the trace order is equivalent to the order
of the aggregate-sum norms.  Since `(DiffTrace).re = ‖Σ Jphase‖² − #Rel` and the two `#Rel` agree, the
comparison reduces to the strict monotonicity of `x ↦ x²` on `[0,∞)`.  (The equal-cardinality
hypothesis is essential: across different piece counts the additive `−#Rel` offsets differ, so the
trace is NOT an order isomorphism of the bare norm.) -/
theorem diffTrace_re_le_iff_norm_le (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel₁ Rel₂ : Finset (Fin r → R))
    (hcard : Rel₁.card = Rel₂.card) :
    (DiffTrace θ Rel₁).re ≤ (DiffTrace θ Rel₂).re
      ↔ ‖∑ T ∈ Rel₁, Jphase θ T‖ ≤ ‖∑ T ∈ Rel₂, Jphase θ T‖ := by
  rw [diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel₁,
      diffTrace_re_eq_normSq_sub_card hmul hone hunit Rel₂,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hcard]
  have h1 : 0 ≤ ‖∑ T ∈ Rel₁, Jphase θ T‖ := norm_nonneg _
  have h2 : 0 ≤ ‖∑ T ∈ Rel₂, Jphase θ T‖ := norm_nonneg _
  set a := ‖∑ T ∈ Rel₁, Jphase θ T‖ with ha
  set b := ‖∑ T ∈ Rel₂, Jphase θ T‖ with hb
  constructor
  · intro h
    -- a^2 ≤ b^2 with a,b ≥ 0 forces a ≤ b: otherwise b < a gives b^2 < a^2.
    by_contra hlt
    push_neg at hlt
    have : b ^ 2 < a ^ 2 := by nlinarith
    linarith
  · intro h
    have : a ^ 2 ≤ b ^ 2 := by nlinarith
    linarith

/-- **`diffTrace_re_lt_iff_norm_lt`** — strict form of the monotone bridge: strictly larger trace ⟺
strictly more coherent aggregate phase sum. -/
theorem diffTrace_re_lt_iff_norm_lt (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel₁ Rel₂ : Finset (Fin r → R))
    (hcard : Rel₁.card = Rel₂.card) :
    (DiffTrace θ Rel₁).re < (DiffTrace θ Rel₂).re
      ↔ ‖∑ T ∈ Rel₁, Jphase θ T‖ < ‖∑ T ∈ Rel₂, Jphase θ T‖ := by
  have hle := diffTrace_re_le_iff_norm_le hmul hone hunit Rel₂ Rel₁ hcard.symm
  rw [lt_iff_not_ge, lt_iff_not_ge, hle]


/-- **`diffTrace_re_eq_iff_norm_eq`** — equality form of the fixed-piece-count bridge: at EQUAL
piece count, two variance-core traces are equal exactly when their aggregate phase-sum norms are equal.
This is the no-slack equality companion to the `≤` and `<` order-isomorphism lemmas. -/
theorem diffTrace_re_eq_iff_norm_eq (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel₁ Rel₂ : Finset (Fin r → R))
    (hcard : Rel₁.card = Rel₂.card) :
    (DiffTrace θ Rel₁).re = (DiffTrace θ Rel₂).re
      ↔ ‖∑ T ∈ Rel₁, Jphase θ T‖ = ‖∑ T ∈ Rel₂, Jphase θ T‖ := by
  constructor
  · intro h
    have h12 : (DiffTrace θ Rel₁).re ≤ (DiffTrace θ Rel₂).re := le_of_eq h
    have h21 : (DiffTrace θ Rel₂).re ≤ (DiffTrace θ Rel₁).re := ge_of_eq h
    have hn12 := (diffTrace_re_le_iff_norm_le hmul hone hunit Rel₁ Rel₂ hcard).1 h12
    have hn21 := (diffTrace_re_le_iff_norm_le hmul hone hunit Rel₂ Rel₁ hcard.symm).1 h21
    exact le_antisymm hn12 hn21
  · intro h
    have h12 : (DiffTrace θ Rel₁).re ≤ (DiffTrace θ Rel₂).re :=
      (diffTrace_re_le_iff_norm_le hmul hone hunit Rel₁ Rel₂ hcard).2 (le_of_eq h)
    have h21 : (DiffTrace θ Rel₂).re ≤ (DiffTrace θ Rel₁).re :=
      (diffTrace_re_le_iff_norm_le hmul hone hunit Rel₂ Rel₁ hcard.symm).2 (ge_of_eq h)
    exact le_antisymm h12 h21

/-- **`diffTrace_re_ne_iff_norm_ne`** — inequivalence form: at EQUAL piece count, changing the
variance-core trace is exactly changing the aggregate coherence norm. -/
theorem diffTrace_re_ne_iff_norm_ne (hmul : ∀ a b, θ (a + b) = θ a * θ b) (hone : θ 0 = 1)
    (hunit : ∀ s, Complex.normSq (θ s) = 1) (Rel₁ Rel₂ : Finset (Fin r → R))
    (hcard : Rel₁.card = Rel₂.card) :
    (DiffTrace θ Rel₁).re ≠ (DiffTrace θ Rel₂).re
      ↔ ‖∑ T ∈ Rel₁, Jphase θ T‖ ≠ ‖∑ T ∈ Rel₂, Jphase θ T‖ := by
  rw [not_iff_not]
  exact diffTrace_re_eq_iff_norm_eq hmul hone hunit Rel₁ Rel₂ hcard

end ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_mem_envelope
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_envelope_endpoints
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_le_iff_norm_le
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_lt_iff_norm_lt
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_eq_iff_norm_eq
#print axioms ArkLib.ProximityGap.Frontier.DiffTraceEnvelopeCapstone.diffTrace_re_ne_iff_norm_ne
