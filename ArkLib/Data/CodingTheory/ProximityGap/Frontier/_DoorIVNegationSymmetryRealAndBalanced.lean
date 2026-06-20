/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) Lane 1/3: the negation symmetry `-1 ∈ μ_n` forces the worst-b sum REAL and the
# half-plane occupancy BALANCED — so the (dilation-NON-invariant) interval-occupancy feature is
# *also* b-blind, by a different mechanism than the dilation-invariance meta-theorem (#444)

## Context — closing a concrete worst-b selector

The campaign meta-theorem `_DoorIVPhaseSetDilationInvariant` proves that every fixed additive-linear
count of the phase set `S_b = {b·z : z ∈ μ_n}` is invariant under the nonzero dilation `b ↦ λ·b`,
hence **b-blind**: it cannot select the adversarial worst frequency. The natural escape is a feature
that genuinely BREAKS under dilation — the most basic being the position of the phase points relative
to a FIXED cut, i.e. the half-plane occupancy
`HP(b) = | #{z ∈ μ_n : (b·z mod p) ∈ [0, p/2)} − n/2 |`, equivalently the SIGN of the real parts of
`e_p(b·z)`. Dilation rotates the residues, so `HP` really does change with `b` — a legitimate
candidate selector outside the reach of the dilation-invariance meta-theorem.

## The probe verdict (`scripts/probes/probe_dooriv_worstb_halfplane_selector.py`)

PROPER thin 2-power `μ_n` (`n = 2^a`), prize regime `p ~ n^4 ≫ n^3`, n=16 FULL `𝔽_p^*` scan,
n=32,64 sampled; never `n = q−1`:

* `−1 ∈ μ_n` and `μ_n` is closed under `y ↦ −y` at every tested `n` (forced: `n` even ⟹ the
  unique order-`n` subgroup contains the order-2 element `−1`).
* consequently `max_b |Im η_b| ~ 1e-15` (float noise): **`η_b` is REAL for every `b`**.
* and `HP(b) = 0` for `99.98%` of all `b` (the `±1` cases are float-boundary): the half-plane
  occupancy is **exactly balanced** for every `b`, including the global argmax `b*`.
* hence `corr(HP, |η|) ≈ +0.05` and the argmax is *not* selected by `HP`.

## The mechanism (this file)

Both phenomena are one fact: `μ_n` is closed under negation, so the phase set
`{e_p(b·z) : z ∈ μ_n}` is closed under complex conjugation for every `b`. Pairing each point with its
conjugate:

* the imaginary parts cancel ⟹ the sum is real (`sum_isReal_of_conj_closed`);
* the upper-half-plane points pair bijectively with lower-half-plane points ⟹ occupancy is balanced
  (`upperHalf_card_eq_lowerHalf_card_of_conj_closed`).

So the dilation-NON-invariant interval-occupancy feature is **b-blind by the negation symmetry**, for a
reason orthogonal to the dilation-invariance meta-theorem. Any surviving door-(iv) worst-b selector
must therefore be invariant under neither dilation NOR conjugation — a strictly finer object than the
first-order real-part / half-plane sign data.

Scope: a finite multiset (`Finset`) of `ℂ` closed under `conj`. Definitional / pairing algebra. **No
CORE / cancellation / completion / moment / anti-concentration / capacity claim** — a refutation of a
concrete candidate selector with its mechanism, in the spirit of the campaign meta-theorem.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVNegationSymmetryRealAndBalanced

open Finset Complex

/-- A finite set of complex numbers is **conjugation-closed** if it is mapped to itself by complex
conjugation. This is the abstraction of "the phase set `{e_p(b·z) : z ∈ μ_n}` is closed under
`z ↦ z̄`", which holds because `μ_n` is closed under negation `y ↦ −y` (as `−1 ∈ μ_n`). -/
def ConjClosed (S : Finset ℂ) : Prop := ∀ z ∈ S, (starRingEnd ℂ) z ∈ S

/-- Conjugation is an involution on a conjugation-closed set, hence injective on it. -/
theorem conj_involutive : Function.Involutive (starRingEnd ℂ) := by
  intro z; simp

/-- **The worst-b sum is real.** If `S ⊆ ℂ` is conjugation-closed, then `∑ z ∈ S, z` is a real
number (it equals its own conjugate). Specialized to `S = {e_p(b·z) : z ∈ μ_n}` this is exactly the
probe fact `Im η_b = 0` for every frequency `b`. -/
theorem sum_isReal_of_conj_closed {S : Finset ℂ} (hS : ConjClosed S) :
    (starRingEnd ℂ) (∑ z ∈ S, z) = ∑ z ∈ S, z := by
  rw [map_sum]
  -- reindex the sum by `z ↦ z̄`, which is a bijection of `S` onto itself
  refine Finset.sum_nbij' (fun z => (starRingEnd ℂ) z) (fun z => (starRingEnd ℂ) z) ?_ ?_ ?_ ?_ ?_
  · intro z hz; exact hS z hz
  · intro z hz; exact hS z hz
  · intro z _; simp
  · intro z _; simp
  · intro z _; rfl

/-- The imaginary part of the worst-b sum is zero (the explicit `Im = 0` form of
`sum_isReal_of_conj_closed`). -/
theorem sum_im_eq_zero_of_conj_closed {S : Finset ℂ} (hS : ConjClosed S) :
    (∑ z ∈ S, z).im = 0 := by
  have h := sum_isReal_of_conj_closed hS
  have hc : ((starRingEnd ℂ) (∑ z ∈ S, z)).im = -(∑ z ∈ S, z).im := Complex.conj_im _
  have : (∑ z ∈ S, z).im = -(∑ z ∈ S, z).im := by
    rw [← hc, h]
  linarith

open scoped Classical in
/-- The "upper half" of a complex set: the points with strictly positive imaginary part. This is the
abstract version of "phase points landing in the open upper half-plane". -/
noncomputable def upperHalf (S : Finset ℂ) : Finset ℂ := S.filter (fun z => 0 < z.im)

open scoped Classical in
/-- The "lower half": strictly negative imaginary part. -/
noncomputable def lowerHalf (S : Finset ℂ) : Finset ℂ := S.filter (fun z => z.im < 0)

/-- **Balanced occupancy.** For a conjugation-closed set the open-upper-half and open-lower-half
points are in bijection (via `z ↦ z̄`), so the two half-plane occupancies are EQUAL. This is the
abstract form of the probe fact `HP(b) = 0`: the half-plane count is exactly balanced for every `b`,
hence carries no information selecting the worst frequency. -/
theorem upperHalf_card_eq_lowerHalf_card_of_conj_closed {S : Finset ℂ} (hS : ConjClosed S) :
    (upperHalf S).card = (lowerHalf S).card := by
  refine Finset.card_nbij' (fun z => (starRingEnd ℂ) z) (fun z => (starRingEnd ℂ) z) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_coe, upperHalf, lowerHalf, Finset.mem_filter] at hz ⊢
    have hc : ((starRingEnd ℂ) z).im = -z.im := Complex.conj_im z
    exact ⟨hS z hz.1, by rw [hc]; linarith [hz.2]⟩
  · intro z hz
    simp only [Finset.mem_coe, upperHalf, lowerHalf, Finset.mem_filter] at hz ⊢
    have hc : ((starRingEnd ℂ) z).im = -z.im := Complex.conj_im z
    exact ⟨hS z hz.1, by rw [hc]; linarith [hz.2]⟩
  · intro z _; simp
  · intro z _; simp

/-- **No half-plane selector.** The signed half-plane imbalance `card(upper) − card(lower)` is `0` for
every conjugation-closed set. Therefore the interval-occupancy feature `HP` is constant in `b`
(it is forced to `0` by the negation symmetry), and cannot select the adversarial worst frequency —
the dilation-NON-invariant escape from the dilation-invariance meta-theorem is itself b-blind. -/
theorem halfPlaneImbalance_eq_zero_of_conj_closed {S : Finset ℂ} (hS : ConjClosed S) :
    ((upperHalf S).card : ℤ) - (lowerHalf S).card = 0 := by
  rw [upperHalf_card_eq_lowerHalf_card_of_conj_closed hS]; ring

/-! ## Signed `b ↦ -b` symmetry of the worst-b sum (the increment over `_DoorIVWorstBCosetClosed`)

The in-tree fact (`_DoorIVWorstBCosetClosed`, DISPROOF_LOG `[door-iv-worstb-...]`) is that the
ABSOLUTE prize statistic `|η_b|` is invariant under `b ↦ -b`, because `η_{-b} = conj(η_b)` (negation-
closed `μ_n`) and `|conj w| = |w|`. Combined with `sum_isReal_of_conj_closed` above (`η_b` is REAL for
every `b`), the symmetry upgrades from the absolute value to the SIGNED value: a real number is its own
conjugate, so `η_{-b} = conj(η_b) = η_b` *exactly*. The two frequencies `b` and `-b` are therefore
interchangeable for the ENTIRE prize problem, not merely for `|η|`. -/

/-- **Signed `b ↦ -b` interchangeability.** If a frequency statistic `η : ι → ℂ` is REAL at `b`
(`conj (η b) = η b`, e.g. via `sum_isReal_of_conj_closed`) and the negation symmetry gives
`η (neg b) = conj (η b)` (the proven `η_{-b} = conj η_b`), then the SIGNED values coincide:
`η (neg b) = η b`. This strengthens the absolute-value `b↦-b` closure of the worst-b set
(`_DoorIVWorstBCosetClosed`) to a signed equality. -/
theorem signed_neg_symmetry {ι : Type*} (η : ι → ℂ) (b nb : ι)
    (hreal : (starRingEnd ℂ) (η b) = η b)
    (hneg : η nb = (starRingEnd ℂ) (η b)) :
    η nb = η b := by
  rw [hneg, hreal]

/-- The signed `b ↦ -b` symmetry, packaged for the conjugation-closed phase set: the real-ness comes
from `sum_isReal_of_conj_closed`, so the only remaining hypothesis is the proven negation relation
`η (neg b) = conj (η b)`. Consequently any frequency selector built on the SIGNED value (not just
`|η|`) is already `±b`-blind. -/
theorem signed_neg_symmetry_of_conjClosed {ι : Type*} (S : ι → Finset ℂ) (b nb : ι)
    (hS : ConjClosed (S b))
    (hneg : (∑ z ∈ S nb, z) = (starRingEnd ℂ) (∑ z ∈ S b, z)) :
    (∑ z ∈ S nb, z) = ∑ z ∈ S b, z := by
  rw [hneg, sum_isReal_of_conj_closed hS]

end ArkLib.ProximityGap.Frontier.DoorIVNegationSymmetryRealAndBalanced
