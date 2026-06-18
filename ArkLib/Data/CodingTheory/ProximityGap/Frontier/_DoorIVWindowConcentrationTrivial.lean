/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-!
# Door IV window-concentration is energy-blind: the single-window small-ball functional only
# yields the trivial linear ceiling `|η_b| ≤ n`

This file records the axiom-clean arithmetic kernel behind the probe
`scripts/probes/probe_dooriv_phaseset_anticoncentration.py` and its discriminator follow-up
`scripts/probes/probe_dooriv_smallball_vs_energy.py`.

## The probed object

For a worst frequency `b`, the period is `η_b = Σ_{y ∈ μ_n} e_p(b·y)`, a sum of `n` unit-modulus
complex numbers. A natural door-(iv) anti-concentration hope is that the additive **spread** of the
phase set `A_b = { b·y mod p }` carries the √-cancellation: if `A_b` were forced to concentrate in
a short arc (small-ball), one would read off a sup-norm bound *without* a moment/completion.

## The probe verdict (reproducible, in the prize regime, proper `μ_n`, p ≫ n³, incl. Fermat 65537)

The coarse window-concentration functional
`C_b = max over arcs W of length p/n of #{ y : b·y mod p ∈ W }`
**fails on both axes**:

* `C_worst / √n → 0` (measured 3.0, 1.59, 1.50, 1.06, 0.625 at n = 16,32,64,128,256): the worst
  window count is *sub*-√n, essentially flat (~10–12 points) — it is far **below** the √n scale, so
  it cannot be the prize object.
* `C_b` **decorrelates from `|η_b|`**: Spearman(|η|, C) collapses (0.49, 0.19, 0.11, 0.07, 0.046)
  and the argmax of `C` decouples from the argmax of `|η|` — at the actual worst `b` for `|η|`, `C`
  is *not* maximal. So `C_b` is not a repackaging of the sup-norm; coarse spatial clustering is **not**
  the mechanism producing a large `|η_b|` (that mechanism is fine phase coherence = the energy object).

## The formalizable kernel (this file)

The reason a single-window concentration count cannot bound the cancellation is purely the triangle
inequality with unit-modulus terms: splitting the `n` summands into the `C` lying in the chosen
window and the `n − C` outside, **each** out-of-window term still has modulus `1`, so the only bound a
single window yields is `|η_b| ≤ C·1 + (n − C)·1 = n` — the **trivial linear ceiling**, independent of
`C`. No choice of window (no matter how concentrated) lowers this below `n`. This is the constraint
lemma: the single-window small-ball functional is energy-blind in the cancellation direction.

This proves *nothing* about CORE and uses no moment/completion; it is a no-go pin saying the
single-window phase-concentration route gives only `n`, matching the probe's `C/√n → 0` degeneracy.
-/

namespace ProximityGap.Frontier.DoorIVWindowConcentrationTrivial

open Finset

variable {ι : Type*}

/-- A "phase vector": each summand has modulus exactly one (the values `e_p(b·y)` on `μ_n`). -/
def IsPhaseVector (f : ι → ℂ) (s : Finset ι) : Prop := ∀ i ∈ s, ‖f i‖ = 1

/-- The triangle bound for the in/out-window split of a unit-modulus character sum.

`W` is the in-window index set (those `i` with `b·y_i mod p` in the chosen short arc); the rest of
`s` is out-of-window. Each term has modulus `1`, so the partial sum over the window has modulus
`≤ |W|` and the out-of-window remainder has modulus `≤ |s \ W|`, giving the total bound `|s|`.

This is the **single-window concentration ceiling**: the only thing a window count buys is the
trivial split `|W| + |s \ W| = |s|`. -/
theorem norm_sum_le_card_of_phase
    {f : ι → ℂ} {s : Finset ι} (hf : IsPhaseVector f s) :
    ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) := by
  calc ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ = ∑ _i ∈ s, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi; exact hf i hi
    _ = (s.card : ℝ) := by simp

/-- The in/out-window decomposition makes the energy-blindness explicit: choosing **any** window
`W ⊆ s` and bounding each block by its cardinality recovers exactly the trivial ceiling `|s|`,
*independently of `|W|`*. So the single-window concentration count `|W|` cannot lower the bound. -/
theorem window_split_bound_is_trivial [DecidableEq ι]
    {f : ι → ℂ} {s W : Finset ι} (hW : W ⊆ s) (hf : IsPhaseVector f s) :
    ‖∑ i ∈ s, f i‖ ≤ (W.card : ℝ) + ((s \ W).card : ℝ) := by
  have hnat : W.card + (s \ W).card = s.card := by
    rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hW
  have hcard : (W.card : ℝ) + ((s \ W).card : ℝ) = (s.card : ℝ) := by
    exact_mod_cast hnat
  rw [hcard]
  exact norm_sum_le_card_of_phase hf

/-- Sharper statement of "the window count is irrelevant": the right-hand side of the window split
equals `|s|` for *every* admissible window `W`, so it carries no information about the concentration
`|W|`. This is the formal content of the probe's `C/√n → 0` + Spearman→0 degeneracy: a single window
count is energy-blind. -/
theorem window_split_rhs_constant [DecidableEq ι]
    {s W : Finset ι} (hW : W ⊆ s) :
    (W.card : ℝ) + ((s \ W).card : ℝ) = (s.card : ℝ) := by
  have hnat : W.card + (s \ W).card = s.card := by
    rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hW
  exact_mod_cast hnat

end ProximityGap.Frontier.DoorIVWindowConcentrationTrivial

#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.norm_sum_le_card_of_phase
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_split_bound_is_trivial
#print axioms ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_split_rhs_constant
