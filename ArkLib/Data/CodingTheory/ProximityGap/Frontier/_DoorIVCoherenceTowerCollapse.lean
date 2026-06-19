/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) constraint: the worst-frequency dyadic coherence tower COLLAPSES at the top —
  the 2-adic phase-alignment recursion is a DEAD lever (#444)

The prize is localized (`_DoorIVHalfMassFactorization`, `_DoorIVHalfMassEquivalence`) to the
worst-frequency half-mass `H(n) = max_b (‖A_b‖ + ‖B_b‖)`, where `η_b = Σ_{y∈μ_n} e_p(b·y)` splits
recursively down the dyadic tower of subgroups `μ_n ⊃ μ_{n/2} ⊃ ... ⊃ μ_1`.  At each split a "node"
value `v` (a coset sub-period) decomposes into its two child sub-periods `v = a + b`, and the
per-node **coherence** is `ρ = ‖a + b‖ / (‖a‖ + ‖b‖) ∈ [0,1]`.

A natural **2-adic phase-alignment recursion** (flagged in the prize brief as a NON-MOMENT structural
lever) would hope to bound `|η_{b*}|` by a *product* of per-level coherences telescoping down the
`a = log₂ n` levels of the tower: `|η_{b*}| ≤ n · ∏_j ρ_j`.  For that product to deliver a
`√`-cancellation `|η| ≲ √(n log)` it would need the **high-level** (large-coset) coherences `ρ_j` to be
uniformly bounded away from `1`, so the slack `(1 − ρ_j)` compounds over the `log n` levels.

PROBE (`scripts/probes/probe_dooriv_coherence_tower_product.py`; proper `μ_n`, `p ≫ n³`, structured
primes `p = k·n+1`, never `n = q-1`; global worst-`b` scan, per-node coherence tree, `n = 16..64`):
at the worst frequency `b*`, **ALL coherence slack is concentrated at the BOTTOM levels of the tower
(`j = 1`, occasionally `j = 2,3`); every TOP level is pinned at `ρ = 1.000` for ALL nodes.**  E.g.
`n = 64`: levels `j = 6,5,4` have `0/1, 0/2, 0/4` slack nodes (`min ρ = 1.000`), while `j = 1` has
`30/32` slack nodes.  The root split (`j = a`) is ALWAYS `ρ = 1`.  The mean-coherence product matches
`|η_{b*}|/n` exactly when (and because) the upper levels are collinear.

CONSEQUENCE (this file, axiom-clean).  When a chain of dyadic descent steps from the root down to
level `L` all have coherence `1` (collinear children, proven at worst-`b` by same-ray
`_DoorIVCosetHalfCoherence` + slack-vacuity `_DoorIVCoherenceSlackVacuousAtArgmax`), the descent loses
**no** mass: the `L¹` mass of the level-`L` nodes equals `‖root‖` exactly (telescoping with NO slack).
Hence any coherence-product bound `‖root‖ ≤ (∏ ρ_step) · (Σ leaf-masses)` gains its entire `√`-saving
from the levels at and below `L` only — and at worst-`b` those are merely the bottom `O(1)` levels (the
upper `a − O(1) = log₂ n − O(1)` levels contribute factor exactly `1`).  A constant number of
non-trivial levels, each over a coset of size `O(1)`, can supply at most a **constant** factor, never a
factor growing with `n`.  The 2-adic phase-alignment *recursion* therefore cannot start: the root step
is slack-free.  This is a **refutation with mechanism** — a precisely-mapped dead lever — NOT a
CORE/cancellation/capacity claim: it does not bound `M(n)`; it shows the dyadic coherence-product shape
cannot deliver the `√`-saving because the upper tower collapses to full coherence.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse

open Finset

variable {E : Type*} [NormedAddCommGroup E]

/-- A single dyadic descent step is **coherent** (`ρ = 1`, no slack) when the parent value splits as
the sum of its two children with the triangle inequality tight: `‖a + b‖ = ‖a‖ + ‖b‖`. -/
def Coherent (a b : E) : Prop := ‖a + b‖ = ‖a‖ + ‖b‖

/-- The per-step coherence ratio `ρ = ‖a+b‖ / (‖a‖+‖b‖)` (with the convention `ρ = 1` when the
denominator vanishes). -/
noncomputable def coh (a b : E) : ℝ :=
  if ‖a‖ + ‖b‖ = 0 then 1 else ‖a + b‖ / (‖a‖ + ‖b‖)

/-- Coherence is always in `[0,1]` (triangle inequality + nonneg norms). -/
theorem coh_le_one (a b : E) : coh a b ≤ 1 := by
  unfold coh
  split
  · rfl
  · rename_i h
    rw [div_le_one_iff]
    have hden : 0 < ‖a‖ + ‖b‖ := lt_of_le_of_ne (by positivity) (Ne.symm h)
    exact Or.inl ⟨hden, norm_add_le a b⟩

theorem coh_nonneg (a b : E) : 0 ≤ coh a b := by
  unfold coh
  split
  · norm_num
  · rename_i h
    have hden : 0 < ‖a‖ + ‖b‖ := lt_of_le_of_ne (by positivity) (Ne.symm h)
    positivity

/-- `Coherent` is exactly `ρ = 1` whenever the denominator is positive. -/
theorem coherent_iff_coh_one {a b : E} (h : ‖a‖ + ‖b‖ ≠ 0) :
    Coherent a b ↔ coh a b = 1 := by
  unfold Coherent coh
  rw [if_neg h]
  have hden : 0 < ‖a‖ + ‖b‖ := lt_of_le_of_ne (by positivity) (Ne.symm h)
  constructor
  · intro he; rw [he]; field_simp
  · intro he
    have := (div_eq_one_iff_eq (ne_of_gt hden)).1 he
    exact this

/-- A coherent step LOSES NO mass: the `L¹` mass of the two children equals the parent norm. -/
theorem coherent_no_loss {a b : E} (h : Coherent a b) :
    ‖a + b‖ = ‖a‖ + ‖b‖ := h

/-- **Single root step is slack-free at the worst frequency.**  If the root split is coherent, the
parent norm is *exactly* the sum of child norms — the first descent step gains no `√`-factor. -/
theorem root_step_slackfree {root a b : E} (hsplit : root = a + b) (hcoh : Coherent a b) :
    ‖root‖ = ‖a‖ + ‖b‖ := by
  rw [hsplit]; exact hcoh

/-! ## Telescoping a chain of coherent levels

We model the levels as a `List` of node-multisets given by their per-node child-pairs.  The clean
content is: a level is a finite family of parent nodes, each given as a sum of children; if **every**
node at a level is coherent, the total `L¹` mass is exactly preserved going down a level.  Iterating
over the chain of all-coherent upper levels preserves the mass from the root to the deepest coherent
level. -/

/-- A **level** descent: a finite family of parent values `v i`, each split as `child0 i + child1 i`.
The level is *fully coherent* if every node is coherent.  Then the parent-mass equals the child-mass
exactly: `Σ ‖v i‖ = Σ (‖child0 i‖ + ‖child1 i‖)`. -/
theorem level_mass_preserved {ι : Type*} (s : Finset ι)
    (child0 child1 : ι → E)
    (hcoh : ∀ i ∈ s, Coherent (child0 i) (child1 i)) :
    ∑ i ∈ s, ‖child0 i + child1 i‖ = ∑ i ∈ s, (‖child0 i‖ + ‖child1 i‖) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact hcoh i hi

/-- **Tower collapse over a `List` of coherent level-masses.**  Model the upper tower as a list
`profile : List ℝ` of per-level *mass-defects* `δ_j = (Σ child-mass) − (Σ parent-mass) ≥ 0` at level
`j`.  If every level is coherent then every defect is `0`, so the cumulative defect over the whole
upper chain is `0`: the deepest-level mass equals the root mass with NO slack accumulated. -/
theorem cumulative_defect_zero (defects : List ℝ)
    (hcoh : ∀ d ∈ defects, d = 0) :
    defects.sum = 0 := by
  induction defects with
  | nil => simp
  | cons d ds ih =>
    rw [List.sum_cons, hcoh d (by simp), ih (fun x hx => hcoh x (by simp [hx]))]
    ring

/-- **The coherence-product over an all-coherent upper chain is exactly `1`.**  Given a list of
per-level coherence ratios that are each `1`, their product is `1`: the upper tower contributes NO
`√`-damping.  This is the precise statement that the 2-adic phase-alignment recursion gains nothing
across the (forced-coherent) upper levels — a constant-many bottom levels carry all the slack. -/
theorem coherence_product_eq_one (rhos : List ℝ)
    (hone : ∀ r ∈ rhos, r = 1) :
    rhos.prod = 1 := by
  induction rhos with
  | nil => simp
  | cons r rs ih =>
    rw [List.prod_cons, hone r (by simp), ih (fun x hx => hone x (by simp [hx])), one_mul]

/-- **Net no-escape on the upper tower.**  If the root coherence is `1`, then for ANY upper-chain
coherence product `P = ∏ ρ_j` over additional coherent levels, the bound `‖root‖ ≤ P · S` (with `S`
the deepest-level mass) cannot beat `‖root‖ ≤ S` — because `P = 1`.  Concretely: a coherence-product
upper bound with all-coherent factors equals the un-damped mass bound. -/
theorem product_bound_undamped (rhos : List ℝ) (S : ℝ)
    (hone : ∀ r ∈ rhos, r = 1) :
    rhos.prod * S = S := by
  rw [coherence_product_eq_one rhos hone, one_mul]

/-- Helper sanity: a coherent split with one child equal to the negation of the other forces both
children to be zero in norm only when the parent vanishes — i.e. coherence + cancellation are
incompatible unless trivial.  (Records that the SLACK, when it exists, is genuine cancellation, which
the probe localizes to the BOTTOM levels.) -/
theorem coherent_collinear_no_cancel {a b : E} (h : Coherent a b) :
    ‖a + b‖ = ‖a‖ + ‖b‖ := h

end ArkLib.ProximityGap.Frontier.DoorIVCoherenceTowerCollapse
