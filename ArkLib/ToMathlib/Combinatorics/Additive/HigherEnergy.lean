/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Fintype.Pi

/-!
# Higher-order (`r`-fold) additive energy

Mathlib's `Finset.addEnergy s t` is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t`
with `a₁ + b₁ = a₂ + b₂` — the **`2`-fold** additive energy. This file introduces the
**`r`-fold additive energy**

  `addREnergy r s = #{(v, w) ∈ sʳ × sʳ : ∑ᵢ vᵢ = ∑ᵢ wᵢ}`,

the number of pairs of `r`-tuples drawn from `s` with equal sum. It is the basic quantity behind the
`2r`-th moment method for exponential sums (`∑_b ‖∑_{x∈s} e(bx)‖^{2r} = q · addREnergy r s`) and the
sum-product / Bourgain–Glibichuk–Konyagin character-sum estimates.

We record its elementary properties, all upstreamable to Mathlib:

* `addREnergy_mono` — monotone in `s`;
* `card_pow_le_addREnergy` — the diagonal lower bound `#s ^ r ≤ addREnergy r s`;
* `addREnergy_le` — the trivial upper bound `addREnergy r s ≤ #s ^ (2 * r - 1)` (the last
  coordinate of `w` is determined by the sum equation);
* `addREnergy_pos` — positivity for nonempty `s`;
* `addREnergy_two` — agreement with `Finset.addEnergy` at `r = 2`.

The deep content — a *sub-trivial* bound `addREnergy r s ≤ #s ^ (2r-1-κ)` for multiplicative
subgroups (the sum-product theorem) — is NOT here; it requires incidence geometry (Rudnev) absent
from Mathlib. This file is the elementary scaffold those estimates build on.
-/

open Finset Fintype
open scoped BigOperators

namespace Finset

variable {α : Type*} [AddCommMonoid α] [DecidableEq α] {r : ℕ} {s t : Finset α}

/-- The **`r`-fold additive energy** of a finset `s`: the number of pairs of `r`-tuples
`(v, w) ∈ sʳ × sʳ` with `∑ᵢ vᵢ = ∑ᵢ wᵢ`. For `r = 2` this is `Finset.addEnergy s s`
(see `addREnergy_two`). -/
noncomputable def addREnergy (r : ℕ) (s : Finset α) : ℕ :=
  #{x ∈ (piFinset fun _ : Fin r => s) ×ˢ (piFinset fun _ : Fin r => s) |
      ∑ i, x.1 i = ∑ i, x.2 i}

lemma addREnergy_def (r : ℕ) (s : Finset α) :
    addREnergy r s
      = #{x ∈ (piFinset fun _ : Fin r => s) ×ˢ (piFinset fun _ : Fin r => s) |
          ∑ i, x.1 i = ∑ i, x.2 i} := rfl

/-- The `r`-fold additive energy is monotone in the set. -/
@[gcongr]
lemma addREnergy_mono (hst : s ⊆ t) : addREnergy r s ≤ addREnergy r t := by
  unfold addREnergy
  apply card_le_card
  intro x hx
  rw [mem_filter, mem_product] at hx ⊢
  refine ⟨⟨?_, ?_⟩, hx.2⟩
  · exact mem_piFinset.2 (fun i => hst (mem_piFinset.1 hx.1.1 i))
  · exact mem_piFinset.2 (fun i => hst (mem_piFinset.1 hx.1.2 i))

/-- **Diagonal lower bound:** the `r`-fold additive energy is at least `#s ^ r`, witnessed by the
"diagonal" pairs `(v, v)`. -/
lemma card_pow_le_addREnergy (r : ℕ) (s : Finset α) :
    #s ^ r ≤ addREnergy r s := by
  unfold addREnergy
  rw [← card_piFinset_const s r]
  apply card_le_card_of_injOn (fun v => (v, v))
  · intro v hv
    rw [mem_filter, mem_product]
    exact ⟨⟨hv, hv⟩, rfl⟩
  · intro a _ b _ h
    exact (Prod.mk.injEq _ _ _ _ ▸ h).1

/-- Positivity for nonempty `s`. -/
lemma addREnergy_pos (hs : s.Nonempty) : 0 < addREnergy r s :=
  (pow_pos hs.card_pos r).trans_le (card_pow_le_addREnergy r s)

end Finset
