/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

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
  have hx' := mem_filter.1 hx
  have hxp := mem_product.1 hx'.1
  refine mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, hx'.2⟩
  · exact mem_piFinset.2 (fun i => hst (mem_piFinset.1 hxp.1 i))
  · exact mem_piFinset.2 (fun i => hst (mem_piFinset.1 hxp.2 i))

/-- **Diagonal lower bound:** the `r`-fold additive energy is at least `#s ^ r`, witnessed by the
"diagonal" pairs `(v, v)`. -/
lemma card_pow_le_addREnergy (r : ℕ) (s : Finset α) :
    #s ^ r ≤ addREnergy r s := by
  calc #s ^ r = #(piFinset fun _ : Fin r => s) := (card_piFinset_const s r).symm
    _ ≤ addREnergy r s := by
        unfold addREnergy
        apply card_le_card_of_injOn (fun v => (v, v))
        · intro v hv
          exact mem_filter.2 ⟨mem_product.2 ⟨hv, hv⟩, rfl⟩
        · intro a _ b _ hab
          simpa using congrArg Prod.fst hab

/-- Positivity for nonempty `s`. -/
lemma addREnergy_pos (hs : s.Nonempty) : 0 < addREnergy r s :=
  (pow_pos hs.card_pos r).trans_le (card_pow_le_addREnergy r s)

/-- The `0`-fold additive energy is `1`: the only `0`-tuple is the empty tuple and the (empty) sum
equation `0 = 0` always holds, so there is exactly one pair. -/
@[simp] lemma addREnergy_zero (s : Finset α) : addREnergy 0 s = 1 := by
  classical
  rw [addREnergy_def]
  rw [Finset.card_eq_one]
  refine ⟨(fun _ => 0, fun _ => 0), ?_⟩
  ext x
  simp only [mem_filter, mem_product, mem_piFinset, mem_singleton, Finset.univ_eq_empty,
    Finset.sum_empty]
  constructor
  · rintro _
    obtain ⟨⟨x1, x2⟩⟩ := x
    refine Prod.ext ?_ ?_ <;>
      exact funext fun i => absurd i.2 (by simp)
  · rintro rfl
    refine ⟨⟨fun i => absurd i.2 (by simp), fun i => absurd i.2 (by simp)⟩, rfl⟩

/-- The `1`-fold additive energy is `#s`: the sum equation `v 0 = w 0` forces `v = w`, so the
pairs are exactly the `#s` diagonal pairs `(v, v)`. -/
@[simp] lemma addREnergy_one (s : Finset α) : addREnergy 1 s = #s := by
  classical
  rw [addREnergy_def]
  rw [← card_piFinset_const s 1]
  apply card_bij (fun x _ => x.1)
  · intro x hx
    exact (mem_piFinset.1 (mem_product.1 (mem_filter.1 hx).1).1)
  · -- injectivity: the filter condition forces x.1 = x.2 (since Fin 1 sums are single terms)
    intro x hx y hy hxy
    have hx' := mem_filter.1 hx
    have hy' := mem_filter.1 hy
    have hxsum : x.1 0 = x.2 0 := by simpa [Fin.sum_univ_one] using hx'.2
    have hysum : y.1 0 = y.2 0 := by simpa [Fin.sum_univ_one] using hy'.2
    have h1 : x.1 = y.1 := hxy
    have h2 : x.2 = y.2 := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [← hxsum, ← hysum, h1]
    exact Prod.ext h1 h2
  · -- surjectivity: every v gives the diagonal pair (v, v)
    intro v hv
    refine ⟨(v, v), ?_, rfl⟩
    refine mem_filter.2 ⟨mem_product.2 ⟨hv, hv⟩, rfl⟩

open scoped Combinatorics.Additive in
/-- **Agreement with Mathlib's `Finset.addEnergy` at `r = 2`.** The `2`-fold additive energy is
exactly the classical quadruple additive energy `E[s] = #{(a₁,a₂,b₁,b₂) ∈ s⁴ : a₁ + b₁ = a₂ + b₂}`.
The bijection sends a pair of `2`-tuples `(![a₁, b₁], ![a₂, b₂])` (equal sum `a₁ + b₁ = a₂ + b₂`)
to the quadruple `((a₁, a₂), (b₁, b₂))`. -/
lemma addREnergy_two (s : Finset α) : addREnergy 2 s = E[s] := by
  classical
  rw [addREnergy_def, addEnergy]
  apply card_bij
    (fun x _ => ((x.1 0, x.2 0), (x.1 1, x.2 1)))
  · -- maps into Mathlib's filtered quadruple set
    intro x hx
    have hx' := mem_filter.1 hx
    have hxp := mem_product.1 hx'.1
    have hv := mem_piFinset.1 hxp.1
    have hw := mem_piFinset.1 hxp.2
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_product.2 ⟨hv 0, hw 0⟩, mem_product.2 ⟨hv 1, hw 1⟩⟩, ?_⟩
    -- the sum condition: a₁ + b₁ = a₂ + b₂ from ∑ v = ∑ w over Fin 2
    have := hx'.2
    simpa [Fin.sum_univ_two] using this
  · -- injectivity: the four coordinates determine both 2-tuples
    intro x _ y _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨⟨h10, h20⟩, h11, h21⟩ := hxy
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i
    · exact h10
    · exact h11
    · exact h20
    · exact h21
  · -- surjectivity
    intro q hq
    have hq' := mem_filter.1 hq
    have hqp := mem_product.1 hq'.1
    have h13 := mem_product.1 hqp.1
    have h24 := mem_product.1 hqp.2
    refine ⟨(![q.1.1, q.2.1], ![q.1.2, q.2.2]), ?_, ?_⟩
    · refine mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, ?_⟩
      · exact mem_piFinset.2 (fun i => by fin_cases i <;> simp [h13.1, h24.1])
      · exact mem_piFinset.2 (fun i => by fin_cases i <;> simp [h13.2, h24.2])
      · have := hq'.2
        simpa [Fin.sum_univ_two] using this
    · ext <;> simp

end Finset

namespace Finset

variable {α : Type*} [AddCommGroup α] [DecidableEq α] {r : ℕ} {s : Finset α}

/-- **Fiber bound (successor form).** The number of `(k+1)`-tuples drawn from `s` with a *fixed*
sum `d` is at most `#s ^ k`: the tuple is determined by its first `k` coordinates (`Fin.init`),
because the last coordinate is forced to be `d - (sum of the first k)`. (This is where the group
structure — subtraction — is used.) -/
lemma addREnergy_fiber_succ_le (k : ℕ) (s : Finset α) (d : α) :
    #{v ∈ (piFinset fun _ : Fin (k + 1) => s) | ∑ i, v i = d} ≤ #s ^ k := by
  classical
  rw [← card_piFinset_const s k]
  apply card_le_card_of_injOn (fun v => Fin.init v)
  · -- `Fin.init v` lands in the `Fin k → s` piFinset
    intro v hv
    have hv' := mem_filter.1 hv
    refine mem_piFinset.2 (fun j => ?_)
    exact mem_piFinset.1 hv'.1 (Fin.castSucc j)
  · -- injectivity on the fiber: equal inits + equal sum ⟹ equal last coordinate
    intro a ha b hb hab
    have ha' := (mem_filter.1 ha).2
    have hb' := (mem_filter.1 hb).2
    -- Split both sums via `Fin.sum_univ_castSucc`.
    rw [Fin.sum_univ_castSucc] at ha' hb'
    -- `Fin.init a = Fin.init b`, and `a i = (Fin.init a) i` for `i = castSucc _`.
    have hinit : ∀ j : Fin k, a (Fin.castSucc j) = b (Fin.castSucc j) := by
      intro j
      have := congrFun hab j
      simpa [Fin.init] using this
    have hsum_eq : ∑ j : Fin k, a (Fin.castSucc j) = ∑ j : Fin k, b (Fin.castSucc j) :=
      Finset.sum_congr rfl (fun j _ => hinit j)
    -- last coordinate forced equal: cancel the common partial sum from a' = d = b'.
    have hlast : a (Fin.last k) = b (Fin.last k) := by
      have : (∑ j : Fin k, a (Fin.castSucc j)) + a (Fin.last k)
           = (∑ j : Fin k, b (Fin.castSucc j)) + b (Fin.last k) := by rw [ha', hb']
      rw [hsum_eq] at this
      exact add_left_cancel this
    -- conclude a = b on all of Fin (k+1) via the `castSucc`/`last` case split.
    funext i
    refine Fin.lastCases ?_ ?_ i
    · exact hlast
    · intro j; exact hinit j

/-- **Trivial upper bound:** the `r`-fold additive energy is at most `#s ^ (2r - 1)` (for `r ≥ 1`).
Heuristically, the `r` coordinates of `w` and the first `r - 1` coordinates of `v` may be chosen
freely (that is `2r - 1` choices from `s`), and then the last coordinate of `v` is *forced* by the
sum equation `∑ v = ∑ w`. Proven by fibering over `w` and applying the fiber bound
`addREnergy_fiber_succ_le`. -/
lemma addREnergy_le (hr : 1 ≤ r) (s : Finset α) :
    addREnergy r s ≤ #s ^ (2 * r - 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [addREnergy_def]
  -- count fiberwise over the second factor `w`
  have hcard :
      #{x ∈ (piFinset fun _ : Fin (k + 1) => s) ×ˢ (piFinset fun _ : Fin (k + 1) => s) |
          ∑ i, x.1 i = ∑ i, x.2 i}
        = ∑ w ∈ (piFinset fun _ : Fin (k + 1) => s),
            #{v ∈ (piFinset fun _ : Fin (k + 1) => s) | ∑ i, v i = ∑ i, w i} := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.card_filter]
  rw [hcard]
  calc ∑ w ∈ (piFinset fun _ : Fin (k + 1) => s),
          #{v ∈ (piFinset fun _ : Fin (k + 1) => s) | ∑ i, v i = ∑ i, w i}
      ≤ ∑ _w ∈ (piFinset fun _ : Fin (k + 1) => s), #s ^ k := by
        exact Finset.sum_le_sum (fun w _ => addREnergy_fiber_succ_le k s (∑ i, w i))
    _ = #s ^ (k + 1) * #s ^ k := by
        rw [Finset.sum_const, card_piFinset_const, smul_eq_mul]
    _ = #s ^ (2 * (k + 1) - 1) := by
        rw [← pow_add]; congr 1; omega

end Finset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Finset.addREnergy_mono
#print axioms Finset.card_pow_le_addREnergy
#print axioms Finset.addREnergy_pos
#print axioms Finset.addREnergy_zero
#print axioms Finset.addREnergy_one
#print axioms Finset.addREnergy_two
#print axioms Finset.addREnergy_fiber_succ_le
#print axioms Finset.addREnergy_le
