/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Basic

/-!
# `B_h`-Sidon sets: the general-`h` predicate and its structural closure (#444, §0)

The §0 lane of the proximity prize needs the **`B_h`-Sidon ladder**: `μ_n` is a
`B_∞`-Sidon set to some depth `ℓ` (the depth where the `h`-fold representation
function first becomes non-trivial). The *plain* Sidon set is the `h = 2` case.

This file introduces the general-`h` predicate `IsBhSidon h S` — every `h`-fold
multiset sum drawn from `S` determines the multiset — and proves its **easy,
char-free structural closure**:

* `IsBhSidon.subset`     — hereditary (a subset of a `B_h`-Sidon set is `B_h`-Sidon)
* `IsBhSidon.translate`  — translation invariance `x + S`
* base cases `isBhSidon_empty`, `isBhSidon_singleton`

These are reusable bricks for the `B_h`-Sidon ladder. They generalise the
`h = 2` (plain Sidon) closure to arbitrary `h`.

**Honesty / scope.** These are *easy* universal structural closures: they hold in
ANY additive commutative group, thin or thick, in any characteristic. They are
NOT the thinness-essential CORE bound; per the prize honesty contract they cannot
be and do not claim to be. The CORE wall (`M(μ_n) ≤ C√(n log(p/n))`) is the
*sup-norm bootstrap* from depth-`ℓ` Sidon, which is OPEN and untouched here.
-/

namespace ArkLib.ProximityGap.BhSidon

variable {G : Type*} [AddCommGroup G]

/-- A set `S` is **`B_h`-Sidon** when every `h`-fold sum drawn from `S`
determines the underlying size-`h` multiset: if two multisets `s, t`, each of
cardinality `h` with all elements in `S`, have the same sum, then `s = t`.

For `h = 2` this is the plain Sidon condition (`a + b = c + d ⇒ {a,b} = {c,d}`).
The multiset formulation is the clean general-`h` statement used for the §0 ladder. -/
def IsBhSidon (h : ℕ) (S : Set G) : Prop :=
  ∀ s t : Multiset G,
    Multiset.card s = h → Multiset.card t = h →
    (∀ x ∈ s, x ∈ S) → (∀ x ∈ t, x ∈ S) →
    s.sum = t.sum → s = t

/-- **Hereditary.** A subset of a `B_h`-Sidon set is `B_h`-Sidon. -/
theorem IsBhSidon.subset {h : ℕ} {S T : Set G} (hT : T ⊆ S)
    (hS : IsBhSidon h S) : IsBhSidon h T := by
  intro s t hs ht hsT htT hsum
  exact hS s t hs ht (fun x hx => hT (hsT x hx)) (fun x hx => hT (htT x hx)) hsum

/-- **Empty set** is `B_h`-Sidon for every `h`. -/
theorem isBhSidon_empty {h : ℕ} : IsBhSidon h (∅ : Set G) := by
  intro s t hs _ht hsE _htE _hsum
  -- if `h = 0` both `s` and `t` are the empty multiset; otherwise `s` would have
  -- an element, contradicting `∀ x ∈ s, x ∈ ∅`.
  rcases Multiset.empty_or_exists_mem s with hse | ⟨x, hx⟩
  · -- s = 0, so card s = 0 = h, hence card t = 0 too, so t = 0 = s
    subst hse
    have h0 : h = 0 := by simpa using hs.symm
    subst h0
    have : Multiset.card t = 0 := _ht
    exact (Multiset.card_eq_zero.mp this).symm
  · exact absurd (hsE x hx) (Set.notMem_empty x)

/-- **Singleton** is `B_h`-Sidon for every `h`: the only size-`h` multiset with all
elements equal to `a` is `h • {a}`, so any two such are equal. -/
theorem isBhSidon_singleton {h : ℕ} (a : G) : IsBhSidon h ({a} : Set G) := by
  intro s t hs ht hsS htS _hsum
  -- every element of `s` (resp `t`) equals `a`
  have hsa : ∀ x ∈ s, x = a := fun x hx => Set.mem_singleton_iff.mp (hsS x hx)
  have hta : ∀ x ∈ t, x = a := fun x hx => Set.mem_singleton_iff.mp (htS x hx)
  -- hence `s = replicate (card s) a` and likewise `t`
  have hs_rep : s = Multiset.replicate (Multiset.card s) a :=
    Multiset.eq_replicate_card.mpr hsa
  have ht_rep : t = Multiset.replicate (Multiset.card t) a :=
    Multiset.eq_replicate_card.mpr hta
  rw [hs_rep, ht_rep, hs, ht]

/-- **Translation invariance.** If `S` is `B_h`-Sidon then so is `x +ᵥ S = {x + a : a ∈ S}`.

Translating every element by `x` shifts every `h`-fold sum by the fixed amount
`h • x`, so sum-coincidences are preserved; the multiset map `(· + x)` is a
bijection, so multiset equality of the shifted witnesses transfers back. -/
theorem IsBhSidon.translate {h : ℕ} {S : Set G} (hS : IsBhSidon h S) (x : G) :
    IsBhSidon h ((fun a => x + a) '' S) := by
  intro s t hs ht hsS htS hsum
  -- pull back: `s = (· + x) '' s₀` with `s₀ ⊆ S`, via subtracting `x` elementwise
  set s₀ : Multiset G := s.map (fun y => y - x) with hs₀
  set t₀ : Multiset G := t.map (fun y => y - x) with ht₀
  have hcard_s₀ : Multiset.card s₀ = h := by rw [hs₀, Multiset.card_map]; exact hs
  have hcard_t₀ : Multiset.card t₀ = h := by rw [ht₀, Multiset.card_map]; exact ht
  -- membership in `S` after un-translating
  have hmem_s₀ : ∀ y ∈ s₀, y ∈ S := by
    intro y hy
    rw [hs₀, Multiset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := hsS z hz
    simpa using ha
  have hmem_t₀ : ∀ y ∈ t₀, y ∈ S := by
    intro y hy
    rw [ht₀, Multiset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := htS z hz
    simpa using ha
  -- sums: `sum s₀ = sum s - h • x`, likewise for `t₀`; equal sums transfer
  have hsum₀ : s₀.sum = t₀.sum := by
    have es : s₀.sum = s.sum - Multiset.card s • x := by
      rw [hs₀, Multiset.sum_map_sub, Multiset.map_id', Multiset.map_const',
        Multiset.sum_replicate]
    have et : t₀.sum = t.sum - Multiset.card t • x := by
      rw [ht₀, Multiset.sum_map_sub, Multiset.map_id', Multiset.map_const',
        Multiset.sum_replicate]
    rw [es, et, hs, ht, hsum]
  -- apply Sidon-ness to the pulled-back witnesses
  have h₀ : s₀ = t₀ := hS s₀ t₀ hcard_s₀ hcard_t₀ hmem_s₀ hmem_t₀ hsum₀
  -- push forward: applying `(x + ·)` to `s₀ = t₀` recovers `s = t`
  have hpush : s₀.map (fun y => x + y) = t₀.map (fun y => x + y) := by rw [h₀]
  rw [hs₀, ht₀] at hpush
  simp only [Multiset.map_map, Function.comp] at hpush
  have hid : (fun y => x + (y - x)) = (id : G → G) := by
    funext y; simp [add_sub_cancel]
  rw [hid, Multiset.map_id, Multiset.map_id] at hpush
  exact hpush

end ArkLib.ProximityGap.BhSidon
