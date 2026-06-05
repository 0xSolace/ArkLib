/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Polynomial.Basic

/-!
# Power-series composition coefficients (BCIKS20 App. A.4 -- WAVE 3 foundation)
-/

namespace ArkLib.PowerSeriesComposition

open Finset BigOperators PowerSeries

section Combinatorics

variable {M : Type*} [CommMonoid M]

/-- The multiset of values of a weak composition `l` over the index set `s`. -/
def valueMultiset {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) : Multiset ℕ :=
  s.val.map (fun i => l i)

@[simp]
theorem valueMultiset_card {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) :
    (valueMultiset s l).card = s.card := by
  rw [valueMultiset, Multiset.card_map, Finset.card_def]

theorem valueMultiset_sum {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ) :
    (valueMultiset s l).sum = ∑ i ∈ s, l i := by
  rw [valueMultiset, Finset.sum]

/-- Index-set product rewritten as product over the multiset of composition values. -/
theorem prod_eq_multiset_value_prod {ι : Type*} (s : Finset ι) (l : ι →₀ ℕ)
    (b : ℕ → M) :
    ∏ i ∈ s, b (l i) = ((valueMultiset s l).map b).prod := by
  rw [valueMultiset, Multiset.map_map, Finset.prod]
  rfl

end Combinatorics

end ArkLib.PowerSeriesComposition
