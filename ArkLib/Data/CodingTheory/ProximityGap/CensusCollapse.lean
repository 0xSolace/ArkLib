/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CosetStrip

/-!
# The conditional census collapse: `a ≡ 0 (mod 4)` rows reduce to the `a = 4` row

Campaign #357. The strip step (`strip_coset`) iterates: under the (named, probe-true)
*contains-a-coset* obligation, every qualifying exponent set strips down to a qualifying
core of size `< 6` — same census value at every prime simultaneously, size preserved
mod 4:

> **`census_collapse_of_containsCoset`** — given `ContainsCosetHyp m`, every qualifying
> `A` has a qualifying core `A'` with `|A'| < 6`, `|A'| ≡ |A| (mod 4)`, and
> `∑_{i∈A} g^i = ∑_{i∈A'} g^i` for every `(p, g)`.

The obligation is restricted to sizes `≡ 0 (mod 4)`: the coset-free balanced 9-sets
(one orbit at `n = 16`, eleven at `n = 32` — `probe_a9_exceptional_family.py` and the
`n = 32` class sweep) REFUTE the naive all-sizes form, and the `a ≡ 1 (mod 4)` rows
genuinely do not collapse (their censuses grow with the primitive layer). The induction
preserves the mod-4 invariant, so the restricted hypothesis is all it ever invokes. Since
the only qualifying sizes `< 6` that are `≡ 0 (mod 4)` are `0` and `4`, the
`a ≡ 0 (mod 4)` censuses collapse onto `census(4) ∪ {0}` — the even-row quarter of the
depth-1 table, modulo the one named obligation: probe-verified at `a = 8, 12, 16` with
zero exceptions at `n = 16, 32` (all class structures) and `n = 64` (`k ≤ 5`),
doubling-stable, with the scale-uniform ℤ[i]-collision analysis as the named route.

## References

* Probes `probe_8set_coset_structure.py`, `probe_coset_core_conjecture.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

/-- **The named obligation** (the project's residual convention): every qualifying
exponent set of size a positive multiple of 4 contains a full coset of the order-4
subgroup in reduction. The size restriction is essential: the coset-free balanced 9-sets
refute the naive all-sizes form. Probe-true with zero exceptions at `n = 16, 32` (all
class structures) and `n = 64` (`k ≤ 5`), stable under the doubling functor; the
scale-uniform ℤ[i]-collision case analysis is the named proof route. -/
def ContainsCosetHyp (m : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range (2 ^ m) → 6 ≤ A.card → A.card % 4 = 0 →
    e2Folded m A = 0 →
    ∃ x : ZMod (2 ^ m),
      x ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)) ∧
      x + ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        ∈ A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))

/-- **The conditional census collapse.** Under the contains-a-coset obligation, every
qualifying set strips to a qualifying core of size `< 6`, congruent mod 4, with the same
census value at every prime and primitive root simultaneously. -/
theorem census_collapse_of_containsCoset {m : ℕ} (hm : 2 ≤ m) (hyp : ContainsCosetHyp m)
    {A : Finset ℕ} (hsub : A ⊆ Finset.range (2 ^ m)) (hmod : A.card % 4 = 0)
    (hzero : e2Folded m A = 0) :
    ∃ A' : Finset ℕ, A' ⊆ Finset.range (2 ^ m) ∧ A'.card < 6 ∧
      A'.card % 4 = A.card % 4 ∧ e2Folded m A' = 0 ∧
      ∀ {p : ℕ} [Fact p.Prime] (g : ZMod p), IsPrimitiveRoot g (2 ^ m) →
        ∑ i ∈ A, g ^ i = ∑ i ∈ A', g ^ i := by
  suffices H : ∀ n (A : Finset ℕ), A.card = n → A ⊆ Finset.range (2 ^ m) →
      A.card % 4 = 0 → e2Folded m A = 0 →
      ∃ A' : Finset ℕ, A' ⊆ Finset.range (2 ^ m) ∧ A'.card < 6 ∧
        A'.card % 4 = A.card % 4 ∧ e2Folded m A' = 0 ∧
        ∀ {p : ℕ} [Fact p.Prime] (g : ZMod p), IsPrimitiveRoot g (2 ^ m) →
          ∑ i ∈ A, g ^ i = ∑ i ∈ A', g ^ i by
    exact H A.card A rfl hsub hmod hzero
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hcard hsub hmod hzero
    by_cases h6 : A.card < 6
    · exact ⟨A, hsub, h6, rfl, hzero, fun g _ => rfl⟩
    · obtain ⟨x, hx, hxq, hxh, hxqh⟩ := hyp A hsub (by omega) hmod hzero
      obtain ⟨A'', hsub'', hcard'', hzero'', hsum''⟩ :=
        strip_coset hm hsub hzero hx hxq hxh hxqh
      obtain ⟨A', hsub', h6', hmod', hzero', hsum'⟩ :=
        ih A''.card (by omega) A'' rfl hsub'' (by omega) hzero''
      refine ⟨A', hsub', h6', by omega, hzero', ?_⟩
      intro p _ g hg
      rw [hsum'' g hg, hsum' g hg]

/-! ## Source audit -/

#print axioms census_collapse_of_containsCoset

end ArkLib.ProximityGap.WindowTwoLayer
