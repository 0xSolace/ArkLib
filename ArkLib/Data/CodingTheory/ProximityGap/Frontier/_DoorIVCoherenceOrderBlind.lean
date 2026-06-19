/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# Door IV coherence is multiplicative-order-blind

This file records the axiom-clean obstruction behind the probe
`scripts/probes/probe_dooriv_rho_vs_order.py`.

## Probe context (door-(iv) Lane 1)

The brief's localized object is the index-2 coset-half coherence `ρ(b)` of the period sum
`S(b) = ∑_{x∈μ_n} e_p(b·x)`.
A natural anti-concentration lever would be to target frequencies `b` of *special multiplicative
order* (a small subgroup, roots of unity) hoping for systematically smaller `ρ` (more cancellation).

The probe (proper `μ_n`, `p ≫ n³`, structured primes) shows this lever is empty:

* the mean `ρ(b)`, bucketed by `ord(b)/φ` into tiny `(≤0.05)`, small `(≤0.5)`, large `(>0.5)`, is
  **flat at `≈0.70–0.74`** across all order classes — `ρ` does not track order;
* the worst `b` (`argmax|S|`) has `ρ = 1.0000` with **generic** order (`ord(b)/φ ∈
  {0.014, 0.33, 0.5, 1.0}` across primes — no special value).

So `ρ` is **order-blind**.

## The brick (mechanism)

`ρ(b)` is built from the two coset-half period sums, which are **constant on multiplicative cosets**
`b·μ_n` (in-tree `_EtaCosetInvariance`).  Hence `ρ` is `μ_n`-coset-invariant.  But the
multiplicative order is *not* a coset invariant: two elements of the same coset `b·μ_n` can have
different orders.  Therefore a coset-invariant statistic takes the **same** value at every order
present in a coset, and no order-indexed restriction can constrain it.  We formalize the abstract
obstruction: a function constant on the cosets of a subgroup `H` is equal on any two `H`-translates
— in particular on a pair of same-coset elements with different orders.  This is a constraint lemma,
not `CORE`, and uses no moment or completion.
-/

namespace ProximityGap.Frontier.DoorIVCoherenceOrderBlind

variable {G : Type*} [Group G]

/-- Coset-invariance of a statistic `f` w.r.t. a subgroup `H`: `f` is unchanged by left-multiplying
by any element of `H`.  (This is the property the coset-half period sums — and hence `ρ` — satisfy
by `_EtaCosetInvariance`.) -/
def CosetInvariant (H : Subgroup G) {β : Type*} (f : G → β) : Prop :=
  ∀ (c : G), c ∈ H → ∀ b : G, f (c * b) = f b

/-- A coset-invariant statistic takes equal values on any two elements of the same left coset
(elements differing by a left `H`-translate). -/
theorem eq_of_cosetInvariant_of_sameCoset {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {a b : G} (hab : a * b⁻¹ ∈ H) :
    f a = f b := by
  have hkey : a = (a * b⁻¹) * b := by group
  rw [hkey, hf (a * b⁻¹) hab b]

/-- **Order-blindness obstruction.**  If `f` is `H`-coset-invariant and two same-coset elements
`a, b` (with `a · b⁻¹ ∈ H`) have *different* multiplicative orders, then `f` still takes the
**same** value on them.  Thus a statistic that is `H`-coset-invariant cannot be made to depend on
multiplicative order of its argument: no order-indexed restriction constrains it.  (Here `H = μ_n`,
`f = ρ`; the probe exhibits same-coset elements of differing order, all with the same `ρ`.) -/
theorem cosetInvariant_blind_to_order {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {a b : G} (hab : a * b⁻¹ ∈ H)
    (_hord : orderOf a ≠ orderOf b) :
    f a = f b :=
  eq_of_cosetInvariant_of_sameCoset hf hab

/-- Contrapositive packaging: if a coset-invariant statistic takes *distinct* values on `a` and `b`,
then `a` and `b` are in *different* cosets — so any genuine `ρ`-difference is a coset-level (not
order-level) phenomenon. -/
theorem distinct_value_forces_distinct_coset {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : CosetInvariant H f) {a b : G} (hne : f a ≠ f b) :
    a * b⁻¹ ∉ H := by
  intro hab
  exact hne (eq_of_cosetInvariant_of_sameCoset hf hab)

end ProximityGap.Frontier.DoorIVCoherenceOrderBlind
