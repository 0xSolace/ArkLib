/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import Mathlib.GroupTheory.OrderOfElement

/-!
# Discharging the FRS `Admissible` side condition (ABF26 Def. 2.14, GR08)

`ReedSolomon.Folded.Admissible L s ω` is the order/orbit-separation hypothesis consumed by
`frs_is_subspaceDesign_gk16_of_admissible` (the in-tree, fully-proven form of ABF26 Theorem
2.18, "FRS is a τ-subspace-design"). It has two clauses:

* **intra-orbit** — `α · ω^i ≠ α` for `α ∈ L`, `0 < i < s`: no fold collapses an `s`-tuple
  to a repeated entry.
* **inter-orbit** — `α · ω^i ≠ β` for distinct `α, β ∈ L`, `i < s`: distinct domain points
  have disjoint length-`s` `ω`-orbits.

This file discharges the **intra-orbit** clause unconditionally from `s ≤ orderOf ω` and
`0 ∉ L` (a nonzero evaluation domain), and packages a constructor that builds the full
`Admissible` predicate from that order bound plus the genuinely domain-dependent inter-orbit
separation. This turns the intra-orbit half of the T2.18 instantiation from an admit into a
proved order-theoretic fact, leaving only the domain-coset inter-orbit condition.
-/

namespace ReedSolomon.Folded

variable {F : Type} [Field F] [DecidableEq F]

/-- **Intra-orbit clause of `Admissible`, discharged.** For a nonzero domain `L` and a folding
element `ω` whose multiplicative order is at least the fold length `s`, no nonzero domain point
is fixed by `ω^i` for `0 < i < s`. Order-theoretic: `α·ω^i = α ⟺ ω^i = 1 ⟺ orderOf ω ∣ i`, and
the smallest positive multiple of `orderOf ω` is `orderOf ω ≥ s > i`. -/
theorem admissible_intra_of_orderOf_ge
    (L : Finset F) (s : ℕ) (ω : F) (h0 : (0 : F) ∉ L) (hs : s ≤ orderOf ω) :
    ∀ α ∈ L, ∀ i : ℕ, 0 < i → i < s → α * ω ^ i ≠ α := by
  intro α hα i hi0 hi_s heq
  have hα0 : α ≠ 0 := by rintro rfl; exact h0 hα
  -- Cancel the nonzero `α`: `α * ω^i = α` forces `ω^i = 1`.
  have hpow : ω ^ i = 1 := by
    have : α * ω ^ i = α * 1 := by simpa using heq
    exact mul_left_cancel₀ hα0 this
  -- `ω^i = 1` ⇒ `orderOf ω ∣ i` ⇒ `orderOf ω ≤ i` (since `0 < i`).
  have hdvd : orderOf ω ∣ i := orderOf_dvd_of_pow_eq_one hpow
  have hle : orderOf ω ≤ i := Nat.le_of_dvd hi0 hdvd
  -- But `i < s ≤ orderOf ω`, contradiction.
  exact absurd (lt_of_lt_of_le hi_s hs) (not_lt.mpr hle)

/-- **`Admissible` constructor from the order bound + inter-orbit separation.** Combines the
discharged intra-orbit clause (`admissible_intra_of_orderOf_ge`) with the genuinely
domain-dependent inter-orbit separation hypothesis, yielding the full `Admissible` predicate
consumed by `frs_is_subspaceDesign_gk16_of_admissible`. -/
theorem admissible_of_orderOf_ge_of_inter
    (L : Finset F) (s : ℕ) (ω : F) (h0 : (0 : F) ∉ L) (hs : s ≤ orderOf ω)
    (hinter : ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β) :
    Admissible L s ω :=
  ⟨hinter, admissible_intra_of_orderOf_ge L s ω h0 hs⟩

end ReedSolomon.Folded
