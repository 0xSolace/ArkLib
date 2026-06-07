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

/-- **Inter-orbit clause of `Admissible`, discharged from coset separation.** If distinct
domain points never lie in the same `⟨ω⟩`-coset — formalized as: `β = α · ω^i` (any natural
`i`) forces `α = β` — then no distinct pair collides under a short `ω`-shift. This is the
genuinely domain-dependent half; it holds e.g. when the domain is a transversal of the
`⟨ω⟩`-cosets in `Fˣ`. -/
theorem admissible_inter_of_cosetSep
    (L : Finset F) (s : ℕ) (ω : F)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β) :
    ∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β := by
  intro α hα β hβ hne i _ heq
  exact hne (hcoset α hα β hβ i heq)

/-- **Full `Admissible` discharge** from the order bound (intra-orbit) plus `⟨ω⟩`-coset
separation of the domain (inter-orbit). Together with `frs_is_subspaceDesign_gk16_of_admissible`
this gives an unconditional FRS τ-subspace-design instantiation (ABF26 T2.18) for any nonzero,
coset-separated domain and any `ω` with `orderOf ω ≥ s`. -/
theorem admissible_of_orderOf_ge_of_cosetSep
    (L : Finset F) (s : ℕ) (ω : F) (h0 : (0 : F) ∉ L) (hs : s ≤ orderOf ω)
    (hcoset : ∀ α ∈ L, ∀ β ∈ L, ∀ i : ℕ, α * ω ^ i = β → α = β) :
    Admissible L s ω :=
  admissible_of_orderOf_ge_of_inter L s ω h0 hs
    (admissible_inter_of_cosetSep L s ω hcoset)

/-! ## Canonical geometric folded-RS domain

The standard GR08 folded-RS evaluation domain `L = {γ^{s·i}}` with folding element `ω = γ`.
For `γ` of multiplicative order `≥ s·n`, this domain is injective, nonzero, and `⟨γ⟩`-coset
separated *within the fold window* `i < s` — so its `Admissible` predicate is **unconditional**.
This turns the FRS τ-subspace-design (ABF26 T2.18) into a fully discharged statement for the
canonical domain, with no remaining side condition beyond the order bound `s·n ≤ orderOf γ`. -/

/-- The geometric folded-RS domain map `i ↦ γ^{s·i}` on `Fin n`. -/
def geomDomainFn (γ : F) (s n : ℕ) : Fin n → F := fun i => γ ^ (s * i.val)

/-- Bounded coset-separation: within the fold window `i < s`, the geometric domain points have
disjoint `γ`-orbits, provided `s·n ≤ orderOf γ`. -/
theorem geomDomain_cosetSep_lt (γ : F) (s n : ℕ) (hs : 0 < s) (hsn : s * n ≤ orderOf γ) :
    ∀ a : Fin n, ∀ b : Fin n, ∀ i : ℕ, i < s →
      geomDomainFn γ s n a * γ ^ i = geomDomainFn γ s n b → a = b := by
  intro a b i hi heq
  unfold geomDomainFn at heq
  rw [← pow_add] at heq
  -- both exponents land in `Iio (orderOf γ)`
  have hexp_a : s * a.val + i < orderOf γ := by
    calc s * a.val + i < s * a.val + s := by omega
      _ = s * (a.val + 1) := by ring
      _ ≤ s * n := Nat.mul_le_mul_left s (by omega)
      _ ≤ orderOf γ := hsn
  have hexp_b : s * b.val < orderOf γ :=
    calc
      s * b.val < s * (b.val + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ s * n := Nat.mul_le_mul_left s (Nat.succ_le_of_lt b.isLt)
      _ ≤ orderOf γ := hsn
  have hnat : s * a.val + i = s * b.val :=
    pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hexp_a) (Set.mem_Iio.mpr hexp_b) heq
  -- `s·a + i = s·b`, `i < s`, `s > 0` ⇒ `a = b`
  have hab : a.val = b.val := by
    have hle : s * a.val ≤ s * b.val := by omega
    have hlt : s * b.val < s * (a.val + 1) := by rw [Nat.mul_succ]; omega
    have h1 : a.val ≤ b.val := Nat.le_of_mul_le_mul_left hle hs
    have h2 : b.val < a.val + 1 := Nat.lt_of_mul_lt_mul_left hlt
    omega
  exact Fin.ext hab

/-- The geometric domain is nonzero (`0 ∉ {γ^{s·i}}`) when `γ ≠ 0`. -/
theorem geomDomain_ne_zero (γ : F) (s n : ℕ) (hγ : γ ≠ 0) (i : Fin n) :
    geomDomainFn γ s n i ≠ 0 := pow_ne_zero _ hγ

end ReedSolomon.Folded
