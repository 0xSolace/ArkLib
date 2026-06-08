/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Subspace-rank and dyadic-domain sanity checks around the ABF26 prize (NOT a prize resolution)

**Honesty note.** A previous revision of this file presented itself as "The Ethereum Proximity
Prize (ABF26) Threshold Resolution", decorating a trivial `finrank` subadditivity lemma and a
`sorry`-stub as a "$1M proof". Per ArkLib Issues #169/#171/#232, that fake-completion framing is
banned: the prize is genuinely open and requires new mathematics that cannot be ground out. This
file now contains only honestly-named, fully-proven elementary lemmas that are *relevant context*
for the "affine folding / derandomization" research direction but do **not** bound any code's
`ε_mca` or pin the threshold `δ*`.

Contents (both `sorry`-free, `[propext, Classical.choice, Quot.sound]`-clean):

* `mcaSubspaceRank_sup_le` — finrank subadditivity for a `signal ⊔ noise` decomposition. A direct
  corollary of `Submodule.finrank_sup_add_finrank_inf_eq`; the "noise subspace" framing is just an
  interpretation, the lemma is pure linear algebra.
* `dyadic_factor_coprime_trivial` — a power of two cannot be split into two *coprime* factors both
  `> 1`. This is the genuine obstruction behind why bivariate "affine grid" folding `L ≅ L₁ × L₂`
  is unavailable for a strongly 2-adic STARK domain `|L| = 2^k`: a nontrivial coprime product
  factorization simply does not exist. (It does **not** show folding is impossible by *any* route,
  only that the coprime-grid route is vacuous; that is an honest negative observation, not a prize
  result.)
-/

namespace ProximityPrize

universe u

/-- The finrank of a "noise subspace", used below only as an interpretive label for an otherwise
plain `Module.finrank`. -/
noncomputable def mcaSubspaceRank {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V]
    (noise_subspace : Submodule F V) : ℕ :=
  Module.finrank F noise_subspace

/-- **Rank subadditivity.** `finrank (signal ⊔ noise) ≤ finrank signal + finrank noise`. A direct
consequence of the dimension formula `finrank (S ⊔ N) + finrank (S ⊓ N) = finrank S + finrank N`.
This is the honest content of the previous "red-team defeat" theorem. -/
theorem mcaSubspaceRank_sup_le
    {F : Type u} [Field F] {V : Type u} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (signal noise : Submodule F V) :
    mcaSubspaceRank (signal ⊔ noise) ≤ mcaSubspaceRank signal + mcaSubspaceRank noise := by
  unfold mcaSubspaceRank
  have h := Submodule.finrank_sup_add_finrank_inf_eq signal noise
  omega

/-- **Dyadic domains admit no nontrivial coprime factorization.** If `a * b = 2 ^ k` and
`Nat.Coprime a b`, then `a = 1` or `b = 1`.

Proof: if both `a, b > 1`, each has a prime factor (`Nat.exists_prime_and_dvd`); that prime divides
`2 ^ k`, hence equals `2` (`Nat.Prime.dvd_of_dvd_pow`). So `2 ∣ a` and `2 ∣ b`, giving
`2 ∣ gcd a b = 1` — a contradiction.

Cryptographic STARK evaluation domains have size `|L| = 2 ^ k`, so the bivariate "affine grid"
folding `L ≅ L₁ × L₂` with coprime side-lengths is *vacuously unavailable*: the only coprime
factorizations are the trivial `1 × 2^k`. This is a real obstruction for the coprime-grid route,
not a statement that the prize threshold is resolved. -/
theorem dyadic_factor_coprime_trivial (a b k : ℕ) (h_prod : a * b = 2 ^ k)
    (h_coprime : Nat.Coprime a b) : a = 1 ∨ b = 1 := by
  by_contra h
  push_neg at h
  obtain ⟨ha, hb⟩ := h
  -- `a, b ≠ 0` since their product `2^k` is nonzero.
  have hab0 : a * b ≠ 0 := by rw [h_prod]; exact pow_ne_zero k (by norm_num)
  have ha0 : a ≠ 0 := fun h0 => hab0 (by simp [h0])
  have hb0 : b ≠ 0 := fun h0 => hab0 (by simp [h0])
  -- `a, b > 1`, so each has a prime factor; that prime divides `2^k`, hence equals `2`.
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (show a ≠ 1 from ha)
  obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd (show b ≠ 1 from hb)
  have hpk : p ∣ 2 ^ k := hpa.trans ⟨b, h_prod.symm⟩
  have hqk : q ∣ 2 ^ k := hqb.trans ⟨a, by rw [mul_comm]; exact h_prod.symm⟩
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow hpk)
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
    (hq.dvd_of_dvd_pow hqk)
  -- Then `2 ∣ a` and `2 ∣ b`, so `2 ∣ gcd a b = 1`, contradiction.
  have h2a : (2 : ℕ) ∣ a := hp2 ▸ hpa
  have h2b : (2 : ℕ) ∣ b := hq2 ▸ hqb
  have hg : (2 : ℕ) ∣ Nat.gcd a b := Nat.dvd_gcd h2a h2b
  rw [h_coprime.gcd_eq_one] at hg
  norm_num at hg

end ProximityPrize
