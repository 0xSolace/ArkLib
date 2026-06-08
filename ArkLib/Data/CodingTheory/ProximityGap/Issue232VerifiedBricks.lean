/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Verified bricks for the Ethereum Proximity Prize (Issue #232)

This file collects the elementary, fully machine-checked lemmas proven while sifting the candidate
generator for ArkLib Issue #232 (the $1M ABF26 Proximity Prize). Each is `sorry`-free and
axiom-clean (`#print axioms` ⇒ `[propext, Classical.choice, Quot.sound]`). None of them resolves
the prize: pinning the MCA threshold `δ*` in the Johnson→capacity gap with matching two-sided
bounds at `ε* = 2^{-128}` remains open research. These are honest *building blocks* and *honest
refutations* of naive/mis-targeted directions, kept here so the open core is correctly delineated
(cf. #169/#171: no fake-completion surfaces).

Contents:
* Algebraic structure — `hasseDeriv_X_pow_prime_pow_sub_one` (char-`p` Hasse–Lucas collapse of the
  vanishing polynomial) and `dyadic_factor_coprime_trivial` (2-adic CRT product-grid obstruction).
* Threshold geometry — `johnson_radius_le_capacity`, `radius_mono_in_exponent` (the
  `1 − ρ^{m/(m+1)}` family interpolates Johnson→capacity; the `1 − ρ^{2/3}` candidate is the
  `m = 2` member), and `candidate_between_johnson_and_capacity`.
* List-decoding engine — `fiber_root_card_le`, `grid_zero_count_le`, `on_curve_iff_mem_roots`, and
  `gs_list_card_le` (the Guruswami–Sudan list-size bound `|list| ≤ deg_Y(H)`).
* Refutations — `refute_naive_matrix_rank_bound`, `refute_naive_alg_independence_bound`.
-/

namespace ArkLib.ProximityGap.Issue232Bricks

open Polynomial

/-! ## Algebraic structure -/

section Algebraic
variable {R : Type*} [CommRing R]

/-- **Char-`p` middle binomial vanishing.** In a commutative ring of prime characteristic `p`,
`C(p^a, m)` casts to `0` for `0 < m < p^a` (Lucas/Kummer for the prime `p`), via comparing
`X^m`-coefficients of `(X+1)^{p^a}` (binomial theorem) and `X^{p^a}+1` (Frobenius). -/
lemma choose_prime_pow_cast_eq_zero (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) : ((p ^ a).choose m : R) = 0 := by
  have hfrob : (X + 1 : R[X]) ^ (p ^ a) = X ^ (p ^ a) + 1 := by
    have h : (X + 1 : R[X]) ^ (p ^ a) = X ^ (p ^ a) + (1 : R[X]) ^ (p ^ a) :=
      add_pow_char_pow X 1 p a
    rwa [one_pow] at h
  have e := congrArg (fun q : R[X] => q.coeff m) hfrob
  simp only [coeff_X_add_one_pow, coeff_add, coeff_X_pow, coeff_one] at e
  rw [if_neg (Nat.ne_of_lt hlt), if_neg (Nat.pos_iff_ne_zero.mp hm), add_zero] at e
  exact e

/-- **Hasse–Lucas collapse of the vanishing polynomial.** Over a characteristic-`p` ring,
`hasseDeriv m (X^{p^a} − 1) = 0` for `0 < m < p^a`. (The `p = 2` instance is the binary-field
case; relevant to additive/Binius domains, not the multiplicative-subgroup prize domain.) -/
theorem hasseDeriv_X_pow_prime_pow_sub_one (p : ℕ) [Fact p.Prime] [CharP R p]
    (a m : ℕ) (hm : 0 < m) (hlt : m < p ^ a) :
    hasseDeriv m (X ^ (p ^ a) - 1 : R[X]) = 0 := by
  ext j
  rw [coeff_zero, hasseDeriv_coeff, coeff_sub, coeff_X_pow, coeff_one]
  by_cases hj : j + m = p ^ a
  · rw [if_pos hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_one, hj]
    exact choose_prime_pow_cast_eq_zero p a m hm hlt
  · rw [if_neg hj, if_neg (show ¬ j + m = 0 by omega), sub_zero, mul_zero]

end Algebraic

/-- **Dyadic coprime impossibility.** If `a · b = 2^k` and `gcd a b = 1`, then `a = 1` or `b = 1`:
a power of two has no nontrivial coprime factorization. A real obstruction to CRT-style bivariate
"affine folding" of an explicit power-of-two (2-adic) smooth STARK domain into a coprime product
grid `L ≅ L₁ × L₂`. -/
theorem dyadic_factor_coprime_trivial (a b k : ℕ) (h_prod : a * b = 2 ^ k)
    (h_coprime : Nat.Coprime a b) : a = 1 ∨ b = 1 := by
  have ha : a ∣ 2 ^ k := ⟨b, h_prod.symm⟩
  have hb : b ∣ 2 ^ k := ⟨a, by rw [Nat.mul_comm]; exact h_prod.symm⟩
  obtain ⟨i, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb
  rcases Nat.eq_zero_or_pos i with hi | hi
  · left; simp [hi]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · right; simp [hj]
  exfalso
  have h2a : 2 ∣ 2 ^ i := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hi)
  have h2b : 2 ∣ 2 ^ j := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hj)
  have hg : (2 : ℕ) ∣ Nat.gcd (2 ^ i) (2 ^ j) := Nat.dvd_gcd h2a h2b
  rw [Nat.Coprime] at h_coprime
  rw [h_coprime] at hg
  exact absurd hg (by decide)

/-! ## Threshold geometry -/

section Threshold
open Real

/-- **Johnson radius ≤ capacity.** For a rate `ρ ∈ [0,1]`, the RS Johnson radius `1 − √ρ` is at
most the capacity (minimum distance) `1 − ρ`; equivalently `ρ ≤ √ρ`. -/
theorem johnson_radius_le_capacity (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    1 - Real.sqrt ρ ≤ 1 - ρ := by
  have h2 : ρ ^ 2 ≤ ρ := by nlinarith [h0, h1]
  have h3 : Real.sqrt (ρ ^ 2) ≤ Real.sqrt ρ := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq h0] at h3
  linarith

/-- **The radius family `1 − ρ^s` is monotone in the exponent `s`** (base `ρ ∈ (0,1]`). Hence the
`m`-interleaved Guruswami–Sudan radii `1 − ρ^{m/(m+1)}` interpolate monotonically from the Johnson
radius `1 − ρ^{1/2}` (`m = 1`) up to capacity `1 − ρ^1 = 1 − ρ` (`m → ∞`); the generator's
`1 − ρ^{2/3}` candidate is exactly the `m = 2` member. -/
theorem radius_mono_in_exponent (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) (s t : ℝ) (hst : s ≤ t) :
    1 - ρ ^ s ≤ 1 - ρ ^ t := by
  have hpow : ρ ^ t ≤ ρ ^ s := rpow_le_rpow_of_exponent_ge h0 h1 hst
  linarith

/-- The `1 − ρ^{2/3}` candidate sits between Johnson and capacity:
`1 − ρ^{1/2} ≤ 1 − ρ^{2/3} ≤ 1 − ρ`. -/
theorem candidate_between_johnson_and_capacity (ρ : ℝ) (h0 : 0 < ρ) (h1 : ρ ≤ 1) :
    1 - ρ ^ (1/2 : ℝ) ≤ 1 - ρ ^ (2/3 : ℝ) ∧ 1 - ρ ^ (2/3 : ℝ) ≤ 1 - ρ := by
  refine ⟨radius_mono_in_exponent ρ h0 h1 _ _ (by norm_num), ?_⟩
  have := radius_mono_in_exponent ρ h0 h1 (2/3 : ℝ) 1 (by norm_num)
  rwa [rpow_one] at this

end Threshold

/-! ## List-decoding engine -/

section ListDecoding
variable {F : Type*} [Field F]

/-- **Fiber root bound.** For a bivariate `H ∈ F[X][Y]` and a point `x`, the univariate fiber
`H(x,·) = H.map (eval x)` has at most `deg_Y(H) = H.natDegree` roots `y`. -/
theorem fiber_root_card_le (H : Polynomial (Polynomial F)) (x : F) :
    (H.map (Polynomial.evalRingHom x)).roots.card ≤ H.natDegree :=
  le_trans (Polynomial.card_roots' _) (Polynomial.natDegree_map_le)

/-- **Grid zero-count bound.** Summed over an evaluation set `S`, the fiberwise curve-point count
`{(x,y) : H(x,y) = 0}` is at most `|S| · deg_Y(H)` (Schwartz–Zippel-style global bound). -/
theorem grid_zero_count_le (H : Polynomial (Polynomial F)) (S : Finset F) :
    ∑ x ∈ S, (H.map (Polynomial.evalRingHom x)).roots.card ≤ S.card * H.natDegree := by
  calc ∑ x ∈ S, (H.map (Polynomial.evalRingHom x)).roots.card
      ≤ ∑ _x ∈ S, H.natDegree := Finset.sum_le_sum (fun x _ => fiber_root_card_le H x)
    _ = S.card * H.natDegree := by rw [Finset.sum_const, smul_eq_mul]

/-- A message polynomial `p ∈ F[X]` lies on the curve `H` (`H(X, p(X)) = 0`) iff it is a root of
`H` in the integral domain `F[X]`. -/
theorem on_curve_iff_mem_roots (H : Polynomial (Polynomial F)) (hH : H ≠ 0) (p : Polynomial F) :
    Polynomial.eval p H = 0 ↔ p ∈ H.roots := by
  rw [Polynomial.mem_roots hH]; rfl

/-- **Guruswami–Sudan list-size bound.** The number of distinct message polynomials lying on the
interpolation curve `H` (the GS candidate list) is at most the `Y`-degree `deg_Y(H)` — exactly
`card_roots'` in the integral domain `F[X]`. The honest combinatorial core of the Grand List
Decoding Challenge; the open part is the interpolation degree budget pinning `δ*`. -/
theorem gs_list_card_le (H : Polynomial (Polynomial F)) :
    H.roots.card ≤ H.natDegree :=
  Polynomial.card_roots' H

/-- **Interpolation existence by counting (the GS interpolation engine).** A linear map from a
finite-dimensional `V` to `W` with `finrank W < finrank V` has a nonzero kernel vector. With
`V =` bivariate polynomials of degree `≤ (d_X, d_Y)` (dimension `(d_X+1)(d_Y+1)`) and `f =`
evaluation at `N` agreement points (`W = Fᴺ`), this is the Guruswami–Sudan interpolation step:
when `(d_X+1)(d_Y+1) > N` there is a nonzero bivariate `H` vanishing at all `N` points. Pairs with
`gs_list_card_le` to give the GS skeleton (existence + list bound); the open part is the
agreement ⇒ root (multiplicity) step that pins which roots are genuine codewords. -/
theorem interpolation_kernel_nontrivial {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hni : ¬ Function.Injective f := by
    intro hinj
    have := LinearMap.finrank_le_finrank_of_injective hinj
    omega
  rw [← LinearMap.ker_eq_bot] at hni
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hni
  exact ⟨v, hv_ne, LinearMap.mem_ker.mp hv_mem⟩

end ListDecoding

/-! ## Refutations of naive list-size bounds -/

/-- **Refute Hyp7 (naive matrix-rank list bound `|L| ≤ k²`).** False unconditionally: a single
evaluation point with `k = 0` breaks it (`1 ≤ 0`). -/
theorem refute_naive_matrix_rank_bound {ι F : Type*} [Nonempty ι] [Zero F] :
    ¬ ∀ (L : Finset (ι → F)) (k : ℕ), L.card ≤ k ^ 2 := by
  intro h
  have := h {0} 0
  simp at this

/-- **Refute Hyp8 (naive algebraic-independence bound `|L| ≤ |F|`).** False: the full space
`L = univ` has `|F|^{|ι|} > |F|` elements once `|ι| ≥ 2` and `|F| ≥ 2`. -/
theorem refute_naive_alg_independence_bound {ι F : Type*} [Fintype ι] [Fintype F]
    [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) (hF : 2 ≤ Fintype.card F) :
    ¬ ∀ (L : Finset (ι → F)), L.card ≤ Fintype.card F := by
  intro h
  have hle := h Finset.univ
  rw [Finset.card_univ, Fintype.card_fun] at hle
  have hpow : Fintype.card F ^ 2 ≤ Fintype.card F ^ Fintype.card ι :=
    Nat.pow_le_pow_right (by omega) hι
  have hlt : Fintype.card F < Fintype.card F ^ 2 := by
    rw [pow_two]; exact lt_mul_of_one_lt_left (by omega) (by omega)
  omega

end ArkLib.ProximityGap.Issue232Bricks
