/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.TopDirectionLineCount

/-!
# Issue #232 — Lam–Leung at the prime 2: vanishing sums of 2-power roots of unity

The classical base case of the O48 tower theorem (DISPROOF_LOG O47–O48), machine-checked:
**in characteristic zero, a subset of the `2^(m+1)`-th roots of unity with vanishing sum
is closed under negation** — equivalently, it is a disjoint union of antipodal pairs
`{x, −x}`. This is the prime-2 instance of Lam–Leung's theorem on vanishing sums of roots
of unity [LamLeung2000], and the engine is Gauss: the `2^(m+1)`-th cyclotomic polynomial
`X^(2^m) + 1` is the rational minimal polynomial of a primitive root, so the indicator
polynomial of the exponent set is divisible by it, which pairs the coefficients at `i` and
`i + 2^m` — and `ζ^(2^m) = −1`.

Consequences wired elsewhere: this discharges the `hLL`/`hLL'` hypotheses of
`TopLine.t2_tower_resolution` (the descent assembly of the tower theorem), making the
`t = 2` exhaustiveness — and, iterated, the full tower theorem and its `2^{O(1/η)}`
deep-interior fiber bound — unconditional over characteristic-zero fields (and over `F_p`
above the O49 effective transfer threshold).
-/

namespace LamLeungTwoPow

open Polynomial Finset

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- A primitive `2^(m+1)`-th root of unity has `ζ^(2^m) = −1`. -/
lemma pow_half_eq_neg_one {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1))) :
    ζ ^ (2 ^ m) = -1 := by
  have hsq : (ζ ^ 2 ^ m) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ m * 2 = 2 ^ (m + 1) := by ring
    rw [this]
    exact hζ.pow_eq_one
  have hne : ζ ^ 2 ^ m ≠ 1 := by
    intro h1
    have hlt : (2 : ℕ) ^ m < 2 ^ (m + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := hζ.pow_ne_one_of_pos_of_lt (Nat.two_pow_pos m).ne' hlt
    exact this h1
  have hfac : (ζ ^ 2 ^ m - 1) * (ζ ^ 2 ^ m + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- **Lam–Leung at the prime 2** (the O48 tower base case): in characteristic zero, a
finite set of `2^(m+1)`-th roots of unity with vanishing sum is closed under negation. -/
theorem vanishing_sum_antipodal {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 1)))
    {S : Finset F} (hS : ∀ x ∈ S, x ^ (2 ^ (m + 1)) = 1)
    (hsum : ∑ x ∈ S, x = 0) :
    ∀ x ∈ S, -x ∈ S := by
  classical
  set n := 2 ^ (m + 1) with hn
  set half := 2 ^ m with hhalf
  have hhn : half + half = n := by rw [hhalf, hn]; ring
  have hhalfpos : 0 < half := by positivity
  -- the exponent set
  set I : Finset ℕ := (Finset.range n).filter (fun i => ζ ^ i ∈ S) with hI
  -- powers are injective below n
  have hinj : ∀ i < n, ∀ j < n, ζ ^ i = ζ ^ j → i = j := by
    intro i hi j hj hij
    exact hζ.pow_inj hi hj hij
  -- the indicator polynomial over ℚ
  set P : ℚ[X] := ∑ i ∈ I, X ^ i with hP
  have hPcoeff : ∀ j, P.coeff j = if j ∈ I then 1 else 0 := by
    intro j
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_congr rfl (fun i _ => Polynomial.coeff_X_pow i j)]
    rw [Finset.sum_ite_eq I j (fun _ => (1 : ℚ))]
  -- ζ kills P
  have hPζ : Polynomial.aeval ζ P = 0 := by
    rw [hP, map_sum]
    have hterm : ∀ i ∈ I, Polynomial.aeval ζ ((X : ℚ[X]) ^ i) = ζ ^ i := by
      intro i _
      simp
    rw [Finset.sum_congr rfl hterm]
    -- ∑_{i ∈ I} ζ^i = ∑_{x ∈ S} x = 0
    rw [← hsum]
    apply Finset.sum_bij (fun i _ => ζ ^ i)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj hij
      rw [hI] at hi hj
      exact hinj i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hij
    · intro x hx
      obtain ⟨i, hi, hxi⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hxi.symm ▸ hx⟩, hxi⟩
    · intro i _
      rfl
  -- the cyclotomic polynomial divides P
  have hdvd : (X ^ half + 1 : ℚ[X]) ∣ P := by
    have hmin := minpoly.dvd ℚ ζ hPζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity)] at hmin
    have hcyc : Polynomial.cyclotomic (2 ^ (m + 1)) ℚ = X ^ half + 1 := by
      rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      rw [hhalf]
      ring
    rwa [hn, hcyc] at hmin
  -- coefficient pairing: P.coeff j = P.coeff (j + half) for j < half
  have hpair : ∀ j < half, P.coeff j = P.coeff (j + half) := by
    obtain ⟨Q, hQ⟩ := hdvd
    by_cases hP0 : P = 0
    · intro j _
      simp [hP0]
    have hQ0 : Q ≠ 0 := by
      intro h
      exact hP0 (by rw [hQ, h, mul_zero])
    have hdegP : P.natDegree < n := by
      rw [hP]
      have : (∑ i ∈ I, (X : ℚ[X]) ^ i).natDegree ≤ n - 1 :=
        Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => by
          rw [Polynomial.natDegree_X_pow]
          have := Finset.mem_range.mp (Finset.mem_filter.mp (hI ▸ hi)).1
          omega
      have hnpos : 0 < n := by positivity
      omega
    have hdegfac : (X ^ half + 1 : ℚ[X]).natDegree = half := by
      rw [show (X ^ half + 1 : ℚ[X]) = X ^ half + C 1 by rw [map_one]]
      exact Polynomial.natDegree_X_pow_add_C
    have hdegQ : Q.natDegree < half := by
      have hmul := Polynomial.natDegree_mul
        (show (X ^ half + 1 : ℚ[X]) ≠ 0 by
          intro h
          have := congrArg (Polynomial.natDegree) h
          rw [hdegfac] at this
          simp at this
          omega) hQ0
      rw [← hQ, hdegfac] at hmul
      omega
    intro j hj
    have hc1 : P.coeff j = Q.coeff j := by
      rw [hQ, add_mul, one_mul, Polynomial.coeff_add]
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_neg (by omega)]
      ring
    have hc2 : P.coeff (j + half) = Q.coeff j := by
      rw [hQ, add_mul, one_mul, Polynomial.coeff_add]
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_pos (by omega)]
      have : j + half - half = j := by omega
      rw [this]
      have hQj : Q.coeff (j + half) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hQj]
      ring
    rw [hc1, hc2]
  -- membership pairing
  have hmem : ∀ j < half, (ζ ^ j ∈ S ↔ ζ ^ (j + half) ∈ S) := by
    intro j hj
    have := hpair j hj
    rw [hPcoeff, hPcoeff] at this
    have hjI : j ∈ I ↔ j + half ∈ I := by
      by_cases h1 : j ∈ I <;> by_cases h2 : j + half ∈ I <;>
        simp [h1, h2] at this ⊢
    rw [hI] at hjI
    simp only [Finset.mem_filter, Finset.mem_range] at hjI
    constructor
    · intro hx
      exact (hjI.mp ⟨by omega, hx⟩).2
    · intro hx
      exact (hjI.mpr ⟨by omega, hx⟩).2
  -- conclude
  intro x hx
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hS x hx)
  have hζhalf := pow_half_eq_neg_one hζ
  rcases lt_or_ge i half with hcase | hcase
  · -- −ζ^i = ζ^(i+half)
    have hmem' := (hmem i hcase).mp hx
    have : ζ ^ (i + half) = -ζ ^ i := by
      rw [pow_add, hhalf, hζhalf]
      ring
    rwa [this] at hmem'
  · -- i ≥ half: −ζ^i = ζ^(i−half)
    have hj : i - half < half := by omega
    have hisplit : i = (i - half) + half := by omega
    have hmem' : ζ ^ (i - half) ∈ S := by
      apply (hmem (i - half) hj).mpr
      rwa [← hisplit]
    have : ζ ^ (i - half) = -ζ ^ i := by
      have h1 : ζ ^ i = ζ ^ (i - half) * ζ ^ half := by
        rw [← pow_add, ← hisplit]
      rw [hhalf] at h1
      rw [h1, hζhalf]
      ring
    rwa [this] at hmem'

/-- **The UNCONDITIONAL t = 2 tower resolution** over characteristic-zero fields: the
Lam–Leung base case discharges both hypotheses of `TopLine.t2_tower_resolution`. Every
finite set of `2^(m+2)`-th roots of unity with `∑x = ∑x² = 0` is closed under
multiplication by `i` — a union of `μ₄`-cosets. The O48 tower theorem's first two rungs
are now hypothesis-free. -/
theorem t2_resolution_unconditional {m : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ (m + 2)))
    {i : F} (hi : i ^ 2 = -1) {S : Finset F}
    (h0 : (0 : F) ∉ S) (hS : ∀ x ∈ S, x ^ (2 ^ (m + 2)) = 1)
    (hsum : ∑ x ∈ S, x = 0) (hsumsq : ∑ x ∈ S, x ^ 2 = 0) :
    ∀ x ∈ S, i * x ∈ S := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  apply TopLine.t2_tower_resolution hi h2 h0 hsum hsumsq
  · intro hs
    exact vanishing_sum_antipodal (m := m + 1) hζ hS hs
  · intro hs
    have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m + 1)) :=
      hζ.pow (by positivity) (by ring)
    refine vanishing_sum_antipodal (m := m) hζ2 ?_ hs
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [← pow_mul]
    have : 2 * 2 ^ (m + 1) = 2 ^ (m + 2) := by ring
    rw [this]
    exact hS x hx

end LamLeungTwoPow
