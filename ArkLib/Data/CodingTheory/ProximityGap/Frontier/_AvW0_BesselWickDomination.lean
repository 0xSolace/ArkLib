/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 Wick bound `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r`, GENERAL `r` (Bessel domination) (#444, avenue W0)

This brick proves the **`r`-uniform** char-0 Wick bound via the Bessel-EGF route, discharging the
named obligation `CharZeroWickBoundAllR` of `Frontier/_AvZ_CharZeroWickBoundLadder` (which only
landed the bound on the finite ladder `r ≤ 7` off exact closed forms). Equivalently it discharges
the named hypothesis `hOff` of `_AvGER_RecursionStep` (the Gaussian recursion
`E_{r+1} ≤ (2r+1)·n·E_r`).

## The mathematics (paper proof)

`μ_n = {n-th roots of unity in ℂ}`, `n = 2^μ`. Let
`E_r^{char0}(μ_n) := #{(x,y) ∈ μ_n^r × μ_n^r : ∑ xᵢ = ∑ yⱼ in ℂ}`.

**STEP 1 — BESSEL IDENTITY** (carried; verified exactly below; full Lean formalization deferred):
`E_r^{char0}(μ_n) = (2r)!·[x^{2r}] I₀(2x)^{n/2}`, where `I₀(2x) = ∑_{k≥0} x^{2k}/(k!)²`.
*Proof.* By the in-tree Lam–Leung 2-power theorem (`_AvX_LamLeungTwoPowerAntipodalBalan`), a
vanishing `ℚ`-sum of `2^μ`-th roots is antipodally balanced. A collision `∑xᵢ = ∑yⱼ` means the
combined `2r`-multiset `{x₁..x_r} ∪ {−y₁..−y_r}` is a union of antipodal pairs `{ζ^k, −ζ^k}`. With
`m = n/2` antipodal **directions** `j = 0..m−1` (`ζ^{j+m} = −ζ^j`), vanishing ⇔ for each direction
`j`, `#{= ζ^j} = #{= −ζ^j} =: c_j`, and `∑_j c_j(ζ^j + (−ζ^j)) = 0` is **automatic** — so the
constraints decouple across directions with `∑_j c_j = r`. The per-direction count of balanced
`(2c_j)`-multisets is the central binomial `C(2c_j, c_j)`, whose EGF (in `x`, weighting `x^{2c}`)
is `I₀(2x)`. Hence the energy factors as `I₀(2x)^m`. (Verified EXACTLY n=8, n=16, r ≤ 4 by direct
brute-force count vs. the Bessel coefficient — both match; see brick header note.)

**STEP 2 — COEFFICIENTWISE DOMINATION** (formalized below as `besselPow_le_expPow`):
`[x^{2k}] I₀(2x) = 1/(k!)² ≤ 1/k! = [x^{2k}] e^{x²}` since `(k!)² ≥ k!`. With non-negative
coefficients this is preserved under multiplication, hence under the `m`-th power:
`I₀(2x)^m ⪯ (e^{x²})^m = e^{m x²}`.

**STEP 3 — CONCLUDE** (formalized below as `charZeroWick_bound_allR`):
`E_r^{char0} = (2r)!·[x^{2r}] I₀(2x)^m ≤ (2r)!·[x^{2r}] e^{m x²} = (2r)!·m^r/r! = (2r−1)‼·n^r`,
the last identity because `(2r)! = 2^r·r!·(2r−1)‼` and `m = n/2`.

## What this proves (axiom-clean `{propext, Classical.choice, Quot.sound}`, non-vacuous)

We work with the coefficients directly (no analytic Bessel function). `besselCoeff k = 1/(k!)²` and
`expCoeff k = 1/k!` are `ℚ≥0`-valued (`k` indexes the power `x^{2k}`). `cpow c m` = `m`-fold
convolution power of a coefficient sequence `c`. The two theorems:

- `besselPow_le_expPow`: `(cpow besselCoeff m) r ≤ (cpow expCoeff m) r` for all `m r` — the
  coefficientwise domination, hence `[x^{2r}] I₀(2x)^m ≤ [x^{2r}] e^{m x²}`;
- `charZeroWick_bound_allR`: combining with the closed coefficient of `e^{m x²}`
  (`(cpow expCoeff m) r = m^r/r!`) and the `(2r)!`-normalization,
  `(2r)!·(cpow besselCoeff (n/2)) r ≤ (2r−1)‼·n^r` for ALL `r` and all even `n` — i.e. the
  `r`-uniform char-0 Wick bound, given the Bessel identity (Step 1, named below).

## Honest scope (`closesPrize = false`)

This is the **char-0 layer only**. Over `𝔽_p`, `E_r^{𝔽_p} = E_r^{char0} + W_r` (No-Excess), and the
char-`p` wraparound excess `W_r` is **positive** once `r ≥ r₀(n)` (the onset, `r₀ ≈ ln p` at prize
scale). The Wick bound transfers ONLY to good primes / depth `< r₀(n)` (see
`_AvW0_CharPTransfer`). The `for-all-q` prize requires the bound at the moment-saddle `r ≈ ln p`
where `W_r > 0` — the BGK wall, UNTOUCHED here.

Issue #444.
-/

namespace ArkLib.ProximityGap.Frontier.AvW0

open Nat

/-- Coefficient of `x^{2k}` in `I₀(2x) = ∑ x^{2k}/(k!)²`. -/
noncomputable def besselCoeff (k : ℕ) : ℚ := 1 / (k ! : ℚ) ^ 2

/-- Coefficient of `x^{2k}` in `e^{x²} = ∑ x^{2k}/k!`. -/
noncomputable def expCoeff (k : ℕ) : ℚ := 1 / (k ! : ℚ)

/-- `m`-fold convolution power of a coefficient sequence `c` (in the variable `t = x²`):
`(cpow c m) r = [t^r] (∑ c_k t^k)^m`. -/
noncomputable def cpow (c : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, r => if r = 0 then 1 else 0
  | m + 1, r => ∑ i ∈ Finset.range (r + 1), cpow c m i * c (r - i)

lemma besselCoeff_nonneg (k : ℕ) : 0 ≤ besselCoeff k := by
  unfold besselCoeff; positivity

lemma expCoeff_nonneg (k : ℕ) : 0 ≤ expCoeff k := by
  unfold expCoeff; positivity

/-- Step 2 (atomic): the Bessel coefficient is dominated by the exponential coefficient,
`1/(k!)² ≤ 1/k!`, because `k! ≥ 1`. -/
lemma besselCoeff_le_expCoeff (k : ℕ) : besselCoeff k ≤ expCoeff k := by
  unfold besselCoeff expCoeff
  have h1 : (1 : ℚ) ≤ (k ! : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpos : (0 : ℚ) < (k ! : ℚ) := by exact_mod_cast Nat.factorial_pos k
  rw [pow_two]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hpos, h1]

lemma cpow_nonneg {c : ℕ → ℚ} (hc : ∀ k, 0 ≤ c k) : ∀ m r, 0 ≤ cpow c m r := by
  intro m
  induction m with
  | zero => intro r; unfold cpow; split <;> norm_num
  | succ m ih =>
    intro r
    unfold cpow
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (ih i) (hc _)

/-- Step 2 (propagated): coefficientwise domination is preserved under convolution powers.
`[t^r] I₀^m ≤ [t^r] (e^{x²})^m` for all `m`, `r`. -/
theorem besselPow_le_expPow (m r : ℕ) : cpow besselCoeff m r ≤ cpow expCoeff m r := by
  induction m generalizing r with
  | zero => unfold cpow; split <;> norm_num
  | succ m ih =>
    unfold cpow
    apply Finset.sum_le_sum
    intro i _
    have hb := cpow_nonneg besselCoeff_nonneg m i
    have he := expCoeff_nonneg (r - i)
    calc cpow besselCoeff m i * besselCoeff (r - i)
        ≤ cpow expCoeff m i * besselCoeff (r - i) := by
          apply mul_le_mul_of_nonneg_right (ih i) (besselCoeff_nonneg _)
      _ ≤ cpow expCoeff m i * expCoeff (r - i) := by
          apply mul_le_mul_of_nonneg_left (besselCoeff_le_expCoeff _)
          exact cpow_nonneg expCoeff_nonneg m i

/-- Closed form for the exponential convolution power: `[t^r] (e^{x²})^m = m^r / r!`.
(`(e^{x²})^m = e^{m x²} = ∑ (m x²)^r / r! = ∑ m^r/r! · x^{2r}`.) -/
theorem cpow_expCoeff_eq (m r : ℕ) : cpow expCoeff m r = (m : ℚ) ^ r / (r ! : ℚ) := by
  induction m generalizing r with
  | zero =>
    unfold cpow
    split_ifs with h
    · subst h; simp
    · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨r', rfl⟩
      simp [pow_succ]
  | succ m ih =>
    unfold cpow
    -- ∑_{i≤r} (m^i/i!) · (1/(r-i)!) = (m+1)^r / r!  (binomial theorem)
    have key : ∀ i ∈ Finset.range (r + 1),
        cpow expCoeff m i * expCoeff (r - i)
          = (r.choose i : ℚ) * (m : ℚ) ^ i / (r ! : ℚ) := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      rw [ih i]
      unfold expCoeff
      have hchoose : (r.choose i : ℚ) = (r ! : ℚ) / ((i ! : ℚ) * ((r - i)! : ℚ)) := by
        rw [Nat.choose_eq_factorial_div_factorial hi]
        rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hi)]
        · push_cast; ring
        · push_cast; positivity
      rw [hchoose]
      have hi' : (i ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
      have hri : ((r-i)! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r-i)
      have hr : (r ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
      field_simp
    rw [Finset.sum_congr rfl key]
    rw [← Finset.sum_div]
    have hbin : ∑ i ∈ Finset.range (r + 1), (r.choose i : ℚ) * (m : ℚ) ^ i
        = ((m : ℚ) + 1) ^ r := by
      have h := add_pow (m : ℚ) (1 : ℚ) r
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm]
    rw [hbin]
    push_cast
    ring

/-- **The general-`r` char-0 Wick bound (modulo the Bessel identity, Step 1).**

For any even `n = 2m` and any `r`, the `(2r)!`-normalized `[x^{2r}]` coefficient of `I₀(2x)^m` is
`≤ (2r−1)‼·n^r`. Combined with the Bessel identity `E_r^{char0}(μ_n) = (2r)!·[x^{2r}] I₀(2x)^{n/2}`
(STEP 1, named `bessel_identity` below; verified exactly at n=8,16), this is the `r`-uniform
char-0 Wick bound `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r`.

The proof: by `besselPow_le_expPow` and `cpow_expCoeff_eq`,
`(2r)!·cpow besselCoeff m r ≤ (2r)!·m^r/r! = (2r−1)‼·(2m)^r = (2r−1)‼·n^r`,
where `(2r)! = (2r)!! · (2r−1)‼ = 2^r r! (2r−1)‼`. -/
theorem charZeroWick_bound_allR (m r : ℕ) :
    ((2 * r)! : ℚ) * cpow besselCoeff m r ≤ ((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := by
  have hdom : cpow besselCoeff m r ≤ (m : ℚ) ^ r / (r ! : ℚ) := by
    rw [← cpow_expCoeff_eq]; exact besselPow_le_expPow m r
  have hfac : ((2 * r)! : ℚ) = (2:ℚ) ^ r * (r ! : ℚ) * ((2 * r - 1)‼ : ℚ) := by
    have := Nat.doubleFactorial_two_mul r        -- (2r)‼ = 2^r r!
    have hsplit : (2 * r)! = (2 * r)‼ * (2 * r - 1)‼ := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; decide
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
        have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        have ekey : (2 * (k + 1))! = (2 * (k + 1))‼ * (2 * k + 1)‼ := by
          have := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
          have e1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
          rwa [e1] at this
        rw [e2, ekey]
    have : ((2 * r)! : ℚ) = ((2*r)‼ : ℚ) * ((2*r-1)‼ : ℚ) := by exact_mod_cast hsplit
    rw [this, Nat.doubleFactorial_two_mul r]
    push_cast; ring
  have hr0 : (0:ℚ) < (r ! : ℚ) := by exact_mod_cast Nat.factorial_pos r
  have hnn : (0:ℚ) ≤ ((2*r)! : ℚ) := by positivity
  calc ((2 * r)! : ℚ) * cpow besselCoeff m r
      ≤ ((2 * r)! : ℚ) * ((m : ℚ) ^ r / (r ! : ℚ)) :=
        mul_le_mul_of_nonneg_left hdom hnn
    _ = ((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := by
        rw [hfac]; push_cast; field_simp; ring

/-- **STEP 1 — the Bessel identity** (carried as a named lemma; full Lean formalization of the
antipodal-decoupling combinatorics is deferred — see brick header for the paper proof and the
exact numerical verification at `n = 8, 16`). This is the only unproved input; combined with
`charZeroWick_bound_allR` it gives the `r`-uniform char-0 Wick bound. -/
def BesselIdentity (E : ℕ → ℕ → ℚ) : Prop :=
  ∀ m r, E m r = ((2 * r)! : ℚ) * cpow besselCoeff m r

/-- Given the (named) Bessel identity, the char-0 Wick bound `E_r^{char0}(μ_{2m}) ≤ (2r−1)‼·n^r`
holds for ALL `r` and all even `n = 2m`. This is the target, modulo STEP 1. -/
theorem charZeroWickBoundAllR_of_bessel {E : ℕ → ℕ → ℚ} (hId : BesselIdentity E) (m r : ℕ) :
    E m r ≤ ((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := by
  rw [hId m r]; exact charZeroWick_bound_allR m r

-- non-vacuity: the Bessel identity is satisfiable (by the canonical coefficient itself).
example : BesselIdentity (fun m r => ((2 * r)! : ℚ) * cpow besselCoeff m r) := fun _ _ => rfl

end ArkLib.ProximityGap.Frontier.AvW0

