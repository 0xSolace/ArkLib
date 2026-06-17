/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonResultantImproved

/-!
# The improved Sidon resultant bound is TIGHT — the extremal four-term meets `8^{φ(n)}` (#444, #389)

`SidonResultantImproved.abs_resultant_fourTerm_sq_le` gives the no-parallelogram resultant cap
`|Res(Φ_n, fourTerm i j k l)|² ≤ 8^{φ(n)}` (distinct-exponent `S = 4` case), the engine behind the
in-tree threshold `p > 2^{3n/4}` (`SidonThresholdImproved.prime_sq_le_of_parallelogram`).  That bound
comes from `‖f(ζ)‖ ≤ 4` at each primitive root plus AM-GM (`∏‖f(ζ)‖² ≤ ∏ 8 = 8^{φ(n)}` via the
Parseval `∑_a ‖s_a‖² = 4` budget).  **Whether the AM-GM step loses anything was never settled** — i.e.
is the cap `8^{φ(n)}` actually *attained*, or is the true worst-case resultant smaller (a sharpenable
threshold)?

This file settles it: the cap is **exactly tight**.  The extremal four-term is the balanced
`fourTerm 0 (n/4) (n/2) (3n/4)`, and it factors cleanly

  **`fourTerm_balanced_factor`** : `fourTerm 0 (n/4) (n/2) (3n/4) = (X^{n/4} + 1) * (1 - X^{n/2})`
  (over `ℤ[X]`, `n = 2^m`, `m ≥ 2`),

and at *every* primitive `n`-th root `ζ` its squared modulus is the **constant** `8`:

  **`normSq_eval_balanced_eq_eight`** : for `ζ` a primitive `2^m`-th root of unity in `ℂ` (`m ≥ 2`),
  `‖(fourTerm 0 (n/4) (n/2) (3n/4)).eval₂ (algebraMap ℤ ℂ) ζ‖² = 8`.

Mechanism (the reason AM-GM is lossless here): at a primitive `2^m`-th root, `ζ^{n/2}` is a primitive
square root of unity, hence `= -1`, so `1 - ζ^{n/2} = 2`; and `ζ^{n/4}` is a primitive *fourth* root,
hence `(ζ^{n/4})² = -1`, so `‖1 + ζ^{n/4}‖² = 2`.  Thus `‖f(ζ)‖² = 2² · 2 = 8` at **every** root — the
Parseval budget `∑‖s_a‖² = 4` per root is spread *uniformly* (`= 2` per term), the equality case of
AM-GM.  Composing with the in-tree complex product formula (`resultant_cast_eq_prod`) this yields
`|Res(Φ_n, f_balanced)|² = ∏_ζ 8 = 8^{φ(n)}` — the cap **attained**, so the threshold `p > 2^{3n/4}`
is the *sharp* guaranteed no-(distinct-)parallelogram threshold; no resultant-level sharpening exists.

## Honest scope (rules 1, 3, 6 + asymptotic guard)

This is a **wall-mapping** result, NOT a CORE closure (rule 4: a precisely-mapped wall is a result).
It does NOT improve the threshold (it proves the threshold is *already sharp*), and crucially the sharp
threshold `2^{3n/4}` is **exponential** in `n`, whereas the prize regime has `p ≈ n^β` (`β ≈ 4-5`),
i.e. `p` *polynomial* in `n` and thus *exponentially below* the threshold.  So `μ_n` is provably
**not** Sidon-mod-negation in the prize regime by this method, and the additive-energy/Sidon route is
confirmed structurally non-proving for the prize (the `E(μ_n) = 3n²-3n` char-0 value
`RootsOfUnityAdditiveEnergyExact` lifts to `F_p` only above `2^{3n/4}`, far above the prize `p`).
No capacity / beyond-Johnson / cliff-at-`n/2` claim.  CORE `M(μ_n) ≤ C√(n log(p/n))` OPEN.

Probe `scripts/probes/probe_step_worstcase_res_exact.py` (exact integer cyclotomic resultants,
`n = 2^a`, `a ∈ {2,3,4,5}`): the balanced four-term `(1+X^{n/4})(1-X^{n/2})` has
`|Res(Φ_n, ·)| = 2^{3φ(n)/2} = 8^{φ(n)/2}` exactly, meeting the bound (`match=True` all `a`).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Complex Finset Polynomial

set_option linter.style.longLine false

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The balanced extremal four-term factors.**  For `n = 2^m`, the balanced four-term
`X^0 + X^{n/4} - X^{n/2} - X^{3n/4}` equals `(X^{n/4} + 1)·(1 - X^{n/2})` over `ℤ[X]`.
(Holds for `m ≥ 2` so that `n/4`, `n/2`, `3n/4` are the intended exponents `n/4`, `n/2`, `n/4+n/2`.) -/
theorem fourTerm_balanced_factor {m : ℕ} (hm : 2 ≤ m) :
    fourTerm 0 (2 ^ m / 4) (2 ^ m / 2) (3 * 2 ^ m / 4)
      = (X ^ (2 ^ m / 4) + 1) * (1 - X ^ (2 ^ m / 2)) := by
  -- normalize the exponents: n = 2^m, n/4 = 2^(m-2), n/2 = 2^(m-1), 3n/4 = 2^(m-2)+2^(m-1)
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e4 : 2 ^ (k + 2) / 4 = 2 ^ k := by
    rw [pow_add]; omega
  have e2 : 2 ^ (k + 2) / 2 = 2 ^ (k + 1) := by
    rw [pow_succ, pow_succ]; omega
  have e34 : 3 * 2 ^ (k + 2) / 4 = 2 ^ k + 2 ^ (k + 1) := by
    rw [pow_add, pow_succ]; ring_nf; omega
  rw [fourTerm, e4, e2, e34, pow_zero, pow_add]
  ring

/-- **The half-power is `-1` at a primitive `2^m`-th root** (`m ≥ 1`).  For `ζ` a primitive
`2^m`-th root, `ζ^{2^{m-1}}` is a primitive square root of unity, hence `= -1`. -/
theorem pow_half_eq_neg_one {m : ℕ} (hm : 1 ≤ m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    ζ ^ (2 ^ m / 2) = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e2 : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; omega
  rw [e2]
  have hprod : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
  have hp2 : IsPrimitiveRoot (ζ ^ (2 ^ k)) 2 :=
    hζ.pow (by positivity) hprod
  exact hp2.eq_neg_one_of_two_right

/-- **The quarter-power squares to `-1` at a primitive `2^m`-th root** (`m ≥ 2`).  For `ζ` a
primitive `2^m`-th root, `ζ^{2^{m-2}}` is a primitive *fourth* root, so its square is `-1`. -/
theorem pow_quarter_sq_eq_neg_one {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) : (ζ ^ (2 ^ m / 4)) ^ 2 = -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e4 : 2 ^ (k + 2) / 4 = 2 ^ k := by rw [pow_add]; omega
  rw [e4, ← pow_mul]
  -- (ζ^{2^k})^2 = ζ^{2^{k+1}} = ζ^{n/2}, which is -1
  have hmul : 2 ^ k * 2 = 2 ^ (k + 2) / 2 := by
    rw [pow_succ, pow_add]; omega
  rw [hmul]
  exact pow_half_eq_neg_one (by omega) hζ

/-- **The extremal four-term has constant squared modulus `8` at every primitive root** (`m ≥ 2`).
This is the equality case of the AM-GM behind `abs_resultant_fourTerm_sq_le`: at a primitive
`2^m`-th root, `1 - ζ^{n/2} = 2` (since `ζ^{n/2} = -1`) and `‖1 + ζ^{n/4}‖² = 2` (since
`(ζ^{n/4})² = -1`), so `‖f(ζ)‖² = ‖2‖² · ‖1 + ζ^{n/4}‖² = 4 · 2 = 8` — **uniform** across all
primitive roots, so AM-GM is lossless. -/
theorem normSq_eval_balanced_eq_eight {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    ‖(fourTerm 0 (2 ^ m / 4) (2 ^ m / 2) (3 * 2 ^ m / 4)).eval₂ (algebraMap ℤ ℂ) ζ‖ ^ 2 = 8 := by
  -- evaluate via the factorization
  have hfac := fourTerm_balanced_factor hm
  have hhalf := pow_half_eq_neg_one (show 1 ≤ m by omega) hζ
  have hq := pow_quarter_sq_eq_neg_one hm hζ
  -- eval₂ of the factored form
  have heval : (fourTerm 0 (2 ^ m / 4) (2 ^ m / 2) (3 * 2 ^ m / 4)).eval₂ (algebraMap ℤ ℂ) ζ
      = (ζ ^ (2 ^ m / 4) + 1) * (1 - ζ ^ (2 ^ m / 2)) := by
    rw [hfac]
    simp [eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_X]
  rw [heval, hhalf]
  -- 1 - (-1) = 2
  have h2 : (1 : ℂ) - (-1) = 2 := by ring
  rw [h2]
  set w : ℂ := ζ ^ (2 ^ m / 4) with hw
  -- From w² = -1: extract the real/imaginary equations.
  have hwsq : w * w = -1 := by rw [← pow_two]; exact hq
  have hre_eq : w.re * w.re - w.im * w.im = -1 := by
    have := congrArg Complex.re hwsq
    simpa [Complex.mul_re] using this
  have him_eq : w.re * w.im + w.im * w.re = 0 := by
    have := congrArg Complex.im hwsq
    simpa [Complex.mul_im] using this
  -- bridge ‖z‖² = normSq z = z.re*z.re + z.im*z.im
  have hns : ∀ z : ℂ, ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  -- ‖w‖² = 1
  have hnorm_w : w.re * w.re + w.im * w.im = 1 := by
    have h1 : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := hns w
    have h2w : ‖w ^ 2‖ = 1 := by rw [hq]; simp
    rw [norm_pow] at h2w
    nlinarith [norm_nonneg w, h1, h2w]
  -- Re w = 0
  have hre0 : w.re = 0 := by nlinarith [hre_eq, hnorm_w, him_eq]
  -- ‖w + 1‖² = 2
  have hw1sq : ‖w + 1‖ ^ 2 = 2 := by
    have h1 : ‖w + 1‖ ^ 2 = (w + 1).re * (w + 1).re + (w + 1).im * (w + 1).im := hns (w + 1)
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero] at h1
    rw [h1, hre0]; nlinarith [hnorm_w, hre0]
  -- assemble ‖(w+1)*2‖² = ‖w+1‖² * ‖2‖² = 2 * 4 = 8
  rw [norm_mul, mul_pow, hw1sq]
  have hn2 : ‖(2 : ℂ)‖ ^ 2 = 4 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real]; norm_num
  rw [hn2]; ring

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.fourTerm_balanced_factor
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.normSq_eval_balanced_eq_eight
