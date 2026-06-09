/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional `errStar` envelope: BCHKS25 T4.6 ≤ §4.5 conjecture `errStar`

**Goal.** The unconditional comparison "the BCHKS25 Theorem 4.6 RS multiplicity-coded
Johnson-range MCA bound is ≤ the ABF26 §4.5 conjecture's `errStar`" is *false*
(numerical counterexample at `η = 0.001` and large `n`, where the multiplicity `m`
pins to its floor `3` while the BCHKS bound carries an explicit `n` factor that the
conjecture bound lacks). This file isolates and proves the **η-conditional** version.

Let `ρ₊ := k/n + 1/n`, `s := √ρ₊`, and `m := max(⌈√ρ₊/(2η)⌉, 3)` (multiplicity).

* **BCHKS25 T4.6 bound** (`bchksBound`, the value inside `ENNReal.ofReal (…/q)` of
  `rs_epsMCA_johnson_range_bchks25` in `CapacityBounds.lean`, with the `1/q` factored out):

  `B := ( 2·(m+½)⁵ + 3·(m+½)·δ·ρ₊ ) / ( 3·ρ₊^{3/2} ) · n  +  (m+½)/√ρ₊`

* **§4.5 conjecture `errStar`** (`errStarNum`, the numerator of `errStarA` in
  `MCAJohnsonErrStarBounds.lean`, again with the `1/q` factored out):

  `E := (parℓ − 1)·2^{2m} / ( 2·min(1 − √ρ₊ − δ, √ρ₊/20) )⁷`

**The explicit side condition.** The load-bearing hypothesis is the *multiplicity
domination* inequality

  `26 · (m:ℝ)⁵ · n ≤ 2^{2m}`,                                        (COND)

which forces the conjecture's `2^{2m}` numerator to dominate the BCHKS `n` factor.
Because `m = max(⌈√ρ₊/(2η)⌉, 3) ≥ √ρ₊/(2η)`, (COND) is *implied by η being small
enough* — concretely `η ≤ √ρ₊ / (2·M)` forces `m ≥ M`, and `M` chosen so that
`26·M⁵·n ≤ 2^{2M}` (always possible since `2^{2M}` is eventually super-polynomial in
`M`). This is the opposite direction from a *large*-η pinning of `m`: the conditional
holds precisely when η is small enough to make the multiplicity large, which is exactly
why the η = 0.001 counterexample to the *unconditional* claim only bites once `n` is
allowed to grow with `m` floored. We expose (COND) directly as the explicit condition,
and prove the envelope `B ≤ E` from it (plus the standard regime hypotheses).

Everything below is Mathlib-only real arithmetic; no `sorry`/`admit`/`native_decide`.
-/

open Real

namespace ConditionalErrStarEnvelope

/-- The BCHKS25 T4.6 bound value (with the `1/q` factor removed), as a real number,
in terms of the half-shifted multiplicity `mh = m + ½`, the block length `n`, the
agreement gap `δ`, and `s = √ρ₊`. Matches the body of
`rs_epsMCA_johnson_range_bchks25` once `ρ₊ = s²`, `ρ₊^{3/2} = s³`, `√ρ₊ = s`. -/
noncomputable def bchksBound (mh n δ s : ℝ) : ℝ :=
  (2 * mh ^ 5 + 3 * mh * δ * s ^ 2) / (3 * s ^ 3) * n + mh / s

/-- The §4.5 conjecture `errStar` value (with the `1/q` factor removed), as a real number.
`K = 2^{2m}`, `parℓ` is the interleaving count, and the denominator uses the genuine
`min(1 − s − δ, s/20)` from `errStarA`. -/
noncomputable def errStarNum (K parl s δ : ℝ) : ℝ :=
  K * (parl - 1) / (2 * min (1 - s - δ) (s / 20)) ^ 7

/-- **Core polynomial domination.** With multiplicity `m ≥ 3` and `n ≥ 1`, the BCHKS
numerator polynomial in `mh = m + ½` is dominated by `26·m⁵·n`. This is where the
`(m+½)⁵` quintic of the BCHKS multiplicity-coded list-decoder analysis is absorbed into
a clean monomial with explicit slack. -/
lemma bchks_poly_le (m n : ℝ) (hm : 3 ≤ m) (hn : 1 ≤ n) :
    (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2)) / 3 * n + (m + 1 / 2) ≤ 26 * m ^ 5 * n := by
  have hm0 : 0 < m := by linarith
  have hmh : m + 1 / 2 ≤ 2 * m := by linarith
  have h5 : (m + 1 / 2) ^ 5 ≤ 32 * m ^ 5 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ m + 1 / 2) hmh 5
    nlinarith [h]
  have hmpow : m ≤ m ^ 5 := by
    nlinarith [pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ m) (by norm_num : 1 ≤ 5)]
  have hm5_1 : (1 : ℝ) ≤ m ^ 5 := le_trans (by linarith) hmpow
  have hm5pos : 0 < m ^ 5 := by linarith
  have h3mh : 3 * (m + 1 / 2) ≤ 5 * m ^ 5 := by nlinarith [hmpow, hm5_1]
  have hnum : (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2)) / 3 ≤ 23 * m ^ 5 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [h5, h3mh]
  have hlast : (m + 1 / 2) ≤ 2 * m ^ 5 * n := by
    have : (m + 1 / 2) ≤ 2 * m ^ 5 := by nlinarith [hmpow]
    nlinarith [this, hm5pos, hn]
  have hpartn : (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2)) / 3 * n ≤ 23 * m ^ 5 * n :=
    mul_le_mul_of_nonneg_right hnum (by linarith)
  nlinarith [hpartn, hlast]

/-- **Cleared-denominator inequality.** After multiplying the envelope `B ≤ E` through by
the common positive denominator `3·s⁷`, the comparison becomes a pure polynomial
inequality. Here `s < 1` (true on the Johnson range, since `δ < 1 − s` and `s = √ρ₊` with
`ρ₊ < 1`) lets us absorb the powers of `s`; (COND), restated as `26·m⁵·n ≤ K`, closes it
with constant slack `7 ≤ 3·10⁷`. -/
lemma cleared_ineq (m n s δ parl K : ℝ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 - s) (hparl : 1 ≤ parl - 1)
    (hKpos : 0 < K) (hcond : 26 * m ^ 5 * n ≤ K) :
    (2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * s ^ 2) * n * s ^ 4
        + 3 * (m + 1 / 2) * s ^ 6
      ≤ 3 * K * (parl - 1) * 10 ^ 7 := by
  have hpoly := bchks_poly_le m n hm hn
  set mh := m + 1 / 2 with hmh_def
  have hmh0 : 0 ≤ mh := by rw [hmh_def]; linarith
  have hmh5 : 0 ≤ mh ^ 5 := by positivity
  have hsle1 : s ≤ 1 := le_of_lt hs1
  have hs2_1 : s ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hs0) hsle1
  have hs4_1 : s ^ 4 ≤ 1 := pow_le_one₀ (le_of_lt hs0) hsle1
  have hs6_1 : s ^ 6 ≤ 1 := pow_le_one₀ (le_of_lt hs0) hsle1
  have hs2_0 : 0 ≤ s ^ 2 := by positivity
  have hs6_0 : 0 ≤ s ^ 6 := by positivity
  have hδ1 : δ ≤ 1 := by linarith
  have hδs2 : δ * s ^ 2 ≤ 1 := by
    calc δ * s ^ 2 ≤ 1 * 1 := by apply mul_le_mul hδ1 hs2_1 hs2_0 (by norm_num)
      _ = 1 := by ring
  have hA : 2 * mh ^ 5 + 3 * mh * δ * s ^ 2 ≤ 2 * mh ^ 5 + 3 * mh := by nlinarith [hmh0, hδs2]
  have hA0 : 0 ≤ 2 * mh ^ 5 + 3 * mh * δ * s ^ 2 := by positivity
  have hAns : (2 * mh ^ 5 + 3 * mh * δ * s ^ 2) * n * s ^ 4 ≤ (2 * mh ^ 5 + 3 * mh) * n := by
    have h1 : (2 * mh ^ 5 + 3 * mh * δ * s ^ 2) * n * s ^ 4
        ≤ (2 * mh ^ 5 + 3 * mh * δ * s ^ 2) * n * 1 := by
      apply mul_le_mul_of_nonneg_left hs4_1; positivity
    have h2 : (2 * mh ^ 5 + 3 * mh * δ * s ^ 2) * n ≤ (2 * mh ^ 5 + 3 * mh) * n :=
      mul_le_mul_of_nonneg_right hA (by linarith)
    nlinarith [h1, h2]
  have hmhs6 : 3 * mh * s ^ 6 ≤ 3 * mh := by nlinarith [hmh0, hs6_1, hs6_0]
  have hsum : (2 * mh ^ 5 + 3 * mh) * n + 3 * mh
      = 3 * ((2 * mh ^ 5 + 3 * mh) / 3 * n + mh) := by ring
  have hpoly3 : (2 * mh ^ 5 + 3 * mh) * n + 3 * mh ≤ 3 * (26 * m ^ 5 * n) := by
    rw [hsum]; nlinarith [hpoly]
  have hKchain : 3 * (26 * m ^ 5 * n) ≤ 3 * K * (parl - 1) * 10 ^ 7 := by
    have hKp : K ≤ K * (parl - 1) := by nlinarith [hparl, hKpos]
    have hKp2 : K * (parl - 1) ≤ K * (parl - 1) * 10 ^ 7 := by nlinarith [hparl, hKpos]
    nlinarith [hcond, hKp, hKp2]
  nlinarith [hAns, hmhs6, hpoly3, hKchain]

/-- BCHKS bound expressed over the common denominator `3·s⁷`. -/
lemma bchks_over_common (mh n δ s : ℝ) (hs : s ≠ 0) :
    bchksBound mh n δ s
      = ((2 * mh ^ 5 + 3 * mh * δ * s ^ 2) * n * s ^ 4 + 3 * mh * s ^ 6) / (3 * s ^ 7) := by
  unfold bchksBound
  field_simp

/-- Worst-case (`min_val = s/20`) `errStar` numerator over the common denominator `3·s⁷`. -/
lemma errStar_worst_over_common (K parl s : ℝ) (hs : s ≠ 0) :
    K * (parl - 1) / (s / 10) ^ 7 = (3 * K * (parl - 1) * 10 ^ 7) / (3 * s ^ 7) := by
  field_simp

/-- The genuine `errStar` numerator (with the real `min(1 − s − δ, s/20)`) is bounded
*below* by its worst case, in which the agreement radius equals the cap `s/20`. This is
the only place the `min` is touched: `min_val ≤ s/20` makes the worst-case denominator
the largest, hence the smallest `errStar`. -/
lemma errStar_worst_le (K parl s δ : ℝ) (hKp : 0 ≤ K * (parl - 1))
    (hs0 : 0 < s) (hδ : δ < 1 - s) :
    K * (parl - 1) / (s / 10) ^ 7 ≤ errStarNum K parl s δ := by
  unfold errStarNum
  have hmv_pos : 0 < min (1 - s - δ) (s / 20) := by
    apply lt_min
    · linarith
    · positivity
  have hmv_le : min (1 - s - δ) (s / 20) ≤ s / 20 := min_le_right _ _
  have hden_small : 0 < (2 * min (1 - s - δ) (s / 20)) ^ 7 := by positivity
  have hs10 : (s / 10) ^ 7 = (2 * (s / 20)) ^ 7 := by ring_nf
  have hle : (2 * min (1 - s - δ) (s / 20)) ^ 7 ≤ (s / 10) ^ 7 := by
    rw [hs10]
    exact pow_le_pow_left₀ (by positivity) (by linarith [hmv_le]) 7
  exact div_le_div_of_nonneg_left hKp hden_small hle

/-- **Conditional `errStar` envelope (main result).**

For `m ≥ 3`, `n ≥ 1`, `s = √ρ₊ ∈ (0,1)`, gap `δ ∈ [0, 1 − s)`, interleaving count
`parℓ ≥ 2` (i.e. `parℓ − 1 ≥ 1`), conjecture numerator `K = 2^{2m} > 0`, under the
explicit multiplicity-domination side condition

  `26 · m⁵ · n ≤ K`,                                                   (COND)

the BCHKS25 T4.6 bound is dominated by the §4.5 conjecture `errStar`:

  `bchksBound (m+½) n δ s  ≤  errStarNum K parℓ s δ`.

Since both `rs_epsMCA_johnson_range_bchks25` and `errStarA` carry the identical `1/q`
prefactor, the same inequality holds for the full `(1/q)·(…)` bounds; the BCHKS bound
therefore *witnesses* the conjecture bound on this conditional range. -/
theorem conditional_errStar_envelope
    (m n s δ parl K : ℝ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 - s)
    (hparl : 1 ≤ parl - 1) (hKpos : 0 < K) (hcond : 26 * m ^ 5 * n ≤ K) :
    bchksBound (m + 1 / 2) n δ s ≤ errStarNum K parl s δ := by
  have hsne : s ≠ 0 := ne_of_gt hs0
  -- Cleared-denominator polynomial inequality (the analytic content).
  have hcleared := cleared_ineq m n s δ parl K hm hn hs0 hs1 hδ0 hδ hparl hKpos hcond
  -- Both sides over the common denominator `3·s⁷ > 0`.
  have hden : (0 : ℝ) < 3 * s ^ 7 := by positivity
  -- Divide the cleared inequality by `3·s⁷`: `a ≤ b → a/c ≤ b/c`.
  have hdiv :
      ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * s ^ 2) * n * s ^ 4
          + 3 * (m + 1 / 2) * s ^ 6) / (3 * s ^ 7)
        ≤ (3 * K * (parl - 1) * 10 ^ 7) / (3 * s ^ 7) :=
    div_le_div_of_nonneg_right hcleared (le_of_lt hden)
  -- Rewrite the two sides back to `bchksBound` and worst-case `errStarNum`.
  rw [bchks_over_common (m + 1 / 2) n δ s hsne]
  rw [← errStar_worst_over_common K parl s hsne] at hdiv
  -- The worst case lower-bounds the genuine `errStarNum`.
  have hKp : 0 ≤ K * (parl - 1) := mul_nonneg (le_of_lt hKpos) (by linarith)
  exact le_trans hdiv (errStar_worst_le K parl s δ hKp hs0 hδ)

/-- Version of `conditional_errStar_envelope` with the common field-size denominator restored.
Both the BCHKS25 T4.6 bound and the conjectural ABF26 §4.5 `errStar` carry the same `1/q`
factor; this corollary is the directly reusable real inequality for later `ENNReal.ofReal`
packaging. -/
theorem conditional_errStar_envelope_with_q
    (m n s δ parl K q : ℝ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 - s)
    (hparl : 1 ≤ parl - 1) (hKpos : 0 < K) (hcond : 26 * m ^ 5 * n ≤ K)
    (hq : 0 < q) :
    bchksBound (m + 1 / 2) n δ s / q ≤ errStarNum K parl s δ / q :=
  div_le_div_of_nonneg_right
    (conditional_errStar_envelope m n s δ parl K hm hn hs0 hs1 hδ0 hδ hparl hKpos hcond)
    (le_of_lt hq)

/-! ## Tying the side condition to an explicit bound on η

In `rs_epsMCA_johnson_range_bchks25` the multiplicity is `m = max(⌈√ρ₊/(2η)⌉, 3)`.
The two lemmas below make precise the sense in which (COND) is an **η-conditional**:
the multiplicity is an antitone function of η, so *small* η forces *large* m, and a
sufficiently large m makes (COND) hold (because `2^{2m}` outgrows `26·m⁵·n`). This is the
direction opposite to the failed unconditional claim, and exactly explains the
`η = 0.001` numerical counterexample: there the *unconditional* statement quantifies over
all `n`, and once `n` is large while `m` is read off as a fixed value the BCHKS `n` factor
wins; the conditional pins down precisely the `m`-vs-`n` budget that must hold. -/

/-- The realized multiplicity `m = max(⌈√ρ₊/(2η)⌉, 3)` always dominates the raw ratio
`√ρ₊/(2η)`. -/
lemma multiplicity_ge_ratio (s η : ℝ) :
    s / (2 * η) ≤ (max ⌈s / (2 * η)⌉ 3 : ℝ) :=
  le_trans (Int.le_ceil _) (by exact_mod_cast le_max_left ⌈s / (2 * η)⌉ (3 : ℤ))

/-- **η forces the multiplicity up.** If `η ≤ √ρ₊/(2M)` for a target `M ≥ 1` (and
`√ρ₊ > 0`, `η > 0`), then the realized multiplicity satisfies `m ≥ M`. Hence choosing
the target `M` large enough that `26·M⁵·n ≤ 2^{2M}` — always possible, since the right
side is super-polynomial in `M` — and taking `η ≤ √ρ₊/(2M)`, the side condition (COND)
holds for the realized multiplicity once one also has the monotonicity `26·m⁵·n ≤ 2^{2m}`
inherited from `m ≥ M`. -/
lemma multiplicity_ge_target (s η : ℝ) (M : ℤ)
    (hη : 0 < η) (_hs : 0 < s) (hM : (1 : ℝ) ≤ M) (hbound : η ≤ s / (2 * M)) :
    (M : ℝ) ≤ (max ⌈s / (2 * η)⌉ 3 : ℝ) := by
  have h2M : (0 : ℝ) < 2 * M := by linarith
  have hstep : (M : ℝ) ≤ s / (2 * η) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * η)]
    have hsη : η * (2 * M) ≤ s := by rw [le_div_iff₀ h2M] at hbound; linarith [hbound]
    nlinarith [hsη]
  exact le_trans (le_trans hstep (Int.le_ceil _))
    (by exact_mod_cast le_max_left ⌈s / (2 * η)⌉ (3 : ℤ))

/-- **η-phrased conditional envelope.** Packaging the main theorem with the η-link: if the
realized multiplicity (a real `m`) is at least `3`, and the explicit side condition (COND)
holds, then the BCHKS25 T4.6 bound is ≤ the conjecture `errStar`. The η-link lemmas above
exhibit (COND) as a small-η condition: pick a target `M` with `26·M⁵·n ≤ 2^{2M}`, force
`η ≤ √ρ₊/(2M)` (so `m ≥ M`), which supplies (COND). -/
theorem conditional_errStar_envelope_of_cond
    (m n s δ parl : ℝ) (mexp : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 - s)
    (hparl : 1 ≤ parl - 1) (hcond : 26 * m ^ 5 * n ≤ 2 ^ (2 * mexp)) :
    bchksBound (m + 1 / 2) n δ s ≤ errStarNum (2 ^ (2 * mexp)) parl s δ :=
  conditional_errStar_envelope m n s δ parl (2 ^ (2 * mexp)) hm hn hs0 hs1 hδ0 hδ hparl
    (by positivity) hcond

/-! ## Discharging the side condition: the envelope is unconditional for large multiplicity

The side condition `(COND): 26·m⁵·n ≤ K = 2^{2m}` is a *polynomial ≤ exponential* statement, so it
holds automatically once the multiplicity `m` is large relative to the block length `n`. The lemmas
below prove this for `m ≥ 31`, `n ≤ 2^m`, removing the side condition entirely in that regime. -/

/-- **Step lemma.** `(k+1)^5 ≤ 2·k^5` for `k ≥ 31`: the quintic grows slowly enough that doubling
`k^5` dominates a unit increment of `k`. The threshold `31` comes from
`5k⁴+10k³+10k²+5k+1 ≤ 31k⁴ ≤ k·k⁴ = k⁵`. -/
lemma succ_pow_five_le (k : ℕ) (hk : 31 ≤ k) : (k + 1) ^ 5 ≤ 2 * k ^ 5 := by
  have hk1 : 1 ≤ k := by omega
  have a3 : k ^ 3 ≤ k ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
  have a2 : k ^ 2 ≤ k ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
  have a1 : k ≤ k ^ 4 := by
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
  have a0 : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hsum : 5 * k ^ 4 + 10 * k ^ 3 + 10 * k ^ 2 + 5 * k + 1 ≤ 31 * k ^ 4 := by linarith
  have h31 : 31 * k ^ 4 ≤ k ^ 5 := by
    calc 31 * k ^ 4 ≤ k * k ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = k ^ 5 := by ring
  have key : 5 * k ^ 4 + 10 * k ^ 3 + 10 * k ^ 2 + 5 * k + 1 ≤ k ^ 5 := le_trans hsum h31
  have e : (k + 1) ^ 5 = k ^ 5 + (5 * k ^ 4 + 10 * k ^ 3 + 10 * k ^ 2 + 5 * k + 1) := by ring
  rw [e, two_mul]
  exact Nat.add_le_add_left key _

/-- **Polynomial ≪ exponential threshold.** `26·m⁵ ≤ 2^m` for every `m ≥ 31`. Induction from the
base `26·31⁵ = 744357926 ≤ 2147483648 = 2³¹` via `succ_pow_five_le`. -/
theorem poly_le_two_pow (m : ℕ) (hm : 31 ≤ m) : 26 * m ^ 5 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 26 * (k + 1) ^ 5 ≤ 26 * (2 * k ^ 5) := Nat.mul_le_mul_left _ (succ_pow_five_le k hk)
      _ = 2 * (26 * k ^ 5) := by ring
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- **The multiplicity-domination side condition `(COND)` holds unconditionally for `m ≥ 31`,
`n ≤ 2^m`.** I.e. `26·m⁵·n ≤ 2^{2m}` (`= K`, the ABF26 §4.5 conjecture numerator). The exponential
`K = 2^{2m} = 2^m · 2^m` absorbs both the polynomial multiplicity factor `26·m⁵ ≤ 2^m` and the
block length `n ≤ 2^m`. -/
theorem cond_holds_large_mult (m n : ℕ) (hm : 31 ≤ m) (hnle : n ≤ 2 ^ m) :
    26 * (m : ℝ) ^ 5 * (n : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
  have ht : 26 * m ^ 5 ≤ 2 ^ m := poly_le_two_pow m hm
  have h1 : 26 * m ^ 5 * n ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul ht hnle
  have h2 : (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
  rw [h2] at h1
  calc 26 * (m : ℝ) ^ 5 * (n : ℝ) = ((26 * m ^ 5 * n : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((2 ^ (2 * m) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (2 : ℝ) ^ (2 * m) := by push_cast; ring

/-- **Unconditional Johnson-range envelope (large multiplicity).** For multiplicity `m ≥ 31` and
block length `n ≤ 2^m`, on the Johnson range `s = √ρ₊ ∈ (0,1)`, gap `δ ∈ [0, 1−s)`, interleaving
`parℓ ≥ 2`, the BCHKS25 T4.6 Johnson-range MCA bound is *unconditionally* dominated by the ABF26
§4.5 conjectural `errStar` (with `K = 2^{2m}`):

  `bchksBound (m+½) n δ s  ≤  errStarNum (2^{2m}) parℓ s δ`.

This removes the `(COND)` hypothesis from `conditional_errStar_envelope` in the natural
`n ≤ 2^{multiplicity}` regime: the BCHKS bound provably *witnesses* the conjecture bound there. -/
theorem unconditional_errStar_envelope_large_mult
    (m n : ℕ) (s δ parl : ℝ) (hm : 31 ≤ m) (hn : 1 ≤ n) (hnle : n ≤ 2 ^ m)
    (hs0 : 0 < s) (hs1 : s < 1) (hδ0 : 0 ≤ δ) (hδ : δ < 1 - s) (hparl : 1 ≤ parl - 1) :
    bchksBound ((m : ℝ) + 1 / 2) (n : ℝ) δ s ≤ errStarNum ((2 : ℝ) ^ (2 * m)) parl s δ := by
  refine conditional_errStar_envelope (m : ℝ) (n : ℝ) s δ parl ((2 : ℝ) ^ (2 * m))
    (by exact_mod_cast (by omega : 3 ≤ m)) (by exact_mod_cast hn)
    hs0 hs1 hδ0 hδ hparl (by positivity) ?_
  exact cond_holds_large_mult m n hm hnle

end ConditionalErrStarEnvelope
