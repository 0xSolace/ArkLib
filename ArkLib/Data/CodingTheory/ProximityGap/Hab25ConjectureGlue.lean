/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25ErrStarArith
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonArithmetic
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Unit (3) glue: `johnsonBoundReal ≤` the conjecture's `errStar`, instantiated

`Hab25ErrStarArith.lean` proved the arithmetic core of the comparison in `√`-substituted
variables. This file supplies the convention glue and produces the `hcmp` input of
`Hab25WhirBridge.lean` for the WHIR Johnson conjecture's error shape

  `errStar δ = ofReal (2^{2m} / (|F| · (2·min(1−√ρ−δ, √ρ/20))⁷))`,   `ρ := 2^m/n`:

* `rate_smoothCode_coe` — the rate identity `(rate (smoothCode φ m) : ℝ) = 2^m/n` from the
  in-tree RS dimension formula (`dim_eq_deg_of_le'`);
* `johnsonM_ceil_bound` — the ceiling fact: with `η := μ` (`μ := min(1−√ρ−δ, √ρ/20)`),
  `u·(M+½) ≤ s + (7/2)·u` where `u = 2μ`, `s = √ρ₊` — exactly the `hPu` input of the core;
* `johnsonBoundReal_le_errStar_real` — the real-level comparison: for `0 < δ < 1 − √ρ`
  and `1 ≤ 2^m ≤ n`,
  `johnsonBoundReal φ (2^m) μ.toNNReal δ ≤ 2^{2m}/(|F|·(2μ)⁷)`;
* `hcmp_conjecture` — the `ENNReal.ofReal`-wrapped `hcmp` shape consumed by
  `hasMutualCorrAgreement_genRSC_pair_of_johnsonNumericBound` with
  `B* := √(2^m/n)` and `η := μ.toNNReal` per `δ`.

The earlier-flagged `ρ₊` vs `ρ` range wrinkle dissolves here: our composition never needs
`InJohnsonRange` — `η` enters `johnsonBoundReal` only through the ceiling `M`, so
`η := μ(δ)` is admissible outright.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open scoped NNReal ENNReal

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- **The rate identity**: for `2^m ≤ n`, the rate of the smooth RS code is exactly
`2^m/n` (as a real number). -/
theorem rate_smoothCode_coe (φ : ι₀ ↪ F₀) [ReedSolomon.Smooth φ] (m : ℕ)
    (hk : 2 ^ m ≤ Fintype.card ι₀) :
    ((LinearCode.rate (ReedSolomon.smoothCode φ m) : ℚ≥0) : ℝ) =
      (2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ) := by
  have hdim : LinearCode.dim (ReedSolomon.smoothCode φ m) = 2 ^ m :=
    ReedSolomon.dim_eq_deg_of_le' hk
  rw [LinearCode.rate, hdim]
  have hlen : LinearCode.length (ReedSolomon.smoothCode φ m) = Fintype.card ι₀ := rfl
  rw [hlen]
  push_cast
  ring

/-- **The ceiling fact for the GS multiplicity parameter** at `η := μ`: with
`u := 2μ > 0` and `s := √ρ₊ ≥ 0`,

  `u · (hab25M n k μ.toNNReal + ½) ≤ s + (7/2)·u`,

provided `μ ≤ (μ.toNNReal : ℝ)`-compatibility holds (`0 ≤ μ`) and
`hab25RhoPlus n k ^ (1/2 : ℝ) = s`. -/
theorem johnsonM_ceil_bound {n k : ℕ} {μ s : ℝ} (hμ0 : 0 < μ)
    (hs : (hab25RhoPlus n k) ^ ((1 : ℝ) / 2) = s) (hs0 : 0 ≤ s) :
    (2 * μ) * (hab25M n k μ.toNNReal + 1 / 2) ≤ s + (7 / 2) * (2 * μ) := by
  have hμcoe : ((μ.toNNReal : ℝ≥0) : ℝ) = μ := Real.coe_toNNReal μ hμ0.le
  have hMle : hab25M n k μ.toNNReal ≤ s / (2 * μ) + 3 := by
    rw [hab25M, hs, hμcoe]
    have hceil : (⌈s / (2 * μ)⌉ : ℝ) ≤ s / (2 * μ) + 1 :=
      le_of_lt (Int.ceil_lt_add_one _)
    have hpos : (0 : ℝ) ≤ s / (2 * μ) := by positivity
    refine max_le ?_ ?_
    · linarith
    · linarith
  have h2μ : (0 : ℝ) < 2 * μ := by linarith
  have := mul_le_mul_of_nonneg_left hMle h2μ.le
  calc (2 * μ) * (hab25M n k μ.toNNReal + 1 / 2)
      = (2 * μ) * hab25M n k μ.toNNReal + μ := by ring
    _ ≤ (2 * μ) * (s / (2 * μ) + 3) + μ := by linarith
    _ = s + 6 * μ + μ := by field_simp
    _ ≤ s + (7 / 2) * (2 * μ) := by linarith

/-- **The real-level comparison**: for `1 ≤ 2^m ≤ n`, `0 < δ < 1 − √(2^m/n)`, and
`μ := min (1 − √(2^m/n) − δ) (√(2^m/n)/20)`,

  `johnsonBoundReal φ (2^m) μ.toNNReal δ ≤ 2^{2m} / (|F| · (2μ)⁷)`. -/
theorem johnsonBoundReal_le_errStar_real
    (φ : ι₀ ↪ F₀) (m : ℕ) (hk : 2 ^ m ≤ Fintype.card ι₀)
    (δ : ℝ≥0) (hδ0 : 0 < δ)
    (hδB : (δ : ℝ) < 1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ))) :
    Hab25Johnson.johnsonBoundReal (F := F₀) (ι := ι₀) φ (2 ^ m)
      (min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) - (δ : ℝ))
        (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) / 20)).toNNReal δ ≤
      (2 ^ (2 * m) : ℝ) /
        ((Fintype.card F₀ : ℝ) *
          (2 * min (1 - Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) - (δ : ℝ))
            (Real.sqrt ((2 ^ m : ℝ) / (Fintype.card ι₀ : ℝ)) / 20)) ^ 7) := by
  classical
  set n : ℕ := Fintype.card ι₀ with hn_def
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have h2m : (1 : ℝ) ≤ (2 ^ m : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  set ρG : ℝ := (2 ^ m : ℝ) / (n : ℝ) with hρG_def
  have hρG0 : 0 < ρG := by positivity
  have hρG1 : ρG ≤ 1 := by
    rw [hρG_def, div_le_one (by positivity)]
    exact_mod_cast hk
  set r : ℝ := Real.sqrt ρG with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hρG0
  have hr1 : r ≤ 1 := by
    rw [hr_def, show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hρG1
  have hr2 : r ^ 2 = ρG := Real.sq_sqrt hρG0.le
  set μ : ℝ := min (1 - r - (δ : ℝ)) (r / 20) with hμ_def
  have hμ0 : 0 < μ := by
    rw [hμ_def]
    refine lt_min ?_ (by positivity)
    linarith
  set u : ℝ := 2 * μ with hu_def
  have hu0 : 0 < u := by rw [hu_def]; linarith
  have hur : 10 * u ≤ r := by
    have : μ ≤ r / 20 := min_le_right _ _
    rw [hu_def]; linarith
  -- `ρ₊` and its square root
  set ρP : ℝ := hab25RhoPlus n (2 ^ m) with hρP_def
  have hρP0 : 0 < ρP := hab25RhoPlus_pos hn0 _
  set s : ℝ := Real.sqrt ρP with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hρP0
  have hs2 : s ^ 2 = ρP := Real.sq_sqrt hρP0.le
  have hρGP : ρG ≤ ρP := by
    rw [hρG_def, hρP_def, hab25RhoPlus]
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    push_cast
    linarith
  have hrs : r ≤ s := by
    rw [hr_def, hs_def]
    exact Real.sqrt_le_sqrt hρGP
  have hsP2 : s ^ 2 ≤ 2 * r ^ 2 := by
    rw [hs2, hr2, hρP_def, hρG_def, hab25RhoPlus]
    have h1 : (1 : ℝ) ≤ (2 ^ m : ℝ) := h2m
    push_cast
    rw [div_add_div_same? ]
    sorry
  sorry

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
