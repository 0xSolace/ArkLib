/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.ToMathlib.KoalaBearCode

/-!
# The concrete KoalaBear winning-set residual is an obstruction (`#106`)

The leaderboard axiom `ToyProblem.fenziSanso_upperBound_attack_concrete_residual` asks for a
**violating instance** of the genuine concrete KoalaBear-sextic carrier
(`KoalaBear.rsCodeSet`, the rate-`1/2` Reed–Solomon code over `Fin 4`) whose winning set has at
least `2^70` challenges.

This file proves a *structural upper bound* that makes that residual **unsatisfiable** at the
concrete carrier: the winning set of the simplified-IOR attack over this `[n = 4, k = 2]` code is
governed by a geometric dichotomy and, in the violating regime, is **tiny** (at most
`C(4,3) = 4` challenges) — never `2^70`.

## The geometry

The concrete code is the `[n = 4, k = 2]` Reed–Solomon code: codewords are evaluations
`j ↦ m₀ + m₁ · j` of affine polynomials at the four points `0,1,2,3 ∈ F_{p^6}`. Its minimum
distance is `n − k + 1 = 3`, so:

* **two points determine a codeword** (`rsEncoder_eq_of_two_points`): if two codewords agree at
  two *distinct* coordinates they are equal; and
* at `δ = 3/10` over `|ι| = 4`, the relaxed-relation agreement threshold is
  `⌈(1 − 3/10)·4⌉ = ⌈2.8⌉ = 3` coordinates.

A challenge `γ` is **winning** only if the line `f₁ + γ·f₂` agrees with *some* codeword on a
`3`-subset `T ⊆ Fin 4`. The codeword restrictions to a fixed `3`-subset `T` form a `2`-dimensional
subspace `V_T ⊆ F^T`; the affine line `{f₁|_T + γ·f₂|_T : γ}` is `1`-dimensional, so it meets
`V_T` in **at most one point** unless it lies entirely inside `V_T`. The contained case means
`f₁|_T` and `f₂|_T` are *both* codeword restrictions on the *same* `T` — exactly a common
agreement set realising the relaxed two-row relation `R̃²`, i.e. the instance is **not**
violating.

Hence, for a violating instance, each of the four `3`-subsets contributes at most one winning
challenge: `|Ω| ≤ 4 < 2^70`.

## What is proven here (axiom-clean)

* `KoalaBear.rsEncoder_eq_of_two_points` — the minimum-distance fact (a codeword is determined by
  its values at two distinct coordinates).
* `KoalaBear.two_winning_same_subset_imp_lineInCode` — the **geometric heart**: if two *distinct*
  challenges both put the line `f₁ + γ·f₂` onto codewords along a common `3`-subset `T`, then both
  `f₁|_T` and `f₂|_T` are codeword restrictions on `T` (the "line lies in `V_T`" conclusion).

These are the fully-formalised, kernel-checked core of the obstruction. The remaining wrapper —
turning "line in `V_T`" into a populated `relaxedRelation (ℓ := 2)` witness (hence contradicting
`x.violates`) and counting the four subsets to the `|Ω| ≤ 4` bound — additionally requires
reconstructing the existential constraint-encoding of `relation`, documented in
`ArkLib/ProofSystem/ToyProblem/Leaderboard.lean` and tracked on `#106`.

## References

* Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated Agreement*
  (eprint 2026/680), §6.3–§6.4.
-/

namespace KoalaBear

open scoped NNReal

/-- **Minimum-distance fact for the `[4,2]` RS code.** A codeword `rsEncoder m` is determined by
its values at any two *distinct* evaluation coordinates: if `rsEncoder m` and `rsEncoder m'` agree
at `j₁ ≠ j₂` (as `Fin 4`), then `m = m'`.

This is the statement that the code has minimum distance `> 2` (here `= 3`): the `2 × 2`
Vandermonde system `m₀ + m₁·jₐ = m'₀ + m'₁·jₐ` (`a = 1,2`) has only the trivial solution
`m = m'` because `rsPoint j₁ ≠ rsPoint j₂`. -/
theorem rsEncoder_eq_of_two_points {m m' : Fin 2 → Sextic} {j₁ j₂ : Fin 4}
    (hj : j₁ ≠ j₂)
    (h₁ : rsEncoder m j₁ = rsEncoder m' j₁)
    (h₂ : rsEncoder m j₂ = rsEncoder m' j₂) :
    m = m' := by
  -- Distinct evaluation points: `rsPoint j₁ ≠ rsPoint j₂`.
  have hpt : rsPoint j₁ ≠ rsPoint j₂ := by
    intro hpt
    -- `rsPoint j = (j.val : Sextic)`; distinct `Fin 4` values cast to distinct field elements
    -- because the characteristic exceeds `4`.
    apply hj
    -- Reduce to equality of the natural-number indices via injectivity of the cast on `{0,1,2,3}`.
    have hcast : ((j₁.val : ℕ) : Sextic) = ((j₂.val : ℕ) : Sextic) := by
      simpa [rsPoint] using hpt
    -- `j₁.val, j₂.val < 4 ≤ p`, so the casts are injective (`Fin` ext + `Nat.cast` injectivity).
    have hlt₁ : j₁.val < 4 := j₁.isLt
    have hlt₂ : j₂.val < 4 := j₂.isLt
    apply Fin.ext
    -- The characteristic of `Sextic = GaloisField fieldSize 6` is `fieldSize` (derived instance).
    have hfs : (4 : ℕ) ≤ KoalaBear.fieldSize := by
      have : KoalaBear.fieldSize = 2130706433 := KoalaBear.fieldSize_eq
      omega
    have hb₁ : j₁.val ∈ Set.Iio KoalaBear.fieldSize :=
      Set.mem_Iio.mpr (lt_of_lt_of_le hlt₁ hfs)
    have hb₂ : j₂.val ∈ Set.Iio KoalaBear.fieldSize :=
      Set.mem_Iio.mpr (lt_of_lt_of_le hlt₂ hfs)
    -- Small natural casts are injective below the characteristic.
    exact CharP.natCast_injOn_Iio (R := Sextic) KoalaBear.fieldSize hb₁ hb₂ hcast
  -- From the two agreements, derive `m 1 = m' 1`, then `m 0 = m' 0`.
  -- `rsEncoder m j = m 0 + m 1 * rsPoint j`.
  have e₁ : m 0 + m 1 * rsPoint j₁ = m' 0 + m' 1 * rsPoint j₁ := by
    simpa [rsEncoder] using h₁
  have e₂ : m 0 + m 1 * rsPoint j₂ = m' 0 + m' 1 * rsPoint j₂ := by
    simpa [rsEncoder] using h₂
  -- Subtract: `(m 1 - m' 1)·(rsPoint j₁ - rsPoint j₂) = 0`.
  have hsub : (m 1 - m' 1) * (rsPoint j₁ - rsPoint j₂) = 0 := by linear_combination e₁ - e₂
  have hne : rsPoint j₁ - rsPoint j₂ ≠ 0 := sub_ne_zero.mpr hpt
  have hm1 : m 1 = m' 1 := by
    have h0 : m 1 - m' 1 = 0 := (mul_eq_zero.mp hsub).resolve_right hne
    exact sub_eq_zero.mp h0
  -- Back-substitute into `e₁` to get `m 0 = m' 0`.
  have hm0 : m 0 = m' 0 := by
    have : m 0 + m 1 * rsPoint j₁ = m' 0 + m 1 * rsPoint j₁ := by
      rw [hm1] at e₁ ⊢; exact e₁
    exact add_right_cancel this
  funext i
  fin_cases i
  · exact hm0
  · exact hm1

/-- **The geometric heart of the `#106` obstruction (line-in-code).**

Suppose two *distinct* challenges `γ ≠ γ'` both make the line `f₁ + γ·f₂` land on a Reed–Solomon
codeword along a common coordinate set `T` (the winning agreement set): there are messages
`mc, mc'` with `rsEncoder mc` agreeing with `f₁ + γ·f₂` on `T` and `rsEncoder mc'` agreeing with
`f₁ + γ'·f₂` on `T`. Then *both* `f₁|_T` and `f₂|_T` are themselves codeword restrictions on `T`:
there are messages `a, b` with `rsEncoder a` agreeing with `f₁` on `T` and `rsEncoder b` agreeing
with `f₂` on `T`.

This is exactly "the affine line `{f₁|_T + γ·f₂|_T}` lies inside the codeword-restriction subspace
`V_T`". Two distinct winning challenges on a *common* `T` therefore force a *common* two-row
agreement set — the structural reason a **violating** instance can win on each `3`-subset at most
once, capping its winning set at `C(4,3) = 4 < 2^70`.

The proof is pure `F`-linearity of `rsEncoder` (no minimum-distance input needed): set
`b := (γ − γ')⁻¹ • (mc − mc')` and `a := mc − γ • b`. -/
theorem two_winning_same_subset_imp_lineInCode
    {f₁ f₂ : Fin 4 → Sextic} {γ γ' : Sextic} (hγ : γ ≠ γ') {T : Finset (Fin 4)}
    {mc mc' : Fin 2 → Sextic}
    (hc : ∀ j ∈ T, rsEncoder mc j = f₁ j + γ * f₂ j)
    (hc' : ∀ j ∈ T, rsEncoder mc' j = f₁ j + γ' * f₂ j) :
    ∃ a b : Fin 2 → Sextic,
      (∀ j ∈ T, rsEncoder a j = f₁ j) ∧ (∀ j ∈ T, rsEncoder b j = f₂ j) := by
  have hd : γ - γ' ≠ 0 := sub_ne_zero.mpr hγ
  -- `b := (γ - γ')⁻¹ • (mc - mc')`, `a := mc - γ • b`.
  refine ⟨mc - γ • ((γ - γ')⁻¹ • (mc - mc')), (γ - γ')⁻¹ • (mc - mc'), ?_, ?_⟩
  · intro j hj
    -- `rsEncoder a j = rsEncoder mc j - γ * rsEncoder b j = (f₁+γf₂) j - γ * f₂ j = f₁ j`.
    have hb : rsEncoder ((γ - γ')⁻¹ • (mc - mc')) j = f₂ j := by
      rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, hc j hj, hc' j hj]
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, hc j hj, hb]
    simp only [smul_eq_mul]
    ring
  · intro j hj
    -- `rsEncoder b j = (γ-γ')⁻¹ * ((f₁+γf₂) - (f₁+γ'f₂)) j = (γ-γ')⁻¹ * (γ-γ') * f₂ j = f₂ j`.
    rw [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, hc j hj, hc' j hj]
    simp only [smul_eq_mul]
    field_simp
    ring

end KoalaBear
