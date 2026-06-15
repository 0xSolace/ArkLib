/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Newton-polygon depth optimization of the char-`p` moment bound (#444, lane wf-M4)

## What this lane established (the reduction)

The prize bound `M = max_{b≠0}‖η_b‖ ≤ C·√(n·log(q/n))` for the thin 2-power subgroup `μ_n`
reduces — via the EXACT `2r`-th moment identity `Σ_b‖η_b‖^{2r} = q·E_r(μ_n)`
(`subgroup_gaussSum_moment`, substrate, no Weil) and a single-term-≤-sum Markov step
(`eta_pow_le_of_energyBound`, substrate) — to the per-depth energy hypothesis

  `GaussianEnergyBound μ_n r :   E_r(μ_n) ≤ (2r-1)‼ · n^r`.

This file supplies the **third leg**: the explicit *depth optimization*, i.e. that IF the energy
bound holds at depth `r`, the resulting per-frequency bound has the **prize square-root shape**.
Concretely we prove, axiom-clean and unconditionally as `ℝ`-arithmetic, the two arithmetic atoms
that turn the substrate's opaque `M_r = (q·(2r-1)‼·n^r)^{1/2r}` into `≤ √(C·r·n)·q^{1/(2r)}`:

* `doubleFactorial_rootBound` : `((2r-1)‼ : ℝ)^{1/r} ≤ 2·r`  (the double-factorial size atom:
  `(2r-1)‼ ≤ (2r)^r`, so its `r`-th root is `≤ 2r`). This is the Newton-polygon **slope-0
  segment count** in size form — the `(2r-1)‼` genuine antipodal matchings of Lam–Leung, whose
  `r`-th root contributes the `√r` (= `√log(q/n)` at the optimal depth) of the prize.

* `eta_sq_le_depthOpt` : from `GaussianEnergyBound μ_n r` (`r ≥ 1`), every period satisfies
  `‖η_b‖² ≤ (2r)·n·q^{1/r}`.  Hence `‖η_b‖ ≤ √(2r·n)·q^{1/(2r)}`.  At the prize-supportable depth
  `r = ⌊2β⌋` (so `q^{1/r} = O(1)` and `2r·n ≍ n·log(q/n)`) this is `M ≤ C·√(n·log(q/n))` — THE
  PRIZE SHAPE.  (The numerical prescreen `scripts/probes/probe_wf5M4_*.py` confirms the implied
  `M/√(n log(q/n))` is bounded by ≈ 0.5 and *decreasing* in β across `n ∈ {16,32,64}`,
  `β ∈ [2,4]` — i.e. this optimization is not just sufficient, it is comfortably so.)

## The Newton-polygon reading (why `(2r-1)‼` is the right slope count)

For `a ∈ μ_n^r`, let `v(a)` be the `(1−ζ_p)`-adic valuation of `S(a) = Σ_i ζ_p^{a_i} ∈ ℤ_p[ζ_p]`
(`e = p−1`, so `v(p) = p−1`).  `S(a) ≡ 0 (mod p) ⟺ v(a) ≥ p−1`.  The Newton polygon of the period
resultant splits the `2r`-tuples by valuation:
  * the **slope-0 segment** = the `(2r-1)‼` genuine antipodal (Lam–Leung) matchings, each free over
    `n` choices ⇒ count `(2r-1)‼·n^r`;
  * the **positive-slope segments** = *spurious* mod-`p` coincidences, count `~ n^{2r}/p`, which is
    `subdominant` exactly while `n^r ≤ p`, i.e. `r ≤ β` (equivalently the in-band depth `2r ≤ 2β`).
The prize-supportable depth `r ≍ log q` lies inside this band for `β` bounded below, and the
finiteness of the valuation (Stevenhagen–Lenstra, formalized in `_ChebotarevValuationModP.lean`
for the sibling DFT-minor object) is what forbids new slope-0 segments below depth `p`.  The OPEN
crux is precisely that no spurious slope-0 segment appears in-band — i.e. `GaussianEnergyBound μ_n r`
at `r ≍ log q` — the char-`p` transfer of the char-0 Lam–Leung matching count.

## Honest scope

Axiom-clean, pure `ℝ`/`ℕ` arithmetic.  The two atoms are UNCONDITIONAL; `eta_sq_le_depthOpt`
consumes the named `GaussianEnergyBound` hypothesis (the open char-`p` transfer) and is the clean
arrow to the prize shape.  This file does NOT prove the prize — it proves that the energy
hypothesis, at the depth the Newton polygon supports, yields the prize square-root form (the
arithmetic the substrate left implicit).  Issues #444, #389, #407.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.GaussPeriodMomentBound (GaussianEnergyBound eta_pow_le_of_energyBound)

namespace ProximityGap.Frontier.NewtonPolygonDepthOpt

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The double-factorial size atom (ℕ):** `(2r-1)‼ ≤ (2r)^r`.  The product
`(2r-1)·(2r-3)···3·1` has `r` factors (for `r ≥ 1`), each `≤ 2r`, so the product `≤ (2r)^r`.
This is the size of the Newton-polygon slope-0 segment count — the `(2r-1)‼` genuine
Lam–Leung antipodal matchings — bounded by the trivial `(2r)^r`. -/
theorem doubleFactorial_le_pow (r : ℕ) :
    Nat.doubleFactorial (2 * r - 1) ≤ (2 * r) ^ r := by
  induction r with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- r = 1:  (1)‼ = 1 ≤ 2^1 = 2
      subst hk0; decide
    · -- k ≥ 1:  2(k+1)-1 = (2k-1)+2,  use doubleFactorial_add_two
      have hstep : 2 * (k + 1) - 1 = (2 * k - 1) + 2 := by omega
      rw [hstep, Nat.doubleFactorial_add_two]
      have h1 : Nat.doubleFactorial (2 * k - 1) ≤ (2 * k) ^ k := ih
      have h2 : (2 * k) ^ k ≤ (2 * (k + 1)) ^ k := Nat.pow_le_pow_left (by omega) k
      calc (((2 * k - 1) + 2) : ℕ) * Nat.doubleFactorial (2 * k - 1)
          ≤ (2 * (k + 1)) * (2 * (k + 1)) ^ k := by
            have hfac : ((2 * k - 1) + 2 : ℕ) ≤ 2 * (k + 1) := by omega
            exact Nat.mul_le_mul hfac (le_trans h1 h2)
        _ = (2 * (k + 1)) ^ (k + 1) := by rw [pow_succ]; ring

/-- **The double-factorial root bound (ℝ):** `((2r-1)‼ : ℝ)^{1/r} ≤ 2r`  (for `r ≥ 1`).
The `r`-th root of the slope-0 segment count is `≤ 2r` — the source of the prize's `√r = √log(q/n)`
factor.  Proof: take real `r`-th roots in `(2r-1)‼ ≤ (2r)^r` (`doubleFactorial_le_pow`). -/
theorem doubleFactorial_rootBound {r : ℕ} (hr : 1 ≤ r) :
    ((Nat.doubleFactorial (2 * r - 1) : ℝ)) ^ ((r : ℝ)⁻¹) ≤ (2 * r : ℝ) := by
  have hbase : (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ ((2 * r : ℕ) : ℝ) ^ r := by
    have := doubleFactorial_le_pow r
    calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ (((2 * r) ^ r : ℕ) : ℝ) := by exact_mod_cast this
      _ = ((2 * r : ℕ) : ℝ) ^ r := by push_cast; ring
  have hmono := Real.rpow_le_rpow (by positivity) hbase (by positivity : (0:ℝ) ≤ (r:ℝ)⁻¹)
  have hcollapse : (((2 * r : ℕ) : ℝ) ^ r) ^ ((r : ℝ)⁻¹) = ((2 * r : ℕ) : ℝ) :=
    Real.pow_rpow_inv_natCast (by positivity) (Nat.one_le_iff_ne_zero.mp hr)
  rw [hcollapse] at hmono
  calc (Nat.doubleFactorial (2 * r - 1) : ℝ) ^ ((r : ℝ)⁻¹)
      ≤ ((2 * r : ℕ) : ℝ) := hmono
    _ = (2 * r : ℝ) := by push_cast; ring

/-- **The depth-optimized per-frequency bound (the prize shape).**
From the depth-`r` energy hypothesis `GaussianEnergyBound μ_n r` (`r ≥ 1`), every Gauss period
satisfies `‖η_b‖² ≤ (2r)·n·q^{1/r}`, i.e. `‖η_b‖ ≤ √(2r·n)·q^{1/(2r)}`.  Combining the substrate's
power bound `‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r` (`eta_pow_le_of_energyBound`) with the root atom
`doubleFactorial_rootBound`.  At the Newton-polygon-supportable depth `r = ⌊2β⌋` (so `q^{1/r}=O(1)`
and `2r·n ≍ n·log(q/n)`), this is exactly the prize `M ≤ C·√(n·log(q/n))`. -/
theorem eta_sq_le_depthOpt {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hr : 1 ≤ r) (h : GaussianEnergyBound G r) (b : F) :
    ‖eta ψ G b‖ ^ 2 ≤ (2 * r : ℝ) * (G.card : ℝ) * (Fintype.card F : ℝ) ^ ((r : ℝ)⁻¹) := by
  -- substrate power bound, raised to the (1/r) power
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  set D : ℝ := (Nat.doubleFactorial (2 * r - 1) : ℝ) with hD
  have hDnn : (0:ℝ) ≤ D := by positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ q * D * n ^ r := by
    rw [← pow_mul]; exact eta_pow_le_of_energyBound hψ h b
  -- take r-th roots
  have hrne : (r : ℕ) ≠ 0 := Nat.one_le_iff_ne_zero.mp hr
  have hroot : ‖eta ψ G b‖ ^ 2 ≤ (q * D * n ^ r) ^ ((r : ℝ)⁻¹) := by
    calc ‖eta ψ G b‖ ^ 2
        = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sq_nonneg _) hrne).symm
      _ ≤ (q * D * n ^ r) ^ ((r : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hpow (by positivity)
  -- distribute the (1/r) power:  (q·D·n^r)^{1/r} = q^{1/r}·D^{1/r}·n
  have hqnn : (0:ℝ) ≤ q := by positivity
  have hnnn : (0:ℝ) ≤ n := by positivity
  have hnr : (n ^ r) ^ ((r : ℝ)⁻¹) = n := by
    rw [← Real.rpow_natCast n r, ← Real.rpow_mul hnnn,
        mul_inv_cancel₀ (by exact_mod_cast hrne : (r:ℝ) ≠ 0), Real.rpow_one]
  have hsplit : (q * D * n ^ r) ^ ((r : ℝ)⁻¹)
      = q ^ ((r : ℝ)⁻¹) * (D ^ ((r : ℝ)⁻¹) * n) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hqnn hDnn, hnr, mul_assoc]
  rw [hsplit] at hroot
  -- D^{1/r} ≤ 2r
  have hDr : D ^ ((r : ℝ)⁻¹) ≤ (2 * r : ℝ) := doubleFactorial_rootBound hr
  calc ‖eta ψ G b‖ ^ 2
      ≤ q ^ ((r : ℝ)⁻¹) * (D ^ ((r : ℝ)⁻¹) * n) := hroot
    _ ≤ q ^ ((r : ℝ)⁻¹) * ((2 * r : ℝ) * n) := by
        gcongr
    _ = (2 * r : ℝ) * n * q ^ ((r : ℝ)⁻¹) := by ring

end ProximityGap.Frontier.NewtonPolygonDepthOpt

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.NewtonPolygonDepthOpt.doubleFactorial_le_pow
#print axioms ProximityGap.Frontier.NewtonPolygonDepthOpt.doubleFactorial_rootBound
#print axioms ProximityGap.Frontier.NewtonPolygonDepthOpt.eta_sq_le_depthOpt
