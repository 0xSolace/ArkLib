/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerRatioSpectralCap

/-!
# Equality in the resonance tower spectral-cap ratio (#444)

The door-(iv) tower ratio cap says
`T(r+1)/T(r) ≤ μ`, where `μ` is a realised entrywise cap for the squared one-step spectrum
`w_k = ‖K̂(k)‖²`.  This file records the exact **equality residual** behind that cap:

> if the ratio saturates the cap, then
> `∑ k, (μ - w_k) * w_k^r = 0`.

Thus a saturated cap has no weighted slack on the `r`-support of the spectrum.  This is a constraint
lemma only: it does not bound `μ`, does not prove cancellation, and does not assert that saturation
occurs.  It merely pins what equality in the already-proven cap would force.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- Spectral weight at frequency `k`: `w_k = ‖K̂(k)‖²`. -/
private noncomputable def capEqWeight (u : ZMod m → ℂ) (k : ZMod m) : ℝ :=
  ‖kernelSpectrum (dftChar k) u‖ ^ 2

/-- The Parseval bridge in squared-weight form: `∑ w_k^r = m · T r`. -/
private theorem sum_capEqWeight_pow_eq (u : ZMod m → ℂ) (r : ℕ) :
    (∑ k : ZMod m, capEqWeight u k ^ r) = (m : ℝ) * resonanceMoment u r := by
  classical
  unfold capEqWeight
  rw [resonanceMoment_eq_spectral_powerMean u r]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← pow_mul, Nat.mul_comm]

/-- A finite power-sum identity: if the consecutive power-sum ratio equals `M`, then the
weighted cap-slack residual `∑ (M-a_i) a_i^r` vanishes. -/
theorem powerSum_capSlack_eq_zero_of_ratio_eq {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (r : ℕ) (M : ℝ)
    (hpos : 0 < ∑ i ∈ s, a i ^ r)
    (heq : (∑ i ∈ s, a i ^ (r + 1)) / (∑ i ∈ s, a i ^ r) = M) :
    (∑ i ∈ s, (M - a i) * a i ^ r) = 0 := by
  classical
  have hden : (∑ i ∈ s, a i ^ r) ≠ 0 := ne_of_gt hpos
  have hmul : (∑ i ∈ s, a i ^ (r + 1)) = M * (∑ i ∈ s, a i ^ r) := by
    calc
      (∑ i ∈ s, a i ^ (r + 1))
          = ((∑ i ∈ s, a i ^ (r + 1)) / (∑ i ∈ s, a i ^ r)) *
              (∑ i ∈ s, a i ^ r) := by
                rw [div_mul_cancel₀ _ hden]
      _ = M * (∑ i ∈ s, a i ^ r) := by rw [heq]
  calc
    (∑ i ∈ s, (M - a i) * a i ^ r)
        = ∑ i ∈ s, (M * a i ^ r - a i ^ (r + 1)) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hp : a i ^ (r + 1) = a i ^ r * a i := by
            exact pow_succ (a i) r
          rw [hp]
          ring
    _ = M * (∑ i ∈ s, a i ^ r) - (∑ i ∈ s, a i ^ (r + 1)) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 0 := by rw [hmul]; ring

/-- **Equality residual for the resonance ratio cap.**  If a realised spectral cap `Mcap` saturates
one tower growth ratio, then the weighted cap-slack residual vanishes:
`∑ k, (Mcap - ‖K̂(k)‖²) * (‖K̂(k)‖²)^r = 0`.

This is the exact equality condition behind `resonanceMoment_ratio_le_specMaxSq`: saturation leaves
no weighted slack on the `r`-support of the one-step spectrum.  It is a constraint only, not a bound
on `Mcap` and not a CORE/cancellation claim. -/
theorem resonanceMoment_ratio_capSlack_eq_zero_of_eq (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hm : 2 ≤ m) (r : ℕ) (Mcap : ℝ)
    (heq : resonanceMoment u (r + 1) / resonanceMoment u r = Mcap) :
    (∑ k : ZMod m,
        (Mcap - ‖kernelSpectrum (dftChar k) u‖ ^ 2) *
          (‖kernelSpectrum (dftChar k) u‖ ^ 2) ^ r) = 0 := by
  classical
  have hmpos : (0 : ℝ) < m := by
    have : (0 : ℕ) < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast this
  have hTrpos : 0 < resonanceMoment u r := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hfloor : ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := resonanceMoment_ge_pow u hu r
    have : (0 : ℝ) < ((m : ℝ) - 1) ^ r := by positivity
    linarith
  have hSpos : 0 < ∑ k : ZMod m, capEqWeight u k ^ r := by
    rw [sum_capEqWeight_pow_eq u r]
    positivity
  have hratio :
      (∑ k : ZMod m, capEqWeight u k ^ (r + 1)) /
        (∑ k : ZMod m, capEqWeight u k ^ r) = Mcap := by
    rw [sum_capEqWeight_pow_eq u (r + 1), sum_capEqWeight_pow_eq u r]
    rw [mul_div_mul_left _ _ (ne_of_gt hmpos)]
    exact heq
  simpa [capEqWeight] using
    (powerSum_capSlack_eq_zero_of_ratio_eq (Finset.univ : Finset (ZMod m))
      (capEqWeight u) r Mcap hSpos hratio)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.powerSum_capSlack_eq_zero_of_ratio_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_capSlack_eq_zero_of_eq
