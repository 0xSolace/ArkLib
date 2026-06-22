/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceTowerLogConvex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceChebyshevLower
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PowerSumRatioMonotone

/-!
# The resonance tower growth ratio is sandwiched: `m−1 ≤ T(r+1)/T(r) ≤ max_k ‖K̂(k)‖²` (#444)

The named `√p`-free door-(iv) free variable is the resonance moment
`T r = resonanceMoment u r = (1/m) ∑_k ‖K̂(k)‖^{2r}`, the `2r`-th spectral power-mean of the
one-step Gauss-period kernel spectrum `K̂(k) = kernelSpectrum (dftChar k) u`
(Parseval bridge `resonanceMoment_eq_spectral_powerMean`).

Two facts about the consecutive growth ratio `T(r+1)/T(r)` are already on main, BUT they live on
different sides and were never joined at the level of the named object:

* the **Plancherel floor** `(m−1) ≤ T(r+1)/T(r)` from the Chebyshev recursion
  `(m−1)·T r ≤ T (r+1)` (`_ResonanceChebyshevLower.resonanceMoment_succ_ge`);
* the abstract **spectral-max cap** `S_{t+1}/S_t ≤ max_i a_i` on an arbitrary nonnegative spectrum
  (`PowerSumRatioMonotone.powerSum_ratio_le_max`), which was NEVER transported onto the named
  spectral measure `w_k = ‖K̂(k)‖²`.

This file lands the **named-object upper cap** and the resulting **two-sided sandwich**:

> **`m − 1 ≤ T(r+1)/T(r) ≤ max_k ‖K̂(k)‖²`** (`resonanceMoment_ratio_le_specMaxSq`,
> `resonanceMoment_ratio_sandwich`),

so the door-(iv) growth ratio of the actual prize object is pinned between the **Plancherel floor**
`m−1` (forced) and the **squared spectral sup-norm** `max_k ‖K̂(k)‖²` (the worst Gauss-period kernel
mass). Together with the just-landed monotonicity `T(r+1)/T(r) ≤ T(r+2)/T(r+1)`
(`resonanceMoment_ratio_monotone`), the ratio is a **monotone sequence trapped in the band
`[m−1, max_k ‖K̂(k)‖²]`** that rises toward `max_k ‖K̂(k)‖²` from below.

## Door-(iv) reading (why this is the right localization, not a moment/spectral-cap brick)

The prize collapse needs `T r` to fall from the trivial `Θ(m^{2r−1})` ceiling to the
`√`-cancelled `Θ(m^r)` regime. Because the growth ratio is monotone and capped by
`max_k ‖K̂(k)‖²`, the asymptotic growth rate `lim_r T(r+1)/T(r)` exists and equals that squared
spectral sup-norm; the ENTIRE open `√`-cancellation question is now exactly the question of how far
`max_k ‖K̂(k)‖²` sits below the trivial frequency ceiling `(m−1)²`. This is NOT a new bound on any
`‖K̂(k)‖` (we supply `max_k ‖K̂(k)‖²` as a free realised upper bound, prove nothing about its size),
and NOT a spectral-cap *consumer* brick (it does not consume a hypothesised cap — it states the
exact bracket the named tower ratio always obeys). It pins the door-(iv) growth rate to the worst
single-frequency Gauss-period kernel mass — the open BGK object — with the floor `m−1` forced and
the ceiling `max_k ‖K̂(k)‖²` ≤ `(m−1)²` trivially (per-frequency triangle), the gap being the open
cancellation budget.

## Honest scope (rules 1,3,6)

CERTAIN exact consequence of the Parseval bridge + the abstract ratio-cap + the proven Chebyshev
floor. The cap value `max_k ‖K̂(k)‖²` is supplied as a *realised* entrywise upper bound; we do NOT
bound its magnitude (that IS the open object). Hence NO bound on `T r` beyond what its endpoints
already give. CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion /
moment / anti-concentration / capacity claim. Axiom-clean (`propext, Classical.choice, Quot.sound`).
Issue #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open Finset
open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- Spectral weight at frequency `k`: the squared one-step kernel modulus `w_k = ‖K̂(k)‖²`. -/
private noncomputable def specWeight (u : ZMod m → ℂ) (k : ZMod m) : ℝ :=
  ‖kernelSpectrum (dftChar k) u‖ ^ 2

private theorem specWeight_nonneg (u : ZMod m → ℂ) (k : ZMod m) : 0 ≤ specWeight u k := by
  unfold specWeight; positivity

/-- The Parseval bridge in weight form: `∑_k w_k^r = m · T r`. -/
private theorem sum_specWeight_pow_eq (u : ZMod m → ℂ) (r : ℕ) :
    (∑ k : ZMod m, specWeight u k ^ r) = (m : ℝ) * resonanceMoment u r := by
  classical
  unfold specWeight
  rw [resonanceMoment_eq_spectral_powerMean u r]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← pow_mul, Nat.mul_comm]

/-- **The named-object spectral-max cap.** For unit-modulus phases with `m ≥ 2`, the resonance
tower growth ratio is bounded above by the squared spectral sup-norm:
`T(r+1)/T(r) ≤ max_k ‖K̂(k)‖²`, supplied as a realised entrywise upper bound `Mcap` with
`b₀` attaining it. Transports `PowerSumRatioMonotone.powerSum_ratio_le_max` on the spectral weights
`w_k = ‖K̂(k)‖²` through the Parseval bridge, clearing the common `m` factor. -/
theorem resonanceMoment_ratio_le_specMaxSq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) (Mcap : ℝ) (hMcap : ∀ k : ZMod m, specWeight u k ≤ Mcap) :
    resonanceMoment u (r + 1) / resonanceMoment u r ≤ Mcap := by
  classical
  have hmpos : (0 : ℝ) < m := by
    have : (1 : ℕ) ≤ m := NeZero.one_le; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  -- positivity of T r (proven tower floor)
  have hTrpos : 0 < resonanceMoment u r := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hfloor : ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := resonanceMoment_ge_pow u hu r
    have : (0 : ℝ) < ((m : ℝ) - 1) ^ r := by positivity
    linarith
  -- positivity of the weight power-sum S_r = m·T r > 0
  have hSrpos : 0 < ∑ k : ZMod m, specWeight u k ^ r := by
    rw [sum_specWeight_pow_eq u r]; positivity
  -- abstract ratio cap on the spectral weights
  have hcap :
      (∑ k : ZMod m, specWeight u k ^ (r + 1)) / (∑ k : ZMod m, specWeight u k ^ r) ≤ Mcap :=
    ProximityGap.Frontier.PowerSumRatioMonotone.powerSum_ratio_le_max
      (specWeight u) (specWeight_nonneg u) Mcap hMcap r hSrpos
  -- rewrite the abstract ratio as T(r+1)/T(r): both power-sums are m·T(·)
  rw [sum_specWeight_pow_eq u (r + 1), sum_specWeight_pow_eq u r] at hcap
  -- (m·T(r+1))/(m·T r) = T(r+1)/T r since m > 0
  have hsimp :
      ((m : ℝ) * resonanceMoment u (r + 1)) / ((m : ℝ) * resonanceMoment u r)
        = resonanceMoment u (r + 1) / resonanceMoment u r := by
    rw [mul_div_mul_left _ _ (ne_of_gt hmpos)]
  rwa [hsimp] at hcap

/-- **The Plancherel floor on the growth ratio**: `m − 1 ≤ T(r+1)/T(r)`. Direct division form of
the proven Chebyshev recursion `(m−1)·T r ≤ T (r+1)` (`resonanceMoment_succ_ge`). -/
theorem resonanceMoment_ratio_ge_base (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) :
    (m : ℝ) - 1 ≤ resonanceMoment u (r + 1) / resonanceMoment u r := by
  have hTrpos : 0 < resonanceMoment u r := by
    have hmR : (1 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hfloor : ((m : ℝ) - 1) ^ r ≤ resonanceMoment u r := resonanceMoment_ge_pow u hu r
    have : (0 : ℝ) < ((m : ℝ) - 1) ^ r := by positivity
    linarith
  have hcheb := resonanceMoment_succ_ge u hu r
  rw [le_div_iff₀ hTrpos]
  linarith [hcheb]

/-- **The two-sided sandwich on the resonance tower growth ratio** (unit phases, `m ≥ 2`):
`m − 1 ≤ T(r+1)/T(r) ≤ max_k ‖K̂(k)‖²`. The door-(iv) growth ratio of the named prize object is
pinned between the forced Plancherel floor `m−1` and the squared spectral sup-norm `Mcap`
(realised at some `b₀`, i.e. `Mcap = max_k ‖K̂(k)‖²`). Combined with
`resonanceMoment_ratio_monotone` this exhibits the growth ratio as a monotone sequence trapped in
`[m−1, Mcap]`, rising toward `Mcap`. -/
theorem resonanceMoment_ratio_sandwich (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) (Mcap : ℝ) (hMcap : ∀ k : ZMod m, specWeight u k ≤ Mcap) :
    (m : ℝ) - 1 ≤ resonanceMoment u (r + 1) / resonanceMoment u r ∧
      resonanceMoment u (r + 1) / resonanceMoment u r ≤ Mcap :=
  ⟨resonanceMoment_ratio_ge_base u hu hm r,
    resonanceMoment_ratio_le_specMaxSq u hu hm r Mcap hMcap⟩

/-- **The realised form: the cap is attained as `max_k ‖K̂(b₀)‖²`.** When `b₀` realises the spectral
max (`∀ k, ‖K̂(k)‖² ≤ ‖K̂(b₀)‖²`), the sandwich becomes
`m − 1 ≤ T(r+1)/T(r) ≤ ‖K̂(b₀)‖²`, exhibiting the worst single-frequency Gauss-period kernel mass as
the exact ceiling of the door-(iv) growth ratio. -/
theorem resonanceMoment_ratio_sandwich_realised (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1)
    (hm : 2 ≤ m) (r : ℕ) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2) :
    (m : ℝ) - 1 ≤ resonanceMoment u (r + 1) / resonanceMoment u r ∧
      resonanceMoment u (r + 1) / resonanceMoment u r
        ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2 :=
  resonanceMoment_ratio_sandwich u hu hm r (‖kernelSpectrum (dftChar b₀) u‖ ^ 2)
    (fun k => hb₀ k)

/-- **Mean-cap rigidity for the tower growth ratio.** If every squared spectral weight is already
at most the Parseval mean `m−1`, then every consecutive resonance growth ratio is forced to equal
`m−1` exactly. This is the tight endpoint of the sandwich: an anti-spike theorem down to the mean
would leave no local ratio slack at all; any actual prize improvement must therefore come from
bounding the realised spectral sup-norm above the floor but far below the trivial `(m−1)^2` ceiling,
not from a below-floor ratio rung. -/
theorem resonanceMoment_ratio_eq_base_of_specMaxSq_le_base
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hm : 2 ≤ m) (r : ℕ)
    (hcap : ∀ k : ZMod m, specWeight u k ≤ (m : ℝ) - 1) :
    resonanceMoment u (r + 1) / resonanceMoment u r = (m : ℝ) - 1 := by
  exact le_antisymm
    (resonanceMoment_ratio_le_specMaxSq u hu hm r ((m : ℝ) - 1) hcap)
    (resonanceMoment_ratio_ge_base u hu hm r)
/-- **A realised spectral maximum cannot sit below the Parseval floor.** If `b₀` realises the
squared one-step kernel spectral maximum, then its mass is at least the forced mean `m−1`.
This is the endpoint form of the growth-ratio sandwich: the ratio has floor `m−1` and ceiling
`‖K̂(b₀)‖²`, so the ceiling itself must clear the floor. It is a lower-side obstruction only,
not an upper bound on the worst frequency. -/
theorem realised_specMaxSq_ge_parseval_floor (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hm : 2 ≤ m) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤
      ‖kernelSpectrum (dftChar b₀) u‖ ^ 2) :
    (m : ℝ) - 1 ≤ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2 := by
  have hs := resonanceMoment_ratio_sandwich_realised u hu hm 0 b₀ hb₀
  exact le_trans hs.1 hs.2

/-- **No sub-floor realised spectral cap.** A proposed realised worst-frequency cap strictly below
`m−1` contradicts the Plancherel floor in the named resonance tower. Thus any door-(iv) proof must
attack the genuine open upper range above the mean; it cannot place the actual spectral
maximum under the mean. -/
theorem not_realised_specMaxSq_lt_parseval_floor (u : ZMod m → ℂ)
    (hu : ∀ l : ZMod m, ‖u l‖ = 1) (hm : 2 ≤ m) (b₀ : ZMod m)
    (hb₀ : ∀ k : ZMod m, ‖kernelSpectrum (dftChar k) u‖ ^ 2 ≤
      ‖kernelSpectrum (dftChar b₀) u‖ ^ 2) :
    ¬ ‖kernelSpectrum (dftChar b₀) u‖ ^ 2 < (m : ℝ) - 1 := by
  exact not_lt_of_ge (realised_specMaxSq_ge_parseval_floor u hu hm b₀ hb₀)

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_le_specMaxSq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_ge_base
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_sandwich
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_sandwich_realised
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_ratio_eq_base_of_specMaxSq_le_base
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.realised_specMaxSq_ge_parseval_floor
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.not_realised_specMaxSq_lt_parseval_floor
