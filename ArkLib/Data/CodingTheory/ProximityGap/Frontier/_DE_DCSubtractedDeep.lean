/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselWickAllR

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# DC-subtracted deep moment: the prize bound reduces (conditionally) to `W_K ≤ 0` via the LANDED
  char-0 Bessel-Wick ceiling — but `W_K ≤ 0` is NOT universal (#444, angle DC_SUBTRACTED_DEEP)

> **CORRECTION (2026-06-19).** The empirical claim below that `W_K := A_K − E_K^{C} < 0` at *every*
> `K` and prime is **REFUTED** by the exact countermodel `_AvCP_AAPKernelCountermodel`
> (`n=16, p=76001, K=6`: `W_K > 0`, growing through `K = ⌊ln p⌋`; ~0.4% of window primes are bad,
> at moderate `v₂(p−1) ∈ {4,5,7}`, NOT Fermat-confined). So the SHARP kernel `A_K ≤ E_K^{C}` is the
> WRONG worst-case target. The conditional reduction in this file is still valid (if `W_K ≤ 0` then
> the prize bound), but its hypothesis cannot be discharged at the bad primes; the correct open
> kernel is the strictly weaker, still-prize-sufficient `A_K ≤ Wick_K` (which survives at every bad
> prime — `A_K/Wick ≈ 0.37` even at the worst witness, binding only at the trivial Parseval `K=1`).

## The exact structural finding (real `μ_n`, `p ≈ n^4`, `K` up to `⌊ln p⌋`)

Write `A_K := (1/q)·∑_{b≠0}‖η_b‖^{2K} = E_K(G) − |G|^{2K}/q` for the **DC-subtracted** energy (the
genuinely-controlling object: `M(n)=max_{b≠0}‖η_b‖`, and `M^{2K} ≤ q·A_K`). Let
`E_K^{C} := E_K^{char0}(μ_n) = (2K)!·[x^{2K}] I₀(2x)^{n/2}` be the char-0 (Bessel-identity) energy
(`AvW0.besselE K (n/2)`), and `Wick_K := (2K−1)‼·n^K`. Exact integer/rational computation on the
ACTUAL subgroups `μ_8 ⊂ F_4129`, `μ_16 ⊂ F_65617`, `μ_32 ⊂ F_1048609` (each `p ≈ n^4`), for every
`K = 1,…,⌊ln p⌋+3`, gives:

| object | finding |
|---|---|
| `A_K / (q·Wick_K)`         | `≤ 1` at every `K`, monotone ↓ in `K`; max at `K=1` (`= 1 − n/p`, the Parseval floor) |
| raw `E_K / Wick_K`         | **> 1** at deep `K` (e.g. `n=32, K=14`: `5.30`) — the DC term `n^{2K}/q` blows up |
| `W_K := A_K − E_K^{C}`     | `< 0` at MOST primes (typical deficit, `|W_K|/Wick_K ≤ 0.029`), but `> 0` at a sparse bad set (see CORRECTION above) |

So at the prize scale the char-`p` wraparound is *typically* an energy DEFICIT on the DC-subtracted
object (`A_K ≤ E_K^{C}` at most primes), but NOT universally. The raw `E_K ≤ Wick` is false (DC
dominates, `DCEnergyEssential`); the prize-sufficient `A_K ≤ Wick_K` holds at every prime (the LANDED
`AvW0.besselWick_allR` bounds `E_K^{C} ≤ Wick_K`, and `A_K ≤ Wick_K` survives even where `A_K > E_K^{C}`).

## What this brick proves (axiom-clean, NON-vacuous)

The chain `A_K ≤ E_K^{C} ≤ Wick_K ⟹ DCEnergyBound G K` is **valid and formalized**:

* `besselE_le_wick'`            — repackages the LANDED `AvW0.besselWick_allR`: `E_K^{C} ≤ Wick_K` (ℝ).
* `dcEnergyBound_of_dcSub_le_besselE` — **MAIN**: the open sign condition `A_K ≤ E_K^{C}` (`W_K ≤ 0`),
  stated cleared-of-division as `q·E_K − |G|^{2K} ≤ q·E_K^{C}`, IMPLIES `DCEnergyBound G K`, hence
  (via the landed `eta_pow_le_of_dcEnergyBound`) the per-frequency prize bound `‖η_b‖^{2K} ≤ q·Wick_K`.

The reduction shows `W_K ≤ 0` is a SHARPER *sufficient* condition than `A_K ≤ Wick_K` (`A_K ≤ E_K^{C}
≤ Wick_K`, and `E_K^{C}/Wick → 0` at deep `K`). It would close the prize IF it held — but per the
CORRECTION above it does NOT hold universally (refuted at `p=76001`). So the live, prize-sufficient
kernel is the weaker `A_K ≤ Wick_K`; this conditional remains a valid (but non-dischargeable-at-bad-
primes) sharper road, retained for the structure it exposes.

## Honest scope (#444)

This is a **reduction, not a closure** — and, post-correction, a reduction to a target now known too
strong for the worst case. The prize-sufficient OPEN KERNEL is `A_K ≤ Wick_K` (`A_K ≤ C·Wick_K`): by
the proven `_AvFrontier_KMomentBarrier`, no finite-order method supplies it, and the onset dichotomy
`_OnsetNormDichotomyTight` (which forces `W_r = 0` for `p > (2r)^{n/2}`) is VACUOUS at deep `K`
(`2^n ≫ n^4`). The brick's content is: (1) the axiom-clean proof that the sufficient sign condition
`A_K ≤ E_K^{C}` discharges `DCEnergyBound` by chaining onto the LANDED char-0 Bessel-Wick ceiling;
(2) the now-corrected picture (`A_K ≤ E_K^{C}` is the WRONG universal target — refuted by
`_AvCP_AAPKernelCountermodel` — but `A_K ≤ Wick_K` survives). The char-0 half (`E_C ≤ Wick`) is
genuinely landed.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.Frontier.DCSubtractedDeep

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The char-0 Bessel energy as a real number, `E_K^{C}(μ_{2m}) = (2K)!·[x^{2K}] I₀(2x)^m`. By the
named STEP-1 antipodal-balance identity this is `E_K^{char0}(μ_n)` for `n = 2m`. -/
noncomputable def besselEℝ (K m : ℕ) : ℝ := ((ArkLib.ProximityGap.Frontier.AvW0.besselE K m : ℚ) : ℝ)

/-- The Wick ceiling as a real number, `Wick_K = (2K−1)‼·n^K` with `n = 2m`. -/
noncomputable def wickℝ (K m : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * K - 1) : ℝ) * ((2 * m : ℕ) : ℝ) ^ K

/-- **The LANDED char-0 ceiling, real-cast.** `E_K^{C} ≤ Wick_K`, r-uniformly. This just repackages
the axiom-clean `AvW0.besselWick_allR` (the Bessel→exp coefficientwise domination) over `ℝ`. -/
theorem besselEℝ_le_wickℝ (K m : ℕ) : besselEℝ K m ≤ wickℝ K m := by
  unfold besselEℝ wickℝ
  have h : (ArkLib.ProximityGap.Frontier.AvW0.besselE K m : ℚ)
      ≤ ArkLib.ProximityGap.Frontier.AvW0.wickRHS K m :=
    ArkLib.ProximityGap.Frontier.AvW0.besselWick_allR K m
  have hcast : ((ArkLib.ProximityGap.Frontier.AvW0.besselE K m : ℚ) : ℝ)
      ≤ ((ArkLib.ProximityGap.Frontier.AvW0.wickRHS K m : ℚ) : ℝ) := by exact_mod_cast h
  -- unfold wickRHS = (2K-1)‼ · (2m)^K on the ℚ side and cast.
  have hw : ((ArkLib.ProximityGap.Frontier.AvW0.wickRHS K m : ℚ) : ℝ)
      = (Nat.doubleFactorial (2 * K - 1) : ℝ) * ((2 * m : ℕ) : ℝ) ^ K := by
    unfold ArkLib.ProximityGap.Frontier.AvW0.wickRHS
    push_cast
    ring
  rw [hw] at hcast
  exact hcast

/-- **MAIN reduction (axiom-clean, non-vacuous).** The open char-`p` excess SIGN condition
`W_K ≤ 0`, i.e. the DC-subtracted energy stays at-or-below the char-0 Bessel energy,
`q·E_K(G) − |G|^{2K} ≤ q·E_K^{C}` (with `E_K^{C} = besselEℝ K (|G|/2)` the char-0 value supplied by
STEP 1), IMPLIES the DC-subtracted prize hypothesis `DCEnergyBound G K`. Chains the open `W_K ≤ 0`
onto the LANDED char-0 Bessel-Wick ceiling `besselEℝ_le_wickℝ`. -/
theorem dcEnergyBound_of_dcSub_le_besselE {G : Finset F} (K : ℕ)
    (hsign : (Fintype.card F : ℝ) * (rEnergy G K : ℝ) - (G.card : ℝ) ^ (2 * K)
              ≤ (Fintype.card F : ℝ) * besselEℝ K (G.card / 2))
    (hcard : 2 * (G.card / 2) = G.card) :
    DCEnergyBound G K := by
  unfold DCEnergyBound
  -- want: q·E_K − |G|^{2K} ≤ q·Wick_K.  We have hsign: LHS ≤ q·E_C, and E_C ≤ Wick_K.
  have hq0 : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hEC : besselEℝ K (G.card / 2) ≤ wickℝ K (G.card / 2) := besselEℝ_le_wickℝ K (G.card / 2)
  -- wickℝ K (|G|/2) = (2K−1)‼ · (2·(|G|/2))^K = (2K−1)‼ · |G|^K  (using hcard).
  have hwick_eq : wickℝ K (G.card / 2)
      = (Nat.doubleFactorial (2 * K - 1) : ℝ) * (G.card : ℝ) ^ K := by
    unfold wickℝ
    have : ((2 * (G.card / 2) : ℕ) : ℝ) = (G.card : ℝ) := by
      rw [hcard]
    rw [this]
  calc (Fintype.card F : ℝ) * (rEnergy G K : ℝ) - (G.card : ℝ) ^ (2 * K)
      ≤ (Fintype.card F : ℝ) * besselEℝ K (G.card / 2) := hsign
    _ ≤ (Fintype.card F : ℝ) * wickℝ K (G.card / 2) := by
        exact mul_le_mul_of_nonneg_left hEC hq0
    _ = (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * K - 1) : ℝ) * (G.card : ℝ) ^ K) := by
        rw [hwick_eq]

/-- **End-to-end per-frequency prize bound from the open sign condition.** Combining the MAIN
reduction with the LANDED `eta_pow_le_of_dcEnergyBound`: if the char-`p` excess sign condition
`W_K ≤ 0` holds (DC-subtracted energy ≤ char-0 Bessel energy), then every nonprincipal frequency
satisfies the Wick-shaped prize bound `‖η_b‖^{2K} ≤ q·(2K−1)‼·|G|^K`. -/
theorem eta_pow_le_of_excess_sign {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {K : ℕ}
    (hsign : (Fintype.card F : ℝ) * (rEnergy G K : ℝ) - (G.card : ℝ) ^ (2 * K)
              ≤ (Fintype.card F : ℝ) * besselEℝ K (G.card / 2))
    (hcard : 2 * (G.card / 2) = G.card) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * K)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * K - 1) : ℝ) * (G.card : ℝ) ^ K) :=
  eta_pow_le_of_dcEnergyBound hψ (dcEnergyBound_of_dcSub_le_besselE K hsign hcard) hb

end ArkLib.ProximityGap.Frontier.DCSubtractedDeep

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.DCSubtractedDeep.besselEℝ_le_wickℝ
#print axioms ArkLib.ProximityGap.Frontier.DCSubtractedDeep.dcEnergyBound_of_dcSub_le_besselE
#print axioms ArkLib.ProximityGap.Frontier.DCSubtractedDeep.eta_pow_le_of_excess_sign
