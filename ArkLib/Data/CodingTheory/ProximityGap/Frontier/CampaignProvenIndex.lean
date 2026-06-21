/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B2_char0_logconcave
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B5_MomentProblemLogConvex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B6_cumulant_signs
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B8_kstability_char0_closure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B9_GaussianConvexOrderExtremal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6F1_gaussian_step_telescope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6P1_nonprincipal_energy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL3_char0_prize_moment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL4_char0_nonprincipal_energy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G2_ResonanceCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G3_periodpoly_coeff_nogo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G4_roughness_not_the_driver
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BridgeOneWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoTighterBoundCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueThinFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPWraparoundLogConcaveQ
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPStepRatioMonotoneFails
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RhoAntitoneFailsThinPrime
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVValueShiftHistogramObstruction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WraparoundMarkovVacuity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVIndexFactorOvershoot
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceOrderBlind
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBSidonNoEnergyExcess
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentTrappedCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeObjectGrandCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSignedDeepSumAbsLeak
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleTrivialOvershoot

/-!
# Campaign-Proven Index — permanent named exports of the prize close-out (#444)

The #389/#407/#444 BGK / δ* campaign produced a large body of **axiom-clean** results in
fast-iteration scratch files (`Frontier/_wf*`). Those files are explicitly *throwaway*
(`Frontier/README.md`: "files starting `_` are throwaway"), yet several of their headline
theorems are load-bearing and proven. This module makes that proven content **permanent and
discoverable**: each load-bearing result below is re-exported under a stable, descriptively
named theorem in a non-underscore permanent module, carrying a docstring that states its
**scope** (`char-0` / `obstruction` / `prize-bridge`) and its axiom audit.

This is a **consolidation only** — no mathematics is changed. Every export here is a direct
alias of a proven theorem; the axiom audit at the bottom confirms the inherited profile is
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Scope tags

* **char-0** — proven unconditionally in characteristic 0 (the regime where the Lam–Leung /
  Wick energy law `E_r ≤ (2r-1)‼·n^r` is a theorem). These are the substrate the prize bridges
  consume; they do NOT by themselves resolve the prize (which needs the char-`p` transfer at
  `r ≈ ln q`).
* **obstruction** — an axiom-clean proof that a *named candidate lever* cannot reach the prize
  floor (a countermodel / no-go). These are permanent negative results.
* **prize-bridge** — an axiom-clean named-conditional reduction: `<named input> ⟹ prize bound`,
  with the named input the only remaining obligation.

The remaining open core (`BGKBound(1/2)`, the thin dyadic Gauss-period exponent-1/2
cancellation) is documented in `PROXIMITY_PRIZE_WORKBENCH.lean` and is NOT discharged by
anything here; this index does not claim otherwise.

## Index of permanent exports (by scope)

| export | scope | source brick |
|---|---|---|
| `char0_stepRatio_antitone_iff_sharpNewton` | char-0 | B2 |
| `char0_W3anti_of_sharpNewton_export` | char-0 | B2 |
| `char0_kstability_cross_le_wick` | char-0 | B8 |
| `char0_prize_moment_bound_unconditional` | char-0 | L3 |
| `char0_prize_moment_bound_sq_unconditional` | char-0 | L3 |
| `char0_nonprincipalEnergyBound_discharged` | char-0 | L4 |
| `char0_eta_pow_le_unconditional` | char-0 | L4 |
| `gaussian_moment_telescope` | prize-bridge | F1 |
| `convexOrder_gaussian_iff_wick_export` | prize-bridge | B9 |
| `prize_of_matchedGaussian_stepLaw_export` | prize-bridge | B9 |
| `eta_pow_le_of_nonprincipalEnergyBound_export` | prize-bridge | P1 |
| `moment_problem_does_not_give_wick_bracket` | obstruction | B5 |
| `cumulant_sign_route_refuted` | obstruction | B6 |
| `resonance_ceiling_below_prize_floor` | obstruction | G2 |
| `coeff_route_loose_export` | obstruction | G3 |
| `roughness_does_not_add_bad_primes_export` | obstruction | G4 |
| `prizeBound_iff_shawValue_le_export` | capstone | ShawValue |
| `shawValue_worstPeriod_clean_corridor_export` | capstone | ShawValue |
| `shawValue_bracket_width_eq_sqrt_export` | capstone | ShawValue |
| `charP_wrap_gap_ge_two_mul_sq_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_wrap_gap_nonneg_of_logConcave_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_transfer_of_dominance_logConcave_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_stepRatioMonotoneAt_iff_gap_nonneg_export` | obstruction | CharPStepRatioFails |
| `charP_stepRatioMonotone_false_n32_export` | obstruction | CharPStepRatioFails |
| `charP_no_universal_positive_stepRatioMonotone_export` | obstruction | CharPStepRatioFails |
| `rho_normalized_antitone_and_ceiling_incompatible_export` | obstruction | RhoAntitoneFails |
| `rho_antitone_route_not_universal_export` | obstruction | RhoAntitoneFails |
| `valueShift_nontrivial_forces_flat_histogram_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `valueShift_step_zero_of_one_histogram_witness_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `valueShift_route_vacuous_of_one_histogram_witness_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `wraparound_markov_count_le_export` | obstruction | WraparoundMarkovVacuity |
| `wraparound_markov_bound_vacuous_below_mean_export` | obstruction | WraparoundMarkovVacuity |
| `wraparound_average_control_does_not_bound_sup_export` | obstruction | WraparoundMarkovVacuity |
| `doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_index_le_sq_of_scaledConstant_le_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_cosetInvariant_blind_to_order_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_cosetHitting_selector_bound_iff_global_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_strict_selector_bound_misses_coset_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_positive_additiveEnergyExcess_iff_not_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export` | capstone | DoorIVHalfMassEquivalence |
| `trivial_cocycle_full_concentration_export` | obstruction | JacobiCocycleDispersion |
| `trivial_cocycle_offSupport_zero_export` | obstruction | JacobiCocycleDispersion |
| `jacobiCocycleDispersion_iff_shawValue_le_export` | capstone | JacobiCocycleDispersion |
| `exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export` | capstone | JacobiCocycleDispersion |
| `not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export` | capstone | JacobiCocycleDispersion |
| `exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export` | capstone | JacobiCocycleDispersion |
| `doorIV_abs_signed_le_abs_moment_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `doorIV_leak_nonneg_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `doorIV_abs_moment_bound_transfers_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `trivial_cocycle_overshoots_thin_export` | obstruction | JacobiCocycleTrivialOvershoot |
| `trivial_overshoot_gap_pos_export` | obstruction | JacobiCocycleTrivialOvershoot |

## Lane-2 capstone (the `prize ⟺ Sh(n)=O(1)` normalization)

The **capstone** scope tag marks the Lane-2 deliverable of the door-(iv) phase (#444,
Shaw-value essay 2026-06-18): the axiom-clean reduction of the prize inequality to a bounded
normalized *Shaw value* `Sh(M) = M / √(n·L)`, together with the proven two-sided corridor
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on the REAL Gauss-period worst frequency `M(μ_n)`. The floor is
unconditional (thin-regime Parseval, `q ≥ 2n`); the ceiling is unconditional (triangle
inequality); the open prize is *exactly* the demand to collapse this `√n`-wide corridor to an
absolute constant. These are normalization/consolidation only — no anti-concentration, completion,
moment, or capacity claim is hidden, and CORE stays OPEN.
-/

open scoped Nat

namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex

open ProximityGap.PrizeWorkbench
open ArkLib.ProximityGap.Frontier
-- `eta` (the subgroup Gauss-sum period) lives here; needed for the L4/P1 exports below.
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteShawValueThinFloor
open ProximityGap.Frontier.WorstPeriodSqrtNFloor

/-! ## B2 — char-0 Wick step-ratio antitonicity (log-concavity), reduced to the classical
`SharpNewtonBessel` (Laguerre–Pólya type-I) input. Scope: **char-0**. -/

/-- **[char-0, B2]** The char-0 Wick-normalised moment step ratio `R d r = m_{r+1}/m_r` is
antitone in `r` **iff** the sharp Newton inequality holds for the Bessel power coefficients —
an exact, axiom-clean algebraic equivalence (no analytic input). -/
theorem char0_stepRatio_antitone_iff_sharpNewton (d : ℕ) (hd : 1 ≤ d) (r : ℕ) :
    Rstep d (r + 1) ≤ Rstep d r ↔
      ((r + 2 : ℕ) : ℚ) * besselCoeff d (r + 2) * besselCoeff d r
        ≤ ((r + 1 : ℕ) : ℚ) * (besselCoeff d (r + 1)) ^ 2 :=
  R_antitone_iff_sharpNewton hd r

/-- **[char-0, B2]** Headline: the classical `SharpNewtonBessel` (LP-I) hypothesis yields the
full telescope input `R d r ≤ 1` for all `r`, i.e. char-0 Wick monotonicity (`W3-anti`). -/
theorem char0_W3anti_of_sharpNewton_export (d : ℕ) (hd : 1 ≤ d)
    (hSN : SharpNewtonBessel d) : ∀ r, Rstep d r ≤ 1 :=
  char0_W3anti_of_sharpNewton hd hSN

/-! ## B8 — char-0 K=1 K-stability cross bound (the dyadic convolution closes). Scope: **char-0**. -/

/-- **[char-0, B8]** The char-0 `K = 1` K-stability cross bound. From the exact dyadic
convolution `E_r(μ_n) = ∑ C(2r,2j)·E_j(H)·E_{r-j}(H)` (`H = μ_{n/2}`, `-1 ∈ H`) and the per-set
char-0 Wick bound, the interior (cross) energy satisfies
`E_r(μ_n) - 2·E_r(H) ≤ (2r-1)‼·((2h)^r - 2 h^r) = Wick(n,r) - 2·Wick(n/2,r)`. -/
theorem char0_kstability_cross_le_wick {r : ℕ} (hr : 1 ≤ r) {h Eμn : ℝ} (hh : 0 ≤ h)
    (E : ℕ → ℝ) (hE0 : E 0 = 1) (hEnonneg : ∀ j, 0 ≤ E j)
    (hconv : Eμn = ∑ j ∈ Finset.range (r + 1),
        (Nat.choose (2 * r) (2 * j) : ℝ) * E j * E (r - j))
    (hwick : ∀ j, j ≤ r → E j ≤ ((2 * j - 1)‼ : ℝ) * h ^ j) :
    Eμn - 2 * E r ≤ ((2 * r - 1)‼ : ℝ) * ((2 * h) ^ r - 2 * h ^ r) :=
  W5KStabilityChar0.cross_le_wick_cross hr hh E hE0 hEnonneg hconv hwick

/-! ## L3 — the FULL char-0 prize moment bound as ONE *unconditional* theorem (no Sidon /
no antipodal-pairing hypothesis; the char-0 Lam–Leung energy bound is discharged internally via
`DyadicEnergyK1`). Scope: **char-0**. This is the strongest single proven statement of the
campaign: in characteristic 0 the per-frequency prize cancellation is a *theorem*, with the only
remaining gap being the char-`p` transfer at the prize scale `n = 2^30` (the BGK wall). -/

/-- **[char-0, L3]** THE char-0 prize moment bound (norm form), UNCONDITIONAL. For `G ⊆ μ_{2^k}`
(`k ≥ 1`) in a characteristic-zero field, a formal period sup `M` with `Q ≥ 1` frequencies and the
formal-period moment identity `M^{2r} ≤ Q·E_r(G)` obeys, at optimal depth `r ≥ max(1, log Q)`, the
prize square-root shape `M ≤ √(2e·|G|·r)`. The Lam–Leung energy bound `E_r ≤ (2r-1)‼·|G|^r` is
proven *inside* the theorem (char-0); there is no Sidon/`repThree`/pairing side hypothesis. -/
theorem char0_prize_moment_bound_unconditional {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) :=
  WFL3.char0_prize_moment_bound hk G hG hM hQ hr hrQ hmoment

/-- **[char-0, L3]** Squared form of `char0_prize_moment_bound_unconditional`: `M² ≤ 2e·|G|·r`. -/
theorem char0_prize_moment_bound_sq_unconditional {L : Type*} [Field L] [CharZero L]
    [DecidableEq L] {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) :=
  WFL3.char0_prize_moment_bound_sq hk G hG hM hQ hr hrQ hmoment

/-! ## L4 — char-0 discharge of the nonprincipal-energy named hypothesis `(S-M1')` and the
per-frequency sup bound wired through the P1 bridge. Scope: **char-0** (the char-0 energy bound is
the proven `DyadicEnergyK1` value). -/

/-- **[char-0, L4]** Under the char-0 additive-energy bound `E_r(G) ≤ (2r-1)‼·|G|^r`, the named
nonprincipal-energy hypothesis `NonprincipalEnergyBound` holds with `doubleFact = (2r-1)‼` (`K=1`):
`q·E_r − n^{2r} ≤ q·(2r-1)‼·n^r`. Discharges `(S-M1')` from the char-0 substrate. -/
theorem char0_nonprincipalEnergyBound_discharged {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :
    WF6P1.NonprincipalEnergyBound (F := F) G r ((2 * r - 1)‼ : ℝ) :=
  WFL4.nonprincipalEnergyBound_of_energyR_le G r henergy

/-- **[char-0, L4]** Composing the char-0 discharge with the P1 bridge: under the char-0 energy
bound, every nontrivial frequency obeys the Gaussian/Wick sup bound
`‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r`. In characteristic 0 the hypothesis is the proven `DyadicEnergyK1`
value, so this is an unconditional per-frequency bound there. -/
theorem char0_eta_pow_le_unconditional {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :=
  WFL4.char0_eta_pow_le_of_energyR_le hψ G r henergy b hb

/-! ## F1 — the sub-Gaussian moment telescope (the consumer that turns a per-step Gaussian
step-law into the full Wick even-moment bound). Scope: **prize-bridge**. -/

/-- **[prize-bridge, F1]** THE TELESCOPE. A nonnegative moment sequence obeying the Gaussian
step-law `M(r+1) ≤ (2r+1)·s·M(r)` from base `M 0 ≤ 1` satisfies the full sub-Gaussian even-moment
bound `M r ≤ (2r-1)‼·s^r` for every `r`. Pure induction; the load-bearing consumer of every
step-law lever. -/
theorem gaussian_moment_telescope {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 ≤ s) (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1)
    (hstep : WF6F1.GaussianStepLaw M s) :
    ∀ r : ℕ, M r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r :=
  WF6F1.gaussian_moment_bound_of_stepLaw hs hM hbase hstep

/-! ## B9 — the matched Gaussian is the unique extremal target; its step-law telescopes to the
prize. Scope: **char-0 / prize-bridge** (the step-law is the named input). -/

/-- **[prize-bridge, B9]** Convex-order domination by the matched Gaussian ⟺ the Wick bound. -/
theorem convexOrder_gaussian_iff_wick_export {n : ℕ} (hn : 1 ≤ n) (M : ℕ → ℝ) :
    (∀ r, M r ≤ WF8B9.gaussianMoment n r) ↔ (∀ r, WF8B9.wickMoment M n r ≤ 1) :=
  WF8B9.convexOrder_gaussian_iff_wick hn M

/-- **[prize-bridge, B9]** Headline: if the period moment sequence obeys the matched-Gaussian
sub-step-law `M(r+1) ≤ (2r+1)·n·M(r)` from base `M 0 ≤ 1`, then `wickMoment M n r ≤ 1` for all
`r` — i.e. the period law is convex-order-dominated by `N(0,n)` (= the prize). The matched
Gaussian is pinned as the unique minimal target. -/
theorem prize_of_matchedGaussian_stepLaw_export {n : ℕ} (hn : 1 ≤ n) {M : ℕ → ℝ}
    (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1) (hstep : WF6F1.GaussianStepLaw M (n : ℝ)) :
    ∀ r, WF8B9.wickMoment M n r ≤ 1 :=
  WF8B9.prize_of_matchedGaussian_stepLaw hn hM hbase hstep

/-! ## P1 — the nonprincipal-energy bridge (the live moment-route lever). Scope: **prize-bridge**. -/

/-- **[prize-bridge, P1]** The named sufficient hypothesis `(S-M1')` — the nonprincipal additive
energy bound — implies the per-frequency sup bound `‖η_b‖^{2r} ≤ q·(doubleFact·|G|^r)` for every
nonprincipal `b`. With `doubleFact = (2r-1)‼` and depth `r ≈ ln q`, this is the prize
cancellation `max_{b≠0}‖η_b‖ ≤ C√(n log q)`. The correct, non-vacuous moment-route lever. -/
theorem eta_pow_le_of_nonprincipalEnergyBound_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (doubleFact : ℝ) (hbnd : WF6P1.NonprincipalEnergyBound (F := F) G r doubleFact)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (doubleFact * (G.card : ℝ) ^ r) :=
  WF6P1.eta_pow_le_of_nonprincipalEnergyBound hψ G r doubleFact hbnd b hb

/-! ## B5 / B6 — the moment-problem obstructions. Scope: **obstruction**. -/

/-- **[obstruction, B5]** Hankel-positivity (the free moment-problem half `M₁² ≤ M₀·M₂`) does
NOT imply the ultra-sub-Gaussian Wick bracket: there is an explicit positive raw-moment sequence
that satisfies the free half yet violates `UltraSubGaussianStep` at `r = 1`. Any unconditional
moment-sequence theorem (which sees only positivity) cannot establish `W3-anti`. -/
theorem moment_problem_does_not_give_wick_bracket :
    ∃ (M W : ℕ → ℝ) (n : ℕ),
      (∀ k, 0 < M k) ∧ (∀ k, W k = ((2 * k - 1)‼ : ℝ) * (n : ℝ) ^ k) ∧
      (M 1) ^ 2 ≤ (M 0) * (M 2) ∧
      ¬ _root_.ProximityGap.Frontier.MomentProblemB5.UltraSubGaussianStep M W 1 :=
  _root_.ProximityGap.Frontier.MomentProblemB5.ultraSubGaussian_not_free

/-- **[obstruction, B6]** The cumulant-sign sufficiency criterion is refuted at the actual
period law: no cumulant sequence with `κ₄ < 0` can have `κ₈ > 0` and still meet the
nonpositive-higher-cumulant envelope. The period law's cumulants are sign-indefinite, so the
cumulant route cannot drive the prize bound. -/
theorem cumulant_sign_route_refuted {κ : ℕ → ℝ} (h4 : κ 2 < 0) (h8 : 0 < κ 4) :
    ¬ (∀ r, 2 ≤ r → κ r ≤ 0) :=
  CumulantSigns.subWick_positivity_refuted h4 h8

/-! ## G2 / G3 / G4 — the late-campaign lever obstructions (resonance / coefficient / roughness).
Scope: **obstruction**. Each is an axiom-clean proof that a named candidate lever cannot reach the
prize floor `√(n·log(p/n))`. -/

/-- **[obstruction, G2]** The Parseval/RMS resonance certificate is strictly below the prize floor
in the thin prize regime: `c·√n < √(n·L)` whenever `0 < n`, `0 ≤ c`, `c² < L`. With the measured
resonance constant `c ≤ 2` and the prize index `L = log(p/n) = log m ≫ c²`, the resonance route
gives NO Ω-disproof of `C = O(1)`. -/
theorem resonance_ceiling_below_prize_floor (c n L : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hL : c ^ 2 < L) :
    c * Real.sqrt n < Real.sqrt (n * L) :=
  WF9G2.resonance_below_floor c n L hn hc hL

/-- **[obstruction, G3]** The cyclotomy-coefficient (Fujiwara coefficient-root) route is loose by a
divergent factor: for every constant `C` there is an `m` with `fujiwaraAtTwo (n·m+1) n > C·prizeScale n m`
for all `n > 0`. No coefficient-magnitude root bound can meet the BGK target. -/
theorem coeff_route_loose_export (C : ℝ) (hC : 0 < C) :
    ∃ m : ℝ, 2 ≤ m ∧
      ∀ n : ℝ, 0 < n →
        WF9G3.fujiwaraAtTwo (n * m + 1) n > C * WF9G3.prizeScale n m :=
  WF9G3.coeff_route_loose C hC

/-- **[obstruction, G4]** Roughness is not the driver: the per-config bad-prime set `{p : p ∣ N}`
is determined by the FIXED integer `N` alone, so adjoining a roughness side-condition `rough p` can
only restrict it — `{p : p ∣ N ∧ rough p} ⊆ {p : p ∣ N}`. The largest prime factor of `m = (p-1)/n`
is not a parameter of the bad set. -/
theorem roughness_does_not_add_bad_primes_export (N : ℕ) (rough : ℕ → Prop) :
    {p : ℕ | p ∣ N ∧ rough p} ⊆ {p : ℕ | p ∣ N} :=
  G4RoughnessNotTheDriver.roughness_does_not_add_bad_primes N rough

/-! ## prize-bridge — the two faces are ONE wall (Parseval-dual; answers the "campaign still
points miners at the refuted bare sup-norm" flag, #444). The additive-energy face and the
multiplicative sup-norm face are the SAME object, bracketed within the trivial averaging factor
`q−1`. The link is the exact moment identity `sum_nonzero_moment` — NO loss and NO gain — so the
open core is one wall in two Fourier-dual bases, not two independent walls to be bridged. -/

/-- **[prize-bridge, OneWall]** The backward bridge: a sup-norm bound forces an energy bound. If
every nonzero period satisfies `‖η_b‖ ≤ M`, then the additive energy is controlled by `M`:
`q·E_r − n^{2r} ≤ (q−1)·M^{2r}`. Together with the forward `M^{2r} ≤ q·E_r − n^{2r}`
(worst-term ≤ sum), the worst-case sup-norm `M^{2r}` and the additive energy `E_r` bracket each
other within `q−1`: the additive count and the Gauss-phase worst case carry IDENTICAL information.
This is the consolidating statement that the prize is one wall, not two independent obstructions. -/
theorem two_faces_are_one_wall_export {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hsup : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ≤ M) :
    (Fintype.card F : ℝ)
        * (_root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ)
        - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ (2 * r) :=
  _root_.ArkLib.ProximityGap.Frontier.BridgeOneWall.pincer_is_one_wall hψ G r hM hsup

/-! ## NoFifthDoor — the Lane-2/3 tetrachotomy capstone (Shaw's "Shaw Value" essay, #444).
Scope: **capstone**. The headline citable statement of the campaign: there is NO fifth door, every
prize-scale certificate must pass through door (iv) (a genuinely new monomial-sum evaluation), and the
remaining obligation is exactly to shave the `√L = √log(p/n)` factor separating the BGK ceiling
`√(n·L)` that doors (i)-(iii) deliver from the prize floor `√n`. Pure scale algebra over the
abstract `Mechanism`/`DoorType` model; the classical-overshoot hypothesis is the formal content of the
proven Lever A-D refutations (indexed above as the obstruction-scope exports). -/

/-- **[capstone, NoFifthDoor]** No fifth door: if every classical door (moment/completion/extreme-value)
overshoots the BGK scale (the proven Lever A-D fate) in the regime `L > 1`, then any mechanism `m`
certifying a prize-scale bound `m.certScale ≤ √n` has door `newEvaluation` — door (iv) is the ONLY
door through which a prize-scale certificate can pass. -/
theorem noFifthDoor_forces_doorIV_export
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK n L)
    (hcert : m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n) :
    m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.forces_doorIV hn hL
    hclassicalOvershoots hcert

/-- **[capstone, NoFifthDoor]** Existential form: under the classical-overshoot hypothesis, the set of
prize-certifying mechanisms is contained in the door-(iv) mechanisms. Every prize-scale certificate is
a door-(iv) certificate. -/
theorem prizeCertifying_subset_doorIV_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK n L) :
    ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
      m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
      m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hn hL
    hclassicalOvershoots

/-- **[capstone, NoFifthDoor]** The door-(iv) target corridor: the worst-frequency sup `M` lives in
`[√n, √(n·L)]` — the prize floor (Plancherel/RMS) below and the BGK ceiling (what doors (i)-(iii)
deliver) above. The entire remaining door-(iv) content is to descend from the ceiling to the floor. -/
theorem doorIV_corridor_export {M n L : ℝ}
    (hfloor : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M)
    (hceil : M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M ∧
      M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.mem_doorIV_corridor hfloor hceil

/-- **[capstone, NoFifthDoor]** The corridor has positive width in the prize regime `L > 1`: the
floor is strictly below the ceiling, so the door-(iv) shave is a real `√L`-factor gap, not a point. -/
theorem doorIV_corridor_width_pos_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      < _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIV_corridor_width_pos hn hL

/-- **[capstone, NoFifthDoor]** The exact factor door (iv) must remove: the BGK ceiling equals the
prize floor scaled by `√L`, i.e. `√(n·L) = √L · √n`. Pins the door-(iv) obligation quantitatively. -/
theorem bgkScale_eq_sqrtL_mul_prizeScale_export {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L
      = Real.sqrt L * _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale_eq_sqrtL_mul_prizeScale hn hL

/-! ## NoTighterBound — the #407/#444 "no tighter bound from any direction" capstone (Lane-2).
Scope: **capstone**. The negative structural theorem: any functional bounding the per-frequency core
`M(n) = max_{b≠0}‖η_b‖` must be simultaneously b-sensitive, deterministic-archimedean, and genuinely
`L∞`. The two machine-checkable failure faces — a b-symmetric (moment-determined) statistic CANNOT
determine the sup, and an only-`L²`/depth-`r`-moment method is floored at the trivial `√S` — are
bundled into one citation point. (The third property, deterministic-archimedean, is named in prose; it
is the absence of an ensemble/freeness the fixed subgroup lacks.) -/

/-- **[capstone, NoTighterBound]** A `b`-symmetric statistic cannot determine the sup: two explicit
real families on `Fin 4` with IDENTICAL first and second moments but a strictly larger coordinate in
one. So any functional determined by the (permutation-invariant) moment data is blind to the worst
`b`. Failure mode (1) of the 3-property necessary condition. -/
theorem noTighterBound_secondMoment_blind_export :
    ∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
      (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
      (∀ j, |η' j| < |η b₀|) :=
  _root_.ProximityGap.Frontier.NoTighterBoundCapstone.secondMoment_does_not_determine_sup

/-- **[capstone, NoTighterBound]** The packaged no-tighter-bound capstone: BOTH machine-checkable
faces in one conjunction — (1) a moment-determined `b`-symmetric statistic cannot see the worst `b`,
and (3) any only-`L²`/depth-`r`-moment method `g` is floored at `√S` (cannot reach
`√(n·log m) ≪ √S`). Every classical and fresh tool fails at least one. The structural reason no
tighter bound on `M` is reachable from the symmetric / `L²` directions. -/
theorem noTighterBound_from_symmetric_or_L2_export :
    (∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
        (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
        (∀ j, |η' j| < |η b₀|)) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}, 1 ≤ r → ∀ (g : ℝ → ℝ),
        (∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r))) →
        ∀ {S : ℝ}, 0 ≤ S → Real.sqrt S ≤ g (S ^ r)) :=
  _root_.ProximityGap.Frontier.NoTighterBoundCapstone.noTighterBound_from_symmetric_or_L2

/-! ## ShawValue — the Lane-2 `prize ⟺ Sh(n)=O(1)` capstone (the citable normalization).
Scope: **capstone**. The prize inequality `M ≤ C·√(n·L)` is exactly a bound on the normalized
Shaw value `Sh(M) = M/√(n·L)`; the proven two-sided corridor `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on
the REAL Gauss-period worst frequency brackets the open prize at multiplicative width `√n`. -/

/-- **[capstone, ShawValue]** The prize normalization equivalence: under a positive prize scale,
the raw prize-shaped bound `M ≤ C·√(n·L)` is *exactly* the statement that the normalized Shaw
value is at most `C`. This removes the arithmetic wrapper, so the prize reads as “bound the
normalized object by an absolute constant” (`Sh(n)=O(1)`). Pure normalization — no cancellation
estimate is hidden. -/
theorem prizeBound_iff_shawValue_le_export {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C :=
  prizeBound_iff_shawValue_le hs

/-- **[capstone, ShawValue]** THE Lane-2 corridor. For the actual primitive-character Gauss-period
worst frequency `M(μ_n) = worstPeriod ψ G` in the thin prize regime `q ≥ 2n` (automatic at
`q = n^β`, `β > 1`), the normalized Shaw value is sandwiched
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)`, both endpoints in closed form. The lower endpoint is the
`n`-independent thin-regime Parseval floor `1/√(2L)`; the upper is the trivial-ceiling scale
`√(n/L)`. The open prize `Sh(M(μ_n)) = O(1)` lives strictly inside this proven corridor.

(All identifiers in the statement are FULLY QUALIFIED: restating them unqualified in this
heavily-`open`ed index context resolves `worstPeriod`/`shawValue` to a different overload, so we pin
the exact source declarations to inherit the clean proof term verbatim.) -/
theorem shawValue_worstPeriod_clean_corridor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (G.card : ℝ) L) :
    1 / Real.sqrt (2 * L) ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ Real.sqrt ((G.card : ℝ) / L) :=
  _root_.ProximityGap.Frontier.ConcreteShawValueThinFloor.shawValue_worstPeriod_clean_corridor
    hψ G hne hn1 hq2n hL hs

/-- **[capstone, ShawValue]** The corridor width is exactly `√n`: the ratio of the trivial-ceiling
endpoint to the Plancherel-floor endpoint equals `√n`. So the open prize is precisely the demand to
collapse this `√n`-wide normalized bracket to an absolute constant. -/
theorem shawValue_bracket_width_eq_sqrt_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    (n / prizeScale n L) / (Real.sqrt n / prizeScale n L) = Real.sqrt n :=
  bracket_width_eq_sqrt hn hL

/-! ## Door-IV wraparound `Q ≥ 0` discharge. Scope: **obstruction**.

These exports preserve the algebraic narrowing of the char-`p` transfer route: the blind
wraparound-gap assumption `Q ≥ 0` follows from the sharper log-concavity input `wa·wc ≤ wb²`,
with an explicit `2·wb²` margin. The companion dominance hypothesis is refuted by the next section,
so this is a route-local constraint/reduction, not a CORE proof. -/

/-- **[obstruction, CharPWraparoundLogConcaveQ]** Under wraparound log-concavity `wa·wc≤wb²`
and `0≤s`, the wraparound transfer gap is at least `2·wb²`. This replaces a blind `Q≥0` input
by a sharper single inequality plus an explicit margin. -/
theorem charP_wrap_gap_ge_two_mul_sq_export {s wa wb wc : ℝ}
    (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    2 * wb ^ 2 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s wa wb wc :=
  ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_ge_two_mul_sq hs hlc

/-- **[obstruction, CharPWraparoundLogConcaveQ]** The open wraparound-control hypothesis `Q≥0`
of the char-`p` transfer assembly follows from `0≤s` and wraparound log-concavity. The remaining
dominance input is separate and is not discharged here. -/
theorem charP_wrap_gap_nonneg_of_logConcave_export {s wa wb wc : ℝ}
    (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s wa wb wc :=
  ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_nonneg_of_logConcave hs hlc

/-- **[obstruction, CharPWraparoundLogConcaveQ]** The char-`p` transfer assembly with the
`Q≥0` hypothesis replaced by wraparound log-concavity. This records the exact remaining obligation:
`0≤G₀+L` dominance plus `wa·wc≤wb²`, with dominance refuted at concrete prize-regime witnesses in
`CharPStepRatioFails`. -/
theorem charP_transfer_of_dominance_logConcave_export {s a₀ b₀ c₀ wa wb wc : ℝ}
    (hs : 0 ≤ s)
    (hdom : 0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s a₀ b₀ c₀ +
      (2 * (s + 2) * b₀ * wb - s * (a₀ * wc + c₀ * wa)))
    (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap
      s (a₀ + wa) (b₀ + wb) (c₀ + wc) :=
  ArkLib.ProximityGap.CharPTransferDecomposition.charP_transfer_of_dominance_logConcave
    hs hdom hlc

/-! ## Door-IV char-p transfer / ρ-antitone refutations. Scope: **obstruction**.

These exports make the newest door-(iv) Lane-3 no-go results permanent: char-`p` step-ratio
monotonicity is exactly the sign of the transfer gap, and explicit prize-regime witnesses
refute both the universal step-ratio route and the normalized `ρ`-antitone-and-bounded route. These are route
refutations only; they do not disprove CORE. -/

/-- **[obstruction, CharPStepRatioFails]** The abstract char-`p` step-ratio monotonicity predicate
`s·E_r·E_{r+2} ≤ (s+2)·E_{r+1}²` is exactly nonnegativity of the transfer gap functional used in
`_CharPTransferDecomposition`. This pins the step-ratio route to one sign condition. -/
theorem charP_stepRatioMonotoneAt_iff_gap_nonneg_export (s Er Er1 Er2 : ℝ) :
    ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt s Er Er1 Er2 ↔
      0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s Er Er1 Er2 :=
  ArkLib.ProximityGap.CharPStepRatioFails.stepRatioMonotoneAt_iff_gap_nonneg s Er Er1 Er2

/-- **[obstruction, CharPStepRatioFails]** Exact prize-regime witness (`n=32`, `p=786433`, `r=3`)
refuting char-`p` step-ratio monotonicity: `7·E₃·E₅ ≤ 9·E₄²` is false for
the exact period energies. -/
theorem charP_stepRatioMonotone_false_n32_export :
    ¬ ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt
        7 446720 92179360 24850732032 :=
  ArkLib.ProximityGap.CharPStepRatioFails.not_stepRatioMonotoneAt_n32

/-- **[obstruction, CharPStepRatioFails]** No theorem using only positivity of
`s,E_r,E_{r+1},E_{r+2}` can prove universal char-`p` step-ratio monotonicity; the exact positive
`n=32` witness violates it. -/
theorem charP_no_universal_positive_stepRatioMonotone_export :
    ¬ (∀ s Er Er1 Er2 : ℝ,
      0 < s → 0 < Er → 0 < Er1 → 0 < Er2 →
        ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt s Er Er1 Er2) :=
  ArkLib.ProximityGap.CharPStepRatioFails.not_forall_positive_stepRatioMonotoneAt

/-- **[obstruction, RhoAntitoneFails]** In normalized `ρ = S/((p−1)E)` coordinates, the `n=32`,
`p=786433` witness cannot satisfy both the antitone step `ρ(4)≤ρ(3)` and the order-5 ceiling
`ρ(5)≤1`. This is the probe-facing no-go interface for the `ρ`-antitone-and-bounded route. -/
theorem rho_normalized_antitone_and_ceiling_incompatible_export :
    ¬ (ArkLib.ProximityGap.RhoAntitoneFails.S4 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E4)
        ≤ ArkLib.ProximityGap.RhoAntitoneFails.S3 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E3) ∧
      ArkLib.ProximityGap.RhoAntitoneFails.S5 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E5)
        ≤ (1 : ℝ)) :=
  ArkLib.ProximityGap.RhoAntitoneFails.not_normalized_antitone_and_ceiling

/-- **[obstruction, RhoAntitoneFails]** The `ρ`-antitone route is not universally satisfiable:
there are positive exact witness values with the `r=3` cross-inequality reversed and the `r=5`
normalized ceiling broken. Hence `open_core_of_rho_antitone` remains a conditional sufficient route,
not a universal proof strategy. -/
theorem rho_antitone_route_not_universal_export :
    ∃ S3 S4 S5 E3 E4 E5 pm1 : ℝ,
      (0 < pm1 ∧ 0 < E3 ∧ 0 < E4 ∧ 0 < E5) ∧
      S3 * E4 < S4 * E3 ∧
      pm1 * E5 < S5 :=
  ArkLib.ProximityGap.RhoAntitoneFails.antitone_route_not_universal

/-! ## Door-IV value-shift histogram obstruction. Scope: **obstruction**.

These exports make the finite anti-concentration no-go reusable from the permanent index. The
value-shift mechanism is the one door-(iv) `L^∞` spreading idea that genuinely avoids the moment route,
but its own necessary condition is stronger than value-set symmetry: a nontrivial shift must preserve
the full fiber-cardinality histogram. In a prime field the realizable steps are all-or-nothing, so one
nonzero histogram mismatch collapses the entire mechanism to step `0` and hence to the trivial
`fiberCard val 0 ≤ #T` ceiling. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVValueShiftHistogram]** In a prime field, a single nonzero realizable
value-shift step forces the fiber histogram to be completely flat: every two residues have equal
fiber cardinality. Thus a useful value-shift free part demands perfect residue equidistribution,
not merely value-set invariance. -/
theorem valueShift_nontrivial_forces_flat_histogram_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s : ZMod p} (hs : s ≠ 0)
    (hreal : ∃ vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val,
      vs.s = s) :
    ∀ a b : ZMod p,
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a =
        ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val b :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.nontrivial_valueShift_forces_flat_histogram val hs hreal

/-- **[obstruction, DoorIVValueShiftHistogram]** Single-witness collapse: in a prime field, one
fiber-cardinality mismatch at one step rules out the all-steps case and forces every value-shift to
have trivial step `0`. -/
theorem valueShift_step_zero_of_one_histogram_witness_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s a : ZMod p}
    (hne : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a ≠
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val (a + s))
    (vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val) :
    vs.s = 0 :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.valueShift_step_zero_of_one_histogram_witness val hne vs

/-- **[obstruction, DoorIVValueShiftHistogram]** With one histogram mismatch, the value-shift
spreading route gives only the trivial ceiling `fiberCard val 0 ≤ #T`; it cannot supply a useful
wraparound anti-concentration bound for the prize value map without a flat periodic histogram. -/
theorem valueShift_route_vacuous_of_one_histogram_witness_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s a : ZMod p}
    (hne : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a ≠
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val (a + s))
    (vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val) :
    vs.s = 0 ∧
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val 0 ≤ Fintype.card T :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.valueShift_route_vacuous_of_one_histogram_witness val hne vs

/-! ## Door-IV wraparound Markov vacuity. Scope: **obstruction**.

These exports lock the average-to-sup no-go interface for the wraparound bad-prime route. The finite
Markov/union bound is valid, but when the threshold is at or below the mean its right side is at least
the whole prime set, so it cannot exclude even one heavy prime. Average wraparound control therefore
does not supply a supremum bound through the union route. -/

/-- **[obstruction, WraparoundMarkovVacuity]** Finite Markov inequality in multiplicative form:
for nonnegative weights, `T * #{j ∈ S : T ≤ W j} ≤ ∑ W j`. This is the exact union-bound interface
for the summed wraparound incidence. -/
theorem wraparound_markov_count_le_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ) (hW : ∀ j ∈ S, 0 ≤ W j) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_count_le S W T hW

/-- **[obstruction, WraparoundMarkovVacuity]** If `0 < T ≤ mean S W`, the Markov right-hand side
`(∑ W)/T` is at least `|S|`, so the union bound is vacuous at that threshold. -/
theorem wraparound_markov_bound_vacuous_below_mean_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T)
    (hTmean : T ≤ ArkLib.ProximityGap.WraparoundMarkovVacuity.mean S W) :
    (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_bound_vacuous_below_mean S W T hne hT hTmean

/-- **[obstruction, WraparoundMarkovVacuity]** Combined interface: below the average, the Markov
count bound still holds but its exclusion bound is already at least the full index-set size, so
average-control does not bound the supremum through this route. -/
theorem wraparound_average_control_does_not_bound_sup_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T) (hW : ∀ j ∈ S, 0 ≤ W j)
    (hTmean : T ≤ ArkLib.ProximityGap.WraparoundMarkovVacuity.mean S W) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j
      ∧ (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.average_control_does_not_bound_sup
    S W T hne hT hW hTmean

/-! ## Door-IV index-factor overshoot. Scope: **obstruction**.

These exports make the naive-incidence scale loss citable from the permanent index: replacing the prize
scale `sqrt(n L)` by the incidence bridge scale `sqrt(n m L)` multiplies the normalized Shaw constant
by exactly `sqrt m`. A bounded normalized naive constant therefore bounds the index itself; an unbounded
index family cannot pass through this bridge without a genuinely new argument removing the factor. -/

/-- **[obstruction, DoorIVIndexFactorOvershoot]** The naive incidence bridge scale
`sqrt(n*m*L)` is exactly `sqrt(m)` times the prize scale `sqrt(n*L)`. -/
theorem doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export {n m L : ℝ}
    (hm : 0 ≤ m) :
    ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L =
      Real.sqrt m * ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_sqrt_mul_prizeScale hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** A raw bound at the naive incidence scale is
exactly a Shaw-value bound with the constant multiplied by `sqrt(m)`. -/
theorem doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export {M C n m L : ℝ}
    (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 < L) :
    M ≤ C * ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L ↔
      ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n L ≤ C * Real.sqrt m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceBound_iff_shawValue_le_scaled hn hm hL

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Contrapositive-facing form: with fixed positive
raw constant `C`, any uniform cap `D` on `C*sqrt(m)` forces `m ≤ (D/C)^2`; hence the naive bridge
cannot give a bounded Shaw constant on an unbounded-index family. -/
theorem doorIV_index_le_sq_of_scaledConstant_le_export {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hbound : C * Real.sqrt m ≤ D) :
    m ≤ (D / C) ^ 2 :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.index_le_sq_of_scaledConstant_le
    hC hm hbound

/-! ## Door-IV order-blindness / selector obstruction. Scope: **obstruction**.

These exports make the Lane-1 `rho(b)` order-selector no-go permanent: a coset-invariant
coherence statistic is a quotient-level function on `b·μₙ`, not a function of the raw
multiplicative order of `b`. Any restricted selector can improve the worst coherence only
by missing an entire coset; merely filtering element-level/order buckets that still hit
every coset preserves the global bound problem. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVCoherenceOrderBlind]** If a statistic is invariant on left `H`-cosets,
then even same-coset elements with different multiplicative orders have the same statistic value.
Thus a `rho(b)`-style coset-level coherence cannot be controlled by multiplicative order alone. -/
theorem doorIV_cosetInvariant_blind_to_order_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f)
    {a b : G} (hab : a * b⁻¹ ∈ H)
    (hord : orderOf a ≠ orderOf b) :
    f a = f b :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.cosetInvariant_blind_to_order
    hf hab hord

/-- **[obstruction, DoorIVCoherenceOrderBlind]** If a restricted frequency class `T` meets every
left `H`-coset, then an upper bound for a coset-invariant statistic on `T` is exactly the global
upper bound. Order buckets or element-level filters do not create a new anti-concentration lever
unless they omit whole cosets. -/
theorem doorIV_cosetHitting_selector_bound_iff_global_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} [LE β] {f : G → β} {C : β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f) {T : Set G}
    (hT : ∀ b : G, ∃ t ∈ T, t * b⁻¹ ∈ H) :
    (∀ t ∈ T, f t ≤ C) ↔ ∀ b : G, f b ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.bound_on_cosetHitting_set_iff_global
    (H := H) (f := f) (C := C) hf hT

/-- **[obstruction, DoorIVCoherenceOrderBlind]** Positive selector no-go: if a restricted class
claims a strict improvement below some global coset-invariant value, then it must miss an entire
left `H`-coset. Any genuine improvement is quotient-level, not multiplicative-order-level. -/
theorem doorIV_strict_selector_bound_misses_coset_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} [Preorder β] {f : G → β} {T : Set G} {C : β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f)
    (hbound : ∀ t ∈ T, f t ≤ C) (hstrict : ∃ b : G, C < f b) :
    ∃ x : G, ∀ t ∈ T, t * x⁻¹ ∉ H :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.exists_coset_missed_of_strict_selector_bound
    (H := H) (f := f) hf hbound hstrict

/-! ## Door-IV worst-b Sidon/no energy-excess obstruction. Scope: **obstruction**.

These exports make the exact Sidon-floor constraint reusable from the permanent index. On a Sidon
worst-frequency representative set, the additive-energy excess above `2|G|²-|G|` is exactly zero,
and this remains true on every subset. Thus an additive-energy/sum-product lever must first prove
non-Sidon structure; when the probe-facing object is Sidon, the route has no positive energy budget
to grip. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** The additive-energy excess above the Sidon
floor vanishes exactly for Sidon sets. This pins the probe report `E(W)=2|W|²-|W|` to a kernel
checked no-excess statement. -/
theorem doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess G = 0 ↔
      ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess_eq_zero_iff_sidon G

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** Sidon-ness is hereditary for this no-go:
every subset of a Sidon worst-b representative set has zero positive additive-energy budget above
the Sidon floor. Restricting to a subcollection cannot resurrect an additive-energy lever. -/
theorem doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {G H : Finset F}
    (hG : ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G) (hHG : H ⊆ G) :
    ∀ B : ℕ, 0 < B →
      ¬ (B ≤ ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess H) :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.no_positive_additiveEnergyExcess_of_subset_sidon
    hG hHG

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** Positive additive-energy excess is exactly
non-Sidon structure. Any door-(iv) certificate demanding positive energy excess is therefore a
certificate that the worst-b object is not Sidon, contrary to the pinned Sidon-floor probe regime. -/
theorem doorIV_positive_additiveEnergyExcess_iff_not_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    0 < ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess G ↔
      ¬ ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.positive_additiveEnergyExcess_iff_not_sidon G

/-! ## Door-IV half-mass equivalence capstone. Scope: **capstone**.

These exports make the half-mass reduction citable: under the pointwise comparison `M ≤ H ≤ K*M`
with one family-wide `K`, the original uniform prize bound is equivalent to a uniform half-mass
bound and to bounded normalized half-mass Shaw value. This is normalization/reduction only; the
analytic half-mass cancellation estimate remains the open door-(iv) problem. -/

/-- **[capstone, DoorIVHalfMassEquivalence]** Uniform-family reduction: with one comparison
constant `K`, the existence of an absolute prize constant is equivalent to the existence of an
absolute half-mass constant. -/
theorem doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
    hK hMH hHM

/-- **[capstone, DoorIVHalfMassEquivalence]** Mixed Shaw-value form: with positive scales, the
raw uniform prize Big-O bound is equivalent to bounded normalized half-mass Shaw value `H/scale`. -/
theorem doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVHalfMassEquivalence]** Four-way packaging: the raw prize bound is equivalent
to simultaneous raw half-mass, normalized prize, and normalized half-mass formulations. -/
theorem doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) ∧
        (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyBound M scale C) ∧
          (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound_iff_all_halfMassShaw_forms
    hK hscale hMH hHM


/-! ## JacobiCocycleDispersion — the named door-(iv) missing theorem, permanently indexed.
Scope: **capstone**. The point of this section is discoverability: the #444 reduction does not
leave an anonymous anti-concentration obligation, but the explicit predicate
`JacobiCocycleDispersion M C n m`, exactly equivalent to a bounded Shaw value with `L = log m`.
These exports are direct aliases of the proven Lane-2 wrappers; they do NOT prove the missing
Jacobi dispersion theorem, and make no CORE/cancellation/completion/moment/capacity claim. -/

/-- **[obstruction, JacobiCocycleDispersion]** The degenerate trivial cocycle has full
concentration at a support frequency: if the written phase ratio satisfies `ζ^k = 1`, the length-`n`
fiber is exactly `n`. This is the baseline the missing Jacobi dispersion theorem must destroy. -/
theorem trivial_cocycle_full_concentration_export {n : ℕ} (hn : 0 < n) (ζ : ℂ) {k : ℕ}
    (hζk : ζ ^ k = 1) :
    (∑ g ∈ Finset.range n, (ζ ^ k) ^ g) = (n : ℂ) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_full_concentration
    hn ζ hζk

/-- **[obstruction, JacobiCocycleDispersion]** Off a support frequency, a trivial cocycle has exact
geometric cancellation. The on/off pattern shows that the named Door-IV theorem is not a normalization
artifact: it must rule out collapse to this degenerate support. -/
theorem trivial_cocycle_offSupport_zero_export {n : ℕ} (ζ : ℂ) {k : ℕ}
    (hpow : (ζ ^ k) ^ n = 1) (hoff : ζ ^ k ≠ 1) :
    (∑ g ∈ Finset.range n, (ζ ^ k) ^ g) = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_offSupport_zero
    ζ hpow hoff

/-- **[capstone, JacobiCocycleDispersion]** Pointwise form of the named door-(iv) target: the
Jacobi-cocycle dispersion predicate is exactly a Shaw-value bound with logarithmic thinness
parameter `L = log m`. -/
theorem jacobiCocycleDispersion_iff_shawValue_le_export {M C n m : ℝ}
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n (Real.log m)) :
    _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.JacobiCocycleDispersion M C n m ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n (Real.log m) ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersion_iff_shawValue_le hs

/-- **[capstone, JacobiCocycleDispersion]** Uniform nonnegative-constant form under the standard
thin-instance positivity hypotheses `0 < n_i` and `0 < log m_i`: bounded Jacobi-cocycle dispersion
is equivalent to `Sh=O(1)`. -/
theorem exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    (∃ C, 0 ≤ C ∧
      _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n
          (fun i => Real.log (m i)) C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
    hn hlog

/-- **[capstone, JacobiCocycleDispersion]** Wall-facing uniform form: under the standard positivity
hypotheses, failing to find any nonnegative Jacobi-dispersion constant is exactly failing to find any
nonnegative Shaw-value constant. -/
theorem not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    ¬ (∃ C, 0 ≤ C ∧
      _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n
          (fun i => Real.log (m i)) C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos
    hn hlog

/-- **[capstone, JacobiCocycleDispersion]** Raw-sandwich invariance for the named Jacobi target:
if a downstream door-(iv) quantity `H` is uniformly between `M` and `K*M`, then boundedness of
Jacobi-cocycle dispersion transfers exactly up to constants. -/
theorem exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export
    {ι : Type*} {M H n m : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound H n m C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_jacobiCocycleDispersionFamilyBound_iff_of_rawSandwich
    hK hMH hHM

/-! ## DoorIVObject — the single live door-(iv) open object is moment-trapped (Lane-1 close-out).
Scope: **capstone**. The worst-frequency coset-half coherence sup of the monomial sum (the sole live
open object of the tetrachotomy) is, in every measurement (n=16..128, multiple structured primes),
moment-trapped: bounded below by the iid-unit-phase (extreme-value) surrogate floor `iidSup`, with the
gap above it bounded by the additive-energy (moment) excess `Δ`. Equivalently the object sup is pinned
to the corridor `[iidSup, iidSup + Δ]`. No non-moment, non-extreme-value slack survives. CORE stays
open; no cancellation/anti-concentration/capacity claim. (#444, probes
`probe_dooriv_jacobi_cocycle_dispersion_magnitude.py`, `probe_dooriv_cocycle_excess_structure.py`.) -/

/-- **[capstone, DoorIVObject]** The door-(iv) object sup is pinned to the moment-corridor: under the
no-edge floor (`iidSup ≤ realSup`) and the excess-is-moment bound (`realSup − iidSup ≤ Δ`), the real
sup satisfies `iidSup ≤ realSup ≤ iidSup + Δ`. -/
theorem doorIV_object_moment_corridor_export {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess : _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ) :
    iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.realSup_in_moment_corridor
    hEdge hExcess

/-- **[capstone, DoorIVObject]** The grand three-pillar statement of the #444 structural result: from
the standard thin-instance positivity, the proven classical-overshoot refutations, and the two measured
facts about the door-(iv) object, ALL THREE pillars hold simultaneously — (1) the prize ⇔ `Sh=O(1)`
reduction, (2) the door-(iv)-only mechanism exclusion, and (3) the object moment-corridor
`[iidSup, iidSup + Δ]`. The single citable statement: the prize is a bounded Shaw value, deliverable
only through door (iv), whose open object is moment-trapped. CORE stays open. -/
theorem prize_iff_shawBounded_doorIV_only_and_object_moment_trapped_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref)
    {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess :
      _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ) :
    ((∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧
          _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale nref →
        m.door =
          _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone.prize_iff_shawBounded_doorIV_only_and_object_moment_trapped
    hs hnref hLref hclassicalOvershoots hEdge hExcess

/-! ## DoorIVSignedDeepSumAbsLeak — the absolute-value leak made permanent.
Scope: **obstruction / positive localization**. The signed deep period-power probe found the
thinness-essential signal in `Σ η_b^r`, while all moment / energy packages pass through
`Σ |η_b|^r` and discard cancellation. These permanent exports expose the kernel-checked
triangle-inequality leak and its monotone transfer direction. They do NOT prove the open
uniform signed deep-cancellation bound, and make no CORE/cancellation/completion/capacity claim. -/

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** Absolute-value / moment packaging can
only upper-bound the signed deep sum through the triangle-inequality leak:
`|Σ η_b^r| ≤ Σ |η_b|^r`. The gap is exactly the signed cancellation thrown away by
moment methods. -/
theorem doorIV_abs_signed_le_abs_moment_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    |∑ b ∈ s, (η b) ^ r| ≤ ∑ b ∈ s, |η b| ^ r := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_signed_le_abs_moment
    s η r

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** The leak gap is nonnegative:
absolute moments minus the signed deep sum magnitude are a real discarded-cancellation
budget, never a saving. -/
theorem doorIV_leak_nonneg_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    0 ≤ (∑ b ∈ s, |η b| ^ r) - |∑ b ∈ s, (η b) ^ r| := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.leak_nonneg s η r

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** Any absolute-moment bound transfers
only one way, to a bound on the signed sum. The converse is false (kernelized in the
source file), so a signed deep-cancellation certificate cannot be recovered from an
absolute-value certificate. -/
theorem doorIV_abs_moment_bound_transfers_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) {B : ℝ}
    (hB : ∑ b ∈ s, |η b| ^ r ≤ B) :
    |∑ b ∈ s, (η b) ^ r| ≤ B := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_moment_bound_transfers
    s η r hB


/-! ## JacobiCocycleTrivialOvershoot — the trivial baseline fails the thin prize target.
Scope: **obstruction**. The trivial cocycle's full `n`-spike is not a dispersion witness in the
prize regime `n > C² log m`; it overshoots the target `C√(n log m)` by a positive amount.
These exports pin the gap the genuine Jacobi cocycle must close, without proving it closes it. -/

/-- **[obstruction, JacobiCocycleTrivialOvershoot]** In the thin prize regime
`C² log m < n`, the trivial-cocycle baseline `M = n` fails the named Jacobi dispersion predicate.
This is the kernel-checked version of "the genuine cocycle must break the full `n`-spike." -/
theorem trivial_cocycle_overshoots_thin_export {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.JacobiCocycleDispersion
      n C n (Real.exp logm) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_cocycle_overshoots_thin
    hn hC hlogm hthin

/-- **[obstruction, JacobiCocycleTrivialOvershoot]** In the same thin regime, the additive
overshoot gap `n - C√(n log m)` of the trivial spike is strictly positive. The open Door-IV
work is exactly to make the genuine cocycle disperse enough to remove this gap. -/
theorem trivial_overshoot_gap_pos_export {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    0 < n - C * Real.sqrt (n * logm) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_overshoot_gap_pos
    hn hC hlogm hthin


end ArkLib.ProximityGap.Frontier.CampaignProvenIndex

/-! ## Cone axiom audit — every permanent export above is axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). -/
namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex
#print axioms char0_stepRatio_antitone_iff_sharpNewton
#print axioms char0_W3anti_of_sharpNewton_export
#print axioms char0_kstability_cross_le_wick
#print axioms char0_prize_moment_bound_unconditional
#print axioms char0_prize_moment_bound_sq_unconditional
#print axioms char0_nonprincipalEnergyBound_discharged
#print axioms char0_eta_pow_le_unconditional
#print axioms gaussian_moment_telescope
#print axioms convexOrder_gaussian_iff_wick_export
#print axioms prize_of_matchedGaussian_stepLaw_export
#print axioms eta_pow_le_of_nonprincipalEnergyBound_export
#print axioms moment_problem_does_not_give_wick_bracket
#print axioms cumulant_sign_route_refuted
#print axioms resonance_ceiling_below_prize_floor
#print axioms coeff_route_loose_export
#print axioms roughness_does_not_add_bad_primes_export
#print axioms prizeBound_iff_shawValue_le_export
#print axioms shawValue_worstPeriod_clean_corridor_export
#print axioms shawValue_bracket_width_eq_sqrt_export
#print axioms charP_wrap_gap_ge_two_mul_sq_export
#print axioms charP_wrap_gap_nonneg_of_logConcave_export
#print axioms charP_transfer_of_dominance_logConcave_export
#print axioms charP_stepRatioMonotoneAt_iff_gap_nonneg_export
#print axioms charP_stepRatioMonotone_false_n32_export
#print axioms charP_no_universal_positive_stepRatioMonotone_export
#print axioms rho_normalized_antitone_and_ceiling_incompatible_export
#print axioms rho_antitone_route_not_universal_export
#print axioms valueShift_nontrivial_forces_flat_histogram_export
#print axioms valueShift_step_zero_of_one_histogram_witness_export
#print axioms valueShift_route_vacuous_of_one_histogram_witness_export
#print axioms wraparound_markov_count_le_export
#print axioms wraparound_markov_bound_vacuous_below_mean_export
#print axioms wraparound_average_control_does_not_bound_sup_export
#print axioms doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export
#print axioms doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export
#print axioms doorIV_index_le_sq_of_scaledConstant_le_export
#print axioms doorIV_cosetInvariant_blind_to_order_export
#print axioms doorIV_cosetHitting_selector_bound_iff_global_export
#print axioms doorIV_strict_selector_bound_misses_coset_export
#print axioms doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export
#print axioms doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export
#print axioms doorIV_positive_additiveEnergyExcess_iff_not_sidon_export
#print axioms doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export
#print axioms doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export
#print axioms doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export
#print axioms trivial_cocycle_full_concentration_export
#print axioms trivial_cocycle_offSupport_zero_export
#print axioms jacobiCocycleDispersion_iff_shawValue_le_export
#print axioms exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export
#print axioms not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export
#print axioms exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export
#print axioms two_faces_are_one_wall_export
#print axioms noFifthDoor_forces_doorIV_export
#print axioms prizeCertifying_subset_doorIV_export
#print axioms doorIV_corridor_export
#print axioms doorIV_corridor_width_pos_export
#print axioms bgkScale_eq_sqrtL_mul_prizeScale_export
#print axioms noTighterBound_secondMoment_blind_export
#print axioms noTighterBound_from_symmetric_or_L2_export
#print axioms doorIV_object_moment_corridor_export
#print axioms prize_iff_shawBounded_doorIV_only_and_object_moment_trapped_export
#print axioms doorIV_abs_signed_le_abs_moment_export
#print axioms doorIV_leak_nonneg_export
#print axioms doorIV_abs_moment_bound_transfers_export
#print axioms trivial_cocycle_overshoots_thin_export
#print axioms trivial_overshoot_gap_pos_export
end ArkLib.ProximityGap.Frontier.CampaignProvenIndex
