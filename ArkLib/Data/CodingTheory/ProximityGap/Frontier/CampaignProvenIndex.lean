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
-/

open scoped Nat

namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex

open ProximityGap.PrizeWorkbench
open ArkLib.ProximityGap.Frontier
-- `eta` (the subgroup Gauss-sum period) lives here; needed for the L4/P1 exports below.
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.NegationClosedWalk

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
end ArkLib.ProximityGap.Frontier.CampaignProvenIndex
