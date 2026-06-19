# δ* (#444) — State of the Prize: the single open core, all equivalent forms, and why each is open

A consolidated map (2026-06-19). The prize is **open**, **believed true**, and reduces — across ~70 distinct
attacks plus a parallel agent converging independently — to **one** equivalent open statement. This document is
the map: the core, every equivalent form, the two-obstruction pincer, and the precise refutation mechanism for
each major route. It claims **no closure**; it is the honest cartography of a real wall.

## 0. The prize floor, formalized end-to-end modulo ONE inequality

`_ProveAssemblyConcrete.period_le_prizeFloor` (axiom-clean): for the actual Gauss period `η_b = Σ_{x∈μ_n}e_p(bx)`,
every nonzero `b` obeys `‖η_b‖ ≤ √e·√(2r·n)` (= the prize floor at `r ≈ log q`) **assuming only**
```
hEnergy :  rEnergy(μ_n, r) ≤ (2r·n)^r   over F_p,  at r ≈ log p,  n = 2^30,  p ≈ n·2^128  (n ≈ p^{0.19}).
```
The char-0 version is PROVEN in Lean (`gaussianEnergyBound_dyadic`, requires `[CharZero F]`). **The entire prize
= delete `[CharZero F]`** — prove the energy bound over `F_p` at the saddle depth. Everything downstream
(energy ⟹ sup-norm floor ⟹ δ* window interior, + the necessity half, + the unconditional bracket) is formalized
axiom-clean (`_DeltaStarDefinitive`, `bgkFloor_interior_reach`, `moment_route_insufficient`, `deltaStar_bracket`).

> **DC-subtraction correction (read this before attacking §0/§1 — supersedes the raw form above).** The
> hypothesis `hEnergy : E_r(μ_n;F_p) ≤ (2r·n)^r` as written is on the **DC-included** raw energy `E_r`, and that
> exact bound is **provably FALSE at prize scale**: the proven DC lower bound `E_r ≥ n^{2r}/q`
> (`DCEnergyEssential.energy_ge_dc`) gives `E_r ≥ 2^{6442} ≫ (2r·n)^r = 2^{4156}` at `n=2^30, p≈2^158, r≈110`
> (and already for every `r ≥ 8`) — formalized as `DCEnergyEssential.not_gaussianEnergyBound_of_deep`. The genuine
> open core is the **DC-subtracted** moment `S_r = q·E_r − n^{2r} = Σ_{b≠0}‖η_b‖^{2r} ≤ (q−1)·Wick`, which IS
> satisfiable/open. `period_le_prizeFloor`'s proof already uses only this (it drops the DC term `n^{2r} ≥ 0`); only
> its *stated* hypothesis is the too-strong raw form. The corrected residual is carried axiom-clean by
> `_ProveAssemblyConcreteDC.period_le_prizeFloor_dc` (via `DCSubtractedMoment.sum_nonzero_moment`; predicate
> `DCEnergyCorrection.DCEnergyBound`). Read every "char-p energy `E_r ≤ Wick`" below (incl. §1 row 1) as the
> DC-subtracted `S_r ≤ (q−1)·Wick`. (This is the canonical form per the cone `CLAUDE.md`; the raw `(2r·n)^r`
> framing above is the pre-correction shorthand.)

## 1. The single open core (all of these are EQUIVALENT — proven or argued so)

| form | statement | where shown equivalent |
|---|---|---|
| **char-p energy** (DC-subtracted, see §0 correction) | `S_r = q·E_r − n^{2r} ≤ (q−1)·(2r−1)‼·n^r` at `r≈log p` | the core; `_OpenCoreMonotoneReduction`, `_ProveAssemblyConcreteDC` |
| **BGK / Paley** | `M = max_{b≠0}‖η_b‖ ≤ C√(n log m)`, exponent 1/2 | `_MomentSaddleValue`, generalized-Paley eigenvalue |
| **Λ(q) set** | `μ_n` is Λ(q) with bounded const at `q≈log m` | `_LambdaQMeanZeroEnergy` (even-q Λ(q)=energy); Pisier iff = Sidon |
| **sub-Gaussian** | the n/2 antipodal phases are sub-Gaussian, proxy n | `_ArcsineIIDFraming` |
| **Jacobi-cocycle dispersion** | projective char of ℤ/n w/ Jacobi-sum cocycle disperses | `_JacobiCocycleDispersion`, `_JacobiMomentIdentity` |
| **wraparound variance** | the wraparound `W_r` fluctuation (random mean DC-cancelled) ≤ slack | `probe_wraparound_correction` |

The campaign's `_BridgeOneWall` proves the additive-energy face and the multiplicative-sup face **bracket each
other within q−1** — they are ONE object in two Fourier-dual bases; "bridging" them is a tautology.

## 2. The two-obstruction PINCER (why everything reduces)

Every approach hits at least one jaw, and a proof must escape BOTH; nothing does (`_BridgeOneWall`,
`_FrontierSheafConductor`, the ambitious meta-assault, ~70 attacks):
- **(i) moment-necessity** (`moment_ladder_exceeds_prize`, PROVEN): no non-negative count / 2nd-order magnitude
  reaches the target — a proof must capture **cancellation** (signs/phases), not a count. *Even a signed Hankel
  determinant reduces* (`_AmbBreakMomentNecessity`: with Weil-frozen anchors it is affine in the count E₂).
- **(ii) √p-vacuity**: `μ_n` is thin (`n≈p^{0.19}`), so Weil/Deligne gives `O(√p)=O(n^{2.6})≫n` — field-scale
  AG is vacuous. The period sheaf `[n]_*L_ψ` has eigenvalues = the n Gauss sums, each `√p`
  (`_FrontierSheafConductor`); the Jacobi correlation re-enters `√p` at the correlation variety's middle
  cohomology `H^{2r-1}`, weight 2r-1 (`_JacobiFermatCohomology`).
- N7-sheaf escapes (ii)'s 0-dim form but hits (ii); the relative-trace escapes (ii) but hits (i). The pincer
  has no gap found.

## 3. This session's genuinely-new contributions (all axiom-clean, none a closure)

- **√p-removal identity** (`_JacobiMomentIdentity.moment_summand_eq`): the 2r-th moment is a SIGNED unit-phase
  Jacobi correlation — the √p cancels out of the whole moment. The first object structurally outside both jaws.
- **Onset growth law** `r_0(n,p) = Θ(p^{1/φ(n)})` (`_OnsetGrowthLaw`, `probe_onset_growth_law`): the wraparound
  onset is exactly the Minkowski/shortest-`𝔭`-vector scale. **Correction**: at prize scale (growing n)
  `r_0 ≈ 1 ≪ log p` (`onset_below_saddle`), so the prize is the *quantitative* `W_r ≤ slack`, NOT `r_0 > log p`.
- **Geometry of numbers closed** (`_OnsetMinimalRelation` + 7 more): the cyclotomic ideal `𝔭` is too "round"
  (all successive minima Θ(1); minimal-relation conjugates balanced, e.g. n=8: {1.47,2.80,2.80,1.47}) ⟹ no short
  anisotropic direction ⟹ every GoN refinement collapses to the (vacuous) norm bound.
- **Variance reframing** (`probe_wraparound_correction`): the wraparound's random mean `n^{2r}/p` is EXACTLY
  DC-cancelled; the prize is the wraparound **fluctuation** (sub-random in data; DC-moment ratio
  `0.87→0.13` for r=2..6, below 1 and improving). A variance/equidistribution statement.

## 4. The dead routes ledger (precise mechanism each fails) — do not re-try

literature sweep (0 verified routes, SOTA exp 1−o(1)); Λ(q)/Rudin (=Sidon=prize by Pisier); sum-product /
di Benedetto (vanishes at p^{0.19}, needs p^{1/4}, by a 724× margin); modern tools decoupling/restriction/VMVT
(μ_n flat 0-dim); 2-power tower decoupling (saving-preserving); explicit Gauss phases (floor at n/4 DOF);
condensed/prismatic/TC/motivic/free-entropy/subfactors/quantum-groups/MTC/VOA/Bethe/RMT/DPP/property-T/QUE/SOS/
Nullstellensatz/slice-rank/incidence/GCT/theta/trace-formula/Cohen-Lenstra/Bilu/Baker/Schmidt/Ruelle/TDA/OT/
tensor-networks/NCG/p-adic-Hodge/crystalline/Bourgain-Gamburd/Lorentzian/Cohn-Elkies/cluster-alg/KZ-period/
tropical/cont-model-theory/Host-Kra (all reduce — see `deltastar-444-exhaustive-loop-log.md`, ~70 entries, every
one to obstruction (i) or (ii)); the ambitious meta-assault (break-the-obstruction, backward-construct, Walsh,
RG, holonomic, info-theoretic — all reduce); geometry of numbers (cyclotomic lattice too round).

## 4b. The variance route — FULLY MAPPED (this session's creation arc, ~28 new axiom-clean objects)

The "rule-in / create" mandate produced 10 frontier objects + 3 next-layer + supporting bricks, all axiom-clean,
all genuinely new. The four variance-core frontiers (F1 growing-order Jacobi discrepancy, F2 wraparound variance
+ `PairCorr`, F3 Stickelberger clustering, F4 tower-variance bootstrap) **converge** on one new open core: the
**second-moment / pair equidistribution of Jacobi sums at growing order** (Katz did first-order, fixed order; the
pair correlation at `r≈log p` is un-attempted). The next layer mapped its exact structure:
- **2nd→1st moment reduction is EXACT** (`_NextDifferenceVariety`): the off-diagonal 2nd moment = a FIRST moment of
  the Jacobi phase over the difference variety `V_diff = append(T, −T')`. Residual = `FirstMomentDiffCancellation` =
  the off-diagonal wraparound, MEASURED non-√-cancelling (`W/√offdiag = 19`, growing) ⟹ V_diff re-enters the wall.
- **Cross-level covariance is EXACTLY `(−1)^r·Var_r`** (`_NextAntipodalAntiCorr`, exact closed form): the antipodal
  tower doubling gives `Var(2n) = ((1−γ_r)²+δ)·Var(n)`, `γ_r=(−1)^{r+1}` ⟹ **maximal contraction at ODD r
  (annihilates), EXPANSION (×4) at EVEN r**. F4's bootstrap is NOT a uniform contraction (dead as a uniform
  mechanism); residual = `OddOrderBridge`.
- **Relation norms are NOT 2-power-smooth** (`_NextNormFactorizationClustering`): largest prime factor grows
  (5→194977 by n=32) ⟹ no smoothness handle.
- **Wraparound is sub-random; random mean DC-cancelled** (`probe_wraparound_correction`): DC-moment ratio
  `0.87→0.13` (below 1, improving) — the prize HOLDS comfortably where computable; the core is the variance of the
  fluctuation at the uncomputable prize scale.

**UPDATE (over-dispersion — the variance route is closed as a *closure path*).** Direct computation of
`Var_P(W_r)` vs `mean_P(W_r)` over the prime family (`probe_wraparound_overdispersion`) refutes the capstone's
sub-Poisson hypothesis everywhere computable: var/mean = **14 … 407555**, heavily **over-dispersed** — a sparse set
of structured primes (high `v₂(p-1)`, Fermat-like) carries the second-moment mass. `_OverdispersionObstructsVariance`
(axiom-clean) proves this is *fatal*: a single prime with `(W_j-mean)² > total` forces `Var > mean`, so Chebyshev
over the family can never select a good prime. The capstone (`subPoisson_variance_implies_prizeFloor`) is therefore
a **true implication with a false hypothesis**. The honest residual shifts from "bound the family variance" to
"**the specific prize prime is round**" (its cyclotomic ideal `𝔭` has no anomalously short vector) — a *per-prime*
lattice-point-equidistribution statement, the same wall, but now correctly located off the family-averaging route.

**FOLLOW-UP (the roundness proxy is refuted; over-dispersion is a thinness/onset effect).** Testing whether
minimal `v₂(p-1)` ("round" `𝔭`) predicts a good prime: it does NOT (`probe_wraparound_v2_stratification`). At `n=8`
the minimal-`v₂` prime `p=41` has `W₃=3120` while higher-`v₂` `p=97` has `W₃=480` — the **v₂-roundness proxy is
REFUTED** as a goodness predictor. The true predictor is **thinness** `β=log p/log n`: `W_r` is largest for the
*smallest* primes (just past the onset `r₀≈p^{1/φ(n)}`) and decays to 0 as `p` grows. So the over-dispersion is a
*finite-window / onset* effect — the smallest primes in any window dominate — re-confirming the
**thinness-essential / regime-gated** verdict (the bound is true at `β≥4`, false at thick structured primes; the
proof must break exactly at the thin/thick boundary). This relocates the per-prime residual back onto the original
thin-regime growing-order equidistribution wall — no new escape, but the obstruction is now correctly attributed
to onset/thinness rather than to 2-adic structure.

**FOLLOW-UP (the roundness proxy is refuted; over-dispersion is a thinness/onset effect).** Testing whether minimal `v₂(p-1)` ("round" `𝔭`) predicts a good prime: it does NOT (`probe_wraparound_v2_stratification`). At `n=8` the minimal-`v₂` prime `p=41` has `W₃=3120` while higher-`v₂` `p=97` has `W₃=480` — the **v₂-roundness proxy is REFUTED**. The true predictor is **thinness** `β=log p/log n`: `W_r` is largest for the smallest primes (just past onset `r₀≈p^{1/φ(n)}`) and decays to 0 as `p` grows. The over-dispersion is a finite-window/onset effect, re-confirming the **thinness-essential / regime-gated** verdict. This relocates the per-prime residual back onto the thin-regime growing-order equidistribution wall.

**RESOLUTION (over-dispersion is BENIGN — the variance route attacked the WRONG statistic).** The decisive
test: the thin-AND-above-onset regime (`n=16, r=5 > r₀≈4, β≈4`) — the first computable window resembling the prize
(`probe_thin_above_onset_goodness`). Result: **every prime is good**, `W₅/E₀ ∈ [0, 0.0057]`, all `≪ 1`, *including
the Fermat prime `p=65537`* (worst structured case, 0.57%); 15/24 have nonzero wraparound (correctly above onset).
The wraparound is **still over-dispersed** there (`W ∈ [0, 2.9M]`) yet every value is `≪ E₀`. So the over-dispersion
is **benign**: the prize needs a **sup / existence** bound (`W_r(p*) ≤ slack` at the *chosen* prime), a *different
statistic* from the family variance. `_OverdispersionObstructsVariance.overdispersion_is_benign` (axiom-clean)
proves sup-goodness and sub-Poisson are **independent** (`W=![B,0]` is over-dispersed yet `≤ B`). The corrected
reduction is to a **uniform sup bound** (every thin above-onset prime good — `>99.4%` margin in data), NOT sub-Poisson
variance. The variance route's death (over-dispersion) was a death of the *wrong target*, not of the prize. The
genuine wall is unchanged: prove the uniform sup bound `W_r ≤ slack` at DEEP `r≈log p` in the thin regime (the
growing-order equidistribution) — but it is now correctly framed as a worst-case/existence sup bound, with strong
positive evidence (Fermat-prime margin `>99%`) at every computable depth.

**Verdict on the variance route:** fully mapped; exact structure known axiom-clean, bottoms out on the SAME
growing-order Jacobi equidistribution as every other route. Genuinely-new objects, no closure.
(See `issue444-create-open-frontiers`.)

## 5. Honest verdict

**Open. Believed true** (numerics `M/√(2n log m) = 0.77–0.85 < 1`; F1 disproof search found no counterexample;
the DC-moment ratio is below 1 and improving where computable). The single missing input is an
**equidistribution / variance bound on the deep-r wraparound** of `μ_n` mod the prize prime — equivalently the
char-p transfer of the (proven) char-0 energy bound at `r ≈ log p` — equivalently BGK/Paley at the prize
exponent, a ~25-year-open analytic-NT problem. We have located it from more angles than perhaps any prior
treatment, formalized everything reducible axiom-clean, and named the irreducible core precisely. The genuine
path past it is a new analytic idea (most plausibly: an effective growing-order equidistribution of Jacobi sums
on the Fermat correlation variety, or a provable variance bound on the wraparound fluctuation) — not a
re-application of existing machinery, all of which we have shown reduces.
