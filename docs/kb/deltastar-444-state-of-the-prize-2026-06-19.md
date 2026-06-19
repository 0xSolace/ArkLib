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

## 1. The single open core (all of these are EQUIVALENT — proven or argued so)

| form | statement | where shown equivalent |
|---|---|---|
| **char-p energy** | `E_r(μ_n;F_p) ≤ (2r−1)‼·n^r` at `r≈log p` | the core; `_OpenCoreMonotoneReduction` |
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
