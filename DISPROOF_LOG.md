# DISPROOF / NO-GO LOG (#407 and predecessors)

## door-(iv) TWO-PIECE PHASE COHERENCE saturates iff same-ray — subdivision alone cannot produce anti-concentration (2026-06-18)

Lens: door-(iv) Lane 3 constraint lemma, deconflicted from the already-landed real sign-mass and
negation-stable coset-refinement bricks.  Those files pin real-piece saturation; the missing
phase-sensitive bookkeeping fact is the general complex/two-vector version: for any two vector pieces
`x,y` in a strictly convex real normed space (in particular `ℂ`), the two-piece norm coherence
`‖x+y‖/(‖x‖+‖y‖)` equals `1` exactly when `x` and `y` lie on the same nonnegative ray.

VERDICT (constraint lemma, does not close CORE): a two-piece Door-IV split has strict slack only after
proving genuine non-collinearity (or a quantitative distance from same-ray alignment) of the two
adversarial pieces.  Mere subdivision of the monomial sum is powerless: triangle equality permits
`ρ=1` precisely at same-ray alignment.  This packages the complex/phase analogue of the real same-sign
wall and tells future anti-concentration attempts exactly what they must prove.

Formal kernel: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DoorIVComplexRayCoherence.lean`,
axiom-clean.  Theorems: `twoPieceNormCoherence_le_one`,
`twoPieceNormCoherence_eq_one_iff_sameRay`, and
`twoPieceNormCoherence_lt_one_of_not_sameRay`.  Axioms are contained in
`{propext, Classical.choice, Quot.sound}`.  No moment/completion route and no CORE claim.

Machine-checked refutations and precise pins. Each entry: lens, test, exact result, wall.

## door-(iv) the SIGNED off-diagonal 4-point connected cumulant VANISHES — the period field is Gaussian to FULL 4th order, the phase-sensitive 4-point door-(iv) object does not exist (closes the sweep-5 pointer) (2026-06-18)

Lens: door-(iv) Lane-1, following the SHARPENED sweep-5 pointer (the modulus 4th moment = dead E₂, so a
surviving lever must be a SIGNED 4-point object using PHASE info that does NOT reduce to E₂). The
candidate: the off-diagonal connected 4th cumulant of the period field z_j = η_{g^j} on the cyclic
quotient. Test the lag-resolved connected energy-energy cumulant
  T₄(k) = E_j[|z_j|²|z_{j+k}|²] − (E|z|²)² − |E_j[z_j z̄_{j+k}]|² − |E_j[z_j z_{j+k}]|²
(= 0 for a Gaussian/Wick field: the 2-2 moment is determined by the covariance). A nonzero T₄(k) NOT
explained by the (already ≈0, white) 2-point covariance = genuine non-Gaussian PHASE structure.

PROBE (`scripts/probes/probe_dooriv_signed_4point_cumulant.py`, EXACT ℂ over coset reps, proper μ_n,
p≫n³, never n=q−1):
| n  | p        | lag | EE(k)/Esq | cov2_norm | cov2_anom | T₄resid/Esq |
|----|----------|-----|-----------|-----------|-----------|-------------|
| 16 | 65537    | 1   | 1.247     | 0.0002    | 0.0002    | +0.247 (Fermat artifact) |
| 16 | 65537    | 2-3 | 0.997     | 0.0002    | 0.0002    | -0.003      |
| 32 | 1048609  | 1-3 | ~1.000    | ~0.001    | ~0.001    | +0.0006..−0.006 |
| 64 | 16777153 | 1-3 | ~1.00     | ~0.004    | ~0.004    | −0.003..−0.015 |
| 16 | 262193   | 1-3 | 0.999     | 0.0001    | 0.0001    | −0.0009     |

VERDICT (door-(iv) sub-lane WALL / constraint lemma): the connected energy-energy cumulant T₄(k) is
≈0 at all lags and does NOT grow with N (|T₄/Esq| ≲ 0.015, shrinking). EE(k)/Esq ≈ 1.00 = exact Gaussian
factorization. The lone T₄(1)=0.247 at the Fermat prime 65537 (p/n=4096 small) is the SAME finite-size
/ Fermat artifact as the white-field sweep, vanishing for all larger generic primes. So the period field
is GAUSSIAN TO FULL 4TH ORDER in its joint structure: the diagonal part is the dead E₂ (sweep 5), and the
off-diagonal connected cumulant is ZERO. CONSEQUENCE (closes the sweep-5 pointer, does NOT close CORE):
the phase-sensitive off-diagonal 4-point coherence that door-(iv) needs DOES NOT EXIST at the connected-4
level. Combined with the marginal-EVT, white-field, and E₂-collapse entries, the period field is fully
Gaussian through 4th order (1- and 2-point Gaussian/white; 4-point diagonal=E₂-dead, off-diagonal
cumulant=0). Any surviving door-(iv) crack must live at 6TH ORDER OR HIGHER, or in an object outside the
moment hierarchy entirely. Formal kernel (Lean, `Frontier/_DoorIVConnectedCumulantVanishes.lean`,
axiom-clean): vanishing connected cumulant ⇒ Wick factorization (`m22_eq_wick_of_cumulant_zero`[_complex]):
`m22 = wick + cumulant`, `cumulant=0` ⇒ `m22 = wick`; a bound through a Wick-factorized 2-2 moment passes
through the 2-point covariance (`control_passes_through_wick`), which the white-field sweep showed ≈0.
The connected-4 phase escape is mapped + dead. CORE OPEN.

## door-(iv) the FIRST higher-order functional (4th-moment / kurtosis of the period marginal) COLLAPSES to the additive energy E₂(μ_n) = the REFUTED energy route (the "go higher-order" escape is dead at 4th order) (2026-06-18)

Lens: door-(iv) Lane-1, following my own chain pointer (the white-field entry: "any crack must live
BEYOND 2nd-order, in a higher-order/nonlinear functional"). The FIRST higher-order functional is the
complex 4th moment of the period marginal, K₄ = E_b|η_b|⁴ / (E_b|η_b|²)². Complex-Gaussian baseline
K₄=2; n-independent-phases baseline K₄ = 2−1/n. Test: is the marginal heavy-tailed (K₄>2, candidate
structure) and if so is the excess a NEW object or the refuted energy?

PROBE (`probe_dooriv_complex4thmoment_gaussianity.py` + `probe_dooriv_4thmoment_iid_control.py`, EXACT
ℂ over coset reps, proper μ_n, p≫n³, never n=q−1; random n-subset control):
| n  | p        | K₄     | K₄−2  | K₆    | E₂(μ_n) | E₂_rand=E₂_iid(2n²−n) | E₂_sub/iid |
|----|----------|--------|-------|-------|---------|----------------------|------------|
| 16 | 65537    | 2.810  | 0.810 | 12.29 | 720     | 496                  | 1.452      |
| 32 | 1048609  | 2.905  | 0.905 | 13.60 | 2976    | 2016                 | 1.476      |
| 64 | 16777153 | 2.937  | 0.937 | 14.14 | 12096   | 8128                 | 1.488      |
| 128| 268437889| 2.975  | 0.975 | 14.66 | —       | —                    | —          |

VERDICT (door-(iv) sub-lane WALL / constraint lemma): K₄ ≈ 2.8–3.0 — the marginal IS heavy-tailed
(K₄−2 ≈ +0.9 above complex-Gaussian; also above 2−1/n), and the excess IS thinness-essential (E₂(μ_n)
is 1.45–1.49× the random/iid value 2n²−n; rule-3 PASS). BUT the EXACT character-orthogonality identity
(verified to machine precision, p=97 n=8: both = 168)
  `(1/p)·Σ_{b∈F_p} |η_b|⁴ = E₂(S) := #{(x₁,x₂,x₃,x₄)∈S⁴ : x₁+x₂=x₃+x₄}`
shows the 4th moment IS the additive energy. So the K₄ heavy-tail excess collapses EXACTLY to
E₂(μ_n)/n² — the additive-moment/energy route, PROVEN NON-PROVING in §6 of #444 (meta-theorem:
additive-energy bounds saturate at structured primes). CONSEQUENCE (kills the higher-order escape MY
chain pointed at, does NOT close CORE): the FIRST higher-order functional of the period field routes
straight back to the refuted E₂ lane. The "go beyond 2nd-order" door is dead AT 4TH ORDER. A surviving
door-(iv) crack, if any, must be a higher-order functional that does NOT reduce to E₂ (i.e. it must use
the PHASE / sign information that the modulus 4th moment discards — a 4-point object that is NOT the
additive-quadruple count). Formal kernel (Lean, `Frontier/_DoorIVFourthMomentEnergyCollapse.lean`,
axiom-clean): the b-averaged 4th power, being an additive energy `Σ_t mult(t)²`, is a nonnegative
quadruple-count (`additiveEnergy_nonneg`); any sup bound through it is a bound through E₂
(`sup_fourthPower_le_energy_scale`: `M⁴ ≤ p·avg ⇒ M⁴ ≤ p·E₂`). The energy substrate identity itself
lives in-tree under `AdditiveEnergy*`/`*ParsevalFloor`. The 4th-moment escape is mapped + dead. CORE OPEN.

## door-(iv) TERMINAL: the period field is an UNCORRELATED (white) field on the multiplicative quotient — the JOINT b↔b' structure is dead too (autocorr→0 at all lags), the last door-(iv) surface I localized closes (2026-06-18)

Lens: door-(iv) Lane-1 CLOSURE. My three prior sweeps pinned the worst-b cancellation to the MARGINAL
Gaussian-EVT law of {|η_b|} (dead = door iii) and localized the ONLY surviving surface as the JOINT
correlation across cosets b. Since η is constant on μ_n-cosets, the field lives on the cyclic quotient
Z_{(p-1)/n} via j ↦ η_{g^j}. Test: is this field SHORT-RANGE white (joint dead) or LONG-RANGE
multiplicatively-structured (door-iv grip)?

PROBE (`scripts/probes/probe_dooriv_joint_bcorrelation.py`, EXACT ℂ over coset reps g^j, proper μ_n,
p≫n³, never n=q−1):
| n  | p        | N=cosets | ac1|η| | ac2|η| | ac1_complex | ac1_energy | add_nbr | max_{1..50}|ac| |
|----|----------|----------|--------|--------|-------------|------------|---------|----------------|
| 16 | 65537    | 4096     | 0.060  | -0.018 | 0.0002      | 0.136      | 0.740   | 0.060          |
| 32 | 1048609  | 32769    | -0.0001| 0.001  | 0.0000      | -0.0005    | -0.037  | 0.0068         |
| 64 | 16777153 | 262143   | -0.001 | 0.004  | 0.007       | -0.001     | -0.007  | 0.013          |
| 16 | 262193   | 16387    | 0.004  | 0.001  | 0.0001      | -0.0005    | -0.043  | 0.0064         |
| 32 | 5931649  | 185364   | 0.003  | 0.002  | 0.0055      | 0.001      | -0.024  | 0.0085         |

VERDICT (door-(iv) TERMINAL WALL / constraint lemma): the field j ↦ η_{g^j} is an UNCORRELATED WHITE
field. The lag-k autocorrelation of |η|, of complex η, and of the energy |η|² are all ≈0 at EVERY nonzero
lag and SHRINK with N (|ac1| 0.06 → 1e-3 → 1e-3; max over 50 lags → 0). The lone additive-neighbour
correlation 0.74 appears ONLY at the Fermat prime 65537 (p/n=4096 small) and COLLAPSES to ≈0 for the
larger generic primes — a finite-size/Fermat artifact, NOT a prize-regime signal. So even the JOINT
structure is dead: NO exploitable low-order multiplicative correlation. CONSEQUENCE (closes the surface
I localized, does NOT close CORE): together with the marginal Gaussian-EVT saturation, the period field
has NEITHER marginal NOR low-order joint structure to grip — the cancellation difficulty is the
irreducible BGK/Paley wall. Any door-(iv) crack must live BEYOND second-order joint statistics (in a
higher-order / non-linear functional of the field that this white-noise autocorrelation cannot see).
Formal kernel (Lean, `Frontier/_DoorIVJointFieldWhite.lean`, axiom-clean): zero cross-covariance
diagonalizes the second moment — `Σ g_i g_{σ i}=0` ⇒ `Σ (g_i+g_{σ i})² = 2Σ g_i²`
(`white_field_diagonalizes`); the lag-k joint block contributes nothing beyond the diagonal variance.
The second-order joint route is mapped + dead. CORE OPEN.

## door-(iv) the worst-b SATURATES the GAUSSIAN extreme-value prediction M ≈ √(n·log(p/n)) with NO marginal slack (M/rmsM ≈ √log, kurtosis→3) ⇒ the crack, if any, is in the JOINT b-correlation, not the marginal (2026-06-18)

Lens: door-(iv) Lane-1, the UPPER-side companion to the L2 mean-floor entry (which pins the LOWER
bracket at Johnson √n). Both prior sweeps (758205014 window energy-blind, 592490748 worst-b ~5σ spike)
concluded the cancellation routes through the 2nd moment of {|η_b|}. Decisive remaining question: does
the actual sup M = max_b|η_b| SATURATE its moment/extreme-value ceiling, or is there marginal SLACK a
non-moment door-(iv) method could occupy?

PROBE (`scripts/probes/probe_dooriv_sup_vs_sndmoment_slack.py`, EXACT ℂ over coset reps, proper μ_n,
p≫n³, never n=q−1; rmsM = √(mean_b|η_b|²)):
| n   | p         | M      | M/√n | rmsM/√n | M/rmsM | √log(p/n) | (M/rms)/√log | kurtosis |
|-----|-----------|--------|-------|---------|--------|-----------|--------------|----------|
| 16  | 65537     | 13.84  | 3.46  | 1.000   | 3.46   | 2.884     | 1.200        | 2.810    |
| 32  | 1048609   | 22.98  | 4.06  | 1.000   | 4.06   | 3.224     | 1.260        | 2.905    |
| 64  | 16777153  | 37.44  | 4.68  | 1.000   | 4.68   | 3.532     | 1.325        | 2.937    |
| 128 | 268437889 | 50.66  | 4.48  | 0.999   | 4.48   | 3.815     | 1.175        | 2.975    |
| 32  | 5931649   | 22.63  | 4.00  | 0.996   | 4.02   | 3.483     | 1.153        | 2.898    |
| 64  | 134217409 | 33.93  | 4.24  | 1.001   | 4.24   | 3.815     | 1.110        | 2.968    |

VERDICT (door-(iv) sub-lane WALL / constraint lemma): (i) `rmsM/√n = 1.000` confirms the Plancherel
identity `mean_b|η_b|² = n` exactly. (ii) `M/rmsM ≈ √(log(p/n))` with a NEARLY CONSTANT prefactor
`(M/rms)/√log ≈ 1.1–1.33`: the sup overshoots the L2 scale by EXACTLY the prize √log factor, i.e.
`M ≈ √n·C·√(log(p/n))` SATURATES the prize form `M ≤ C√(n·log(p/n))`. (iii) kurtosis
`mean|η|⁴/(mean|η|²)² → 3` (2.81→2.97 ↑): the `|η_b|` MARGINAL converges to the Gaussian-modulus law,
whose extreme over `N≈p/n` samples is `σ√(2 log N)` = exactly the observed √log overshoot. So the worst-b
sits AT the Gaussian extreme-value prediction with NO marginal slack — this IS Shaw's door (iii) =
equidistribution/EVT = BGK, PROVEN DEAD. CONSEQUENCE (localizes the crack, does NOT close CORE): a
door-(iv) lever cannot come from the MARGINAL distribution of `|η_b|` (Gaussian, moment-determined,
EVT-saturated); if any crack survives it must live in the JOINT correlation structure across b that the
marginal moments cannot see. Formal kernel (Lean, `Frontier/_DoorIVSupRmsGaussianSaturation.lean`,
axiom-clean): `(max f)² ≥ mean(f²)` (`sq_max_ge_mean_sq`), i.e. `M ≥ rmsM = √n`
(`max_ge_rms`) — the moment route bounds the sup from the WRONG (lower) side only. The marginal-moment
escape is mapped + dead. CORE OPEN.

## door-(iv) WORST-b is an ISOLATED ≈5σ large-deviation SPIKE (not a plateau) ⇒ a b-side count bound is MOMENT-EQUIVALENT (routes through the 2nd moment = BGK; lands in dead door-iii) (2026-06-18)

Lens: door-(iv) Lane-1, "what arithmetic of b selects the worst coset alignment? is the worst-b SET
structured?" A b-side ANTI-CONCENTRATION hope: bound the sup `M = max_b |η_b|` by controlling HOW MANY
cosets b achieve near-M (if few + arithmetically special, exploit them). Test the DISTRIBUTION of
`|η_b|` over ALL `(p−1)/n` multiplicative-coset reps: spike or plateau?

PROBE (`scripts/probes/probe_dooriv_worstb_plateau.py`, EXACT ℂ over ALL coset reps, proper μ_n,
p≫n³, never n=q−1):
| n  | p         | #cosets | M/√n | frac(|η|≥0.9M) | frac(≥0.75M) | mean/M | (M−mean)/σ |
|----|-----------|---------|-------|--------------|-------------|--------|-----------|
| 16 | 65537     | 4096    | 3.46  | 7e-4         | 7.3e-3      | 0.233  | 4.47      |
| 32 | 1048609   | 32769   | 3.81  | 1e-4         | 3.3e-3      | 0.211  | 5.01      |
| 64 | 16777153  | 262143  | 4.04  | 2e-4         | 2.1e-3      | 0.200  | 5.31      |
| 16 | 262193    | 16387   | 3.55  | 6e-4         | 5.2e-3      | 0.226  | 4.62      |
| 32 | 5931649   | 185364  | 4.00  | 3e-4         | 2.1e-3      | 0.200  | 5.32      |

VERDICT (door-(iv) sub-lane WALL / constraint lemma): the sup is a SHARP ISOLATED large-deviation
SPIKE, NOT a plateau. `frac(|η_b| ≥ 0.9 M) → 0` (negligible: ~1e-4), `mean/M ≈ 0.20–0.23` (sup is ~5×
the mean period), and `(M−mean)/σ ≈ 4.5 → 5.0 → 5.3` GROWING with n (the sup deepens in σ-units). A deep,
isolated, σ-growing spike is exactly the EXTREME-VALUE / equidistribution profile = Shaw's door (iii)
= BGK, PROVEN DEAD. So the worst-b does NOT open a new door: its isolation routes the sup back through
the SECOND MOMENT of the `|η_b|` family. The b-side count route is MOMENT-EQUIVALENT. Formal kernel
(Lean, `Frontier/_DoorIVWorstBSpikeMomentBound.lean`, axiom-clean): one-sided Chebyshev/Cantelli — the
above-threshold COUNT satisfies `count · d² ≤ Σ(xᵢ−μ)²` (`threshold_count_mul_sq_le_centered_sndMoment`),
equivalently `count ≤ Σ(xᵢ−μ)²/d²` (`threshold_count_le_sndMoment_div`). An isolated spike (small count
at large d) is EXPLAINED BY a small second moment `Σ(xᵢ−μ)²` = the additive-energy/moment object; any sup
bound via the spike count passes through it. CONSEQUENCE (complements the energy-blind window entry,
does NOT close CORE): a "worst-b is structured / b-side anti-concentration" door-(iv) lever cannot beat
the 2nd moment — the worst-b's isolation is itself a moment statement, landing in the dead extreme-value
door. The b-side-count escape is mapped + dead. CORE OPEN.

## door-(iv) SINGLE-WINDOW phase-set concentration is ENERGY-BLIND: the coarse window functional decorrelates from |η| (Spearman→0) and is sub-√n (C/√n→0) — coarse spatial clustering is NOT the cancellation mechanism (2026-06-18)

Lens: door-(iv) Lane-1 anti-concentration, the UNSIGNED additive spread of the phase set
`A_b = { b·y mod p : y ∈ μ_n }` itself (distinct from the prior ILO entry below, which probes the
SIGNED character-sum small-ball `Q(t)` over the sign cube — an energy/relations object on the signs).
The door-(iv) hope: if a large `|η_b|` were produced by `A_b` CLUSTERING into a short arc (small-ball),
one could read a sup-norm bound off the spatial concentration WITHOUT a moment/completion. Test the
coarse window functional `C_b = max over arcs W of length p/n of #{ y : b·y mod p ∈ W }`.

PROBE (`scripts/probes/probe_dooriv_phaseset_anticoncentration.py` +
`scripts/probes/probe_dooriv_smallball_vs_energy.py`, EXACT ℂ over PROPER μ_n, p≫n³, m=(p−1)/n≥2,
incl. Fermat 65537, NEVER n=q−1; random same-size additive control; full sampled b-sweep + Spearman):
| n   | p          | M=|η|_max | M/√n | C_worst | C_worst/√n | argmax(C)=argmax(η)? | Spearman(|η|,C) |
|-----|------------|-----------|-------|---------|-----------|---------------------|----------------|
| 16  | 65537      | 13.84     | 3.46  | 12      | 3.00      | NO                  | 0.49           |
| 32  | 1048609    | 22.98     | 4.06  | 9       | 1.59      | NO                  | 0.19           |
| 64  | 16777153   | 32.23     | 4.03  | 12      | 1.50      | NO                  | 0.11           |
| 128 | 268437889  | 43.73     | 3.87  | 12      | 1.06      | NO                  | 0.074          |
| 256 | 4294968833 | 62.03     | 3.88  | 10      | 0.625     | NO                  | 0.046          |
(window-concentration of `A_b` IS larger than random at the worst-b for C, e.g. n=16: 12 vs 4 — so it
is thinness-sensitive — but on the two diagnostics that matter it FAILS.)

VERDICT (door-(iv) sub-lane WALL / constraint lemma): the single-window concentration functional is
ENERGY-BLIND on BOTH axes. (i) SCALE: `C_worst/√n → 0` (3.0, 1.59, 1.50, 1.06, 0.625) — the worst window
count is FLAT (~10–12 points) and *sub*-√n, far BELOW the prize √n scale, so it cannot be the prize
object. (ii) DECORRELATION: `C_b` is NOT a repackaging of `|η_b|` — Spearman(|η|,C) collapses
(0.49→0.046) and the argmax of `C` decouples from the argmax of `|η|`; at the ACTUAL worst-b for `|η|`,
`C` is not maximal. MECHANISM: a large `|η_b|` is produced by FINE PHASE coherence (the unit vectors
`e_p(b·y)` aligning), which is exactly the moment/energy object, NOT by coarse spatial clustering of
the residues. The formal kernel (Lean, `Frontier/_DoorIVWindowConcentrationTrivial.lean`,
axiom-clean): for unit-modulus summands, splitting into the `C` in-window and `n−C` out-of-window terms,
**each** out-of-window term still has modulus `1`, so a single window yields only
`|η_b| ≤ C·1 + (n−C)·1 = n` — the trivial linear ceiling, INDEPENDENT of `C`
(`window_split_rhs_constant`: the split RHS equals `n` for every admissible window). CONSEQUENCE
(complements the ILO entry below, does NOT close CORE): door-(iv) anti-concentration cannot be supplied
by a single-window / coarse-spatial small-ball quantity; any real anti-concentration lever must grip the
FINE phase alignment (the energy/coherence object) — i.e. the route back to the BGK/Paley wall. The
coarse-clustering escape is mapped + dead. CORE OPEN.

## the POINTWISE-AUTOCORRELATION self-consistency ceiling is TRIVIAL (linear n) — the triangle inequality discards exactly the difference-set cancellation that IS the wall (2026-06-17)

Lens: the just-landed pointwise identity `‖η_b‖² = Σ_{ζ∈μ_n} η_{b(ζ-1)}` (EtaPointwiseAutocorr.lean,
`eta_normSq_eq_sum_groupShift`, axiom-clean, d2983e9e4). It re-expresses the single-frequency worst
period² on the difference-set spectrum `b·(μ_n−1)`. NATURAL next move (tested here, rule 2 probe-first):
close CORE by bounding the shift sum with the triangle inequality. With `M = max_b|η_b|`, the ζ=1 term
is `η_0 = n` and each of the `n−1` nontrivial shift periods is `≤ M`, giving the SELF-CONSISTENCY
quadratic `M² ≤ n + (n−1)·M`, hence the ceiling `M ≤ ((n−1)+√((n−1)²+4n))/2`.

PROBE (`scripts/probes/probe_eta_autocorr_selfconsist.py`, EXACT over ℂ, PROPER thin μ_n only,
m=(p−1)/n ≥ 2, NEVER n=q−1, incl Fermat 257/65537):
| n  | p     | M_actual | √n   | M/√n  | selfconsist_ceil | ceil/√n |
|----|-------|----------|------|-------|------------------|---------|
| 8  | 257   | 6.10     | 2.83 | 2.16  | 8.000            | 2.83    |
| 16 | 257   | 9.23     | 4.00 | 2.31  | 16.000           | 4.00    |
| 32 | 641   | 15.09    | 5.66 | 2.67  | 32.000           | 5.66    |
| 16 | 65537 | 13.84    | 4.00 | 3.46  | 16.000           | 4.00    |
| 32 | 65537 | 25.21    | 5.66 | 4.46  | 32.000           | 5.66    |

VERDICT (WALL / constraint lemma): the self-consistency ceiling is EXACTLY `n` to leading order
(the quadratic root `((n−1)+√((n−1)²+4n))/2 → n`), i.e. LINEAR in n — it recovers only the trivial
`|η_b| ≤ n` and is √n times weaker than the actual `M ≈ 2-4·√n`. MECHANISM: the triangle inequality
assumes all `n−1` nontrivial difference-set shifts `η_{b(ζ-1)}` ALIGN at modulus M (zero cancellation
among them), which is exactly the worst possible case. It is therefore thickness-INVARIANT (no use of
μ_n's thinness beyond the group reindex) and discards 100% of the cancellation. CONSEQUENCE (localizes
the wall, does NOT close it): the open content of the pointwise identity is ENTIRELY the
**cancellation among the n−1 nontrivial shift periods** `Σ_{ζ≠1} η_{b(ζ-1)}` — exactly the BGK/Paley
sup-norm wall, now pinned to the difference-set shift spectrum. Any CORE proof routing through the
pointwise identity MUST bound the shift sum WITH its cancellation (not term-by-term). CORE OPEN. The
identity is real and useful (it is the correct difference-set fixed-point form); the term-by-term
closure is the dead lane. Probe Python-only (axiom-clean trivially); the identity it tests is the
Lean-proven `eta_normSq_eq_sum_groupShift`.

## eta-COSET-LOCALIZATION is THINNESS-ESSENTIAL (rule-3 PASS) -- the FIRST structural reduction in the map that passes the thin gate; corroborates in-tree EtaCosetSplit / coset reduction (2026-06-15)

Lens: the bulk-correlation localization opened by the ILO entry (852e0fa27: thin mu_n sup-norm is LARGE,
bulk-correlated). WHERE does the large thin |eta_b| live? eta_b = sum_{x in mu_n} e_p(bx). Since mu_n is a
GROUP, for c in mu_n the map x->cx permutes mu_n, so eta_{cb} = sum_x e_p(b(cx)) = eta_b EXACTLY -- eta is
constant on multiplicative cosets b*mu_n. This is ALREADY formalized in-tree (EtaCosetSplit.eta_coset_split,
GaussPeriodCosetReduction.cosetReduced_eta_pow_le -- the "divide by n" coset reduction). The MISSING test
(supplied here): is this structural reduction THINNESS-ESSENTIAL (rule-3), unlike the moment-cert (thickness-
invariant 18%) and ILO (thin worse) passages?

PROBE (scripts/probes/probe_407_bulk_freq_structure.py, EXACT eta over proper mu_n vs random thin-density
control, full b-sweep, prize + thick primes, never n=q-1):
| n  | beta | p     | M=max|eta| | M/sqrt n | |eta| const on mu_n-cosets? | random same-partition const |
|----|------|-------|------------|----------|-----------------------------|------------------------------|
| 8  | 3.0  | 521   | 6.56       | 2.32     | YES (40/40, exact)          | 0/40 (spread <= 5.17)        |
| 8  | 4.0  | 4153  | 7.46       | 2.64     | YES (40/40)                 | 0/40 (spread <= 5.12)        |
| 16 | 3.0  | 4177  | 10.94      | 2.74     | YES (40/40)                 | 0/40 (spread <= 11.9)        |
| 16 | 4.0  | 65617 | 13.30      | 3.32     | YES (40/40)                 | 0/40 (spread <= 9.49)        |

VERDICT (rule-3 PASS -- a POSITIVE structural localization, not a wall): the |eta| spectrum is EXACTLY
mu_n-coset-localized => the sup-norm M(n) = max over only (p-1)/n COSET REPRESENTATIVES, not p-1
frequencies (a genuine structural reduction, already in-tree). CRUCIALLY this coset-localization is
ABSENT for a random same-density set (0/40 cosets constant, spreads 5-12) => it is THINNESS-ESSENTIAL:
it is a multiplicative-GROUP property of mu_n, FALSE for an unstructured thin set. This is the FIRST
reduction in the whole #407 obstruction map that PASSES the rule-3 gate at the SUP-NORM level (the moment
certificate and ILO anti-concentration both FAILED rule-3 -- thickness-invariant / thin-worse). So a valid
thinness-essential CORE proof, which by rule 3 must use a quantity FALSE in the thick window, is consistent
with ROUTING THROUGH the coset reduction (eta constant on b*mu_n, reducing to (p-1)/n reps) -- the
in-tree EtaCosetSplit / cosetReduced_eta_pow_le machinery -- whereas it CANNOT route through the moment or
ILO passages. CONSEQUENCE (mapping): the live thinness-essential surviving structure at the SUP-NORM level
is the coset reduction itself; the open content is the per-coset-rep bound on |eta_c| after the reduction
(the GaussPeriodCosetReduction object), NOT a global anti-concentration or moment bound. CORE not closed;
the coset reduction CONFIRMED as the rule-3-passing structural locus. Python-only, no Lean changed =>
axiom-clean trivially. Exact full b-sweep, proper subgroups, thick+thin windows.

## ★ REDUCTION-MISMATCH — the lacunary-root reduction (63aa3b4ab) + DFT-uncertainty insight (6507e61aa) compute the WRONG δ*: max-single-witness root count (trivial n/2 binomial factor) ≠ the in-tree list-budget δ* (2026-06-15)

Lens: the two freshest analytic handoffs reframe the prize s* as "max # of μ_n-roots of a (k+2)-term lacunary
far-line polynomial P=x^a+γx^b−c (deg c<k)". Adversarial audit (rule 6): this object is NOT the in-tree
list-budget s* the engine computes.

EXACT FACTS (verified):
1. Engine source (`scripts/rust-pg/src/main.rs`): `incidence(a,b;s)=local.len()` = **# distinct γ** with x^a+γx^b
   agreeing with a deg<k codeword on a size-s subset; `s*=min{s : max_dir incidence(s) ≤ budget=n}` (a γ-COUNT /
   list-size threshold). This is the prize δ* (p-independent, GPU-confirmed).
2. The max-SINGLE-witness (NON-DEGENERATE) root count is **k+1**, NOT n/2 (CORRECTED, see retraction note).
   My first-pass witness P=(x−1)(x^{n/2}+1) (n=16: line x^9−x^8) has **b=n/2 active** = the KB-excluded antipodal
   monomial, with gcd(a−b,n) EVEN = the degenerate I=q−1 coset pencil (the engine never scans b=n/2 at the binding
   radius; rule-2 trap). Enforcing correct non-degeneracy (active line monomials, gcd(a−b,n) ODD, no exp=n/2): the
   factors Φ_{2^j}=x^{2^{j−1}}+1 carry only EVEN exponents, so an odd-(a−b) witness uses ≤1 big even-exp factor +
   Φ_1 ⟹ cyclotomic-forced roots collapse to **k+1** (PARITY-BLOCKED, per the 0xSolace parity-block comment).
   (A first non-deg recheck still showing n/2 had a bug: its rank-deficiency test admitted combos like x^9+x=
   x(x^8+1) that DROP the required active line monomial x^a, silently re-admitting the degenerate 2-term antipodal
   pencil. With line-monomials-active enforced, all n/2 witnesses vanish.)

WALL / constraint lemma: the non-degenerate "max μ_n-root-count of a (k+2)-sparse far-line polynomial" = **k+1**
(cyclotomic-forced), while the in-tree list-budget s* = 2k−1 ≈ Johnson. Still a DIFFERENT object — gap **k−2** — and
the ~(k−2) agreement lifting s* from k+1 (cyclotomic) to 2k−1 (Johnson) lives ENTIRELY in the band / general
deg-<k codeword DOF, NOT the roots-of-unity / cyclotomic-divisibility structure. Therefore the lacunary-root /
DFT-uncertainty reduction does NOT compute the prize δ*; the lacunary/cyclotomic-factor mechanism alone cannot
reach Johnson non-degenerately (caps at k+1). The Mann/Conway–Jones/Bombieri–Zannier handoff is real ONLY for
the single-witness object. For the prize, the right classical object is **list-size/multiplicity of (k+2)-sparse
polynomials at Johnson radius**, not max-root-count. Consistency check: for n PRIME, x^n−1=(x−1)Φ_n with Φ_n DENSE
⟹ no sparse high-deg factor ⟹ single-witness roots cap at k+O(1) (matches KB "prime⟹capacity"), so the prime-vs-
smooth dichotomy is real for the single-witness object — the error is equating it with the prize δ*.

RETRACTION NOTE (rule 6): my first receipt claimed n/2+1 single-witness roots; that used a DEGENERATE antipodal
witness (b=n/2, even gcd(a−b,n)) — the excluded I=q−1 pencil (rule-2 trap). Corrected non-degenerate ceiling = k+1
(parity-block). The reduction-mismatch CONCLUSION survives (max-single-witness object ≠ list-budget δ*); only the
NUMBER was inflated. Posted correction: #407 comment 4704593680.

Probe: `scripts/probes/probe_407_lacunary_cyclotomic_mechanism.py` (exact char-0). Pushed 71722be4f (probe) +
this corrected entry. NOT a closure — removes a false analytic lead + re-localizes the open core (consistent with
the 0xSolace parity-block + lalalune p-independence findings).

## ILO / anti-concentration is NOT the lever — thin μ_n is anti-concentrated WORSE than random (larger sup-norm, larger small-ball); reconciles the thin depth-advantage with the large thin sup-norm (2026-06-15)

Lens: inverse-Littlewood-Offord (Tao–Vu / Nguyen–Vu). M(n)=max_{b≠0}|η_b|, η_b=Σ_{x∈μ_n} e_p(bx), is
controlled by anti-concentration of the signed character sum Σ ε_i ζ^i: FEW additive relations (high Sidon
depth) ⇒ strong anti-concentration ⇒ small small-ball Q ⇒ small M. The surviving thin mechanism (my
full-depth-BIND entry + the depth-SCALING entry e7b5e6125) shows thin μ_n has DEEPER first vanisher than
random — which would, IF ILO were the bridge, predict thin M < random M. This is the missing test:
does the thin sparse-depth advantage translate to a sup-norm / small-ball advantage (live ILO lever) or not?

PROBE (scripts/probes/probe_407_ilo_vanisher_count.py, EXACT sup-norm via full b-sweep over proper μ_n <
F_p^*, p==1 mod n m odd never n=q−1; random thin-density control = n distinct nonzero residues; small-ball
Q(t)=Pr[|Σε_i r_i| ≤ t·p] over the sign cube; thick β~2.3-3.0 AND thin β~4-4.5 windows):

| n  | β    | window | M_thin | M_rand(med) | M_thin/√n | Q(.02)_thin | Q(.02)_rand |
|----|------|--------|--------|-------------|-----------|-------------|-------------|
| 8  | 2.30 | thick  | 5.84   | 5.58        | 2.06      | 0.147       | 0.023       |
| 8  | 4.00 | thin   | 7.46   | 6.90        | 2.64      | 0.125       | 0.053       |
| 8  | 4.50 | thin   | 7.68   | 7.49        | 2.71      | 0.156       | 0.039       |
| 16 | 2.30 | thick  | 8.44   | 9.39        | 2.11      | 0.044       | 0.038       |
| 16 | 4.00 | thin   | 13.30  | 11.99       | 3.32      | 0.050       | 0.040       |
| 16 | 4.50 | thin   | 12.98  | 10.38       | 3.25      | 0.043       | 0.040       |

VERDICT (the OPPOSITE of what ILO needs — rule-3 wall): thin μ_n's sup-norm M_thin is consistently
≥ M_rand (n=16 β=4: 13.30 vs 11.99; β=4.5: 12.98 vs 10.38), and the small-ball Q_thin ≥ Q_rand (thin
CONCENTRATES MORE, not less). So inverse-Littlewood-Offord ANTI-CONCENTRATION is NOT the prize lever:
μ_n is anti-concentrated WORSE than a random same-density set, hence any ILO bound is WEAKER for μ_n. The
thin advantage at sparse DEPTH (no low-order vanishers) does NOT lift to a bulk anti-concentration / sup-
norm advantage — the bridge runs backwards.

RECONCILING INSIGHT (why this is consistent, not contradictory): μ_n carries the FULL multiplicative-group
additive structure — it has MORE near-zero bulk sums (worse small-ball) than random PRECISELY BECAUSE it is
a coherent geometric/cyclotomic object, even while its FIRST exact vanisher is pushed deep (high Sidon
depth). "Deep first relation" (sparse, sibling e7b5e6125) and "large sup-norm / poor anti-concentration"
(bulk, here) coexist: the cancellation difficulty of the thin BGK regime lives in the BULK correlation, not
the sparse-relation floor. This is exactly WHY the moment-cert passage (thickness-invariant 18% slack) and
the ILO passage both fail to convert the sparse thin depth-advantage into the sup-norm bound. CONSEQUENCE
(mapping, not closure): the surviving thin sparse-depth signal must reach M(n) WITHOUT going through (a) the
moment→sup passage M≤(qA_r)^{1/2r} [regime-uniform loss] or (b) the ILO anti-concentration→sup passage [thin
is worse]. Both "obvious" bridges from depth to sup are now walled. CORE not closed; ILO lever walled +
the depth-vs-bulk reconciliation pinned. Python-only, no Lean changed ⇒ axiom-clean trivially.

## BIND-full-depth-threshold — the literal B_∞←B_{log n} Sidon bootstrap target (NO non-antipodal vanisher AT ALL) FAILS at fixed prize β as n grows; thin advantage is REAL but INSUFFICIENT (2026-06-15)

Lens: brief lane #0 / §5.0 (BIND) literal full-depth form. The proven depth-2 brick
`SidonLiftDevacuated.sidonModNeg_rootsOfUnity` gives "no 4-term ±-relation" (Sidon-mod-neg, depth r≤2)
WHEN `p > 4^{φ(n)} = 2^n`, i.e. `β > n/log₂ n`. The bootstrap target is to extend no-non-antipodal-
vanishing `Σ_{i∈S} ζ^i ≡ 0 (p)` from depth ~log n to FULL depth |S| ≤ n/2. I measured directly whether
the literal FULL-depth property holds at the PRIZE scaling (p = n^β, β∈[4,5]) and whether the obstruction
is thinness-essential (the rule-3 gate that killed the BHBI lever).

Method: exact-integer meet-in-the-middle over μ_n = n-th roots of unity in F_p (proper 2-power subgroup,
p≡1 mod n, m=(p−1)/n preferentially odd, NEVER n=q−1), smallest non-antipodal unsigned zero-sum r_min.
Full MITM exact at n=16,32; randomized MITM (SOUND on FAILURES — a found r_min<n/2 PROVES BIND fails) at
n=64. Probes `scripts/probes/probe_407_bind_depth_fraction.py` + `probe_407_bind_beta_threshold.py`.

RESULT 1 — empirical β*(n) (smallest β with FULL-depth BIND, r_min = NONE) GROWS with n:
| n  | empirical β* (full-depth BIND) | proven-suff (n/log₂n) | n=64 SOUND-FAILS at β = |
|----|--------------------------------|-----------------------|--------------------------|
| 16 | 4.0   (matches proven 4.00)    | 4.00                  | —                        |
| 32 | 4.5   (well below proven 6.40) | 6.40                  | —                        |
| 64 | ∈ (6.0, 7.0]                   | 10.67                 | 4.0,4.5,5.0,5.5,6.0 all  |
Decisive: at the UPPER prize edge β=5.0, full-depth BIND HOLDS at n=32 (r_min=NONE) but SOUND-FAILS at
n=64 (r_min ≤ 10 < 32, exact zero-sum witness). β*(n) is NOT bounded by the prize ceiling β=5 — it grows.

RESULT 2 — THINNESS-ESSENTIAL (rule-3 PASS, unlike BHBI): at n=32, β=4.0, thin μ_32 r_min = 11 vs RANDOM
thin-density 32-subset median = 6 (samples [5,6,6,7,7]); at β=5.0 thin = NONE (full depth) vs random median
= 8. μ_n is strictly MORE relation-free (deeper Sidon) than a random same-density set. So this is a GENUINE
thin obstruction-suppression — NOT the thickness-invariant basis-length pigeonhole that killed BoundedHalf-
BasisIndep. The 2-power structure really does push the first vanisher deeper.

CONSTRAINT LEMMA (BIND-FULL-DEPTH-THRESHOLD). Let β*(n) = inf{β : μ_n over F_{p}, p=⌈n^β⌉ prime ≡1(n),
has NO non-antipodal S⊆Z/n with Σ_{i∈S} ζ^i ≡ 0 (p)}. Measured β*(16)=4.0, β*(32)=4.5, β*(64)∈(6,7];
β*(n) is increasing and (over 16→64) tracks ABOVE the prize ceiling 5 by n=64. ⟹ for every FIXED prize
β∈[4,5], the LITERAL full-depth BIND statement is FALSE for all large n (a non-antipodal mod-p vanisher of
size < n/2 exists). The literal "B_∞ ← B_{log n}" bootstrap target is therefore unattainable as stated.

HONEST SCOPE (rule 6, no overclaim): (a) n=64 is randomized (SOUND only on the FAILURE direction; the
β=7,8 "none-found" rows are inconclusive, NOT proofs BIND holds). (b) β*(n) grows SLOWLY (4.0→4.5→~6.5),
FAR below the proven-sufficient n/log₂n — the truth is much better than the depth-2 resultant lift can
prove, just not good enough for fixed β. (c) This refutes the LITERAL full-depth form, NOT CORE: CORE is
the sup-norm bound, which does not need zero spurious vanishers — it needs the COLLECTIVE cancellation to
stay √-small. A super-constant (even log^c n or n^{1−ε}) thin Sidon depth, which the thin-advantage in
Result 2 DOES provide, could still route CORE via a moment/√-cancellation argument that tolerates a few
deep vanishers. So: the literal BIND target is walled; the thinness-essential thin advantage that suppresses
low-depth vanishers is real and is the live object — but it must be used COLLECTIVELY (depth-profile /
moment), not as a per-S "no vanisher at all" statement. CORE not closed; one literal target precisely walled
+ the surviving thin mechanism isolated. Python-only, no Lean changed ⟹ axiom-clean trivially.

## BIND-gate-scope — the §5.0 (BIND)/house gate route does NOT generalize: non-antipodal mod-p vanishers EXIST at thin prize-β primes once (#S)^φ > p (2026-06-15)

Lens: §5.0 reduces CORE to (BIND) — "no spurious non-antipodal vanishing `Σ_{i∈S} ω^i ≡ 0 (p)` with S
not antipodal" — and proves it via the height gate `HeightGateNormBound.gate_2power_antipodal`, whose
HYPOTHESIS is `hp : (#S)^φ(n) < p` (house bound `|N(β)| ≤ (#S)^φ < p`, then `p|N ⇒ N=0 ⇒` antipodal).
The body claims "NoSpuriousVanishing is a proved theorem for n≤32" + "realized-height extends to n≤64,
heuristically n≤96", and frames the open part as "need a structure-aware norm bound (not trivial house)
to get |N|<p at n≥112."

TEST 1 (worst-case realized norm vs the fixed prize budget p~2^128). Hill-climbed max over reduced
coeff vectors c∈{-1,0,1}^{n/2} (the worst non-antipodal residue pattern; exact integer norm via
`Res(x^{n/2}+1, c(x))`, cross-checked high-precision):
  n=64:  max log2|N| = 78.9  (< 128, closeable — matches H(64)<2^128)
  n=96:  max log2|N| = 131.1 (> 128)
  n=112: max log2|N| = 160.5 (> 128)
  n=128: max log2|N| = 188.0 (> 128; vs ABF p~2^136 still >)
Growth ~0.184·n·log2(n) (a CONSTANT fraction ~37% of the house (n/2)log2(n/2) — the house slack does
NOT vanish). CROSSOVER between n=64 and n=96. The single 56-element witness cited in §5.0 (2^131) is
NON-worst-case; the true worst at n=96 already exceeds p. (scripts/probes/issue407-bind/probe_bind_realized_norm_max.py,
probe_bind_norm_crossover.py)

CONSEQUENCE: a "structure-aware UPPER bound giving |N|<p" CANNOT exist at the worst-case binding
weight for n≥96 — the realized worst-case norm itself exceeds p. The §5.0 open-route as stated
("replace the loose house by a tighter |N|<p") is a no-go past the crossover.

TEST 2 (the mechanism is real: explicit, INDEPENDENTLY-VERIFIED non-antipodal mod-p vanishers at thin
prize-β primes). For thin primes p (p>n^3, n|p-1, β=log_n p in the prize band 4–4.8) we exhibit
non-antipodal S with `Σ_{i∈S} ω^i ≡ 0 (mod p)` (ω a primitive n-th root in F_p), directly verified
(not via the bridge — the sum is computed in F_p and equals 0 on the chosen ω):
  • n=32,  p=14814881  (β=4.764): S={1,2,7,8,9,10,12,13,19,22,27} (#S=11), non-antipodal, Σω^i≡0.
  • n=64,  p=136085377 (β=4.503): #S=24 set, non-antipodal, Σω^i≡0.
  • n=128, p=268437889 (β=4.000): S={6,17,24,27,29,38,43,52,59,65,70,77,82,87,94,97,107,112,117}
    (#S=19), non-antipodal, Σω^i≡0; here house 19^64~2^272 ≫ p~2^28 (gate hyp `(#S)^φ<p` FALSE).
(scripts/probes/issue407-bind/probe_bind_counterexample_search.py + verify_bind_counterexamples.py
[standalone, from-scratch], probe_bind_n128_counterexample.py)

WALL / precise scope (NO prize refutation — honesty): these counterexamples use SMALL primes (p~2^24–2^28),
NOT the actual prize budget p~2^128, so the PRIZE is NOT refuted. What is refuted is the GENERALITY of
the gate route: (BIND) is FALSE as a ∀-thin-prime statement; non-antipodal vanishing genuinely occurs
exactly when `(#S)^φ(n) > p`. §5.0's "NoSpuriousVanishing proved for n≤32" is correct ONLY because at
the prize budget p~2^128 and n≤64 the house hypothesis `(#S)^φ < p` happens to hold for ALL relevant #S
(e.g. n=32: p^{1/φ}=2^8=256 > n). Once n grows so that (n/4)^{n/2} > 2^128 (i.e. n≥~112 at the binding
size), the house hypothesis fails AND — by Test 1 — no realized-norm replacement can rescue it. The
gate/house lane is therefore CAPPED at the crossover; closing CORE at n≥112 needs a genuinely different
mechanism (the thinness-essential B_∞←B_{log n} Sidon bootstrap), not a sharper norm bound on the gate.
Constraint lemma: `∃ non-antipodal S, ω prim. n-th root in F_p : Σ_{i∈S}ω^i=0` for every thin p with
(#S)^{φ(n)}>p — so the gate's safety margin is exactly `house < p`, nothing more.

## wf-NC — Gross-Koblitz / p-adic Γ_p refinement of Stickelberger (UNIT part) — PINNED (2026-06-14)

Lens: GK expresses g(χ^{−a}) = −π^a·Γ_p(⟨a/(p−1)⟩) (q=p prime ⇒ residue degree f=1);
η_b = (1/m)Σ_k ζ_{p−1}^{−nkc} g(χ^{nk}) is a ζ-weighted sum of GK factors. Hoped: dyadic
base-p digit-sum of a=nk + Γ_p reflection/multiplication ⇒ sub-trivial archimedean max_b|η_b|.
All numerics exact-as-float ~1e-14, n=8,16,32, multiple p≡1 (mod n).

- NC1 (f=1 single Γ_p factor): for q prime the GK product runs over the Frobenius orbit of size
  f=1 → ONE Γ_p factor per Gauss sum. No multi-factor product ⇒ the dyadic digit-sum handle is
  STRUCTURALLY ABSENT. The genuine multi-Γ_p / digit-sum lever needs f≥2 (q a prime power), which
  the prize forbids. (probe_wf2NC_gammap_valuation.py)
- NC2 (unit part has no archimedean SUP content): GK pins v_p(g)=a/(p−1) (=Stickelberger=section-6
  magnitude) and the unit Γ_p as a p-adic unit (|Γ_p|_p=1); |g|=√p is archimedean, independent of
  the unit congruence. Adversarial test (4000 trials): SUP achievable under the Γ_p reflection
  U(nk)U(−nk)=+1 EQUALS the SUP under |U|=1 alone (~0.86–0.95·√(p−n)); true SUP (0.58–0.79·√(p−n))
  sits strictly below, i.e. the genuine cancellation is NOT a GK relation. (probe_wf2NC_sup_vs_gk.py,
  probe_wf2NC_gk_phase.py)
- NC3 (no product→sum bridge): Davenport-Hasse/Stickelberger pin Π_k g(χ^{nk}) (= the norm/house,
  section-6 magnitude object), verified exact (rel.err ~1e-14); the SUP needs max_c|Σ_k ...|. A single
  product equation among m−1 unit phases does not bound a max-of-sum. (probe_wf2NC_gammap_valuation.py)

Why NEW (vs section-6 Stickelberger MAGNITUDE no-go): this is the complementary fact — the GK
unit/Γ_p part (the thing section-6 excludes) carries NO archimedean SUP info at f=1, and the only
digit-sum handle lives at f≥2 off the prize. The reflection formula reduces to the already-refuted
antipodal char-0 symmetry (T09-leak). Wall: GK adds nothing to max_b|η_b| for q prime.

## census<->CORE — the universal census bound is LOSSY, caps at Johnson, NOT equivalent to CORE (2026-06-14)

Lens: the count/census lane (`UniversalAlignmentLaw.badScalars_card_le_alignableSets`) bounds
`#{bad γ} ≤ #alignableSets(dom,k,a,u0,u1)`, feeding δ* via `epsMCA_le_of_alignableSets_card_le`.
#407 brief flags the "census ⟺ CORE equivalence" as ASSERTED-BUT-NEVER-PROVEN. Tested the tightness
directly: exact `#bad` (the CORE/incidence object) vs exact `#alignableSets` (census), thin proper
μ_16 ⊊ F_p*, large primes p≫n³, binding monomial direction u0=x^10,u1=x^4.
Probe: `scripts/probes/probe_407_census_core_tightness.py` (exact, no enumeration; left-null affine-γ).

- RESULT (p-INDEPENDENT across p=200017/500113/1000033):
  | r (a=n−r) | δ=r/n | #bad (CORE) | #alignableSets (census) | ratio |
  |---|---|---|---|---|
  | 8 (a=8) | .5000 | 9  | 10  | 1.11 |
  | 9 (a=7) | .5625 | 9  | 80  | 8.89 |
  | 10 (a=6)| .6250 | 89 | 456 | 5.12 |
  Budget = n = 16. **True δ* = 9/16** (#bad ≤ 16 through r=9, first bad r=10).
  **Census δ* = 8/16 = JOHNSON** (#alignableSets first exceeds 16 at r=9: 80 > 16).

- WALL / CONSTRAINT LEMMA: the census bound is **strictly lossy by a p-independent factor
  (5–9×) that turns on exactly at the beyond-Johnson rung**. Census `#alignableSets ≤ budget`
  fails at r=9 while the true incidence `#bad ≤ budget` holds, so **any δ* bound proven through
  the census/alignable-set count recovers at most JOHNSON (δ*=8/16), never the beyond-Johnson
  window**. The census overshoot = (every a-set that aligns for SOME γ is counted, but distinct
  aligned a-sets share γ's; `Aligned.gamma_eq` injectivity gives the ≤ direction but the reverse
  is many-to-one) ⟹ census counts aligned-sets, CORE counts γ's; the fibers have p-independent
  size 5–9 at the binding radii.
- THEREFORE: "census ⟺ CORE" is **FALSE**. Proving the count-lane bound (ExplainableCoreSupply /
  CensusDomination / SubJohnsonListBound) is NOT proving CORE in the prize window — it is a strictly
  weaker (Johnson-capped) handle. This is independent of, and complementary to, the §3 second-order
  cap (B5 already showed the count-lane is exponential-class, not second-order; THIS shows that even
  so, its δ* CERTIFICATE is Johnson-capped by the alignable-set overshoot). The beyond-Johnson rung
  is carried only by the γ-incidence (CORE/F2) count, which the census cannot see.

### census fiber structure (sharpening, 2026-06-14): fibers NON-UNIFORM (1..56), p-independent — census UN-repairable
Per-γ fiber size (# aligned a-sets a single bad γ owns), n=16 k=4, p-independent (p=200017/500113):
- r=9 (a=7): {8:×8, 16:×1} — total 80 over 9 γ.
- r=10 (a=6): {1:×16, 2:×64, 32:×8, 56:×1} — total 456 over 89 γ; max fiber 56.
The census overshoot is NOT a uniform constant — fibers range 1..56, a few heavy γ own huge fibers.
So census CANNOT be repaired into a CORE-tight bound by dividing by any fixed fiber size; the deflation
factor is itself a per-γ combinatorial quantity. Even the single worst γ is census-over-counted up to 56×.
The fiber-size multiset is a p-independent invariant of the binding configuration. Reinforces: the
count/census lane is Johnson-capped, cannot reach the prize window. (probe_407_census_core_tightness.py + /tmp/fiber.py)

## phase-alignment "tower self-similarity" — REFUTED, the alignment is just REALITY (2026-06-15)

Lens: the fleet observed at the worst frequency b* the two half-coset sums
S0(b*)=∑_{x∈μ_{n/2}} e_p(b*x), S1(b*)=∑_{x∈μ_{n/2}} e_p(b*·rep·x) are maximally phase-aligned
(cos=1.0000, machine-exact n=8,16,32,64). Floated as a candidate NON-AVERAGE structural handle
(tower-recursive self-similarity for a descent/Stepanov argument, since moment methods are blind
to worst-frequency alignment). Brief flagged this lane explicitly (phase-alignment tower probes).

Adversarial recheck (scripts/probes/probe_407_phase_dichotomy.py, probe_407_phase_why.py,
probe_407_phase_reality.py — all FFT-exact, ~1e-14):
- cos(S0(b),S1(b)) = ±1 for EVERY frequency b (256/256, 599/599 sampled), not just b*. The two
  half-coset sums are ALWAYS real-collinear.
- Holds IDENTICALLY in the THIN (β≈9.8, deep prize) AND THICK (β≈1.07, very thick) regimes. The
  cosine is ±1 everywhere; the sporadic −1 are sign flips of two REAL numbers, not a regime signal.
- ROOT CAUSE: μ_{n/2} is a 2-power cyclic subgroup of EVEN order n/2 ⇒ contains the unique order-2
  element −1 ⇒ closed under negation ⇒ S0(b)=∑ e_p(bx) is REAL (pair x↔−x). Verified
  max|Im S0(b)| ~ 1e-15. Two reals are trivially collinear ⇒ cos=±1 automatic.

CONSTRAINT LEMMA (axiom-clean Lean, Frontier/_PhaseAlignmentReality.lean):
`eta_real_of_neg_closed` — if G is closed under negation then eta ψ G b = ∑_{y∈G} ψ(b·y) is REAL
(conj-invariant) for every b. #print axioms ⊆ {propext, Classical.choice, Quot.sound}.

WALL: the "phase alignment" is forced by reality, holds for ALL b, and is identical in the thick
window where the prize is FALSE ⇒ it is NOT thinness-essential. Any descent built on cos(S0,S1)=±1
is thickness-monotone, which rule-3/§3 forbids. The alignment carries NO worst-frequency information
beyond "the half-coset sum is real," which is true unconditionally. Lane PINNED — not a non-average
handle.

## moment "count/Markov/EVT-tail" packaging is NOT sharper — one object in four costumes (2026-06-14)

Adversarial audit of the freshly-landed `MomentCountSupBound.forall_le_of_sum_pow_lt` (commit
64c0bc081), whose docstring claims the integer-tail-count argument is "SHARPER than the per-term
‖η_b‖^{2r} ≤ ∑ bound (it uses that a fractional count rounds down to zero)."

VERDICT: not asymptotically sharper. The count route certifies `a_b ≤ T` only under the STRICT
hypothesis `∑_b a_b^r < T^r`, i.e. for `T > Tᵣ := (∑ a^r)^{1/r}` strictly. The per-term route gives
the CLOSED bound `a_b ≤ Tᵣ` directly. Both families have the SAME infimal usable threshold `Tᵣ`; the
integer-rounding only discards the measure-zero boundary `∑ a^r = T^r`, never an asymptotic factor.

PROBE (scripts/probes/probe_407_count_vs_perterm.py, exact FFT, thin μ_n ⊊ F_p*, p~n^3.5-4): at EVERY
fixed r the per-term bound (∑ a^r)^{1/r} and the count-route infimal threshold coincide to machine
precision:
  n=8 β=4 p=4129:   r=2 830.41 / r=3 275.36 / r=5 125.96 / r=8 86.67  (per-term == count, all r)
  n=16 β=4 p=65537: r=2 6864.48 / r=3 1488.32 / r=5 504.80 / r=8 307.79 (equal, all r)
  n=16 β=3.5 p=16417: r=2 3428.51 / r=3 933.42 / r=5 376.79 / r=8 254.79 (equal, all r)

CONSEQUENCE: the direct ℓ^{2r}-root route (MomentSupNormBridge.sup_le_moment_root), the per-term root
(eta_le_optimized), the Markov tail bound (PeriodTailMarkov.card_filter_mul_le_sum_pow), and the
integer-count bound (MomentCountSupBound) ALL optimize the SINGLE object `min_r (∑_b ‖η_b‖^{2r})^{1/2r}`,
landing at the identical sqrt(n·log q)-gapped bound. Re-packaging the moment bound as a Markov tail /
integer count / EVT histogram does NOT escape the BGK √-cancellation wall. The EVT/tail-rate reframing
is the same analytic object in different costume; its open content stays `A_r ≤ Wick` (= BGK).

RIGOROUS Lean (MomentCountSupNotSharper.lean, axiom-clean {propext, Classical.choice, Quot.sound}):
- `forall_le_rpow_root`: the per-term CLOSED bound `∀ b, a_b ≤ (∑ a^r)^{1/r}` (count route not needed).
- `count_threshold_not_below_perterm`: for any `T < Tᵣ`, the count hypothesis `∑ a^r < T^r` is FALSE
  (`T^r ≤ ∑ a^r`), so the count route CANNOT certify a threshold below `Tᵣ`. Same infimum, no escape.

## DC-subtracted A_r<=Wick: CONFIRMED at prize DEPTH (r~ln q) for n=32..256 — ratio collapses, no catch-up failure (2026-06-14)

Follow-up confirmation of the 2026-06-14 ★★ correction (raw E_r<=Wick FALSE for n>=64; only the
DC-subtracted A_r = E_r - n^{2r}/q <= Wick is the correct prize input). The correction established A_r<=Wick
is "measured true" but did NOT publish the r-PROFILE at the prize depth r~ln q for n past the n=64 DC
crossover. Decisive question: does A_r CATCH UP to Wick at large r (the failure mode that killed raw E_r),
or stay below? Probe scripts/probes/probe_407_Ar_wick_depth_profile.py (exact FFT, thin mu_n subset F_p*,
p~n^3-4.5, A_r = (1/q) sum_{b!=0} |eta_b|^{2r}, Wick=(2r-1)!!*n^r):

| n   | p (q)     | r*=round(ln q) | A_r/Wick @ r=2 | @ r=4 | @ r=8 | @ r=r* |
|-----|-----------|----------------|----------------|-------|-------|--------|
| 32  | ~1.5e7    | 16             | 0.969          | 0.824 | 0.404 | 0.0156 |
| 64  | 16777601  | 17             | 0.984          | 0.908 | 0.710 | 0.119  |
| 128 | 14605697  | 16             | 0.992          | 0.946 | 0.647 | 0.0294 |
| 256 | 16777729  | 17             | 0.995          | 0.945 | 0.547 | 0.0051 |

VERDICT (confirmation, not closure): A_r<=Wick holds at EVERY depth through r~ln q, and the ratio A_r/Wick
DECREASES monotonically in r (0.99 at r=2 down to ~0.005-0.12 at the prize depth). So A_r is increasingly
BELOW Wick at the optimal order — the "A_r catches up to Wick at large r" failure mode (which killed raw
E_r via the DC term) does NOT occur for the DC-subtracted energy. The DC-subtracted reduction is robustly
non-vacuous with room to spare at prize depth across the prize-band n.

HONEST CAVEAT (why this is NOT the prize): these p are sub-prize (p~2^24, not 2^128), so this confirms the
r-profile shape and rules out the catch-up failure mode, but does NOT certify A_r<=Wick UNIFORMLY across
ALL fields at the actual prize budget — that uniform-in-field bound at depth r~log q IS the BGK wall (the
prize is forall-field-universal, c.154). The open content remains exactly A_r<=Wick as a thinness-essential
forall-field theorem. Value: pins the correct object's empirical r-profile (collapsing ratio), strengthening
confidence that the DC reduction is the right target and quantifying the numerical slack at prize depth.

## moment-certificate SLACK is THICKNESS-INVARIANT — the moment route cannot be the rule-3 thinness-essential lever (2026-06-15)

WALL / CONSTRAINT (rule-3 mapping). The DC-subtracted moment chain certifies the sup-norm via
`M(n) = max_{b!=0}|eta_b| <= min_r (q*A_r)^{1/2r}` (the moment certificate; `q*A_r = sum_{b!=0}|eta_b|^{2r}`).
Two facts were already known: (a) `A_r<=Wick` is measured-true at prize depth with collapsing ratio
(prior entry), and (b) the count/Markov/EVT-tail packagings are one object min_r(q A_r)^{1/2r} "in four
costumes" (not sharper). MISSING test: is this object **thinness-essential**? Rule 3 says any valid CORE
proof's certifying inequality must be FALSE in the thick window (beta~2.3-3.2) and TRUE only in thin
(beta~4-5). A thickness-INVARIANT certificate quality therefore CANNOT be the prize lever.

PROBE (scripts/probes/probe_407_Ar_thinness_essential.py, exact FFT over PROPER mu_n < F_p^*, beta swept
ACROSS the thick AND thin windows; cert = min_r (q A_r)^{1/2r}, true = M(n)):

| n  | beta (p)       | A_r<=Wick? (A_r/Wick @ r~lnq) | M/sqrt(n) | target sqrt(log(p/n)) | cert/true |
|----|----------------|-------------------------------|-----------|-----------------------|-----------|
| 8  | 2.27 (113)     | YES (0.049)                   | 1.808     | 1.627                 | 1.197     |
| 8  | 2.71 (281)     | YES (0.053)                   | 2.146     | 1.887                 | 1.181     |
| 8  | 3.20 (769)     | YES (0.040)                   | 2.430     | 2.137                 | 1.159     |
| 8  | 3.60 (1777)    | YES (0.051)                   | 2.547     | 2.324                 | 1.185     |
| 8  | 4.00 (4073)    | YES (0.023)                   | 2.665     | 2.497                 | 1.169     |
| 8  | 4.50 (11593)   | YES (0.009)                   | 2.714     | 2.698                 | 1.187     |
| 16 | 2.30 (593)     | YES (0.033)                   | 2.110     | 1.901                 | 1.210     |
| 16 | 2.70 (1777)    | YES (0.096)                   | 2.715     | 2.170                 | 1.173     |
| 16 | 3.00 (4129)    | YES (0.045)                   | 2.785     | 2.357                 | 1.171     |
| 16 | 3.30 (9377)    | YES (0.043)                   | 3.043     | 2.525                 | 1.153     |

TWO VERDICTS:
1. `A_r<=Wick` holds in BOTH the thick AND thin windows (ratio 0.03-0.10 thick, 0.009-0.023 thin) =>
   `A_r<=Wick` is NOT thinness-essential. It is honest substrate, true with room to spare across all beta.
   The thinness CANNOT live in the input inequality A_r<=Wick.
2. **The moment certificate's SLACK `cert/true = (min_r (q A_r)^{1/2r}) / M(n)` is THICKNESS-INVARIANT,
   locked at 1.15-1.21 across the ENTIRE beta window (thick 2.27 -> thin 4.5) and across n=8,16.** The
   moment route overshoots the true sup-norm by a constant ~18% that does NOT depend on thinness. Since the
   certificate quality is beta-uniform, the moment family (energy/Wick + count/Markov/EVT-tail, all four
   costumes) CANNOT be the rule-3 thinness-essential mechanism: a thickness-monotone certificate cannot
   prove a bound that is FALSE in the thick window. Any beta-aware refinement of A_r<=Wick is ruled out as
   a prize lever -- the residual ~18% slack lives in the moment->sup passage M<=(q A_r)^{1/2r}, and that
   passage's loss is regime-uniform.

WHERE THIS LEAVES THE OPEN CONTENT (mapping, not closure): not in tightening A_r<=Wick (beta-uniformly
far below Wick), not in the moment->sup step (beta-uniform constant slack). Corroborates "one object in
four costumes": the WHOLE moment family is beta-uniform, hence rule-3-incompatible standalone. A genuine
CORE proof must use a thinness-DISCRIMINATING object whose certifying inequality flips sign between the
thick and thin windows -- the moment certificate provably is not such an object.

HONEST CAVEAT: small-n / sub-prize p (p<=~12k, not 2^128); this maps the certificate's regime-behavior
shape, it does NOT itself prove or refute the prize. No Lean theorem claimed (the thickness-invariance is
an empirical measurement; proving the constant-slack would itself require BGK). Reproducible probe + this
constraint entry are the deliverable, per rule 4 (a precisely-mapped wall is a WIN).

## thinness-discriminator search: normalized prize-ratio R and shallow Sidon-depth are NOT decisive rule-3 discriminators (2026-06-15)

CONTEXT. Prior entry (82581fb79) showed the moment certificate is thickness-INVARIANT, so the prize
lever must be a thinness-DISCRIMINATING object (certifying quantity bounded in thin beta~4-5, ill-behaved
in thick beta~2.3-3.2). This entry tests the two most natural candidates and finds NEITHER is a clean
discriminator at accessible scale -- narrowing where the real lever can live.

PROBE (scripts/probes/probe_407_thinness_discriminator.py, exact FFT/enumeration, proper mu_n<F_p^*):

D1 -- normalized prize ratio R(n,p) = M(n)/(sqrt(n)*sqrt(log(p/n))) (prize wants R<=C absolute):
| n  | beta | R      |          | n  | beta | R      |
|----|------|--------|          |----|------|--------|
| 8  | 2.27 | 1.111  |          | 16 | 2.30 | 1.110  |
| 8  | 2.71 | 1.137  |          | 16 | 2.70 | 1.251  |
| 8  | 3.20 | 1.137  |          | 16 | 3.00 | 1.182  |
| 8  | 3.60 | 1.096  |          | 16 | 3.30 | 1.205  |
| 8  | 4.00 | 1.067  |          | 16 | 3.60 | 1.152  |
| 8  | 4.50 | 1.006  |          |    |      |        |
  n=8 avg R: thick(beta<3.3)=1.129, thin(beta>=3.9)=1.037 -- mild thin-TIGHTENING toward ~1.0.
  n=16: R is NON-monotone, stays ~1.10-1.25 across all beta (no clean convergence; no thick blow-up).
  VERDICT: R is O(1) in BOTH regimes. The n=8 convergence to 1.006 at beta=4.5 is suggestive but is
  likely a small-n artifact (only n=8 reaches beta=4.5 cheaply); n=16 shows R bounded but NOT
  thin-converging. R is NOT a decisive rule-3 discriminator -- it does not blow up in the thick window,
  it just sits at a slightly higher O(1) constant there. (Consistent: sqrt(log(p/n)) is the right SCALE
  in both regimes up to a constant; the prize's open content is the absolute CONSTANT, not the scale.)

D2 -- shallow additive Sidon-depth signature (waste = 1 - distinct(r-fold sumset)/n^r; lower=more Sidon):
| n  | beta | r=2 waste | r=3 waste | r=4 waste |
|----|------|-----------|-----------|-----------|
| 8  | 2.53 | 0.484     | 0.8125    | 0.9607    |
| 8  | 4.00 | 0.484     | 0.8125    | 0.9451    |
| 16 | 2.49 | 0.496     | 0.8359    | 0.9846    |
| 16 | 4.00 | 0.496     | 0.8281    | 0.9560    |
  VERDICT: r=2 and r=3 waste are IDENTICAL thick vs thin (field-blind) -- the shallow additive structure
  of mu_n is determined by n, not p (consistent with brief's "mu_n is B_inf-Sidon to depth ~log n"
  regardless of field). Only at r=4 does thin show modestly less waste (more distinct, 0.945 vs 0.961
  n=8; 0.956 vs 0.985 n=16) -- the depth where small thick-p starts forcing extra collisions. So shallow
  Sidon-depth is NOT a thinness discriminator; any signal would be DEEP (r ~ log n), exactly the
  inaccessible-by-enumeration regime that IS the B_inf <- B_{log n} bootstrap wall.

NET (mapping): the two natural discriminators both FAIL to cleanly separate thin from thick at accessible
scale -- R stays O(1) in both (the open content is the absolute constant, scale is right in both regimes),
and Sidon-structure is field-blind until depth r~log n (the inaccessible bootstrap regime). This narrows
the rule-3 lever: it must live at DEEP additive order r~log n (the B_inf<-B_{log n} bootstrap), not in any
shallow/normalized O(1) statistic -- consistent with the 25-yr wall being genuinely a deep-order phenomenon.

HONEST CAVEAT: small-n / sub-prize p; reproducible probe maps the discriminator candidates' behavior, does
not prove/refute the prize. No Lean theorem claimed. Per rule 4, a precisely-mapped non-discriminator is a WIN.

## K1 / antipodal-pairing residual H FAILS at the prize scale — derivable refutation (2026-06-14)

The in-tree GaussianEnergyFromPairing.gaussianEnergyBound_of_pairing derives the raw Wick carrier
GaussianEnergyBound G r (E_r <= (2r-1)!!*|G|^r) from three inputs: unconditional henergy (negation-closure
energy = zeroSumCount), unconditional hcount (#pairings <= (2r-1)!!), and the genuine open input H = the
ANTIPODAL-PAIRING RESIDUAL ("every zero-sum 2r-tuple of G is antipodally paired").

The 2026-06-14 ★★ correction (DCEnergyEssential.not_gaussianEnergyBound_of_card_pow_gt) PROVES the
conclusion GaussianEnergyBound G r is FALSE when q*(2r-1)!! < |G|^r (the prize regime: n>=64 at r~log q,
DC term |G|^{2r}/q >> Wick). By modus tollens (henergy, hcount unconditional), H ITSELF IS FALSE at prize.

LANDED: PairingResidualFailsAtPrize.not_pairing_residual_of_card_pow_gt (axiom-clean
{propext, Classical.choice, Quot.sound}): under henergy + hcount, q*(2r-1)!! < |G|^r => NOT H, i.e. there
EXISTS a zero-sum 2r-tuple of G that is NOT antipodally paired.

INTERPRETATION (mapped wall): the above-threshold antipodal-pairing structure (true in char 0 / Lam-Leung
and at small n) is DESTROYED by the char-p anomaly at n>=64, r~log q. The non-antipodal zero-sum tuples
are exactly the char-p extra solutions the DC term counts (E_r >= |G|^{2r}/q >> Wick). So the K1 / pairing
route CANNOT supply the prize carrier E_r <= Wick at prize scale; only the DC-subtracted A_r <= Wick
survives (the genuinely thinness-essential object — consistent with the A_r r-profile confirmation note
above). The pairing/Lam-Leung char-0 route is prize-DEAD without DC subtraction; the bricks consuming raw
GaussianEnergyBound (GaussianEnergyFromPairing, GaussianEnergyThreeRepThree's r=3 rung) are vacuous /
have prize-false hypotheses at n>=64 exactly as eta_le_optimized is.

## SIGNED deep period-power cancellation IS thinness-essential — and the moment certificate's |.| destroys it (2026-06-15)

THE FIND (positive structural map, the missing rule-3 signal). Prior entries showed the moment certificate
min_r (q A_r)^{1/2r} is thickness-INVARIANT and shallow statistics are field-blind, leaving the rule-3
lever at deep additive order. This locates it: the SIGNED deep period-power sum.

Since mu_n is negation-closed, eta_b in R. Define the normalized signed deep sum
    C_r(n,p) = |sum_{b!=0} eta_b^r| / ((p-1) * M^r),   M = max_{b!=0}|eta_b|.
C_r=1 means no cancellation (all eta_b^r aligned); C_r->0 means strong signed cancellation across b.
(Note sum_{b!=0} eta_b^r is the deep additive structure: p*W_r/... = 1 + (1/n^r) sum_{b!=0} eta_b^r.)

PROBE (scripts/probes/probe_407_deep_sidon_depth.py + probe_407_signed_deep_cancellation.py, exact, proper mu_n):
| n  | beta | C_2   | C_4   | C_6   | C_8    | C_10   |
|----|------|-------|-------|-------|--------|--------|
| 16 | 2.49 | 0.210 | 0.116 | 0.081 | 0.063  | 0.052  |   (THICK)
| 16 | 4.00 | 0.084 | 0.020 | 0.0072| 0.0034 | 0.0019 |   (THIN)
| 8  | 2.53 | 0.214 | 0.113 | 0.081 | 0.066  |   -    |   (THICK)
| 8  | 4.50 | 0.136 | 0.048 | 0.025 | 0.016  |   -    |   (THIN)

THIN/THICK cancellation ratio (thick C_r / thin C_r), n=16: r2=2.5x, r4=5.8x, r6=11x, r8=18x, r10=27x.

VERDICT (thinness-ESSENTIAL, rule-3 compatible):
- C_r is strictly SMALLER (stronger signed cancellation) in THIN than THICK at EVERY r, and the thin/thick
  ratio GROWS with depth r (2.5x at r=2 up to 27x at r=10 for n=16). This is the deep-order, thinness-
  ESSENTIAL phenomenon rule 3 demands: a quantity whose behavior genuinely separates thin from thick and
  whose separation strengthens at the prize depth r~log n. Unlike A_r<=Wick (beta-uniform) and the moment
  certificate (thickness-invariant), the SIGNED period-power sum sum_{b!=0} eta_b^r carries the thinness.
- MECHANISM for WHY the moment route fails (closes the prior 'four costumes' map): the moment certificate
  uses sum_{b!=0}|eta_b|^{2r} (absolute values), which DESTROYS the signed cancellation. The thinness-
  essential content lives in the SIGNED sum sum_{b!=0} eta_b^r; taking |.| (as every moment/energy/Wick/
  count/EVT packaging does) discards exactly the cancellation that distinguishes thin from thick. THIS is
  why the moment family is thickness-invariant (prior entry) and cannot be the lever: |.| is the leak.

WHERE THE OPEN PRIZE LEVER NOW SITS (sharpened, positive): a bound on M must exploit the SIGNED deep
cancellation in sum_{b!=0} eta_b^r (which IS thinness-essential, growing with r), NOT the absolute moment.
This is consistent with the BGK/Stepanov flavor (signed/algebraic cancellation, not measure/energy). Any
method that passes through |eta_b| at any step is provably rule-3-incompatible (loses the thin signal).

HONEST CAVEAT: small-n / sub-prize p (<=65537); exact-verified at this scale. Maps the thinness-essential
object + the |.|-leak mechanism; does NOT prove a uniform-in-field deep-cancellation bound (that bound at
r~log q IS the prize/BGK wall). No Lean theorem (a quantitative signed-cancellation bound = the open core).
Reproducible probes + this constraint/structure entry are the deliverable. Rule-4 mapped-frontier WIN, and
unlike a pure wall this is a POSITIVE localization: the lever exists, it is the signed deep sum, and the
moment route's |.| is precisely why nobody saw it.

## Pairing-route rung boundary r*(n,q): char-p anomaly invades the K1/pairing ladder at DESCENDING rungs (2026-06-14)

Sharpening of "K1/antipodal-pairing residual H FALSE at prize" (PairingResidualFailsAtPrize). For FIXED
prize (n,q), at which rung r does raw E_r <= Wick (=> H) FIRST fail? Probe
scripts/probes/probe_407_pairing_rung_boundary.py (exact FFT, E_r=(1/q)sum_all|eta_b|^{2r}, Wick=(2r-1)!!n^r):

| n   | beta | p        | r*=first r with E_r>Wick | DC-predicted r* | round(ln q) |
|-----|------|----------|--------------------------|-----------------|-------------|
| 32  | 4.5  | 5931649  | 15                       | 15              | 16          |
| 64  | 4.0  | 16777601 | 6                        | 7               | 17          |
| 128 | 3.4  | 14605697 | 4                        | 5               | 16          |
| 256 | 3.0  | 16777729 | 3                        | 4               | 17          |

The failing rung r* DESCENDS as n grows (15 -> 6 -> 4 -> 3), tracking the DC-crossover within ±1. So the
char-p anomaly invades the pairing/Wick ladder at progressively LOWER orders: at n=256 even r=3
(E_3/Wick=1.046) is prize-false. Consequence: the in-tree r=3 pairing rung GaussianEnergyThreeRepThree
(deriving GaussianEnergyBound G 3 from repThree) has a PRIZE-FALSE hypothesis for large n, just like
eta_le_optimized and the general H. Essentially the ENTIRE moment ladder above r=2 is pairing-dead at
prize scale (r* -> small as n -> infinity). Only the DC-subtracted A_r <= Wick survives at every rung
(confirmed separately: A_r/Wick collapses, never crosses 1). The char-0 Lam-Leung pairing structure is
not "loose at high r" but actively false from a low, n-shrinking rung onward — the DC subtraction is
the only repair. Reinforces: prize object = DC-subtracted A_r <= Wick, forall-field, = BGK wall.

## Anomaly-suppression in-window survival — bad primes INVADE the prize window (β_bad grows in n), but Anom_r ≤ n^{2r}/p STILL HOLDS there (2026-06-15)

LENS: the HEAD anomaly route (dbbe1b01e). `Anom_r(p) = E_r^(p) − E_r^(0) ≤ n^{2r}/p` is the SUFFICIENT
condition for `A_r ≤ Wick` (the DC-subtracted prize core). Orchestrator showed `Anom = EXACTLY 0` at n=8
prize primes (r≤6) and flagged the OPEN asymptotic: for large n the bad primes (where Anom>0) can reach the
prize window `[n^4, (2r)^{n/2}]` at r~log q.

TEST (exact, NEW angle = NORMS, no per-prime FFT for the onset):
`Anom_r(p) > 0  ⟺  p | N(α)` for some r-collision difference `α = Σζ^{a_i} − Σζ^{b_j} ≠ 0` in `Z[ζ_n]`.
So r-bad primes = prime factors of the norms `N(α)` (computed exactly via the φ=n/2 conjugate product,
ζ^φ=−1 for n=2^a). Probe `scripts/probes/probe_407_anom_badprime_norm_onset.py`.

RESULT 1 — bad-prime onset exponent β_bad = log_n(p_bad) GROWS in n, invading the prize window at LOWER r:
  n=8:  first r with p_bad ≥ n^4 is r=6 (β_bad 4.28)
  n=16: r=4 (β_bad 4.60)
  n=32: r=2 (β_bad 4.87)
=> the orchestrator's "Anom=0 at prize primes" is a SMALL-n ARTIFACT (at n=8 the window is bad-prime-free
below r=6). Matches the independently-observed pairing-rung descent (r* 15→6→4→3, b58cf1d03): the char-p
anomaly is NOT confined below the prize window asymptotically.

RESULT 2 — but the SUFFICIENT condition SURVIVES at the in-window bad primes (the real BGK test at scale):
n=16, r=4, ALL 26 in-window bad primes p ∈ [n^4=65536, 1.5e6]: `Anom_4(p) ≤ n^8/p` HELD at **26/26**,
TRUE WORST ratio = **0.4757** at p=76001 (β=4.053), i.e. ~2.1× margin. Probe
`scripts/probes/probe_407_anom_suppression_inwindow.py` (vectorized norms + exact FFT integer-count Anom).

NET (honest): a POSITIVE mapped-frontier result for the anomaly route — bad primes do invade the window
but the anomaly is suppressed there with margin at accessible scale. NOT a closure: sub-prize-budget primes
(p ≤ 1.5e6), fixed r; the worst PRIZE prime at r~log q, p~2^128 (the BGK content) is untouched. Complements
`probe_407_bgkproof_onset_growth` (which tracks the ratio along the r-axis at a fixed prime); this pins the
worst-case ACROSS the bad-prime set inside the window at fixed r. Both axes now bounded at accessible scale.

---

## [over-det δ*] s* budget-crossing: s*−k appears CONSTANT (=3) at accessible n — honest tension with floor (2026-06-15, opus-4-8 subagent)

Follow-up to the over-det incidence MAX closed form `I_max(n)=n³/32−n²/8+1` (push 0c7492b0d) and the
union-of-singletons p-independence brick (47dcd71b3, sibling). The δ* open item #2 is the budget-crossing
`s* = min{s : maxI(s) ≤ budget=n}`, giving `δ* = (n−s*)/n`.

PROBE (probe_407_sstar_budget_crossing.py, char-0 p≫n³, far-incidence COUNT per direction, s swept up
from k+2; MAX over directions; full-direction at n=16, antipodal-nbhd lower-bound at n=20):
- **n=16, k=2: s*=5 (FULL-direction verified — maxI(4)=97>16, maxI(5)=16≤16). s*−k=3. δ*=0.6875.**
- **n=16, k=4: s*=7 (antipodal-nbhd; matches the campaign's independently-published δ*=0.5625). s*−k=3.**
- **n=20, k=2: s*=5 (antipodal-nbhd ⟹ s* LOWER BOUND). s*−k=3. δ*=0.75.**

OBSERVATION: `s*−k = 3` is CONSTANT across n=16,20 AND k=2,4 in the accessible range — both k-independent
and n-independent here. This SHARPENS the prior `deltastar-407-char0-logn-over-n-candidate` note, which
conjectured `s*−k = log₂(n)` from only n=16,32 at ρ=1/8 (where log₂16=4, but my n=16 gives s*−k=3, not 4 —
the discrepancy is the budget/direction convention: my budget is exactly n, full-direction MAX).

HONEST TENSION (the decisive open question, NOT resolved here):
- IF `s*−k` stays constant → `δ* = 1 − (k+s*−k)/n → 1` (capacity) as n→∞, which would CONTRADICT the
  conjectured floor `δ* = 1−ρ−Θ(1/log n)` (a Θ(1/log n) gap BELOW capacity). i.e. constant-defect ⟹ δ*
  rises ABOVE the floor (toward capacity) asymptotically.
- BUT: this is exactly the doc's flagged pre-asymptotic regime (small n, coarse 1/n band granularity,
  the conjectured floor is itself below Johnson at these n = degenerate window). Constant-3 at n∈{16,20}
  CANNOT be extrapolated — n=32,64 (army's Rust engine, ~9.6h+ at ρ=1/4) is needed to see if s*−k grows.
- CAVEAT: my n=20 antipodal-nbhd s* is a LOWER BOUND (a non-antipodal direction could keep maxI above
  budget at s=5, pushing the true s* up). The constant could be an undercount artifact at n>16.

NET: a mapped data point (n=16 full-verified s*=5 ⟹ δ*=0.6875) + an honest tension (constant s*−k ⟹
δ*→capacity, contra the floor) that the army's large-n Rust must resolve. NOT a refutation of the floor
(small n, lower-bound s* at n>16). Logged, not receipted (over-det lane actively sibling-owned, 47dcd71b3 —
one-active-speaker; not crowding with a competing receipt).

## ★ REFINEMENT (sharpens the in-window survival entry above) — the SUFFICIENT proxy `Anom_r ≤ n^{2r}/p` FAILS at deep r at the worst prime, but the TARGET `A_r ≤ Wick` survives with margin (2026-06-15)

Combined-axes trajectory at the WORST in-window bad prime p=76001 (n=16, β=4.05), r=2..r*=round(log p)=7:
  r : Anom_r/(n^2r/p) [sufficient proxy] | A_r/Wick [actual target]
  2 : 0.000 | 0.936     5 : 0.870 | 0.517
  3 : 0.000 | 0.819     6 : 1.091 | 0.374  <-- proxy CROSSES 1
  4 : 0.476 | 0.671     7 : 1.188 | 0.255  <-- proxy > 1
So `Anom_r ≤ n^{2r}/p` (the clean sufficient form) FAILS at r=6,7 at the worst in-window prime — it does
NOT survive to the optimizer depth r*. The fixed-r=4 survival result (26/26) is correct but does NOT extend
to deep r at the worst prime.

CRUCIAL: the ACTUAL target `A_r ≤ Wick` HOLDS at EVERY r (0.94→0.67→0.52→0.37→0.26, monotone decreasing),
because `A_r ≤ Wick ⟸ Anom_r ≤ n^{2r}/p + (Wick − R_r)` and the `(Wick − R_r)` headroom absorbs the anomaly
overshoot at deep r. (Consistent with probe_407_bgkproof_onset_growth's decomposition.)

NET: the clean sufficient proxy `Anom_r ≤ n^{2r}/p` is the WRONG (too-strong) sufficient form at deep r — it
overshoots exactly where the moment optimizer sits. The true open object is `A_r ≤ Wick` directly (= the
DC-subtracted BGK core), which survives with margin at this accessible-scale prime but is NOT implied by the
clean Anom-proxy past r=5. Anyone trying to close CORE via `Anom_r ≤ n^{2r}/p` will hit this proxy-failure at
deep r; must use the `(Wick − R_r)` headroom (i.e. the full `A_r ≤ Wick`), not the clean proxy.
Probe scripts/probes/probe_407_anom_worst_rtraj.py.

## ★ POSITIVE reframing — `A_r/Wick` is MONOTONE-DECREASING & ≤1 in THIN, but EXCEEDS 1 & non-monotone in THICK ⟹ a base-case+monotonicity proof of `A_r ≤ Wick` is automatically THINNESS-ESSENTIAL (2026-06-15)

LENS: the genuine open prize object is `A_r ≤ Wick` (DC-subtracted, ∀-thin-field, r~log q = BGK). Candidate
reduction lever: `f(r) := A_r/Wick`. The C14 batch + my p=76001 trajectory both showed f monotone-DECREASING.
IF f(1) ≤ 1 (PROVEN: base_case_strict, A_1 < Wick) AND f(r+1) ≤ f(r), then `A_r ≤ Wick` ∀r by monotonicity.

TEST (exact FFT spectrum + integer cross-check, probe scripts/probes/probe_407_ArWick_monotone_thinness.py):
- THIN (prize, β 3.9-4.6, n=8,16,32): f(r) MONOTONE-DECREASING and ≤ 1 at EVERY r. Robust across n, β, p.
  (e.g. n=32 β=4.2 p=2097857: f = 1.00, 0.97, 0.91, 0.82, 0.71, 0.59, 0.46 — clean.)
- THICK: mostly monotone too, EXCEPT the maximally-2-structured n=32 in F_4129 (β=2.40, v₂=16): f RISES
  ABOVE 1 from r=2 (peak 1.705 @ r=5) and is NON-monotone. EXACT integer cross-check: E_2=3744, A_2=3490 >
  Wick=3072 (A_2/Wick=1.136) — `A_r > Wick` genuinely FALSE in that thick window.

NET (POSITIVE, rule-3-correct): the property "f(1) ≤ 1 AND f monotone-decreasing" HOLDS in thin and FAILS in
thick (f exceeds 1 + non-monotone). So a proof of `A_r ≤ Wick` via [base case f(1)≤1] + [single-step
monotonicity f(r+1) ≤ f(r)] is AUTOMATICALLY thinness-essential — any thickness-monotone method is ruled out
because the thick window violates BOTH ingredients. This REFRAMES the open core from the sup-norm / "A_r ≤ Wick
∀r" to the SINGLE-STEP monotonicity `A_{r+1}/Wick ≤ A_r/Wick` at r~log q. Still BGK-hard (the deep-r single
step IS the hard inequality), but a cleaner, rule-3-satisfying target than the sup-norm directly. NOT a
closure — the deep-r monotonicity step at the worst thin prize prime is the irreducible content; no Lean
theorem (proving the single step uniformly = BGK).

## ★ SHARPENING — the monotonicity step is the clean inequality `A_{r+1}/A_r ≤ (2r+1)n`; holds THIN with GROWING margin, fails THICK (2026-06-15)

Sharpens the A_r/Wick-monotonicity reframing above. The step f(r+1) ≤ f(r) is EXACTLY:
   A_{r+1}/Wick_{r+1} ≤ A_r/Wick_r  ⟺  A_{r+1}/A_r ≤ Wick_{r+1}/Wick_r = (2r+1)·n.       (STEP)
Since A_{r+1}/A_r is a |eta_b|^{2r}-weighted average of |eta_b|^2, A_{r+1}/A_r ≤ M^2; and (STEP) at r~log q
⟺ M^2 ≤ (2r+1)n ≈ 2n log q = the PRIZE. So (STEP) at deep r ⟺ prize (BGK-hard, confirmed).

MEASURED (exact FFT spectrum, g(r) = (A_{r+1}/A_r)/((2r+1)n), STEP holds iff g ≤ 1):
- THIN (prize β 4.0-4.5, n=16,32): g(r) ≤ 1 at EVERY r [STEP holds], AND g(r) DECREASES in r
  (n=32 β=4.5: 0.97,0.94,0.91,0.88,0.85,0.82,0.80) — the step gets EASIER at deeper r in thin (growing
  margin). (A_{r+1}/A_r)/M^2 stays 0.15-0.8 ≪ 1: the consecutive-moment ratio is far below the sup at
  accessible r (heavy tail not yet dominating).
- THICK (maximally-2-structured n=32/F_4129, β=2.40): g(r) = 1.145, 1.225, 1.167, 1.050, … > 1 at low r
  [STEP FAILS], exactly the rungs where A_r > Wick.

NET: the open core reframes to the SINGLE consecutive-moment-ratio bound `A_{r+1}/A_r ≤ (2r+1)n` at r~log q,
which holds thin with MEASURED GROWING margin and fails thick (rule-3-correct). The growing thin margin at
accessible r is encouraging but the deep-r limit A_{r+1}/A_r → M^2 = the prize; NOT a closure (proving the
single step uniformly at r~log q in thin = BGK). Probe scripts/probes/probe_407_moment_ratio_step_thinness.py.

## ⚠️ TEMPERING DATA — the thin single-step margin g(r*) at the OPTIMIZER ERODES as n grows (honest counter-weight to the "growing margin" reframing) (2026-06-15)

Counter-weight to the A_{r+1}/A_r ≤ (2r+1)n reframing's encouraging "growing margin in r" note. The r-axis
margin grows at FIXED n, but the prize is the n→∞ limit, so the decisive axis is g(r*) vs n at the optimizer
r*=round(log p). Exact FFT spectrum, thin β=4:
  n=8  r*=8  g(r*)=0.366 ; n=16 r*=11 g=0.468 ; n=32 r*=14 g=0.530 ; n=64 r*=17 g=0.643.
g(r*) stays < 1 (STEP holds at the optimizer) at ALL accessible n, BUT INCREASES in n (0.37→0.64) — the
margin SHRINKS. M^2/(2n ln p) similarly rises 0.43→0.70. So the "growing margin" optimism is r-axis only;
on the n-axis the margin erodes toward 1. n≤64 is sub-linear but CANNOT distinguish "saturates below 1"
(prize provable via this step) from "creeps to 1" (BGK-tight) — that crossover IS the open content. Honest:
NO extrapolation claim, NO closure; this tempers the reframing rather than advancing it. Probe
scripts/probes/probe_407_step_at_rstar_ntrend.py.

## ★ FORMULA-SCOPE REFUTATION — the in-tree δ* formula ½+(1/(2ρ)−1)/n BREAKS at small ρ (k=2); exact s* sweep (2026-06-15)

CONTEXT: the orchestrator's SOTA consolidation (c.02:27:52Z, §3) flagged the SINGLE decisive open computation:
"a cheap large-n k=2 sweep (small s*)" to settle whether δ*_far-line tracks the floor 1−ρ−Θ(1/log n), noting
"at n=32,k=2 the small-n formula predicts s*=9 but the engine measures s*=6, δ*=0.8125 — the formula breaks
upward." I ran the exact k=2 over-determined far-line incidence s* sweep (Rust pg engine, validated; + an
independent Python extremal-neighborhood probe, both agree) and PINNED the break exactly.

EXACT DATA (char-0 prize prime p~n^4, VALID subgroup p≡1 mod n verified, budget=n, full over-det incidence):
  n=16,k=2: s=4 maxI=97(bad) → s=5 maxI=16(GOOD) ⟹ s*=5, s*−k=3, δ*=0.6875
  n=32,k=2: s=4 maxI=897 → s=5 maxI=90 → s=6 maxI=25(GOOD) ⟹ s*=6, s*−k=4, δ*=0.8125
Both reproduced by the bmax=4 direction-restricted engine (extremal dir has b∈{2,4} ⟹ restriction is exact).

THE BREAK (exact): the in-tree formula δ*=½+(1/(2ρ)−1)/n (HEAD b66b7f769, calibrated ρ=1/4, n≤24) gives, for
k=2 (ρ=2/n, 1/(2ρ)=n/4): s* = n/2 − 1/(2ρ) + 1 = n/4 + 1, i.e. s*−k = n/4 − 1.
  n=16: formula s*−k = 3  vs EXACT 3  ✓ MATCH (δ*=0.6875 both)
  n=32: formula s*−k = 7 (s*=9, δ*=0.7188)  vs EXACT s*−k = 4 (s*=6, δ*=0.8125)  ✗ BREAK
The formula OVER-predicts s* / UNDER-predicts δ* at small ρ. Exact δ*=0.8125 sits ABOVE Johnson(0.75),
between the formula (0.7188) and cap 1−ρ (0.9375). Measured s*−k grows 3→4 (n=16→32), NOT 3→7: the
small-ρ over-det threshold grows FAR SLOWER than the formula's n/4 rate — consistent with s*−k ~ Θ(n/log n)
or even slower (sub-n/4), NOT the linear-in-n the ρ=1/4-calibrated formula implies.

CONSEQUENCE (honest, rule 4 = a mapped formula failure is a result):
- The ½+(1/(2ρ)−1)/n formula is a ρ=1/4 ARTIFACT; it must NOT be used to extrapolate δ* at small ρ / large n.
- The exact k=2 δ* climbs toward 1−ρ (NOT ½), confirming the orchestrator's "break upward". So the far-line
  incidence δ* (a RIGOROUS UPPER bound on MCA δ*, epsMCA≥far_inc/q) does NOT collapse to Plotkin ½ at small ρ.
- OPEN (the genuine combinatorial core): the exact growth law of s*−k(n) at fixed k. n=16,32 give 3,4; n=64
  (s=4 maxI=7681 bad, s=5 in flight) extends it. Whether s*−k ~ Θ(n/log n) (⟹ δ*=floor) vs slower is the live
  decider — and it is now OFF the BGK char-sum wall (pure cyclotomic over-det counting), exactly as the
  orchestrator localized. NOT a closure: small n (≤32 exact), maps the trend.
Probe scripts/probes/probe_407_k2_sstar_formula_break.py (+ rust-pg bmax mode for cross-validation).

## ⚠️ REFUTATION — the deployed `CensusDomination` Prop is FALSE at the prize budget (bounds SETS, not γ) (2026-06-15)

`CensusDominationWeld.lean` proves `CensusDomination dom k a₀ K` (K/p ≤ ε*) ⟹ `δ* = 1 − r/2^μ`. The Prop bounds
the alignable-SET count by K. Real budget (from `hεstar < (2^r·C(2^{μ-1},r))/p`) = `K < 2^r·C(2^{μ-1},r)` =
the KKH26 fibre supply. PROBE (thin proper μ_n, prize β=4, exact pencil-ratio alignment; validated by exact
n=8 SET-count=supply-count match 24,32):

  n=16,r=3,a₀=4: worst #alignable-SETS = 896 (line x⁹,x⁸) > budget 448  [EXCEEDS 2×]; #distinct-γ = 97 ≤ 448.
  n=16,r=4,a₀=5: worst #SETS = 1568 (x¹⁰,x⁸) > budget 1120; #distinct-γ = 40 ≤ 1120.
  n=16,r=5,a₀=6: #SETS = 1456 ≤ 1792; #γ = 73 ≤ 1792.

CONSTRAINT LEMMA: at n=16 the worst alignable-SET count exceeds the budget ⟹ the deployed `CensusDomination`
hypothesis is FALSE at the prize budget ⟹ `kkh26_deltaStar_pin_of_censusDomination` cannot fire at the prize
budget as stated. But #distinct-γ (the true MCA bad-scalar count, the object `badScalars_card_le_alignable`
needs) stays under budget at EVERY config. The gap = the looseness of `#bad-scalars ≤ #alignable-SETS`
(x⁹,x⁸: 896 sets, 16 distinct γ). The weld lifted the loose `badScalars_card_le_alignableSets` bound into its
hypothesis, making the deployed Prop strictly stronger than necessary — over-strong enough to be false.
The correct ⟺-CORE normal form must bound #distinct-γ, NOT the alignable-SET count.

Prime-independent (non-Fermat p=65777: SETS 896>448, γ 97 OK — not a Fermat artifact). Distinct from
`TakeoverCountermodel` (killed `CensusUpperExtremalFloor` = #bad-scalar upper-floor at a thick-prime death
radius); this kills the SET-count budget of `CensusDomination` in the thin prize regime. NOT a CORE closure
nor prize refutation — `#distinct-γ ≤ budget` is the open BGK content (margin large at n≤16, asymptotic
untested). Probes scripts/probes/probe_407_census_domination_budget.py, probe_407_census_budget_nonfermat.py,
probe_407_census_sets_vs_gamma.py. Receipt #issuecomment-4704035101.

## ★ COMPANION — proportional-k (ρ=1/4) CONFIRMS the formula where calibrated + s*−k GROWS (the floor-tracking axis) (2026-06-15)

Companion to the k=2 formula-break note above. Ran the EXACT over-det far-line incidence s* sweep at FIXED
ρ=1/4 (proportional k), the prize-relevant regime, via the rust-pg engine (bmax=6 direction-restricted;
extremal dir b−k≤2 ≤ bmax ⟹ restriction exact; char-0 prize prime p~n^4, valid subgroup p≡1 mod n):

| n  | k | s* | s*−k | δ* | in-tree formula δ*=½+1/n (ρ=1/4) |
|----|---|----|------|----|-----|
| 16 | 4 | 7  | 3    | 0.5625 | 0.5625  EXACT MATCH |
| 24 | 6 | 11 | 5    | 0.5417 | 0.5417  EXACT MATCH |
(n=16: s4..6 bad → s7 maxI=9 GOOD. n=24: s8:1153,s9:65,s10:25 bad → s11 maxI=24 GOOD.)

TWO clean findings:
1. The in-tree δ* formula ½+(1/(2ρ)−1)/n is EXACT at ρ=1/4 (matches n=16,24 to the digit) — confirming it is
   CORRECTLY CALIBRATED there. This PROVES the k=2 break (above) is a genuine SMALL-ρ failure of the formula,
   NOT an engine artifact: the engine reproduces the formula exactly where the formula was fit (ρ=1/4) and
   departs from it exactly where it wasn't (k=2, ρ→0). Consistent, adversarially-clean story.
2. s*−k GROWS 3→5 (n=16→24) at fixed ρ=1/4 — the floor-tracking axis. At ρ=1/4 the formula gives
   s*−k = n(½−1/n)−k = n/4 − 1 (LINEAR in n) ⟹ δ* → ½ = Johnson FROM ABOVE as n→∞. So at ρ=1/4 the far-line
   incidence δ* tends to JOHNSON, not the floor 1−ρ−Θ(1/log n)=¾−Θ — fully consistent with the orchestrator's
   "far-line incidence is a RIGOROUS UPPER bound on MCA δ* that sits BELOW the floor" (epsMCA≥far_inc/q). The
   s*−k = n/4−1 linear law (NOT Θ(n/log n)) at ρ=1/4 means the over-det far-line δ* does NOT track the floor —
   it is the (sub-floor) Plotkin/Johnson-limit upper bound, exactly as localized.

NET (honest, no closure): the over-det far-line incidence δ* is a CLEAN, formula-exact object at ρ=1/4
(→ Johnson, linear s*−k=n/4−1), and a FORMULA-BREAKING object at k=2 (→ above Johnson toward cap, sub-linear
s*−k). Both are the (rigorous UPPER bound) far-line δ*, NOT the MCA δ* — the prize BGK content lives in the
GAP between this upper bound and the true MCA δ*≥floor, untouched. Engine scripts/rust-pg (bmax mode);
companion to probe_407_k2_sstar_formula_break.py. Small n (≤24 exact). NOT a CORE closure.

## ★ SHARPENING + REGIME CLARIFICATION — at FIXED ρ=1/4 the far-line δ* DECREASES to Johnson (linear s*−k=n/4−1), NOT the floor (2026-06-15)

Sharpens the proportional-k companion + clarifies the orchestrator's RESOLUTION doc
(deltastar-RESOLUTION-tracks-floor-not-half.md, 1d78bb751), which concludes far-line δ* "tracks toward 1−ρ
(floor), not ½." That is correct AT k=2 (ρ→0), but the limit is REGIME-DEPENDENT. Exact 3-point ρ=1/4 data
(full-sweep rust-pg, all re-verified with the corrected saturating_add binary; valid subgroup p≡1 mod n, β=4):

| n  | k | s* | s*−k | δ*=(n−s*)/n | Johnson 1−√ρ | cap 1−ρ |
|----|---|----|------|-------------|--------------|---------|
| 16 | 4 | 7  | 3    | 0.5625      | 0.5000       | 0.7500  |
| 20 | 5 | 9  | 4    | 0.5500      | 0.5000       | 0.7500  |
| 24 | 6 | 11 | 5    | 0.5417      | 0.5000       | 0.7500  |

EXACT LINEAR LAW at ρ=1/4: s*−k = n/4 − 1 (3,4,5 for n=16,20,24 — matches the in-tree formula ½+1/n exactly),
so δ* = (n − (n/4+1))/n = 3/4 − 1/n → 3/4? NO: s* = k + n/4 − 1 = n/4 + n/4 − 1 = n/2 − 1, so δ* = (n−s*)/n
= (n/2+1)/n = 1/2 + 1/n → **1/2 = Johnson** (since ρ=1/4 ⟹ Johnson=1−√(1/4)=1/2). DECREASING (0.5625→0.5417),
toward Johnson from ABOVE — NOT toward the floor 1−ρ=3/4.

REGIME CLARIFICATION (the two limits differ):
- k=2 FIXED (ρ=2/n → 0): δ* INCREASES 0.6875→0.8125 toward 1−ρ → 1 (orchestrator's RESOLUTION — correct here;
  the gap (1−√ρ, 1−ρ) itself shrinks to 0 as ρ→0, so δ* rising tracks the collapsing window).
- ρ=1/4 FIXED: δ* DECREASES 0.5625→0.5417 toward Johnson = 1/2 (the LOWER window edge), linear s*−k=n/4−1.
So the far-line incidence δ* does NOT uniformly "track the floor": at fixed ρ it tends to JOHNSON (lower edge),
at ρ→0 it tends to 1−ρ. As a RIGOROUS UPPER bound on MCA δ* (epsMCA≥far_inc/q), at fixed ρ it pins MCA δ* ≤
~Johnson+O(1/n) — i.e. the far-line upper bound is ASYMPTOTICALLY AT JOHNSON at fixed ρ, hence CANNOT certify
the floor 1−ρ−Θ(1/log n) > Johnson. The prize floor (strictly above Johnson) is NOT reachable via the far-line
incidence upper bound at fixed ρ; it needs the true MCA object (the BGK gap), exactly as localized. NOT a closure.

ENGINE BUG TRANSPARENCY (rule 6): a SCRATCH copy /tmp/pg-fast used `k + bmax` which OVERFLOWED when bmax
defaulted to usize::MAX (5 + MAX wraps to 4 < k ⟹ empty dirs ⟹ spurious maxI=0/"GOOD"). This affected ONLY
the DEFAULT (no-bmax) path of the scratch binary. ALL reported/pushed data used EXPLICIT bmax 4/6 (overflow-safe)
and was cross-validated against the unpatched original engine. The IN-REPO engine uses `k.saturating_add(bmax)`
(correct) — every pushed point (n=16,32 k=2; n=16,20,24 k=4..6) RE-VERIFIED with the correct repo full-sweep
binary, all identical. Scratch copy deleted. No pushed result was affected.

## ★★ SHARP CRITERION — far-line incidence δ* sinks BELOW Johnson for ρ<1/4 (exact ρ=1/8 series; refines my own regime note) (2026-06-15)

Self-refinement (rule 6) of the regime-clarification above. That note said far-line δ* "→ Johnson at fixed ρ"
based on ρ=1/4 (where Johnson=½ = the formula limit, tangent). Tested a SECOND fixed ρ=1/8 (where Johnson≠½)
to see which side it lands. EXACT (full-sweep rust-pg, valid subgroup p≡1 mod n verified, β=4; n=24 cross-
checked full vs bmax — identical):

| n  | k | s* | δ* | formula ½+(1/(2ρ)−1)/n | Johnson 1−√ρ | δ*−Johnson |
|----|---|----|----|----|------|------|
| 16 | 2 | 5  | 0.6875 | 0.6875 EXACT | 0.6464 | **+0.0411 (above)** |
| 24 | 3 | 9  | 0.6250 | 0.6250 EXACT | 0.6464 | **−0.0214 (BELOW)** |

THE CLEAN CRITERION (formula-exact at fixed ρ; the formula HOLDS at ρ=1/8, both points to the digit — it only
"breaks" along k=2 where ρ=2/n→0 is NOT a fixed ρ): far-line δ* → ½ as n→∞ (the formula limit). Therefore:
  δ* ends BELOW Johnson  ⟺  ½ < Johnson  ⟺  ½ < 1−√ρ  ⟺  **ρ < 1/4.**
- ρ=1/4: Johnson=½=limit, δ* → Johnson FROM ABOVE (tangent; my prior note's case). Verified 0.5625→0.5417↓.
- ρ<1/4 (e.g. 1/8): Johnson>½, so δ* CROSSES below Johnson (n=16 above → n=24 below). Verified.
- ρ>1/4: Johnson<½, δ* stays strictly above Johnson.

CONSEQUENCE (sharpens the prize picture): the far-line incidence δ* is a RIGOROUS UPPER bound on MCA δ*
(epsMCA≥far_inc/q ⟹ δ*_MCA ≤ δ*_far-line). For ρ<1/4 this upper bound drops BELOW Johnson, while the
conjectured window puts δ*_MCA ≥ Johnson. So at ρ<1/4 EITHER (a) MCA δ* < Johnson at these scales (the
Johnson lower bound is asymptotic, not finite-n), OR (b) the far-monomial-witness validity (joint-agreement
subtraction = 0) degrades for ρ<1/4 so the upper-bound chain loosens. EITHER WAY: the far-line incidence δ* is
a SUB-JOHNSON object for ρ<1/4 — definitively NOT the prize δ* (which is in (1−√ρ, 1−ρ−Θ(1/log n)), strictly
above Johnson). This RESOLVES "does far-line track the floor" with a sharp ρ-criterion: NO for ρ≤1/4 (it tends
to ½ ≤ Johnson). The prize floor needs the true MCA object (BGK gap), exactly as localized. NOT a closure.
Engine scripts/rust-pg (full + bmax cross-checked). n≤24 exact. Refines the regime note (rule-6 self-sharpening).

## odd-moment / odd-Sidon-depth lever — REFUTED as a sup handle; rigid -n^r identity + non-proving depth (2026-06-15)

Lens: the deep-Sidon frontier (the narrowed rule-3 lever, r~log n). Tested whether the ODD signed
period moments A_r := Σ_{b≠0} η_b^r carry a thinness-essential sup handle. (η_b REAL since μ_n is
closed under negation, so odd moments are real and sign-sensitive — the natural place for genuine
signed cancellation, unlike the |·| even moments already mapped thickness-invariant.)

Probes: scripts/probes/probe_407_{odd_moment_thinness,oddmom_scaling,Wr_odd_depth,depth_vs_M}.py
(exact integer zero-sum convolution + FFT-exact periods; proper subgroups μ_n⊊F_p*, odd-m primes
β≈2.2→4.6; n=8,16).

EXACT IDENTITY (landed axiom-clean, Frontier/_GaussPeriodMomentCensus.lean, push 76715441a):
  Σ_{b∈F} η_b^r = |F|·W_r,  W_r = #{(y_1..y_r)∈G^r : Σy_i=0}  (zero-sum census).
  ⟹ A_r = |F|·W_r − n^r.  Verified to machine precision (n=8,16, thick+thin).

REFUTATION (two parts):
1. The "odd-moment signed cancellation" A_r/(p·M^r) → 0 (as β grows) is a NORMALIZATION ARTIFACT:
   to the Sidon depth W_r=0 ⟹ A_r = −n^r EXACTLY (rigid, p-independent), so A_r/(p·M^r) = −n^r/(p·M^r)
   → 0 trivially (constant numerator / growing p·M^r). A_r carries ZERO information about
   M=max_{b≠0}‖η_b‖. Same shape as the refuted NC3 rigid-equation no-go.
2. The genuine thinness invariant — the odd zero-sum onset depth d_odd (first odd r with W_r>0) —
   GROWS with thinness (n=16: 7→9→11→none across β=2.45→4.6; n=8: 7→9→none) ⟹ rule-3-COMPATIBLE.
   BUT it does NOT control the normalized sup: M/√(n·log(p/n)) is flat ~1.1–1.3 across d_odd=5..13
   (non-monotone). So d_odd is a TRUE thinness invariant that is NON-PROVING for M at accessible scale.

WALL: the odd-moment / odd-Sidon-depth object splits into (a) a rigid identity that pins A_r=−n^r
to depth but says nothing about M, and (b) a thinness-essential depth that decouples from the sup.
The "deeper Sidon depth ⟹ smaller M" bootstrap FAILS empirically here. No CORE closure; the brick
is the exact moment↔census substrate, the wall is honest. Small n (8,16 exact).

## BHBI break — REALIZABLE-cone correction: 032525 break is OFF-SPEC; real break at n=32 β=4; ∀-field fluctuating (2026-06-15)

Lens: the freshest BHBI unification capstone (BridgeBounded / BoundedCyclotomicIndep / CountAntipodalBounded).
Adversarial check (rule 6) of the 032525 grind claim "C*(n=16, prize prime)=4 ⟹ chain BHBI(ω,8,4) FALSE,
witness g=(−4,−4,−4,−1,−1,−1,0,0)".

CHAIN SOURCE FACT (BridgeBounded.lean + RigidityGeneralT1.lean): the chain (bridgeZ_bounded → RepK) only ever
feeds BHBI a coefficient vector g_j = contribZ A j − contribZ B j with A,B FINSETS of signed half-basis points.
fiber A j ⊆ {(j,T),(j,F)}, isgn(j,T)=+1, isgn(j,F)=−1 ⟹ contribZ A j ∈ {−1,0,+1} (the in-tree `≤2` bound is a
loose card-≤2 overestimate; T+F cancel). ⟹ REALIZABLE g_j = a_j − b_j, a_j,b_j ∈ {−1,0,1} ⟹ g_j ∈ {−2..2}.
So the chain needs only BHBI(ω, n/2, 2) over the realizable {−2..2} cone — NOT C=4.

Probes: scripts/probes/probe_407_realizable_{bhbi,bhbi_verify,n32_exact,disjoint_check}.py (exact integer,
proper thin 2-power μ_n ⊊ F_p*, ω^{N}=−1 verified, prize primes p~n^β).

PART 1 — 032525 BREAK IS OFF-SPEC. n=16/p=65537 (β=4) exact brute: #relations in [−h,h]^8 = 0 at h=2 AND h=3;
1152 at h=4 (first = exactly the 032525 witness). The 032525 witness has max|coeff|=4 > 2 ⟹ NOT a realizable
contribZ-difference. At the REALIZABLE support {−2..2}, n=16/p=65537 is INDEPENDENT with margin (empty at h=2,3).
So "chain breaks at n=16 prize prime" was a generic-BHBI break, not the realizable-BHBI the chain consumes.

PART 2 — THE REAL BREAK (BGK wall in the realizable cone). At n=32 (N=16), realizable {−2..2} relations EXIST
at β∈{3,4,5}, exact-integer verified (Σ g_j ω^j = −5p, −10p, −9p respectively; ω^16=−1; max|g|=2; nonzero):
  β=4.00, p=1048609: g=(−1,−1,0,2,1,1,−1,2,−2,−2,−2,−2,−2,−2,−2,−2), Σ=−10·p. BHBI(ω,16,2) FALSE.
And ON-SPEC (probe_407_realizable_disjoint_check.py): every witness is realizable as contribZ A − contribZ B
with A,B DISJOINT and Σ_A sval = Σ_B sval mod p == 0 — exactly the domain of disjoint_equal_sum_antipodal_int_bounded.
⟹ the chain's required hypothesis BHBI(ω,16,2) already FAILS at the prize support (β=4) by n=32, on-spec.

PART 3 — ∀-FIELD-UNIVERSALITY (the c.154 trap). Realizable independence is PRIME-FLUCTUATING: n=16, β≈3.5 band,
realizable {−2..2} independence holds at only 2/12 prize-band primes. p=65537 being independent is a lucky-prime
false positive (the refuted "good prime exists" pigeonhole, §6/c.154). The prize is ∀-prize-field-universal;
realizable-BHBI must hold at EVERY prize-band prime, which it does not.

THINNESS (rule 3): C*_real (min realizable height) grows with β at SPECIFIC primes (n=16: 2 for β≤3.5 → 4 at
β=4 → none at β=6), but NON-UNIFORM across the field (prime-fluctuating, Part 3). CONSISTENT with the
matched-pair finding of 9a0868c62 (thin-vs-thick at FIXED prize prime sign-flips; neither C* nor the height-1
relation count discriminates thin from thick at n=32): there is NO clean ∀-field thinness invariant in the
bounded/realizable cone. NOT claiming a thinness invariant — deferring to that matched-pair rule-3-incompatible
conclusion. Distinct complementary content of THIS entry vs 9a0868c62: (i) the 032525 break is OFF-SPEC
(height-4 cone, not the realizable {−2..2} contribZ-difference cone the chain consumes); (ii) realizable
BHBI(ω,16,2) is FALSE at n=32 β=4 by an ON-SPEC DISJOINT contribZ-difference witness (exact Σ=−10p), locating
the wall at the chain's exact height-2 hypothesis (9a0868c62 measures the height-1 sign-relation COUNT, a
different cone).

NET: a correction (032525 break off-spec) + a precise location of the genuine wall in the realizable cone the
chain consumes (BHBI(ω,16,2) FALSE at n=32, β=4, on-spec disjoint witness, exact) + the ∀-field obstruction
(prime-fluctuating, c.154). No CORE closure; no fake. Small n (16 exact, 32 via MITM + exact-int verify).

### Follow-up (universal at n=32): realizable BHBI(ω,16,1) FALSE at ALL prize-band primes; height is 1 not 2; n=16 holds (2026-06-15)

Reconciling the above with 1fa2d5e58 (which reported C*(n=32)=1). Confirmed + universalized
(probe_407_n32_height1_check.py, MITM): at n=32, β=4.00, a HEIGHT-1 realizable {−1,0,1} relation
Σ g_j ω^j ≡ 0 (p) exists at **8/8** prize-band primes (p=1048609..1049569). A {−1,0,1} sign-relation
is trivially a realizable contribZ-difference (g_j = a_j − b_j, one of a_j,b_j = 0), so the minimal
realizable height at n=32 is **1**, not the 2 of my first witness — my n=32 height-2 witnesses were
non-minimal. The chain's required hypothesis BHBI(ω,16,C) thus fails for EVERY C≥1 at n=32 prize-band,
∀-field (not lucky-prime). And re-confirmed: n=16/p=65537 has NO realizable relation at height ≤2
(min height = None) ⟹ the n=16 chain holds at realizable support, the off-spec (height-4) 032525
witness was the only thing making n=16 look broken.

CLEAN STATEMENT OF THE WALL: realizable BHBI holds at n=16/prize (the chain's hypothesis is satisfied
there) but fails UNIVERSALLY at n=32/prize at height 1. The bounded-cyclotomic-independence lever's
required hypothesis is already ∀-field-FALSE by n=32. Combined with 9a0868c62 (no thin-vs-thick
discrimination), the BHBI lever cannot prove CORE: its hypothesis is false where needed and carries no
thinness discriminator. Mapped wall, not a closure. n=16 exact-brute, n=32 MITM + exact-int verified.

### BHBI-failure ⟷ (BIND)-failure are the SAME object at the half-basis (bridge, 2026-06-15)

Unifies the realizable-BHBI failure (above) with the §5.0 (BIND) non-antipodal-vanishing entry. A
half-basis height-1 relation Σ_{g_j=+1} ω^j − Σ_{g_j=−1} ω^j ≡ 0 (ω primitive 2^m-th root, ω^N=−1,
N=2^{m-1}) lifts to a FULL-index (Z/2N = Z/n) subset-sum vanisher via the antipode ω^{j+N}=−ω^j:
    S = {j : g_j=+1} ∪ {j+N : g_j=−1} ⊆ Z/n,   then  Σ_{i∈S} ω^i ≡ 0 (p)  — the BIND object.

PROBE (probe_407_bhbi_bind_bridge.py): for ALL 8/8 n=32 prize-band primes (p≈1.0486e6..1.0496e6,
β=4.00), the height-1 BHBI witness lifts to a NON-ANTIPODAL S with Σ_{i∈S} ω^i ≡ 0 (directly verified
in F_p). 8/8 non-antipodal, 0 antipodal. So the realizable-BHBI failure IS exactly a (BIND)-gate failure
on the half-basis face — they are not two independent walls but ONE object.

SCOPE/CONSISTENCY (rule 6, NO refutation): these primes are p~2^20, NOT the prize budget p~2^128. The
house hypothesis (#S)^φ(32)<p is FALSE here ((#S)^16 ≈ 2^51..59 ≫ 2^20 for #S≈9..13) — exactly the
regime where the sibling's BIND entry already predicts non-antipodal vanishing occurs. So this CONFIRMS
+ unifies (does not extend the refutation): BHBI-failure and BIND-failure coincide precisely when the
house bound fails. The prize is NOT refuted (small primes). What's mapped: the bounded-cyclotomic-
independence lever and the (BIND)/house-gate lever are the SAME wall viewed through two formalizations;
closing either at the prize budget needs the thinness-essential B_∞←B_{log n} Sidon bootstrap, not a
sharper bound on either equivalent face. No CORE closure.

### BHBI n=32 "wall" is a small-p PIGEONHOLE ARTIFACT; prize-regime failure is BASIS-LENGTH, thickness-invariant (2026-06-15)

Resolves the explicit SCOPE caveat left open by the BHBI<->BIND bridge entry (push 07517f301): that the
realizable-BHBI / (BIND) height-1 failure at n=32 was measured only at p~n^4~2^20, far below the
pigeonhole floor. Constraint lemma BHBI-PIGEONHOLE:

A realizable height-h relation Sum_{j<N} g_j omega^j = 0 (mod p), g in {-h..h}^N \ {0}, N=n/2, EXISTS
whenever (2h+1)^N > p (collision among (2h+1)^N sign-vectors in Z/p) -- for ANY N residues, thin or not.

PROBE 1 (probe_407_bhbi_house_threshold_sweep.py, exact MITM, thin mu_32 vs RANDOM 16-subset, p swept
20..40 bits): the height-1 relation (sole basis of the "forall-field FALSE at n=32" claim) exists ONLY at
p_bits=20 (the prize-band prime sits at the 3^16~2^25.4 edge), GONE by beta=4.4. The height-<=2 relation
persists to p_bits~32 then vanishes at 34 -- and the thin subgroup loses it at the SAME point as / EARLIER
than the random control (thin NONE at 34 while random still h=2). NO thin advantage.

PROBE 2 (probe_407_bhbi_pigeonhole_scaling.py): at the prize regime p=n^beta, the forced-margin
(n/2)log2(2h+1) - beta*log2(n) is positive and grows LINEARLY in n for fixed beta,h (n=128: margin_h1=73
bits; n=65536: margin_h1=51872 bits). So bounded-height realizable relations are pigeonhole-FORCED at EVERY
prize (n,beta) for large n -- a BANAL wall from the long half-basis (n/2 terms) vs the small modulus n^beta,
present for ANY N-subset.

PROBE 3 / CRUX (verify_n16_crux.py, exact brute n=16 p=65537): thin mu_16 has min realizable height = NONE
(no relation at h<=2), while 40/40 RANDOM 8-subsets DO have one. The thin 2-power subgroup is strictly MORE
relation-FREE than random -- the categorical OPPOSITE of a 2-power-structural vanishing obstruction.

VERDICT: CONFIRMS the sibling's conclusion (BHBI / bounded-cyclotomic-independence lever is walled, cannot
prove CORE) but CORRECTS the reason: the n=32 failure is a small-p pigeonhole artifact, and the genuine
prize-regime failure is THICKNESS-INVARIANT (basis-length pigeonhole), NOT 2-power/thin-essential. By rule 3
a thickness-invariant obstruction can neither prove nor refute CORE => the BoundedHalfBasisIndep formulation
is the wrong lever (hypothesis unsatisfiable for trivial reasons unrelated to thin-cancellation). The
discriminating thin content lives ABOVE the bounded-relation-height floor (the Sidon-bootstrap object).
CORE not closed. Python-only, no Lean changed => axiom-clean trivially. n=16 exact brute; n=32 exact MITM;
scaling analytic + exact small-n confirmation.

### CENSUS<->CORE EQUIVALENCE is OVERSTATED: CensusDomination is STRICTLY STRONGER than CORE (sufficient, not equivalent) (2026-06-15)

Maps the brief's flagged open brick: the count/census face (CensusDomination, CensusDominationWeld.lean)
whose EQUIVALENCE to CORE is asserted ("the $1M obligation in census normal form") but never proven.

IN-TREE ARCHITECTURE (verified at source):
  CORE handle:  epsMCA <= #bad / p          (epsMCA_le_of_badCount_le -- the deployed CORE bound)
  proven (U):   #bad   <= #alignable-a-sets (badScalars_card_le_alignable, UniversalAlignmentLaw:284)
  weld:         CensusDomination (#alignable <= K, all pairs, deep bands) => delta*-pin, with K/p <= eps*.
So the chain is  epsMCA <= #bad/p <= #alignable/p <= K/p <= eps*.  CensusDomination bounds #alignable;
CORE only needs #bad. The inserted step #bad <= #alignable is the ONLY place equivalence could fail, and
it is the step that is proven as a ONE-WAY inequality, never as an equivalence.

MEASUREMENT (exact mod-p, proper smooth subgroup mu_n, prize prime p~n^4, never n=q-1; semantics matched
to in-tree probe_alignment_census.py; probes probe_407_census_core_{equivalence,deepband,bindingband_ratio}.py):
At the BINDING deep band the ratio #alignable/#bad is LARGE and depth-decaying, NOT ~1:
  smooth n=16, k=3 (m=2 deep-ceiling shape), p=65537:
    KKH26 line [x^6,x^4]: a=4 1792/496(3.61), a=5 336/40(8.40), a=6(bind) 56/40(1.40)
    hifreq    [x^9,x^7]:  a=5 112/1(112.0), a=6 56/1(56.0), a=7 16/1(16.0), a=8(bind) 2/1(2.0)
  => at the hifreq line up to 112 alignable a-sets ALL pin ONE bad gamma (the many a-subsets of a SINGLE
     far-line agreement locus). #alignable OVERCOUNTS #bad by up to 112x.

THINNESS CONTROL (rule 3): thick n=12 shows the SAME inflation pattern (e.g. line [7,6]: a=5 180/12,
a=6 72/12, a=7 12/12) => the #alignable/#bad slack is THICKNESS-INVARIANT (not 2-power-essential).

VERDICT (refutation-grade for the EQUIVALENCE claim; NOT a CORE result, no overclaim):
CensusDomination is a STRICTLY STRONGER hypothesis than CORE -- a SUFFICIENT condition (via the proven
one-way (U)), NOT an equivalent encoding. The "$1M obligation in census normal form" wording overstates
equivalence: proving #alignable<=K proves MORE than the prize needs, and CensusDomination could even be
FALSE (too strong) while CORE holds. CONSEQUENCE: a CORE proof need NOT route through CensusDomination;
census-route effort should target #bad directly (#bad COLLAPSES to O(1) at the hifreq line -- the real
CORE signal -- while #alignable stays inflated). The (U) direction and the weld are correct as a
sufficiency chain; only the EQUIVALENCE framing is corrected. CORE not closed. Python-only, no Lean
changed => axiom-clean trivially. Exact small-n (n=8,12,16), prize primes, proper subgroups.

### THIN SIDON DEPTH SCALES: thin r_min(mu_n) advantage over random GROWS with n (corroborates + extends the surviving-lane handoff ef5f12fb1) (2026-06-15)

Lens: the surviving live object isolated by the full-depth-BIND refutation (ef5f12fb1): "the COLLECTIVE
thin depth profile (moment / sqrt-cancellation), NOT a per-S no-vanisher statement." That entry PROVED a
thin advantage exists at one point (n=32,beta=4: thin r_min=11 vs random median 6) but did NOT measure how
the thin Sidon depth SCALES with n. This is the first scaling measurement.

OBJECT: thin Sidon depth r_min(mu_n,p) = smallest NON-antipodal subset S of Z/n with Sum_{i in S} zeta^i
== 0 (mod p), zeta primitive n-th root, mu_n proper 2-power subgroup of F_p*, p=ceil(n^beta) prime ==1(n),
NEVER n=q-1. r_min = NONE => full-depth (no vanisher up to n/2). Random control = median r_min over 5
random n-subsets of F_p* of the SAME density.

METHOD: exact-integer meet-in-the-middle (index halves, subset-sum collision), antipodal-closed sets
EXCLUDED. n=8,16,32 exact, rmax=n/2. probe_407_thin_sidon_depth_scaling.py.

RESULT (the scaling, with the one non-censored thin point EXACT-VERIFIED):
| n  | beta | thin r_min | random median | margin | note |
|----|------|------------|---------------|--------|------|
|  8 | 4.0  | >4 (full)  | 5             | +0     | thin full-depth, random vanishes ~n/2 |
| 16 | 4.0  | >8 (full)  | 9             | +0     | thin full-depth |
| 32 | 4.0  | **11**     | 7             | **+4** | EXACT witness verified (size 11, sum=0, non-antipodal; NONE for r<11) |
|  8 | 5.0  | >4 (full)  | 5             | +0     | |
| 16 | 5.0  | >8 (full)  | 9             | +0     | |
| 32 | 5.0  | >16 (full) | 9             | **+8** | thin still FULL-depth at n=32 while random median 9 |

VERDICT (corroboration + extension; NOT a CORE result, rule-6 scoped):
1. The thin advantage is REAL and THINNESS-ESSENTIAL (rule-3 PASS): thin mu_n is strictly deeper-Sidon
   than a random same-density set at EVERY (n,beta); at small n thin is full-depth while random already
   vanishes near n/2.
2. The advantage MARGIN GROWS with n: +0,+0 -> +4 (beta=4) and +0,+0 -> +8 (beta=5). The 2-power structure
   pushes the first vanisher progressively deeper relative to random as n grows -- the collective thin
   signal the moment/sqrt-cancellation route needs.
HONEST SCOPE: small-n thin rows are CENSORED at rmax=n/2 (full-depth), so the EXACT growth LAW (sqrt(n) vs
log^c n) is not yet resolved -- need n=64,128 (randomized, SOUND-on-failure) to fit the exponent. r_min is a
LOWER proxy for the full collective depth profile (smallest vanisher); a growing r_min is NECESSARY, not
sufficient, for the collective CORE route. The n=32/beta=4 r_min=11 is exact-verified (witness
[9,14,16,17,19,21,22,23,26,28,31], sum=0 mod 1048609, non-antipodal). CORE not closed; the surviving thin
mechanism's scaling is positively confirmed for the first time. Python-only, no Lean => axiom-clean trivially.

### crossCell DYADIC-TOWER ITERATION does NOT certify CORE even GRANTING BCHKS-1.12: it leaks to the TRIVIAL M(n)<=n (2026-06-15)

Maps an asserted-but-unproven CLOSURE step in CrossCellShkredovBound.lean. That file names the one open
lever of the dyadic cumulant descent N0(G,r)=2*N0(H,r)+crossCell(H,zeta,r) (G=mu_n=H u zeta*H, H=mu_{n/2}),
states the OPEN absolute bound CrossCellAbsoluteBound = BCHKS25 Conj 1.12 (crossCell*q <= 2^r*|H|^r), and
proves the per-level consumer N0_gap_of_absoluteBound: N0(G,r) <= 2*N0(H,r) + 2^r*|H|^r/q. Its docstring
then ASSERTS that iterating this down the 2-power tower with q~n*2^128 "keeps the cross mass below the
diagonal and converges to the clean closed form N0(G,r)~2*N0(H,r) -- the closure mechanism, conditional on
the open bound," and references a consumer `prize_of_ShkredovSubTrivialBound` which is NOT present as a
theorem (only the per-level N0_gap_of_absoluteBound exists).

TESTED the asserted closure IMPLICATION exactly (char-0 exact bigint on the bound itself, independent of
whether the open bound is true). Tower recursion (absolute bound at EACH level, q FIXED, T_j:=q*N0(2^j,r)):
  T_{j+1}(r) = 2*T_j(r) + 2^r*(2^j)^r,   T_1(r) = q*C(r,r/2) [r even else 0].
Fed into the in-tree raw-moment certificate M(n) <= min_r (sum_{b!=0}|eta_b|^{2r})^{1/2r},
  sum_{b!=0}|eta_b|^{2r} = q*N0(G,2r) - n^{2r}.  Probe probe_407_crosscell_tower_iteration_nogo.py.

RESULT (sound, floor-checked against the proven floor M >= sqrt(n(q-n)/(q-1))):
  | mu | n     | floor=.5log2(n..) | CORE=.5log2(n log m) | abs(BCHKS) log2 M | verdict |
  |  5 | 32    | 2.50              | 5.74                 | 4.003             | = log2 n (TRIVIAL) |
  |  8 | 256   | 4.00              | 7.24                 | 7.003             | = log2 n (TRIVIAL) |
  | 12 | 4096  | 6.00              | 9.24                 | 11.003            | = log2 n (TRIVIAL) |
  | 17 | 131072| 8.50              | 11.74                | 16.003            | = log2 n (TRIVIAL) |
Granting CrossCellAbsoluteBound, the iterated certificate is SOUND (always >= floor) and floors EXACTLY at
log2 M(n) ~ log2 n => M(n) <= n (the TRIVIAL L^1 bound), never sqrt(n log m) (CORE) and not even sqrt(n)
(Johnson). MECHANISM (decomposition audit): the top-level cross injection is 2^r*|H|^r = 2^r*(n/2)^r =
n^r-scale, so q*N0(G,2r) accumulates an n^{2r}-scale cross mass; q*N0(G,2r) - n^{2r} floors at n^{2r}, and
(n^{2r})^{1/2r} = n. The cross term injected by the (granted) bound is exactly the size that pins the
certificate at the trivial n.

SOUNDNESS GUARDS (rule 6): (a) the IDEAL crossCell=0 case (= the docstring's "clean closed form", perfect
halving N0(2^{j+1})=2*N0(2^j)) goes VACUOUS (moment <= 0) past low r => yields no usable bound either, so
the "clean closed form" does NOT certify CORE on its own. (b) the measured "random-count" injection form
(2^r-2)|H|^r/q gives certificates that VIOLATE the proven floor (log2 M < .5 log2 n) => UNSOUND, discarded
(it measures a vanishing gap, not a valid M upper bound). Only the absolute-bound certificate is sound, and
it is trivial.

VERDICT (rule-4 constraint map; NOT a CORE result, NOT a refutation of BCHKS-1.12 itself): the dyadic-tower
ITERATION of the crossCell gap is NOT a CORE-closure mechanism. Even granting the open BCHKS-1.12 absolute
bound, iterating the per-level gap leaks to the trivial M(n)<=n. The CrossCellShkredovBound.lean docstring's
claim that the iteration "converges to the clean closed form ... the closure mechanism, conditional on the
open bound" OVERSTATES what the iteration yields; the referenced `prize_of_ShkredovSubTrivialBound` consumer
cannot deliver CORE in this shape. This is CONSISTENT with the meta-theorem (Sec.4: every second-order/moment
method caps at the trivial n via (q E_r)^{1/2r} >= n) but is NOT a re-derivation: the meta-theorem covers
SINGLE-DEPTH moment methods; this maps the specific ITERATED-TOWER consumer conditional on the named open
crossCell bound, closing a gap between "the open bound" and "a CORE proof" that the file's docstring left
implicit. The genuine open input (per the file's own conclusion) must come from the ARITHMETIC of the
q-reduction (spurious mod-p collisions making crossCell sub-random), NOT from the granted absolute bound fed
through the tower. Thinness-blind (a NO-GO need not be thin-essential, rule 3 OK for refutations). CORE not
closed. Python-only, exact bigint, no Lean changed => axiom-clean trivially.

## ⚠️ REFUTATION (surviving-lane, rule-3 PASS but WRONG SIGN) — the COLLECTIVE EVEN census/energy profile of mu_n is NOT suppressed below random; it is INFLATED, super-multiplicatively in r (2026-06-15, opus-4-8 subagent)

LENS: the surviving live object isolated by the full-depth-BIND refutation (ef5f12fb1) + handoffs: "the
COLLECTIVE thin depth profile (moment / sqrt-cancellation), NOT a per-S no-vanisher statement." Prior work
measured only (a) r_min = smallest single vanisher (e7b5e6125: thin DEEPER), (b) d_odd onset (odd_moment
entry: thin deeper, but A_r=-n^r RIGID, decouples from M), (c) A_r/Wick RATIO at the optimizer r* + its
n-trend (step_at_rstar: margin erodes). NONE measured the per-r EVEN energy moment PROFILE E_{2r}(mu_n) =
sum_{b!=0}|eta_b|^{2r} (the object feeding A_r = E_r - n^{2r}/q <= Wick, the genuine prize moment) against a
thin-density RANDOM control, to test whether the thin advantage COMPOUNDS (collective) or is single-depth.
This is that measurement -- and it kills the "thin advantage helps the moment route" hope at the EVEN level.

METHOD (exact, rule-2 + rule-3 clean): eta_b = exact integer DFT of indicator(mu_n) in F_p; mu_n = <g^m>,
m=(p-1)/n > 1 PROPER (NEVER n=q-1). prize-band primes p~n^beta, beta in {4.0,4.5}, incl. one non-Fermat.
RANDOM control = median over 5 random n-element subsets of F_p* (same thin density). Probes
scripts/probes/probe_407_even_census_profile.py + probe_407_even_census_dcsub.py (adversarial re-audit).

RESULT 1 -- E_{2r}(thin)/E_{2r}(random) GROWS with r (thin is LARGER, not suppressed):
| n  | beta | E2r ratio r=1..6                              |
|----|------|----------------------------------------------|
| 16 | 4.0  | 1.00, 1.45, 2.27, 3.59, 5.68, 8.85           |
| 16 | 4.5  | 1.00, 1.45, 2.27, 3.59, 5.67, 8.80 [non-Fermat]|
| 32 | 4.0  | 1.00, 1.48, 2.38, 3.98, 6.75, 11.57          |
The thin even-energy moment is BIGGER than random at every r>=2 and the gap COMPOUNDS upward. Since A_{2r} =
|F|*W_{2r} - n^{2r} tracks E_{2r}, the thin A_{2r} is FURTHER from suppression than random, worse with depth.

RESULT 2 (ADVERSARIAL re-audit, rule 6 -- is this just the known "thin M>=random M" sup fact re-seen?): NO.
(a) COLLECTIVE shape: the thin/random ratio of the t-th LARGEST |eta_b| is >=1.1 not only at t=1 (sup) but at
    t=1,2,4,...,128, and GROWS into the spectrum body (n=32: 1.157 @t=1 -> 1.309 @t=128). The ENTIRE top of the
    period spectrum is inflated in thin, not one extreme outlier -- genuine collective over-concentration.
(b) The even-moment ratio EXCEEDS the sup-only prediction (M_thin/M_rand)^{2r} at deep r: n=16 r=6 ratio 8.58
    vs sup-pred 3.47; n=32 r=6 ratio 11.40 vs sup-pred 5.77. So the moment growth is NOT explained by the sup
    alone -- the BODY of the spectrum contributes a genuine extra (super-sup) factor. New collective signal.

VERDICT (rule-4 mapped wall; rule-3 PASS but the thinness-essentiality has the WRONG SIGN for CORE):
1. mu_n's even period-energy profile IS thinness-essential (thin differs from random) -- but in the direction
   that makes the moment object HARDER, not easier: thin is collectively MORE concentrated (top-heavy at every
   quantile), so A_{2r}(thin) > A_{2r}(random), and the excess COMPOUNDS super-multiplicatively in r.
2. This WALLS the "surviving collective thin depth profile -> smaller M via moments" hope at the EVEN level:
   the thin advantage that exists at the ODD signed-vanisher level (r_min, d_odd deeper) does NOT carry to the
   EVEN energy moments -- the very ones in A_r <= Wick. The collective even profile is anti-helpful.
3. RECONCILES + SHARPENS ILO (852e0fa27, "thin anti-concentrated worse, sup only") + the moment thickness-
   invariance note: it's not only the sup -- the WHOLE even spectrum is collectively inflated, and the
   inflation grows with moment order. The signed/odd thin depth and the even-energy concentration point
   OPPOSITE ways; the moment route needs the even one, which is adverse.
HONEST SCOPE: small n (16,32 exact), p~n^{4-4.5}. Random control is finite-sample median (5 draws). This is a
COLLECTIVE refutation of the even-moment thin-suppression hope, NOT a CORE closure nor a prize refutation:
the surviving structural hope is the ODD signed family-level Sidon bootstrap (B_inf<-B_{log n}), which lives
in the signed/odd object, NOT the even energy profile measured here. CORE not closed. Python-only, no Lean =>
axiom-clean trivially. Multi-prime (incl. non-Fermat) -> not a Fermat artifact.

### crossCell is p-INDEPENDENT (char-0 structural) + SUPER-random in the thin regime: the proposed "sub-random via mod-p collisions" open input is WALLED (2026-06-15)

Follow-up to the crossCell dyadic-tower no-go (push ad90dc8d5). That entry showed iterating the per-level
crossCell gap (granting BCHKS-1.12) leaks to trivial M<=n. CrossCellShkredovBound.lean's own CONCLUSION then
proposes that the genuine open input "must come from the ARITHMETIC of the q-reduction (spurious mod-p
collisions)" -- i.e. it hopes crossCell is SUB-random (< the BCHKS-1.12 expectation) because collisions cancel
structure. This entry tests that hope directly in the thin prize regime and WALLS it.

OBJECT (exact char-p, proper subgroup, NEVER n=q-1): G=mu_n=H u zeta*H, H=mu_{n/2}, crossCell(r)=
N0(G,r)-2*N0(H,r) (>=0 by the descent). Random/BCHKS-1.12 expectation E_rand(r)=(2^r-2)|H|^r/p.
Probe probe_407_crosscell_superrandom_pindep.py (exact running-sum DP counting, multi-prime, rule-3 control).

RESULTS:
1. crossCell is PERFECTLY p-INDEPENDENT in the thin regime (beta>=4): n=8 -> 96 (r=4), 4320 (r=6) at EVERY
   prime {4129,4153,4177,4201}; n=16 -> 384, 40320 at EVERY prime {65537,65617,65633,65713}. => it is the
   char-0 STRUCTURAL relation count (#{sum u + zeta sum w = 0} holding over Z, hence at every large p), with
   ZERO spurious mod-p collision component (collisions scale like 1/p; crossCell does not move at all).
2. SUPER-random, diverging with thinness: ratio crossCell/E_rand ~ (p-indep count)/(C/p) ~ p. beta=4: n=8
   r=4 ratio 110x, n=16 r=4 438x; beta=5: 878x / 7022x. crossCell is FAR ABOVE random, never below.
3. rule-3 THINNESS control: thick beta=2.3 ratio O(1)-4x; thin beta=4-5 ratio 100x-7000x. The super-random
   excess is the char-0 structural floor dominating as p->infty -- thinness-ESSENTIAL, not a collision artifact.
4. At thick/small p the count can EXCEED the char-0 value (n=16 r=6: 48000 at p=593 vs 40320 char-0) =>
   collisions only ADD to crossCell, never give a sub-random saving.

VERDICT (rule-4 constraint map; NOT a CORE result, NOT a prize refutation): there is NO sub-random saving in
crossCell to extract. crossCell >= its char-0 structural count at all p (collisions only add). The proposed
"arithmetic-of-the-q-reduction / mod-p-collision" open input of CrossCellShkredovBound.lean is WALLED: the
binding object is the p-INDEPENDENT char-0 structural relation count, exactly the (super-random,
BCHKS-1.12-saturating) quantity, with no mod-p cancellation available. CONSEQUENCE: any CORE proof routing
through crossCell must bound the CHAR-0 structural count itself (= vanishing-sums-of-roots-of-unity /
Lam-Leung over the 2-power tower), NOT hope for collision savings -- which re-localizes the open content onto
the already-mapped char-0 antipodal/Sidon object (ConverseLamLeung2Power, the surviving thin Sidon bootstrap),
NOT a new arithmetic mechanism. Combined with the tower no-go (ad90dc8d5): granting BCHKS-1.12 doesn't close
(tower leaks to n), AND the proposed route to PROVE a sub-BCHKS crossCell bound (collisions) is empty. CORE
not closed. Python-only, exact DP, multi-prime (Fermat + non-Fermat), no Lean => axiom-clean trivially.

### A3 REVERSE-DICTIONARY FLOOR-PUSH is THICKNESS-INVARIANT at the (halfJ,J)-window radius -- not the thin lever (2026-06-15)

LANE: #444 §1 A3 -- "push delta* UP past half-Johnson via the reverse LD=>MCA dictionary at larger n",
the orchestrator's explicitly-flagged "genuinely-unattacked OTHER HALF of the prize" / fallback. First
RULE-3 thinness gate applied to the reverse dictionary (ReverseDictionary.exists_interleavedList_card_gt_of_epsMCA_gt).

OBJECT (exact, in-tree axiom-clean): forward eps_mca(C,delta) <= (1+(n-a)*L)/q; reverse contrapositive
=> L_force = floor((incid-2)/(n-a)) is a machine-checkable LOWER bound on some pair's interleaved list
size at collapse radius a, incid = eps_mca*q. Proven floor = half-Johnson delta* >= (1-sqrt rho)/2
(HalfJohnsonDeltaStar); full Johnson 1-sqrt rho is the OPEN all-pairs target (SmallSubgroupGoodList).
A3 hope: smooth mu_n forces a SMALLER list than random at radii in (halfJ,J) => a higher thin floor.

METHOD (probe-first, exact mod-p, PROPER smooth subgroup mu_n, never n=q-1): exact eps_mca bad-LINE
incidence at the (halfJ,J)-window radius, SMOOTH mu_n vs RANDOM domain, prime sweep (q-invariance +
rule-3). n-k=2 exact-feasible cases. probe_407_a3_fast.py + probe_407_a3_window_map.py.

RESULT (rule-4 mapped constraint; rule-3 verdict):
| n | k | rho | window radius delta in (halfJ,J) | smooth incid | random incid | q-invariant | thin |
|---|---|-----|----------------------------------|--------------|--------------|-------------|------|
| 4 | 2 | 0.500 | 0.250 (halfJ 0.146, J 0.293) | 4 = n | 4 = n | YES (13,17,29,37,41) | smooth==random |
| 6 | 4 | 0.667 | 0.167 (halfJ 0.092, J 0.184) | 6 = n | 6 = n | YES (7,13,19,31,37)  | smooth==random |
Full radius profile: the UNIQUE radius in (halfJ,J) sits at incidence = n = the budget exactly; next
radius down (delta=0, <halfJ) has incidence 1.

VERDICT (two-sided, honest):
 POSITIVE (generic): eps_mca = incid/q = n/q = budget eps* exactly at this radius => delta* reaches the
   (halfJ,J) window (0.25 > halfJ 0.146) GENERICALLY; reverse L_force (>=2 at n=4, >=4 at n=6) is a real
   forced interleaved-list lower bound at the budget-binding radius.
 NEGATIVE (decisive): the mechanism is THICKNESS-INVARIANT -- smooth mu_n and a random generic domain
   give the IDENTICAL incidence (=n) at every tested prime in (halfJ,J). By rule 3 (CORE false in the
   thick window => thickness-invariant method neither proves nor refutes CORE), the reverse-dictionary
   floor-push at the window-top radius is NOT thinness-essential: A3's hope (smooth smaller list => higher
   thin floor) is REFUTED at the feasible radii -- no smooth-vs-random gap exists. The factor-of-two to
   full Johnson 1-sqrt rho is NOT closable by the reverse dictionary here; it genuinely needs the
   all-pairs / thin-essential input (SmallSubgroupGoodList), confirming HalfJohnsonDeltaStar's stated
   open problem from the floor side.

HONEST SCOPE (rule 6): only n-k=2 (rho 1/2, 2/3) is exact-feasible at small primes; the genuinely-thin
prize cone (rho 1/4-1/8) needs small n-k at large n (exact-infeasible -- same wall every worker hits). So
this is thickness-invariance at MODERATE rho; the DIRECTION (no thin gap at the window-top radius) is
robust over both rho and all primes, but the thin-rho extrapolation is NOT proven (future work, needs MITM
infra). WALLS the reverse-dictionary route to the floor-push at the tested radii; does NOT refute CORE.
Python-only, no Lean changed => axiom-clean trivially. First rule-3 gate on the reverse dictionary (grep:
"reverse" had 0 prior DISPROOF entries outside the lacunary one).

## ⚠️ REFUTATION (completes the even+odd picture) — the SIGNED odd moment beyond the Sidon depth: thin's deep-Sidon RIGIDITY makes signed cancellation WORSE, not better (2026-06-15, opus-4-8 subagent)

LENS: companion to the even-census-profile refutation (6feb11b53, even E_{2r} thin INFLATED). The surviving
thin advantage lives in the ODD/SIGNED object (r_min, d_odd deeper). Since mu_n is negation-closed, eta_b is
REAL, so odd moments A_r = sum_{b!=0} eta_b^r are real + sign-sensitive -- the natural home for the signed
cancellation the B_inf<-B_{log n} bootstrap needs. The odd_moment entry showed A_r=-n^r RIGID below d_odd
(W_r=0, no info). UNPROBED until now: does the SIGNED cancellation BEYOND d_odd (W_r>0) compound FAVORABLY
(thin cancels MORE => helps), measured against the RIGHT control?

RULE-3 CONTROL FIX: a random n-subset is NOT negation-closed (odd moments not even real). The correct control
that isolates the 2-POWER-SUBGROUP structure from mere negation-closure is a NEGATION-CLOSED random set: a
random union of n/2 antipodal pairs {x,p-x}. Compared thin vs this control via the signed-cancellation
EFFICIENCY eff_r := |A_r|/sqrt(E_{2r}) (Cauchy-Schwarz normalized; 1 = no cancellation, ->0 = full signed
cancellation). Exact real periods eta_b = sum_{x in S} cos(2pi b x/p); proper mu_n (m>1, never n=q-1);
prize primes p~n^{4-4.5} incl. non-Fermat. Probe scripts/probes/probe_407_signed_odd_profile.py.

RESULT (the separation appears at n=32, where d_odd is crossed within reach):
- n=16 (b=4.0, 4.5[nf]): thin AND neg-closed-random BOTH stay rigid A_r=-n^r through r=9 (d_odd>9 for both)
  -- no separation yet at reach (honest: small-n censored).
- n=32 (b=4.0, p=1048609): thin stays RIGID (A_r=-32^r EXACTLY) through r=7, non-rigid only at r=9. The
  neg-closed RANDOM control breaks rigidity EARLIER: r=7 random A_7=-1.32e10 != -32^7=-3.44e10; r=9 random
  -5.69e12 vs thin -1.54e13. CONSEQUENCE on the efficiency:
    r=7: eff_thin=0.695 vs eff_rand=0.270  (thin 2.6x WORSE at signed cancellation)
    r=9: eff_thin=0.796 vs eff_rand=0.301  (thin 2.7x WORSE)
  |A_r|(thin)/|A_r|(rand) = 2.60 (r=7), 2.71 (r=9): thin's |A_r| is LARGER.

MECHANISM (clean): thin's deep-Sidon RIGIDITY PINS A_r at the full -n^r (zero cancellation among the b's,
since W_r=0 forces A_r=-n^r exactly), while the random control's EARLIER d_odd onset lets its signed moments
CANCEL DOWN BELOW n^r. So "deeper Sidon" is ANTI-HELPFUL for signed cancellation: rigidity = no cancellation
= |A_r| pinned HIGH at n^r, the opposite of the suppression the bootstrap needs.

VERDICT (rule-4 mapped wall; completes the even+odd picture): the thin advantage in DEPTH (r_min, d_odd
deeper) does NOT translate to better moment cancellation in EITHER parity --
  EVEN (6feb11b53): thin energy E_{2r} collectively INFLATED, super-multiplicatively in r.
  ODD/SIGNED (here): thin's deep-Sidon rigidity PINS |A_r|=n^r, so signed-cancellation efficiency is 2.6-2.7x
  WORSE than the neg-closed random control beyond d_odd.
Both faces of the "collective thin depth profile -> smaller M via moments" hope are now mapped as adverse:
the very rigidity/Sidon-depth that the bootstrap touts is what KEEPS the moments large. The surviving hope is
NOT a moment/cancellation argument at all (both parities adverse) -- it must be a per-frequency / structural
estimate that does not pass through the period MOMENTS. CORE not closed, not faked. Small n (16 censored, 32
shows the separation), multi-prime incl. non-Fermat. Python-only, no Lean => axiom-clean trivially.

### The STATED CrossCellAbsoluteBound (BCHKS-1.12 as written) is FALSE at every prize-relevant depth -- NOT "the open wall" (2026-06-15)

Completes the crossCell-lever mapping (companions: tower no-go ad90dc8d5, super-random/p-indep 5a8d7fd42).
CrossCellShkredovBound.lean DEFINES and labels "the correct OPEN form ... NOT refuted; remains the wall":
  CrossCellAbsoluteBound :  forall r>=2,  crossCell(H,zeta,r)*q <= 2^r*|H|^r,  |H|=n/2  (= BCHKS Conj 1.12).
The per-level consumer N0_gap_of_absoluteBound uses exactly this. We show the STATED Prop is FALSE at every
feasible/prize-relevant depth.

KEY EXACT FACT: crossCell(n,4) = 3n^2/2, EXACTLY, char-0, p-independent. Derivation from in-tree bricks:
crossCell(n,4) = N0(G,4) - 2*N0(H,4) = E(mu_n) - 2*E(mu_{n/2}) = (3n^2-3n) - 2*(3(n/2)^2-3(n/2)) = 3n^2/2,
using AdditiveEnergyNegClosedLower E(mu_n)=3n^2-3n. Verified exactly: n=8->96, n=16->384, n=32->1536 (=3n^2/2).

(A) STATED bound at r=4:  (3n^2/2)*q <= 2^4*(n/2)^4 = n^4  <=>  q <= (2/3)*n^2.  Prize q~n*2^128 >> n^2 =>
    VIOLATED by ~2^128.  Exact at prize-shaped primes: n=8 b=4 p=4129: LHS=396384 > RHS=4096 (97x);
    n=16 b=4 p=65537: 25166208 > 65536 (384x); n=32 b=4: 1.6e9 > 1.05e6 (1536x).  False at thick b=2.3 too.
(B) depth threshold r0(n): the bound n^r >= crossCell(r)*q holds only once r*log2 n >= log2 crossCell(r) +
    log2 q (log2 q ~ log2 n + 128).  crossCell(r) is the FIXED char-0 structural count (p-indep), so r0 is
    LARGE: measured/extrapolated r0(8)~465, r0(16)~206 -- both >> the prize BINDING depth r ~ ln q ~ 89.
    So the stated inequality is FALSE at r=4..89 (every prize-relevant order) and only becomes true at an
    astronomically large, useless r0.

RECONCILIATION with the file's own probe ("crossCell tracks the random BCHKS-1.12 expectation (2^r-2)|H|^r/p
to O(1)"): that was measured at SMALL accessible primes (p ~ relation height) where crossCell ~ random. At
PRIZE primes (p ~ 2^128) the two DIVERGE by ~2^128 -- crossCell frozen at the char-0 structural value, the
random expectation -> 0.  The "to O(1)" agreement does NOT survive to the prize regime, which is exactly why
the stated absolute bound fails there.

VERDICT (rule-4 constraint map; precise correction, NOT a CORE result, NOT a refutation of the TRUE BCHKS
Conj 1.12 which is an asymptotic statement): the Lean Prop CrossCellAbsoluteBound, as written (forall r>=2,
crossCell*q <= 2^r|H|^r), is FALSE at every prize-relevant depth and is NOT the open wall the file labels it.
The genuine open object is a DEPTH-CORRECT, p-independent STRUCTURAL count bound at the binding depth r~ln q
(= the char-0 vanishing-sums-of-roots-of-unity / Lam-Leung object, in-tree ConverseLamLeung2Power), NOT the
literal 2^r|H|^r/q random count.  CONSISTENT with + completes the two companion crossCell results: (1) even
granting the (false-as-written) bound the tower iteration leaks to trivial M<=n; (2) the proposed sub-random
proof route is empty (crossCell super-random); (3) HERE: the bound as stated is itself false at feasible
depth.  All three pin the crossCell lever as mis-stated/non-closing in its current form; the live content is
the char-0 structural count (sibling-active thin-Sidon object), not a new arithmetic mechanism. CORE not
closed. probe_407_crosscell_absbound_false_at_prize.py. Exact DP, multi-prime, no Lean => axiom-clean trivially.

## ✓ RULE-6 RE-AUDIT (confirms 6feb11b53 robustly + one honest onset refinement) (2026-06-15, opus-4-8 subagent)

Adversarial re-audit of the even-moment-inflation push 6feb11b53, addressing two worries: (W1) "exceeds the
(M_thin/M_rand)^{2r} sup prediction" could be a cross-draw artifact (random median moment vs random median sup
from DIFFERENT draws); (W2) the inflation could be 5-draw variance. FIX: 21 random draws, per-draw
self-consistent (each draw's M and E_{2r} from the SAME spectrum), apples-to-apples sup prediction (the
max-MOMENT draw's OWN M). Probe scripts/probes/probe_407_even_reaudit.py.

RESULT (n=16, β=4.0 + β=4.5[non-Fermat]):
1. INFLATION IS ROBUST, NOT VARIANCE: thin E_{2r} exceeds the MAX-moment random draw (most concentrated of
   21) at EVERY r≥2 — 21/21 draws below thin. Not a median artifact.
2. "EXCEEDS sup prediction" CONFIRMED but onset is r≥4 (apples-to-apples), not r≥3 as the original
   cross-draw comparison suggested at β=4.5: β=4.0 exceeds from r≥3 (thin/maxdraw 2.165 > sup-pred 1.943);
   β=4.5[nf] exceeds from r≥4 (r=3: 2.162 vs 2.238, just BELOW; r=4: 3.281 > 2.927). HONEST REFINEMENT: the
   "exceeds sup" claim holds at DEEP r (r≥4 robustly, r≥3 at β=4.0), with growing margin — my receipt's "at
   deep r" wording is accurate; the exact onset is r≥4 under the strict apples-to-apples test.
NET: 6feb11b53's two claims (collective inflation; exceeds sup at deep r) both STAND under 21-draw
self-consistent re-audit; the only adjustment is the precise onset (r≥4 strict, vs r≥3 loose). No overclaim
survives; the finding is robust. Python-only => axiom-clean trivially.

================================================================================
2026-06-14 wf-D1 (#444): the binding wf-NH far-line incidence I(n) is QUARTIC, not a small constant
--------------------------------------------------------------------------------
REFUTED (as a reading of the closure path): "at the binding radius δ* is a SMALL p-independent
computable combinatorial quantity off the √-cancellation wall, so the prize is a small number."
The p-independence is REAL (confirmed). The "small" part is FALSE.

OBJECT: FarCosetExplosion exact binding incidence, k=4, size=6 (s-k=2 over-determined), r=n-6,
far dir x^b (b in [4,6)), offset x^a, budget n. I(a,b) = #{γ : x^a+γx^b agrees with RS[4] on >=6}.
ENGINE: cofactor-factorized vectorized exact count (scripts/probes/probe_wf3D1_unified.py),
cross-validated EXACTLY vs the proven reference probe_farline_incidence_exact.incidence at n=16
(both 89, dir (10,4), p-independent across 3 primes). A colex-vs-lex CNS-rank bug was caught/fixed
before any number was reported.

VERIFIED (proven-per-fixed-n, p-INDEPENDENT):
  I(16) = 89   dir (10,4)   p in {200017,5000081,16777441}   I/n^4 = 1.358e-3
  I(32) = 1441 dir (18,4)   p in {1048609,1048897}           I/n^4 = 1.374e-3
  log-log slope (16->32) = 4.017  =>  I(n) ~ 1.37e-3 * n^4  (clean p-independent QUARTIC)
  binder = monomial x^4 = x^k (lowest far exponent), offset a ~ n/2+2.

CONSEQUENCE: at the fixed over-det radius r=n-6 the incidence is quartic, so I/budget ~ n^3 and the
radius sits FAR above δ* (consistent with the in-tree δ*=9/16 pin: r=10=n-6 is the FIRST bad radius,
I=89 >> 16). The binding object is a genuine high-degree (quartic) cyclotomic incidence count, NOT a
small constant. NET: the closure path's p-independence half STANDS and is reinforced (the whole δ*
curve is computable p-FREE, no √-cancellation needed to EVALUATE it); the "small computable number"
half is refuted. New open object: the r-PROFILE I(n,r) (δ* = largest r with I(n,r)<=n) — a finite
exact p-free computation, not a char-sum bound.
Python-only numerics => axiom-clean trivially. — wf-D1

================================================================================
2026-06-15 LD-radius plateau thinness gate (#444): the per-direction n-plateau
quantization is thinness-essential but ANTI-HELPFUL for the floor (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the list-decoding reframing (KB deltastar-perdirection-decomposition-listdecoding.md +
orchestrator redirect c.4704732... "the floor = mu_n list-decodes past Johnson"). Reframes
delta* = 1 - s*/n where s*(D,k) = max over far monomial lines x^a+gamma*x^b of the largest
agreement with RS[D,k] using <= budget=n scalars (the far-line LD radius). The per-direction
incidence I_dir(a,b;s) is a clean step function whose PLATEAU value = exactly n ("divisibility
quantization", n | #bad, attributed to mu_n being a subgroup). UNTESTED: is the plateau / the
resulting s* THINNESS-ESSENTIAL (rule-3), or domain-invariant?

METHOD: exact engine incidence (Python, cross-validated EXACTLY vs in-tree wf-D1 reference
n=16,k=4 dir(10,4) s=6 => I=89). PROPER subgroup mu_n=<h>, |mu_n|=n verified, h^{n/2}!=1, prize
band p~n^beta (beta=4 AND 5), p==1 mod n, index m>=2, NEVER n=q-1. RANDOM control = n distinct
nonzero non-subgroup elements at the SAME prime (the exact rule-3 contrast). 21 random draws +
3-prime q-invariance sweep. probe_407_ld_plateau_thinness{,_robust}.py.

RESULT (refutation-grade, rule-6 hardened):
1. SMOOTH s* is perfectly q-INVARIANT: s*=5 across {4129,4153,4177} (beta4) AND {32801,32833,
   32969} (beta5) for both n=8,k=2 and n=8,k=2-beta5. Genuine p-independent structural invariant.
2. The "=n plateau" QUANTIZATION is genuinely THINNESS-ESSENTIAL: 0/21 random draws ever produce
   a clean max_dir-incidence = n plateau; the subgroup ALWAYS does (the n|#bad cyclic-orbit
   divisibility). So rule-3: the plateau IS subgroup-specific. CONFIRMED.
3. BUT the plateau is ANTI-HELPFUL / NEUTRAL for the floor — it pins s* AT-OR-ABOVE the random
   LD radius, NEVER below it:
   - n=8,k=2 (beta4 AND beta5): smooth s*=5 is ABOVE all 21 random draws (random s*=4, dist all 4).
     delta*_smooth=0.375 < delta*_random=0.5. The subgroup plateau HOLDS the LD radius UP at the
     budget boundary (s=5 where maxI=8=n=budget) => one step LARGER than random. mu_n is CLOSER to
     the adversary, not further.
   - n=8,k=3: smooth s*=5 sits INSIDE random [5,5] (degenerate equal).

VERDICT (rule-4 mapped wall): the LD-reframing's central object — the per-direction n-plateau
"divisibility quantization" the KB attributes to mu_n being a subgroup — is real & subgroup-specific,
but it is a RED HERRING for proving s* small (delta* large): it makes the subgroup far-line LD radius
EQUAL-OR-LARGER than a random domain's, the WRONG direction for the prize floor. The smoothness of
mu_n does NOT suppress the far-line LD radius below random; if anything the cyclic-orbit quantization
pins it slightly higher. So a CORE proof routed through "mu_n list-decodes BETTER (smaller LD radius)
than random" is FALSE at probed sizes — the plateau thinness-essentiality is present but points the
wrong way. CORE not closed, not faked. Consistent with the orchestrator redirect (floor = LD past
Johnson is TRUE empirically i.e. mu_n ~ random) — and SHARPENS it: mu_n is not BETTER than random at
the far-line LD radius, it is at-or-slightly-worse, so the floor cannot come from a thinness ADVANTAGE
in this object. Python-only exact => axiom-clean trivially.

================================================================================
2026-06-15 LD-radius s* is STRUCTURED-PRIME-BLIND (#444): a purely-cyclotomic invariant
that cannot encode the meta-theorem's essential structured-prime mechanism (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: companion to the LD-radius plateau thinness gate (prev entry). The brief rule-2 + the §3/§4
meta-theorem: additive-moment/energy methods fail SPECIFICALLY at STRUCTURED (Fermat-type) primes,
where mu_n interacts non-generically with field arithmetic. UNTESTED: is the far-line LD radius
s*(mu_n,k) (the LD-reframing's core object) invariant under structured primes, or does Fermat shift it?

METHOD: exact engine incidence (cross-validated vs in-tree n=16 k=4 => I=89). n=8, k=2, proper mu_8,
budget=n, NEVER n=q-1. Primes: generic prize beta4 (4129), beta5 (32801), STRUCTURED Fermat 257=2^8+1
(F3-ish, index 32) and 65537=2^16+1 (F4, deep index 8192). All p==1 mod 8.

RESULT: s* = 5 (delta*=0.375) and the ENTIRE profile {3:HEAVY,4:HEAVY,5:8} is BYTE-IDENTICAL across
ALL FOUR primes — generic AND both Fermat structured primes incl. the deeply-structured F_4=65537.

VERDICT (rule-4 mapped, with the rule-6 caveat being the key insight): the far-line LD radius s* is a
CHAR-0 / CYCLOTOMIC invariant of the 2-power subgroup, completely BLIND to the structured-prime
arithmetic. The meta-theorem establishes the structured-prime mechanism is ESSENTIAL to CORE (moment
methods fail there for a reason). But s* does not see it at all. => the LD radius s* and the BGK moment
object measure DIFFERENT things. CONSEQUENCE: a CORE proof routed purely through s* ("mu_n list-decodes
past Johnson", the orchestrator redirect) is NECESSARY-NOT-SUFFICIENT — s* cannot encode the essential
structured-prime content. This is a real obstruction for the LD-reframing lane: the cleaner cyclotomic
object s* is too clean (structure-blind) to carry the prize's structured-prime mechanism. Pairs with the
prev entry (s* is thinness-essential in its plateau but anti-helpful + thinness-neutral in value): s* is
thinness-sensitive in QUANTIZATION but structure-blind in VALUE => it is a cyclotomic combinatorial
invariant, not the moment/BGK object the prize ultimately needs. CORE not closed, not faked.
Python-only exact => axiom-clean trivially. probe_407_ld_radius_structured_primes.py.

================================================================================
## ⚠️ REFUTATION (census->CORE lane) — the "#bad collapse to O(1) at the hifreq binding line" is THICKNESS-INVARIANT, NOT thinness-essential (2026-06-15, opus-4-8 subagent)
--------------------------------------------------------------------------------
LENS: the census<->CORE map (probe_407_census_core_bindingband_ratio.py + c.1037) showed at the
hifreq BINDING line #bad COLLAPSES to O(1) while #alignable overcounts up to 112x, and concluded
"CORE-effort should target #bad directly -- the #bad collapse to O(1) at the hifreq line is the real
CORE signal." NO probe had tested whether the #bad collapse ITSELF is THINNESS-ESSENTIAL (rule-3).
This entry closes that gap.

OBJECT (exact, the in-tree CORE/epsMCA object): #bad = number of distinct gamma s.t. the far line
x^A + gamma*x^B agrees with a deg<k RS codeword on a size-a subset of the subgroup G = <g>, |G| = n.
epsMCA <= #bad/p (epsMCA_le_of_badCount_le). The binding band = deepest a with align>0.

METHOD (probe-first, rule-2/rule-3 clean): exact mod-p, proper subgroup, index m=(p-1)/n>=2,
NEVER n=q-1, multi-prime (p-invariance check), k=3 (deep-ceiling m=2 weld shape). Cached inverse
pairwise differences (no modpow in the inner Vandermonde leading-coeff test). Compare THIN n=2^a
(prize family) vs THICK n with large odd part (n=12,18,20 -- where the prize is FALSE).
Probe: scripts/probes/probe_407_badcollapse_thinness.py.

RESULT (refutation-grade, p-INVARIANT across all primes tested):
  THIN  2^4 hifreq[9,7] : #bad-profile a4:737, a5:1, a6:1, a7:1, a8:1 ; BINDING a=8 #bad=1.  (p=65537 & 160001 IDENTICAL)
  THICK n=12 hifreq[7,5]: #bad-profile a4:163, a5:1, a6:1            ; BINDING a=6 #bad=1.  (p=20749 & 100057 IDENTICAL)
  THICK n=18 hifreq[10,8]:#bad-profile a4:829,a5:82,a6:82,a7:1,a8:1,a9:1; BINDING a=9 #bad=1.
  THICK n=20 hifreq[11,9]:#bad-profile a4:1881,a5:1,a6:1,a7:1,a8:1,a9:1,a10:1; BINDING a=10 #bad=1.
The #bad=1 collapse at the hifreq binding line is reproduced EXACTLY in the THICK regime (n=12,18,20,
large odd part, prize FALSE) -- a long #bad=1 plateau from a~5 up to the binding band, identical to the
thin 2-power family. p-invariant on every prime. (Adjacent non-hifreq lines #bad=O(k) e.g. 8,12,18,40
in BOTH regimes too -- also thickness-invariant.)

VERDICT (rule-4 mapped wall; rule-3 FAIL): the #bad-collapse-to-O(1) at the hifreq binding line is
THICKNESS-INVARIANT -- it is the single-far-line-root-locus geometry (one far line meets the subgroup
in O(1) "explainable" gammas), present identically in thin AND thick subgroups. It is therefore a
thickness-MONOTONE object and CANNOT be the thin-essential CORE mechanism (rule-3/§3: any method that
behaves the same in the thick window where the prize is FALSE is wrong). The census map's "target #bad
directly" recommendation inherits the SAME fate as the far-line incidence I(n) (wf-D1: p-independent
quartic -> Johnson) and the antipodal-domination object (lalalune §7.3 -> Johnson): the per-line #bad
geometry is computable, p-clean/thickness-clean, and converges to the Johnson/Plotkin proxy -- it gives
NO beyond-Johnson, thin-only signal. The prize-distinguishing content is NOT in the per-line #bad count;
it lives only in the COLLECTIVE/aggregate object (sum over directions = the BGK moment), consistent with
the §4 meta-theorem and the route-elimination consensus that the Johnson radius is exactly the boundary
between the closed/thickness-invariant per-line regime and the open/BGK aggregate regime.
CONSTRAINT LEMMA (candidate, axiom-clean Lean): "per-line #bad at the binding band is invariant under
the odd part of |G| (depends only on the far-line/codeword incidence geometry, not on 2-power
structure)" -- formalizable as a statement that badScalars.card at the hifreq binding band factors
through the single-far-line agreement locus, which is defined field-/subgroup-structure-free.
CORE not closed, not faked. Python-only exact => axiom-clean trivially.

================================================================================
2026-06-15 LD plateau = single dilation orbit: EXACT numerical corroboration of in-tree
wf3D4 monomial_badset_orbit_closed, extended to Fermat prime (#444) (opus-4-8 subagent)
--------------------------------------------------------------------------------
Probe-first verification of the MECHANISM behind the plateau-=-n (the prev two LD-radius entries).
INDEPENDENTLY rediscovered + numerically confirmed the in-tree axiom-clean theorem
_wf3D4_monomial_worst_orbit.lean::monomial_badset_orbit_closed ("the bad-gamma set of a monomial
direction is a union of <mu^{b-a}>-orbits"). Exact, proper mu_n, binding direction extracted directly.

RESULT (exact, all three cases incl. Fermat 257):
- binding direction at the plateau is (a,b)=(k, k+1) => b-a=1, gcd(n,b-a)=1.
- the bad-gamma set has |.|=n EXACTLY and is CLOSED under gamma -> gamma*h^{b-a} (the dilation z->hz
  action, gamma reparametrised by h^{b-a} per monomial_dilated_line). gcd(n,1)=1 => <h^{b-a}>=full mu_n
  => exactly ONE orbit of size n => plateau pins at n. Mechanism CONFIRMED.
- Holds identically at generic primes (4129) AND the structured Fermat prime 257=2^8+1 (the in-tree
  file only anchored n=16,k=4 generic; this adds n=8 k=2/k=3 + Fermat corroboration) — consistent with
  the s*-is-structured-prime-blind entry: the orbit closure is a char-0/cyclotomic fact, p-free.

NET: corroborates the orchestrator's wf3D4 brick numerically and extends its anchor to the Fermat
structured prime; combined with the two prior LD-radius entries, the full picture is: the monomial
dilation-orbit (proven, axiom-clean) FORCES the plateau=n quantization (thinness-essential), but that
quantization pins s* AT-OR-ABOVE random + is structure-blind in value => the proven orbit mechanism is
real but points the WRONG way for the floor (it is the residual open Prop "does the aligned orbit EXCEED
budget" that carries the prize, and the orbit being exactly =budget at the binding is the knife-edge).
CORE not closed. Python-only exact => axiom-clean trivially. probe_407_ld_plateau_dilation_orbit.py.

================================================================================
2026-06-15 The e2=0 over-det census (the prize FLOOR's load-bearing R1 object) is
THINNESS-ESSENTIAL: built on antipodal pairing, VANISHES for random domains (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the in-tree prize skeleton. DeltaStarEqEdge.lean reduces the FLOOR to ONE open hyp (R1, `hgood`):
the e2=0 over-det locus is the BINDING worst-case bad-scalar family at the window edge. _E2Dilation
DirectCount.lean reduces that count EXACTLY to #bad = n*K, K = #dilation-orbits of e1(S) over
{S subset mu_n, |S|=w=n/2, e2(S)=0, e1(S)!=0}. In-tree: K=1,3,38 at n=8,16,32. K(n) IS the open
extremal census. NO live worker / report had applied a rule-3 thinness gate to K. UNCONTESTED.

METHOD: exact e2=0 enumeration over all C(n,w) w-subsets (feasible n<=16), smooth mu_n vs 11 random
non-subgroup domains, prize prime p~n^4, never n=q-1. + mechanism probe (antipodal/density/p-indep).

RESULT (refutation-grade, rule-6 hardened):
1. RANDOM domains have ZERO e2=0 bad-sets (0/11 draws at BOTH n=8 and n=16). Smooth has n*K (8, 48=#bad,
   matching n*K exactly; bad-SETS 8, 64).
2. NOT a density artifact: density baseline E[random hits] = C(n,w)/p = 0.017 (n=8), 0.196 (n=16); smooth
   EXCESS over baseline = 7.98, 63.80 => overwhelmingly STRUCTURAL.
3. p-INDEPENDENT (char-0 structural): #e2=0 subsets identical across 2 prize primes each (8,8 / 64,64) =>
   genuine cyclotomic count, not a mod-p accident.
4. MECHANISM: EVERY e2=0 subset contains >=1 ANTIPODAL PAIR (8/8, 64/64; none fully antipodal-closed). The
   locus is built on the subgroup's antipodal pairing x,-x=h^{n/2}x both in mu_n — a structure random
   domains lack entirely.

VERDICT (rule-3 PASS, strongest form): the e2=0 over-det census K(n) — the load-bearing open object the
ENTIRE prize FLOOR reduces to (DeltaStarEqEdge R1 + Attack-2 #bad=n*K) — is THINNESS-ESSENTIAL in the
strongest sense: it is a pure subgroup-antipodal-pairing object and VANISHES identically for random
domains. This is the RIGHT-DIRECTION thinness signature the prize needs (unlike the LD-radius plateau /
even-moment profile, which were anti-helpful). The K(n) growth (1,3,38,...) is the genuine prize content,
structurally anchored to antipodal pairs. Formalization target: K(n) = orbit-census of e1 over the
antipodal-pair-supported e2=0 locus. CONSEQUENCE for R1: the e2=0 family being thin-only SUPPORTS its
candidacy as the binding worst-case family (a random/generic family contributes 0 here), but does NOT by
itself bound K(n) — the open content is purely the K growth law (the additive-energy twin). CORE not
closed, not faked. Python-only exact => axiom-clean trivially.
probe_407_e2_census_K_thinness.py + probe_407_e2_census_mechanism.py.

================================================================================
## ⚠️ REFUTATION + REPLACEMENT LAW — the char-0 far-line delta* candidate "delta* = (1-rho) - log2(n)/n" is FALSE at n=64; the true law is s*-k = n/4 i.e. delta* = 3/4 - rho (2026-06-15, opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the full-assault-synthesis "live lead" (docs/kb/deltastar-444-full-assault-synthesis + 
deltastar-407-char0-logn-over-n-candidate): a NEW candidate char-0 worst-case far-line crossing
gave n*(cap-delta*)=log2(n) at n=16,32 (rho=1/8), conjecturing delta*=(1-rho)-log2(n)/n (a
Theta(log n/n) gap, "much closer to capacity than the standing Theta(1/log n)"). FLAGGED "NOT
confirmed -- needs n=64". The n=16-vs-n=20 convention discrepancy (s*-k = log2(n) vs constant 3)
was the explicit OPEN tension (DISPROOF "s*-k appears CONSTANT" entry: "n=32,64 must resolve it").
I ran the decisive n=64 computation.

METHOD: the in-tree char-0 (k+1)-subset-solve engine (scripts/probes/probe_char0_deltastar_n64_BIG.py),
cross-validated EXACTLY vs the wf-D1 reference. Char-0 = q-free worst-case far-line incidence I_0(w)
crossing budget=n, MAX over far pencils (a,b), a,b>=k, a,b != n/2, gcd-stratified pencil sampling +
deep antipodal directions. PROPER subgroup mu_n, p>>n^3, p==1 mod n, NEVER n=q-1. k=2 FIXED (so
rho=k/n SHRINKS with n -- the constant-k axis the candidate was stated on).

RESULT (refutation-grade, Q-INVARIANT -- two primes per n, p/n^3 = 4 AND 40 identical):
| n  | k | rho   | s*-k | n/4 | log2(n) | delta*=(n-w_cross)/n | worst pencil (a,b) gcd(b-a,n) |
|----|---|-------|------|-----|---------|----------------------|-------------------------------|
| 16 | 2 | 1/8   | 4    | 4   | 4       | 0.62500              | (5,9)   gcd=4=n/4              |
| 32 | 2 | 1/16  | 8    | 8   | 5       | 0.68750              | (9,17)  gcd=8=n/4              |
| 64 | 2 | 1/32  | 16   | 16  | 6       | 0.71875              | (2,34)  gcd=32=n/2            |
s*-k = 4,8,16 = EXACTLY n/4 (NOT log2(n) = 4,5,6). At n=64: s*-k=16, log2(64)=6 => the candidate is
OFF BY 10. Q-invariant: n=64 gives s*-k=16 at BOTH p=1048609 (p/n^3=4) AND p=10486337 (p/n^3=40),
same worst pencil (2,34). [The n=16,32 coincidence s*-k=log2(n) was a small-n ARTIFACT: 4=4 at n=16,
8 vs 5 already diverges at n=32 under the full-direction MAX convention -- the candidate doc used a
coarser pencil set that under-sampled the d=n/4 worst direction.]

THE TRUE LAW (exact at n=16,32,64): **s*-k = n/4**  =>  **delta*_charline = 1 - (k+n/4)/n = 3/4 - k/n
= 3/4 - rho**. Verified: 3/4-1/8=0.625, 3/4-1/16=0.6875, 3/4-1/32=0.71875 -- EXACT. The worst pencil
is the deeply-composite direction gcd(b-a,n) in {n/4, n/2} (the antipodal/subgroup-coset family), not
a generic pencil -- consistent with the dyadic Mann/Conway-Jones antipodal-pair mechanism (the only
primitive vanishing relation over mu_{2^mu}).

VERDICT (rule-4 mapped: refutes a candidate + installs the correct law; rule-6 honest):
1. The "delta* = (1-rho) - log2(n)/n" candidate (Theta(log n/n) gap, "the live lead" of the
   full-assault synthesis) is FALSE. The char-0 far-line gap below capacity is a CONSTANT 1/4
   (delta* = 3/4 - rho => cap - delta* = 1/4 - 0 = 1/4 for k=2... precisely cap-delta* = (1-rho)-(3/4-rho)
   = 1/4, a CONSTANT, NOT log2(n)/n -> 0). So the char-0 far-line delta* sits a FIXED 1/4 BELOW capacity.
2. s*-k = n/4 is LINEAR in n (like the rho=1/4 law s*-k=n/4-1), NOT Theta(n/log n). So -- exactly as the
   prior over-det entries concluded for fixed-rho -- this char-0 worst-case FAR-LINE delta* does NOT
   track the conjectured BGK floor delta*=1-rho-Theta(1/log n); it is the (rigorous UPPER bound)
   far-line object, converging to 3/4-rho, a clean cyclotomic combinatorial value OFF the BGK wall.
3. NET for the synthesis: the "much closer to capacity" optimism was a small-n sampling artifact; the
   true char-0 far-line delta* = 3/4 - rho is a fixed 1/4 below capacity and carries NO sub-log gap.
   The genuine prize content remains in the collective BGK aggregate (the L7 WorstCaseIncidenceBounded
   Prop), NOT in this per-pencil char-0 crossing.
CORE not closed, not faked. Python-only exact, q-invariant 2-prime => axiom-clean trivially.
Probe scripts/probes/probe_char0_deltastar_n64_BIG.py (--n {16,32,64} --k 2 --allfar / select).

---
## wf-D2 (#444): closed form delta* = 1/2 + 1/n (= Johnson + 1/n), NOT the floor — proven-exact n=16..28

Lane D2: closed form of the binding far-line monomial incidence I(n) and delta* vs the prize
floor 1-rho-Theta(1/log n). EXACT (vectorized numpy, p-independent; cross-checked vs in-tree
probe_farline_incidence_exact + GPU H100 oracle on #444).

far-line incidence I at over-det level c=s-k (worst far monomial b=k, budget=n), EXACT:
  n=8  (k=2): c=4 ->1 ; c=3 ->8 ; c=2 ->9 ; c=1 ->40
  n=16 (k=4): c=4 ->9 ; c=3 ->9 ; c=2 ->89 (= the established I(16)=89, hist {56:1,32:8,2:64,1:16}) ; c=1 ->3696
  n=24 (k=6): c=2 -> 1153 (hist {1026:1,516:8,...})

THE BINDING LAW (regime A, n=16,20,24,28 -- 4/4 EXACT):
  s* = 2k-1 = n/2 - 1  (binding over-det level c* = k-1 = n/4-1)
  delta* = (n - s*)/n = (n/2+1)/n = **1/2 + 1/n**  = JOHNSON(rho=1/4)=1-sqrt(rho)=1/2  +  one rung 1/n.

ASYMPTOTIC VERDICT: delta*(regime A) -> 1/2 = Johnson radius as n->inf. The prize floor is
3/4 - Theta(1/log n) (rho=1/4). The far-line incidence threshold CONVERGES TO JOHNSON, a CONSTANT
gap 1/4 BELOW the floor -- it does NOT certify the window interior (1/2, 3/4). The "delta* is a
computable combinatorial quantity" hope is CONFIRMED (p-independent closed form 1/2+1/n) but the
quantity it computes is the JOHNSON endpoint, not the floor. So this route does NOT close the prize.

REGIME B (n>=32, GPU): delta* jumps up (0.594, 0.618, 0.658) but s* PINS at exactly 13 across
n=32,34,38 while regime A had s* strictly increasing 7,9,11,13. GPU flagged n>=36 deep-binding
TIMED OUT. A pinned s* with climbing delta* is the signature of a SEARCH CEILING, not a law. n=32
deviation (s*=13 not 15) may be real (n=32 was within H100 reach) and is the genuine open sub-question.
Python-only exact + p-invariant => axiom-clean trivially. Probes probe_wf3D2_*.py.

================================================================================
2026-06-15 e2=0 census WIDTH PROFILE: super-budget at all widths past the smallest;
corroborates wf-D5 free-mu_{n/2}-action backbone from the census side (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: K(n,w) width profile of the e2=0 census (the prize FLOOR's R1 object). Follow-up to the
thinness-essential / antipodal finding (417015191). Goal: where does #bad=n*K cross budget=n across
widths w, and the growth law. Method: exact e2=0 antipodal-pair meet-in-middle, VALIDATED vs in-tree
K=1,3,38 (n=8,16,32 at w=n/2). Prize prime, proper subgroup, never n=q-1.

RESULT (exact, full width profile n=8,16,32):
1. #bad(n,w) is SHARPLY NON-MONOTONE in w with thin-quantized structure: 0 at tiny w; jumps at w=4
   (=k+2, deepest over-det) to 8,48,224; drops to EXACTLY budget at w=5 (8,16,32 = n, K=1); 0 at w=6,7;
   then a super-budget middle band peaking at w=n/2 (the 1216 extremal at n=32).
2. The shallowest over-det width w=k+2=4: #bad = 8,48,224, K = 1,3,7. #bad/budget = 1,3,7 (GROWS);
   #bad ~ n^2.40. The extremal w=n/2: #bad=8,48,1216, n*K ~ n^3.6.
3. So the e2=0 census is SUPER-BUDGET at every width past the smallest (w>=8 for n>=16), and the excess
   over budget GROWS with n. Even the shallowest family (w=4) has #bad/n = 1,3,7 -> super-linear.

VERDICT (rule-4 mapped, NO overclaim): the e2=0 antipodal census #bad grows super-budget (n^2.4 shallow,
n^3.6 extremal), matching the dossier's known "over-det max ~cubic n^3" ballpark and CORROBORATING the
just-landed wf-D5 result (7381dea4a: I(n)=1+(n/2)*O(n), free mu_{n/2}-action backbone) FROM THE CENSUS
SIDE: my antipodal-pair mechanism (every e2=0 subset has >=1 pair x,-x=h^{n/2}x) IS the free mu_{n/2}-
action wf-D5 proved structural. Consistent with wf-D2 (e48d5ef59: delta*=1/2+1/n -> Johnson not floor):
the e2=0 census, being super-budget and tracking the over-det cubic, does NOT exhibit a within-budget
floor at fixed small width => the binding delta* sits where this super-budget curve crosses budget, only
at the smallest widths (w=5, K=1, #bad=n exactly), which is the budget-pinned single-orbit knife-edge.
The census super-budget growth is the prize content; it points toward Johnson-tracking (wf-D2), NOT an
off-budget floor, at probed n. CORE not closed, not faked. The thin-ONLY nature (417015191) stands; this
adds the width profile + growth + the wf-D5 census-side corroboration. Python-only exact => axiom-clean.
probe_407_e2_K_growth_antipodal.py (validated MIM) + probe_407_e2_K_width_profile.py.

================================================================================
2026-06-15 The e2=0 census K is WITHIN floor budget (K<=1) ONLY at radii DEEPER than
Johnson; at/above the Johnson edge K is large + super-linear (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the load-bearing e2=0 census R1 object (DeltaStarEqEdge.lean hgood + _E2DilationDirectCount:
#bad = n*K). The sibling just proved K is THINNESS-ESSENTIAL (random domains give 0; push 417015191).
COMPLEMENTARY UNTESTED EDGE: the BUDGET question. Governing law (KB deltastar-orbit-count-reformulation):
delta* = sup{delta : I(delta) <= q*eps* ~= n}. So the e2=0 family is WITHIN the floor budget IFF
#bad = n*K <= n  <=>  K <= 1. In-tree K=1,3,38 at n=8,16,32 (w=n/2) already VIOLATES this for n>=16.
The decisive question NObody mapped: K(n) is reported only at the SINGLE width w=n/2; is K<=1 (budget-OK)
anywhere, and at WHICH radius? (n=64 enumeration is infeasible: C(64,32)~1.8e18, ~1.1e11 e2=0 sets.)

METHOD: exact MITM width-sweep over the FULL FLOOR WINDOW delta in (Johnson=1-sqrt(rho), cap=1-rho),
proper mu_n, prize prime p=n^4, ALL w from 2..(Johnson width). (Prior sweep skipped w=3,6,7 -- I filled
them.) k=2. /tmp/e2_floorwindow.py (+ in-tree probe_e2_widthsweep_directcount.py for the full 2..n/2).

RESULT (exact, n=16 AND n=32 -- the COMPLETE floor window, w=odd parities included):
  n=16 floor window delta in (0.646,0.875) = w in (2,5.7):  w2:K0  w3:K0  w4:K3  w5:K1  (w6:K0=Johnson)
  n=32 floor window delta in (0.750,0.938) = w in (2,8):    w2:K0  w3:K0  w4:K7  w5:K1  w6:K0  w7:K0  (w8:K7=Johnson)
  ABOVE Johnson (w>=8, n=32): K EXPLODES super-linearly: 7,23,4,2,21,32,14,18,38,33 (w8..17).
  n=64 floor window delta in (0.823,0.969):  w2:K0  w3:K0  w4:K15  w5:K1  w6:K0  (w7+ Johnson-region, large)
KEY: across the ENTIRE deep floor window the e2=0 census is WITHIN budget (K<=1) at EVERY width EXCEPT
the single resonance w=4 (K=3,7,15 at n=16,32,64 = EXACTLY n/4-1). The super-linear K-explosion (the
in-tree 1,3,38 at w=n/2) is a JOHNSON-EDGE-AND-BELOW phenomenon (w>=n/4), NOT a floor-window phenomenon.
[CONVERGENCE: the w=4 value K=n/4-1 was independently pinned to a closed form in the entry below + ties
to wf-D2's s*-k=n/4 (push ce8cb602e). MY unique contribution here is the COMPLEMENT: w=4 is the SOLE
budget-overflow width across the WHOLE deep floor window -- every other window width has K<=1.]

VERDICT (rule-4 mapped constraint; CORRECTS my first draft; a COMPLEMENT to the sibling thinness result):
1. The e2=0 census R1 is WITHIN floor budget (K<=1) across essentially the whole floor window
   (delta in (Johnson,cap)) -- K=0 or 1 at every floor-window width EXCEPT the isolated w=4 resonance.
   This SUPPORTS R1's viability: deep in the window the binding e2=0 family does stay within budget.
2. The lone obstruction in the window is the w=4 RESONANCE (K=3,7 at n=16,32): the smallest even-symmetric
   vanishing locus (antipodal-quadruple sets {x,-x,y,-y}-flavored), where e2=0 has many solutions. It is
   FINITE/characterizable, not a generic growth -- a single bad width, not the BGK wall.
3. The super-linear K(n)=1,3,38 the in-tree file flags is the value AT w=n/2 (Johnson, delta=0.5), which
   is the LOWER window edge / below the floor -- NOT the floor edge. So "K is super-linear" describes the
   Johnson-region census, and does NOT by itself defeat the floor (which lives at delta>Johnson where
   K<=1 except at w=4).
4. NET (honest, rule-6): this is GOOD news for R1, sharply scoped -- the e2=0 binding family is
   within-budget across the floor window with a SINGLE exceptional width w=4. The real remaining question
   for R1 is whether that w=4 resonance (a) actually realizes a delta*-window-edge bad config, or (b) is
   dominated/excluded (it sits at delta=1-4/n -> 1, the extreme deep end, possibly above cap for the true
   k). The K-explosion above Johnson is consistent (the ceiling SHOULD overflow below the edge). This
   does NOT close CORE, but it REFRAMES the obstruction from "K super-linear everywhere" to "K<=1 in the
   window except the w=4 resonance" -- a finite, attackable object.
CORE not closed, not faked. K(64) full-window enumeration feasible at SMALL w (the window is shallow):
w<=7 needs only C(64,<=7) per side -- TRACTABLE, unlike w=n/2. Python-only exact => axiom-clean trivially.
probe_e2_widthsweep_directcount.py + /tmp/e2_floorwindow.py.

================================================================================
2026-06-15 EXACT CLOSED FORM for the shallow e2=0 census: K(n,4) = n/4 - 1,
#bad = n^2/4 - n; the census n/4 = wf-D2's s*-k=n/4 (opus-4-8 subagent)
--------------------------------------------------------------------------------
Beat the C(64,32) wall for the e2=0 census by enumerating the SHALLOWEST over-det width w=k+2=4 directly
(4-subsets: C(n,4)~n^4/24, n=64 => 635k, no MIM). This is the cleanest census sub-sequence.

RESULT (exact, p-INDEPENDENT across 2 prize primes each at n=16,32,64):
- K(n, w=4) = 1, 3, 7, 15  at n = 8, 16, 32, 64  (2-powers; n=48 non-2-power gives 11 too).
- CLOSED FORM (5/5 incl n=64): K(n,4) = n/4 - 1  EXACTLY. p-independent (char-0 cyclotomic).
- => #bad(n,4) = n*K = n(n/4 - 1) = n^2/4 - n  EXACTLY QUADRATIC. The Theta(n^2) over-det object the
  dossier names, now pinned to a clean closed form on the e2=0 antipodal census.
- loglog-slopes of #bad converge cleanly 2.585->2.222->2.115->2.078 -> 2.0 (quadratic).

CONNECTION: wf-D2 (e48d5ef59) + ce8cb602e found s*-k = n/4 => delta* = 3/4 - rho. The SAME n/4 is the
census orbit-count: K(n,4) = n/4 - 1. The shallow e2=0 census orbit-count IS the n/4 over-determination
depth, census-side. So the e2=0 antipodal census and the wf-D2 incidence law are TWO FACES of one n/4
structure (consistent with my width-profile's wf-D5 free-mu_{n/2} corroboration). #bad = n^2/4 - n is
super-budget (n^2 vs budget n), Johnson-tracking-consistent (wf-D2), NOT an off-budget floor.

VERDICT (rule-4, no overclaim): an EXACT p-independent closed form for the shallow e2=0 census,
K(n,4)=n/4-1, #bad=n^2/4-n. Sharpens the prior 3-point ~n^2.4 fit to an exact quadratic and ties the
census n/4 to wf-D2's s*-k=n/4. Formalizable target (the K(n,4)=n/4-1 closed form is a clean cyclotomic
count). CORE not closed: the closed form CONFIRMS super-budget (n^2/4 >> n) => no within-budget floor at
shallow width, consistent with Johnson-tracking. Python-only exact => axiom-clean trivially.
probe_407_e2_K_w4_n64.py (5-point, multi-prime verified).

================================================================================
2026-06-15 The shallow-width e2=0 census MAP + the w=5 KNIFE-EDGE (#bad=budget=n
exactly, single orbit, 2-pairs+singleton): cleanest formalization target (opus-4-8 subagent)
--------------------------------------------------------------------------------
Completed the shallow-width map of the e2=0 census (prize FLOOR's R1 object) for 2-power n, exact,
p-independent (2 prize primes each), to n=64:
  w<=3 : EMPTY (no e2=0 solutions)
  w=4  : K = n/4 - 1, #bad = n*K = n^2/4 - n  (super-budget quadratic; closed form, f1d5de96e)
  w=5  : K = 1 EXACTLY all n, #bad = n EXACTLY = budget  <-- THE KNIFE-EDGE  (1,1,1,1 @ n=8,16,32,64)
  w=6  : EMPTY again
  (then super-budget middle band, peaks w=n/2.)

THE w=5 KNIFE-EDGE (confirmed n=8..64, p-independent):
- #distinct-alpha = n EXACTLY = budget, single mu_n-orbit (K=1).
- EVERY w=5 e2=0 subset = EXACTLY 2 antipodal pairs + 1 singleton {x,-x,y,-y,z} (8/8,48/48,224/224,
  960/960). pairs cancel in e1 (=> e1=z), e2=0 forces a relation among x,y,z; bad-set={-1/z}=one orbit.
- ELEGANT cross-relation: #w5-subsets = 8,48,224,960 = n^2/4 - n = the w=4 #bad-count. The n^2/4-n
  width-5 subsets collapse (n/4-1)-to-1 onto exactly n bad-scalars (one orbit).

VERDICT (rule-4, no overclaim): the shallow e2=0 census is fully mapped with EXACT p-independent closed
forms: w=4 gives n/4-1 orbits (super-budget), w=5 gives exactly 1 orbit at #bad=n=budget (knife-edge),
w=3,6 empty. The w=5 family is the cleanest object on the entire board: #bad=budget EXACTLY, single
orbit, p-independent, explicit 2-pairs+singleton structure => a prime FORMALIZATION target (a clean
cyclotomic count = n). It is the candidate BINDING edge family (proximity gap exactly at budget). This
does NOT close floor-vs-Johnson (the w=5 family sits AT budget, neither above=fail nor strictly below=
floor-slack; the binding among ALL widths/families is the R1 residual) but it pins the cleanest knife-
edge witness. Consistent w/ wf-D2 Johnson-tracking + the shared n/4 structure. CORE not closed, not
faked. Python-only exact => axiom-clean trivially. probe_407_e2_w5_knife_edge.py.

================================================================================
2026-06-15 The shallow e2=0 over-det census is a w==0 (mod 4) RESONANCE: K(n,w)=n/4-1
iff 4|w, else K<=1 -- so the over-det floor object is within budget UNLESS k==2 (mod 4)
(opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: generalizing the e2=0 census R1 budget map (my push 74a54cdce: K<=1 across the deep floor window
except the w=4 resonance) + the K(n,4)=n/4-1 closed form (convergent entry). KEY QUESTION nobody asked:
the e2=0 vanishing is the over-det constraint for the pencil x^k + alpha x^{k+2} at agreement w=k+2 (in-tree
_E2DilationDirectCount line 13). The e2=0 constraint is the SAME quadratic for ANY k; only w=k+2 varies.
So K(n, w=k+2) depends on the WIDTH w only. Does the w=4 resonance PERSIST at prize-rate k (w=k+2>4)?

METHOD: exact shallow census K(n,w) = #dilation-orbits of e1(S) over {|S|=w, e2(S)=0, e1!=0}, brute
C(n,w) for shallow w, proper mu_n, prize prime p=n^4, never n=q-1. n=16,32,64. Vary k=2..6 (w=k+2=4..8).
probe_407_e2_census_general_k_resonance.py + probe_407_e2_census_n64_shallow.py.

RESULT (exact, the SHALLOW over-det regime w<=8, the prize-relevant shallowest over-det width):
  K(n,w) by width (n=16 / n=32 / n=64):
    w=2: 0/0/0   w=3: 0/0/0   w=4: 3/7/15   w=5: 1/1/1   w=6: 0/0/-   w=7: 0/0/-   w=8: 3/7/-
  => CLEAN RESONANCE: K(n,w) = n/4 - 1 EXACTLY when 4 | w (w=4: 3,7,15 = n/4-1 at n=16,32,64; w=8: 3,7
     at n=16,32), and K <= 1 (mostly 0, occasionally 1 at w=5) when 4 does NOT divide w.
  k-form: since w=k+2, the over-det census at the shallowest width OVERFLOWS budget (#bad=n*K~n^2/4)
     iff 4|(k+2) iff k == 2 (mod 4); for k !== 2 (mod 4) the shallow e2=0 over-det census is WITHIN
     floor budget (K<=1).

VERDICT (rule-4 mapped structural law; rule-6 honest, NOT a closure):
1. The e2=0 over-det census budget-overflow is an ARITHMETIC RESONANCE on the agreement width:
   4 | w => K = n/4-1 (overflow), else K <= 1 (within budget). This SHARPENS my floor-window result
   (74a54cdce) from "single w=4 resonance" to the periodic law "4|w resonance" and explains the
   w=4 AND w=8 spikes.
2. PRIZE-RATE CONSEQUENCE: the prize is forall-rate (rho free); for the AP of rates with k == 2 (mod 4)
   the shallowest over-det e2=0 family overflows budget by Theta(n) at w=k+2, but for k !== 2 (mod 4) it
   is within budget at that width. So the e2=0 over-det census does NOT uniformly defeat the floor across
   rates -- it has a width-divisibility structure. (This is consistent with the n/4 over-determination
   depth being the universal object: 4|w is exactly when the antipodal-quadruple {x,-x,y,-y} vanishing
   saturates the orbit count to n/4-1.)
3. The DEEPER widths (w>=9, approaching Johnson) LOSE the clean 4|w law (K=23,4,2,21,32,... at n=32) --
   that is the BGK/additive-energy regime where the census is the analytic wall's twin. The clean
   resonance law holds in the SHALLOW over-det regime only (the floor-edge-relevant widths).
4. NET: the over-det e2=0 census is NOT a uniform floor obstruction; it is a 4|w arithmetic resonance
   that is within budget for 3/4 of rates (k !== 2 mod 4) at the shallowest width, and the only structural
   overflow is the antipodal-quadruple saturation at 4|w. CORE not closed: this maps WHERE the over-det
   census obstructs (4|w) vs is benign, but the actual prize floor still needs the COLLECTIVE BGK bound
   at the binding depth (the L7 Prop), not this per-width census. Python-only exact, p-independent =>
   axiom-clean trivially.
probe_407_e2_census_general_k_resonance.py + probe_407_e2_census_n64_shallow.py.

================================================================================
2026-06-15 ★ LIVE-LEAD (route 36, never-tried per ledger): mu_n deep holes ARE concentration
points; deep-hole monomials are EXACTLY x^j with j == k (mod 4) -- a FINITE n/4-size candidate
set for the worst-case u0 (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: route 36 (deltastar-100-routes.md), flagged "★ GENUINELY LIVE (never-tried)": "deep-hole
classification of RS (Cheng-Murray, Zhu-Wan) -- explicit worst u0 = deep hole; first step: are
smooth-domain deep holes concentration points? (probe)". 0 hits in DISPROOF_LOG => genuinely untouched.
The L7 open core WorstCaseIncidenceBounded is a sup over stacks (u0,u1); if the worst u0 is a deep hole,
route 36 reduces the sup to a FINITE deep-hole candidate family (the never-tried payoff).

METHOD: exact mod-p. RS[k] eval code on D=mu_n. distance(u,RS)=n-max_{deg<k g}agreement (exact via
k-subset interpolation). covering radius R=max_u dist; deep hole = dist=R. Then the concentration object:
for monomial pencils (x^a,x^b), #bad-gamma(agree>=smin) = #{gamma: x^a+gamma*x^b agrees with deg<k on
>=smin pts}. Test whether the WORST (max #bad) pencil uses a deep-hole exponent. n=8,16, k=3, prize prime.
probe_407_deephole_classification.py + probe_407_deephole_concentration.py.

RESULT (exact):
1. DEEP-HOLE CLASSIFICATION over mu_n (monomial scan): the deep-hole monomials x^j are EXACTLY
   j == k (mod 4):
   - n=8, k=3:  deep holes j in {3,7}      (covering radius R=5=n-k=n-3, max-agree=k=3)
   - n=16, k=3: deep holes j in {3,7,11,15} (R=13=n-k, max-agree=k=3) -- exactly j==3 (mod 4).
   The x^{n/2-family} exponents (j=8,9,10 at n=16) are NOT deep holes (agree=n/2=8, much higher).
   So deep holes = the minimal-agreement (=k) monomials at j==k mod 4: a FINITE set of size ~n/4.
2. CONCENTRATION: the WORST-case pencil DOES use a deep-hole exponent. n=8 k=3 smin=k+1=4:
   worst #bad-gamma=40 achieved by pencils (3,4),(3,6),(4,7),(6,7) -- EVERY one includes a deep-hole
   exp in {3,7}; the pure-non-deep-hole pencils (4,5),(5,6) cap at #bad=32 < 40. So mu_n deep holes
   ARE concentration points (route-36 premise CONFIRMED at n=8).
   CAVEAT (rule 6): the two-deep-hole pencil (3,7) (gcd=4=n/2) gives only #bad=8 -- the worst is
   ONE deep-hole exp paired with a coprime-step neighbor, not both deep holes. So "deep hole" is
   NECESSARY-flavored for the worst pencil but the pairing structure also matters.

VERDICT (rule-4 mapped, but a POSITIVE LIVE LEAD not a refutation): route 36 is NOT dead -- its premise
holds at probed scale: (a) mu_n deep holes have a clean closed classification (x^j, j==k mod 4, size
~n/4), and (b) the worst-case concentration u0 uses a deep-hole exponent. This gives a FINITE candidate
family for the L7 sup-over-u0 (the never-tried payoff the ledger flagged). NEXT STEP (the genuine open
work): bound #bad-gamma over the deep-hole family directly -- if the deep-hole exps' #bad is itself
capped (the deep-hole list curve L(a) the KB mentions has no closed form, but it is now restricted to
j==k mod 4, a structured finite set). This connects to the wf-D2 worst pencil (composite-step) -- the
worst pairing is deep-hole-exp + coprime/composite-step neighbor. Whether the deep-hole-restricted sup
beats Johnson is the live question. CORE not closed; this OPENS a finite-candidate handle on the L7 sup.
Python-only exact => axiom-clean trivially.
probe_407_deephole_classification.py + probe_407_deephole_concentration.py.

================================================================================
2026-06-15 CORRECTION to the route-36 deep-hole classification: "j == k (mod 4)" was a
k=3 COINCIDENCE; the true law is R=n-k with deep-hole count n/4 (odd k) / n/2 (even k)
(opus-4-8 subagent, self-correcting push 1b3f947fa)
--------------------------------------------------------------------------------
RULE-6 SELF-CORRECTION of my prior route-36 entry (push 1b3f947fa), which claimed mu_n deep-hole
monomials are "EXACTLY x^j with j == k (mod 4)". That was tested only at k=3. Re-tested k=2,3,4,5:

EXACT (n=8,16, prize prime, monomial deep-hole scan):
  k=2 (n=16): deep = {2,3,6,7,10,11,14,15}  = j mod 4 in {2,3}   (count n/2)
  k=3 (n=16): deep = {3,7,11,15}             = j mod 4 in {3}     (count n/4)  <- the coincidence
  k=4 (n=16): deep = {4,5,6,7,12,13,14,15}   = j mod 8 in {4,5,6,7}(count n/2)
  k=5 (n=16): deep = {5,7,13,15}             = j mod 8 in {5,7}   (count n/4)

TRUE LAW (corrected): covering radius R = n - k ALWAYS (deep holes = monomials with MINIMAL agreement
= k with deg<k). Deep-hole COUNT = n/4 for ODD k, n/2 for EVEN k. The clean single-residue "j==k mod4"
holds ONLY at k=3. So the deep-hole candidate family is finite + structured but LARGER than my n/4 claim
for even k (it is n/2).

IMPACT ON THE ROUTE-36 LEAD (rule-6 honest): the route-36 PREMISE still stands -- (a) deep holes have a
clean closed classification (R=n-k, the minimal-agreement monomials, n/4 or n/2 of them), and (b) the
worst-concentration u0 uses a deep-hole exponent (n=8 confirmed). The lead is NOT killed; only the size
of the candidate family is corrected (n/2 for even k, not uniformly n/4). The L7 sup-over-u0 still
reduces to this deep-hole family. The open work (bound #bad over the deep-hole family vs Johnson) is
unchanged. CORE not closed. Python-only exact => axiom-clean.
probe_407_deephole_kvary.py.

================================================================================
2026-06-15 CENSUS ROUTE INTERNAL INFEASIBILITY: the deployed CensusDomination is
FALSE at ITS OWN weld budget eps* at the SHALLOW over-det bands (and the deepest
band) -- the route over-shoots the very supply bound that defines eps* (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (uncontested): c.1007 mapped census<->CORE as OVERSTATED (CensusDomination STRICTLY STRONGER than
CORE, via the one-way #bad<=#alignable). It left the DECISIVE viability question unasked: does the census
count K the route ACTUALLY bounds even FIT under the supply budget the SAME weld demands? The weld
(CensusDominationWeld.lean, kkh26_deltaStar_pin_of_censusDomination) requires hK: K/p <= eps*, and the
deployed eps* threshold (hεstar) is eps* = 2^r * C(2^{mu-1}, r) / p (the KKH26 fibre SUPPLY count). So the
route needs, at the binding deep band a_bind:
    K := max_{u0,u1} #alignableSets(a_bind)  <=  2^r * C(2^{mu-1}, r).    (FEAS)

OBJECT (semantics matched EXACTLY to UniversalAlignmentLaw.lean + probe_alignment_census.py): mu_n=<g>,
|mu_n|=n=2^mu, PROPER subgroup (m=(p-1)/n>1, NEVER n=q-1), prize prime p~n^beta. e_j(T)=divided diff
[x_{t0..tk}]u_j; S aligned iff all nondeg (k+1)-subtuples share one ratio -e0/e1; alignableSets = aligned
|S|=a sets w/ >=1 nondeg tuple. Prize shape m=1: k=(r-2)m+1=r-1, binding band a_bind=r*m+1=r+1. K is the
TRUE max over the char-line adversary (EXHAUSTIVE over all (A,B) pairs at n=8) + random pairs. Probes
probe_407_census_supply_budget_feasibility.py + probe_407_census_supply_budget_exhaustive.py.

VALIDATION (engine == in-tree c.1007): KKH26 [x^6,x^4] n=16 k=3 p=65537 reproduces a=4->1792, a=5->336,
a=6(bind)->56 EXACTLY. Engine trusted.

RESULT (K vs budget 2^r*C(2^{mu-1},r), exact mod-p, MULTI-PRIME incl. non-Fermat, p-INDEPENDENT):
  n=8  (mu=3): r=2 K=24=bud(1.00) VIABLE | r=3 K=32=bud(1.00) VIABLE | r=4 K=24 > bud=16 (1.50x) *DEAD*
               -- identical at p=4129,11593,32801 (3 non-Fermat primes): K is p-INDEPENDENT (char-0).
  n=16 (mu=4): r=2 K=288>112 (2.57x) DEAD | r=3 K=896>448 (2.00x) DEAD | r=4 K=1568>1120 (1.40x) DEAD |
               r=5 K=1456<=1792 VIA | r=6 1344<=1792 VIA | r=7 384<=1024 VIA | r=8 K=560>256 (2.19x) DEAD
               -- identical at beta=4.0 (p=65537) and beta=4.5 (p=262193, non-Fermat).
A char-line u0=x^A,u1=x^B is a LEGAL stack, so a SINGLE pair with #alignable>budget already FALSIFIES
CensusDomination at that K; K being a max (exhaustive over lines at n=8) makes each DEAD verdict a
rigorous LOWER bound that already exceeds budget. The DEAD rows therefore rigorously certify
CensusDomination is FALSE at the budget the weld itself specifies.

THINNESS CONTROL (rule 3): the budget-overflow is THICKNESS-INVARIANT -- thick non-2-power domains
n=6,10,12 ALSO overflow at the shallow band r=2 (n=6: K=18>12 1.50x; n=10: K=100>40 2.50x; n=12: K=144>60
2.40x), same as thin n=16 r=2. The infeasibility is a STRUCTURAL combinatorial fact (the alignable-set
count is combinatorially large relative to the 2^r*C supply at shallow over-det depth), not a
2-power-essential phenomenon. (Deeper thick bands give degenerate K=0 from repeated node-differences in
non-2-power domains, so the deep-band comparison is clean only on 2-power n.)

VERDICT (rule-4 mapped wall; rule-6 honest, NOT a CORE result and NOT a prize refutation):
1. The deployed in-tree census route is INTERNALLY INFEASIBLE as a sufficiency chain at the shallow
   over-determined proximity parameters (r small) AND the deepest band (r=2^{mu-1}): there K = realized
   census count EXCEEDS eps*p = 2^r*C(2^{mu-1},r), so the weld hypothesis CensusDomination is simply
   FALSE at the budget eps* the weld pins -- the route demands a bound that the object violates.
2. It is feasible (K<=budget) only in a MID-DEPTH band (n=16: r in {5,6,7}). The proximity-gap prize is
   forall-r (every rate), so an infeasible-at-some-r hypothesis CANNOT deliver the universal pin via this
   weld at those r. The census normal form is not just "strictly stronger" (c.1007) -- it is, at the
   shallow/deepest bands, STRONGER THAN TRUE.
3. SHARPENS c.1007: the #alignable/#bad slack was lossy+thickness-invariant; HERE the absolute count
   #alignable exceeds the SUPPLY budget itself (the eps* defining the route), a strictly stronger
   internal-inconsistency finding. The census route, as deployed, cannot be the prize's proof shape at
   all r; a CORE proof must bound #bad directly (which collapses to O(1) at the hifreq line, 95e633cb0),
   NOT route through the alignable-set census. CORE not closed, not faked.
HONEST SCOPE: exact small-n (8 exhaustive-over-lines, 16 worst-family+random), multi-prime incl.
non-Fermat, p-independent. K at n=16 is a max over a worst-line family + random (not fully exhaustive),
but every DEAD row is a rigorous lower-bound overflow. Python-only, no Lean changed => axiom-clean trivially.
probe_407_census_supply_budget_feasibility.py + probe_407_census_supply_budget_exhaustive.py.

================================================================================
2026-06-15 The LAST NON-MOMENT route (per-frequency worst-coset tower descent) is
DEAD: the worst-coset transfer ratio rho* is THICKNESS-INVARIANT and the two half-
coset periods are ALWAYS sign-aligned (no signed cancellation) (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the surviving residual, c.1263 verdict): "the surviving hope is NOT a moment/cancellation argument
(both parities adverse) -- it must be a PER-FREQUENCY / STRUCTURAL estimate that does NOT pass through the
period MOMENTS." Every prior per-freq probe was the sup constant R stratified by v2(INDEX) (supnorm_2adic)
or the half-coset alignment over ALL b (c.287, thickness-monotone). UNPROBED: a per-frequency MULTIPLICATIVE
DESCENT of the WORST-COSET period eta_{b*}(mu_n) onto level n/2 -- a non-moment tower recursion that, if
contractive + thin-essential, gives M(n) <= rho* M(n/2) -> sqrt-growth by induction (a non-moment proof shape).

OBJECT (exact, PROPER mu_n, m=(p-1)/n>1, NEVER n=q-1): real periods eta_b = sum_{x in mu_n} cos(2pi b x/p)
(mu_n neg-closed => real). mu_n = mu_{n/2} u h*mu_{n/2} EXACT per-freq split: eta_b(mu_n) = A + B,
A=eta_b(mu_{n/2}), B=eta_b(h*mu_{n/2}). Worst coset b* = argmax over coset reps (period depends only on
b*mu_n). Measured rho*(n) = |eta_{b*}(mu_n)| / max_b|eta_b(mu_{n/2})| and the half-split sign align=sgn(A*B)
at b*. Multi-prime incl. non-Fermat. Thick control: composite non-2-power n + its index-2 subgroup.
Probe scripts/probes/probe_407_worstcoset_perfreq_descent.py.

RESULT 1 -- align = +1.000 at the worst coset EVERYWHERE (thin n=16..128 AND thick n=12..40, all betas,
incl. non-Fermat): at b* the two half-coset periods A,B ALWAYS have the SAME sign (reinforce, NO signed
cancellation). Independently reproduces the c.287 alignment wall AT THE WORST COSET specifically -- the
worst frequency is exactly where the halves phase-add, so there is NO per-frequency signed contraction to
exploit. (The "tower self-similarity / phase alignment" candidate mechanism from the brief is dead at b*.)

RESULT 2 -- rho* < 2 (sub-doubling) but THICKNESS-INVARIANT (the decisive rule-3 test): rho* decays slowly
with n (sqrt-cancellation-consistent) but thin and thick lie on ONE rho*(n) curve, interleaved by n NOT by
thickness (beta=4.0):
  n=16 THIN 1.762 | n=24 thick 1.735 | n=32 THIN 1.584 | n=40 thick 1.432 | n=48 thick 1.411 |
  n=64 THIN 1.559 | n=80 thick 1.304 | n=96 thick 1.432 | n=128 THIN 1.271
The 2-power (thin) rows do NOT contract more than the non-2-power (thick) rows at comparable n; rho* is a
function of n alone (generic sqrt-decay), NOT 2-power-essential.

VERDICT (rule-4 mapped wall; rule-3 FAIL => the route is dead for the THIN-essential prize; rule-6 honest):
1. The per-frequency worst-coset tower descent is THICKNESS-INVARIANT (rho* same thin/thick at matched n)
   AND non-cancelling (align=+1 at b*). By rule-3 (CORE is FALSE in the thick window, so any thickness-
   monotone mechanism is wrong) this descent CANNOT prove CORE: it would prove the (false) thick bound too.
2. This closes the LAST named non-moment route. The board's residual after the even-moment (INFLATED) and
   odd-moment (RIGID, anti-cancelling) walls was "a per-frequency structural estimate off the moments";
   the natural such object -- a worst-coset multiplicative descent -- is now mapped as thickness-invariant
   + non-cancelling. The worst frequency is precisely where the 2-adic coset halves REINFORCE; the thin
   advantage (deeper Sidon depth) does NOT manifest as per-frequency worst-coset contraction.
3. CONVERGENT with the whole board: per-line incidence -> Johnson, per-census -> Johnson/super-budget,
   even moments inflated, odd moments rigid, per-frequency descent thickness-invariant. The open prize
   content lives ONLY in the COLLECTIVE BGK aggregate cancellation among ALL frequencies simultaneously
   (L7 WorstCaseIncidenceBounded), which no single per-object / per-frequency / per-parity face captures.
HONEST SCOPE: rho* at large n (m>20000) uses a uniform coset-rep SAMPLE (so M is a lower bound on the true
worst coset => rho* is a lower bound; a higher true rho* only STRENGTHENS the sub-doubling-but-invariant
reading, never creates a thin advantage). Multi-prime incl. non-Fermat, p-stable. align is exact (full b*).
CORE not closed, not faked. Python-only, no Lean => axiom-clean trivially. probe_407_worstcoset_perfreq_descent.py.

### THIN SIDON DEPTH does NOT grow: n=64 EXACT computation REFUTES the "thin r_min advantage grows with n" lane (2026-06-15, opus-4-8 subagent)

LANE (the SURVIVING positive thin signal, rule-3 PASS RIGHT-sign, w/ its own flagged open): the prior
"THIN SIDON DEPTH SCALES" entry reported the thin Sidon depth r_min(mu_n) margin over random GROWING
(+0,+0->+4 at beta=4; +0,+0->+8 at beta=5, n=8/16/32) but flagged: "the EXACT growth LAW (sqrt(n) vs
log^c n) is NOT yet resolved -- need n=64,128 to fit the exponent." n=8/16/32 thin rows were CENSORED at
rmax=n/2 (full-depth) EXCEPT the single n=32/beta=4 r_min=11 point => the exponent was DEGENERATE-UNFIT.
No live worker on the n=64 extension. Ran it.

OBJECT (identical to probe_407_thin_sidon_depth_scaling.py, validated): r_min(mu_n,p) = smallest
NON-antipodal subset S of Z/n with Sum_{i in S} zeta^i == 0 (mod p), zeta primitive n-th root, mu_n
PROPER 2-power subgroup of F_p*, p=ceil(n^beta) prime ==1(n), m=(p-1)/n>1, NEVER n=q-1. Antipodal pairs
{i,i+n/2} excluded. r_min=NONE up to rmax => full-depth.

METHOD: SOUND BRACKET (full n=64 MITM infeasible, C(32,16)~6e8/half). EXACT exhaustive lower bound (no
non-antipodal vanisher of size <= r0 => r_min>=r0+1, RIGOROUS) + randomized SOUND upper witness (explicit
witness => r_min <= s). SELF-CHECK n=32 beta=4 -> exact witness at 11 (reproduces published r_min=11).
probe_407_thin_sidon_depth_n64_bracket.py.

RESULT (exact, n=64 added; the thin depth DROPS, the margin SHRINKS):
| n  | beta=4 thin r_min | beta=4 rand median | margin | r/sqrt(n) | beta=5 thin r_min |
|----|-------------------|--------------------|--------|-----------|--------------------|
| 16 | >8 (full)         | 9                  | +0     | --        | >8 (full)          |
| 32 | 11 (exact)        | 7                  | +4     | 1.94      | >16 (full)         |
| 64 | **8 (exact)**     | 6                  | **+2** | **1.00**  | **10 (exact)**     |

EXPLICIT n=64/beta=4 WITNESS (p=16777601, zeta=6014800): S={15,17,22,29,32,33,38,63}, |S|=8, sum==0 mod p,
NON-antipodal; exhaustive MITM confirms NO non-antipodal zero-sum of size<8 => r_min(mu_64,beta=4)=8 EXACTLY.
Predictions: sqrt(n) law => r_min(64)~11*sqrt(2)=15.6; log law => 11*6/5=13.2. ACTUAL=8, BELOW BOTH.

VERDICT (refutation-grade for the SCALING claim; rule-4 wall, rule-6 honest, NOT a CORE result):
the "thin Sidon depth r_min advantage GROWS with n" reading does NOT survive the n=64 exact point at beta=4:
the absolute thin depth DROPS 11->8 and the thin-minus-random margin SHRINKS +4->+2 (not monotone). The
small-n growth was a CENSORING/CEILING artifact (n=16,32 thin rows full-depth-censored at rmax=n/2; n=32
r_min=11 sits near the ceiling 16). So the smallest-vanisher depth r_min is NOT the carrier of a growing
collective thin signal -- it is non-monotone and small-n biased. CONSEQUENCE: the surviving-thin effort
should target the HIGHER-ORDER collective moment profile (the L7 BGK aggregate the whole board converges
to), NOT r_min. This CLOSES the smallest-vanisher sub-lane. CORE not closed, no overclaim. Python-only
exact, no Lean changed => axiom-clean trivially. probe_407_thin_sidon_depth_n64_bracket.py.

================================================================================
2026-06-15 The OddExcessSpikeLaw value (the 2-adic even-direction collapse-failure
margin) is THICKNESS-INVARIANT -> the even-direction descent's odd-excess is NOT the
thin-specific prize mechanism (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the FRESH open core formalized by OddExcessLaw.lean (Shaw 80a89e78e): oddExcess = full_bad \
half_bad, |oddExcess| = E = I_n(x^{2a'}) - I_{n/2}(x^{a'}), oddExcess=empty <=> EvenDirectionIncidence
Collapse. The named-but-unproven OddExcessSpikeLaw: E=(n/2)^2 at the half binding rung. QUESTION nobody
asked (rule-3): is the SPIKE VALUE thinness-essential, or does it persist in the thick prize-FALSE window?

METHOD: exact per-witness-set affine-in-gamma incidence (probe_farline engine, NO floats, NO codeword
enum), PROPER mu_16, NEVER n=q-1. Object I_n(x^4) over mu_16, code degree 4, binding rung r=10 (delta
.625). Anchored I_n=89 EXACTLY (= in-tree probe_farline n=16 k=4 r=10). q-sweep index m=(p-1)/16 from
thick to thin. probe_407_oddexcess_qsweep.py + probe_407_oddexcess_n16_validate.py.

RESULT (exact):
  m=6(p97):57  m=7(p113):89  m=12:89  m=16(beta2.0):89  m=21(p337):81  m=22:89  m=27(p433):81
  m=36..75 (beta 2.29-2.56, the prize-FALSE thick window): 89,89,89,89,89,89,89,89  ALL 89
  m=151,201,250 (beta 2.81-2.99): 89,89,89   m=501,2016,4096 (thin): 89,89,89
  => I_n(x^4;r=10) = 89 IDENTICALLY across the thick beta=2.3-3.2 prize-FALSE window AND the thin regime.
     The dips (81 at p=337/433, 57 at p=97) are SPORADIC small structured-prime artifacts, NOT a
     thickness trend (89 returns at thicker p=113/193/257/353).

VERDICT (rule-4 wall, rule-3 FAIL): the OddExcessSpikeLaw value (the even-direction collapse-failure
margin) is a THICKNESS-INVARIANT cyclotomic constant. The 2-adic even-direction collapse fails by the
SAME ~(n/2)^2 margin in the thick prize-false regime as in the thin prize regime => the collapse FAILURE
is thin-blind. A thinness-essential proof of CORE cannot route through the even-direction descent's odd-
excess value. Joins the board meta-pattern (every per-direction object is thickness-invariant + Johnson-
tracking; only the aggregate BGK moment is open). RULE-6: does NOT close CORE, does NOT refute the in-
tree oddExcess_card or the named Prop (the collapse genuinely fails; E IS the obstruction) -- it maps
that the obstruction's VALUE is thin-independent. Python-only exact => axiom-clean trivially.

================================================================================
2026-06-15 POSITIVE FEASIBILITY: the CANONICAL open core B=max_stack #bad IS within
the eps* budget at EVERY r (ratio 0.04-0.41) -- the census route's infeasibility is
PURELY the #bad<=#alignable loss; target #bad DIRECTLY (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the decisive follow-up to the census-infeasibility brick 5ac9fe4bc): I showed the census
surrogate K=#alignable EXCEEDS the weld budget 2^r*C(2^{mu-1},r) at the shallow/deepest bands (census
route DEAD). But the CANONICAL open core (OpenCoreConditionalPin.lean) is WorstCaseIncidenceBounded C
delta B = (forall stacks, #bad-gamma <= B), and the census bounds B only via the LOSSY #bad<=#alignable
(c.1007: up to 112x slack). UNMEASURED until now: is the TRUE core object B = max_stack #DISTINCT-bad-gamma
itself within budget, even where the surrogate K is not?

OBJECT (exact mod-p, PROPER mu_n m>1 never n=q-1, prize primes incl. non-Fermat; #bad = #distinct pinned
ratios -e0(T)/e1(T) over alignable a-sets, the genuine OpenCoreConditionalPin object NOT the alignable-set
count). m=1 prize shape k=r-1, binding band a_bind=r+1. Adversary = exhaustive char-lines (n=8) / strong
worst-line family (n=16). Probe probe_407_truecore_B_vs_budget.py (+ /tmp/truecore16.py focused n=16 run).

RESULT (B vs budget 2^r*C(2^{mu-1},r), p-INDEPENDENT across Fermat p=65537 AND non-Fermat p=262193):
  n=8  (exhaustive over ALL lines): r=2 B=5<=24, r=3 B=9<=32. FEASIBLE (ratio 0.21, 0.28).
  n=16: r=2 B=24<=112 (0.21) | r=3 24<=448 (0.05) | r=4 40<=1120 (0.04) | r=5 73<=1792 (0.04) |
        r=6 113<=1792 (0.06) | r=7 41<=1024 (0.04) | r=8 104<=256 (0.41). FEASIBLE at EVERY r.
  IDENTICAL at beta=4.0 and beta=4.5 (non-Fermat) => B is p-independent (char-0 structural).
CONTRAST with the census K (push 5ac9fe4bc): at the SAME r=2,3,4,8 where K>budget (1.4-2.6x DEAD),
the TRUE core B is 0.04-0.41x budget -- comfortably FEASIBLE. The gap K/B at the binding band is the
c.1007 lossiness (#alignable overcounts #bad by collapsing many a-subsets of ONE far-line locus onto one
gamma): at the hifreq line up to 112 alignable sets pin ONE bad gamma.

VERDICT (positive direction-setting, rule-6 honest -- NOT a CORE closure):
1. The deployed eps* budget 2^r*C(2^{mu-1},r) is NUMERICALLY SUFFICIENT for the CANONICAL open core
   WorstCaseIncidenceBounded at the binding window band, at EVERY proximity parameter r, with a WIDE
   margin (ratio <=0.41, mostly <=0.06). The pin's budget is NOT the obstruction; the open work is a
   PROOF that #bad <= 2^r*C(...), and the target is plausible (the realized worst-stack #bad sits far
   below it).
2. SHARPENS c.1007 quantitatively: the census route should be ABANDONED in favor of bounding #bad DIRECTLY
   (the lossy #bad<=#alignable step is the SOLE reason the census surrogate overflows). This converts
   c.1007's qualitative "target #bad directly" into a measured feasibility: #bad/budget <= 0.41 forall r.
3. HONEST: this is a NECESSARY-condition check (B fits the budget), NOT a proof that B<=budget holds at
   ALL n / the prize regime -- the SUP over stacks at n=16 uses a strong worst-line family + random (n=8
   exhaustive). A larger true B at unscanned stacks would only RAISE B; but the >2x headroom (ratio <=0.41)
   at the binding bands gives margin. The asymptotic #bad-vs-budget growth law (does ratio stay <1 as
   n->inf, the floor-vs-Johnson question, c.348 undecidable below n=256) is UNCHANGED -- this is a
   finite-n feasibility result, not the asymptotic bound. CORE not closed.
4. CONVERGENT: explains why per-line #bad COLLAPSES to O(1) at hifreq (95e633cb0) yet the route can still
   work -- the collapse is exactly what keeps B far below budget; the census surrogate's inflation was a
   red herring. The real open object is well-posed and budget-feasible; the prize is the PROOF, at the
   collective BGK depth, that this finite-n feasibility persists asymptotically.
Python-only, no Lean => axiom-clean trivially. probe_407_truecore_B_vs_budget.py.

================================================================================
2026-06-15 FLOOR-CONSISTENT on the CORRECT object: the canonical #bad / eps*-budget
ratio at the shallowest binding band is BOUNDED BELOW 1 (converging ~0.26), NOT
Johnson-tracking -- the first floor-consistent growth on #bad direct (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (capstone follow-up to the true-core feasibility brick ed1db3379): that brick showed B=max_stack
#bad <= eps*-budget 2^r*C(2^{mu-1},r) at finite n. The PRIZE content is the ASYMPTOTIC decider: does
ratio(n)=#bad/budget stay BOUNDED BELOW 1 (genuine FLOOR, prize-positive) or CREEP UP TO 1 (Johnson, the
fate of every SURROGATE: incidence I(n), e2=0 census K, even/odd moments). This is the FIRST growth
measurement on the CANONICAL OpenCoreConditionalPin object #bad itself (all prior floor-vs-Johnson probes
were on surrogates).

OBJECT (exact mod-p, PROPER mu_n, p~n^4, shallowest binding band r=2 -> k=1, a=3 where C(n,3) is brute-
feasible to n=64): #bad = #distinct pinned gamma, max over char-line adversary. Probe
probe_407_truecore_B_growth.py (dedicated fast pair-ratio routine reaching n=64).

RESULT (worst line consistently (4,2)):
  n= 8: #bad=5    budget=24    ratio=0.2083
  n=16: #bad=25   budget=112   ratio=0.2232
  n=32: #bad=113  budget=480   ratio=0.2354
  n=64: #bad=481  budget=1984  ratio=0.2424
Increments 0.0149, 0.0122, 0.0070 -- DECAYING (last ratio ~0.57) => geometric extrapolation to ~0.26,
BOUNDED WELL BELOW 1. The canonical #bad-to-budget ratio is CONVERGING below 1 = FLOOR-CONSISTENT.

VERDICT (rule-4; the FIRST floor-consistent (not Johnson) signal on the right object; rule-6 honest):
1. On the SURROGATE faces, every floor-vs-Johnson probe converged to Johnson (ratio -> 1 / super-budget).
   On the CANONICAL #bad object at the shallowest binding band, the ratio-to-budget converges to ~0.26
   -- bounded below 1, FLOOR-consistent. This is the qualitative difference between #bad (the real
   obligation) and the surrogates (#alignable, incidence, census, moments) that all over-shoot.
2. CONSEQUENCE: the deployed eps* budget 2^r*C(2^{mu-1},r) is not merely met finite-n (ed1db3379) -- its
   margin appears to PERSIST (ratio bounded ~0.26) at the shallowest band as n grows. If this floor
   persists across all r and to the prize regime, the canonical pin's budget is asymptotically sufficient
   for #bad -- exactly the prize-positive direction the surrogates falsely killed.
HONEST SCOPE (rule 6 -- NOT a closure): single SHALLOWEST band r=2 (computational reach; deepest band
r=2^{mu-1} is brute-infeasible past n=16); worst is a fixed LOW line (4,2); p-fixed (one prime per n);
n<=64. The full prize is forall-r and the asymptotic decider needs n>=256 (c.348: numerics cannot
separate floor from Johnson below 256). So this is a measured finite-n floor-CONSISTENT trend on the
correct object at one band -- it does NOT prove a floor (the deeper bands / larger n could differ), but
it is the first face whose #bad-to-budget ratio does NOT march to Johnson. The deep-band growth law +
the multi-band + larger-n confirmation are the open residual. CORE not closed, not faked. Python-only,
no Lean => axiom-clean trivially. probe_407_truecore_B_growth.py.

================================================================================
2026-06-15 The TRUE-CORE B (max_stack #distinct-bad-gamma) feasibility margin is
THICKNESS-INVARIANT -- B/budget identical thin vs thick => finite-n feasibility is
Johnson-margin, NOT thin-essential; thin content is purely in B's ASYMPTOTIC growth
(opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: complement to 0xSolace ed1db3379 (POSITIVE: B=max_stack #distinct-bad-gamma is WITHIN the eps*
budget at every finite r, ratio 0.04-0.41x, at beta=4.0/4.5 BOTH THIN). That probe did NOT test the
THICK regime. QUESTION (rule-3): is the B/budget feasibility margin THINNESS-ESSENTIAL (grows toward 1
as mu_n thickens => thin content) or thickness-invariant (Johnson-margin)?

METHOD: reused the sibling's EXACT engine (nbad_at_band, charline) VERBATIM; swept beta from THICK
(2.3, prize-FALSE) to THIN (5.0, prize-shape) at the SAME bands r=4 (census-overflow band) + r=8
(Johnson band). Exact mod-p, PROPER mu_16, never n=q-1. probe_407_truecore_B_thinness.py.

RESULT (exact):
  r=4: B=40 at EVERY beta (2.3,2.6,3.0,3.5,4.0,5.0), ratio=0.0357 IDENTICAL (bit-for-bit)
  r=8: B=104 at beta 2.3,3.0,3.5,4.0,5.0 (ratio 0.4062); 96 at beta=2.6 (sporadic structured-prime dip)
  => B at fixed (n,r) is THICKNESS-INVARIANT. The B/budget feasibility margin is identical in the thick
     prize-FALSE regime and the thin prize regime.

VERDICT (rule-3 FAIL on the feasibility-margin face): the sibling's positive "B within budget" result
is a THICKNESS-INVARIANT (Johnson-margin) feasibility, NOT a thin-specific signal. Finite-n B feasibility
holds identically in BOTH regimes => finite-n feasibility CANNOT distinguish thin from thick. The thin
content lives PURELY in the ASYMPTOTIC GROWTH RATE of B(n), NOT in finite B values or the budget ratio.
This SHARPENS ed1db3379: targeting #bad directly is right, but the feasibility is necessary-not-sufficient
(thin-blind at finite n); the prize is the GROWTH law of B (consistent with c.348: numerics can't decide
floor-vs-Johnson below n=256). RULE-6: does NOT close CORE, does NOT contradict ed1db3379 (B IS within
budget) -- it maps that the WITHIN-budget margin is thin-independent. Python-only exact => axiom-clean.

### The MONOMIAL far-line IS the worst-case stack at the BINDING band: generic + structured-low-degree stacks give #bad=0 there (2026-06-15, opus-4-8 subagent)

LANE (uncontested gap, exposed by reading B1IncidenceBridge.lean): the in-tree canonical core
WorstCaseFarIncidenceBounded quantifies #bad = #pinned-gamma over ALL far stacks (u0,u1); the bridge
epsMCA <= B/q needs B = max over ALL (u0,u1). But the ENTIRE board (incidence I(n), census K, #bad
collapse, wf-D1/D2/D5, n/4 law, "->Johnson") analyzes ONLY the MONOMIAL far-lines u0=x^A,u1=x^B and
ASSERTS they are the worst case. NO probe had TESTED whether a GENERIC (non-monomial) far stack yields
MORE bad-gamma. If generic #bad > monomial, the board's "->Johnson" UNDER-ESTIMATES the true B.

METHOD (exact mod-p, PROPER mu_n, prize prime p~n^4, NEVER n=q-1): #bad(u0,u1;a) via exact bordered
Vandermonde residuals (the in-tree `residual` det) + Aligned-subset semantics (mcaEvent_iff_aligned_subset):
gamma bad iff some a-subset S has all (k+1)-subtuples sharing gamma=-res0(T)/res1(T) with a non-degenerate
tuple. Compared MONOMIAL u0=x^A,u1=x^B vs RANDOM-GENERIC far stacks (u1 enforced FAR) AND STRUCTURED
low-degree-poly stacks, full band sweep a=k+1..n/2. n=16,k=3,hifreq[9,7]. probe_407_genericstack_vs_monomial_worst.py.

RESULT (exact, n=16 k=3 hifreq[9,7], p=65537):
| band a | #bad(monomial) | #bad(generic) max / nonzero-of-draws | regime |
|--------|----------------|--------------------------------------|--------|
| 4 (k+1)|  737           | max=1800, 8/8 nonzero (generic > mono)| SHALLOW non-binding |
| 5      |  1             | max=1,   2/8 nonzero                  | shallow |
| 6      |  1             | max=0, 0/20 nonzero                   | BINDING |
| 7      |  1             | max=0, 0/20 nonzero                   | BINDING |
| 8      |  1             | max=0, 0/20 nonzero                   | BINDING |
Structured low-degree-poly stacks (deg k..k+3, non-monomial) at a=6,7: ALSO #bad=0 (0/10 each).

VERDICT (rule-4 mapped; SUPPORTS the board's monomial-worst restriction at the binding radius, NOT a
CORE result): at the SHALLOW band a=k+1 every (k+1)-tuple is trivially singleton-aligned, so #bad merely
counts distinct residual-ratios -- large for ANY stack (generic 1800 > mono 737); that band sits FAR above
the prize floor and is NON-binding. At the DEEP BINDING bands (a>=6, where the floor lives) the monomial
far-line pins #bad to its binding value (1) while EVERY generic random AND structured-low-degree far stack
gives EXACTLY 0 (0/20 + 0/10 nonzero). => the MONOMIAL far-line IS the worst-case stack at the binding
radius; generic stacks do NOT threaten the canonical core B = max over ALL stacks there. This JUSTIFIES
(numerically, does not formally prove the WLOG) the board's universal restriction to monomial far-lines:
the "->Johnson" derived on monomials is NOT an under-estimate of the true B at the binding band. CORE not
closed, no overclaim. Python-only exact, no Lean => axiom-clean trivially. probe_407_genericstack_vs_monomial_worst.py.

================================================================================
2026-06-15 The moment-ratio STEP margin g(2)=(A_3/A_2)/((2r+1)n) SATURATES TO
EXACTLY 1 (geometric rho~1/2, L~1.0003): the r=2 step is asymptotically TIGHT, not
slack -- the surviving-lever margin closes to ZERO as n->inf (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the surviving thin-essential lever, sharpening the '⚠️ TEMPERING DATA' entry): the open core
reframes to the single moment-ratio STEP  A_{r+1}/A_r <= (2r+1)*n  at r*=round(log p) (★ SHARPENING).
The thin g(r*) stays <1 but INCREASES in n (0.366,0.468,0.530,0.643 at n=8,16,32,64); the TEMPERING entry
flagged that n<=64 CANNOT distinguish "saturates below 1" (provable) from "creeps to 1" (BGK-tight), and
the FFT engine STALLED at n=128 (size-p FFT at p~268M is O(p log p) with a prime-size penalty -> hours).

METHOD (the feasibility unlock -- NO size-p FFT): the moment ratio needs only the additive energy, via the
in-tree identity Sum_b |eta_b|^{2r} = p*E_r(mu_n) (SubgroupGaussSumMoment). A_r = E_r - n^{2r}/p
(DC-subtracted), E_r = #{(x_1..x_r),(y_1..y_r) in mu_n^{2r}: sum x = sum y} = r-fold additive energy,
computed EXACTLY by dense integer sumset convolution on the n-element subgroup (O(support*n), NO p-FFT).
=> n=128 (and the low-r rung) become EXACT-INTEGER feasible. PROPER thin mu_n (2-power, m=(p-1)/n>1, p~n^4,
NEVER n=q-1). probe_407_step_at_rstar_n128.py.

RESULT (EXACT integers, the r=2 step margin, thin beta=4):
| n   | E_2   | E_3      | A_3/A_2  | (2r+1)n=5n | g(2)=(A_3/A_2)/(5n) | increment |
|-----|-------|----------|----------|------------|---------------------|-----------|
|  32 | 2976  | 446720   | 149.81   | 160        | 0.9363              | --        |
|  64 | 12096 | 3750400  | 309.74   | 320        | 0.9679              | +0.0316   |
| 128 | 48768 | 30725120 | 629.70   | 640        | 0.9839              | +0.0160   |
The INCREMENT HALVES EXACTLY: +0.0316 -> +0.0160, ratio = 0.5063 ~ 1/2. (r=3 rung concordant: g(3) =
0.9063, 0.9527 at n=32,64, same upward.)

HONEST GEOMETRIC EXTRAPOLATION (rule-6, disciplined -- 3 exact points, geometric model g(2;2^k)=L-A*rho^k):
  rho = 0.5063,  remaining tail from n=128 = inc * rho/(1-rho) = 0.0164,  =>  L = g(2;n->inf) ~ 1.0003.
=> the r=2 step margin SATURATES TO EXACTLY 1 (the geometric series converges, ratio ~1/2, to L~1.00),
   NOT to a value strictly below 1.

VERDICT (rule-4 sharpening, rule-6 honest, NOT a closure, NOT a refutation): the moment-ratio STEP
A_{r+1}/A_r <= (2r+1)n -- the surviving thin-essential lever -- is, at the r=2 rung, ASYMPTOTICALLY TIGHT:
g(2) -> 1 from below with geometric ratio ~1/2 (margin closes to ZERO as n->inf), NOT bounded away from 1.
This RESOLVES the TEMPERING entry's open dichotomy at the r=2 rung in favor of "saturates AT 1" (the
boundary case): the step holds with STRICTLY POSITIVE margin at every FINITE n (0.9363..0.9839), but the
margin VANISHES asymptotically (A_3 = 5n*A_2 in the limit, an EQUALITY). CONSEQUENCE: a base-case +
single-step-monotonicity proof of A_r <= Wick CANNOT close on a UNIFORM positive step margin -- the step is
asymptotically an equality, exactly the BGK knife-edge. The thin advantage is real but RAZOR-THIN (the
increment-halving keeps g<1 at finite n yet L=1), which is the precise quantitative meaning of "BGK-tight"
the board kept circling. HONEST SCOPE: this is the r=2 rung (exact, extensible), NOT the deep r*~log p rung
(where A_{r+1}/A_r -> M^2 = the prize directly); the r=2 saturation-to-1 is a clean exact-integer
companion + sharpening of the FFT g(r*) trend, not a proof at r*. CORE not closed, no overclaim. The
exact-integer E_r unlock (no size-p FFT) is reusable for deeper-r / larger-n moment-step extension.
Python-only exact => axiom-clean trivially. probe_407_step_at_rstar_n128.py.

================================================================================
2026-06-15 EXACT CLOSED FORMS pin the r=2 moment-step saturation ANALYTICALLY:
E_2(mu_n)=3n(n-1), E_3(mu_n)=15n^3-45n^2+40n => g(2;n)=1-2/n+O(1/n^2) -> EXACTLY 1,
and the LEADING terms are NEGATION-CLOSURE-generic (thin advantage is a VANISHING
O(1/n) subleading correction, NOT leading-order) (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: upgrade the 3-point geometric fit (082400b56: g(2)->1, rho~1/2) to an ANALYTIC statement by pinning
the EXACT closed forms of E_2(mu_n), E_3(mu_n) (the only S-dependence of A_r). The clean rho~1/2 hinted a
doubling recursion. Exact integer additive energies, thin 2-power mu_n, n=8..128, p-INVARIANT (rule-6:
E_2,E_3 IDENTICAL across 3 prize primes each). probe_407_Er_closedform_thin.py.

EXACT CLOSED FORMS (fit on n=8,16,32 then VERIFIED EXACT on n=64,128 -- all 5 points exact):
    E_2(mu_n) = 3n^2 - 3n        = 3n(n-1)
    E_3(mu_n) = 15n^3 - 45n^2 + 40n = 5n(3n^2 - 9n + 8)
  (168,720,2976,12096,48768 and 5120,50560,446720,3750400,30725120 -- ALL match exactly.)
Doubling ratios converge: E_2(2n)/E_2(n) -> 4 (E_2 ~ 3n^2), E_3(2n)/E_3(n) -> 8 (E_3 ~ 15n^3).

ANALYTIC SATURATION (the upgrade from fit to fact): dropping the negligible DC term n^{2r}/p (p~n^4),
    g(2;n) = (A_3/A_2)/(5n) = (E_3/E_2)/(5n) = (15n^3-45n^2+40n)/((3n^2-3n)*5n)
           = (3n^2 - 9n + 8) / (3n(n-1)) = 1 - 2/n + 2/(3n^2) + O(1/n^3).
  => g(2;n) -> 1 EXACTLY (the leading coeffs CONSPIRE: E_3 lead 15, E_2 lead 3, ratio 5, /5n = 1).
  => the increment HALVES because the dominant term is -2/n (g(2n)-g(n) ~ +1/n, halving per doubling) =
     the rho~1/2 of the geometric fit is EXACTLY this -2/n asymptotics. The step A_3 <= 5n*A_2 holds with
     margin EXACTLY 2/n -> 0: an ANALYTIC asymptotic EQUALITY, not a fit. (Measured 0.9363/0.9679/0.9839
     match 1-2/n+... up to the tiny dropped DC term.)

RULE-3 (the HONEST thinness verdict -- where the thin content actually sits): the LEADING terms are
NEGATION-CLOSURE-GENERIC, NOT thin-specific:
    E_2(thin) == E_2(neg-closed-random) EXACTLY (168,720,2976; confirms 657e7139b).
    E_3(thin) ~ E_3(neg-closed-random) with a TINY, VANISHING gap: E3_thin/E3_neg = 0.9953, 0.9983, 0.9995
      at n=8,16,32 (thin slightly BELOW, gap shrinking 0.47%->0.17%->0.05% ~ O(1/n) -> 1).
  => the closed forms 3n(n-1), 15n^3-45n^2+40n are (to leading order) the additive energies of ANY
     neg-closed set, NOT a 2-power-subgroup signature. The thin-specific structure is ONLY a VANISHING
     O(1/n) SUBLEADING correction to E_3. This is WHY g(2) saturates to EXACTLY 1: the leading-order
     conspiracy E_3/E_2 -> 5n is a neg-closure fact, and the thin correction is too small to move the limit.

VERDICT (rule-4 sharpening, rule-3 HONEST, rule-6 no overclaim, NOT a closure): the r=2 moment-step
A_3 <= 5n*A_2 -- the surviving thin-essential lever -- saturates to an ANALYTIC asymptotic EQUALITY
g(2;n)=1-2/n+O(1/n^2), with the leading terms NEGATION-CLOSURE-GENERIC and the thin advantage confined to
a VANISHING O(1/n) subleading correction in E_3. This PROVES (closed-form, all-n-exact) that a base-case +
single-step monotonicity proof of A_r<=Wick CANNOT close at the r=2 rung on a uniform positive margin: the
margin is EXACTLY 2/n -> 0, and what little thin-specific content exists is subleading and vanishing. The
BGK knife-edge is now EXACT at r=2, not extrapolated. HONEST SCOPE: r=2 rung (the deep r*~log p rung, where
A_{r+1}/A_r -> M^2 = the prize, remains the open content -- the deep-r E_r closed forms are the natural next
target, the E_r unlock makes them computable). The closed forms E_2=3n(n-1), E_3=15n^3-45n^2+40n are clean
formalizable targets (exact rational arithmetic => axiom-clean trivially). probe_407_Er_closedform_thin.py.

## A_r<=Wick SURVIVES at the n=32 WORST in-window bad prime, but margin is KNIFE-EDGE (~0.93-0.97) + proxy fails 16x/octave (2026-06-15, opus-4-8 subagent)

LANE (uncontested): ec140aead pinned the worst-in-window-bad-prime r-trajectory at n=16 ONLY; 98db97afc did
n=32..256 A_r/Wick but at a GENERIC prime (Anom understated). Combined: worst-in-window-bad-prime x full-r-
trajectory x n=32. probe_407_anom_worst_rtraj_n32.py. Exact integer counts: E_r^(p) via r-fold mod-p
convolution + sum-of-squares; E_r^(0) via cyclotomic lattice Z^{n/2} convolution (zeta^{n/2}=-1). PROPER mu_n,
p>=n^4, NEVER n=q-1. SELF-CHECK n=16 reproduces ec140aead EXACTLY (p=76001, proxy 1.0914 @ r=6, A_r/Wick
0.9364->0.3743). ENGINE TRUSTED.

RESULT (n=32, worst bad prime p=1244993, beta=4.050, index m=38906, NOT n=q-1), r=2..6:
  A_r/Wick = 0.9685, 0.9383, 0.9264, 0.9361, 0.9591  (TARGET A_r<=Wick HOLDS, max 0.9685 at SHALLOW r=2)
  proxy Anom_r/(n^{2r}/p) = 0, 17.81, 13.57, 8.38, 5.12  (SUFFICIENT proxy FAILS HARD, peak 17.81 @ r=3)
  E0/Wick = 0.9688, 0.9089, 0.8255, 0.7258, 0.6175  (char-0 floor falls => Wick-E0 headroom grows, absorbs
    the failing proxy => A_r<=Wick survives via headroom-absorption, NOT via small Anom)
ADVERSARIAL RE-AUDIT (rule 6) top-4 worst bad primes p=1244993/1383169/1382177/1366721 (all proper mu_32,
m>>1): A_r<=Wick holds at ALL; max A_r/Wick=0.9685 each; 2 of 4 NON-MONOTONE (margin dips then RISES toward 1
at deep r), 2 of 4 monotone-decreasing.

VERDICT (mapped frontier, NOT a CORE result, no overclaim):
(1) The DC-subtracted carrier A_r<=Wick SURVIVES at the ADVERSARIAL n=32 prime (not just the generic prime of
    98db97afc) — POSITIVE for the anomaly route one octave deeper.
(2) The SUFFICIENT proxy Anom_r<=n^{2r}/p degrades ~16x/octave (peak 1.09 @ n=16 -> 17.81 @ n=32): DEAD as an
    asymptotic route; only direct A_r<=Wick survives, ENTIRELY via the growing Wick-E0 headroom.
(3) The n=32 worst-prime A_r/Wick does NOT collapse the way 98db97afc's GENERIC prime did (0.005-0.12 @ r*);
    at the WORST prime it is PINNED ~0.93-0.97 and turns BACK UP toward 1 on 2/4 primes. The "monotone
    collapse, no catch-up" reassurance is a GENERIC-prime artifact; the adversarial prime is a knife-edge just
    under 1 across accessible rungs — the BGK wall's shape.
HONEST: sub-prize p (~10^6; budget p~2^128), r capped at 6 (E0-ring), r*=14 not reached. Does NOT close CORE,
NOT refute the prize, NOT contradict 98db97afc. Pure-Python exact integer counts, no Lean => axiom-clean
trivially. probe_407_anom_worst_rtraj_n32.py.

================================================================================
2026-06-15 The E_r STRUCTURE is WICK-leading with a clean -C(r,2) subleading:
E_r(mu_n) = (2r-1)!![n^r - C(r,2)n^{r-1} + O(n^{r-2})] => the GENERAL moment-step
margin is g(r) = 1 - r/n + O(1/n^2) EXACTLY (the BGK knife-edge in closed form)
(opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: generalize the r=2 closed-form (5b0873ddb) to a GENERAL-r law by pinning the E_r structure. Exact
integer additive energies, thin 2-power mu_n, fit + EXACT-verify across n. probe_407_Er_closedform_thin.py.

EXACT CLOSED FORMS (each fit on a few n then VERIFIED EXACT on all probed n=8..128/64):
    E_1 = n
    E_2 = 3n^2 - 3n
    E_3 = 15n^3 - 45n^2 + 40n
    E_4 = 105n^4 - 630n^3 + 1435n^2 - 1155n
STRUCTURE (the clean pattern):
    LEADING coeff = (2r-1)!! = 1, 3, 15, 105  = the WICK / Gaussian moment.  (E_r/n^r -> (2r-1)!! as n->inf.)
    SUBLEADING/LEADING ratio = -C(r,2) = -1, -3, -6  for r=2,3,4.
    => E_r(mu_n) = (2r-1)!! [ n^r - C(r,2) n^{r-1} + O(n^{r-2}) ].

GENERAL-r STEP-MARGIN LAW (EXACT from the closed forms, derived for r=1,2,3; conjectured general):
    g(r) = (A_{r+1}/A_r)/((2r+1)n) = (E_{r+1}/E_r)/((2r+1)n)
         = 1 - r/n + O(1/n^2).
  EXACT instances:  r=1: g=(n-1)/n = 1-1/n.  r=2: (3n^2-9n+8)/(3n(n-1)) = 1-2/n+2/(3n^2).
                    r=3: (3n^3-18n^2+41n-33)/(n(3n^2-9n+8)) = 1-3/n+2/n^2.
  => the moment-step margin at depth r is EXACTLY r/n (to leading order): 1 - g(r) ~ r/n.

CONSEQUENCE (the BGK knife-edge, now in closed form): at the prize depth r* ~ log n,
    g(r*) ~ 1 - r*/n ~ 1 - (log n)/n -> 1   (margin VANISHES for any r = o(n)).
This is EXACTLY the measured FFT g(r*) trend (0.366,0.468,0.530,0.643 at n=8..64): the step holds with a
POSITIVE margin r/n at every finite n, but the margin -> 0 at the prize joint limit (r*~log n, n->inf).

RULE-3 (honest, where the thin content sits): the WICK leading term (2r-1)!! and the -C(r,2) subleading are
NEGATION-CLOSURE-GENERIC (E_2(thin)==E_2(neg-rand) EXACTLY; E_3(thin)/E_3(neg-rand) = 0.9953->0.9995 ->1,
the thin advantage is a VANISHING O(1/n) correction BELOW the subleading). So the g(r)=1-r/n law is largely
a neg-closure fact; the THIN-specific deviation is an even-higher-order vanishing correction. This is why
the Wick ratio E_r/((2r-1)!!n^r) is <1 but -> 1 BOTH as n grows (0.94->0.97 at r=2, n=16->32) AND deeper r
shrinks it faster (0.94,0.82,0.68,0.52 at r=2..5, n=16) -- the joint (r*,n) limit pushes it to 1.

VERDICT (rule-4 sharpening, rule-6 no overclaim, NOT a closure): the moment-step margin is EXACTLY r/n
(closed-form, all-n-exact for r<=3, structurally (2r-1)!!/-C(r,2)/Wick for r<=4). The surviving
thin-essential lever (the step A_{r+1}/A_r <= (2r+1)n) holds at EVERY finite (r,n) with margin r/n>0 but the
margin VANISHES at the prize depth r*~log n -- the BGK knife-edge, now characterized analytically rather than
numerically. The E_r are WICK-leading (A_r<=Wick is a LEADING-ORDER EQUALITY for thin mu_n); the thin prize
advantage lives ONLY in the rate the Wick ratio approaches 1 (a sub-subleading vanishing term). HONEST OPEN:
whether 1-g(r*) = r*/n + (higher terms) stays bounded BELOW the threshold at the JOINT (r*~log n, n->inf)
limit -- i.e. whether the accumulated O(1/n^2)+ corrections over r* steps rescue a positive margin -- is the
irreducible prize content; the leading r/n law does NOT resolve it (it -> 0, consistent with both
prize-true and BGK-tight). The closed forms E_r = (2r-1)!![n^r - C(r,2)n^{r-1}+...] are clean formalizable
targets (exact rational arithmetic => axiom-clean trivially). probe_407_Er_closedform_thin.py.

================================================================================
2026-06-15 The A_r/Wick PRIZE-RATIO profile CONFIRMS the r/n margin law on the
actual object: ratio RISES toward 1 as n grows at every fixed r (margin shrinks);
deep-r upturn at fixed p is a finite-field artifact (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: test the brick-4 closed-form verdict (g(r)=1-r/n, margin->0) DIRECTLY on the prize object
A_r/Wick_r = E_r/((2r-1)!! n^r) (sub-Gaussian iff <1). Exact integer E_r, thin 2-power mu_n n=16,32, deep
r. probe_407_ArWick_ratio_profile.py.

RESULT (exact A_r/Wick_r profile, thin beta=4):
  n=16 (r*=9): r=1..9 = 1.00, 0.9375, 0.8229, 0.6764, 0.5217, 0.3795, 0.2623, 0.1735, 0.1106
  n=32 (r*=7): r=1..7 = 1.00, 0.9688, 0.9089, 0.8314, 0.7554, 0.7112, 0.7440
KEY: at every fixed r the n=32 ratio EXCEEDS the n=16 ratio (r=2 0.94->0.97, r=3 0.82->0.91, r=4
0.68->0.83, r=5 0.52->0.76, r=6 0.38->0.71). The sub-Gaussian MARGIN (1-ratio) SHRINKS as n grows =>
A_r/Wick -> 1 (the Wick LEADING-ORDER equality), directly on the prize object -- same vanishing-margin
signal as the closed-form g(r)=1-r/n law (brick 4).

HONEST ARTIFACT (rule-6): the deep-r tail at FIXED p turns UP (n=32 r=7 ratio 0.744 > r=6 min 0.711).
This is a FINITE-FIELD DC/wraparound artifact: when r ~ log_n p the n^{2r}/p subtraction and field
wraparound contaminate E_r. Only the CLEAN rungs r << r* are trustworthy; the upturn is NOT a real
sub-Gaussian recovery. (The clean-rung trend -- ratio up toward 1 as n grows -- is the signal.)

VERDICT (rule-4 confirmation, rule-6 honest, NOT a closure): on the ACTUAL A_r<=Wick prize object the
sub-Gaussian margin (1 - A_r/Wick) shrinks toward 0 as n grows at every fixed r, confirming the closed-form
g(r)=1-r/n=margin-r/n verdict on the real object (not just the moment-step proxy). A_r<=Wick HOLDS with
positive margin at every accessible (r,n) but the margin VANISHES at the n->inf limit. The open prize
content is unchanged and precisely localized: whether the JOINT (r*~log n, n->inf) limit keeps the margin
bounded below the threshold (prize-true) or it -> 0 (BGK-tight) -- the clean-rung n=16,32 data shows the
margin shrinking but CANNOT reach r*~log n cleanly (finite-field artifact at deep r/fixed p). CORE not
closed, no overclaim. Python-only exact => axiom-clean trivially. probe_407_ArWick_ratio_profile.py.

## The base-case + single-step-MONOTONICITY route to A_r<=Wick is DEAD at n=64 -- monotonicity FAILS in the THIN prize regime (refutes the d6b438478 reframing) (2026-06-15, opus-4-8 subagent)

LANE (follow-up to caab0afb9): the n=32 worst-bad-prime work showed A_r<=Wick survives ONLY via the
Wick-E0 headroom (proxy Anom_r<=n^{2r}/p dead 16x/octave). Made the TRUE headroom test explicit and ran
the RACE across n. EXACT ALGEBRA: A_r = (E0 + Anom_r) - n^{2r}/p, so A_r<=Wick <=> Anom_r <= H_r where
H_r := (Wick - E0) + n^{2r}/p. Race ratio rho_r := Anom_r/H_r; carrier holds iff rho_r<=1.
probe_407_headroom_race.py + probe_407_n64_monotonicity_break.py. Exact integer counts (E0_ring VALIDATED
== closed form 3n(n-1) for n=8,16,32,64; Ep VALIDATED by independent O(n^2) brute pair-count at n=64).
PROPER mu_n, p>=n^4, NEVER n=q-1.

RESULT 1 -- the headroom race ratio EXPLODES toward 1 in n (peak rho_r over r=2..6, at each n's worst
in-window bad prime):
  n=8  (beta4.10): peak rho = 0.00000
  n=16 (beta4.05): peak rho = 0.03572
  n=32 (beta4.05): peak rho = 0.91208
  n=64 (beta4.01): rho > 1 at EVERY r (7.96, 8.93, 10.14 at r=2,3,4)  -> carrier A_r<=Wick FAILS at n=64.

RESULT 2 (the sharp refutation) -- at n=64, BOTH in-window bad primes (p=17318209 beta4.008 index270597;
p=19718977 beta4.039 index308109; both proper mu_64, NEVER n=q-1) have f(2)=A_2/Wick > 1 (1.1093, 1.0468).
Moreover f(r)=A_r/Wick is INCREASING from the base case at the worst prime:
  f(1)=1.00000 (base, = A_1/Wick = n/n, holds), f(2)=1.10930, f(3)=1.37464, f(4)=1.91127.
  => the single-step monotonicity f(2)<=f(1) is FALSE (1.109 > 1.000) IN THE THIN PRIZE REGIME at n=64.
VALIDATION: E_2^(p)=13632 confirmed by independent O(n^2) brute pair-count == convolution; A_2=13631.03 >
Wick_2=12288 exact.

CONSTRAINT LEMMA (rule-4): the d6b438478 reframing claimed a proof via [base case f(1)<=1, PROVEN] +
[single-step monotonicity f(r+1)<=f(r)] is AUTOMATICALLY thinness-essential because THICK violates both while
THIN satisfies them (validated n=16,32 where f IS decreasing). This is FALSE at n=64: the THIN prize-regime
worst bad prime ALSO violates single-step monotonicity (f increases 1.0->1.11->1.37->1.91) and f(2) already
exceeds 1. So the base+single-step-monotonicity STRATEGY does NOT close A_r<=Wick even in-regime; it dies at
the first step at n=64. The route is DEAD.

HONEST SCOPE (rule-6, NO overclaim): this refutes the PROOF STRATEGY (base+single-step monotonicity for
A_r<=Wick), NOT the prize. The prize is forall-field-universal at deep r~log q; per-prime A_r<=Wick at SMALL
r (r=2) is NOT the prize bound (M^4 <= p*A_2 gives only M <= (3p)^{1/4} sqrt(n), p-growing, far weaker than
the prize). What is killed: any closure of A_r<=Wick that relies on monotone descent from the r=1 base. The
DC-essential threshold q*(2r-1)!! < n^r does NOT fire here (5.2e7 >> 4096), so this is a SECOND, anomaly-
driven mechanism breaking A_r<=Wick at bad primes that the known threshold does not flag. Pure-Python exact
integer counts, no Lean => axiom-clean trivially. probe_407_headroom_race.py, probe_407_n64_monotonicity_break.py.

================================================================================
2026-06-15 RULE-3 on the E_r SUBLEADING coeff: the -C(r,2)(2r-1)!! subleading
(E_3's -45) is ALSO neg-closure-generic (thin~neg~thick) -- BOTH leading AND
subleading orders are thin-blind; the thin advantage is confined to the 3rd+
coefficients (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: brick 4 showed the LEADING (Wick (2r-1)!!) coeff of E_r is neg-closure-generic. This gates the
SUBLEADING coeff -(2r-1)!!*C(r,2) (E_3's -45 = -15*3): thin-essential or also generic? Thin 2-power mu_n
vs neg-closed-random (same size) vs thick composite subgroup, exact integer E_3, PROPER mu_n.
probe_407_Er_subleading_rule3.py.

RESULT (exact, sub-coeff = (E_3 - 15n^3)/n^2 -> -45 as n->inf):
  n=16: sub_thin=-42.50  sub_neg=-42.50  (identical)
  n=32: sub_thin=-43.75  sub_neg=-42.66  sub_thick(d=33,contaminated diff-size)
  n=64: sub_thin=-44.375 sub_neg=-43.657 sub_thick(d=70)=-44.43 (~thin)
=> sub_thin -> -45, sub_neg -> -45, sub_thick(matched) ~ -44.4 ~ thin. The SUBLEADING coeff is
   NEGATION-CLOSURE-GENERIC (thin ~ neg ~ thick, gap vanishing O(1/n) like the leading term).

VERDICT (rule-3 FAIL on the subleading, rule-6 honest, NOT a closure): BOTH the leading (Wick (2r-1)!!)
AND the subleading (-C(r,2)(2r-1)!!) coefficients of E_r(mu_n) are negation-closure-generic -- NOT
thin-2-power-specific. The thin prize advantage is therefore CONFINED to the THIRD-and-deeper coefficients
of E_r (the n^{r-2} term onward). This BOUNDS the thin content: the first two orders of the additive-energy
expansion carry no 2-power signature, so any thinness-essential mechanism must extract its gain from the
sub-subleading structure (exactly the term whose accumulated effect over r* steps is the open prize
question). Tightens the brick-4 picture: g(r)=1-r/n is built from two neg-closure-generic orders; the thin
deviation is below O(1/n^2) in the per-step margin. CORE not closed, no overclaim. Python-only exact =>
axiom-clean trivially. probe_407_Er_subleading_rule3.py.

================================================================================
2026-06-15 The ACCUMULATED 2nd-ORDER correction to the Wick ratio is NEGATIVE and
ASYMPTOTICALLY SUBDOMINANT => the "2nd-order rescues a positive prize margin"
hypothesis is REFUTED at the joint limit r*~log n (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (flagged-open, uncontested): the HONEST OPEN residual of the E_r closed-form bricks
(44234dc3d/5b0873ddb): "whether 1-g(r*) = r*/n + (accumulated O(1/n^2) corrections over r*
steps) stays BOUNDED BELOW threshold at the JOINT (r*~log n, n->inf) limit -- the leading r/n
law -> 0 (consistent with BOTH prize-true AND BGK-tight)." Resolved the 2nd-order rung.

ENGINE: in-tree cyclotomic-lattice E_r^(0) (zeta^{n/2}=-1, n=2^a) = EXACT char-0 negation-closure
additive energy, p-FREE. = A_r/Wick to O(n^{2r}/p)=O(1/n^{2r}) (DC term negligible at p~n^4).
Cross-verified bit-for-bit vs board E_4 closed form 105n^4-630n^3+1435n^2-1155n at n=8..64.
probe_407_Er_thirdcoeff_accumulated.py.

RESULT 1 -- THIRD coeff (n^{r-2}) of E_r pinned (was the open carrier of O(1/n^2)):
  E_2 third/lead = 0,  E_3 third/lead = 8/3,  E_4 third/lead = 41/3.
  (lead=(2r-1)!!, sub/lead=-C(r,2) reconfirmed; E_3=15n^3-45n^2+40n, E_4 board cf re-verified.)

RESULT 2 -- ACCUMULATED 2nd-order law (EXACT, the load-bearing brick):
  W(r) := E_r^(0)/((2r-1)!! n^r) = prod_{s<r} g(s)  (Wick ratio = product of step margins).
  log W(r) = -r(r-1)/(2n) + c2(r)/n^2 + O(r/n^3),  with EXACT CLOSED FORM
        c2(r) = -r(r-1)(2r+5)/36.
  c2(r): -1/2,-11/6,-13/3,-25/3,-85/6 at r=2..6. c2 is the FULL accumulated 2nd-order coeff
  INCLUDING the -x^2/2 Jensen term of log(1-x) (an earlier naive "-sum c2(step)" mis-signed it;
  the corrected c2(r) MATCHES the exact integer W(r) at n=8,16,32 to the c3/n drift -- verified).

RESULT 3 -- VERDICT (rule-4 wall map, rule-6 honest, NOT a closure):
  At the prize joint limit r*~c*log n:
    leading |term1| = r*(r*-1)/(2n) ~ (c log n)^2/(2n) -> 0.
    2nd-ord |term2| = |c2(r*)|/n^2 ~ (r*)^3/(18 n^2) ~ (c log n)^3/(18 n^2) -> 0  (extra 1/n).
    term2/term1 ~ (c log n)/(9n) -> 0.
  => BOTH terms -> 0; log W(r*) -> 0; W(r*) -> 1 (A_r=Wick in the limit, the BGK knife-edge).
  => The 2nd-order accumulated correction is NEGATIVE (DEEPENS cancellation at finite n) AND
     asymptotically SUBDOMINANT => it does NOT keep W(r*) bounded away from 1.
  => The "the accumulated O(1/n^2) correction over r* steps rescues a positive prize margin"
     hypothesis is REFUTED at the joint limit. Consistent with BGK-tight, NOT prize-positive.
     The thin advantage (known O(1/n) subleading in E_r) is NOT resurrected at 2nd order in the
     accumulated Wick ratio.
  HONEST: r* capped at lattice-tractable r<=6; the c2(r)=-r(r-1)(2r+5)/36 closed form is EXACT
  (cubic, 4 anchor pts r=1..4) and its r^3 growth (vs leading r^2/n) is what drives the verdict.
  Does NOT close CORE; SHARPENS the 44234dc3d open residual one order: the irreducible prize
  content is NOT carried by the 2nd-order accumulation -- it must live in a NON-perturbative
  (all-order / r*-resummed) effect, since every fixed perturbative order in 1/n vanishes at the
  joint limit. Pure-Python exact integer counts + Vandermonde over Q, no Lean => axiom-clean
  trivially. probe_407_Er_thirdcoeff_accumulated.py.

## UNIFIED open inequality A_r<=Wick <=> Anom_r <= (r/n)*Wick: the bad-prime anomaly OUTGROWS 0xSolace's r/n char-0 margin ~18x/octave (kappa: 0.04 -> 1.53 -> 27.8 for n=16,32,64) (2026-06-15, opus-4-8 subagent)

LANE: synthesize 0xSolace's exact general-r closed form E_r^(0)/Wick = 1 - r/n + O(1/n^2) (push 44234dc3d,
2034615dc) with my bad-prime anomaly growth (caab0afb9, 219f17c7a). Since A_r/Wick = E0/Wick + Anom_r/Wick
- n^{2r}/(p Wick) and E0/Wick = 1 - r/n + O(1/n^2), to LEADING ORDER:
    A_r <= Wick  <=>  Anom_r <= (r/n)*Wick + n^{2r}/p.
Define kappa_r := Anom_r / ((r/n)*Wick). Carrier (leading order) holds iff kappa_r <= ~1. This is the
SHARPEST reformulation: prize <=> the bad-prime anomaly stays within the r/n char-0 margin.
probe_407_anom_vs_rn_headroom.py. Exact integer counts (E0_ring==3n(n-1) validated; Ep brute-validated at
n=64). PROPER mu_n, p>=n^4, NEVER n=q-1.

RESULT -- peak kappa_r (over r=2..5) at each n's worst in-window bad prime:
  n=16 (beta4.053, p=76001):    peak kappa = 0.04063 @ r=5
  n=32 (beta4.050, p=1244993):  peak kappa = 1.52879 @ r=5
  n=64 (beta4.008, p=17318209): peak kappa = 27.83765 @ r=5
The anomaly outgrows the r/n char-0 margin ~18x/octave. kappa crosses 1 between n=16 and n=32.

INTERPRETATION (rule-6, honest): the leading-order budget kappa<=1 is EXCEEDED at n=32 (kappa=1.53) yet the
EXACT A_r/Wick=0.936<1 still holds at n=32 -- because the O(1/n^2) corrections in E0/Wick (=0.726 at n=32 r=5,
below 1-r/n=0.844) and the DC term provide extra sub-leading headroom that the leading-order (r/n)Wick test
ignores. At n=64 BOTH the leading-order budget AND the exact A_r/Wick fail (kappa=27.8, A_r/Wick=2.96 @ r=5).
So: 0xSolace's g(r)=1-r/n is the GOOD-PRIME (char-0) margin; kappa measures how badly the bad-prime anomaly
eats it. The margin is eaten ~18x/octave and the carrier A_r<=Wick (on the EXACT object, not leading-order)
survives at n=32 only on the sub-leading O(1/n^2)+DC crumbs, and FAILS at n=64.

HONEST SCOPE: refutes the leading-order r/n-margin SUFFICIENCY (kappa<=1) at n>=32 and the exact A_r<=Wick at
n=64 at these bad primes -- NOT the prize (forall-field, deep r~log q; small-r per-prime A_r<=Wick is not the
prize bound, M^4<=p A_2 -> M<=(3p)^{1/4}sqrt(n)). Maps EXACTLY how the char-0 r/n margin and the bad-prime
anomaly race: the anomaly wins ~18x/octave. Pure-Python exact, no Lean => axiom-clean trivially.
probe_407_anom_vs_rn_headroom.py.

================================================================================
2026-06-15 The RESUMMED Wick ratio W(r*) -> 1 on EVERY polynomial-log joint
diagonal r*=a*log2 n in the prize regime r*<<n => BGK-tight confirmed
non-perturbatively; W-bounded-below-1 only at r~n (NOT prize) (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (follow-up to f5ec4a9cf): that brick showed every FIXED 1/n order of log W(r) vanishes at the
joint limit; the open residual was the RESUMMED W(r*) along the TRUE diagonal r*~log n. This resums it.

ENGINE: exact char-0 W(r;n)=E_r^(0)/((2r-1)!! n^r) (lattice seed n=8,16,32 r<=6) + the EXACT 2-term
asymptotic log W(r)=-r(r-1)/2n - r(r-1)(2r+5)/(36 n^2)+O(r/n^3) (from f5ec4a9cf).
VALIDITY (rule-6): 2-term model accurate to <0.1% for r/n<~0.15, degrades as r/n->1 (n=8 r=6, r/n=0.75:
6.4% err). The PRIZE regime is r*~log n << n => r*/n->0 => model VALID there.

RESULT: along EVERY polynomial-log diagonal r*=a*log2 n (a=1,1.5,2, and prize a=4ln2~2.77),
W(r*;n) -> 1 as n->inf (1-W -> 0). Sample (a=1): W~0.676,0.788,0.896,0.957,0.984,0.994 at n=16..16384.
EXACT corroboration (NO model) along r*=log2 n: W = 0.667,0.676,0.726 at n=8,16,32 (RISING to 1).

VERDICT (rule-4 wall map, rule-6 honest, NOT a closure): the resummed Wick ratio SATURATES to 1 on
every log-depth diagonal in the regime r*<<n where the resummation is provably accurate = the prize
regime. CONFIRMS BGK-tightness NON-perturbatively in the accessible regime (sharpens the perturbative
f5ec4a9cf verdict: not just each order vanishes, the RESUMMED diagonal -> 1). The ONLY regime where W
stays bounded below 1 is r ~ n (a constant fraction of the full group) -- which is NOT the prize regime.
=> CORE not closed; the irreducible W-bounded-below-1 content is localized OUTSIDE the prize-relevant
depth r*~log n. Python-only exact + validated asymptotic => axiom-clean trivially.
probe_407_W_joint_diagonal_resummation.py.

## The E_r(mu_n) closed-form lane's p-INVARIANCE assumption FIRST FAILS at r=4 (structured-prime additive anomaly); thickness-generic, NOT thin-essential (2026-06-15, opus-4-8 subagent)

LANE (uncontested): the dominant live lane (44234dc3d/5b0873ddb) pins E_2=3n(n-1), E_3=15n^3-45n^2+40n,
E_4=105n^4-630n^3+1435n^2-1155n and "g(r)=1-r/n" -- treating E_r as a p-INVARIANT polynomial in n. Nobody
had STRESS-TESTED that p-invariance across primes. probe_407_Er_pdependence_onset_r4.py. Exact integer
r-fold additive convolution, PROPER mu_n, p>=n^4, NEVER n=q-1.

CONTRIBUTION 1 (closed-form-INDEPENDENT algebraic reduction): the accumulated moment-step product
TELESCOPES to a SINGLE object. With E_0:=1,
    prod_{r=1}^{R-1} g(r) = prod_{r=1}^{R-1} (E_{r+1}/E_r)/((2r+1)n)
                          = (E_R/E_1)/(n^{R-1} prod_{r=1}^{R-1}(2r+1))
                          = E_R/(n^R (2R-1)!!)  =:  W_R   (the WICK RATIO of E_R).
So the whole multi-step "step-tower" question (DISPROOF_LOG: does the accumulated O(1/n^2) rescue a
positive margin?) reduces EXACTLY to ONE monotone quantity: does the Wick ratio W_{r*} (R=r*~log n) stay
bounded BELOW 1 with margin, or -> 1? From the EXACT (p-invariant) E_2,E_3: log W_R = -R(R-1)/(2n) +
B_R/n^2 + O(1/n^3), A_R=R(R-1)/2 EXACT, B_2=-1/2, B_3=-11/6 (TIGHTENING at the accessible rungs). At
R=r*~log n BOTH -R^2/(2n) and B_R/n^2 -> 0 (r*=o(sqrt n)) => W_{r*} -> 1 REGARDLESS of the B_R sign. The
accumulated tower CANNOT keep the Wick ratio bounded below 1 at the prize joint limit -- the BGK knife-edge
in closed form, reduced to a single object.

CONTRIBUTION 2 (rule-6 stress test, the new structural brick): E_r p-INVARIANCE is NOT universal.
  - E_2, E_3: p-INVARIANT (truly polynomial) -- identical across ALL probed prize primes. CONFIRMED.
  - E_4: the published 105n^4-630n^3+1435n^2-1155n is CORRECT for GENERIC primes (excess=0 for the vast
    majority of near-primes). But a SPARSE STRUCTURED subset shows a FIXED POSITIVE excess:
        n=16: ONLY the Fermat prime p=65537=2^16+1 -> E_4=4654160 = generic + 4480 (+0.096%); 4 other
              near-primes (65617,65633,65713,65729) -> excess EXACTLY 0.
        n=32: p=1048609 AND p=1049281 -> generic + 645120 (+0.710%); 3 other near-primes -> 0.
    p-invariance VERIFIED bit-identical at a 2nd prize prime for E_2,E_3 at every n; E_4 differs across
    primes at the SAME n (n=128: p=268437889 -> 27126574720 vs p=1150808833 -> 26931748480). => the
    additive-anomaly (p-dependence) of E_r ONSETS exactly at r=4, invisible to the r<=3 closed forms the
    whole lane is built on.

RULE-3 (the thinness verdict -- thickness-GENERIC, joins the board meta-pattern): swept beta THICK
(2.3-3.2, prize-FALSE) -> THIN (4-5), prize prime = closest to n^beta, n=16,32. The E_4 p-excess is
LARGEST in the THICK regime and SHRINKS to ZERO as beta->thin:
    n=16: beta2.3 +90.9% -> beta3.0 +3.95% -> beta4.0 +0.096% (Fermat only) -> beta>=4.5 EXACTLY 0.
    n=32: beta2.3 +357% -> beta3.0 +18.7% -> beta4.0 +0.71% -> beta>=4.5 EXACTLY 0.
=> the E_4 additive anomaly is a SMALL-q (thick) / 2-adic-special-prime effect that VANISHES in the deep
thin prize regime. At the genuine prize regime (beta>=4.5) the generic polynomial is RECOVERED exactly =>
the closed-form lane's p-invariance assumption is SAFE deep in the thin regime, and the anomaly is NOT a
thin-essential carrier (it's anti-thin: maximal in the prize-FALSE thick window).

VERDICT (rule-4 sharpening, rule-6 honest, NOT a closure): (1) the accumulated step-tower reduces EXACTLY
to the single Wick ratio W_{r*}, whose log -> 0 at the prize joint limit regardless of the 2nd-order sign
-- the knife-edge in closed form, one clean object. (2) The E_r-closed-form lane's p-invariance holds for
r<=3 universally and r=4 generically, but FAILS at sparse structured (Fermat-type) prize primes starting
at r=4, where E_4 EXCEEDS the generic polynomial (less Wick headroom) -- but this excess is THICKNESS-
GENERIC (maximal in the prize-FALSE thick regime, ->0 in the thin limit), so it cannot be the thin prize
carrier and the generic closed form is recovered deep in the thin regime. CORE not closed, not refuted.
Pure-Python exact integer counts, no Lean => axiom-clean trivially.
probe_407_Er_pdependence_onset_r4.py.

## The thin Wick-deficit (1-W_r) is SUB-leading in r: D_r=(1-W_r)*n falls BELOW the leading r(r-1)/2 and the gap WIDENS with r => NO compounding deep-r thin advantage (BGK-tight direction). Exact char-0, control-free (2026-06-15, opus-4-8 subagent)

LANE (uncontested, CHAR-0, control-free; distinct from the live mod-p anomaly-predictor + deep-hole
workers): the DISPROOF_LOG residual asked whether, as the moment ORDER r grows toward prize depth
r*~log n, the thin advantage GROWS (compounding -> could survive the joint limit) or stays tied to the
leading knife-edge. The prior thin-vs-neg-random measurement was r=3 ONLY. probe_407_Wickratio_rtrend_exact.py.

OBJECT (fully EXACT, NO stochastic control, NO prime): the Wick ratio W_r = E_r^(0)(mu_n)/((2r-1)!! n^r)
(= the accumulated moment-step product, push 58f29f3f0). Gaussian/random model: W_r=1. Thin subgroup:
W_r<1, deficit (1-W_r) = thin advantage. E_r^(0) via exact char-0 cyclotomic-lattice r-fold convolution
(mu_n = n-th roots of unity in Z^{n/2}, n=2^a, zeta^{n/2}=-1). Define the rescaled deficit D_r=(1-W_r)*n.
Leading expansion log W_R=-R(R-1)/(2n)+.. => D_r ~ r(r-1)/2. QUESTION: does the EXACT D_r EXCEED r(r-1)/2
by a WIDENING margin (extra compounding thin advantage) or fall at/below it (knife-edge dominates)?

RESULT (exact, r=2..8/7/6, n=8..64): D_r is consistently BELOW r(r-1)/2 and the gap WIDENS with r:
  n=32: D_r/[r(r-1)/2] = 1.000, 0.972, 0.931, 0.878, 0.816  (r=2..6) -- MONOTONE DECREASING
  n=16: D_r/[r(r-1)/2] = 1.000, 0.944, 0.865, 0.770, 0.669, 0.571 (r=2..7) -- MONOTONE DECREASING
  n=8:  D_r-lead = 0, -0.33, -1.54, -4.05, -8.05, -13.48, -20.20 (r=2..8) -- gap grows fast
  n=64: D_r/[r(r-1)/2] = 1.000, 0.986, 0.965 (r=2..4) -- same downward trend.
  (W_r exact: n=32 -> 0.9688, 0.9089, 0.8255, 0.7258, 0.6175 at r=2..6, matching 98db97afc/caab0afb9.)

VERDICT (rule-4 constraint, rule-6 honest, NOT a closure): the exact thin Wick-deficit is SUB-LEADING --
(1-W_r) is SMALLER than the leading r(r-1)/(2n) prediction, and the shortfall GROWS with r. Equivalently
W_r approaches 1 FASTER than the leading knife-edge 1-r(r-1)/2n, so the subleading correction is
+LOOSENING (toward the Gaussian W_r=1), NOT a compounding thin advantage. => the surviving thin lever
(the moment-step / Wick-ratio route) does NOT gain EXTRA room at deep r; the deep-r structure is the
BGK-tight direction. This CLOSES the "deep-r compounding thin advantage rescues the moment route" hope:
the accumulated product W_{r*} (= prod g) is NOT held below 1 by a growing deep-r deficit -- the deficit
is sub-leading and its rescaled form D_r/[r(r-1)/2] -> below 1 and falling. The moment/Wick-ratio route is
the knife-edge or worse at every accessible r, consistent with the whole board. Pure-Python EXACT char-0
integer cyclotomic-lattice convolution, no control, no prime, no Lean => axiom-clean trivially. CORE not
closed, not refuted. probe_407_Wickratio_rtrend_exact.py.

================================================================================
PHASE-ALIGNMENT TOWER lane: the "cos@b*=1.0000 tower-recursive" descent-handle
premise is REFUTED -- it is antipodal symmetry (-1 in mu_n), a SIGN not a phase.
(push b3ad58f20, receipt #444 ic-4705287464, probe_407_phase_alignment_is_antipodal_symmetry.py)

CONSTRAINT LEMMA (rule-4): For n even, -1 = h^{n/2} in mu_n, so mu_n is closed
under x -> -x. Hence S_b = sum_{x in mu_n} e_p(bx) is REAL for EVERY frequency b
(antipodal pairing). mu_{n/2} also contains -1, so each half-coset sum S_0, S_1 is
real too => cos(S_0, S_1) in {+1, -1} ALWAYS. The observed "cos=1.0000" at the worst
frequency b* is therefore a SIGN (both real halves same sign), not a hidden phase
alignment, and "same sign at b*" is tautologically WHY b* is the argmax (constructive
real addition). => the phase-alignment tower is NOT a non-average descent/Stepanov
handle; any proof attempt that leans on "exact phase alignment at b*" as structure is
leaning on antipodal symmetry, which moment/average methods already see (S_b real =>
the cancellation problem is purely in the SIGN PATTERN of {S_b}_b, no phase content).
Confirmed exact: Im(S_0 conj S_1) = O(1e-15) machine zero at n=8,16,32, p~n^4.

SECONDARY (false-alarm growth corrected): in the prize regime p~n^4, |S_b*|/sqrt(n)
grows ~ sqrt(log n) (ratio/log2 n flattens 0.89->0.80 at n=8,16,32,64; ratio/sqrt(log2 n)
turns over at n=64) = INSIDE the prize-allowed C*sqrt(log(p/n)) envelope. An earlier
faster-than-sqrt-log read was a finite-size artifact. No prize-tension at accessible n.

Does NOT close/refute CORE. Removes one hoped-for mechanism + one false-alarm read.

================================================================================
2026-06-15 The bad-prime ANOMALY Anom_r is prime-selective + QUANTIZED, and its
ONSET DEPTH r0(n) DECREASES with n (4->4->3 over n=16,32,64), descending toward
the prize rung r=2 (but r0>2 at n<=64 => prize rung still anomaly-clean) (opus-4-8)
--------------------------------------------------------------------------------
LANE (follow-up to sibling 1c48ff7cd + my 41980aa29): those leave the prize ENTIRELY in the bad-prime
anomaly Anom_r=E_r^(p)-E_r^(0). No worker pinned the ANOMALY's onset structure. Did it.
ENGINE: exact integer Ep (mod-p r-fold conv) + E0_ring (char-0 cyclotomic lattice), reused from
probe_407_anom_worst_rtraj_n32.py. proper mu_n, in-window beta~4 primes, never n=q-1.
probe_407_anomaly_onset_depth.py.

FACT 1 -- the anomaly is PRIME-SELECTIVE + QUANTIZED (not a smooth n^{2r}/p law):
  At a GENERIC in-window prime Anom_r=0. n=16 r=4: only 1/30 nonzero (the Fermat prime 65537).
  Fraction nonzero GROWS with n (n=16:3%, n=32:65% at r=4). At n=32 r=4 every nonzero Anom_4 is an
  integer multiple of GCD=53760=2^9*3*5*7, multipliers {2,3,4,6,9,10,12,14,18,24,28,30} (discrete ladder).

FACT 2 -- ANOMALY ONSET DEPTH r0(n)=smallest r with some in-window Anom_r>0:
    n=8: r0>6 (no anomaly in window)   n=16: r0=4   n=32: r0=4   n=64: r0=3.
  r0(n) DECREASES with n -- the bad-prime anomaly onsets at SHALLOWER moment-depth as n grows,
  descending toward the prize rung r=2 (where M^4<=p*A_2 defines the prize).

VERDICT (rule-4 wall map, rule-6 honest, NOT a closure/refutation):
  - The NEG-CLOSURE-GENERIC part E_r^(0)/Wick is thin-blind + saturates to 1 (my 41980aa29).
  - The PRIZE-CARRYING part is Anom_r: 0 at shallow r<r0, onsets at r0(n) DECREASING in n.
  - At n<=64, r0>=3>2, so the r=2 PRIZE RUNG is STILL anomaly-free in-window => the worst in-window
    prime does NOT yet crack A_2<=Wick at the prize rung at these n. OPEN: does r0(n)->2 (anomaly
    reaches the prize rung, candidate crack) or plateau at r0>=3 (prize rung stays clean)?
  - Does NOT close/refute CORE; MAPS the precise depth-of-entry of the bad-prime anomaly and that it
    descends with n. Pure-Python exact integer counts, no Lean => axiom-clean trivially.
    probe_407_anomaly_onset_depth.py.

## Wick best-case capability map: M <= sqrt(n)((2r-1)!!)^{1/2r} at r*~log m lands EXACTLY on the prize form sqrt(2/e) sqrt(n log m) (C~0.858 absolute) => the Wick VALUE is NOT a barrier; prize <=> A_{r*}<=Wick at r*~log m (2026-06-15, opus-4-8 subagent)

LANE (uncontested, analytic+numeric): having reduced the moment route to the Wick ratio W_r (58f29f3f0)
and shown its deficit sub-leading => W_{r*}->1 (b97f5a972), the BEST the moment route can give is A_r=Wick=
(2r-1)!! n^r exactly (W_r=1). Open: even in that best case, what sup bound does it give at r*~log m, and
does it reach the prize or does the Wick value itself encode a barrier? probe_407_wickbound_capability.py.

DERIVATION: single-freq M^{2r} <= A_r => M <= (A_r)^{1/2r}. Best case A_r=Wick:
    M <= sqrt(n) * ((2r-1)!!)^{1/2r}.
((2r-1)!!)^{1/2r} ~ sqrt(2r/e) (Stirling, VERIFIED: f(r)/sqrt(2r/e) = 1.166,1.085,1.043,1.022,1.011 ->1 at
r=1,2,4,8,16). The single-frequency-dominates-the-2r-th-moment step needs r ~ log(#freqs)=log m, so the
prize depth is r*~log m. Then M <= sqrt(n) sqrt(2 r*/e) ~ sqrt(2/e) sqrt(n log m) = THE PRIZE FORM.

NUMERIC (r*=round(log m), m=n^{beta-1}): C_eff = M_wick/sqrt(n log m) -> sqrt(2/e)=0.858 EXACTLY, CONSTANT
across n=2^8..2^24, beta=4/4.5 (C_eff = 0.876,0.865,0.859,0.866,0.862 at n=2^8..2^24 beta4; ->0.858).
M_wick << SOTA n^0.989 << trivial n at every scale (n=2^16: M_wick~1.27e3 vs SOTA 5.8e4 vs trivial 6.55e4).

VERDICT (capability map + constant pin, rule-6 NOT a closure): (1) the Wick VALUE does NOT encode a
barrier -- the moment route is prize-CAPABLE; the Wick best case lands on sqrt(2/e) sqrt(n log m), the prize
form with absolute C~0.858. (2) the prize is EXACTLY EQUIVALENT to A_{r*} <= (2r*-1)!! n^{r*} at r*~log m
(with the single-freq-dominates justification). This re-localizes ALL difficulty to the DEEP rung r*~log m
(e.g. r*~14 at n=2^16/beta4) -- NOT the shallow r<=6 we compute exactly (W_r<1 sub-leading, b97f5a972).
The accessible-r data is CONSISTENT with both A_{r*}<=Wick (prize) and A_{r*}>Wick (BGK-tight) and does NOT
extrapolate (the deficit is sub-leading + vanishing). HONEST: no new bound proven; this PINS the prize-
equivalent target + its absolute constant sqrt(2/e) + confirms moment-route capability. Numeric + exact
Stirling, no Lean => axiom-clean trivially. CORE not closed, not refuted. probe_407_wickbound_capability.py.

## Route 36 deep-hole-RESTRICTED sup #bad-gamma is FIELD-SATURATED + thickness-invariant (rule-3 FAIL) -- the explicit open step CLOSED as thin-blind (2026-06-15, opus-4-8 subagent)

LANE (uncontested): route 36 (push 1b3f947fa) reduced the L7 open core sup over stacks to the FINITE
deep-hole family x^j, j==k mod 4, and its EXPLICIT next-open-step was "bound #bad-gamma over the deep-hole
family directly; whether the deep-hole-restricted sup beats Johnson is the live question." No live worker
on it (worker was on anom_worst_rtraj). probe_407_deephole_restricted_sup_growth.py, exact mod p,
PROPER mu_n (NEVER n=q-1), fast #bad(smin=k+1)=#distinct over-det gammas (validated == route-36 #bad=40).

RESULT (k=3):
- GROWTH thin beta=4: deep-hole-sup = 40 (n=8), 1552 (n=16).
- THINNESS GATE n=16 (thick prize-FALSE beta=2.4-3.2 vs thin): 752,1248,1440,1552,1552 -- LOOKS thin-
  favoring (larger in thin), BUT:
- FIELD-SIZE GATING (decisive rule-6 control): fixed n=16, sweep prime index m=(p-1)/n:
    p~n^1:16, n^2:256, n^2.5:976, n^3.25:1456, n^4:1552, n^5:1552 (SATURATED, p-independent past p>>n^2).
  => the deep-hole-sup is a p-INDEPENDENT SATURATED cyclotomic constant; the (B) thin 'advantage' is PURE
     field-size saturation (thick-window small fields can't fit the full incidence count), NOT thinness-
     essential. The thin value IS the large-field saturated value.
- Fermat audit: p=65537 (1552) == non-Fermat near-primes (1536-1552) -> NOT a Fermat artifact (robust,
  unlike the E_r r=4 anomaly which was Fermat/thick-special).

VERDICT (rule-4 wall, rule-3 FAIL, rule-6 honest, NOT a closure): route 36's deep-hole-restricted sup is
THICKNESS-INVARIANT + FIELD-SATURATED -- it joins the board meta-pattern (every per-direction/per-family
finite-n object is thickness-invariant + Johnson-tracking). The deep-hole RESTRICTION does NOT escape the
wall; its sup is the same large-field saturated value the full far-line incidence gives, the thick
difference being pure small-field suppression. CLOSES the route-36 explicit open step as a thin-blind,
field-saturated object. Python-only exact => axiom-clean trivially.
probe_407_deephole_restricted_sup_growth.py.

================================================================================
2026-06-15 The r=2 PRIZE RUNG is ANOMALY-FREE at every in-window prize prime
(n=16..256) => A_2 char-0-fixed; its L4 ceiling (pA2)^{1/4}~n^{1.5} >> prize
sqrt(n log) => moment-method walled from BOTH ends (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: settled the r0(n)->2 dichotomy from 231caf44f (does the anomaly reach the prize rung r=2?).
ENGINE: exact Ep (mod-p) + E0_ring (char-0). probe_407_r2_rung_anomaly_free.py.

RESULT 1 -- r=2 PRIZE RUNG ANOMALY-FREE, ROBUSTLY: Anom_2 = E_2^(p)-E_2^(0) = 0 for ALL 40 in-window
beta~4 prize primes at EACH n in {16,32,64,128,256}. => A_2 = 3n(n-1) - n^4/p is char-0-FIXED at every
prize prime; the bad-prime anomaly NEVER reaches r=2 in the window; r0(n)>2 robustly (resolves the
231caf44f open dichotomy: r0 does NOT reach 2 at n<=256). The r=2 rung A_2<=Wick can NOT crack.

RESULT 2 -- WHY the clean r=2 rung does NOT prove the prize: the in-tree L4 bound M^4<=sum|eta_b|^4=p*A_2
gives M<=(p*A_2)^{1/4} ~ (n^4*3n^2)^{1/4} = 3^{1/4} n^{1.5}. Actual M(n)~sqrt(n log(p/n))~few*sqrt(n).
MEASURED ((pA2)^.25 vs actual-M-sampled vs prize): n=16: 82.9/13.8/11.5; n=32: 236/23.0/18.2; n=64:
671/28.4/28.3. The L4 ceiling OVERSHOOTS the prize target by a factor ~n (n^1.5 vs sqrt(n)); the actual
M TRACKS the prize target (prize is TRUE). Confirms the board "2nd-order capped above Johnson by theorem."

SYNTHESIS (the moment-method wall from BOTH ends, rule-4/rule-6): the SHALLOW rung r=2 is anomaly-free
(char-0-clean) but TOO WEAK (L4 ceiling n^{1.5} >> prize sqrt(n log)); the DEEP rungs r>=r0(n) (r0
DECREASING 4,4,3) CARRY the bad-prime anomaly but there the char-0 Wick ratio saturates to 1 (f5ec4a9cf/
41980aa29) and the anomaly is BGK-tight (kappa explodes, sibling 1c48ff7cd). => BOTH accessible-clean
ends are walled; the prize sits in neither. CORE not closed; the moment/L4 method is mapped as
walled-from-both-ends. Pure-Python exact => axiom-clean trivially. probe_407_r2_rung_anomaly_free.py.

================================================================================
2026-06-15 The bad-prime anomaly ONSET DEPTH r0(n) PLATEAUS at 3 (does NOT reach
the prize rung r=2): r0 = {16:4, 32:4, 64:3, 128:3}. The r=2 prize rung is
anomaly-CLEAN in-window at n=128 (exact, 30-prime net). (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the decisive open question explicitly posed by the prior onset-depth entry above): the bad-prime
anomaly Anom_r = E_r^(p) - E_r^(0) carries the ENTIRE prize (the char-0 part E_r^(0)/Wick is thin-blind +
saturates to 1, 41980aa29). Its onset depth r0(n) = smallest r with some in-window prime Anom_r>0 was
measured DECREASING: 16:4, 32:4, 64:3 -- marching toward the prize-defining rung r=2 (M^4 <= p*A_2). The
prior entry left OPEN: does r0(n) -> 2 (anomaly reaches + potentially CRACKS the prize rung) or plateau at
r0>=3 (prize rung stays clean)? n=128 decides the trend.

OBJECT (exact, PROPER mu_n, in-window beta~4 primes p=1 mod n, NEVER n=q-1): engine REUSED verbatim from
probe_407_anom_worst_rtraj_n32.py (Ep = mod-p r-fold additive convolution count; E0_ring = char-0 neg-
closure cyclotomic-lattice energy). Engine cross-validated: E0_ring(n,2)=3n(n-1) EXACTLY at n=16..128
(=48768=3*128*127 at n=128), matching the in-tree closed form E_2(mu_n)=3n(n-1) (44234dc3d/5b0873ddb).
Probe scripts/probes/probe_407_anomaly_onset_n128.py (+ _verify.py for robustness/anti-vacuity).

RESULT -- r0(128) = 3 (PLATEAU, not ->2):
    n   | 16 | 32 | 64 | 128
    r0  |  4 |  4 |  3 |  3      <- decreasing 16->64, then PLATEAUS at 3 from n=64 to n=128.
  At n=128: r=2 anomaly-clean (Anom_2 = 0 over a WIDE 30-prime in-window net, beta 4.0-4.10, 0 nonzero);
  r=3 ONSET (6/30 primes nonzero, quantized witnesses {92160, 138240, ...} -- the discrete arithmetic
  ladder of the prior entry). ANTI-VACUITY (rule 1): at r=2, Ep=E0=48768 (both LARGE positive, equal) =>
  Anom_2=0 is a GENUINE exact cancellation, NOT a vacuous/trivial zero. r=2 anomaly-clean is robust.

VERDICT (rule-4 mapped result, rule-6 honest -- NOT a closure/refutation):
  - The prize-defining rung r=2 STAYS anomaly-free in-window through n=128. The worst in-window prize
    prime does NOT crack A_2 <= Wick at the prize rung at any accessible n (<=128) -- the candidate
    "anomaly reaches r=2" crack does NOT happen at the next octave.
  - r0(n) plateaus at 3, so the bad-prime anomaly enters one rung ABOVE the prize-defining rung and stays
    there (so far). This is CONSISTENT with the prize-equivalent target sitting at the DEEP rung r*~log m
    (the wickbound-capability pin sqrt(2/e)): the shallow accessible rungs (r=2 prize-defining, r=3 onset)
    do NOT extrapolate to the deep-r behavior -- the prize is decided at r*~log m (r*~14 at n=2^16), far
    above the r=3 plateau. The plateau REMOVES the "anomaly descends to r=2" mechanism as a finite-n crack
    route and reconfirms that all prize tension lives at deep r*, not at the shallow prize-defining rung.
  - Does NOT close/refute CORE. MAPS the onset-depth trend to its next octave + resolves the prior entry's
    open question (plateau, not ->2). Pure-Python exact integer counts, no Lean => axiom-clean trivially.
    probe_407_anomaly_onset_n128.py + probe_407_anomaly_onset_n128_verify.py.

================================================================================
THIN-SIDON depth->sup-norm bootstrap (§7.2, the only-live thinness-essential lead):
the conversion failure is beta-ROBUST. (push edc3a3913, receipt #444 ic-4705330516,
probe_407_supnorm_gate_beta_invariance.py)

CONSTRAINT LEMMA (rule-4, tightening §7.2): mu_n's Sidon DEPTH advantage grows with n
AND is LARGER at beta=5 (+8 vs +4 at n=32). But the sup-norm gate ratio
M_thin/M_neg-closed-random is FLAT across BOTH n and beta:
   beta=4 n=16: ~0.93 (p=65537,65617)
   beta=5 n=16: ~0.96 (p=1048609,1048721)  -- if anything WEAKER at beta=5.
=> the deeper beta=5 Sidon depth (where depth is LARGEST) buys NO sup-norm saving.
The depth->sup-norm bootstrap is necessary-not-sufficient (known) AND beta-robust (new):
a growing depth does not convert, and the conversion wall does not soften in the deepest-
depth regime. Also M_thin/M_generic-random ~1.07-1.14 (thin WORSE than generic random;
only beats neg-closed-random -- the 0.93-0.96 gap is the control's antipodal penalty,
not a 2-power-subgroup bonus). M_thin tracks ~0.92*sqrt(n log p), never a power below.
Builds on probe_407_supnorm_thinness_gate (n-axis flatness at beta=4). n=16 two-prime
per beta; n=32 beta=5 sup-sweep (p~3.3e7) untested (heavy). Does NOT close/refute CORE.

  SHARPENING (rule-3 gate, same session): the anomaly onset depth r0(n) is THICKNESS-MONOTONE.
  Thick composite 4|n controls vs thin 2-power at matched scale (probe_407_anomaly_onset_rule3.py,
  n=80 corrected to r0=3 via 20-prime net -- the 8-prime r0=4 was a net artifact):
      n     | 32  48  64  80  96  112  128
      type  |thin thk thin thk thk thk thin
      r0    | 4   3   3   3   3   3   3
  r0=3 for ALL n>=48 regardless of thickness (only n=32 thin=4, smaller scale). Thin n's do NOT onset
  SHALLOWER than thick at matched scale -- r0 tracks SCALE, not 2-power structure. By rule-3 (CORE is
  FALSE in the thick window), a thickness-monotone quantity cannot carry the prize => the anomaly ONSET
  DEPTH is NOT a thin-essential mechanism. Combined with the plateau (r0 stays 3, not ->2): the bad-prime
  anomaly enters at a thickness-generic, scale-tracking depth one rung above the prize rung, and stays
  there -- it is neither thin-essential at its onset nor descending to the prize-defining rung. CORE not
  closed/refuted; the onset structure mapped as thickness-generic + plateaued. probe_407_anomaly_onset_rule3.py.

  FURTHER (anomaly MAGNITUDE, same session): the Anom_3 quantization ladder is ALSO thickness-generic.
  GCD-factorization across thin 2-power vs thick 4|n at r=3 (probe_407_anom3_quantization_rule3.py):
      n=64 thin: 2^10*3^2*5 | n=96 thk: 2^6*3^2*5 | n=112 thk: 2^8*3^2*5*7 | n=128 thin: 2^10*3^2*5 |
      n=80 thk: 2^7*3*5^2
  ALL GCDs are the SAME smooth-number family 2^a*3^b*5^c*7^d -- thin and thick share the quantization
  structure => the anomaly MAGNITUDE quantization is thickness-generic too (rule-3 FAIL on magnitude,
  consistent with the onset-depth verdict). HONEST CAVEAT (rule 6): the nonzero-anomaly DENSITY #nz/#p is
  non-monotone + n-arithmetic-sensitive (n=96=2^5*3 is 20/20 anomalous vs thin n=64 1/20, n=128 5/20) --
  the density tracks the divisor/2-adic structure of n, NOT a clean thin-vs-thick signal. Net: neither the
  onset depth NOR the magnitude quantization of the bad-prime anomaly is thin-essential; the density is a
  separate n-arithmetic phenomenon, not a prize lever. probe_407_anom3_quantization_rule3.py.

================================================================================
2026-06-15 The SINGLE-FREQUENCY-DOMINATES step (M^{2r} <= p*A_r) carries NO thin
advantage: the domination slack D_r is thickness-generic and thin is slightly
WORSE (adverse, rule-3 fail) -- all prize tension is in A_{r*}<=Wick, not the
moment-to-sup passage (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (uncontested, follow-up to the wickbound-capability pin): that pin reduces the prize to A_{r*}<=Wick
at r*~log m VIA the single-frequency-dominates step M^{2r} <= sum_b|eta_b|^{2r} = p*A_r (tight when
r >~ log #freqs). UNTESTED: is the domination SLACK itself thin-essential? If thin mu_n's max frequency
dominates more cleanly (fewer competing big freqs), a thin advantage could hide in the domination step,
NOT the Wick value. Measured the slack ratio D_r := (sum_b|eta_b|^{2r})^{1/2r} / M (->1 as r grows).
Exact real periods (mu_n neg-closed => real), proper mu_n (beta~3, scale-stable ratio), NEVER n=q-1.
probe_407_singlefreq_domination_slack.py.

RESULT -- D_r is THICKNESS-GENERIC and thin is slightly WORSE (adverse direction):
    n=16 thin D3=1.358 D4=1.194 | n=24 thick D3=1.263 D4=1.106
    n=32 thin D3=1.617 D4=1.351 | n=40 thick D3=1.572 D4=1.302 | n=48 thick D3=1.584 D4=1.302
    n=64 thin D3=1.855 D4=1.476
  At matched scale thin D_r is LARGER (converges to 1 SLOWER) than thick -- the domination step is thin-
  ADVERSE, not thin-favorable. D_r tracks scale m=#cosets, and thin mu_n has MORE near-maximal frequencies
  competing (consistent with the prior ILO entry: thin concentrates more / worse bulk anti-concentration).

VERDICT (rule-3 mapped, rule-6 honest -- NOT a closure/refutation):
  - The single-frequency-dominates passage carries NO thin advantage; if anything it is thin-adverse. So
    a valid thin-essential prize proof CANNOT gain from the moment-to-sup domination step -- all the thin
    advantage (if any) must live ENTIRELY in the A_{r*} <= Wick inequality at the deep rung r*~log m.
  - This complements the wickbound-capability pin (the Wick VALUE is not a barrier) + the anomaly-onset
    thread (onset depth + magnitude both thickness-generic): every accessible structural handle around
    the deep-r A_{r*}<=Wick inequality is now mapped as thickness-generic. The irreducible thin-essential
    content is the deep-rung connected/cumulant Wick bound itself, nothing in its surrounding passages.
  - Does NOT close/refute CORE. Maps the domination step as a non-lever. Pure-Python exact (FFT-free real
    period sums), no Lean => axiom-clean trivially. probe_407_singlefreq_domination_slack.py.

================================================================================
2026-06-15 The SHALLOW e2=0 over-det resonance K(n,4)=n/4-1 is THICKNESS-INVARIANT
(rule-3 FAIL): subgroup-essential but NOT thin-essential (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE: the §6 honest-open-question combinatorial face -- the e2=0 over-det census R1 object. Follow-up to
(a) the EXACT shallow closed form K(n,w=4)=n/4-1, #bad=n^2/4-n (push e2_K_w4_n64), and (b) the width-sweep
finding that the w=4 resonance is the SOLE budget-overflow width across the whole deep floor window, which
left OPEN: "does the w=4 resonance (a) realize a delta*-window-edge bad config or (b) get dominated/excluded?"
417015191 proved the census thin-essential via RANDOM-SET vanishing; the THICK 2-POWER SUBGROUP control at
the shallow closed-form width was NEVER run. probe_407_shallow_resonance_thickness_rule3.py.

METHOD: same 2-power group mu_n (antipodal x->-x intact in ALL cases), vary ONLY beta=log_n(q). Exact,
2 prize-shaped primes per (n,beta), proper subgroup, never n=q-1. THICK prize-FALSE beta=2.3,3.0 vs THIN
prize beta=4.0,5.0.

RESULT 1 (exact, p-independent): K(n,w=4) is IDENTICAL across thick AND thin:
  n=16: K=3=n/4-1 at beta=2.3,3.0,4.0,5.0 (8/8 primes, #bad=48)
  n=32: K=7=n/4-1 at beta=2.3,3.0,4.0,5.0 (8/8 primes, #bad=224)
  => K(n,4)=n/4-1 is BETA-INVARIANT (thickness-independent + p-independent).
RESULT 2 (rule-6 disambiguation): negation-closed RANDOM sets (size n, x->-x closed, NOT a subgroup) give
  #bad=0 (4/4 draws at n=16 AND n=32) => the n/4-1 VALUE needs the cyclic 2-power SUBGROUP, not mere
  negation-closure. Sharpens 417015191 (random vanishes) to: neg-random ALSO vanishes at this width.

VERDICT (rule-3 constraint lemma, NO overclaim): the shallow e2=0 resonance K(n,4)=n/4-1 is SUBGROUP-
ESSENTIAL (random + neg-random both give 0) but THICKNESS-INVARIANT (same value in the prize-FALSE thick
beta=2.3-3.0 window as in the prize thin beta=4-5 window). CORE is FALSE in the thick window (rule-3), so a
thickness-invariant quantity CANNOT be the thin-essential mechanism. The w=4 resonance, though IN-WINDOW
(delta=1-4/n below cap, k-independent per probe_407_e2_census_general_k_resonance) and realizing e2=0 bad
configs (NOT excluded above cap), carries NO thin-vs-thick signal => NOT a thin-essential prize lever; a
generic 2-power-subgroup cyclotomic-antipodal count. This RESOLVES the sibling's open R1 w=4 sub-question
in the REFUTATION direction (in-window but thin-blind => Johnson-region/thickness-generic, consistent with
wf-D2 delta*->Johnson and #bad=n^2/4-n super-budget). CORE not closed, not faked. Pure-Python exact, no
Lean => axiom-clean trivially. probe_407_shallow_resonance_thickness_rule3.py.

================================================================================
2026-06-15 FINER rule-3 on the shallow resonance: the orbit-rep STRUCTURE is
ALSO thickness-blind (rule-3 FAIL is TOTAL, count AND structure) (opus-4-8 subagent)
--------------------------------------------------------------------------------
Follow-up to push 563fc7f85 (K(n,4)=n/4-1 thickness-invariant). Loophole closed: could two same-COUNT
families differ in WHICH e1-values appear (a thin-only algebraic signature in the orbit reps)? Tracked,
per (n,beta,prime): #reps in mu_n, and the multiplicative quotient-orders of e1-rep^n normalized by
m=(p-1)/n. probe_407_resonance_e1set_structure_rule3.py. proper subgroup, 2 primes/beta, never n=q-1.

RESULT (exact, n=16,32 x beta=2.3,3.0 [thick prize-FALSE] + 4,5 [thin prize]):
1. in_mu_n = 0 in EVERY case (thick AND thin): the resonance e1-representatives are NEVER in the subgroup
   mu_n itself -- uniform across all beta. No thin-only "reps land in subgroup" signature.
2. the normalized coset-order pattern (norm/m) spans the SAME small-fraction family {1, 1/2, 1/3, 1/4, 1/9,
   ...} for thick and thin; the variation present tracks the DIVISOR STRUCTURE of m=(p-1)/n (prime-
   arithmetic-dependent: e.g. beta=2.3 p=577 -> {0.25,0.5}; beta=4 p=65537 -> {0.25}; beta=5 p=1048721 ->
   {1.0}), NOT the thin-vs-thick axis. The per-prime factorization of m, orthogonal to thickness, is the
   only thing that moves.

VERDICT (rule-3, no overclaim): the shallow e2=0 resonance is thickness-blind in BOTH count (n/4-1) and
orbit-rep structure. The rule-3 FAIL is TOTAL -- there is no residual thin signal hiding in the e1-value
structure. Confirms + completes 563fc7f85: the shallow resonance is a generic 2-power-subgroup cyclotomic
object, not a thin-essential prize lever, at the count AND the structural level. CORE not closed, not faked.
Pure-Python exact, no Lean => axiom-clean trivially. probe_407_resonance_e1set_structure_rule3.py.

================================================================================
2026-06-15 n=64 octave confirms the shallow-resonance thickness-invariance brick
(K(64,4)=15 across thick+thin) (opus-4-8 subagent)
--------------------------------------------------------------------------------
Extension of push 563fc7f85 to the dossier's enumeration frontier n=64 (the thick-beta n=64 control was
never run; e2_K_w4_n64 did only the thin prize prime). probe_407_resonance_n64_thickness.py, exact,
C(64,4)=635376, 2 primes/beta, proper subgroup, never n=q-1.
RESULT: K(64,4)=15 (=n/4-1) IDENTICAL across thick beta=2.3 (p=14401,14593), thick beta=3.0
(p=262337,262657) AND thin beta=4.0 (p=16777601,16777729); #bad=960=64*15 exactly, p-independent, 6/6.
VERDICT: the thickness-invariance of the shallow e2=0 resonance now holds at n=16,32,64 -- three octaves
to the enumeration frontier. The rule-3 FAIL is robust across scale. CORE not closed, not faked.
Pure-Python exact, no Lean => axiom-clean trivially. probe_407_resonance_n64_thickness.py.

================================================================================
2026-06-15 wf-D2 BINDING-LAW CORRECTION: the formula s*=2k-1 (c*=k-1, delta*=1/2+1/n)
FAILS at n=8 -- the TRUE binding is s*=5 (c*=3), q-invariant. Independent EXACT
(non-GPU) reconfirmation of n=16 binding s*=7. The "law" is NOT universal => the
regime A->B s* transition is a REAL binding-formula change, not just a search
ceiling. (opus-4-8 subagent)
--------------------------------------------------------------------------------
LANE (the explicitly-flagged OPEN SUB-QUESTION of the wf-D2 entry, push e48d5ef59): regime A
(n=16,20,24,28) binding far-line monomial law s* = 2k-1 = n/2-1 (delta* = 1/2 + 1/n -> Johnson);
regime B (n>=32, GPU) "s* PINS at 13 across n=32,34,38 ... a pinned s* with climbing delta* is the
signature of a SEARCH CEILING, not a law. n=32 s*=13 not 15 MAY BE REAL and IS THE GENUINE OPEN
SUB-QUESTION." The GPU enumerated size-s WITNESS sets (C(n,s), infeasible deep) + TIMED OUT n>=36.

NEW INDEPENDENT ENGINE (avoids the witness-set wall): the in-tree FarCosetExplosion /
divided-difference fact -- every bad alpha at agreement >= k+1 is produced by some (k+1)-subset, and
the interpolability condition is AFFINE in alpha => each (k+1)-subset yields <=1 candidate alpha.
So I(a,b;thr) = #{alpha : maxagree(x^a+alpha x^b, RS[k]) >= thr} is EXACT via C(n,k+1) candidate gen
+ numpy-vectorized max-agreement (Lagrange eval over all n points at once). budget = n, binding
s* = largest thr with max-over-far-dirs I(thr) <= budget AND I(thr-1) > budget (the explosion edge).
Prize-faithful: PROPER mu_n (m=(p-1)/n>1), p>>n^3, p==1 mod n, NEVER n=q-1. rho=1/4 FIXED (k=n/4,
the wf-D2 axis). Probe scripts/probes/probe_407_regimeB_sstar_np.py (+ probe_407_regimeB_n32_sstar_exact.py).

ENGINE VALIDATION (n=16, k=4, FULL (a,b) sweep, EXACT, q-invariant p/n^3 in {8,80}):
  s=5(c=1)->I=3824[OVER]  s=6(c=2)->I=89[OVER]  s=7(c=3)->I=9[ok]  s>=8 ->0
  => binding s* = 7 = n/2-1 = 2k-1, c* = 3 = k-1.  delta* = 9/16 = 1/2 + 1/16.  AGREES with wf-D2
  (its c=2->89 = the established I(16)=89). Independent NON-GPU exact reconfirmation of regime A at n=16.

EXACT s* DATA (rho=1/4 axis, FULL (a,b) sweep, q-invariant -- 3 primes each where shown):
  n=8  k=2 (p/n^3 in {8,80,300}): I[s3]=40 I[s4]=9 I[s5]=8[ok] => binding s* = 5  (c*=3)  [n/2-1=3]
  n=12 k=3 (p/n^3 in {8,80,300}): I[s5]=169 I[s6]=169 I[s7]=12[ok] => binding s* = 7 (c*=4)  [n/2-1=5]
  n=16 k=4 (p/n^3 in {8,80}):     I[s6]=89  I[s7]=9[ok]            => binding s* = 7 (c*=3)  [n/2-1=7]
  At n=12, I[s7]=12 = budget=12 EXACTLY (sits AT the budget) and s6->169 explodes; q-invariant.

VERDICT (rule-4 mapped correction; rule-6 honest, NOT a CORE result):
1. The wf-D2 binding "law" s* = 2k-1 = n/2-1 (delta* = 1/2 + 1/n) is NOT universal: s* = 5,7,7 at
   n=8,12,16, vs the formula's n/2-1 = 3,5,7. It is CORRECT only at n=16 (independently re-confirmed
   exact q-invariant here, NON-GPU) and OVER-predicted-down at n=8,12 (true s* is HIGHER: 5 vs 3, 7 vs 5).
   The over-det binding level c* = s*-k = 3,4,3 is NOT a clean k-1 = 1,2,3 either. So neither s*=2k-1
   nor c*=k-1 is the universal binding law; both are small-n-coincidental.
2. THE REAL PHENOMENON -- s*-VALUE PINNING (exact, q-invariant, the SAME signature the GPU flagged):
   s* PINS at 7 across n=12 AND n=16 (two consecutive even n, q-invariant, EXACT). This is direct
   small-n EXACT evidence that "s* pins across a range of n then jumps" is a REAL property of the
   binding far-line incidence object -- NOT a search ceiling. It is structurally the SAME pattern the
   GPU reported in regime B ("s* PINS at exactly 13 across n=32,34,38"). The GPU's pinned-s* reading
   is therefore corroborated as a genuine law-feature by an independent EXACT engine at small n, which
   REVERSES the wf-D2 entry's "a pinned s* ... is the signature of a SEARCH CEILING" presumption for
   the s*=13 plateau: pinning is intrinsic, not a compute artifact.
   [HONEST CAVEAT: this is an analogy across scales (small-n exact pinning n=12,16 vs GPU n=32-38),
   NOT a proof that the n=32 s*=13 value itself is exact. The decisive n=24,32 exact recompute is
   compute-bound in pure Python (below). But the EXISTENCE of genuine s*-pinning is now exact-established.]
3. COMPUTE-WALL MAP (rule-6): n=32, k=8 candidate generation over C(32,9)=2.8e7 (k+1)-subsets is
   >20 min on CPU (measured: <2e6 subsets in 90s), confirming the GPU's own n>=36 timeout. So the GPU's
   exact regime-B s*=13 VALUE is not independently CPU-reproducible at present. The decisive n=24,32 exact
   recompute needs a faster (numba/Rust or GPU) candidate-gen + vectorized-agreement engine; the in-tree
   Rust pg engine (scripts/rust-pg/) is the natural vehicle.
SCOPE: this corrects a stated closed-form law (s*=2k-1 fails at n=8,12; correct s* = 5,7,7 not 3,5,7) and
establishes that s*-VALUE PINNING is a REAL exact feature (s*=7 pinned across n=12,16, q-invariant) -- the
same signature the GPU saw at n=32-38, REVERSING the prior "pinning = search ceiling" presumption. NOT a
CORE closure: the far-line delta* stays a Johnson-region object (delta* <= 1/2+1/n at tested n; at n=8
delta*=3/8 < Johnson), off the prize floor 3/4-Theta(1/log n) -- so the route still does not certify the
window interior. CORE not closed, not faked. Python+numpy EXACT, multi-prime q-invariant, no Lean changed
=> axiom-clean trivially. probe_407_regimeB_sstar_np.py + probe_407_regimeB_n32_sstar_exact.py.

--------------------------------------------------------------------------------
2026-06-15 UPDATE (TWO-ENGINE EXACT, decisive n=24): the wf-D2 binding-law correction +
s*-pinning is CONFIRMED. Independent in-tree RUST engine (scripts/rust-pg/pg) reproduces
my numpy results EXACTLY, and the decisive n=24 point lands s*=11.
--------------------------------------------------------------------------------
Cross-validated the above correction with the in-tree Rust far-line engine (scripts/rust-pg/src/main.rs,
pre-built target/release/pg) -- a COMPLETELY INDEPENDENT implementation (rayon-parallel divided-difference
over-determined witness enumeration, NOT my (k+1)-subset candidate-gen). The two engines AGREE EXACTLY on
both s* and the full incidence profile:

| n  | k | s* (BOTH engines) | n/2-1 | c*=s*-k | I-profile (matches both)                  |
|----|---|-------------------|-------|---------|-------------------------------------------|
|  8 | 2 | 5                 | 3     | 3       | s4->9, s5->5/8  (binding s5)              |
| 12 | 3 | 7                 | 5     | 4       | s5->17, s6->13, s7->7  (binding s7)       |
| 16 | 4 | 7                 | 7     | 3       | s6->89, s7->9  (binding s7)               |
| 24 | 6 | 11 (RUST, ~6min)  | 11    | 5       | s8->1153, s9->65, s10->25, s11->24        |

DECISIVE READING (exact, two-engine):
- s* = 5, 7, 7, 11 at n=8,12,16,24. The wf-D2 formula n/2-1 = 3,5,7,11 FAILS at n=8,12 (s* HIGHER:
  5 vs 3, 7 vs 5) and HOLDS at n=16,24. So s*=2k-1 is an ASYMPTOTIC law with small-n exceptions, NOT exact
  from n=8; n=12 is the last exception and is where the pinning is visible.
- s*-VALUE PINNING IS REAL: s* PINS at 7 across n=12 AND n=16, then JUMPS to 11 at n=24 (catching up to the
  n/2-1 line). This is EXACTLY the GPU regime-B signature ("s* pins at 13 across n=32,34,38 then the law
  would jump"). The small-n pinning (n=12->16) is now EXACT + TWO-ENGINE confirmed => the GPU's pinned-s*=13
  is corroborated as a GENUINE law-feature (a pinning plateau before a jump), NOT a search ceiling artifact.
  This RESOLVES the wf-D2 "genuine open sub-question" in the direction: the pinning is real; s*=13 is a
  plateau value, and the regime-A formula resumes at larger n (as it did n=12->16->24: 7,7,11).
- The defect (s*-k)/n = .375,.333,.1875,.2083 is non-monotone (the pinning dip), settling toward the
  Johnson-region value; delta* = .375,.4167,.5625,.5417 -> 1/2 = Johnson. STILL off the prize floor
  3/4-Theta(1/log n): this far-line object remains a Johnson-region quantity regardless of the pinning
  fine-structure. NOT a CORE result.
NET: a stated in-tree closed-form (s*=2k-1) is corrected (fails n=8,12), the regime-A<->B "open sub-question"
is resolved (pinning is a real plateau-before-jump, not a ceiling), via TWO independent exact engines
(my numpy + the in-tree Rust pg) that agree to the last incidence value. Rust n>=28~24min, n=32~9.6h (README)
=> the exact n=32 s*=13 value stays GPU/long-Rust-only, but its pinning NATURE is now exact-established at
small n. No Lean changed by me => axiom-clean trivially. probe_407_regimeB_sstar_np.py + scripts/rust-pg/pg.

--------------------------------------------------------------------------------
2026-06-15 SELF-CORRECTION (rule-6 adversarial re-audit of the two entries above):
n=20 (s*=9) added => the wf-D2 formula s*=n/2-1 HOLDS EXACTLY for ALL n>=16; the only
exceptions are n=8,12 (BELOW the wf-D2 stated range). The "s*-pinning resolves the GPU
regime-B sub-question" framing was OVER-READ and is RETRACTED. (two-engine exact)
--------------------------------------------------------------------------------
Filled the n=16->24 gap with the Rust engine: n=20,k=5 -> s*=9 (= n/2-1, formula HOLDS). Full exact
two-engine table on the rho=1/4 axis:
  n   |  8 | 12 | 16 | 20 | 24
  s*  |  5 |  7 |  7 |  9 | 11
  n/2-1| 3 |  5 |  7 |  9 | 11
  match| NO | NO |YES |YES |YES
HONEST RE-READING (correcting my own two prior entries):
1. The wf-D2 closed form s* = n/2-1 (delta* = 1/2+1/n) is CORRECT EXACTLY for all n>=16 (n=16,20,24
   confirmed exact two-engine; n=28 in progress). Its stated range was n=16..28 -- so within its claimed
   range it is RIGHT. My "correction" applies ONLY to n=8,12 (s* = n/2+1, exactly +2), which are BELOW
   the wf-D2 range. So this is a boundary-extension footnote, NOT a refutation of the in-range law.
2. The "s*-PINNING at 7 across n=12,16" I flagged is NOT a genuine plateau-before-jump: it is the n=12
   below-range exception (s*=n/2+1=7) COINCIDING by arithmetic with the n=16 in-range formula value
   (s*=n/2-1=7). With n=20 added the sequence 5,7,7,9,11 is strictly the formula +2 (n<=12) then exact
   (n>=16) -- a clean +2 boundary offset, NOT an extended pin. => my claim that this "corroborates the
   GPU regime-B s*=13 pinning as a genuine plateau and resolves the open sub-question" was OVER-READ.
   RETRACTED. The GPU regime-B (n=32,34,38; note n=34,38 are NOT divisible by 4, so those are a DIFFERENT
   axis -- fixed k, not fixed rho=1/4 -- and NOT directly comparable to my rho=1/4 table). The genuine
   regime-B sub-question (is the n=32 fixed-rho s* = n/2-1 = 15, or really 13?) is NOT resolved by my
   small-n data; it remains compute-bound (Rust n=32 ~9.6h).
NET (honest final): the only solid NEW results are (a) a two-engine EXACT extension of the wf-D2 table
to n=8,12,20 (n=8,12 are +2 boundary exceptions; n>=16 confirms the in-range formula), and (b) an
independent NON-GPU + Rust reconfirmation that the wf-D2 in-range law is exact. The far-line delta* stays
Johnson-region (-> 1/2), off the floor. NOT a CORE result; NO pinning-resolution claim. The regime-B
n=32 exact value remains open + compute-bound. Python+numpy + in-tree Rust, no Lean changed => axiom-clean.

--------------------------------------------------------------------------------
2026-06-15 DECOUPLING / INCIDENCE-DECAY frontier (#444 caveat #2): the budget crossing is
DEEPLY OVER-DETERMINED (c* = m-1 = n/4-1 = Theta(n)) -- resolves the §6 dichotomy in the
"deeply over-determined / OFF-BGK" horn. Axiom-clean Lean: DecouplingDecayCrossingDepth.lean.
--------------------------------------------------------------------------------
LANE: the decoupling/incidence-decay edge. OverdetIncidenceUnionCount.lean settled caveat #1
(p-independence: each far witness forces <=1 gamma). The remaining CHAR-0 OPEN ITEM (caveat #2,
explicitly NOT closed there) is the DECAY-vs-BUDGET threshold: at what over-determination depth
c = s-k does the decaying incidence I(s) cross the budget n? The §6 dichotomy pins the prize on this:
"deeply over-det (s-k ~ Theta(n/log n)) => p-indep cyclotomic root-count floor OFF BGK" vs
"under-det => re-couple to BGK". The brief's open question: is the crossing at s*-k ~ Theta(n/log n)?

DATA (all EXACT, q-invariant/p-independent, PROPER mu_n m=(p-1)/n>1, p>>n^3, p==1 mod n, NEVER n=q-1):

(1) k=2 axis (the closed-form axis), ANTIPODAL dir (n/2,n/2-1) -- probe_407_decoupling_decay_law.py:
    Decay is a CLIFF. I(c=2) = 2m^3-2m^2+1 (the in-tree closed form: 9,37,97 at n=8,12,16, HIT exactly,
    multi-prime). Then I(c>=3) COLLAPSES to {0,1}. => on k=2, s* = k+3 always. (Antipodal IS the k=2
    maximizer; the cliff is exact + p-independent at n=8,12,16.)

(2) rho=1/4 axis (k=n/4) = the PRIZE axis, FULL (a,b) direction sweep, two-engine exact (the
    DISPROOF two-engine s* table + a fresh independent full-sweep multi-prime reconfirm at n=12):
      n=12 (full sweep, p=13873 AND 138241 IDENTICAL): I(c)=17,13,7,6,0 at c=2,3,4,5,6 -> s* at c*=4.
      Two-engine s* table (rho=1/4): s*=5,7,7,9,11 at n=8,12,16,20,24 => c*=s*-k=3,4,3,4,5.
      For n>=16 (the in-range regime, s*=n/2-1 exact two-engine): c* = (n/2-1)-n/4 = n/4-1 = m-1.
      I-profile near crossing (n=24, k=6, budget=24): c2->1153, c3->65, c4->25, c5->24[=budget,CROSS].

DECAY-LAW STRUCTURE (the general I(c), derived + data-matched):
  I(c) = [a fast-decaying CUBIC BULK ~n^3/32 at c=2, dropping ~20-50x per step, gone by c~3-4]
       + [a persistent FLOOR PLATEAU of height ~n (the in-tree B1 count law = n), holding to c~m].
  The budget crossing c* is exactly where the cubic bulk drops below the ~n-height B1 floor: the LAST
  c before only the n-floor remains. At the crossing I(c*) ~ budget = n (n=24: I(c*=5)=24=budget exact;
  n=16: I(c*=3)=9; n=12: I(c*=4)=7).

VERDICT (the answer to the §6 / brief open question):
  c*(n) = s*-k = m-1 = n/4-1 = Theta(n) for n>=16  -- DEEPLY over-determined, LINEAR in n,
  EVEN DEEPER than the Theta(n/log n) posed in §6. (n=8,12 are the s*=n/2+1 boundary exceptions.)
  => FIRST HORN of the §6 dichotomy: the far-line incidence stays deeply over-determined at the
  binding radius, so it is a p-independent CYCLOTOMIC ROOT-COUNT FLOOR, OFF the BGK wall. It does
  NOT re-couple to BGK at the crossing.

SCOPE (rule-3, rule-6 -- NOT a CORE result): this RESOLVES the §6 combinatorial sub-question in the
deeply-over-determined direction, reached from the DECAY-CURVE angle. It CORROBORATES c.348 (far-line
is Johnson-region, delta* = (n-s*)/n -> 1/2, OFF the prize floor 1-rho-Theta(1/log n)) and gives the
MECHANISM: the deep over-determination (c*=Theta(n)) is exactly WHY the far-line object cannot reach
the floor -- it crosses the budget against a p-independent cyclotomic floor, never re-coupling to the
open BGK character-sum max. So the far-line/numeric enumeration route is confirmed OFF the prize wall.
CORE (the BGK sup-norm M(n) <= C sqrt(n log m)) remains OPEN -- this maps WHY the count face is not it.

LEAN (axiom-clean, [propext, Quot.sound] subset {propext,Classical.choice,Quot.sound}, 0 sorryAx):
DecouplingDecayCrossingDepth.lean -- crossingDepth_eq (c*=m-1), crossingDepth_values (3,4,5 at m=4,5,6),
crossingDepth_unbounded (c* exceeds any constant => not O(1)), crossingDepth_linear (m <= c*+1 => Theta(n),
not o(n)), crossingDistanceNumer_eq (delta*.n = 2m+1), crossingDistance_lt_capacity (2m+1 < 3m = capacity,
Johnson-side). Full locked build OK (3297 jobs). probe_407_decoupling_{decay_law,rho14_decay,full_decay}.py.

--------------------------------------------------------------------------------
2026-06-15 DECOUPLING rate-sweep EXTENSION: the c*=Θ(n) OFF-BGK verdict is RATE-INDEPENDENT
(holds for ALL sub-half rates rho<1/2). Lean: crossingDepthRate_ge / crossingDepthRate_quarter.
--------------------------------------------------------------------------------
Extends the decoupling crossing-depth result (push 93cfc0bf0) across rates. The binding
s* = n/2-1 is a RATE-INDEPENDENT consequence of the ANTIPODAL mechanism (the maximizer dir
(n/2,n/2-1) + its gamma=0 antipodal-closed witness are a structural property of mu_n, NOT of k).
PROBE CORROBORATION (probe_407_decoupling_rate_sweep.py, EXACT antipodal): the cubic peak
I(s=k+2)=2m^3-2m^2+1 is rate-independent -- n=16 antipodal gives I(c=2)=97 at k=2 (the rho=1/8 row)
matching the k=4 closed form. So for general rate k=rho*n (rho<1/2): c* = (n/2-1)-k = n(1/2-rho)-1:
  rho=1/4 -> c*/n -> 0.25 ; rho=1/8 -> 0.375 ; rho=1/16 -> 0.4375  -- ALL Theta(n), OFF BGK.
Degenerates only at rho->1/2 (c*/n->0): there the antipodal over-det floor s=k+2=n/2+1 EXCEEDS
n/2-1 so the antipodal binding law does not apply (k=n/2 regime, the Johnson endpoint itself).
=> The FIRST HORN (deeply over-det, p-indep cyclotomic floor OFF the BGK wall) holds across the
ENTIRE window-interior rate set rho in {1/4,1/8,1/16}. The far-line/count face is off the prize
wall at every accessible rate; CORE (BGK M(n)) remains the only open object.
HONESTY: the s*=n/2-1 RATE-INDEPENDENCE is a structural argument from the antipodal mechanism,
VALIDATED on the cubic-peak (rate-independent, exact) + the rho=1/4 full s* table (two-engine exact),
but NOT exhaustively swept for growing-k rho=1/8 (n=24 k=3 full sweep walled in pure Python). Stated
as a structural extension, not a fully-swept theorem. Lean records the arithmetic (crossingDepthRate_ge
=> c*>=d when k+d<=N-1; crossingDepthRate_quarter recovers the m-1 axis). Axiom-clean, locked build OK.

--------------------------------------------------------------------------------
2026-06-15 wf-RB: REGIME-B DECISIVE TEST — over-det far-line s* is JOHNSON-side, NOT a floor
climb; the n=32 "s*=13" climb is the engine b<s direction-cap ARTIFACT (lead refuted).
--------------------------------------------------------------------------------
Reimplemented the over-det far-line incidence I(a,b;s) = #{gamma : x^a+gamma x^b agrees with
RS[mu_n,k] on s pts} as a numpy-VECTORIZED EXACT F_p engine over the FULL b-range (no b<s
direction cap). Per witness set: the (s-k) consecutive order-k divided-difference RS-parity
functionals applied to u0,u1 in batched int64 mod-p; gamma=parallel-ratio verified across all
s-k comps; heavy=>p. CROSS-VALIDATED EXACT vs the proven in-tree CPython `incidence`: n=16 dir
(10,4) s=6->89/s=7->9/s=8->9; n=20 (18,5)s7->20,(16,5)s7->21,(10,5)s6->6521,(8,6)s7->121 — all OK.
Files scripts/probes/probe_wf4RB_{vec_rprofile,decisive,boundary,overdet_rprofile}.py.

VERIFIED EXACT r-profiles (p-INDEPENDENT, two primes p=1 mod n, p>>n^3; budget=q*eps*=n):
 n=16 k=4: BAD r=11,10 (binders (14,4),(11,4)); GOOD r=9(I=9),8(I=9). smallest BAD r=10 =>
   r*=9=n/2+1, delta*=9/16=1/2+1/n, s*=7=n/2-1. JOHNSON+1rung. (complete exact profile)
 n=20 k=5: BAD r=14,13,12 (binders (18,5),(16,5)); GOOD r=11,10(I=5). smallest BAD r=12 =>
   r*=11=n/2+1, delta*=11/20=1/2+1/n, s*=9=n/2-1. JOHNSON+1rung. (complete exact profile)
 n=24 k=6: BAD r=16,15 (binders (21,6),(15,6)). Binder (15,6) by rung: s8(r16)=1153, s9(r15)=49,
   s10(r14)=9, s11(r13)=9 — crosses budget=24 between r=15(BAD) and r=14(GOOD). (21,6): s8=57(BAD),
   s9=8,s10=0,s11=0. Consistent with the campaign's exact full-sweep s*=11=n/2-1 => r*=13=n/2+1
   JOHNSON+1rung. (binder-family transition exact; the FULL r=14 sweep over all far-valid dirs hit
   the CPython enumeration wall C(24,14)~1.96M x ~70 dirs — reported as such, not claimed.)

THE n=32 s*=13 ARTIFACT: confirms KB farline-engine-bs-direction-cap-artifact.md — the Rust/CUDA
engine caps far dirs to b in [k,s), dropping the binding directions throughout their BAD phase,
so it UNDER-counts incidence => OVER-estimates delta* (0.594 vs true ~0.531). My full-b-range
engine reproduces JOHNSON exactly at n=16,20 with NO climb; n=32 exhaustive boundary is
compute-walled (C(32,16)~6e8), so the n=32 climb is killed by the artifact mechanism + the exact
n=16,20,24 pattern, NOT by a direct n=32 exhaustive recompute.

VERDICT: over-det far-line is JOHNSON-side (delta*=1/2+1/n -> 1/2), NOT a window-interior floor
climb. The far-line over-det FLOOR-mechanism lead is REFUTED. Reconfirms the campaign over-det
Johnson-lock (9629193c6, DecouplingDecayCrossingDepth, antipodal mechanism) by independent exact
full-b-range enumeration. Far-line is the Plotkin/Johnson PROXY (epsMCA >= far_inc/q); the open
prize is the UNDER-determined (s-k<=1) BGK char-sum wall M(n)=max_{b!=0}|sum_{x in mu_n} e_p(bx)|,
UNCHANGED. No closure claimed. — wf-RB (proven-per-fixed-n n=16,20; binder-exact n=24)

================================================================================
REFUTATION (constraint lemma): the over-det VANISHING (coset-union) supply is NOT the binding
constraint at prize depth — it is super-exponentially LOOSE there. (zeta lane, push pending)
================================================================================
OBJECT (exact char-0 cyclotomic, PROPER mu_n, n=2^a, NEVER n=q-1): the over-det vanishing-subset
count V_r(n) = #{S subset mu_n : p_1(S)=...=p_r(S)=0}, the §6.5 generating-function object. CLOSED
FORM (axiom-clean, OverdetVanishingCosetCount.lean, pushes 29b45f180 + f4e864a8b):
   V_r(n) = 2^{ n / 2^{floor(log2 r)+1} }   (r>=1)   [= coset-unions of the order-2^{floor(log2 r)+1}
   subgroup; vanishing <=> coset-union; #cosets = n/d, each in/out].

CONSTRAINT LEMMA (probe_zeta_supply_vs_budget.py, exact integer, multi-n 2^8..2^128):
The prize budget is q*eps* ~ n (the #bad cap). Comparing V_r to the budget n:
 (a) At the PRIZE BINDING DEPTH r ~ log2 n (the deep-rung r* ~ ln q ~ depth log m, where the BGK
     wall lives): V_{log2 n}(n) = 2^{n/(2 log2 n)} -- SUPER-EXPONENTIALLY above the budget n
     (supply/budget = 2^{n/(2 log2 n) - log2 n}; e.g. n=2^16: 2^2048 vs 2^16; n=2^30: 2^33554432
     vs 2^30). The coset-union vanishing supply is ASTRONOMICALLY loose at prize depth.
 (b) V_r(n) only DROPS to the budget n at depth r* ~ n/(2 log2 n) (EXACT: r*/n = 1/(2 log2 n),
     verified n=2^8..2^30, MATCH). That crossover depth r* ~ n/log n is FAR deeper than the
     prize-relevant shallow depth r ~ log n.

VERDICT: the over-det vanishing (coset-union) subset COUNT is NOT the constraint that binds at prize
depth -- it is loose by a doubly-exponential margin throughout the shallow r ~ log n regime where the
BGK wall lives. This is a mapped refutation WITH MECHANISM (the exact dyadic closed form): it rules
out the coset-union supply-count as the prize binding object and confirms (per the §2 master chain)
that the binding constraint at prize depth must be the W4 sub-exponential CANCELLATION (the
DC-subtracted A_r <= Wick char-p validity), NOT the supply count. Localizes the open core AWAY from
the §6.5 supply-count object. CORE (M(mu_n) <= C sqrt(n log m)) UNCHANGED/OPEN. -- zeta lane,
co-author wakesync.

================================================================================
CONSTRAINT LEMMA (push CrossStepCeilingInsufficient.lean, lane m3r2, 2026-06-15):
The LOOSE Lam-Leung ceiling alone CANNOT discharge M3CrossStepBound for r >= 2.
================================================================================

The recursion-closure (_wf5M3_crossstep_ceiling) localized the prize energy ladder onto ONE open
Prop: M3CrossStepBound G : forall r, crossMass G r <= 2r*(2r-1)!!*n^{r+1}, where
crossMass G r = E_{r+1} - n*E_r (off-diagonal cross mass of the proven recursion E_{r+1}=n*E_r+cross_r).
CrossStepRungOne discharged r=0,1 from the proven r<=2 energy ceilings. This entry maps the wall on
the OBVIOUS next strategy (keep using ceilings) and proves it insufficient, axiom-clean.

INPUTS available without new analytic work:
 - Lam-Leung upper ceiling  E_{r+1} <= (2r+1)!!*n^{r+1}  (LamLeungCeiling G (r+1))
 - UNCONDITIONAL diagonal floor  E_r >= n^r  (pow_card_le_rEnergy, proven here: the n^r pairs (v,v)).

Subtracting floor from ceiling:
  crossMass G r = E_{r+1} - n*E_r  <=  (2r+1)!!*n^{r+1} - n*n^r  =  ((2r+1)!! - 1)*n^{r+1}.
M3 step target = 2r*(2r-1)!!*n^{r+1}. Since (2r+1)!! = (2r+1)*(2r-1)!!:
  ((2r+1)!! - 1) - 2r*(2r-1)!!  =  (2r-1)!! - 1.    [ceiling_slack_eq, exact]
So the loose-ceiling bound EXCEEDS the M3 step target by EXACTLY ((2r-1)!! - 1)*n^{r+1}.
 = 0  iff  (2r-1)!! = 1  iff  r <= 1   ((-1)!!=(1)!!=1, (3)!!=3, (5)!!=15, ...).

VERDICT (ceiling_insufficient_of_two_le): for every r >= 2 (and n >= 1) the loose Lam-Leung ceiling +
diagonal floor STRICTLY overshoot the M3CrossStepBound target by ((2r-1)!!-1)*n^{r+1} > 0. The deep
rungs therefore CANNOT be closed by ceilings alone -- they require genuine off-diagonal autocorrelation
CANCELLATION (C_r(delta) << E_r on average), which is precisely the open BGK content. This explains
mechanistically why r=1 (CrossStepRungOne) closes from ceilings and r>=2 does not: the overshoot
(2r-1)!! - 1 vanishes only at r<=1.

Probe corroboration (probe_crossstep_r2.py, PROPER mu_n, n=2^a, n|p-1, p>>n^4, NEVER n=q-1): the TRUE
cross_2 <= 12n^3 holds (ratio 0.33->0.89), but the composite-ceiling bound 15n^3 - n*E_2 = 12n^3 + 3n^2
overshoots 12n^3 by 3n^2 = ((2*2-1)!!-1)*n^3 at every prime -- matching the lemma exactly.

NOT a refutation of M3CrossStepBound (which IS true). A refutation of the ceiling-only PROOF STRATEGY
for r >= 2, with the exact slack. CORE (M(mu_n) <= C sqrt(n log(p/n))) UNCHANGED/OPEN. -- m3r2 lane,
co-author wakesync.

================================================================================
CONSTRAINT LEMMA (probe probe_spur_onset_growth.py, lane spur3, 2026-06-15):
The smallest odd bad prime for antipodal-free relations does NOT grow with scale m —
it pins at 3 from weight 4 onward, uniformly in m. Bad primes ACCUMULATE, they don't escape.
================================================================================
OBJECT (exact char-0 cyclotomic norms N(σ_T)=|Res(R_T,Φ_{2^m})|, PROPER μ_n, n=2^a, NEVER n=q−1):
the spurious-collision support — for weight w and scale m, the set of odd primes p with p|N(σ_T) for
SOME antipodal-free relation σ_T of weight w over μ_{2^m}. This is the p-set on which Spur_{w/2}(p)≥1.

PROBE (exact sympy, m=3,4,5, all antipodal-free weight-2 and weight-4 relations enumerated):
 (a) WEIGHT-2: min odd bad prime = None at m=3,4,5 — NO odd prime divides ANY weight-2 norm
     (norm ≡ Φ_{2^m}(1)=2). Reconfirms the LANDED ShortRelationNormBase.not_dvd_weight_two_norm_of_odd
     UNIFORMLY in m (not just m=3): Spur_1(p)=0 at every odd p, every scale.
 (b) WEIGHT-4: min odd bad prime = 3 at m=3,4,5 (smallest bad primes {3,7,17,47,79,97,113,193,257,...}).
     The smallest bad prime is SCALE-INVARIANT (=3 for all m≥3) — it does NOT grow with m.

VERDICT (constraint): the bad-prime set does NOT escape to ∞ with scale. A FIXED small odd prime (3)
supports weight-4 spurious collisions at EVERY scale m≥3. So the "no spurious collision at a fixed
prize prime for large m" hope is FALSE on the arithmetic face: every odd prime is eventually bad at
bounded weight. This INDEPENDENTLY reconfirms (via the p-divisibility/norm face) the refutation of the
"good prime exists" pigeonhole (c.154, prize is ∀-field-universal) — the spurious-collision obstruction
is present at EVERY odd prime, accumulating from weight 4, not localizable to a sparse bad-prime set at
fixed weight. The wall therefore cannot be dodged by choosing a good prime; it must be beaten by
bounding the COUNT Spur_r(p) at the worst fixed p (the genuine open object). Pairs with the LANDED
weight-3 witness SpurWeightThreeCollision (Spur_2(3)≥1, 8fadf6eb1): together — weight-2 clean at all
odd p, weight≥3 dirty at every odd p — they pin the tower's onset at weight 3 and its universality in p.
NOT a refutation of CORE; a mapped boundary on the Spur support. CORE (M(μ_n)≤C√(n log(p/n))) OPEN.
-- spur3 lane, co-author wakesync.

================================================================================
REFUTATION-WITH-MECHANISM (lane dblcompose, 2026-06-15): the doubling-mass HALVING
does NOT iterate via the other tower neighbor. plus2Mass = plusMass EXACTLY.
================================================================================
OBJECT. DilationDoublingMassHalf proves a SINGLE-level cap: along one genuine disjoint
tower step (negation-closed G=μ_n, ζ order 2n, μ_n ⊔ ζμ_n disjoint), the L²-weighted
DOUBLING (+sign) cross-mass plusMass = Σ_{s_b≥0} ‖η_b‖‖η_{ζb}‖ ≤ ½q|G|, where
s_b = Re η_b · Re η_{ζb}. Its honesty note flags the OPEN gap: a single frequency may sit
on the +trajectory through MANY levels; the average only forbids ALL of them. The natural
hope is the halving ITERATES — intersecting +sign at a second tower dilation thins by
another ½ ⟹ geometric deep-descent cap plus_ℓ ≤ 2^{-ℓ}q|G|.

PROBE (scripts/probes/probe_doubling_twolevel_compose.py + _massloc.py + _orbit_sign_coherence.py;
exact complex periods over PROPER thin μ_n=⟨h²⟩, h order 2n, p≍n⁴, 2n|p−1, n=8,16,32,64,
NEVER n=q−1; imMax ≤ 1e-8 confirms reality from negation-closure):
The two tower neighbors of b are ζb and ζ⁻¹b. Define the doubly-doubling mass plus2Mass on
{b : s_b(ζ)≥0 AND s_b(ζ⁻¹)≥0}. RESULT, every n:
  • plus2Mass/plusMass = 1.000   (the second halving FAILS completely)
  • cross-mass over (s1,s2) sign-quadrants: mass(++)=0.500, mass(−−)=0.500,
    mass(+−)=mass(−+)=0.000 to machine precision — the mass is PERFECTLY sign-coherent.
  • DIRECT VERIFY (verify_coset): max|η_{ζb} − η_{ζ⁻¹b}| = 1.8e-15 ⟹ η_{ζb} = η_{ζ⁻¹b} EXACTLY.

MECHANISM (now an exact algebraic identity, not just empirics). ζb and ζ⁻¹b differ by
ζ² = ζ·(ζ⁻¹)⁻¹, and ζ² ∈ μ_n = G (ζ has order 2n ⟹ ζ² has order n). The period is
G-COSET-INVARIANT in the frequency (eta_smul_invariant, #389: η_{gb}=η_b for g permuting G).
Hence η_{ζ⁻¹b} = η_{ζ⁻²·(ζb)} = η_{ζb} since ζ⁻² ∈ G. Therefore the second cross-sign
s_b(ζ⁻¹) = Re η_{ζ⁻¹b}·Re η_b = Re η_{ζb}·Re η_b = s_b(ζ) IDENTICALLY. The "second" +condition
is LITERALLY the first; intersecting them is intersecting a set with itself ⟹ plus2Mass=plusMass.

CONSTRAINT LEMMA. The doubling-mass halving is a G-COSET INVARIANT of the dilation:
plusMass ψ G (g·ζ) = plusMass ψ G ζ for any g permuting G. So NO dilation in the G-coset of ζ
(in particular the inverse/other-neighbor ζ⁻¹) yields a second, independent halving. A geometric
deep-descent cap CANNOT be built from tower-neighbor dilations; any genuine second halving needs a
dilation OUTSIDE the G-coset of {ζ, ζ⁻¹}, and the worst-case single-frequency sign word (the
BGK/Paley wall) is untouched by this average-mass argument. Companion to survivor-honesty's COUNT
no-recursion finding (S_i/S_{i-1}≈0.50 with no clean identity) — here the MASS side has no recursion
either, for a sharper reason (exact period collapse, not statistical).

FORMALIZED (axiom-clean, in-graph, build exit 0 / 3319 jobs):
Frontier/DilationDoublingMassNoCompose.lean —
  • crossSign_dilate_smul_eq / crossMass_dilate_smul_eq : G-coset-invariance of the cross-sign/mass.
  • plusMass_dilate_smul_eq : plusMass ψ G (g·ζ) = plusMass ψ G ζ (the doubling mass is a G-coset
    invariant of the dilation) — EXTENDS eta_smul_invariant.
  • plusMass_inv_eq : plusMass ψ G ζ⁻¹ = plusMass ψ G ζ (no second halving via the other neighbor).
NOT a refutation of CORE; a precise NO-GO on the iterated-halving deep-descent route + the exact
mechanism. CORE M(μ_n) ≤ C√(n log(p/n)) UNCHANGED/OPEN. -- dblcompose lane, co-author wakesync.

================================================================================
REFUTATION-WITH-MECHANISM (lane bivstep, 2026-06-16): the SECOND Stepanov stall
on mu_n -- the Stepanov-Weil sqrt(q) FIELD bound is VACUOUS in the prize regime,
and Johnson sqrt(kn) sits strictly BELOW both Stepanov outputs.
================================================================================
OBJECT. StepanovStructuredVacuous formalized the FIRST Stepanov stall (classical Stepanov on the
SEPARABLE X^n-1 pins multiplicity to M=1 => trivial degree bound s* <= n-1, mu_n_roots_simple /
stepanov_collapses_to_degree). Its docstring records the SECOND stall AS PROSE ONLY: the
Stepanov-Weil / Kelley-Owen field-root bound is ~ sqrt(q), "exponentially vacuous because
p ~ n*2^128 >> n^2". This lane makes that an axiom-clean THEOREM and pins the exact three-way
arithmetic separation in the prize regime.

PROBE (ONE sweep, exact integer arithmetic, scripts/probes/probe_stepanov_weil_qvacuity.py;
n=2^a a=3..8 (n=8..256) x beta in {3,4,5} (prize beta in [4,5], beta=3 = boundary q=n^3); worst
interior rate k=n/4; NEVER n=q-1): 0/54 fails. In every prize instance:
  1. q >= n^2 (beta>=3 certainly) => sqrt(q) >= n => Weil FIELD bound EXCEEDS trivial deg=n => VACUOUS.
  2. k < n => sqrt(kn) < n => Johnson strictly below the trivial bound.
  3. k*n < q => sqrt(kn) < sqrt(q) => Johnson strictly below the Weil bound.

MECHANISM. The sqrt(q) field bound (Kelley-Owen 2015 arXiv:1510.01758 trinomial-root; Bi-Cheng-Rojas
/ Kelley 2016 arXiv:1602.00208 t-nomial) counts F_q-POINTS; it is in sqrt(q), NOT in the subgroup
size n. In the prize regime q ~ n^beta (beta>=4) we have sqrt(q) ~ n^{beta/2} >= n^2 >> n, so the
field bound is exponentially worse than the trivial separable-relation degree bound n-1 (the FIRST
stall's output). The Johnson radius sqrt(kn) ~ n^{(1+rho)/2} (rho=k/n<1) is strictly below BOTH
n and sqrt(q). So the Johnson saving is NOT a Stepanov phenomenon in EITHER form: classical Stepanov
gives only the trivial n (no sqrt-saving, multiplicity pinned by separability), and Stepanov-Weil
gives a vacuous sqrt(q). The sqrt(kn) Johnson saving is a sparsity / uncertainty-principle
phenomenon (Tao / Donoho-Stark / Meshulam), as the in-tree verdict already names.

CONSTRAINT LEMMA. The vacuity is thinness-localized: sqrt(q) >= n iff q >= n^2 iff beta >= 2; for
the THICK regime q ~ n^{2.3..3.2} the field bound only starts to bite near beta=2, but in the THIN
prize regime (beta>=4) it is exponentially vacuous. The Weil/field-cardinality route to s* cannot
reach Johnson, let alone the prize floor sqrt(n log(q/n)); any real beyond-Johnson saving must come
from the subgroup-intrinsic sparsity/uncertainty input, not from counting field points.

FORMALIZED (axiom-clean {propext, Classical.choice, Quot.sound}, in-graph lake-locked exit 0 /
1969 jobs): Frontier/StepanovWeilQVacuous.lean --
  • weil_field_bound_vacuous : n^2 <= q => n <= sqrt q (the Weil bound exceeds the trivial deg bound).
  • johnson_below_trivial : k < n => sqrt(kn) < n (Johnson below classical Stepanov output).
  • johnson_below_weil : k*n < q => sqrt(kn) < sqrt(q) (Johnson below Weil output).
  • stepanov_outputs_strictly_above_johnson : the packaged three-way separation
    sqrt(kn) < n <= sqrt(q) AND sqrt(kn) < sqrt(q) in the prize regime.
NOT a refutation of CORE; a precise NO-GO mapping the SECOND Stepanov stall (the field-bound
vacuity), companion to the in-tree FIRST stall (separability/M=1 collapse). CORE
M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. -- bivstep lane, co-author wakesync.

================================================================================
REFUTATION-WITH-MECHANISM (lane plotkinsep, 2026-06-16): the far-line incidence
threshold is a PLOTKIN PROXY -> 1/2, strictly BELOW Johnson for rho < 1/4, hence
it is NOT the MCA delta* (the prize object, >= Johnson). Clean structural
separation isolating the BGK/Paley-hard residual. master-open-thread #5.
================================================================================
OBJECT. Two distinct thresholds are conflated in the #357/#389/#407 attack:
  (1) far-line incidence threshold (COMPUTABLE proxy), in-tree budget B = q*eps* =
      (n*2^128)*2^-128 = n (B1IncidenceBridge.WorstCaseFarIncidenceBounded at B=n).
      Validated exact (Rust engine, matches canonical probe delta*(mu_16,k=4)=9/16):
        farLineProxy n rho = 1/2 + (1/(2 rho) - 1)/n.
  (2) the true MCA delta* (PRIZE target), >= Johnson = 1 - sqrt rho (list-decodable).

PROBE (ONE sweep, exact rational arithmetic, scripts/probes/probe_plotkin_farline_johnson.py
+ Newton bracket /tmp/johnson_tight.py; n=2^a a=3..11 (n=8..2048), rho in
{1/8,1/6,1/5,3/16,1/4,1/3}; PROPER thin mu_n power-of-two; NEVER n=q-1):
  - tends-to-1/2: |farLineProxy - 1/2| = (1/(2 rho) - 1)/n -> 0, 54/54 pass.
  - Johnson-crossing (rho<1/4, Johnson>1/2 via tight Newton sqrt bracket): the proxy
    drops STRICTLY below Johnson by n=32 for EVERY rho<1/4 tested
    (rho=1/8: below n>=32; rho=1/6,1/5,3/16: below n>=32).

MECHANISM. The far-line proxy threshold's excess over 1/2 is the explicit O(1/n) term
(1/(2 rho) - 1)/n (the Plotkin-ceiling approach), so the proxy -> 1/2. For rho < 1/4 the
Johnson radius 1 - sqrt rho exceeds 1/2 (square: rho<1/4 => sqrt rho<1/2). Hence past an
explicit n-threshold the computable proxy is strictly below Johnson, and since MCA delta*
>= Johnson (list-decodability), the proxy is strictly below MCA delta*. The two objects
diverge: the (easy, -> 1/2) far-line incidence is NOT the (hard, >= Johnson) MCA threshold.

CONSTRAINT LEMMA. The BGK/Paley half-power difficulty lives ENTIRELY in the gap between
the far-line proxy (-> 1/2, computable, p-independent) and the true MCA delta* (>= Johnson).
Any "decoupled / p-independent" claim about the far-line incidence is a claim about the
PROXY, not the prize delta*. The prize-hard residual is exactly the asymmetric far-line
words whose MCA contribution exceeds the symmetric Plotkin ceiling 1/2 (master-list #5:
"isolate the hard residual to genuinely asymmetric far-line words").

FORMALIZED (axiom-clean {propext, Classical.choice, Quot.sound}, in-graph lake-locked
exit 0 / 3298 jobs): Frontier/FarLineProxyBelowJohnson.lean --
  - farLineProxy_sub_half : farLineProxy n rho - 1/2 = (1/(2 rho) - 1)/n (exact O(1/n) gap).
  - farLineProxy_gt_half : 0<rho<1/2, 0<n => 1/2 < farLineProxy (approach from above).
  - farLineProxy_lt_half_add : n > (1/(2 rho)-1)/eps => farLineProxy < 1/2 + eps (quant. Plotkin).
  - half_lt_johnson_of_lt_quarter : 0<rho<1/4 => 1/2 < 1 - sqrt rho (Johnson exceeds 1/2).
  - farLineProxy_lt_johnson : prize regime + explicit n-threshold => farLineProxy < 1 - sqrt rho.
  - farLineProxy_lt_mca : + (Johnson <= mcaDeltaStar) => farLineProxy < mcaDeltaStar (separation).
NOT a refutation of CORE; a precise structural SEPARATION refuting the over-identification
"far-line incidence = delta*" in the prize regime, isolating the prize-hard residual.
CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. -- plotkinsep lane, co-author wakesync.

---

## Orbit-count is doubling-INVARIANT: the plateau is INVISIBLE to the orbit skeleton (imprimrung)

CONTEXT (master-open-thread item #3). _Close26_PrimitiveCleanRecursion proves the clean
recursion D*_{2n}(m) = D*_n(m-1) (no plateau) at PRIMITIVE far directions (gcd(b-a,n)=1),
and defers the IMPRIMITIVE analogue (the plateau-doubling rung, B27) as the open landable
brick. lalalune's measurement: the plateau IS active at imprimitive binding directions
(w(16)=1, w(32)=2).

FINDING (probe scripts/probes/probe_imprimitive_rung_decomp.py + the gcd sweep, exact,
n=2^a a=3..8, every in-range direction s, never n=q-1). The governing ORBIT COUNT
N = d = gcd(b-a, n) (the OrbitCountCrossingLaw budget threshold) is DOUBLING-INVARIANT at a
FIXED direction, at PRIMITIVE *and* IMPRIMITIVE directions ALIKE: for n=2^a and any in-range
shift 1 <= s <= n, gcd(s, 2n) = gcd(s, n). Exhaustively verified 0 fails over 4094 cases.

MECHANISM. Write t = v_2(s). For a power of two gcd(s, 2^a) = 2^min(t, a). The in-range
bound s <= 2^a forces t <= a (else 2^(a+1) | s => s >= 2^(a+1) > 2^a >= s). So
min(t, a) = min(t, a+1) = t, hence gcd(s, 2^a) = gcd(s, 2^(a+1)). The orbit count is fixed
under n -> 2n at EVERY in-range direction; the imprimitivity (d even) does NOT create an
extra orbit under doubling.

CONSTRAINT LEMMA. The plateau-doubling lalalune measured (w(32)=2) is NOT visible at the
orbit-count level. The orbit-count skeleton route to the imprimitive recursion is
PLATEAU-BLIND: it gives N(2n)=N(n) just like the primitive case, so it cannot be the source
of the extra rung. The plateau lives STRICTLY in the gap between the orbit count N and the
distinct-gamma count D* (the BGK/incidence content) -- the open object. This refines item #3:
any imprimitive "clean recursion" derived purely from the orbit-count crossing law inherits
the primitive cleanness and therefore CANNOT capture the plateau; the plateau is an N->D*
phenomenon, not an N phenomenon.

FORMALIZED (axiom-clean {propext, Classical.choice, Quot.sound}, single-file lake-env-lean
exit 0 + in-graph lake-locked exit 0): Frontier/OrbitCountDoublingInvariant.lean --
  - gcd_two_pow_eq_two_pow_min_v2 : gcd(s, 2^a) = 2^min(v2 s, a) for s>0 (the pin).
  - v2_le_of_le_two_pow : 1 <= s <= 2^a => v_2(s) <= a (in-range valuation bound).
  - gcd_doubling_invariant : 1 <= s <= 2^a => gcd(s, 2*2^a) = gcd(s, 2^a) (headline).
  - orbitCount_doubling_invariant : packaged on the supply identity; the orbit count d is
    unchanged under n -> 2n at primitive AND imprimitive directions.
NOT a CORE closure; a constraint lemma localizing the plateau to the N->D* gap. Field-
universal arithmetic; thinness enters only via the tower n=2^a. ASYMPTOTIC GUARD cliff-at-n/2
untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. -- imprimrung, co-author wakesync.

## The proven entropy CEILING is decision-IMPOTENT for the plateau dichotomy: it is the WRONG inequality direction (ceildecimp)

CLAIM REFUTED. That the proven entropy ceiling (prizeDeltaStar_ceiling: delta* <=
prizeDeltaStar, unconditional) could DECIDE the additive-vs-multiplicative plateau dichotomy
(is m* = O(log n), prize HOLDS, or m* linear, prize FAILS?). lalalune's 8-angle consolidation
(#444, 2026-06-16 04:57Z) flagged this as finding #2, adversarially verified but NEVER a
theorem: "entropy-ceiling | provably CANNOT decide -- ceiling bounds m* from below; deciding
needs an upper bound (logically independent). Confirmed clean negative."

MECHANISM. The ceiling bounds delta* from ABOVE. A deeper binding plateau (larger m*) means a
smaller radius delta*, so an upper bound on delta* is exactly a FLOOR a <= m* (direction:
BELOW). Deciding the ADDITIVE horn needs an UPPER bound m* <= g (a CEILING on m*, direction:
ABOVE). A floor and a ceiling on the same quantity are LOGICALLY INDEPENDENT: from a <= m*
alone one derives neither m* <= g nor g < m*. The predicate (a <= .) is realised by witnesses
on BOTH sides of every threshold g >= a (a itself is <= g; g+1 is > g), so it implies neither.

PROBE (one sweep, exact, the tree's own cStarFull from rho4.out, thin mu_n=2^a, NEVER n=q-1):
scripts/probes/probe_entropy_ceiling_decision_impotence.py. Tower {8,16,32}: each measured m*
clears the unconditional floor a=1 yet a strictly larger value clears it too (0 fails). The
abstract straddle (a <= vlo <= g < vhi for vlo=a, vhi=g+1) holds for every (a,g) with a <= g
(0 fails). The floor cannot separate the horns.

FORMALIZED (axiom-clean, in fact depends on NO AXIOMS AT ALL -- strict subset of {propext,
Classical.choice, Quot.sound}; single-file lake-env-lean exit 0 + in-graph lake-locked 112
jobs exit 0): Frontier/_EntropyCeilingDecisionImpotence.lean --
  - floor_not_imp_ceiling : exists v, a <= v and not v <= g (floor does not give additive horn).
  - floor_not_imp_strict_gt : exists v, a <= v and not g < v (floor does not give mult horn).
  - floor_straddles : for a <= g, two witnesses straddle g, both clearing the floor.
  - ceiling_floor_cannot_decide (HEADLINE) : BOTH implications fail; the ceiling-side floor
    decides NEITHER horn.
  - floor_predicate_independent_of_ceiling : the general logical form (floor predicate
    independent of any ceiling predicate).
  - tower_instance_n32 : non-vacuity at n=32 (m*=5, floor 1, additive threshold 10=2 log2 32).
NOT a CORE closure; a constraint lemma forbidding the ceiling-route to the dichotomy. The
plateau-rate dichotomy = BCHKS Conj 1.12 = the BGK/Paley wall stays OPEN. Field-universal Nat
order arithmetic; thinness enters only via WHICH m* the tower binds. NO capacity / beyond-
Johnson / sub-linear / growth-law claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE
M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. -- ceildecimp, co-author wakesync.

## The master gap identity capacity-delta* = (m*-1)/n in _BridgeB01/_BridgeB04 is OFF BY ONE; the audited-correct identity is capacity-delta* = m*/n (mastergapfix)
lalalune's 2026-06-16 audit (docs/kb/deltastar-444-audit-corrections-2026-06-16.md, S.A.1) caught a
convention off-by-one in the landed master-gap bricks. _BridgeB01.deltaStar_master_gap_identity and
_BridgeB04.deltaStarFormula take the binding radius as delta* = 1 - (s*-1)/n (the orbcount script-
display convention) and correctly derive capacity-delta* = (m*-1)/n -- honest conditionals, but on a
hypothesis that encodes the off-by-one. The INCIDENCE-CORRECT radius (delta-close iff agreement
>= (1-delta)*n) is delta* = 1 - s*/n; with THAT radius the forced identity is capacity-delta* = m*/n.
PROBE (scripts/probes/probe_master_gap_offbyone.py, exact Q over the audit's own VERIFIED rows): the
corrected gap m*/n REPRODUCES the audit's exact delta* (3/8 at n=8 BELOW Johnson, 9/16 at n=16 ABOVE);
the old (m*-1)/n is exactly 1/n too small; the old radius over-states delta* by exactly 1/n. The
corrected delta* CROSSES Johnson 1/2 between n=8 and n=16 (the structural fact the laundered 0.5/0.625
hid). LANDED Frontier/_MasterGapOffByOneCorrected.lean (single-file lake-env-lean axiom-clean
{propext, Classical.choice, Quot.sound} on all 5 printed, no sorry; in-graph lake-locked 819 jobs exit
0): master_gap_identity_corrected (delta* = 1 - rho - m*/n from the correct radius),
capacity_gap_eq_corrected (capacity-delta* = m*/n), old_radius_off_by_one_n (the two radii differ by
1/n), old_gap_under_by_one_n (old gap 1/n smaller), corrected_crosses_johnson (3/8 < 1/2 < 9/16), plus
the exact n=8,16 pins. Discharges audit ACTION G.1. A CONSTRAINT/CORRECTION brick (rule 4), NOT a CORE
closure: supplies the audited-correct identity + certifies the off-by-one. Field-universal Q algebra;
thinness enters only via which (s*, m*) bind. NO capacity / beyond-Johnson / sub-linear / growth-law
claim (the delta* values 3/8, 9/16 + the Johnson crossing are exactly the audit's); ASYMPTOTIC GUARD
cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. -- mastergapfix, co-author
wakesync.

## The dedup N_r < C(n,r) is STRICT but FRACTIONALLY VANISHING at the binding log depth r=log2 n => the A3 WeakestSuff escape is strict-but-asymptotically-thin (leans WALL) (dedupstrict)
The A3 escape question (_CoreA3_BackwardProof.lean; dossier deltastar-444-prize-regime-established-
2026-06-16.md sec VI lever 2 + sec IX): WeakestSuff is weaker-or-equal to BCHKS 1.12, the gap being
the dedup slack Sigma_r - D >= 0; a REAL escape (vs the wall) requires the dedup D <= Sigma_r to be
STRICT at log depth r ~ log n. Instantiated on a concrete p-INDEPENDENT object via the just-landed
spectrum closed form _SubsetSumSpectrumClosedForm.spectrumCount (push 89151523f) over the thin
dyadic mu_n (n=2^a, m=n/2): Sigma_r = C(n,r) (r-subsets with multiplicity), D = N_r =
spectrumCount m r = Sum_{k==r mod 2} C(m,k) 2^k (distinct r-subset-sums), slack = C(n,r) - N_r.
PROBE (scripts/probes/probe_dedup_slack_strict_at_log_depth.py +
probe_dedup_ratio_trend_at_log_depth.py, EXACT big-int, NEVER n=q-1): at the binding r=log2 n the
dedup is STRICT at every tower level n=8..16384 and the slack GROWS in absolute terms (n=8:16,
n=16:587, n=32:57088, ...), BUT the slack FRACTION f(n)=slack/C(n,r) is monotonically DECREASING
from n=16 onward (0.323 -> 0.283 -> 0.219 -> 0.156 -> ... -> 0.0055 at n=16384), survival N_r/C ->1.
VERDICT: the dedup is strict (escape direction non-vacuous as a strict inequality) but fractionally
vanishing at the binding log depth: asymptotically almost all r-subsets have distinct sums at
r=log n, so the dedup gives NO fractional savings there. This QUANTIFIES the dossier's 'in-tree
evidence leans wall': a strict-but-fractionally-thin dedup is NOT a real escape. LANDED
Frontier/_DedupSlackStrictButVanishing.lean (single-file lake-env-lean axiom-clean {propext,
Classical.choice, Quot.sound} on all 8, no sorry; in-graph lake-locked 3297 jobs exit 0): anchor_n8/
n16/n32 (exact C(n,r), N_r, slack at the binding depth, slack>0 STRICT), dedup_strict_on_tower,
slack_grows_absolute, frac_dec_16_32, frac_dec_32_64 (slack fraction strictly decreasing via exact
Nat cross-multiplication slack1*C2 > slack2*C1), strict_but_fractionally_vanishing (HEADLINE: strict
+ grows-absolute + fraction-decreasing combined). A CONSTRAINT/refutation-with-mechanism brick
(rule 4), NOT a CORE closure: does NOT close BCHKS 1.12 (the budget-scale ~n relevance of the slack
is not bounded here). EXTENDS _SubsetSumSpectrumClosedForm + the A3 reduction by measuring the
named-open dedup-strictness quantity at the binding depth. Field-universal Nat combinatorics;
thinness enters via the 2-power tower n=2^a. NO capacity / beyond-Johnson / sub-linear / growth-law
claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.
-- dedupstrict, co-author wakesync.


## O191 -- the leading rung D*(1) is p-DEPENDENT; the binding over-det count is NOT (audit ACTION G.3)
Discharges ACTION G.3 of lalalune's 2026-06-16 audit (deltastar-444-audit-corrections-2026-06-16.md
section B): the orbcount leading-rung value D*(1) was laundered as a single fixed p-independent datum
D*(1)=3936 across four bridge files (_BridgeB46, _BridgeB33, _CoreA1_LowerBound, _BridgeB23) and many
#444 comments. The audit caught that the m=1 / under-determined edge (s-k<=1) is genuinely
p-DEPENDENT; only the over-det m>=2 regime is p-independent. PROBE: INDEPENDENTLY re-ran the in-tree
enumerator orbcount 16 4 (scripts/rust-pg) at the two audit primes (this session, 2026-06-16) +
scripts/probes/probe_dstar1_p_dependence_split.py locks the verdict (NEVER n=q-1, thin 2-power mu_n):
D*(1)=3936 at p=65537 (=16^4+1 Fermat) but D*(1)=3984 at p=1048609 (=16^5+33) -- they DIFFER by 48,
so the laundered "D*(1)=3936 p-independent" is FALSE. Meanwhile D*(2)=89 and D*(3)=9 are IDENTICAL
across both primes, and the binding radius is IDENTICAL across both primes: at BOTH primes D*(1),D*(2)
exceed budget(=n=16) and D*(3)=9<=16 is the first rung at/below budget, so m*=3 and the over-det
far-line delta*=1-(s*-1)/n=5/8 are p-INDEPENDENT. The p-dependence of D*(1) is invisible to m* (both
3936 and 3984 exceed budget 16). VERDICT: p-independence is a property of the BINDING over-det count,
NOT the leading rung -- the precise corrected statement the audit requires. LANDED
Frontier/_DStarOneIsPDependentBindingIsNot.lean (single-file lake-env-lean exit 0 + in-graph
lake-locked 778 jobs exit 0; ALL theorems depend on NO axioms at all, strict subset of {propext,
Classical.choice, Quot.sound}, no sorry): dStar1_at_65537/at_1048609, dStar1_p_dependent (HEADLINE
refutation), dStar1_gap (=48), dStar2_p_independent, dStar3_p_independent, binding_at_65537/at_1048609,
binding_radius_p_independent, dstar_p_independence_is_binding_not_leading (HEADLINE: leading rung
p-dependent + binding over-det count p-independent + binding radius m*=3 p-independent). A
CONSTRAINT/refutation-with-mechanism + correction brick (rule 4), NOT a CORE closure: refutes a value
laundered identically across 4 bridge files and certifies p-independence at the audit's required
granularity. Field-universal exact Nat over the orbcount rows; thinness enters via the 2-power mu_n on
which D*(m) was measured. NO capacity / beyond-Johnson / sub-linear / growth-law claim; ASYMPTOTIC
GUARD cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.
-- dstar1pdep, co-author wakesync.


## O192 -- the corrected n=32 far-line proxy is 17/32 / m*=7 (audit G.5, post-RETRACTION 3c2d4fdf1)
The audit (deltastar-444-audit-corrections-2026-06-16.md) originally FLAGGED n=32 as disputed
between m*=4/0.625 and m*=5/19/32(=0.594). lalalune's RETRACTION commit 3c2d4fdf1 (sec A0, "THE
BIG ONE") killed BOTH: the m*=5/0.594 reading was an engine DIRECTION-CAP (b<s) ARTIFACT (the GPU
pg searched too few far directions). With the FULL b-range, the over-det far-line delta* is a
JOHNSON-LOCKED PLOTKIN PROXY: farLineProxy(n,rho)=1/2+(1/(2 rho)-1)/n, at rho=1/4 it is 1/2+1/n,
with m*=n/4-1 (LINEAR, not sub-linear). VERIFIED full-direction at n=16 (9/16,m*3), n=20
(11/20,m*4), n=24 (13/24,m*5). So the corrected n=32 value is delta*=17/32(~0.531), m*=n/4-1=7,
NOT 0.594/m*5, NOT 0.625/m*4. PROBE:
scripts/probes/probe_farline_proxy_exact_tower_n32_corrected.py confirms the in-tree
FarLineProxyBelowJohnson.farLineProxy formula reproduces the VERIFIED anchors n=16,20,24 and pins
n=32 at 17/32/m*7, and that the retracted artifact 19/32 is OFF the proxy by exactly 1/16 (m* off
by 2 rungs). LANDED Frontier/_FarLineProxyTowerN32Corrected.lean (single-file lake-env-lean exit
0; axiom-clean, strict subset of {propext, Classical.choice, Quot.sound}, no sorry;
mStar_n32_is_seven depends on NO axioms at all): proxy_quarter (farLineProxy n (1/4)=1/2+1/n),
proxy_n16/n20/n24 (the VERIFIED anchors), proxy_n32_corrected (=17/32, HEADLINE),
artifact_off_proxy (!=19/32), artifact_gap (19/32-proxy=1/16), mStar_linear (m*=n/4-1 on the
tower), mStar_n32_is_seven (=7, !=5), proxy_n32_above_half (>1/2=Johnson),
g5_resolved_proxy_tower_corrected (HEADLINE). EXTENDS the in-tree farLineProxy def (commit
bce3f1a79) by pinning its exact tower values + the corrected n=32 point. A CONSTRAINT/correction
brick (rule 4) resolving the flagged G.5 datum in the form the retraction left it; NOT a CORE
closure. Field-universal exact R/Nat over the proxy formula; thinness enters via the 2-power mu_n
on which the proxy was measured. NO capacity / beyond-Johnson / climb-to-capacity claim (the
climb-to-capacity reading is exactly what 3c2d4fdf1 retracted; the proxy LOCKS to 1/2=Johnson from
above, the prize floor >=Johnson is the SEPARATE harder BCHKS/BGK object); ASYMPTOTIC GUARD
cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.
-- flpproxytower, co-author wakesync.


## O193 -- the TOTAL char-0 subset-sum spectrum mass of mu_n is 3^(m-1)(m+3) (extends spectrumCount)
EXTENDS the just-landed _SubsetSumSpectrumClosedForm.spectrumCount (per-depth char-0 subset-sum
cardinality N_r of the 2-power subgroup mu_n, m=n/2; lalalune 06:07Z) from the per-depth count to
the TOTAL over all depths r=0..2m: T(m) := sum_{r=0}^{2m} N_r = 3^(m-1)*(m+3). MECHANISM is a
depth-multiplicity reindex (NOT a moment/energy method): a net-vector class with k nonzeros
(contributing C(m,k)2^k) is reachable at depth r iff k==r(2) and k<=r<=2m-k, i.e. at exactly
(m-k+1) depths; swapping summation order gives T(m)=sum_k (m-k+1)C(m,k)2^k, closed via the two
binomial GF sums sum_k C(m,k)2^k=3^m and sum_k k C(m,k)2^k=2m 3^(m-1) into (m+1)3^m-2m 3^(m-1)=
3^(m-1)(m+3). PROBE scripts/probes/probe_spectrum_total_mass.py: all three forms (direct double
sum, k-form, closed form) + both GF identities agree EXACTLY over n=2..80 (VERDICT PASS); pure
char-0 count, never validated at n=q-1. LANDED Frontier/_SubsetSumSpectrumTotalMass.lean (push
faabd2c86; single-file lake-env-lean exit 0 + in-graph lake-locked 3298 jobs exit 0; axiom-clean,
strict subset of {propext, Classical.choice, Quot.sound}, no sorry/axiom/native_decide on all 7
printed): sum_choose_two_pow, sum_k_choose_two_pow (the GF sums, fully general), spectrumTotal_eq_
kForm (the swap; sum_comm + card bijection r->(r-k)/2 onto range(m-k+1)), spectrumTotalKForm_closed,
spectrumTotal_closed (HEADLINE), spectrumTotal_values (T(1..4)=4,15,54,189), spectrumTotal_n16
(=24057). An EXTEND-PROVEN structural census brick (rule 4): the total spectrum mass in closed form,
building directly on the freshly-landed spectrumCount. Does NOT close CORE: the prize binds the
PER-DEPTH growth N_{rho n+1} at the binding depth, not the total mass, and the char-0<->F_p bridge
holds only in the dilute N_r << p regime (the binding depth is collision-saturated = the BGK/BCHKS
wall). NO capacity / beyond-Johnson / sub-linear / growth-law claim; ASYMPTOTIC GUARD cliff-at-n/2
untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. 2-power-specific (spectrumCount fails
at non-2-power n). Author 0xSolace/Sol, co-author wakesync.
-- spectotal.


## O194 -- the PEAK of the char-0 subset-sum spectrum of mu_n is (3^m+1)/2, attained UNIQUELY at the center depth r=m=n/2 (the distinct-gamma growth-law center value, extends spectrumCount)
EXTENDS the in-tree _SubsetSumSpectrumClosedForm.spectrumCount (per-depth char-0 subset-sum
cardinality N_r of the 2-power subgroup mu_n, m=n/2) by pinning its PEAK in closed form and
certifying STRICT UNIMODALITY with the unique max at the center r=m. This is the #444 sec VIII-C
distinct-gamma growth-law object: the maximal width of the deep-band distinct subset-sum (= bad-
scalar) census. RESULT: spectrumCount m m = (3^m + 1)/2, equivalently 2*N_m = 3^m + 1.
MECHANISM is a PARITY SPLIT of the binomial GF (NOT a moment/energy method, NOT the O193 total-mass
reindex): at r=m the range bound is min(m,2m-m)=m so N_m = sum_{k<=m, k==m(2)} C(m,k)2^k is the
SAME-PARITY-AS-m half of the binomial expansion. Adding the two evaluations (1+2)^m=3^m (all k) and
(1-2)^m=(-1)^m (alternating) gives 2*(parity-m sum) = 3^m + (-1)^m*(-1)^m = 3^m + 1 in BOTH parities
of m. PROBE scripts/probes/probe_spectrum_growth.py (ONE sweep, thin tower m=4..12, never n=q-1):
2*N_m=3^m+1 EXACT; N_r strictly increasing on 0..m; UNIQUE center peak; palindrome r<->2m-r; VERDICT
PASS. FORMALIZED Frontier/_SubsetSumSpectrumPeak.lean (single-file lake-env-lean exit 0, axiom-clean
strict subset of {propext, Classical.choice, Quot.sound}, no sorry/axiom/native_decide on all 7
printed): sum_choose_two_pow_full ((2+1)^m GF), sum_choose_neg_two_pow ((-2+1)^m alternating GF),
spectrumCount_peak_two_mul (HEADLINE, 2*N_m=3^m+1 via the parity-weighted sum filter split),
spectrumCount_peak (N_m=(3^m+1)/2 division form), spectrumCount_peak_values (41,122,365,1094,3281 at
m=4..8), spectrumCount_strict_increase_tower (N_r strictly up on 0..m for m=4..8 = strict
unimodality on the rising half), spectrumCount_peak_strict_max_tower (r=m is the strict argmax of
the spectrum r=0..2m at m=4,8). An EXTEND-PROVEN structural census brick (rule 4): the PEAK of the
distinct-gamma spectrum in closed form, building on the freshly-landed spectrumCount + palindrome.
Does NOT close CORE: the prize binds the PER-DEPTH growth N_{rho n+1} at the BINDING depth
(collision-saturated = the BGK/BCHKS wall, where char-0<->F_p fails), NOT the center value.
NO capacity / beyond-Johnson / sub-linear / closure claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched.
CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. 2-power-specific (spectrumCount fails at non-2-
power n). Author Sol, co-author wakesync.
-- spectgrowth.

## O195 -- rising-half SECOND-DIFFERENCE recurrence of the char-0 subset-sum spectrum: N_r - N_{r-2} = C(m,r)*2^r on 2<=r<=m (each two-step rise is EXACTLY the leading antipodal term; extends spectrumCount)
STATUS: EXTEND-PROVEN structural census brick (rule 4), axiom-clean, LANDED. NOT a CORE closure.
For the 2-power subgroup mu_n (n=2^mu, m=n/2) the depth-r char-0 subset-sum spectrum cardinality
N_r = spectrumCount m r (the deep-band bad-scalar count #bad_r, via in-tree
_SubsetSumSpectrumClosedForm + DeepBandSubsetSumSpectrum.witness_pin) obeys, on the RISING HALF
2<=r<=m, the exact two-step recurrence N_r - N_{r-2} = C(m,r)*2^r. MECHANISM (NOT a moment method):
spectrumCount filters k in {0..min(r,2m-r)} on the parity class k==r(2). On the rising half
min(r,2m-r)=r and min(r-2,2m-(r-2))=r-2, and the parity classes coincide (r, r-2 same mod 2), so the
two sums run over the SAME parity class but range(r+1) vs range(r-1). The only index added going
r-2 -> r that survives the parity filter is k=r itself (k=r-1 is the WRONG parity), term C(m,r)*2^r
= the leading antipodal cross-polytope term. So each two-step rise of the deep-band census is
EXACTLY the top antipodal term, no lower-order mixing; it exposes N_r = sum_j C(m,r-2j)2^{r-2j}
(the parity-class partial sum) and pins the dominant part C(m,r)2^r. PROBE
scripts/probes/probe_spectrum_rising_step.py (ONE sweep, exact big-int, thin tower m=8,16,32,64,
never n=q-1): N_r-N_{r-2}=C(m,r)2^r for every 2<=r<=m AND N_r=sum_j C(m,r-2j)2^{r-2j}; VERDICT PASS.
FORMALIZED Frontier/_SubsetSumSpectrumRisingStep.lean (single-file lake-env-lean exit 0 + in-graph
lake-locked 3298 jobs exit 0; axiom-clean subset of {propext, Classical.choice, Quot.sound}, no
sorry/axiom/native_decide on all 3 printed): min_eq_left_rising (min r (2m-r)=r on r<=m),
parity_sub_two ((r-2)%2=r%2 for 2<=r), spectrumCount_rising (rising-half unfold over range(r+1)),
spectrumCount_rising_step (HEADLINE: N_r = N_{r-2} + C(m,r)2^r via a range-split range(r+1) =
range(r-1) cup Ioc(r-2) r, filter_union, the Ioc-filtered-by-parity collapses to singleton {r}),
spectrumCount_rising_anchors + spectrumCount_rising_n8_r2 (N_2=113=N_0+C(8,2)*4=1+112). Builds on
the freshly-landed spectrumCount; DISTINCT from O193 (total 3^(m-1)(m+3)) and O194 (peak
(3^m+1)/2): this is the per-2-step INCREMENT law, not the total or center value. Does NOT close
CORE: the prize binds the PER-DEPTH growth N_{rho n+1} at the BINDING depth (collision-saturated =
the BGK/BCHKS wall,
where char-0<->F_p fails), not the char-0 rise. NO capacity / beyond-Johnson / sub-linear / closure
claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.
2-power-specific (spectrumCount fails at non-2-power n). Author Sol, co-author wakesync.
-- risingstep.

## O196 -- GROWTH LAW of the deep-band distinct-gamma ORBIT count at the shallow rungs r=3,4: it is STRICTLY super-linear in n (oc3 = C(g,2) ~ n^2/32; oc4 = 2(g/2)^2(g/2-1)+1 ~ n^3/512), QUANTIFYING the obstruction to the ThreadD O<=1 union-count floor (extends DeepBandOrbitCountDescent)
STATUS: EXTEND-PROVEN structural growth-law brick (rule 4), axiom-clean, LANDED. NOT a CORE closure.
Shaw's 03:33 exhaust-#444 commit (e3c7c4c97) funneled ALL remaining structural threads to ONE open
object: the distinct-gamma ORBIT count being <= 1 at the binding rung (ThreadD
_ThreadD_UnionCountFloor reduces the prize floor hfloor PROVABLY to UnionCountBadStacks _ _ n, i.e.
to orbit-collapse O -> 1 at binding = DstarPlateauLeBudget = the BGK/BCHKS wall). The in-tree
DeepBandOrbitCountDescent pins the shallow-rung orbit counts oc3 (r=3) and oc4 (r=4) via the 2-adic
self-similar descent but ONLY certifies the rungs n=16..128 by decide (no general-g growth law) and
never compares them to the O<=1 floor. This brick supplies the general-g growth law + the resulting
strict super-linearity, making the ThreadD obstruction QUANTITATIVE. RESULTS (g = n/4, the 2-power
prize tower, NEVER n=q-1): oc3 g = g*(g-1)/2 = C(g,2) (quadratic, ~ n^2/32); oc4 (2h) = 2h^2(h-1)+1
(cubic, ~ n^3/512); BOTH strictly super-linear (oc3 g > g for g>=4; oc4 (2h) > 2h for h>=2); and the
gap oc4 - 1 = 2h^2(h-1) to the O<=1 floor is STRICTLY INCREASING in h (blows up). So the union-count
floor (ThreadD, needing O<=1) is FALSE at the shallow rungs by a strictly GROWING margin; the O -> 1
collapse can only happen AT the deep binding rung r ~ log n (the open growth law = the wall). The
brick LOWER-BOUNDS the gap the descent must cross between the shallow rung and binding; it does NOT
cross it. PROBE scripts/probes/probe_orbit_count_growth_law.py (ONE sweep, exact int, prize tower
n=16..512, never n=q-1): oc3=g(g-1)/2, oc4=2(g/2)^2(g/2-1)+1, oc3>g, oc4>g, the descent
oc4(2h)=2(2h)oc3(h)+1 (in-tree cross-check), and the gap oc4-1 strictly increasing; VERDICT PASS.
FORMALIZED Frontier/_OrbitCountGrowthLaw.lean (single-file lake-env-lean exit 0 + in-graph
lake-locked 8316 jobs exit 0; axiom-clean subset of {propext, Classical.choice, Quot.sound}, no
sorry/axiom/native_decide on all 6 printed): orbitCount3_closed (oc3 g = g(g-1)/2 via
Nat.choose_two_right), orbitCount4_closed (oc4 (2h) = 2h^2(h-1)+1 via the descent def),
orbitCount3_gt_self (oc3 g > g for g>=4, consecutive-product evenness + nlinarith),
orbitCount4_gt_self (oc4 (2h) > 2h for h>=2), orbitCount4_gap_strict_mono (the gap oc4-1 strictly
increasing for h>=2), orbit_count_growth_obstructs_union_floor (HEADLINE: the four facts conjoined).
Builds on the in-tree DeepBandOrbitCountDescent (orbitCount3 = C(g,2), orbitCount4 = bad3(g/2));
DISTINCT from that file's decide-rungs (this is the general-g growth law + super-linearity, the
quantitative ThreadD obstruction it never stated). Does NOT close CORE: it bounds the SHALLOW rungs
r=3,4, not the deep binding rung r ~ log n (= |Sigma_r(mu_s)| = BCHKS 1.12 = the BGK wall;
the descent itself stops past r=4 where the maximizing line flips to full-order). Char-sum-free,
char-agnostic, NOT thinness-essential. NO capacity / beyond-Johnson / sub-linear / closure claim;
ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.
Author Sol, co-author wakesync.
-- orbcountgrowth.

## O197 -- the translation orbit of an ODD-card carrier E over ZMod(2^a) has cardinality EXACTLY 2^a = n (the proven orbit-SIZE factor in #bad = n*#orbits + 1; extends CliqueOrbitFreeness.prize_regime_fixed_eq_zero)
STATUS: EXTEND-PROVEN structural cardinality brick (rule 4), axiom-clean, LANDED. NOT a CORE
closure. CliqueOrbitFreeness.prize_regime_fixed_eq_zero proves the STABILIZER half of lalalune's
orbit-count reformulation D*(m) = (orbit size = n)*#orbits(m): for an ODD-card exponent set E in
ZMod(2^a) the translation E -> E+j fixes E only for j=0 (trivial stabilizer). That file asserts in
PROSE "hence the orbit has size exactly n = 2^a" but never proves the CARDINALITY conclusion, the
literal orbit-size factor n in the in-tree #bad = n*#orbits + 1 (DeepBandOrbitCountDescent) and in
ThreadD's union-count floor. grep-confirmed-MISSING: no in-tree theorem states the orbit cardinality
= 2^a (only the trivial-stabilizer j=0). This brick supplies it; it is the COMPANION orbit-SIZE half
to O196's orbit-COUNT growth law (the two factors of D = (orbit size)*#orbits). MECHANISM (NOT a
moment method, pure cyclic Finset counting): model the rotation action by translate j E := E.image
(.+j); injectivity of j -> translate j E for odd-card E (translate i E = translate j E => translate
(i-j) E = E => i-j in stabilizer => i-j=0 by prize_regime_fixed_eq_zero), so the orbit = univ.image
(translate . E) has card = card univ = 2^a (Finset.card_image_of_injective + ZMod.card). PROBE
scripts/probes/probe_orbit_card_eq_n.py (ONE sweep, exact, a=2..6, never n=q-1): ALL odd-card E
subset ZMod(2^a) have orbit size EXACTLY n; even-card E can have a SMALLER orbit (e.g. {0,n/2} has
orbit n/2, nontrivial stabilizer); VERDICT PASS. FORMALIZED Frontier/_OrbitSizeEqN.lean (single-file
lake-env-lean exit 0 + in-graph lake-locked olean exit 0; axiom-clean subset of {propext,
Classical.choice, Quot.sound}, no sorry/axiom/native_decide on all 5 printed): translate_eq_self_iff
(translate j E = E <-> forall x in E, x+j in E, reconciling the file's stabilizer predicate via
injectivity of (.+j)), translate_injective_of_odd_card (the orbit map is injective for odd-card E),
orbit_card_eq_two_pow (HEADLINE: orbit card = 2^a), orbit_card_eq_card_addGroup (= Nat.card (ZMod
(2^a)), the orbit-stabilizer conclusion with trivial stabilizer explicit), orbit_n16_singleton (a=4
anchor: orbit of {0} has size 16). Builds on CliqueOrbitFreeness; sharpens the orbit-SIZE half
(trivial stabilizer -> the cardinality = n). Does NOT close CORE: it is the PROVEN multiplicative
factor n, NOT a bound on #orbits(m) (the open cyclotomic-collision growth law = the BGK/BCHKS wall,
the object O196 shows is super-linear). Pure cyclic-group Finset counting: character-sum-free,
char-agnostic, p-independent, NOT thinness-essential. NO capacity / beyond-Johnson / sub-linear /
closure claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n))
UNCHANGED/OPEN. Author Sol, co-author wakesync.
-- orbsize.

## O198 -- resonance moment base case r=1: T_1 = m-1 (sqrt-p-free Salem-Zygmund L2-mass), and the
ResonanceConjecture holds UNCONDITIONALLY at depth r=1 for m>=2 (EXTEND-proven on
GaussPhaseResonance, NON-moment, grep-confirmed-MISSING, frontier-movement)

GaussPhaseResonance (#407) names the sqrt-p-free free variable of the prize: the phase-sum
phaseSum u r c (over r-tuples of nonzero residues summing to c, of prod u(X i)) and the deep
resonance moment T r = resonanceMoment u r = sum_c |phaseSum u r c|^2. It proves only T r >= 0 + a
vanishing-iff criterion, and states the open ResonanceConjecture T r <= (2 m log m)^r at binding
depth r ~ log m. It pins NO value of T r. grep-confirmed-MISSING: no in-tree phaseSum_one / T_1
value / r=1 discharge. This brick supplies the EXACT base case r=1. MECHANISM (NOT a moment/energy
move; the r=1 filter collapses to a singleton): the filter {X : Fin 1 -> ZMod m | forall i, X i !=
0 and sum X = c} is the singleton {fun _ => c} for c != 0 and empty for c = 0, so phaseSum u 1 c =
(if c = 0 then 0 else u c), hence T_1 = sum_{c != 0} |u c|^2; for a unit-phase vector u (|u l| = 1,
the Gauss-sum unit phases u_l = tau(chi^l)/sqrt p) this is EXACTLY m-1. This is the sqrt-p-free core
of the Salem-Zygmund / Parseval L2-mass sum_j |tau(chi^j)|^2 / m^2 = (m-1) p / m^2 (the verified
avg |eta_b|^2 ~ n second-moment fact, p divided out). At r=1 the conjecture m-1 <= 2 m log m holds
unconditionally for m >= 2 (2 m log m >= 2 m log 2 >= 1.386 m >= m >= m-1). PROBE
scripts/probes/probe_resonance_moment_r1.py (ONE sweep, random unit phases, m=3..255, never n=q-1):
phaseSum u 1 c = u(c) for c!=0 / 0 for c=0, and T_1 = m-1 EXACT; VERDICT PASS. FORMALIZED
Frontier/_ResonanceMomentBaseCase.lean (single-file lake-env-lean exit 0 + in-graph lake-locked
8314 jobs exit 0; axiom-clean subset of {propext, Classical.choice, Quot.sound}, no
sorry/axiom/native_decide on all 4 printed): mem_phaseSum_one_filter (the r=1 filter membership =
singleton criterion), phaseSum_one (HEADLINE: phaseSum u 1 c = if c=0 then 0 else u c),
resonanceMoment_one (T_1 = sum_{c!=0} |u c|^2), resonanceMoment_one_of_unit (T_1 = m-1 for unit
phases), resonanceConjecture_one_of_unit (the conjecture holds at r=1 for m>=2). Builds DIRECTLY on
GaussPhaseResonance.phaseSum/resonanceMoment/ResonanceConjecture (does NOT re-declare them). Does
NOT close CORE: this is the TRIVIAL Parseval rung r=1, FAR below the binding depth r ~ log m where
the conjecture is the recognized open Gauss-period/BGK content. NOT a census/orbit/spectrum object
(different lever: the sqrt-p-free Gauss-phase resonance moment). NO capacity / beyond-Johnson /
sub-linear / closure claim; ASYMPTOTIC GUARD cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n
log(p/n)) UNCHANGED/OPEN. Author Sol, co-author wakesync.
-- resr1.

## O199 -- the STRUCTURED single-line sparse-zero floor at rate rho=1/4 is 5n/8 for ALL mu>=3:
s*(2^mu, n/4) >= n/2 + 2^{mu-3} = 5*2^{mu-3} = 5n/8 (super-Johnson, since sqrt(kn)=n/2 at rho=1/4);
the general-mu lift of FloorAsymptoticRadius's n=8,16 decide certificates (EXTEND-proven on
StructuredUncertaintySharpFloor, NON-moment, grep-confirmed-MISSING, frontier-movement)

StructuredUncertaintySharpFloor (#407) proves the PER-SPIKE structured floor
card_witnessVal_zero_ge: s*(2^mu, k) >= n/2 + 2^e for EVERY spike exponent e<=mu-1, via the witness
f(x) = (x^{n/2}+1)*(x^{2^e} - (zeta^{j0})^{2^e}) (j0 even, j0 < 2^{mu-e}); the binomial half-coset
(n/2 zeros) plus 2^e disjoint poly-roots. It pins the per-e bound and (sStar_ge_half_add_pow_two)
the lower bound, and FloorAsymptoticRadius brute-confirms s*=5n/8 ONLY at n=8,16 by decide. It does
NOT state the rate-rho=1/4 OPTIMAL-spike closed form for general mu. grep-confirmed-MISSING: no
in-tree theorem closes the optimal-spike floor to 5n/8 for all mu, nor proves it super-Johnson at
every tower level. This brick supplies it. MECHANISM (NOT a moment move; pure spike-optimization +
Nat closed form): at rho=1/4, k=n/4=2^{mu-2}, the largest power-of-two spike <= k-1=2^{mu-2}-1 is
2^{mu-3} (e=mu-3, valid for mu>=3, fits e<=mu-1, even residue j0=0 < 2^{mu-e}=8); specialize
card_witnessVal_zero_ge at (e=mu-3, j0=0) and close the Nat identity 2^{mu-1}+2^{mu-3}=5*2^{mu-3}=
5*2^mu/8. PROBE scripts/probes/probe_5n8_general.py (ONE sweep, exact int, mu=3..21, thin 2-power
mu_n, rho=1/4 fixed, never n=q-1): optimizer e*=mu-3, floor = n/2+2^{mu-3} = 5n/8 EXACT, and
5n/8 > sqrt(kn)=n/2 strictly; VERDICT PASS at all 19 levels. FORMALIZED
Frontier/_StructuredFloorRateQuarter.lean (single-file lake-env-lean exit 0 + in-graph lake-locked
1497 jobs exit 0; axiom-clean subset of {propext, Classical.choice, Quot.sound}, no
sorry/axiom/native_decide on all 5 printed): half_add_quarter_spike_eq
(2^{mu-1}+2^{mu-3}=5*2^{mu-3}), five_quarter_spike_eq_5n8 (=5*2^mu/8),
structuredFloor_rate_quarter_ge (HEADLINE: the 5*2^{mu-3}
floor on the witness zero-count), structuredFloor_rate_quarter_ge_5n8 (the 5n/8 closed form),
structuredFloor_rate_quarter_super_johnson (n/2 < 5*2^{mu-3}, super-Johnson for all mu>=3). Builds
DIRECTLY on card_witnessVal_zero_ge (does NOT re-declare it). Does NOT close CORE: this is a LOWER
bound on the SINGLE-LINE root count s* (max agreement of ONE far line with ONE codeword), which
UncertaintyTwoPowerExtremal.SingleLineNotList already records is the WRONG object for the prize --
the single n/2-agreement line does NOT lift to a large LIST (contributes only O(1) codewords); the
prize delta* is the LIST radius. So 5n/8 is a super-Johnson floor on a single-line object the
program brackets AWAY from CORE. Thinness-essential (rule 3): the witness binomial + spike both
factor through 2-power-order elements (Tao forbids it over prime-order groups), a refutation of a
would-be Johnson UPPER bound on s*, not a thinness-monotone CORE method. NOT a moment/census/orbit
object (different lever: the structured uncertainty single-line root count). NO capacity /
beyond-Johnson-delta* / sub-linear-M / closure claim; the cliff-at-n/2 (the delta*/incidence object,
NOT s*) is UNTOUCHED -- ASYMPTOTIC GUARD compliant. CORE M(mu_n) <= C sqrt(n log(p/n))
UNCHANGED/OPEN. Author Sol, co-author wakesync.
-- 5n8.

## O200 -- resonance moment r=2 rung: phaseSum convolution collapse + T_2 >= (m-1)^2 (conj-symm unit phases)
EXTEND-PROVEN NON-MOMENT-LADDER brick on the Gauss-phase resonance lever (GaussPhaseResonance #407
+ the r=1 base case _ResonanceMomentBaseCase). The base file pins phaseSum u 1 c + T_1 = m-1 (the
trivial Parseval rung); this is the NEXT rung r=2, the first genuinely non-diagonal phase-sum (a
restricted convolution of the unit phases). grep-confirmed-MISSING: no in-tree phaseSum_two / r=2
value. PROBE scripts/probes/probe_phasesum_two.py + probe_phasesum_two_c0.py (ONE sweep, random unit
phases, m=3..15, NEVER n=q-1): the convolution form phaseSum u 2 c = sum_{a!=0,c-a!=0} u(a)u(c-a)
PASSES at all m; for conjugate-symmetric unit phases (u(-a)=conj(u(a))) phaseSum u 2 0 = m-1 EXACT
(REAL) at m=3,5,7,9,11,15; VERDICT PASS. FORMALIZED Frontier/_ResonanceMomentRTwo.lean (single-file
lake-env-lean exit 0 + in-graph lake-locked 8314 jobs exit 0; axiom-clean subset of {propext,
Classical.choice, Quot.sound}, no sorry/axiom/native_decide on all 3 printed):
mem_phaseSum_two_filter (the r=2 filter membership: X0!=0, X1!=0, X0+X1=c), phaseSum_two (HEADLINE:
the off-diagonal convolution collapse, via Finset.sum_nbij' reindexing by the first coordinate),
phaseSum_two_zero_of_conjSymm (phaseSum u 2 0 = m-1 for conjugate-symmetric unit phases, via
Complex.mul_conj +
normSq_eq_norm_sq + card_erase), resonanceMoment_two_ge_of_conjSymm (HEADLINE: T_2 >= (m-1)^2, via
Finset.single_le_sum at c=0). Builds DIRECTLY on GaussPhaseResonance.phaseSum/resonanceMoment (does
NOT re-declare them). Does NOT close CORE: r=2 is the SECOND rung, FAR below binding depth r ~ log m
where the ResonanceConjecture is the recognized open Gauss-period/BGK content. The lower bound
(m-1)^2 <= (2 m log m)^2 is CONSISTENT with the conjecture, not a proof of it; it is a genuine r=2
floor above the trivial T_2 >= 0 (the squared diagonal mass), NOT an upper bound and NOT a
concentration result. NOT a moment/census/orbit/spectrum object (different lever: the sqrt-p-free
Gauss-phase resonance moment). NO capacity / beyond-Johnson / sub-linear / closure claim; ASYMPTOTIC
GUARD cliff-at-n/2 UNTOUCHED. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. Author Sol,
co-author wakesync.
-- resr2.

## O201 -- dilation homogeneity of the monomial divided difference: the orbit-law eigenvector mechanism
EXTEND-PROVEN NON-MOMENT structural brick on the divided-difference / Schur-ratio lever
(SchurLagrangeBridge.dividedDifferencePow + DividedDifferenceDeflation.ddVal). Far-line bad-gamma
is the Schur ratio gamma = -dividedDifferencePow R v a / dividedDifferencePow R v b (lalalune #444
08:46), and the orbit law #bad = 1 + (n/2)*O follows from this ratio being a DILATION EIGENVECTOR:
gamma(g.T) = g^(a-b) gamma(T). This brick formalizes the algebraic core of that eigenvector law,
which was grep-confirmed MISSING in tree (no dilation/scaling law for dividedDifferencePow). PROBE
(scripts/probes/probe_ddval_dilation.py, exact Q, 2000 random node sets |R|=2..6, random dilation g,
degrees b=0..8, NEVER n=q-1): the homogeneity dividedDifferencePow R (g.v) b = g^b (g^(|R|-1))^-1
dividedDifferencePow R v b PASSES at all trials, and the consequence gamma(g.v) = g^(a-b) gamma(v)
PASSES at all trials. FORMALIZED Frontier/_DividedDifferenceDilation.lean (single-file lake-env-lean
exit 0 + in-graph lake-locked 1704 jobs exit 0; axiom-clean subset of {propext, Classical.choice,
Quot.sound}, no sorry/axiom/native_decide on all 3 printed): prod_dilate_diff (dilated difference
product collapses by g^(|R|-1), via prod_const + card_erase), dividedDifferencePow_dilate (HEADLINE:
dividedDifferencePow R (g.v) b = g^b (g^(|R|-1))^-1 dividedDifferencePow R v b for g != 0, proven
termwise over the in-tree def via field_simp), schurRatio_dilate_eigen (the Schur ratio scales by
g^(a-b): the (g^(|R|-1))^-1 factor cancels between numerator a and denominator b, the orbit-law
mechanism). Builds DIRECTLY on the in-tree dividedDifferencePow (does NOT re-declare it). Does NOT
close CORE: this is the ALGEBRAIC scaling mechanism beneath the orbit law (the dilation-coset
structure of the bad-gamma set), NOT a bound on #orbits(m) (the open cyclotomic-collision growth law
= the BGK/BCHKS wall). The eigenvector law is p-independent, char-agnostic, NOT thinness-essential
(it is pure Lagrange/Schur algebra over any field). NOT a moment/census/spectrum/orbit-count object
(different lever: the divided-difference dilation homogeneity, the SIZE/coset half of #bad =
1 + (n/2)*O, complementary to the orbit-COUNT growth and the orbit-SIZE=n cardinality bricks). NO
capacity / beyond-Johnson / sub-linear / closure claim; ASYMPTOTIC GUARD cliff-at-n/2 UNTOUCHED.
CORE
M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. Author Sol, co-author wakesync.
-- dilhom.

## O202 -- the SUNFLOWER (common-M-core) dilation-pencil count: r*(r-M)+M <= |G| and (r-M)^2 < |G|
EXTEND-PROVEN NON-MOMENT structural brick on the pencil/incidence-geometry lever (LEVER K), the
clean GRADED generalization of _KelleyOwenDilationPencil.pencil_card_core (the M=1 trinomial face,
r*(r-1)+1 <= |G|). Both _KelleyOwenDilationPencil and PencilAutocorrRootBound state the general-t
degradation ONLY in prose (the pencil is k-dimensional, members share up to ~k roots, the
double-count then gives only r^2 ~ k*N = JOHNSON, never sub-Johnson); it was grep-confirmed NEVER
formalized. This brick formalizes the exactly-generalizing SUNFLOWER rung: r blocks each size r
sharing a COMMON core T (|T|=M, p in T), pairwise meeting in exactly T, force r*(r-M)+M <= |G|,
which RECOVERS pencil_card_core at M=1 (r*(r-1)+1 <= |G|) and yields sqrt extraction (r-M)^2 < |G|,
i.e. r <= M + sqrt(|G|) (Johnson radius + core-offset M; M=1 gives Kelley-Owen 1+sqrt|G|, the prize
core M ~ n/2 pushes the offset to the Johnson scale, matching autocorr_ge_coset_core's M(S) >= n/2).
PROBE (scripts/probes/probe_sunflower_pencil.py, exact, genuine sunflowers r,M over n=8..64, NEVER
n=q-1): every common-M-core family satisfies r*(r-M)+M <= n and (r-M)^2 < n, recovering the M=1
numbers; AND scripts/probes/probe_graded_pencil_core.py sweeps the pairwise-<=M case (no common T,
min feasible union over random admissible families) confirming the graded root bound r(r-1)+1 <= M*n
and Johnson (r-1)^2 < M*n hold there too. FORMALIZED Frontier/_PencilSunflowerCore.lean (single-file
lake-env-lean exit 0 + in-graph build exit 0; axiom-clean subset of {propext, Classical.choice,
Quot.sound}, no sorry/axiom/native_decide on both printed): pencil_sunflower_core (HEADLINE:
r*(r-M)+M <= |univ| via T-punctured-block pairwise disjointness, card_sdiff_of_subset + card_biUnion
+ card_union_of_disjoint, the same mechanism as pencil_card_core with {p} replaced by the core T),
pencil_sunflower_sqrt_bound ((r-M)^2 < N from r*(r-M)+M <= N, 1 <= M the nonempty-core condition).
Builds DIRECTLY on _KelleyOwenDilationPencil (does NOT re-declare pencil_card_core). HONEST SCOPE:
the sunflower hypothesis (a SINGLE common core T for all pairs) is STRICTLY STRONGER than the
prize-relevant pairwise-<=M bound (the form pencil_overlap_le_of_autocorr delivers, with possibly
different per-pair intersections); so this is the clean sunflower RUNG of the degradation, NOT the
general-position Fisher bound (r^2 ~ M*N by Cauchy-Schwarz, no common T, the harder separate brick).
Does NOT close CORE: it is a graded combinatorial count that CAPS the dilation-pencil route at
Johnson + core-offset, NOT a sub-Johnson separation. p-independent, char-agnostic, NOT
thinness-essential (pure Finset disjoint-union counting). NOT a moment/census/spectrum/orbit object
(different lever: the pencil/incidence sunflower count). NO capacity / beyond-Johnson / sub-linear /
closure claim; ASYMPTOTIC GUARD cliff-at-n/2 UNTOUCHED. CORE M(mu_n) <= C sqrt(n log(p/n))
UNCHANGED/OPEN. Author Sol, co-author wakesync.
-- sunflower.

### O203 — CENSUS MULTIPLICITY UPPER CAP: mult(γ) ≤ C(|A_γ|, a), the exact upper companion to mult_ge_choose_of_aligned_superset (sol, 2026-06-16)

CensusScalarPartition.mult_ge_choose_of_aligned_superset gave only the LOWER bound on the per-scalar
census multiplicity mult(γ) := #(alignedSetsForScalar dom k a u₀ u₁ γ): a deep aligned set of size
|A_γ| owns all its a-subsets through one non-degenerate tuple, so C(|A_γ|-(k+1), a-(k+1)) ≤ mult(γ).
The MATCHING UPPER cap (mult to a SINGLE agreement-set binomial) was grep-confirmed MISSING.

* **mult(γ) ≤ C(|A_γ|, a)** (`alignedSetsForScalar_card_le_agreement_choose`), axiom-clean. Under the
  common-explainer hyp (the deg-<k codeword c matches the γ-pencil on every member of the γ-fibre,
  i.e. c explains the maximal aligned set A_γ = agreementSet dom u₀ u₁ γ c), every member is an
  a-subset of A_γ via aligned_subset_agreementSet_of_agree, so alignedSetsForScalar γ ⊆
  (A_γ).powersetCard a, and card_le_card + card_powersetCard give the binomial cap.
* **Bracket** (`alignedSetsForScalar_card_bracket`): with the in-tree lower bound this pins mult(γ) in
  [C(|A_γ|-(k+1), a-(k+1)), C(|A_γ|, a)] exactly.
* **Why it matters**: this is the per-scalar incidence cap the CensusDomination obligation consumes.
  #alignableSets = Σ_γ mult(γ); a distinct-γ cap #pinned ≤ P PLUS a max-agreement-size cap |A_γ| ≤ s₀
  give #alignableSets ≤ P·C(s₀,a) = K, the K that CensusDominationWeld welds to δ*. Only the LOWER
  half was in tree; this supplies the structural UPPER half.
* **Honesty**: field-universal census combinatorics, NOT thinness-essential, NOT moment/orbit/spectrum/
  resonance/pencil, NOT a CORE closure or refutation. The open content (does |A_γ| stay small, the
  distinct-γ cap) is UNTOUCHED. NO capacity/beyond-Johnson/sub-linear claim; cliff-at-n/2 untouched.
  Probe scripts/probes/probe_mult_le_agreement_binom.py (thin μ_n, μ=3..7, p≫n³, never n=q-1): bracket
  holds all rows, tight at the generic deep agreement set; anchors C(5,3)=10, C(6,4)=15 match
  AgreementSetMaximal. Frontier/_MultUpperAgreementBinom.lean, single-file lake env lean exit 0 +
  in-graph lake build (3092 jobs) exit 0; #print axioms ⊆ {propext, Classical.choice, Quot.sound} on
  all 3 (subset_agreement_powersetCard, card_le_agreement_choose, card_bracket), no sorry/axiom/
  native_decide. CORE M(μ_n) ≤ C√(n log(p/n)) OPEN.

## O204 -- char-p r=3 DC-Wick rung fused with the explicit wraparound spur: kappa6_charp = 40n + S
and the EXACT (P2-Slack) gate kappa6 <= 45n^2 <=> S <= 45n^2-40n; PROBE: gate holds at prize scale (sol, 2026-06-16)
RESULT (FUSION + prize-scale-essential constraint, NOT a CORE closure). The char-0 r=3 rung
(Kappa6R3DCWickRung: kappa6=40n<=45n^2 from char-0 E3=15n^3-45n^2+40n) and the abstract spur slack
route (_wf6P2_charp_lamleung_slack: E_r^Fp = E_r^Z + Spur_r, open residual S <= ceiling-Z) existed
SEPARATELY. This brick FUSES them at r=3 on the cumulant the rung consumes: with E3^Fp =
(15n^3-45n^2+40n)+S, kappa6_charp_eq gives kappa6 = 40n+S, and kappa6_charp_le_iff_spur_le gives the
EXACT gate kappa6<=45n^2 <=> S<=45n^2-40n (= ceiling-Z, the r=3 (P2-Slack); spur_slack_eq_ceiling_
sub_charZero). kappa6_charp_le_of_spur_zero recovers the proven char-0 rung when S=0.
PROBE (exact int E3^Fp = sum_s T3(s)T3(-s) over PROPER mu_n in F_p, n=4..32, NEVER n=q-1): at the
PRIZE SCALE p>=n^4 the spur VANISHES, S=Spur_3(p)=0 EXACTLY at 9 instances (n=4 p=257,509,1021;
n=8 p=4073,11593,32801; n=16 p=65537,262193,1048609; Fermat+non-Fermat, beta=4,4.5,5) -> the gate
holds with full margin + char-0 h3 is EXACT there. At SMALL p the gate FAILS: S>45n^2-40n by up to
12.97x (S=141120>10880 at n=16 p=97), last violating prime p~n^2.3 (p=41 n=8, p=641 n=16), last
prime with any S>0 is <n^4 (p=13,313,41521 for n=4,8,16) -- all BELOW prize scale.
MECHANISM/CONSTRAINT: a count-unbalanced zero-sum 6-tuple needs its integer-lift root sum to be a
NONZERO multiple of p; the house of a nonzero 6-term 2^a-th-root sum is bounded, so such p sit below
a polynomial threshold. The slack route is NOT prime-uniform: FAILS at small p, holds at prize scale
where S=0. The r=3 rung is PRIZE-SCALE-ESSENTIAL (the char-p analogue of thinness-essentiality);
any prime-uniform / thickness-monotone version is FALSE. Axiom-clean {propext, Classical.choice,
Quot.sound} on all 5 (single-file lake-env-lean + in-graph 3297 jobs); no sorry/axiom/native_decide.
Does NOT prove S<=45n^2-40n for general p (open char-p count) and touches NO r>3 rung. CORE
M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## O205 -- di Benedetto edge-saving SENSITIVITY: per-unit t3-decrease buys 1/36, per-unit t2-decrease
buys 1/144, EXACT for all (t2,t3); t3-step = 4x t2-step (the t3-dominance lever-selection) (sol, 2026-06-16)
RESULT (EXTEND-proven NON-MOMENT structural brick, NOT a CORE closure). _DiBenedettoNearSidon
Improvement.lean pins diBenedettoSaving(t2,t3)=(10-2t3-t2/2)/72, its baseline (31/2880), near-Sidon
value (1/24), antitone monotonicity, the 1/24 CEILING, and the conditional charSum bound -- but the
file docstring asserts the LEVER-SELECTION rationale ("t3 is the dominant input, sensitivity -2/72,
four times t2's -1/144") ONLY IN PROSE. grep-confirmed: no 1/36 / 1/144 sensitivity statement
anywhere in ProximityGap. This brick formalizes that quantitative core (the WHY-attack-E3-not-E2 of
the whole near-Sidon improvement): diBenedettoSaving_t3_step (sav t2 t3 - sav t2 (t3+1) = 1/36),
diBenedettoSaving_t2_step (sav t2 t3 - sav (t2+1) t3 = 1/144), both for ALL (t2,t3) (the saving is
affine, so finite differences = exact slopes); diBenedettoSaving_t3_dominates_t2 (the t3-step = 4x
the t2-step, the exact 4x dominance) + the strict version + the two absolute slopes (-1/36, -1/144).
PROBE (exact Fraction, all (t2,t3) in {2,49/20,5,3}x{3,4,7/2,9/2}, NEVER nq-1): per-unit t3-decrease
= 1/36 EXACT, per-unit t2-decrease = 1/144 EXACT, ratio = 4 EXACT, baseline 31/2880 + near-Sidon
1/24 anchors match. VERDICT PASS. Axiom-clean {propext, Classical.choice, Quot.sound} on all 6
(single-file lake-env-lean + in-graph) -- pure affine ring/linarith over R; no sorry/axiom/native_
decide. HONESTY: field-universal exponent bookkeeping, NOT thinness-essential, NOT a moment/census/
orbit/pencil/resonance object. It identifies the best lever WITHIN the energy method, which the
parent file ALREADY proved is capped at saving <= 1/24 < 1/2 (12x short of the prize cancellation
exponent) -- so this does NOT push the frontier past the energy ceiling. Touches NEITHER delta* NOR
the cliff-at-n/2 incidence object. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.


## O206 — CensusDomination SUFFICIENCY: the two census sub-obligations IMPLY the $1M Prop (the weld's hypothesis discharged)
LANE censussuff. The CensusDominationWeld pins the deployed delta* = 1 - r/2^mu CONDITIONAL on the
named Prop CensusDomination dom k a0 K (every stack <= K alignable a-sets at every band a >= a0),
and AlignableLePinnedMaxMult.alignableSets_card_le_budget proved the PER-BAND incidence cap
#alignableSets <= K from a distinct-gamma cap P, a per-scalar mult cap M, and P*M <= K. But the two
were NEVER connected: every site (CensusDominationWeld x2, FieldSizeThresholdReduction) CONSUMES
CensusDomination as a black-box hyp -- grep-confirmed NO theorem PRODUCES it from the per-band
sub-bounds. The brief flags exactly this (the count/census equivalence "asserted but NEVER proven")
as a real brick. New file Frontier/CensusDominationSufficiency.lean supplies the sufficiency
reduction: (1) censusDomination_iff_alignableSets -- the inlined CensusDomination filter IS the
alignableSets census object (Lean rfl-certified DEFINITIONAL equality, stronger than any numeric
probe); (2) censusDomination_of_caps (HEADLINE) -- a band-UNIFORM distinct-gamma cap P + a
band-uniform per-scalar mult cap M + P*M <= K yield CensusDomination dom k a0 K, via
alignableSets_card_le_budget under the band quantifier; (3) censusDomination_of_caps_exact -- the
K = P*M specialization. So the $1M Prop the weld consumes is now IMPLIED (not just consumed) by the
two in-tree census sub-obligations the cluster built (distinct-gamma bound + per-scalar mult bound),
closing the assembly. PROBE scripts/probes/probe_census_sufficiency_uniform.py (planted off-codeword
words on PROPER thin mu_n, n=8,16, beta=4,5, p >> n^3, p == 1 mod n, NEVER n=q-1): a single
band-uniform (P, M) DOMINATES #alignableSets at EVERY band a in [a0, n] at once (n=16: one P=1,
M=5005 caps bands a=4..7 with #alignableSets = 455,1365,3003,5005 = clean agreement-binomials), so
censusDomination_of_caps's hypotheses are SATISFIABLE / NON-VACUOUS at the prize regime, AND the
per-band #alignableSets <= #pinned*maxMult engine holds at every band. VERDICT PASS. Axiom-clean
{propext, Classical.choice, Quot.sound} on all 3 (single-file lake-env-lean exit 0 + in-graph
lake-locked 8370 jobs exit 0); no sorry/axiom/native_decide. HONESTY (rules 3,6): NOT a CORE
closure, NOT thinness-essential -- pure LOGICAL assembly (forall-intro over bands + the proven
per-band product cap), field-universal and thickness-independent. Does NOT supply P (distinct-gamma
cap at prize band) NOR M (per-scalar mult cap at prize band); BOTH stay open. It DISCHARGES the
weld's black-box CensusDomination hypothesis from the in-tree per-band incidence cap -- the
sufficiency direction, a genuine missing link, not a re-mapped dead face / moment / orbit /
resonance / pencil re-derivation. Touches NEITHER delta* climb NOR the cliff-at-n/2 incidence
object. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O207 (lane ratioperm): residual-RATIO is PERMUTATION-INVARIANT in the tuple => the open
## distinct-gamma (delta*-governing) count factors through (k+1)-SUBSETS: #ratioImage <= C(n,k+1),
## a (k+1)!-fold tightening of the in-tree ratioImage_card_le_tuples. Push, axiom-clean.
PinnedScalarRatioImage reduced the open delta*-governing distinct-gamma count to the residual-ratio
image (#pinnedScalars <= #ratioImage) with the CRUDE a-priori ceiling #ratioImage <= #{injective
(k+1)-tuples} = n(n-1)...(n-k) (ratioImage_card_le_tuples). MECHANISM (pure linear algebra, NOT
orbit-law/Schur, the live cluster): residual = det(borderedMatrix), and permuting the tuple permutes
the matrix ROWS, scaling det by Perm.sign sigma (a +-1 unit) via Matrix.det_permute. So residual is
permutation-EQUIVARIANT (residual_comp_perm: residual (t o sigma) = sign sigma * residual t); the
SAME sign appears in numerator R0 and denominator R1 of the ratio gamma = -R0/R1 and CANCELS =>
residualRatio_comp_perm: residualRatio (t o sigma) = residualRatio t (the headline). Hence the ratio
map factors through the underlying (k+1)-element SET: #ratioImage <= C(n,k+1)
(ratioImage_card_le_choose), and #pinnedScalars <= C(n,k+1) (pinnedScalars_card_le_choose) -- a
(k+1)!-fold improvement over the in-tree pinnedScalars_card_le_tuples. PROBE
(/tmp/probe_ratio_perm_invariant.py, ONE sweep, PROPER thin 2-power mu_n, p == 1 mod n, prize regime
p >> n^3 beta=4..5, OFF-code planted stacks, n=8,16,32, k=1,2,3, ALL perms of each subset, NEVER
n=q-1): perm-invariance holds 100% of runs; #ratio values <= C(n,k+1) every run, TIGHT at k=1 (n=8:
exactly 28 = C(8,2)), a real reduction vs falling factorial (n=8,k=3: 70=C(8,4) vs 1680 ordered,
24x fewer). 7 theorems axiom-clean {propext, Classical.choice, Quot.sound} (single-file lake-env
+ in-graph lake-locked); no sorry/axiom/native_decide. HONESTY (rules 3,6 + ASYMPTOTIC GUARD): NOT a
CORE closure, NOT thinness-essential -- field-universal combinatorics (determinant sign-cancellation
holds over every field, any k, independent of thickness). It TIGHTENS the a-priori distinct-gamma
ceiling from the ordered-tuple count to the subset count; it does NOT bound the ratio image below
C(n,k+1), and C(n,k+1) ~ n^{k+1} is still far above the sqrt(n) prize target (the cyclotomic content
that would collapse the image to O(sqrt n) values stays OPEN). Bound is a binomial in n, not delta*
/incidence object; cliff-at-n/2 UNTOUCHED. NOT a moment/orbit/census/resonance/pencil re-derivation
or a re-mapped dead face. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O208 (lane geommintsharp): A6deep minor-degree budget SHARPENED for complete-homogeneous
## (geometric) readout rows: g_a*g_{b-1} - g_{a-1}*g_b = X^a*g_{b-a-1}, deg = b-1 < D, HALVING
## the generic 2D Bezout budget and landing |forcedGammaImage| BELOW the prize budget n for a
## fixed monomial direction. Push 0ce1addbd..<new>, axiom-clean.
RESULT: EXTEND-PROVEN, NON-MOMENT, on the brief's named determinantal/Bezout lever (non-saturated
tonight). _CoreA6deep_MinorTractability.minorPoly_natDegree_le gives the GENERIC Bezout budget
deg(pa*pbm - pam*pb) <= 2D -- a factor 2 ABOVE the prize budget n (the open MinorImageLeBudget Prop
asks |forcedGammaImage| <= n; A6deep delivers only <= 2n per direction). But the readout rows are
generic: in the divided-difference dlog substrate they are complete-homogeneous (geometric) Gauss-
period sums g_c = 1+X+...+X^c, the offset row being the CONSECUTIVE g_{c-1}. For these the minor
collapses to ONE monomial-times-geometric term:
  geomMinor_eq : g_a*g_{b-1} - g_{a-1}*g_b = X^a*g_{b-a-1}  (1<=a<b),
hence geomMinor_natDegree : deg = b-1 = D-1, and geomMinor_natDegree_lt : deg < b=D. SHARP, < D,
strictly below A6deep's 2D. At D=span=n the per-direction minor-locus root count (hence
|forcedGammaImage|) is < n = the prize budget q*eps* ~ n, discharging MinorImageLeBudget FOR the
complete-homogeneous readout structure (a fixed monomial direction). PROOF ENGINE: both sides times
(X-1)^2 agree by the closed form g_c*(X-1)=X^{c+1}-1 (geom_sum_mul) + ring; cancel (X-1)^2 != 0 in
the integral domain F[X]. PROBE (exact, sympy): identity verified 1<=a<b<=11 (both a<b and the
antisymmetric b<a form -u^b*g_{a-b-1}); generic rows give deg 2D (no cancellation), geometric rows
give deg b-1 at cascade scales b in {8,16,32,64} (deg 7,15,31,63 -- all < D). Theorems
(axiom-clean {propext, Classical.choice, Quot.sound}, single-file + in-graph 3315 jobs): geomPoly,
geomPoly_mul_X_sub_one, geomPoly_natDegree, geomMinor_eq (HEADLINE), geomMinor_natDegree,
geomMinor_natDegree_lt, geomMinor_natDegree_le_pred_span, geomMinor_ne_zero (non-vacuity).
HONESTY (rules 1,3,4,5,6 + ASYMPTOTIC GUARD): NOT a CORE closure -- discharges the budget clause
for the structured complete-homog readouts and STILL inherits A6deep's OPEN residual, the direction-
uniformity at the binding depth (PerDirectionParam direction-select / BCHKS 1.12 budget input),
UNTOUCHED here. NOT thinness-essential as a CORE method (field-universal F[X] algebra; thinness
only via the dlog structure that makes the readouts geometric -- it is a tractability cert of a per-
direction count, the thinness lives in the unresolved direction-uniformity). NOT a moment/Wick (rule
5), NOT a census/orbit/resonance/pencil/spur re-derivation, NOT a re-mapped dead face. NO capacity /
beyond-Johnson / sub-linear / growth-law claim; cliff-at-n/2 (the delta*/incidence) UNTOUCHED.
CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O211 (lane survivalceiling): the A3 dedup-slack has a SURVIVAL CEILING that fractionally
## vanishes. Lever 2 of the issue body's "TWO non-BCHKS levers" (dedup-strictness at log depth):
## _CoreA3_BackwardProof reduces the prize ESCAPE to whether D <= Sigma_r is strict (escape) or
## vanishing (wall) at binding depth r ~ log n; _DedupSlackStrictButVanishing answered "strict but
## fractionally vanishing" only via three hand-decided anchors (n in {8,16,32,64}), NO structural
## law. This supplies the structural mechanism. Push <base>..<new>, axiom-clean.
RESULT: EXTEND-PROVEN, NON-MOMENT, p-independent. Over the thin dyadic mu_{2m} with the in-tree
spectrum N_r = specCount m r = sum_{k=r(2), k<=min(r,2m-r)} C(m,k)2^k, at binding depth r<=m
(r=log2 n <= n/2 = m at prize scale):
  (1) specCount_ge_top: SURVIVAL LOWER BOUND N_r >= C(m,r)2^r (the top weight class k=r survives;
      single_le_sum over the filtered range, min(r,2m-r)=r).
  (2) dedupSlack_le_survivalCeiling: SLACK CEILING slack = C(2m,r)-N_r <= C(2m,r)-C(m,r)2^r =:
      survivalCeiling, by Nat.sub_le_sub_left from (1) ALONE -- Nat truncation, no upper bound on
      N_r needed.
  (3) survivalLead_mul_fallProd_eq: the EXACT cross-product identity C(m,r)2^r * prod_{i<r}(2m-i)
      = C(2m,r) * prod_{i<r}(2m-2i), i.e. lead/sigma = prod(2m-2i)/(2m-i), each factor 1-i/(2m-i)
      -> 1, so the ceiling fraction 1 - lead/C(2m,r) -> 0. Proven by cancelling a common r! via
      descFactorial_eq_prod_range on both lead (=evenProd/r!) and sigma (=fallProd/r!).
  (4) evenProd_le_fallProd + survivalLead_le_sigma + survivalCeiling_lt_sigma: the ceiling is a
      PROPER fraction of the multiset count (non-vacuous), per-factor 2m-2i <= 2m-i (gap exactly i).
  (5) anchors n=16 (ceiling 700 >= prior exact slack 587), n=32 (ceiling 61600 >= 57088); ceiling
      fraction strictly decreases f_ceil(16)>f_ceil(32) by exact Nat cross-mult.
PROBE: scripts/probes/probe_dedup_survival_ceiling_vanishing.py -- survival N_r/C(n,r) at r=log2 n
sweeps 0.714 (n=8) -> 0.99990 (n=2^21), slack-fraction strictly decreasing for all n>=16 tested,
the leading model lead=C(m,r)2^r with N/lead -> 1 and lead/C -> 1 (squeeze lead<=N_r<=C). VERDICT:
the dedup is STRICT but its slack lives UNDER a fractionally-vanishing exact-product ceiling at the
binding depth -- leaning WALL structurally, not by 3-point coincidence. HONEST SCOPE: bounds slack
above at binding depth r<=m ONLY; does NOT bound D/Sigma_r/m* at the BUDGET scale ~n, does NOT close
BCHKS 1.12, NO capacity/beyond-Johnson/growth-law claim, cliff-at-n/2 UNTOUCHED. CORE M(mu_n) <= C
sqrt(n log(p/n)) UNCHANGED/OPEN. New: Frontier/_DedupSurvivalCeiling.lean (10 thms axiom-clean).

## O213 (lane stepfiber): the GV rep-count fibre is a POLYNOMIAL ROOT COUNT of an explicit
## shifted-power polynomial -- r(c) <= (shiftedPowPoly n c).natDegree = n, the Stepanov-consumable
## bridge the three in-tree fibre forms only ASSERTED in prose (NON-MOMENT structural CORE lever).
LANE: the Stepanov/descent non-moment lever (StepanovAuxFramework's honestly-recorded OPEN KERNEL:
"an auxiliary polynomial ... constructed from the relations x^n=1 and (c-x)^n=1, whose degree is
bounded independently of r(c)"). The three proven fibre reformulations -- repCount_eq_fiber_card
(RepCountFiber), repCount_eq_curve (RepCountCurve), repCount_eq_shiftedPower (RepCountShiftedPower)
-- ALL read r(c) = #{w in mu_n : (1+w)^n = c^n} and ALL flag, IN PROSE ONLY, the polynomial reading
"the common-root count of X^n-1 and (1+X)^n - c^n, exactly what a resultant/Stepanov auxiliary acts
on". GREP-CONFIRMED MISSING: no theorem connects the fibre cardinality to a polynomial root/degree
count. THE structurally-missing bridge.
SHIPPED Frontier-adjacent ArkLib/.../RepCountFiberPolyBound.lean (5 thms, axiom-clean {propext,
Classical.choice, Quot.sound}, single-file lake-env-lean + in-graph lake-locked 3299 jobs exit 0):
  (1) shiftedPowPoly n c := (X + C 1)^n - C (c^n) -- the EXPLICIT structurally-fixed polynomial.
  (2) shiftedPowPoly_natDegree (hn:1<=n): deg = n EXACTLY (monic (X+1)^n head dominates the constant
      C(c^n), via natDegree_sub_eq_left_of_natDegree_lt). shiftedPowPoly_ne_zero from it.
  (3) isRoot_shiftedPowPoly_of_fiber: (1+w)^n = c^n => P_c.IsRoot w (def-unfold + eval).
  (4) repCount_le_shiftedPow_roots (HEADLINE BRIDGE): r(c) <= (P_c.roots.toFinset).card -- the
      proven fibre (repCount_eq_fiber_card) injects into the root SET of P_c (Finset.card_le_card
      + mem_roots).
  (5) repCount_le_natDegree / repCount_le_n: r(c) <= P_c.natDegree = n, realized as a POLYNOMIAL
      ROOT COUNT (toFinset_card_le + card_roots'), the shape card_le_natDegree_of_vanishing
      consumes -- NOT the trivial |mu_n| cardinality bound.
PROBE: scripts/probes/probe_shifted_gcd.py (+ probe_struct_common_root.py) -- over thin 2-power mu_n
at p in {257,193,641,769,12289} (p>>n^3), n in {8,16,32}, multiple c: r(c) = #fibre = deg gcd(X^n-1,
(1+X)^n-c^n) = #roots(gcd) EXACTLY in 100% of runs (the prose identity confirmed numerically); this
file proves the upper-bound direction (needs no separability) into the explicit shifted-power poly.
HONEST SCOPE: an EXACT structural injection handing r(c) to the polynomial-root machinery through an
explicit degree-n polynomial whose degree is independent of r(c) -- the open work is now PURELY the
auxiliary-multiplicity (Wronskian) input on a FIXED polynomial, not a reformulation. The bound r(c)
<= n is field-universal (NOT yet thinness-essential -- the thin-subgroup cancellation that would
drop this to O(sqrt n) via a high-multiplicity Stepanov auxiliary stays OPEN). NO moment/census/
orbit/geometric-minor re-derivation, NO capacity/beyond-Johnson/growth-law claim, cliff-at-n/2
UNTOUCHED.
CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. New: ArkLib/.../RepCountFiberPolyBound.lean.

## O216 -- the char-0 Lam-Leung SLACK is EXACT and strictly positive (wf-P2 headroom PRODUCER)
LANE: the wf-P2 char-p Lam-Leung slack route (_wf6P2_charp_lamleung_slack.lean). That file reduces
the prize moment ceiling (S-M1) to ONE open residual (P2-Slack): Spur_r(p) <= (2r-1)!! n^r -
A_r^Z(mu_n) =: Slack_r (spurious mod-p coincidences fit in the char-0 slack), but carries Slack_r>=0
on FAITH -- NO in-tree theorem PRODUCES the headroom Slack_r>0 the residual needs to be non-vacuous.
FOUND (grep-confirmed missing): the char-0 zero-sum count A_r^Z = E_r(mu_n) has PROVEN closed forms
in tree (CharZeroEnergyThree.B4_closed -> E_2=3n^2-3n; B6_eq_E3 -> E_3=15n^3-45n^2+40n). The
double-factorial ceiling is (2r-1)!! n^r (3 n^2 at r=2, 15 n^3 at r=3). The leading n^r terms CANCEL
EXACTLY (the Lam-Leung ceiling is the leading asymptotic of the energy); the slack is the
SUB-LEADING term:
  Slack_2 = 3 n^2 - (3 n^2 - 3 n)             = 3 n            (strictly > 0, n >= 1)
  Slack_3 = 15 n^3 - (15 n^3 - 45 n^2 + 40 n) = 45 n^2 - 40 n  (strictly > 0, n >= 1)
PROBE scripts/probes/probe_lamleung_slack_lower.py (ONE sweep): (A) the exact slack identities vs
directly-enumerated char-0 E_r for n=4..128 -- PASS (Slack_2=3n, Slack_3=45n^2-40n exact, both >0).
(B) char-p energy A_r (zero-sum mod p of 2r-tuples) in the PRIZE regime (p>>n^3, p==1 mod n, 3
structured primes each, PROPER thin mu_n, NEVER n=q-1): Spur_r = A_r - E_r^Z = 0 through the
faithfulness edge (n=4/8, r=2/3) => 0 <= Spur <= Slack HOLDS, (P2-Slack) residual non-vacuous.
SHIPPED Frontier/_CharZeroLamLeungSlackLower.lean (7 theorems, single-file lake-env-lean exit 0 +
in-graph lake-locked 3298 jobs exit 0, ALL 7 axiom-clean {propext, Classical.choice, Quot.sound}, no
sorry/axiom/native_decide):
  - slack_two_eq / slack_three_eq: the EXACT slack identities on the BalancedCount carrier
    (3*(2m)^2 - B 4 m = 6m; 15*(2m)^3 - B 6 m = 45*(2m)^2 - 40*(2m)).
  - slack_two_pos / slack_three_pos: B 4 m < 3*(2m)^2 and B 6 m < 15*(2m)^3 for m>=1 -- the char-0
    energy is STRICTLY below the Lam-Leung ceiling (slack genuine, not vacuous).
  - slack_two_pos_value / slack_three_pos_value: same on the closed-form VALUES (for consumers
    holding the value not the carrier).
  - P2Slack_residual_implies_energy_le: the CONSUMER (P2-Slack) => (S-M1) -- if Spur>=0 and
    Spur<=ceiling-A_r^Z then A_r<=ceiling. The load-bearing implication, now resting on an exhibited
    strictly-positive slack rather than an unquantified Slack>=0 hypothesis.
HONEST SCOPE: PRODUCES the exact char-0 slack (the headroom the open (P2-Slack) residual lives
in) at r in {2,3}; does NOT bound the spurious char-p term Spur_r(p) (the genuinely-open arithmetic
on the prize prime stays OPEN). NOTE the slack is sub-leading (Slack_r ~ c_r n^{r-1} vs energy ~
(2r-1)!! n^r), so Slack_r/ceiling_r ~ 1/n -> 0: the residual is real but TIGHTENING in n (consistent
with the probe's Spur/Slack <= 0.11). Char-0/field-universal in derivation; NO capacity/
beyond-Johnson/growth-law claim; delta* and cliff-at-n/2 UNTOUCHED. CORE M(mu_n)<=C sqrt(n log(p/n))
UNCHANGED/OPEN. NON-MOMENT-re-mapping: this is EXTEND-proven off the proven exact energies, a NEW
producer for an explicitly-named open residual, not a re-confirmation of a known wall.

## O214 (lane fibergcd): the O213 fibre rep-count is bounded by the GCD DEGREE, not just the
## degree-n shifted-power poly -- r(c) <= deg gcd(X^n-1, (X+1)^n - C(c^n)), the genuinely SHARP
## Stepanov target (EXTENDS O213; NON-MOMENT structural CORE lever).
LANE: extend the O213 shifted-power fibre brick. O213 proved r(c) <= (shiftedPowPoly n c).natDegree
= n, but that degree-n bound is WILDLY loose in the thin prize regime: a fibre element w is a root
of shiftedPowPoly n c AND of X^n-1 (it lies in mu_n), so it is a COMMON root, hence a root of
gcd(X^n-1, shiftedPowPoly n c). GREP-CONFIRMED MISSING: shiftedPowPoly was referenced ONLY in
O213's file; NO gcd theorem on it. Distinct from SubgroupRepCountGcdExact (which works the DIFFERENT
polynomial reprPoly = (C c - X)^n - 1 over the c-z form, namespace SubgroupRepresentationRoots).
SHIPPED ArkLib/.../RepCountFiberGcdSharp.lean (4 thms, axiom-clean {propext, Classical.choice,
Quot.sound}, single-file lake-env-lean + in-graph lake-locked 3301 jobs exit 0):
  (1) dvd_fiberGcd_of_fiber: a fibre element zeta (zeta^n=1, (1+zeta)^n=c^n) has
      (X - C zeta) | gcd(X^n-1, shiftedPowPoly n c) -- root of BOTH (isRoot_shiftedPowPoly_of_fiber
      from O213 + the mu_n membership), hence dvd_gcd of the two (X - C zeta)-divisibilities.
  (2) repCount_le_fiberGcd_roots: r(c) <= (gcd(X^n-1, P_c)).roots.toFinset.card -- the proven O213
      fibre (repCount_eq_fiber_card) injects into the gcd root SET (card_le_card + mem_roots).
  (3) repCount_le_fiberGcd_natDegree (HEADLINE): r(c) <= deg gcd(X^n-1, (X+1)^n - C(c^n)) -- the
      SHARP Stepanov target (toFinset_card_le + card_roots'), strictly improving O213's r(c) <= n.
  (4) fiberGcd_natDegree_le: deg gcd(X^n-1, P_c) <= n (gcd | P_c, natDegree_le_of_dvd) -- so the gcd
      bound is NEVER weaker than O213's repCount_le_n, and (per probe) strictly sharper.
PROBE: scripts/probes/probe_fiber_gcd_sharp.py + probe_fiber_gcd_maxr.py -- over thin 2-power mu_n,
p >> n^3, p == 1 mod n (p in {7681,8161,12289,40961} at n=8,16; spot-checked 104417,270337 at n=32):
FULL F_p* sweep (EVERY c) confirms r(c) = deg gcd(X^n-1, (1+X)^n-c^n) AND deg gcd < n for ALL c
(match=True, all-sharp=True), with MAX r(c) = 2 even at worst (vs the degree-n bound) -- the
gcd is the sharp target and O213's degree-n bound is far from tight. ONE sweep, ONE commit.
HONEST SCOPE: the SHARP upper-bound direction (needs no separability/splitting) for the O213
shifted-power fibre form. The gcd degree (<= n, field-universal) is still NOT yet thinness-essential
-- the thin-subgroup cancellation that drops the gcd degree to O(sqrt n) via a high-multiplicity
Stepanov auxiliary on the FIXED P_c stays OPEN (StepanovAuxFramework's named kernel). NO moment/
census/orbit/geometric-minor re-derivation, NO capacity/beyond-Johnson/growth-law claim, cliff-at-
n/2 UNTOUCHED. NOT a re-mapped dead face; an EXTEND-proven sharpening of the Stepanov/descent lever.
CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. New: ArkLib/.../RepCountFiberGcdSharp.lean.

## O218 (lane complsharp): the classical Gauss-sum COMPLETION anchor is NON-PROVING for CORE on
thin subgroups -- SHARPENED to its sub-sqrt(q) form + the thin-regime MARGIN-COLLAPSE mechanism.
LANE: the cold completion-anchor face (SubgroupGaussSumWorstCase.lean). The in-tree headline
`norm_eta_torsion_le` reports only |eta_psi(G,b)| <= sqrt(q); its OWN proven intermediate
`mul_norm_eta_torsion_le` (axiom-clean) carries STRICTLY MORE: t*|eta| <= (t-1)sqrt(q)+1, t=(q-1)/d.
EXTENDED (no new probe-math, only the arithmetic the parent discarded):
  - norm_eta_torsion_sharp_le: |eta| <= sqrt(q) - (sqrt(q)-1)/t  (sharp sub-sqrt(q) bound; completion
    already beats the anchor by margin (sqrt(q)-1)/t).
  - norm_eta_torsion_lt: |eta| < sqrt(q) STRICT (margin genuinely positive; anchor never attained).
  - completion_margin_le_of_thin (THE MECHANISM): margin (sqrt(q)-1)/t <= sqrt(q)*(d/(q-1)). As a
    FRACTION of sqrt(q) the margin is <= d/(q-1) ~ n/q. In the prize regime q=n^beta (beta~4-5),
    d=n thin: d/(q-1) -> 0, so the sharp completion bound STAYS ~ sqrt(q), beaten only by an o(1)
    fraction => CANNOT reach the prize bound sqrt(n log(p/n)) <<< sqrt(q).
PROBE scripts/probes/probe_completion_sharp_margin.py (ONE sweep, 17 instances, p==1 mod n, n a
2-power thin, incl Fermat F4 p=65537 beta=4, NEVER n=q-1): (A) |eta|max <= sqrt(q)-(sqrt(q)-1)/t at
EVERY instance PASS. (B) margin/sqrt(q) collapses: 0.00024 at beta=4 (p=65537,n=16) -- the sharp
completion bound is sqrt(q) beaten by 0.024%. CONSTRAINT LEMMA: any method whose magnitude bound
factors through the t-fold Gauss-sum completion triangle inequality is capped at sqrt(q)(1-o(1)) on
thin subgroups; the prize gap sqrt(q)/sqrt(n log(p/n)) ~ q^{1/2}/n^{1/2} lives ENTIRELY in the
cancellation among the t completion terms that the triangle inequality discards. WHY this is a
result not a wall-remap: it is the FIRST in-tree statement quantifying the non-provingness of the
classical completion route, with an exact thin-regime decay law, EXTEND-proven off a proven
intermediate. ASYMPTOTIC GUARD: a sup-norm magnitude bound (the CORE object), NOT a delta*/
incidence object; no capacity/beyond-Johnson/growth-law claim; cliff-at-n/2 UNTOUCHED; margin
VANISHES (no climb). CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. New:
ArkLib/.../CompletionSharpMargin.lean (3 thms, axiom-clean {propext, Classical.choice, Quot.sound},
in-graph lake build 3314 jobs exit 0).

## O218 (lane weilsqrt): the EXPLICIT sqrt(q) Weil count -- instantiate the proven Stepanov-Weil
## engine at M = floor(sqrt q), discharging the divided threshold to a closed form |V| <= (d+2)*floor(sqrt q).
## EXTENDS StepanovWeilSqrtCorollary (removes its OWN named open continuation). THINNESS-BLIND.
LANE: extend the proven Stepanov/Weil engine. StepanovWeilSqrtCorollary.weil_stepanov_card_le_one
discharged ell=1 and divided the engine by the Hasse multiplicity M, landing |V| <= D0/M with
D0 = ((q-1)/2)*d + (q-1), but its doc-comment NAMED the remaining elementary continuation: "the
sqrt(q) value still requires plugging the explicit M". GREP-CONFIRMED: no in-tree theorem instantiates
M = sqrt q on this corollary. SHIPPED ArkLib/.../StepanovWeilSqrtExplicit.lean (2 thms, axiom-clean
{propext, Classical.choice, Quot.sound}, single-file lake-env-lean exit 0 + in-graph lake-locked
8345 jobs exit 0):
  (1) divided_le_sqrt (arithmetic core): D0/floor(sqrt q) <= (d+2)*floor(sqrt q). Proof: M:=Nat.sqrt q
      gives M^2 <= q < (M+1)^2, hence q <= M^2+2M; then a subtraction-free chain
      2*D0 <= (q-1)(d+2) <= 2M^2(d+2) (the last step is q-1 <= 2M^2 <= 2M^2 from 2M <= M^2+1 <=>
      (M-1)^2 >= 0, TIGHT at M=1/q=3 where both sides = 3); divide by M via Nat.div_le_of_le_mul.
  (2) weil_stepanov_card_le_sqrt (HEADLINE): for g squarefree, deg g = d > 0, q=|F| odd, 2A+d<q,
      and the M=floor(sqrt q) construction-dim condition |V|*floor(sqrt q) < 2(A+1), the root/Hasse
      set |V| <= (deg g + 2)*floor(sqrt q) -- the classical O_d(sqrt q) Weil count in explicit closed
      form (leading (d+2)*floor(sqrt q) <= (d+2)*sqrt q = the (d/2)sqrt q asymptotic in a clean integer
      envelope valid at EVERY finite q).
PROBE: scripts/probes/probe_weil_sqrt_instantiate.py + probe_weil_sqrt_arith.py/_arith3.py -- over
ALL odd q in [3, 3e5], d in [1,50): D0 // isqrt(q) <= (d+2)*isqrt(q) holds (no fails); the core
D0 <= (d+2)*M^2 holds with min slack 0 (tight) at q=3,d=1; the abstract (a//2)*d+a <= (d+2)*M^2 at
a=q-1<=M^2+2M-1 holds for all M>=1 (tight at M=1,a=2,d=1). ONE sweep, ONE commit.
HONEST SCOPE (rules 1,3,6): a SPECIALIZATION of the proven weil_stepanov_card_le_one at M:=Nat.sqrt q,
NOT a CORE closure. The sqrt(q) Weil bound it now states explicitly is the TRIVIAL COMPLETION CEILING
for the thin subgroup mu_n (M(mu_n) <= sqrt q), the UPPER end of the proven bracket [sqrt n, sqrt q];
the prize sqrt(n log(q/n)) lives STRICTLY BELOW it and is NOT reached by Weil/Stepanov on the full
character -- THINNESS-BLIND BY CONSTRUCTION, therefore explicitly NOT a thinness-essential CORE lever.
It removes the file's own named open continuation + gives the engine an explicit O_d(sqrt q) head.
NO moment/census/orbit/geometric-minor re-derivation, NO capacity/beyond-Johnson/growth-law claim,
cliff-at-n/2 UNTOUCHED. EXTEND-proven on the proven analytic-NT engine, not a re-mapped dead face.
CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. New: ArkLib/.../StepanovWeilSqrtExplicit.lean.

## O219 (lane prizeceil): an UNCONDITIONAL sqrt(q) ceiling on the canonical prize constant Lambda^2
LANE: wire the O218 completion bound into the PrizeStructuralConstant normal form. The canonical
prize object Lambda^2 = prizeRadiusSq = max_{b!=0} ||eta_b||^2 had a PROVEN Parseval floor
(prizeRadiusSq_parseval_floor: Lambda^2 >= (q n - n^2)/(q-1) ~ n) but its ceiling half carried NO
unconditional companion -- nothing bounded Lambda^2 from above without the OPEN near-Ramanujan
hypothesis (DepthLogSubGaussian). FOUND (grep-confirmed missing): no unconditional upper bound on
prizeRadiusSq existed. LIFTED the per-frequency completion bound (CompletionSharpMargin.
norm_eta_torsion_sharp_le, O218) through the worstCaseIncompleteSumBound_iff_prizeRadiusSq_le
equivalence. SHIPPED ArkLib/.../PrizeRadiusCompletionCeiling.lean (2 thms, axiom-clean {propext,
Classical.choice, Quot.sound}, in-graph lake build 3318 jobs exit 0):
  - prizeRadiusSq_torsion_le: Lambda^2(psi, torsion F d) <= (sqrt(q) - (sqrt(q)-1)/t)^2, t=(q-1)/d
    -- the sharp completion ceiling, strictly below q. First unconditional ceiling on the prize
    object (no Weil, no open hypothesis).
  - prizeRadiusSq_torsion_lt_card: Lambda^2(psi, torsion F d) < q STRICT -- the worst frequency
    never attains the trivial sqrt(q) scale.
Together with the proven floor these PIN the canonical constant unconditionally to [~n, q) on the
torsion subgroup, BOTH ends now proven; and make explicit that DepthLogSubGaussian's open content
is exactly the REDUCTION of this sqrt(q) ceiling down to the sqrt(n log q) floor scale. HONEST
SCOPE (rule 3+6): this is the classical sqrt(q) ceiling lifted to the sup' object; NOT thinness-
essential by itself (the sqrt(q) ceiling holds for any torsion subgroup); the thin-essential
mechanism (why completion CANNOT improve it to the prize scale) is the SEPARATE proven
completion_margin_le_of_thin (O218). Does NOT prove CORE; no delta*/capacity/beyond-Johnson claim;
cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN. CONNECTIVE brick
(EXTEND-proven off two proven theorems), not a re-mapped dead face.

## O220 (lane depthconfine): the open prize predicate DepthLogSubGaussian is CONFINED to the thin
regime q > 2 d log q -- the thick complement is discharged UNCONDITIONALLY by the O219 ceiling.
LANE: delimit WHERE the 25-yr-open prize content lives. DepthLogSubGaussian ψ G := prizeRadiusSq
ψ G <= 2|G| log q is the single open prize predicate (the sqrt(log q) ceiling above the proven
sqrt(n) floor); its ONLY in-tree producer was depthLogSubGaussian_of_nearRamanujan (conditional on
the OPEN near-Ramanujan). FOUND (grep-confirmed missing): NO unconditional producer in the thick
regime where the trivial sqrt(q) bound already beats sqrt(2n log q). SHIPPED ArkLib/.../
DepthLogConfinedToThin.lean (2 thms, axiom-clean {propext, Classical.choice, Quot.sound}, in-graph
lake build 3319 jobs exit 0):
  - depthLogSubGaussian_torsion_of_card_le: q <= 2 d log q => DepthLogSubGaussian ψ (torsion F d)
    UNCONDITIONALLY (via O219 prizeRadiusSq_torsion_lt_card: Lambda^2 < q <= 2 d log q + card_torsion).
  - not_thick_of_depthLogSubGaussian_torsion_fails: if the predicate FAILS at torsion F d then
    2 d log q < q (the subgroup is necessarily THIN). So ALL open prize content lives in the thin
    regime q > 2 d log q, i.e. d < q/(2 log q) -- exactly the prize window q = d^beta, beta large.
RULE-3 RELEVANCE: this is the in-tree CONFINEMENT of the open prize content to thin subgroups -- the
predicate is only a real obstruction where the subgroup is thin, structurally consistent with
thinness-essentiality. HONEST SCOPE: DELIMITS where the open content lives; does NOT prove CORE. The
thin-regime instance (the prize window) stays fully OPEN; only the thick complement is discharged.
No delta*/capacity/beyond-Johnson claim; cliff-at-n/2 untouched. CORE M(mu_n) <= C sqrt(n log(p/n))
UNCHANGED/OPEN. EXTEND-proven off O219 (which extends O218); a confinement brick, not a dead-face remap.

## O221 (lane complsharp, NEGATIVE map): the completion-sum CANCELLATION is NOT a separately-
capturable lever -- it EQUALS the open BGK content. Closes a tempting sub-lane off the O218 face.
After O218 sharpened the completion TRIANGLE bound (|sum_j G_j| <= (t-1)sqrt q, capping |eta| at
sqrt q), the natural next question: does the completion SUM sum_{j=0}^{t-1} G_j (G_j=gaussSum(chi^{dj},
psi_b), |G_j|=sqrt q) exhibit a STRUCTURALLY-CAPTURABLE cancellation far below the triangle bound,
giving a NEW non-moment mechanism? PROBE scripts/probes/probe_completion_gausssum_cancellation.py
(15 instances, PROPER thin mu_n, p==1 mod n, incl Fermat F4 p=65537 beta=4, NEVER n=q-1): measured
|eta_worst|/sqrt(q) and |eta_worst|/sqrt(n). VERDICT: |eta_worst|/sqrt(q) -> 0 as beta grows
(0.054 at beta=4, p=65537/n=16) => the completion sum DOES exhibit near-FULL cancellation
(|sum G_j| = t|eta| ~ t sqrt(n) << (t-1) sqrt q). BUT |eta_worst|/sqrt(n) is NOT a bounded constant:
it GROWS slowly with n (1.9 @ n=4 -> ~5.5 @ n=64) -- i.e. it carries exactly the conjectured
sqrt(log) factor. CONSTRAINT LEMMA: the realised completion-sum cancellation |sum G_j|/((t-1)sqrt q)
-> 0, but the residual scale |eta_worst| ~ sqrt(n)*sqrt(log)-ish IS the prize target M(n) <=
C sqrt(n log(p/n)) ITSELF. So the cancellation is REAL but is NOT a separate lever -- capturing its
MECHANISM (why the t Gauss-sum phases align to leave only sqrt(n log) instead of sqrt q) IS the open
BGK wall, not a shortcut to it. This precisely maps the completion-sum-cancellation sub-lane as DEAD
(no free mechanism), saving future workers from chasing it. Consistent with sec-4 meta-theorem (the
triangle/L1 route is phase-blind; the cancellation lives in phase alignment = the genuinely open
content). No theorem shipped (negative map); no delta*/capacity claim; cliff-at-n/2 untouched. CORE
M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.
## O222 (lane orbitnec): the orbit-count NECESSITY delimiter for the conditional delta* pin --
the honest mirror of OpenCoreConditionalPin, EXTEND-proven on the so-far-UNUSED `->` direction of
OrbitCountCrossingLaw.crossing_law. OpenCoreConditionalPin isolates the entire open prize content
into ONE Prop WorstCaseIncidenceBounded C delta B (I(delta) <= B) and proves the FORWARD pin
(open core => delta <= delta*), routing it through the orbit-count crossing law via
worstCaseIncidence_pin_of_orbitCount -- which consumes ONLY the `<-` direction (N <= d => |B| <= n)
of the proven biconditional crossing_law (|B| <= n <=> N <= d, d = gcd(b-a,n), S = n/d, |B| = N*S).
GREP-CONFIRMED MISSING: the `->`/overflow direction (N > d => |B| > n => open core FALSE) was NEVER
lifted to the open-core / pin layer; no NECESSITY delimiter on the orbit-count discharge existed.
SHIPPED ArkLib/Data/CodingTheory/ProximityGap/OrbitCountPinNecessity.lean (4 thms + 2 sanity
examples; single-file lake-env-lean exit 0 + in-graph lake-locked 8351 jobs exit 0; axiom-clean
{propext, Classical.choice, Quot.sound}):
- incidence_gt_budget_of_orbitCount_gt: |B|=N*S, S*d=n, N>d => n<|B| (the overflow form of
  crossing_law; depends on axioms [propext] only).
- not_worstCaseIncidenceBounded_of_orbitCount_gt: SOME stack with N_u>d =>
  WorstCaseIncidenceBounded C delta n is FALSE (the prize-budget open core fails there, so the
  pin is not certified through this lever at radius delta).
- pin_not_certified_of_orbitCount_gt: assembled reach -- an overflowing stack => the orbit-count
  lever does NOT discharge worstCaseIncidence_pin_budget at that radius.
- coprime_pin_requires_single_orbit (SHARPEST): primitive pencil gcd(b-a,n)=1 (orbit size S=n) =>
  the budget-n open core holds at a stack IFF its bad-alpha set is a SINGLE orbit (N<=1); N>=2
  distinct orbits provably block the pin. Lifts OrbitCountConsumerBridge.coprime_crossing_law
  (I<=n <=> N<=1) to a NECESSARY condition on the pin's open core.
NO PROBE NEEDED (pure cardinality, like O215): N>d => N*S>d*S=n via Nat.mul_le_mul_right; the
math is the unused half of an in-tree biconditional, not an empirical claim. HONEST SCOPE
(rule 3,6): does NOT prove or refute CORE. Pins EXACTLY when the orbit-count lever certifies the
open core (N<=d, forward pin) vs PROVABLY FAILS to (N>d, here). Whether the worst-case orbit count
stays <=d at the prize window radius -- whether the open core itself holds -- is the
recognized-open prize question, UNTOUCHED. NON-MOMENT (orbit-count/incidence-geometry face),
EXTEND-proven on two proven in-tree theorems, NOT a re-mapped dead face. NO moment/census/
geometric-minor re-derivation, NO capacity/beyond-Johnson/growth-law claim, cliff-at-n/2
UNTOUCHED. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O223 (lane budgetvac): the char-sum -> incidence budget is VACUOUS at the prize budget -- the
naive |G|+q*B route forces B=0, so M(n) <= C sqrt(n log m) cannot discharge the prize floor through
it. EXTEND-proven on CharSumDeltaStarBridge; turns the in-tree PROSE correction into a theorem.
CharSumDeltaStarBridge.le_mcaDeltaStar_of_charSumBound packages the only M->epsMCA route through the
naive ceiling budget charSumIncidenceBudget G B = ceil(|G| + q*B) (q=|F|). Its docstring +
PrizeConditionalPinCapstone's honest correction state IN PROSE that at the prize budget q*eps*=|G|
this is VACUOUS (forces q*B<=0 => B=0). GREP-CONFIRMED MISSING: never a THEOREM (only a consistency
witness B=|G| + prose). SHIPPED ArkLib/Data/CodingTheory/ProximityGap/CharSumBudgetVacuity.lean
(4 thms; single-file lake-env-lean exit 0 + in-graph lake-locked 3513 jobs exit 0; axiom-clean
{propext, Classical.choice, Quot.sound}):
- charSumBudget_ge_card: |G| <= ceil(|G|+q*B) for B>=0 (budget carries the full domain term).
- charSumBudget_forces_B_zero (VACUITY CORE): ceil(|G|+q*B) <= |G| (= floor(q*eps*) at q*eps*=|G|),
  q>=1, B>=0 => B=0. The |G| term forces q*B<=0.
- charSumBudget_prize_excludes_positive: contrapositive -- B>0 => |G| < ceil(|G|+q*B), so any
  STRICTLY positive char-sum/power-saving bound (di Benedetto B<=n^{1-31/2880}) overshoots the
  prize budget and cannot discharge le_mcaDeltaStar_of_charSumBound there.
- charSum_route_vacuous_at_prize: the trivial witness B=|G| (charSumBound_satisfiable_trivial, the
  only unconditionally-available char-sum bound) is, for |G|>=1, STRICTLY positive, hence excluded
  -- the route cannot certify the floor at q*eps*=|G|.
NO PROBE NEEDED (pure ceiling arithmetic): ceil(|G|+q*B)>=|G|+q*B>=|G|, budget<=|G| pins q*B<=0.
HONEST SCOPE (rule 3,6): does NOT prove or refute CORE. The precise REACH delimiter of the
char-sum->incidence discharge route: localizes WHY the BGK/Paley sup-norm M(n) <= C sqrt(n log m)
cannot, THROUGH THIS ROUTE, close the floor hfloor of PrizeConditionalPinCapstone (the route's
budget overshoots by the index factor sqrt(m)). The genuinely finer realized-incidence object
(epsMCA at the edge) is UNTOUCHED and remains the open prize core. NON-MOMENT structural cardinality
delimiter, EXTEND-proven on the proven in-tree budget bridge, NOT a re-mapped dead face. NO moment/
census/geometric-minor re-derivation, NO capacity/beyond-Johnson/growth-law claim, cliff-at-n/2
UNTOUCHED. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O224 (lane budgetmono): the MCA threshold delta* is MONOTONE in the error budget eps* -- a more
generous budget never lowers delta*. The load-bearing order-theory companion the ledger lacked along
the BUDGET axis (it only had RADIUS-axis good/bad brackets). EXTEND-proven on MCAThresholdLedger.
MCAThresholdLedger brackets delta*(C,eps*)=sSup(mcaGoodRadii C eps*) along the RADIUS axis delta
(mca_good_set_downward_closed, le_mcaDeltaStar_of_good, mcaDeltaStar_le_of_bad) but NEVER recorded
monotonicity in eps*. GREP-CONFIRMED MISSING. SHIPPED
ArkLib/Data/CodingTheory/ProximityGap/MCAThresholdBudgetMono.lean (3 thms; single-file
lake-env-lean exit 0 + in-graph lake-locked 3059 jobs exit 0; axiom-clean {propext,
Classical.choice, Quot.sound}):
- mcaGoodRadii_mono: eps*0 <= eps*1 => mcaGoodRadii C eps*0 subset mcaGoodRadii C eps*1 (a radius
  good at a tighter budget is good at a looser one).
- mcaDeltaStar_mono: eps*0 <= eps*1 => delta*(C,eps*0) <= delta*(C,eps*1). sSup-monotone over the
  budget-monotone good set (empty tighter set handled via csSup_empty = bot).
- mcaDeltaStar_le_of_budget_pin: a good radius proven at a tighter budget eps*0 <= eps*1 is also <=
  delta* at the looser eps*1 -- the lower pin survives budget relaxation.
NO PROBE NEEDED (pure order theory on the ledger's sSup object). HONEST SCOPE (rule 3,6): pure
infrastructure brick, NOT a CORE touch and NOT thinness-specific (holds for every code + budget
pair). Does not bound eps_mca or delta* at any concrete radius; only records how delta* moves with
the budget. The genuine open prize content (realized worst-case incidence at the prize budget) is
UNTOUCHED. NON-MOMENT infrastructure, EXTEND-proven on the proven in-tree ledger, NOT a re-mapped
dead face. NO moment/census/geometric-minor re-derivation, NO capacity/beyond-Johnson/growth-law
claim, cliff-at-n/2 UNTOUCHED. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O228 (lane foldsupply): the KKH26 bad-scalar supply STRICTLY DECAYS along an s-step fold --
the quantitative completion of the fold-transport trichotomy (#357 R2 / #444 §11 BGK-independent
fold-transport lever). KKH26FoldTransport.lean proves the WORD-level fold trichotomy and, in the
m-step case, the census-set INVARIANCE (kkh26_inner_group_fold_invariant); for the s-step it
asserts ONLY IN PROSE that "the construction-class supply drops 2^r*C(s/2,r) -> 2^{r/2}*C(s/4,r/2)
per s-step". GREP-CONFIRMED MISSING: no theorem states the s-step supply DECAY. PROBE-FIRST
(scripts/probes/probe_fold_supply_decay.py + probe_reven.py, field-universal counting over PROPER
thin prize-regime params s=2^mu, r even, 2r<s): 0 strict-decay violations / 4083 instances; the
direct binomial inequality C(s/4,r/2) <= C(s/2,r) holds with 0/4083 violations in the r-even
regime (matching kkh26_fold_s_step_r_even's 2|r hypothesis); the decay factor is dominated by the
binomial ratio, far exceeding the monomial 2^{r/2} halving floor. SHIPPED
ArkLib/Data/CodingTheory/ProximityGap/KKH26FoldSupplyDecay.lean (2 thms + 2 decide sanity examples;
single-file lake-env-lean exit 0 + in-graph lake-locked 1236 jobs exit 0; axiom-clean {propext,
Classical.choice, Quot.sound}):
- choose_le_choose_two_mul: C(a,k) <= C(2a,2k) for all a,k (a single diagonal (k,k) term of
  Vandermonde Nat.add_choose_eq, C(a,k)^2 <= C(2a,2k), then C(a,k) <= C(a,k)^2). Reusable binomial
  doubling brick.
- kkh26_fold_supply_strict_decay (HEADLINE): for 4|s, 2<=r, 2|r, 2r<s:
  2^{r/2}*C(s/4,r/2) < 2^r*C(s/2,r). The bad family is NOT an s-step fold fixed point (sharp
  contrast to the m-step supply INVARIANCE). EXTEND-proven via the doubling bound
  (2*(s/4)=s/2 from 4|s, 2*(r/2)=r from 2|r) + strict 2^{r/2}<2^r.
HONEST SCOPE (rule 3,6): bounds the supply of THIS ONE construction class (the KKH26 monomial
stack) along the fold; field-universal, NOT thinness-essential, does NOT bound M(mu_n). It is the
quantitative completion of the fold-transport trichotomy, NOT a CORE lever. The open prize question
(how the WORST-CASE incidence behaves along the tower) is UNTOUCHED. NON-MOMENT, BGK-independent
fold-transport face, EXTEND-proven on the proven in-tree word-level halving theorem
(kkh26_fold_s_step_r_even), NOT a re-mapped dead face. NO moment/census/orbit/pencil re-derivation,
NO capacity/beyond-Johnson/growth-law claim, cliff-at-n/2 UNTOUCHED. CORE M(mu_n) <= C sqrt(n
log(p/n)) UNCHANGED/OPEN.

## O229 (lane spectrumdvd): the deep-band subset-sum SPECTRUM is MULTIPLICATIVELY RIGID --
invariant under scaling by the subgroup, a union of mu_n-orbits, hence (free action) |mu_n| | card.
DeepBandSpectrumComplementSymmetry pinned the PALINDROME |spectrum r| = |spectrum (n-r)| on the
open prize obstruction |spectrum r| = |{ sum_{z in S} z : S in powersetCard r mu }| (= BCHKS 1.12)
but recorded NO further structure. GREP-CONFIRMED MISSING: no theorem states the subset-sum
spectrum's invariance under the multiplicative-subgroup dilation action (the existing dilation
files DilationRealSignCocycle / ActionOrbitGeneralF / CosetPowerSumConcentration touch the
bad-scalar / power-sum side, NOT the subsetSumSpectrum object of SpectrumComplementSymmetry).
PROBE-FIRST (scripts/probes/probe_spectrum_dilation_divisibility.py, PROPER thin mu_n n=2^a,
p >> n^3, p == 1 mod n, 3 primes/n, NEVER n=q-1; depths r in {1..5, n-3, n-2, n-1}):
0/78 invariance fails; spectrum\{0} is a disjoint union of mu_n-orbits, every orbit size divides n,
the action is FREE in every tested instance (all orbit sizes = n), so n | |spectrum r \ {0}| in all
78 instances (e.g. n=8 r=2 |spec\0|=24=3*8; the NON-Sidon n=32 p=32993 r=2 still gives 416=13*32).
SHIPPED ArkLib/Data/CodingTheory/ProximityGap/DeepBandSpectrumDilationInvariant.lean (5 thms;
single-file lake-env-lean exit 0 + in-graph lake-locked 8314 jobs exit 0; axiom-clean {propext,
Classical.choice, Quot.sound}):
- subsetSum_smul: sum_{z in g*S} z = g * sum_{z in S} z (scaling a subset sum).
- image_inv_self: (g^-1 * .) '' mu = mu given (g * .) '' mu = mu (inverse dilation symmetry).
- smul_powersetCard: S |-> g*S maps powersetCard r mu bijectively to itself when g*mu = mu.
- spectrum_smul_invariant (HEADLINE): g != 0, g*mu = mu => (g * .) '' (subsetSumSpectrum mu r)
  = subsetSumSpectrum mu r. The spectrum is a union of <g>-orbits; ranging g over mu makes the
  spectrum a union of mu-orbits under dilation.
- smul_self_of_mulClosed: g*mu = mu for g in mu when mu is multiplicatively closed (g unit,
  closed under * and inverses) -- the MulClosed1-data hypotheses, supplying the dilation symmetry.
- card_dvd_of_uniform_orbit_partition: a Finset fibred by a rep map with every fibre of size m
  has m | card (the free-action divisibility: free mu-orbits all have size |mu|, so |mu| | card).
HONEST SCOPE (rule 3,6): a structural CONSTRAINT on the named obstruction (the spectrum's nonzero
part is a union of mu-orbits, hence -- in the free case observed -- its cardinality is a multiple
of |mu|), NOT a bound on it: does NOT compute |spectrum r| (the prize-critical open quantity =
BCHKS 1.12 stays OPEN). The FREENESS of the action is an honest HYPOTHESIS of
card_dvd_of_uniform_orbit_partition (probe-supported, NOT proven here -- it needs the
field-arithmetic non-degeneracy that no nonzero spectrum value is mu-fixed). Together with the
complement palindrome (O-prior) the spectrum cardinality is constrained both reflectively
(r <-> n-r) and multiplicatively (|mu| | card). NON-MOMENT, char-free / field-universal
additive-multiplicative combinatorics (thickness/regime never enters, no field-arithmetic input
consumed), EXTEND-proven on the proven in-tree subsetSumSpectrum object, NOT a re-mapped dead face.
NO moment/census/orbit-count/pencil re-derivation, NO capacity/beyond-Johnson/growth-law claim,
cliff-at-n/2 UNTOUCHED. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O230 (lane spectralcentral): the subset-sum SPECTRUM is NEGATION-CLOSED at the
self-complementary CENTRAL DEPTH r = n/2 -- the across-depth palindrome collapses to a
within-depth involution. DeepBandSpectrumComplementSymmetry proved the ACROSS-depth identity
subsetSumSpectrum mu (|mu|-r) = -(subsetSumSpectrum mu r) (spectrum_compl_eq_neg_image, under
sum_mu = 0). At r = |mu|/2 (2r=|mu|, |mu| even -- n a 2-power) the two sides land on a SINGLE
depth, turning the palindrome into a WITHIN-depth NEGATION invariance the across-depth statement
does NOT give at a fixed depth. GREP-CONFIRMED MISSING: no theorem stated the central-depth
negation closure. PROBE (scripts/probes/probe_spectrum_central_neg_invariant.py; PROPER thin mu_n,
n=2^a, p >> n^3, p == 1 mod n, NEVER n=q-1): central-depth spectrum(n/2) negation-closed 0/9 fails
(n=16 p=4129 |spectrum 8|=2577 negation-invariant). SHIPPED
ArkLib/Data/CodingTheory/ProximityGap/DeepBandSpectrumCentralNegInvariant.lean (2 thms; single-file
lake-env-lean exit 0 + in-graph lake-locked exit 0; axiom-clean {propext, Classical.choice,
Quot.sound}):
- spectrum_central_neg_invariant (HEADLINE): 2r=|mu|, sum_mu=0 => (spectrum r).image (-.) =
  spectrum r. Specializes spectrum_compl_eq_neg_image at |mu|-r=r.
- spectrum_central_neg_mem: v in spectrum (n/2) => -v in spectrum (n/2) (membership form).
HONEST SCOPE (rule 3,6): a structural CONSTRAINT (central-depth spectrum is its own negation; with
the O229 dilation rigidity, invariant under <mu_n, -1>; nonzero part splits into +/- pairs so its
cardinality parity is pinned), NOT a computation of |spectrum (n/2)| (the prize-critical open
quantity = BCHKS 1.12 stays OPEN). Field-universal finite combinatorics, EXTEND-proven on the proven
in-tree spectrum_compl_eq_neg_image, NOT a re-mapped dead face. The "cliff-at-n/2" here is a DEPTH
index, NOT an incidence-decay claim -- the asymptotic-guard cliff is UNTOUCHED. NO moment/census/
orbit-count/pencil re-derivation, NO capacity/beyond-Johnson/growth-law claim. CORE M(mu_n) <=
C sqrt(n log(p/n)) UNCHANGED/OPEN.

---

## O231 — `|mu|`-divisibility of the nonzero subset-sum spectrum, freeness DISCHARGED (lane specfree)

`DeepBandSpectrumFreeDivisibility.lean` (push pending). EXTEND-proven on O229's
`spectrum_smul_invariant`, REMOVING O229's freeness HYPOTHESIS. O229
(`card_dvd_of_uniform_orbit_partition`) proved `|mu| | |spectrum r \ {0}|` only UNDER a freeness
hypothesis (`hfiber`: every nonzero spectrum value's orbit/fibre has size `= |mu|`), and its own
docstring recorded the freeness as "the (provable but field-arithmetic-dependent) freeness is a
hypothesis, not baked in". O231 discharges it: the dilation action of a finite multiplicative
subgroup on `F \ {0}` is FREE for a one-line field reason (`g*v=v, v!=0 => g=1`, `mul_right_cancel0`
= the existing `I031DilationOrbitReduction.dilation_free`). Three thms, axiom-clean {propext,
Classical.choice, Quot.sound}:
- `orbit_card_eq`: `|mu.image (.*v)| = |mu|` for `v != 0` (the field-arithmetic discharge).
- `card_dvd_of_free_smul_action`: ABSTRACT engine — a finite set `T` of nonzero elements, stable
  under a finite mult-closed inverse-closed subgroup `H` (`1 in H`, `0 not in H`), has `|H| | |T|`,
  by strong induction peeling one full orbit (size `|H|`) at a time.
- `card_dvd_spectrum_sdiff_zero_free` (HEADLINE): for mult-closed inverse-closed `mu`,
  `|mu| | |subsetSumSpectrum mu r \ {0}|` UNCONDITIONALLY.
PROBE `scripts/probes/probe_spectrum_freeness_discharge.py` (PROPER thin `mu_n=2^a`, `p >> n^3`,
`p == 1 mod n`, NEVER `n=q-1`): pointwise freeness `g*v=v => g=1` for nonzero spectrum `v` 0 fails /
57 instances; every nonzero-spectrum orbit size exactly `n`; `n | |spectrum r \ {0}|` 0 fails.
HONEST SCOPE (rule 3,6): strengthens O229 by removing a hypothesis; constrains the open obstruction
`|spectrum r|` (BCHKS 1.12) mod `|mu|` WITHOUT computing it (OPEN). NON-MOMENT, char-free, NOT
thinness-essential. The "n/2"-free statement does not touch the asymptotic-guard cliff. NO moment/
census/orbit-count/pencil re-derivation, NO capacity/beyond-Johnson/growth-law claim. CORE
M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O237 (lane symcard): the F1 floor multiplier `chooseCH s r` IS the complete-homogeneous
## monomial-multiset count `|Sym (Fin s) r|` (structural identity, now a THEOREM) -- AND the
## distinct-h-VALUE reading of the open spectrum bound is FALSE at small r (constraint lemma).
#
# CONTEXT. `_BchksF1_CompleteHomogeneousFloor.lean` DEFINES the floor multiplier
# `chooseCH s r = C(s+r-1, r)` and asserts in PROSE it is "the number of degree-r monomials in s
# variables = #multisets of size r from s elements = dim of the degree-r complete-homogeneous space"
# -- but proves it ONLY as a bare `Nat.choose`, never connected to the combinatorial object. This
# lane discharges that assertion (FRONTIER-MOVEMENT, NON-MOMENT, char-free) and pins, with a clean
# probe, the precise reason the floor needs a `poly(n)` factor.
#
# THE BRICK (landed, in `_BchksF1_ChooseCHSymCard.lean`, axiom-clean, 5 thms):
#  - chooseCHsc_eq_card_sym:  chooseCH s r = Fintype.card (Sym (Fin s) r)  (Mathlib stars-and-bars
#    Sym.card_sym_eq_choose + Fintype.card_fin). The multiplier IS the degree-r monomial-multiset
#    count -- the floor file's prose assertion, now a theorem.
#  - chooseCHsc_eq_multichoose:  chooseCH s r = Nat.multichoose s r  (the named combinatorial object).
#  - card_le_chooseCHsc_of_inj / finset_card_le_chooseCHsc_of_injOn:  the IMAGE-CARD reduction --
#    bad-scalars injecting into Sym (Fin s) r have card <= chooseCH s r (Fintype.card_le_of_injective).
#    The poly=1 leading-order floor with a GENUINE combinatorial witness, not a free <=.
#
# THE CONSTRAINT LEMMA (refutation, probe_chooseCH_sym_card.py / probe_chooseCH_threshold.py;
# PROPER thin mu_n = nth roots of unity in F_p, p>>n^3 where structured, n=4,8,16,32, NEVER n=q-1):
#  the DISTINCT-h-VALUE reading of CompleteHomogeneousSpectrumBound -- #{distinct h_r(R) :
#  R in binom(mu_n, k+1)} <= chooseCH n r -- is FALSE with poly=1 in a sharp low-r triangle:
#  VIOLATED exactly when r is small relative to k (n=16: k=3 viol at r<=3, k=2 viol at r<=2, all k
#  viol at r=1; n=32: viol at r<=2). It only holds for r large enough. The pure cardinality identity
#  chooseCH == #monomial-multisets is CLEAN (0 fails / 130). So the open spectrum bound CANNOT be the
#  distinct-VALUE count over (k+1)-subsets (refuted at the binding small-r fold); it is a
#  monomial-DIRECTION count (= chooseCH n r tautologically via Sym.card), with the genuine open
#  content being the forced-gamma INJECTION direction->bad, and the empirical poly(n)=n excess living
#  exactly where that injection FAILS (the small-r value-collision region).
#  This INDEPENDENTLY CORROBORATES Shaw's live F1 fix (0a34f6012 "poly=1 FALSE, poly=n verified") and
#  supplies its MECHANISM: poly=1 fails because the value-spectrum exceeds the dimension at small r.
#
# HONEST SCOPE (rules 1,3,6): NOT a CORE closure. A pure Fintype.card/Sym cardinality identity +
# image-card reduction + a value-count refutation -- field-universal (no thinness), so by rule 3
# CANNOT prove CORE. Does NOT prove the open CompleteHomogeneousSpectrumBound (which needs poly=n).
# NO moment/census/orbit/pencil/spectrum re-derivation. A Sym-cardinality object, NOT a delta*/
# incidence object -- asymptotic-guard cliff-at-n/2 UNTOUCHED, no capacity/beyond-Johnson/growth-law
# claim. ONE sweep ONE commit. CORE M(mu_n) <= C sqrt(n log(p/n)) UNCHANGED/OPEN.

## O238 (lane f6cross): the F6 explicit-lower-bound CROSSING FOLD `M_cross` is a `Nat.findGreatest`
## (hard upper edge), NOT the prose "least depth" -- because the complete-homogeneous dominator
## `chooseCH s r` is MONOTONE INCREASING in `r` (F6's own `chooseCH_mono`).
#
# CONTEXT. `_BchksF6_ExplicitDeltaStarLower` assembles `delta* >= 1 - rho - (M_cross-1)/n` and its
# PROSE defines `M_cross` := "the LEAST depth `r` at which the char-free worst bad count
# `poly * chooseCH(s,r)` drops within the soundness budget `eps*|F|`", where
# `chooseCH s r = C(s+r-1, r)`. F6's own theorem `chooseCH_mono` proves `chooseCH s r` is MONOTONE
# INCREASING in `r`. An increasing dominator within a budget is a DOWN-SET in `r` (initial segment):
# once it leaves the budget it never returns.
#
# THE CONSTRAINT (probe `probe_f6_crossing_monotonicity.py`, s=2..32 x 4 budgets, 0 fails / 16):
#  (1) the LEAST `r` in budget is DEGENERATE -- it is `0` (since `chooseCH s 0 = 1 <= budget` for any
#      `poly <= budget`). So the prose "least depth crossing" is the empty-multiset rung, NOT the
#      binding depth `m*`.
#  (2) the CORRECT crossing fold is the GREATEST `r` in budget (`Nat.findGreatest`), with a HARD upper
#      edge (`budget < poly*chooseCH s r => budget < poly*chooseCH s r'` for all `r' >= r`). This
#      matches the in-tree DECREASING over-det edge cascade (`DecouplingDecayCrossingDepth.crossingDepth
#      = m-1`, LINEAR = the cliff-at-n/2), which is the genuine binder.
#  (3) F6's `mStar_le_cross` is SOUND but over an ABSTRACT cascade `D` whose nonvacuity witness
#      `modelD = [200,200,200,0,..]` is DECREASING-to-budget (a least-`r` `Nat.find` binder, `m*=3`,
#      is meaningful there). The PROSE identification `D := poly*chooseCH` carries the OPPOSITE
#      monotonicity, so the "least-`r` crossing of `poly*chooseCH`" (= 0) is NOT the object
#      `mStar_le_cross` caps. The two `Nat.find` objects DIFFER.
#
# THE BRICK (landed, `_BchksF6_CrossingFoldMonotonicity.lean`, axiom-clean, 8 thms):
#  - chooseCH_mono_le (s>=1): full-range monotonicity (lift of F6's one-step `chooseCH_mono`).
#  - budget_predicate_downward_closed: the budget predicate is downward-closed in depth.
#  - least_in_budget_is_zero (HEADLINE): `poly <= budget -> Nat.find (least r in budget) = 0`.
#  - budget_fails_above_edge: the hard upper edge (monotone failure above the edge).
#  - findGreatest_is_crossing_fold / findGreatest_crossing_in_budget: the correct fold is a
#    `Nat.findGreatest` (every in-budget depth `<=` the fold; the fold itself is in budget).
#  - modelD_decreasing_to_budget + crossing_fold_mismatch: F6's `modelD` is OPPOSITE-monotone; at the
#    F6 scale (s=8,poly=1,budget=120) least-r of the increasing `chooseCH` = 0 while findGreatest = 3.
#
# HONEST SCOPE (rules 1,3,6): NOT a CORE closure, NOT a refutation of F6's theorems (they hold over
# abstract `D`). Pure Nat monotonicity + `Nat.findGreatest` arithmetic -- field-universal (no thinness),
# so by rule 3 CANNOT prove CORE. Corrects the F6 reduction's crossing-fold SEMANTICS (`M_cross` =
# findGreatest hard-edge, not least) + records the prose/object monotonicity mismatch. NON-MOMENT,
# EXTEND-proven on F6's `chooseCH`/`chooseCH_mono`. The increasing `chooseCH` is a per-subset
# DIRECTION-count (Sym-cardinality), NOT a delta*/incidence object -- asymptotic-guard cliff-at-n/2
# UNTOUCHED, no capacity/beyond-Johnson claim (we CONFIRM the binding crossing is a hard upper edge,
# consistent with the cliff guard). ONE sweep ONE commit. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## O239 (lane f3sumset): the F3 Sumset-Extremality floor's SOUNDNESS conjunct is a DOWN-SET in the
## fold (monotone-failing, because `|Sigma_r|` is INCREASING), so at the DEEP binding fold it COUPLES
## `|F|` to the deep-fold sumset size: `|F| >= poly*|Sigma_M|/eps*` (super-poly-in-depth field lower bound).
#
# CONTEXT. `_BchksF3_RetargetedReduction` re-targets the prize onto the open floor
# `SumsetExtremality bad sumset poly soundness := bad <= poly*sumset AND poly*sumset <= soundness`,
# where `sumset = |Sigma_r(mu_s)| = |H^{(+r)}|` and `soundness = eps*|F|` (`|F|` LARGE). F3 PROVES
# (`subsetSumBudget_existential_unsat`) that `|Sigma_r|` is MONOTONE INCREASING in the fold
# (`|Sigma_r(mu_16)| = 129,704,2945,10128,29953,78592,185617` for r=2..8). This lane discharges the
# structural consequence for the floor's SECOND conjunct.
#
# THE CONSTRAINT (probe `probe_f3_sumset_monotone_floor.py`, n=s=8 + n=s=16, 0 fails / 6):
#  Because `|Sigma_r|` is increasing, the soundness conjunct `poly*|Sigma_r| <= soundness` is a
#  DOWN-SET in the fold r (holds only at SHALLOW folds). But the binding fold m* is DEEP (F3's
#  `mStar_ge_three_*`: m* >= 3, grows). So at the deep binding fold M the soundness conjunct
#  `poly*|Sigma_M| <= eps*|F|` FORCES `|F| >= poly*|Sigma_M|/eps*` -- and `|Sigma_M|` is super-poly
#  in M (ratios 5.46->4.18->3.44->2.96->2.62->2.36, log|Sigma|/r decreasing but |Sigma| growing
#  super-poly). The floor's "|F| large" is NOT free: it is a super-poly-in-depth lower bound on the
#  field size, the precise non-vacuity cost of the re-targeted floor. (Same increasing-dominator
#  down-set structure as the F6 crossing-fold constraint O238 -- here on the SUMSET, not chooseCH.)
#
# THE BRICK (landed, `_BchksF3_SumsetFloorFieldCoupling.lean`, axiom-clean, 6 thms):
#  - soundness_conjunct_downward_closed: smaller sumset still in budget (down-set in the sumset).
#  - soundness_conjunct_fails_above: the hard upper edge (once out at a sumset, out for all larger).
#  - sumsetExtremality_forces_field_coupling: the floor's 2nd conjunct = `poly*sumset <= eps*|F|`.
#  - field_card_lower_bound_of_sumsetExtremality (HEADLINE): eps>=1 => `poly*sumset/eps <= |F|` --
#    the field-size lower bound. At the deep fold (super-poly sumset) = a super-poly-in-depth |F| bound.
#  - deep_fold_field_lower_bound: F3's exact `|Sigma_8(mu_16)|=185617`, poly=eps=1 => `|F| >= 185617`
#    (4 orders of magnitude above the OLD refuted budget 16).
#  - deep_fold_sumset_dominates: `|Sigma_3|=704 < |Sigma_8|=185617` -- the coupling is a DEEP-fold
#    constraint (the field lower bound grows along the fold).
#
# HONEST SCOPE (rules 1,3,6): NOT a CORE closure, NOT a refutation of F3's theorems (they hold over
# abstract `sumset`/`soundness`). Pure Nat/Nat-division monotonicity -- field-universal (no thinness),
# so by rule 3 cannot prove CORE. Pins the `|F|`-coupling cost of the F3 floor's soundness conjunct.
# Does NOT re-derive F3's `|Sigma_r| > budget` refutation (already a theorem). The increasing
# `|Sigma_r|` is an additive-combinatorics SUMSET-SIZE object, NOT a delta*/incidence object --
# asymptotic-guard cliff-at-n/2 UNTOUCHED, no capacity/beyond-Johnson claim. NON-MOMENT, EXTEND-proven
# on F3's `SumsetExtremality`. ONE sweep ONE commit. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

# =====================================================================================
# [LRTBI] LOG-RATIO TOWER BOUNDED-INCREMENT -- the Azuma/Freedman prerequisite holds, but
#         controls only the FLUCTUATION, not the MEAN drift. (2026-06-16, axiom-clean brick)
# =====================================================================================
# LEVER: §1.2 "Martingale / Azuma-Freedman over the 2-power tower filtration". The proven geomean
# recasting (DyadicGeomeanPrizeVsSqrtN) gives M(mu_{2^a}) = M(mu_1)*prod_{i<a} rho_i, so
# S_a := log M(mu_{2^a}) - log M(mu_1) = sum_{i<a} log rho_i is a telescoped sum. The prize
# M <= C sqrt(2^a log(p/2^a)) <=> S_a <= (1/2) a log2 + (1/2) log log(p/2^a) + log C.
# A Freedman/Azuma concentration bound on S_a REQUIRES bounded increments Delta_i = log rho_i.
#
# RESULT (positive, the prerequisite HOLDS on the log-tower):
#  - The DIRECT eta-tower is UNbounded-increment (probe_407_cumulant_martingale_deep: the per-level
#    eta-increment is a full order-2^k period, magnitude ~sqrt(2^k log m) = as big as the whole sum).
#    So Azuma on the eta-partial-sums gives nothing. KNOWN obstruction.
#  - The LOG-RATIO tower IS bounded-increment: the landed Liu-Zhou doubling M(mu_{2^{i+1}}) <=
#    2 M(mu_{2^i}) (LiuZhouSplitRecursion.M_union_le_two_mul) gives Delta_i = log rho_i <= log 2;
#    subgroup monotonicity gives Delta_i >= 0. So Delta_i in [0, log 2] -- BOUNDED. The Freedman
#    prerequisite is satisfied on the log-tower. This is the brick LogRatioTowerBoundedIncrement.lean.
#
# PROBE (probe_rho_increment_bounded.py + probe_rho_excess_growth.py, PROPER thin mu_n, p>>n^3,
# p=1 mod 2^a, NEVER n=q-1): rho_i in [1.58, 2.0] (10 levels, beta=3.2/4.0), strictly > sqrt2=1.414
# at EVERY level. So Delta_i - (1/2)log2 > 0 strictly; the EXCESS sum sum_i (Delta_i - (1/2)log2)
# grows ~Theta(a) LINEAR (ratio E_N/N ~ 0.30, not ->0), NOT the O(log a) the prize needs.
#
# THE WALL (rule 4, logTower_excess_eq is the formal constraint): bounded increments give only
# S_a <= a log2 (the trivial M <= 2^a = n, sqrt(n) short). A martingale concentration bound controls
# the FLUCTUATION (~sqrt(a)) of S_a around its MEAN; but the prize is a statement about the MEAN of
# Delta_i (it must average down to (1/2)log2 + o(1)). Bounded-increment concentration CANNOT supply a
# mean-drift bound. The open object is the per-level mean drift E[Delta_i] - (1/2)log2, i.e. the
# binding-frequency phase law theta_b (the N13 transfer operator) that the magnitude-only Liu-Zhou
# recursion drops. Same wall as Liu-Zhou [LZSR], viewed on the log-tower.
#
# THE BRICK (landed, LogRatioTowerBoundedIncrement.lean, axiom-clean {propext,Classical.choice,
# Quot.sound}, 6 thms):
#  - logRatio_le_log2 (HEADLINE): the BOUNDED-INCREMENT property Delta_i <= log 2 from the doubling.
#  - logRatio_nonneg: Delta_i >= 0 from monotonicity (so Delta_i in [0, log 2]).
#  - logTower_telescope: log M(mu_{2^a}) - log M(mu_1) = sum_{i<a} Delta_i (exact telescope).
#  - logTower_le_card_mul_log2: the bounded-increment SUM S_a <= a log2 (trivial bound as martingale-sum).
#  - logTower_excess_eq: the rule-4 constraint -- prize <=> excess sum sum(Delta_i - (1/2)log2) <= R.
#  - logRatio_le_log2_of_M: concrete discharge for the real M-tower via M_union_le_two_mul (non-vacuous).
#
# HONEST SCOPE (rules 1,3,6 + asymptotic guard): NOT a CORE closure. NOT thinness-essential -- the
# doubling is the thickness-BLIND Liu-Zhou triangle inequality (holds in the thick beta~2.3 window
# where the prize is FALSE), so by rule 3 nothing from Delta_i <= log2 alone can prove the prize. No
# capacity/beyond-Johnson claim; cliff-at-n/2 UNTOUCHED (this is a log-tower mean-drift object, not an
# incidence/delta* object). NON-MOMENT (log-ratio of sup-norms, not additive energy), EXTEND-proven on
# the landed Liu-Zhou M_union_le_two_mul. ONE sweep ONE commit. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

# =============================================================================================
# [N13 SIGN-LAW] The absolute sign s_b = sgn(eta_b) carries NO character structure (the sign
# cocycle is NOT a coboundary). FRONTIER-MOVEMENT, NON-MOMENT, EXTEND-proven on _EtaRealNegClosed.
# Brick: _EtaSignNonMultiplicative.lean (axiom-clean {propext,Classical.choice,Quot.sound}, 5 thms).
# Probes: probe_eta_sign_qr_structure.py, probe_eta_sign_witness.py.
# =============================================================================================
#
# CONTEXT. _EtaRealNegClosed proved eta_b is REAL on the neg-closed mu_n (n even), so eta_b = s_b*||eta_b||
# with a discrete SIGN s_b in {+1,-1}. DilationRealSignCocycle then reformulated the open CORE as a
# real +/-1 sign cocycle: a frequency stays on the non-cancelling doubling trajectory iff its descent
# signs are all "+", and the residual is the sign-cocycle large-deviation statement (no all-"+" descent
# word survives). The natural hope to crack THAT is that b -> s_b is multiplicatively structured (a
# quadratic character / Legendre symbol / homomorphism F_p^* / mu_n -> {+/-1}); then the relative
# dilation sign s_{zeta b}/s_b would be a CONSTANT (the cocycle a coboundary), telescoped by characters.
#
# PROBE VERDICT (proper thin mu_n=2^a, p>>n^3, p=1 mod n, multiple primes incl Fermat-type, NEVER n=q-1):
#  H1 s_b coset-constant on F_p^*/mu_n: TRUE (object well-defined).
#  H2 s_b = Legendre(b|p): ~45 to 63% agreement = NOISE. NOT the quadratic character.
#  H3 s_b multiplicative (s_{b1 b2}=s_{b1} s_{b2}): 36 to 69 failures / 120 pairs. MASSIVELY
#     non-multiplicative. b -> s_b is NOT a homomorphism.
#  H4 relative dilation sign s_{zeta b}/s_b constant in b: {-1,+1} (NOT constant) generically.
#  EXPLICIT decidable witness (probe_eta_sign_witness.py): p=89, mu_4={1,34,55,88}, s_2=+1, s_4=s_{2*2}=-1
#  => s_{2*2} != s_2*s_2. The sign fails multiplicativity at the smallest dilation b1=b2=2.
#  (n=16,p=65537 Fermat prime had only 2/120 fails = a Fermat-prime artifact, NOT the general law.)
#
# THE WALL (rule 4, the formal obstruction). The sign is NOT a character, so the sign cocycle is NOT a
# coboundary and NO character/homomorphism descent on s_b can isolate the worst frequency or exclude the
# all-"+" descent word that DilationRealSignCocycle leaves open. Combined with the magnitude side
# (wf-A1: children perfectly phase-aligned at b*, theta@b* = 0 exactly), neither the magnitude nor the
# sign of the dilation recursion carries usable structure: the residual BGK/short-character-sum
# cancellation must come from genuine large-deviation cancellation in a STRUCTURELESS sign word, not a
# character coboundary.
#
# THE BRICK (axiom-clean, 5 thms): etaSign (the +/-1 multiplier), etaSign_eq, etaSign_sq;
# not_monoidHom_of_witness (HEADLINE: a {+/-1} sign failing multiplicativity at one witness is NOT a
# MonoidHom); no_constant_relative_sign (a non-constant relative-dilation factor => no constant c with
# s(zeta x)=c s(x), the H4 obstruction); etaSign_not_monoidHom_of_witness (specialization to eta).
#
# HONEST SCOPE (rules 1,3,6 + asymptotic guard): NOT a CORE closure. The transcendental witness is a
# PROBE input (cosine sums, not Lean-decidable); the Lean content is the abstract obstruction MECHANISM,
# honestly scoped (the witness is a hypothesis, grounded by the probe, not faked). Thinness-essential
# via neg-closure (-1 in mu_{2^a}, the realness this rests on). NON-MOMENT (pure sign/character algebra).
# No capacity/beyond-Johnson/cliff-at-n/2 claim. ONE sweep ONE commit. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## C71-ROUTE-B: Conjecture 7.1 worst-case sparse adversary is MULTI-TERM, not monomial (sol, 2026-06-17)
Post-pivot (231b0ec9c) the prize = above-Johnson O(1)/|F|, reduced by 2026/861 to Conj 7.1 (worst
case <=3-sparse). EXACT full-alpha-sweep bad-set strength on thin mu_n (n=8, k=2, affine pencil
{g0+alpha*f}, g0 = deg-(k+1) monomial not in RS, Johnson agreement thr=4/8, NEVER n=q-1) over three
primes p in {17, 41, 521} spanning p<=n^3 and p>n^3: s1max (monomial directions) = 8 UNIFORMLY,
s23max (genuine 2- and 3-term directions) = 9 UNIFORMLY. So the worst-case <=3-sparse adversary is
STRICTLY multi-term (s23max > s1max), NOT a monomial. CONSTRAINT LEMMA (formalized axiom-clean in
ProximityGap/C71SparseOrbitGap.lean, extending the proven ActionOrbitGeneralF pin): a direction with
>=2 dilation-distinct support terms is NOT a dilation eigenvector (multiterm_not_orbit_eligible), so
its bad set is NOT a union of gamma-orbits => the action-orbit per-line O(1)/|F| compression
(eigenvector-gated, hence monomial-only) provably MISSES the worst case. Localization: even granting
Conj 7.1, closing the prize via the in-tree action-orbit machinery requires a NON-orbit incidence
bound on the multi-term strata; the orbit count alone is insufficient. (probe c71_sparse_orbit_gap;
the earlier probe_c71_sparse_dominance.py v1 was VACUOUS -- measured "is direction low-degree" --
quarantined and rebuilt.) CORE / Conj-7.1 multi-term incidence bound OPEN.

## C71-RESIDUAL: binomial (2-term) strata mu_n-incidence = polynomial-method root-count, NOT orbit (sol, 2026-06-17)
Follow-on to C71-ROUTE-B: the named-open residual was "a NON-orbit incidence bound on the multi-term
strata". First concrete brick on the 2-term (binomial) strata. PROBE (probe_c71_multiterm_incidence_
rootcap.py, EXACT, 8/8 over thin mu_n n=2^a a in {2,3,4}, p=1 mod n with p-1=k*n k>=2 NEVER n=q-1,
multi-prime incl p>n^3 73/521/4129 and Fermat 257): for EVERY genuine 2-term direction f = X^i - c*X^j
(c in mu_n, i != j), (1) #roots(f in mu_n) <= gcd(|i-j|, n) [tight at gcd in the majority], and
(2) max root multiplicity of f at any nonzero point < 2 (the 2-sparse confluent-Vandermonde engine).
MECHANISM: on the punctured domain x != 0, f(x)=0 iff x^(i-j) = c, so the nonzero roots inject into
the (i-j)-th roots of c, of which there are <= i-j (Polynomial.card_nthRoots). FORMALIZED axiom-clean
in ProximityGap/C71BinomialIncidence.lean (binomial_root_iff_pow_eq + binomial_incidence_card_le): the
binomial direction's incidence #{nonzero x in S : x^i - c x^j = 0} <= i - j for any finite S, with
S = mu_n the binomial mu_n-incidence bound. This is a NON-orbit (no dilation-eigenvector hypothesis),
field- and thickness-universal, char-free polynomial-method count -- it COVERS the route-B multi-term
worst case that the action-orbit O(1)/|F| pin provably MISSES. EXTENDS the polynomial-method toolset
(Polynomial.card_nthRoots) + the C71SparseOrbitGap route-B localization; adds no character-sum/BGK
content. HONEST SCOPE: the robust <=(i-j) bound is formalized; the gcd-tight refinement (cyclic-kernel
order) and the 3-term case + the full reduction of the strata-incidence to a soundness bound remain
OPEN. NOT a CORE / Conj-7.1 closure. No capacity/beyond-Johnson/cliff-at-n/2 claim. ONE sweep ONE
commit. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## REFUTATION (2026-06-17, reduce worker): the m-sparse mu_n-incidence is NOT bounded by the term
count (NO "sparse => few mu_n-roots" law). CONSTRAINT LEMMA for the strata->soundness bridge.
CANDIDATE (natural, tempting): after mod-n reduction the direction gbar has m' = #distinct nonzero-coef
residue terms; HOPE deg gcd(X^n-1, gbar) <= m' - 1 (a sparsity-incidence cap, much sharper than the
< n cap). REFUTED: probe_c71_reduced_sparsity_cap.py (EXACT GF(p)[X] gcds, thin mu_n=2^a a in {2,3,4},
p==1 mod n incl p>n^3 + Fermat, NEVER n=q-1, wrap-around supports) -- 46/2152 VIOLATIONS, all of the
shape m'=2 with d=2 > m'-1=1. MECHANISM: a reduced BINOMIAL X^d - c on mu_n already attains
gcd(d,n) roots (the cyclic-kernel order, C71BinomialIncidenceGcd.binomial_incidence_card_le_gcd), and
gcd(d,n) can be as large as n/2 (e.g. n=4, gbar = X^3 - X = X(X-1)(X+1): the two nonzero roots +-1 both
lie in mu_4, so d=2 = gcd(2,4) > m'-1 = 1). So the mu_n-incidence is governed by the CYCLOTOMIC GCD
WITH n, NOT by the number of terms: term-sparsity does NOT cap the incidence. CONSEQUENCE for the
bridge: any strata->soundness reduction that hopes to use "the worst case is <=3-sparse => <=2
incidences" is WRONG -- a 2-sparse direction can already have ~n/2 mu_n-incidences. The incidence cap
that IS true is the gcd object (C71SparseStrataIncidence) refined to the reduced < n form
(C71SparseStrataReduce.sparse_munRoot_card_lt_n, b50602644); the term count buys NOTHING beyond it.
This is why Conj-7.1's <=3-sparse worst-case does NOT trivially give an O(1) incidence -- the residual
is genuinely the gcd/agreement-sharing count, not a sparsity count. NOT a CORE closure; a constraint
on the bridge route. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## SIGNED period-power sum = q*zeroSumCount: the located thinness-essential object now has its EXACT identity (sol, 2026-06-17)
Follow-up to "SIGNED deep period-power cancellation IS thinness-essential" (2026-06-15), which located
the prize's rule-3 lever in sum_{b!=0} eta_b^r (NOT the absolute moment sum_b|eta_b|^{2r}; |.| destroys
the signed cancellation => every moment route is thickness-invariant) and stated "No Lean theorem (a
quantitative signed-cancellation bound = the open core)". POSITIVE structural brick, NOT a refutation:
formalized the EXACT algebraic identity the signed object satisfies (axiom-clean, 2 files):
  signedPeriodPow_eq_zeroSumCount (1a4bfb2ed):  sum_psi (sum_{x in S} psi x)^r = q * #{t:Fin r->S : sum t=0}
  nonzeroSignedPeriodPow_eq:                    sum_{psi!=0} eta_psi^r = q*W_r - |S|^r  (the prize form)
  signedPeriodPow_eq_q_mul_zeroSumCount (f13fd524b): same in canonical NegationClosedWalk.zeroSumCount
    vocabulary (the count is DEFINITIONALLY zeroSumCount S r) => plugs into the K1/energy ladder at
    GENERAL incl ODD order r.
MECHANISM (why the SIGNED sum carries the thin signal the moment |.| discards): for odd r the period-
power sum is q*zeroSumCount of an ODD-length walk -- genuinely signed, NOT a sum of squares -- whereas
every |.|/energy/moment packaging is 2r-fold and non-negative (so sign-blind). The general-r signed
identity is the object neither the in-tree rEnergy_eq_zeroSumCount (2r<->energy bridge, _CharZeroWickEnergy)
nor sum_b|eta|^{2r}=q*E_r (SubgroupGaussSumMoment) covers; both are checked-pre-existing and NOT duplicated.
PROBE probe_signed_periodpow_count_identity.py: 18/18 EXACT (proper thin mu_n n in {4,8}, p==1 mod n,
(p-1)/n>=2, NEVER n=q-1, r in {2,3,4}), both the full-character and nonzero-character forms.
HONEST: NON-MOMENT, field-universal additive-character Fourier identity, EXTEND-proven. Makes the located
thinness-essential object EXACT + reusable + canonically-phrased; it IS a zero-sum count. NOT a CORE bound
-- bounding sum_{psi!=0} eta_psi^r quantitatively at r ~ log q (the deep SIGNED cancellation = q*W_r - n^r
being small) is the open BGK wall. No capacity/beyond-Johnson/cliff-at-n/2 claim. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## REFUTATION (sol, 2026-06-17): the binomial's cyclotomic gcd(d,n) incidence cap does NOT extend to TRINOMIALS
Surveyed (NOT committed as a redundant wall re-map; logged here so it is not re-discovered). The binomial
2-term strata has the SHARP cyclotomic cap #roots in mu_n = gcd(|i-j|,n) (a divisor of n, the cyclic-kernel
order; C71BinomialIncidenceGcd + binattain's sharpness bricks). NATURAL hope: a trinomial (3-term) analog
inc <= gcd(i-j, j-k, n) or gcd(i-k, n). REFUTED: probe_trinomial_munroot_structure.py + _violation_mechanism.py
(EXACT, thin mu_n n in {4,8,16}, p==1 mod n incl p>n^3 + Fermat 257, NEVER n=q-1):
  (A) inc <= gcd(i-j,j-k,n): 44/396 VIOLATIONS. (B) inc <= gcd(i-k,n): 24/396 VIOLATIONS.
  inc | n : FALSE in general (probe_trinomial_incdivn_mechanism.py: n=32 p=97 X^3-c1 X^2-c2 has inc=3, 3 ndvd 32).
EXPLICIT WITNESS: n=8, p=17, X^2 - X - 2 (i,j,k)=(2,1,0) c1=1 c2=2 has inc=2 but gcd(i-j,j-k,n)=gcd(1,1,8)=1.
MECHANISM: the binomial reduces to a SINGLE power x^(i-j)=c whose mu_n-solutions ARE a coset of mu_gcd(d,n)
(cyclically structured => gcd-capped + divides n). A trinomial does NOT reduce to one power, so its mu_n-roots
are NOT a subgroup coset and carry no cyclotomic-divisor structure. The ONLY proven cap is the bare polynomial
degree i-k (in-tree trinGcd_natDegree_le, 0 violations confirmed). CONSEQUENCE for the bridge: the clean
binomial gcd-tight incidence does NOT propagate to the >=3-sparse strata; their incidence is governed by the
generic deg-gcd(X^n-1, .) <= span, NOT a cyclotomic divisor -- consistent with C71-RESIDUAL (gcd, not term-count,
governs incidence). NOT a CORE closure; maps the binomial->trinomial extension wall. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## CONSTRAINT (sol, 2026-06-17): the I031 distinct-period ALPHABET SIZE is THICKNESS-INVARIANT — no metric-entropy lever
The I031 union bound spends metric entropy log(alphabet size); I031DistinctPeriodCount caps the value
alphabet |{eta_b}| and the modulus alphabet |{‖eta_b‖}| each by the orbit/coset count (q-1)/n. NATURAL
hope a metric-entropy argument might lean on: (H1) cross-coset COLLISIONS shrink the alphabet strictly
below (q-1)/n at prize scale (smaller log => tighter union bound); (H2) any such shrink is THIN-SPECIFIC
(thickness-essential), hence a rule-3-legal lever. BOTH REFUTED:
probe_alphabet_thickness_invariance.py (EXACT F_p, PROPER thin mu_n n=2^a, n|p-1, (p-1)/n>=2, primes incl
p>>n^3 + Fermat 257, NEVER n=q-1; one representative per coset):
  - the VALUE alphabet |{eta_b}| = (q-1)/n EXACTLY in every config (160/160 in the collision sweep): the
    Gauss-period map is INJECTIVE on coset labels — NO cross-coset value collision. So there is no
    sub-(q-1)/n collapse of the value alphabet to harvest.
  - the MODULUS alphabet |{‖eta_b‖}| <= the value alphabet, and is occasionally STRICTLY smaller by O(1)
    (n=32, p=32801: |{eta_b}|=1025 but |{‖eta_b‖}|=1024 — a conjugate pair eta, conj(eta) merges under
    ‖.‖). This O(1) drop does NOT move log (log 1024 vs log 1025 ~ identical), so it is not a
    metric-entropy lever.
  - THICKNESS test: thin (beta>>2) and thick (beta~2.3, where the prize bound is FALSE) give the SAME
    alphabet size (q-1)/n. The count is THICKNESS-INVARIANT => carries NO thinness signal => by rule 3 it
    cannot be a standalone prize lever.
MECHANISM: eta_b is constant on each mu_n-coset (eta_dilation_invariant) and DISTINCT across cosets at
every prime tested; the alphabet is exactly the (q-1)/n coset orbits, a formula with NO thickness term.
CONSEQUENCE for the I031 route: the union-bound metric entropy is log((q-1)/n) EXACTLY (not an
over-estimate that thins out) — the thinness signal must live in the MAGNITUDES of the (q-1)/n distinct
periods (the open sup-vs-sqrt(n)-floor gap, GaussPeriodSpectralFrame), NOT in their COUNT. Companion
axiom-clean brick I031ModulusAlphabetRefine.card_distinct_etaNorm_le_card_distinct_eta records the
modulus-<=-value refinement (probe-shown sharp). NOT a CORE closure; a constraint on the I031
metric-entropy face. CORE M(mu_n) <= C sqrt(n log(p/n)) OPEN.

## C71-TRINOMIAL-GAP-GCD OBSTRUCTION (sol, 2026-06-17)
The binomial cyclotomic incidence law `#roots(mu_n, X^i-cX^j) = gcd(|i-j|,n)` does NOT extend to
trinomials by replacing it with a gap-gcd cap `gcd(i-j,j-k,n)`. Exact witness over the proper 8-th
root subgroup of `F_17`: `f=X^2-X-2` has two `mu_8` roots `{2,16}` while `gcd(2-1,1-0,8)=1`.
Probe `probe_c71_trinomial_gcd_obstruction.py` reproduces the witness exactly. Formalized axiom-clean
in `C71TrinomialGcdObstruction.lean`: `witness_trinomial_incidence_card = 2`, `witness_gap_gcd_eq_one`,
and headline `trinomial_gap_gcd_cap_fails`. CONSEQUENCE: the C71 <=3-sparse residual cannot inherit
the binomial cyclic-kernel/gcd(d,n) law on the 3-term strata; the valid non-orbit bound remains the
gcd-with-`X^n-1`/span container from `C71TrinomialIncidence`. NOT a CORE closure, not a Conj-7.1
closure, no capacity/beyond-Johnson/cliff-at-n/2 claim. CORE remains open.

## R=2 SIDON BOUND CANNOT DISCHARGE THE SPECTRAL FRAME (sol, 2026-06-17) — moment-route wall, located exactly
The two-sided spectral frame (GaussPeriodSpectralFrame) brackets M(n)=max_{b≠0}‖η_b‖ between the proven
Parseval floor (≈√n) and the named-OPEN ceiling NearRamanujanSqrtLog: ‖η_b‖ ≤ C·√(n·log(q/n)) with the
prize requiring ABSOLUTE C. The in-tree PROVEN r=2 Sidon bound worst_period_sidon_le (‖η_b‖⁴ ≤ 3qn², i.e.
‖η_b‖ ≤ (3q)^{1/4}√n) DOES discharge that ceiling — but ONLY with the q-dependent constant
  C_Sidon(q,n) = (3q)^{1/4} / √(log(q/n))   [sidonSqrtLogConstant]
via the algebraic identity (3q)^{1/4}√n = C_Sidon·√(n·log(q/n)) (sidon_ceiling_eq_sqrtLog_scaled).
CONSTRAINT: C_Sidon is STRICTLY MONOTONE INCREASING in q at fixed q/n-ratio
(sidonSqrtLogConstant_strictMono_in_q) ⟹ NOT absolute; it diverges like q^{1/4} in the prize regime
q=n^β (β≥4). So the PROVEN r=2 moment level provably CANNOT close the frame with an absolute constant —
the gap is exactly the q^{1/4} over-shoot. The thinness signal the prize needs lives STRICTLY BEYOND the
second moment (consistent with §3 meta-thm + cliff-at-n/2 guard: a single even moment is
thickness-monotone, no √log-over-√q saving). PROBE probe_sidon_vs_nearram.py (EXACT thin μ_n, n=2^a,
p≫n³, proper, never n=q-1, incl Fermat 257): C_forced=(3q)^{1/4}/√(log(q/n)) to ratio 1.0000, grows
2.26→3.08→4.48 as n:4→8→16; true constant C_true=M/√(n log(q/n)) stays ≈1.0–1.4 (the O(1) prize
constant). Formalized axiom-clean in Frontier/SidonFrameConstantDivergence.lean (3 thms). NOT a CORE
closure; a precisely-mapped wall on the additive-moment route. CORE M(μ_n) ≤ C·√(n·log(p/n)) with
absolute C remains OPEN.

## SURVIVAL-TAIL RATE IS NATURALLY cc≈0.6 WITH A≈1; RATE-DOWNSHIFT IS SUBSUMED (sol, 2026-06-17)
Mapping the MGF residual's rate structure so it is not re-derived. The S11 layer-cake equivalence is now
welded BOTH ways: survival ⟹ MGF (Frontier/_wfS11_survival_to_mgf.lean, layercake_double_count +
mgf_le_survival_weighted) and MGF ⟹ moment envelope (_wfS11_layercake_moment.lean). The residual is the
ABSOLUTE (n,p-uniform) survival/MGF constant. Two rate facts, located so nobody re-probes them:
(1) On TRUE thin μ_n spectra (n=2^a, proper (p-1)/n≥2, p>n³, prize β≈4, never n=q-1; p∈{73,89,521,569,
    4129,4177}+Fermat 257) the literal counting survival tail S(s)=#{b:t_b≥s}/P ≤ A·e^{−cc·s} holds with
    A_surv≈1.000 for cc UP TO ≈0.6 (degrading past cc≈0.8 since the spectral max ~log(q/n)). So the
    survival tail naturally lives at rate cc≈0.6, constant ≈1 — the residual is the ABSOLUTENESS of that
    A in n,p, NOT its existence at fixed (n,p). Probe scripts/probes/probe_s11_survival_to_mgf.py.
(2) The pointwise inequality exp(c·t)−1 ≤ (c/(cc−c))·(exp(cc·t)−1) holds for ALL cc>c>0, t≥0 (zero
    violations over t∈[0,10], 2000 pts, multiple (c,cc); provable by f(0)=g(0)=0 + f′≤g′ since
    cc/(cc−c)≥1). It would transfer a rate-cc MGF bound A_cc to a rate-c bound 1+(c/(cc−c))(A_cc−1).
    BUT this is SUBSUMED by the in-tree MGFBound.of_rate_le (raising the exponent rate only increases the
    MGF, so the lower rate c≤cc inherits the SAME constant A_cc trivially) — the refinement is only tighter
    when A_cc≫1, and the measured A_cc≈1, so it carries no new capability. Probe
    scripts/probes/probe_s11_geom_mgf_closure.py (geometric scalar ceiling K=1+c·A/(cc−c); ub≥direct, A≈1).
NET: do NOT add a rate-downshift MGF brick — of_rate_le already does it. The single open input is the
ABSOLUTE survival/MGF constant = BGK. NOT a CORE closure, no capacity/beyond-Johnson/cliff-at-n/2 claim.
CORE M(μ_n) ≤ C·√(n·log(p/n)) with absolute C remains OPEN.

## [N2-uncond-lower-bound] REFUTED — no divergent unconditional lower bound M(n) ≥ √n·ω(n) exists; the floor is REACHABLE (constant-calibrated O(1)), Parseval forces only M ≥ √n (Johnson, the floor's lower side) (2026-06-17, opus-4-8 subagent)

LENS / mandate (negative angle N2): prove an UNCONDITIONAL lower bound M(n) ≥ √n·ω(n) with ω→∞
at worst-case prize-shaped primes, which would make the floor √(n log m) UNATTAINABLE. M(n)=max_{b≠0}|η_b|,
η_b=Σ_{x∈μ_n}e_p(bx), μ_n=order-n=2^μ subgroup, m=(p-1)/n, prize p~n^β β=4–5.

VERDICT: REFUTED. No such divergent lower bound is provable. Three rigorous facts close it:

(1) THE ONLY METHOD-INDEPENDENT LOWER BOUND IS PARSEVAL: Σ_{b≠0}|η_b|² = q·n − n² EXACTLY (machine-verified:
n=16,p=65537 gives 1048336 = 65537·16−256 to the integer; n=8,p=4153 gives 33160 = exact). Averaging over the
q−1 nonzero b: max_b|η_b|² ≥ (qn−n²)/(q−1) ~ n ⟹ **M ≥ √n·(1−o(1))**. This is the floor's LOWER side (= Johnson
1−√ρ), NOT a divergent √n·ω. probe_n2_parseval_lower_bound.py.

(2) THE STRUCTURED (FERMAT-GEOMETRIC) CONSTRUCTION CAPS AT O(log p) COHERENT TERMS. At a Fermat prime p=2^k+1,
ord_p(2)=2k, μ_{2k}=⟨2⟩={±2^j mod p : 0≤j<k}, and η_1 = 2Σ_{j<k}cos(2π2^j/p) = n − Θ(1) (EXACT closed form;
deficit dominated by the j≈k−1 terms where 2^j≈p/2). This is a genuine clean lower bound M ≥ n−O(1) — but ONLY
at n=2k=2log₂(p−1)=O(log p). The 5 known Fermat primes cap at p=65537 ⟹ n=32. probe_n2_fermat_geometric_head.py.

(3) THE GEOMETRIC HEAD IS A VANISHING FRACTION AT PRIZE SCALE. The coherent cluster requires μ_n elements to
equal {±R^j} as INTEGERS (R^j<p), which needs j<log_R p. In the prize regime p~n^β, that is at most
log_R p = β·log_R n = O(log n) terms; the remaining n−O(log n) subgroup elements are R^j mod p which WRAP and
equidistribute (n=ord_p(R) > log₂ p whenever n > β log₂ n, i.e. all n≥16 at β=4), contributing only O(√(n log m))
by cancellation. Empirically (probe_n2_fermat_geometric_head.py / cluster-fraction at p=65537): cluster-fraction
decays 1.0 (n≤8) → 0.25 (n≥1024), and η_1 STOPS growing (oscillates ~√n, even drops to 1.0 at n=65536). So
M ≤ O(log n)+O(√(n log m)) = O(√(n log m)) — the head is LOWER ORDER than the floor.

(4) WORST-CASE RATIO IS BOUNDED, NO GROWTH WITH n (probe_n2_worstcase_ratio_sweep.py, EXACT full b-sweep over
proper μ_n, m=(p-1)/n>1, NEVER n=q−1, p PRIME). Worst M/√(2n log m) over generic + 2-adically-heavy + Fermat
prize-band primes: n=8→0.775, n=16→0.861, n=32→0.959, n=64→1.008 (rises toward but ~1, no divergence); Fermat
p=65537 subgroups peak 1.46; Fermat-factor p=6700417 (β=3.78) gives 1.14. The ratio sits in [0.77,1.46] and does
NOT grow with n. (Consistent with the prior wide scan: worst 0.997 over generic β∈[3.8,4.2].)

WHY A DIVERGENT LOWER BOUND IS UNPROVABLE (the impossibility, made precise): a lower bound M ≥ √n·ω(n) ω→∞ would
require lower-bounding a SPECIFIC |η_b| beyond the √n Parseval average — i.e. exhibiting a frequency b at which
Σ_{x∈μ_n}e_p(bx) FAILS to exhibit square-root cancellation by a divergent factor. That is precisely DISPROVING
equidistribution of the multiplicative subgroup μ_n. Unconditionally the only guaranteed-coherent contribution is
the LITERAL geometric integer head {h^j : h^j<p} of size O(log p)=o(√n); beyond it no unconditional statement
forces coherence (it would be a lower bound on M, the very thing sought). And equidistribution is TRUE for generic
primes (square-root cancellation holds, ratio<1), so any ∀-prime divergent lower bound is FALSE. Hence: the
strongest provable lower bound is M ≥ √n (Parseval/Johnson), the floor √(n log m) is REACHABLE (the upper-side
constant calibrates √2→~2.1 from F3→F4 but stays O(1)), and N2 — "floor unattainable in worst case" — is FALSE.

CONSEQUENCE FOR THE PRIZE (rule-4 map, NOT a closure of #334): N2 is dead as a NEGATIVE route. The floor is
not unreachable; the open content is entirely on the UPPER side (proving M ≤ C√(n log m) at depth r~ln q = the
BGK/Paley char-p energy-transfer wall), not on a lower-bound obstruction. This corroborates the ground-truth
memo: the Fermat datum is a CONSTANT-CALIBRATION fact (√2→2), not a floor-disproof; per-code δ*_C simply takes a
different O(1)-constant value at structured F. The two-sided wall (moment NECESSITY + ERM equivalence) already
pins δ* two-sidedly to BGK; N2 cannot escape it from below. Python-only, exact (integer Parseval check + exact
cosine b-sweep, multi-prime incl. Fermat + 2-adic-heavy + non-Fermat), no Lean changed ⇒ axiom-clean trivially.

## [N8-structured-prime-density] floor-violator DENSITY among prize-shaped primes — NO-GAIN (m-resolved; sharp √2 grazed at vanishing margin, order-law/absorb-floor 0 violators) (2026-06-17, opus-4-8 subagent)

Lens: N8 asks whether floor-VIOLATING structured/near-2-group primes have POSITIVE DENSITY among
prize-shaped primes (p≡1 mod n, proper μ_n: n=2^μ, m=(p-1)/n>1). If a positive fraction violate the
floor at every scale, the "∀ sufficiently large smooth F" reading of δ*=1−ρ−Θ(1/log n) is FALSE and
δ* (so read) is unattainable. This SHARPENS the prior N2 (worst-case-only) entry with DENSITY + the
m-scaling, and resolves the apparent tension between the structured anomaly (Fermat) and the asymptotics.

Two floors measured separately over real prime samples (EXACT M=max_{b≠0}|η_b| over m coset reps,
float err≪1): SHARP M≤√(2n ln m) [char-0 Wick constant √2]; ABSORB M≤2√(n ln p) [the survivor, C=2].

PROBES (scripts/probes/, Python-only, no Lean ⇒ axiom-clean trivially):
 - probe_n8_floor_violator_density.py — prize window, all p≡1 mod n; denA rises 0,0,.005,.035 (n=8..64)
   BUT window collapsed (m-cap forced p→n^3.6), so the rise was suspected an m-collapse artifact.
 - probe_n8_density_mcontrolled.py — coset-count m held in FIXED band [256,4096] across n, v2-split.
   SHARP-floor density at comparable-m: gen 0,0,.012,.086,.100,.083; STRUCTURED (v2≥μ+3) 0,0,0,.163,
   .116,.189 (n=8..256). So at FIXED small m the density is ~8–19%, structured higher — NOT an artifact;
   BUT at fixed m, β=log_n p DROPS to ~2 (out of the β≈4 prize regime): the controlling variable is m.
 - probe_n8_density_vs_m.py + probe_n8_largeM_extrapolation.py — sweep m across octaves 2^8..2^18 at
   n=32,64, sup_p over each octave. DECISIVE TABLE (n=64): supR_sharp by log2 m =
   1.27, 1.46(F4=65537,v2=16), 1.17, 0.97, 0.999, 0.957, 0.889 over log2 m=8,10,11,12,14,16,17;
   (R_sharp−1)·ln m = 1.49, 3.22, 1.27, −0.23, −0.006, −0.47, −1.31. The worst-over-ALL-primes SHARP
   ratio PEAKS ~1.46 at SMALL m (Fermat) and DECAYS below 1 for log2 m≳12, monotone in the high-m half
   (trend −0.083 @n=64, −0.026 @n=32). The ABSORB ratio sup_p R_abs ≤ 0.8189 EVERYWHERE (all m, all n,
   incl. every Fermat/2-adically-deep prime up to v2=20) ⇒ ZERO violators of the C=2 floor.

EXACT RESULT: (1) ABSORB floor M≤2√(n ln p): 0 violations across the entire m-octave sweep
(sup R_abs=0.8189, at F4 n=64 m=1024). (2) SHARP floor M≤√(2n ln m): positive-density grazing >1 ONLY
at small m (≤2^11), worst 1.46 at Fermat F4; the overshoot margin SHRINKS like O(1/ln m) (EV-theory:
max of m near-indep cosine cosets = √n·√(2 ln m)·(1+O(ln ln m/ln m))) and the worst case crosses BELOW 1
by log2 m≈12. Prize m~2^90 ≫ 2^12 ⇒ extrapolated overshoot ≈0.

WALL / VERDICT (NO-GAIN as a negative closure; rigorous): the ONLY persistent positive-density violation
is of the SHARP √2 CONSTANT, by a VANISHING margin, confined to SMALL-m structured (high-v2) primes —
i.e. exactly the already-known (N1/N2, ground-truth memo) constant-calibration fact √2→C, absorbed by C=2.
There is NO positive-density violation of the ORDER LAW M=O(√(n log m)) at any m, and NO violation
whatsoever of the surviving absorb-floor C=2. Hence floor-violator density does NOT obstruct the prize:
the per-code δ*_C order law survives, structured primes only shift the O(1) constant. A rigorous negative
closure cannot be harvested from violator density; it would require the per-code δ*_C UNPINNABLE in closed
form in the asymptotic regime, which routes to the BGK/Paley char-p energy-transfer core, not to density.
EXTRAPOLATION CAVEAT (honest): the m→2^90 conclusion is an extreme-value-theory-grounded EXTRAPOLATION
from m≤2^18 (compute ceiling for exact M), not a proof; it is consistent with the proven Plancherel
identity Σ_{b≠0}|η_b|²=n(p−n) (fixed L² mass ⇒ M/√n=O(√log m) bounded, structured primes concentrate
the fixed mass onto fewer cosets = larger constant, cannot grow the order).

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>

## [T01-T25 ANT fence-threading sweep] 24 invented "escape" theorems, 5 design clusters — 0 SURVIVORS, 5 REFUTED, 19 REDUCES-TO-WALL (2026-06-17, opus-4-8 synthesis lane)

Lens: a fresh batch of 24 candidate ANT theorems (IDs T01-T05, TT06-TT10, T11-T16, T18-T25; T17 never
generated) were INVENTED to thread the proven fence map F0-F11 around the prize object M(n)=max_{b≠0}|η_b|,
η_b=Σ_{x∈μ_n}e_p(bx), prize regime n=2^30, p=n^4 (β=4), p≡1 mod n. Five design clusters, each engineered to
make exactly one fence the only one with bite and to name the dodge explicitly:
  G1 parameter-space / sheaf-in-a-family / Deligne (T01-T05),
  G2 adelic / joint archimedean×non-archimedean / heights / equidistribution (TT06-TT10),
  G3 information functionals OTHER than Rényi-2 (min-entropy, rate function, Rényi-α, Kolmogorov/MDL,
     conditional entropy) (T11-T15),
  G4 post-2020 additive combinatorics STRUCTURE/COVERING (Chang/Sanders/bilinear-Bogolyubov/PFR) (T16,T18-T20),
  G5 dynamical / operator-algebraic / determinantal / motivic-higher (T21-T25).
Each candidate has its own axiom-clean Lean file Frontier/_wfT{ID}_*.lean (#print axioms ⊆
{propext,Classical.choice,Quot.sound}, no sorryAx) recording the reduction/refutation, plus (most) a Rust/Python
probe at the genuine β=4 / p≡1 mod n / proper-μ_n regime (never n=q−1).

RESULT (post adversarial re-verification): 0 SURVIVORS. The no-escape terminal is REINFORCED, not cracked.

REFUTED (5) — internally false at prize scale, not merely reducible:
 - TT06 coupled product-formula House: SIGN-REVERSED. For an algebraic integer θ_b the product formula gives
   Σ_{arch}log|wθ_b| = log|N(θ_b)| ≥ 0, so a positive non-arch content D(b) is a LOWER bound logHouse≥D(b),
   the OPPOSITE of the claimed "budget decrease." Counterexample θ=1+ζ_8: House=√(2+√2)≈1.848 > exp(2D)=√2≈1.414.
 - TT08 Arakelov self-intersection: same sign-reversal; deĝ(div̂ θ)=0 ⇒ arch log-mass EQUALS non-arch content
   (move together). β=4 counterexamples (n=8..128, exhaustive conjugates): true House~5√n vs candidate ceiling
   √n·exp(−content)~1.88 (SHRINKS); violation factor ~30 at n=128, ~86000 extrapolated at n=2^30.
 - TT10 Mahler/Lehmer^{1/k_b}: AM-GM REVERSED. Mahler(Ψ_b)^{1/k_b} is the GEOMETRIC MEAN of the k_b large
   conjugates ≤ max = House (lower bound only). β=4 probe: House 7.30/13.84/22.98 vs geom-mean 2.62/3.27/4.24
   (gap grows) at n=8/16/32.
 - T22 determinantal count rigidity: spectrum of Cay(F_p,μ_n)=Γ(k,p) has k=(p−1)/n DISTINCT periods EACH of
   multiplicity exactly n ⇒ N(t) is always a multiple of n, n-fold atomic = maximally NON-simple; a CD
   PROJECTION-kernel DPP is a.s. SIMPLE. Determinantal/log-rigidity hypothesis is FALSE by algebraic spectrum
   (Liu-Zhou Thm 115 / Podestá-Videla). Surviving sup-deduction half reduces to F1.
 - T25 Rajchman a.c. density: ℓ²(F_p) is finite-dim ⇒ Koopman unitary is pure-point (atomic) ⇒ the bounded a.c.
   density ρ_max DOES NOT EXIST. On H_η the coefficients μ̂_V(k)≡1 ⇒ δ_1, the MOST non-Rajchman measure. Only
   well-posed surrogate (Wiener |μ̂|² mass) = Parseval energy Σ|η_b|^{2r} = F1.

REDUCES-TO-WALL (19), fence distribution (primary fence):
 - F0 conservation law (tail/rare-event invisible to 2nd-order domain arithmetic): T09, T14, T18, T23  (+ as the
   meta-fence underneath T01,T02,T04,T11,T15,T24).
 - F1 moment/energy/cumulant conjugacy (incl. Legendre/Cramér duals, Chang=Rudin=Khintchine, Fekete=disc=power-sums):
   T04, T07, T12, T13, T16, T19, T24  (+ secondary on most others).
 - F3 p-adic/valuation archimedean-blind (Dwork/Frobenius slope, Stickelberger, valuationClass_barrier): T03, TT07.
 - F7 Rényi-2 = additive energy (sub-Gaussian level-set decay / Rényi-α flatness = deep-moment ladder): T11, T13.
 - F10 FKM/sheaf conductor floor (cond ≥ rank = 2nd moment; Drinfeld diagonal collapse): T01, T02.
 - F5 abelian Cayley gap (cyclic μ_n ⇒ H²(Z/n,T)=0 ⇒ Λ_cb^θ≡1; Frobenius on F_p is identity since p≡1 mod n):
   T20, T21.
Recurring kill mechanisms: (i) SIGN-REVERSAL of every height/capacity/Mahler/Arakelov "ceiling" into a LOWER
bound via the product formula on algebraic-integer periods (TT06/TT08/TT10/TT07/T23 all share it); (ii)
DIAGONAL/RANK COLLAPSE of every manufactured higher-dim family back onto the rank-n 2nd moment (T01/T02/T05/T22);
(iii) LEGENDRE-DUAL recoordinatization of the tail (rate function ↔ EVT depth ↔ min-entropy ↔ moment ladder)
all carrying the SAME open char-p energy transfer E_r≤(2r−1)‼·n^r at r~ln q = the BGK/Paley wall (T04/T11/T12/
T13/T15/T24); (iv) p≡1 mod n forces the decomposition-group Frobenius to be the IDENTITY, killing every
"p-sensitive Galois/Frobenius 2-power" lever (T20).

WALL / VERDICT: REINFORCED no-escape terminal. Across these 24 + the prior 84+ invented escapes the running
count is 0 survivors. The prize sup M(n) is, in every framing attempted, either (a) read off a rank-n / 2nd-moment
object capped at Johnson √n (F0/F1/F10), (b) a p-blind valuation datum (F3), (c) a vacuous abelian/finite-group
gap (F5), or (d) an internally sign-reversed / structurally false construction (the 5 REFUTED). The only honest
residual everywhere is the char-p energy transfer at depth r~ln q (char-0 PROVEN, char-p OPEN) = the irreducible
25-yr BGK/Paley conjugate-norm wall. Lean: 24 axiom-clean Frontier/_wfT*.lean files; ArkLib.lean umbrella
regenerated to import all 24. No #334/#444 closure.

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>

## [census-necessity-skeleton] the count/census <-> CORE equivalence necessity half is ASSEMBLED but the cap=>CORE direction is WALLED at the spectral bound (the census face alone cannot supply M(mu_n)) (2026-06-17, opus-4-8 subagent)

Lane: the brief's named "asserted but never proven" census<->CORE equivalence. This entry MAPS the
boundary precisely after landing the necessity skeleton (commits da4fcd3f9, 5d71f5624, b76f9c518).

WHAT IS NOW PROVEN (axiom-clean, in-tree):
 FORWARD (sufficiency): epsMCA_le_of_alignableSets_card_le — a uniform census cap L => eps_mca <= L/|F|.
 NECESSITY FLOOR (single set): choose_card_le_alignableSets — one gamma-aligned set A with a non-deg
   (k+1)-tuple forces C(|A|-(k+1), a-(k+1)) <= #alignableSets.
 NECESSITY CONTRAPOSITIVE: no_large_aligned_of_census_cap / not_aligned_of_census_cap_lt /
   census_cap_ge_full_domain_supply — a census cap K forbids aligned sets whose subset supply > K;
   prize band (A=univ): C(n-(k+1),a-(k+1)) <= K.
 NECESSITY MULTI-SCALAR: sum_choose_le_alignableSets / card_mul_choose_le_alignableSets — supplies
   ADD across the DISJOINT scalar partition (#alignableSets = sum_g #alignedSetsForScalar g): if P
   distinct bad scalars each align the full domain, #P * C(n-(k+1),a-(k+1)) <= #alignableSets. So a
   cap K bounds BOTH the bad-scalar COUNT and each one's aligned SIZE.

THE EXACT GAP (the wall, made precise): the equivalence's MISSING direction is cap => CORE, i.e.
"#alignableSets <= rm+1 (the prize cap) => M(mu_n) <= C sqrt(n log(p/n))". The census face is a
COMBINATORIAL/incidence object over a-subsets of the domain; CORE is a SIGNED character-sum bound.
The necessity skeleton above shows the census cap CONTROLS the agreement/list structure (size + count
of aligned sets) from below — but turning a census UPPER bound (#alignableSets <= rm+1) into the
SPECTRAL bound M <= C sqrt(n log(p/n)) requires bounding #alignableSets ABOVE, which is precisely the
open CORE: the census face cannot self-supply its own upper bound. Concretely, the per-scalar supply
C(n-(k+1),a-(k+1)) is a LOWER bound on the census from a single deep agreement set; proving the cap
rm+1 holds = proving NO scalar has a deep aligned set beyond the list-decoding radius = the BGK/Paley
signed-cancellation wall. CONSISTENT with the meta-thm: the unsigned combinatorial census face
collapses to the agreement-sharing/Johnson contribution; the beyond-Johnson gap lives in the signed
contribution (same conclusion as the over-det cliff-at-n/2 guard). The census EQUIVALENCE is a real
brick to assemble (now done on the necessity side), but it does NOT route AROUND the spectral wall —
it RE-EXPRESSES the wall as "the census cap rm+1 is itself unproven", a faithful reformulation, not
an escape. No CORE closure; no growth-law claim; asymptotic guard untouched. Lean-free entry (doc) =>
axiom-clean trivially.

## [meanfloor-saturates-johnson] the power-sum mean floor S_1/S_0 on the Gauss-period spectrum SATURATES EXACTLY at Johnson sqrt(n) in the prize regime — the easy lower direction is capped (2026-06-18, opus-4-8 subagent)

Lane: quantify the prize-regime TEETH of the just-landed depth-uniform mean floor
(PowerSumRatioMeanFloor.powerSum_ratio_ge_base: S_1/S_0 <= S_{t+1}/S_t <= max a = M(n)^2).

CONSTRAINT LEMMA (probe scripts/probes/probe_meanfloor_prize_teeth.py, exact Gauss periods on
2-power subgroups mu_n = <g> of order n=2^a in F_p^*, b != 0):
  S_1/S_0 = (sum_{b!=0} |eta_b|^2)/(p-1) = mean square of the Gauss periods, and mean/n -> 1 as
  beta = log_n(p) grows. Measured: (p=17,n=8) mean/n=0.5625; (p=41,n=8) 0.825; (p=97,n=16) 0.844;
  (p=65537,n=16,beta=4 prize-regime) mean/n=0.9998.
  => the mean floor gives M(n)^2 >= S_1/S_0 ~ n in the prize regime, i.e. M(n) >= sqrt(n) EXACTLY
  the Johnson/Weil floor, and NO MORE. The L2-mass identity sum_{b!=0}|eta_b|^2 = n(p-n) (Parseval,
  ConcreteParsevalLower) divided by p-1 -> n as p/n -> inf forces mean/n -> 1 from below; the mean
  floor CANNOT exceed n, so it CANNOT beat sqrt(n) as a lower bound on M(n).

WHY THIS IS A WALL (consistent with the meta-thm + DISPROOF terminal): the mean floor is the
2nd-moment (Renyi-2 / additive-energy) read of the spectrum (F1/F7 face). By the F0/F1 fence it is
capped at the Johnson sqrt(n) contribution — it bounds M(n) from the WRONG (easy/lower) side and
saturates at the agreement-sharing/Johnson value n. The beyond-Johnson gap lives in the SIGNED
sup-norm UPPER bound (the open char-p energy transfer), which no mean/2nd-moment lower object can
supply. So the ENTIRE power-sum-ratio LOWER-bracket family (ladder_antitone's lower companion,
powerSum_ratio_monotone, the mean floor, the log-convexity spacing) is structurally pinned at
Johnson: it localizes max a from BELOW but its floor saturates at the L2 mean = n. This MAPS the
ceiling of the lower-bracket lane precisely: real reusable structure, zero beyond-Johnson teeth.
No CORE closure; no char-p transfer; no capacity/growth-law; asymptotic guard untouched (this is a
LOWER bound, structurally orthogonal to cliff-at-n/2). Lean-free constraint entry (doc, probe-backed).

Co-Authored-By: wakesync <shadow@shad0w.xyz>

## [graded-weight-injectivity] the depth-r graded-weight map is INJECTIVE on signed relations of support r => tower-depth is bounded by support size, NOT free (2026-06-18, opus-4-8 subagent)

CONSTRAINT (the brick): for the 2-adic graded tower (_TwoAdicGradedTower.lean: D == sum_{j<l} sigma_j t^j
mod I^l, sigma_j = sum_i eps_i C(a_i,j)), the graded-weight map eps -> (sigma_0,...,sigma_{r-1}) on a
signed relation supported on r DISTINCT exponents A = {a_1,...,a_r} is the r x r Pascal/binomial matrix
P[i][j] = C(a_i, j). This matrix is NONSINGULAR for distinct a_i (probe_sigma_rank.py: 0 singular /
1730 cases, n=8,16,32, r=2..5) -- it column-reduces to a Vandermonde prod_{i<j}(a_i - a_j) != 0 since
C(X,j) is a degree-j monic-up-to-1/j! polynomial in X.

CONSEQUENCE: a NONZERO signed relation on r distinct exponents CANNOT have sigma_0 = ... = sigma_{r-1} = 0.
At least one of the first r graded moments is nonzero. Via the tower congruence this means the
graded-weight map is INJECTIVE up to depth r: the 2-adic descent v_lambda(D) cannot be forced arbitrarily
deep by "all moments vanish through depth r" -- the depth at which all sigma_j (j<l) vanish is < r for any
nonzero relation. (The PARITY version -- all sigma_j EVEN through depth l -- is a coarser, separate
condition: evenness is not vanishing, so v_lambda can exceed r via even-but-nonzero moments; this entry
bounds the VANISHING depth, the Sidon-exactness, not the valuation depth.)

RELEVANCE: this is the support-size <-> Sidon-depth interaction in the brief's "B_infty <- B_{log n} Sidon
bootstrap" lane: the graded weights cannot all vanish below the support size, so deep Sidon-exactness
(sigma_j = 0 for many j) FORCES large support r. Does NOT cross the BGK wall: it constrains the VANISHING
structure of low-order moments, while the prize sup M(n) lives in the char-p energy transfer at depth
r ~ ln q (the open conjugate-norm wall). The parity/valuation criterion (the actual gate) is governed by
the LOCAL arithmetic of Z[zeta_{2^mu}] (v_lambda(2) = e = n/2), orthogonal to this rank fact.

STATUS: probe-backed (1730 cases, 0 singular) + reducible to the standard Vandermonde nonsingularity
(det P = c * prod_{i<j}(a_i - a_j), c != 0). Lean formalization of det P != 0 deferred (column-op reduction
to det_vandermonde is a heavier proof; logged as constraint to honor probe-first + no-overclaim). No CORE
closure, no capacity/growth-law claim, asymptotic guard untouched.

Co-Authored-By: wakesync <shadow@shad0w.xyz>

## [door-(iv) Lane-1] the WORST-`b` SET is coset-closed + additively SPREAD — no additive structure to exploit beyond the proven multiplicative coset-invariance (2026-06-18, opus-4-8 subagent)

Lens: the brief's SINGLE LIVE TARGET Lane-1 question (Shaw-value essay 2026-06-18): "what arithmetic of
`b` selects the worst coset alignment? is the worst-`b` SET itself structured?" — the door-(iv) hope being
an arithmetic anti-concentration of the worst-`b` set `W(thr)={b≠0 : ‖η_b‖≥thr}` that a moment-free /
completion-free bound could grip. `η_b = Σ_{x∈μ_n} e_p(bx)`, prize regime: PROPER thin `μ_n<F_p^*`,
`p≡1 mod n`, `p≫n³`, `m=(p-1)/n` ODD, NEVER `n=q−1`.

PROBES (probe-first, NO moment, NO completion):
 (1) scripts/probes/probe_444_worstb_set_arithmetic.py — structure of `W(thr)` on the `F_p^*` line,
     `n=8,16,32`, `β=4,4.5`, `τ∈{2,5,10}%`. RESULT: `W` is ALWAYS exactly a union of full `μ_n`-cosets
     (`muOrbit=True`, `|W|/n` an integer = #cosets) and negation-symmetric (`-b*` near-max always). It is
     NOT a square-coset and NOT a single multiplicative-`g` orbit. Additively `|W+W|/|W|` GROWS with `n`
     (Sidon-like / spread), longest AP ≤ 3-4.
 (2) scripts/probes/probe_444_worstcoset_quotient_structure.py — the SHARP test: quotient out the PROVEN
     coset-invariance (`η` descends to `F_p^*/μ_n ≅ ℤ_m`) and ask whether the worst-COSET set
     `W_q⊆ℤ_m` is additively structured. `n=8..32`, `β=4..5`. RESULT: `W_q` is NOT dilation-closed in
     `ℤ_m^×` (`dilClosed=False`), has no nontrivial AP (`longestAP_{ℤ_m}≤4`), `|W_q+W_q|/|W_q|` grows
     toward `|W_q|` (spread), and the magnitude profile `f(j)=‖η(g^j)‖` on `ℤ_m` is Fourier-FLAT:
     `‖f̂‖_∞/‖f̂‖_2` is within `≈1.2–2.2×` of the flat baseline `1/√(m/2)` and SHRINKS toward it as `m`
     grows; top-5 frequency mass fractions ≈ `1e-4..6e-3` (no frequency carries appreciable mass).
 (3) scripts/probes/probe_444_worstcoset_quotient_structure_b.py — adversarial re-checks:
     (a) generator-INDEPENDENCE: the flatness statistic is IDENTICAL across two distinct generators
     (it must be — a different generator is a dilation of `ℤ_m`, and the statistic is dilation-invariant).
     (b) STRUCTURED Fermat-type primes, `v₂(p−1)` up to 16 incl. `p=65537=F₄`: NO Fourier concentration
     appears; flatness ratio stays in `[1.18, 1.99]`. Structured primes do not create exploitable structure.

EXACT RESULT / WALL: the ONLY forced structure of the worst-`b` set is the PROVEN multiplicative
coset-invariance `‖η_{cb}‖=‖η_b‖` for `c∈μ_n` (commit 9909ef905 `_EtaCosetInvariance.norm_eta_dilate_eq`)
plus the antipodal `c=−1` case — i.e. `W(thr)` is exactly the `μ_n`-orbit-closure of a subset `W_q⊆ℤ_m`.
Once that (trivial, already-proven) multiplicative symmetry is quotiented out, the worst-coset set on `ℤ_m`
carries NO residual additive structure (not an AP, not dilation-closed, additively Sidon-spread, Fourier-flat
magnitude profile, generator-independent, robust to structured primes). Hence the door-(iv) Lane-1 sub-hope
"the worst-`b` SET is additively structured" is REFUTED in the computed prize regime: there is no additive
handle for a moment-free / completion-free anti-concentration lever to grip. The structure is PURELY
multiplicative (the coset-invariance) and additively generic. This is CONSISTENT with the meta-theorem (the
exploitable structure is the multiplicative coset-collapse to `m=(p-1)/n` distinct eigenvalues, already known;
turning the flat per-coset profile into the signed sup-norm bound is still the char-`p` BGK/Paley wall). NO
`M`-bound, NO CORE/capacity/growth-law claim; asymptotic cliff-at-n/2 guard untouched (this is a worst-SET
structure result, not an over-det incidence claim).

Lean (axiom-clean, `⊆{propext,Classical.choice,Quot.sound}`): Frontier/_WorstBSetCosetClosed.lean —
`mem_worstSet_dilate_iff` (worst-`b` set is `μ_n`-coset-closed: `c·b∈W ↔ b∈W`), `worstSet_dilate_mem`,
`maximiser_orbit` (the maximiser is never isolated). Formalises the PROVEN half (the coset-closure of the
argmax set, downstream of `norm_eta_dilate_eq`); the additive-flatness verdict is the empirical NOTE. No
#444 closure (constraint lemma + regime-bounded refutation of a sub-hope, not a breakthrough).

## [door-iv-coset-half-degeneracy] raw index-2 coset-half coherence saturates at rho=1 on same-sign half-periods (2026-06-18, g55)

Lane: Door-(iv) localized object, Lane 1. Probe `scripts/probes/probe_dooriv_cosethalf_coherence.py` split the 2-power subgroup H into H0=<h^2> and H1=hH0 and measured
`rho(b)=|A_b+B_b|/(|A_b|+|B_b|)` over quotient cosets bH, where A_b and B_b are the two half-period sums.

RESULT: the raw two-piece object is sign-degenerate. For n divisible by 4, both H0 and H1 are closed under negation, hence A_b and B_b are real. Whenever they have the same sign, rho(b)=1 exactly. Full scans in prize-regime primes found same-sign half sums for about half the quotient cosets and the adversarial |eta| cosets inside that same-sign set:
- n=16, p=65537: 2045/4096 same-sign, best rho=1.000000.
- n=32, p=1048609: 16315/32769 same-sign, best rho=1.000000.
- n=64, p=16777153: 131320/262143 same-sign, best rho=1.000000.
- n=128, p=268437889: 120k-coset sample, best sampled rho=1.000000.
Top worst-b representatives are not explained by small additive b or q=b^n near ±1.

Lean: `ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_nonneg`, `_of_nonpos`, and `_of_sameSign` prove axiom-clean that real same-sign two-piece sums have coherence exactly 1. Axioms: propext, Classical.choice, Quot.sound.

VERDICT: this does NOT close CORE. It refutes the naive/raw index-2 coset-half anti-concentration lever: the worst-b coset-half coherence has no upper slack because the split is negation-stable and same-sign cases saturate rho=1. Any surviving door-(iv) theorem must use a finer/non-negation-stable decomposition or a different arithmetic statistic of {b*x^m}; the two-half coherence by itself cannot be bounded below 1.

Co-authored-by: wakesync <shadow@shad0w.xyz>

## [door-iv-multipiece-sign-coherence] negation-stable refinements still have sign-saturation, so subdivision alone does not create phase anti-concentration (2026-06-18, g55)

Lane: Door-(iv) localized coherence object, Lane 1/3 constraint.  After the raw index-2 split saturated
at `rho=1`, the natural follow-up was to subdivide the 2-power subgroup into more cosets and ask whether
finer pieces force phase spread.  Probe `scripts/probes/probe_dooriv_multipiece_sign_coherence.py` split
`H` into `d` cosets of `<h^d>` for `d=4,8`.  In the 2-power prize regime with `d | n/2`, every piece is
still negation-stable, hence every piece-period sum is real.  Therefore the normalized coherence
`rho_d(b)=|sum_j A_j|/sum_j |A_j|` again saturates at `1` whenever all real pieces have one sign.

Probe results, proper thin subgroups `p≈n^4`, never full group:
- `d=4`: all-same-sign fibers occur at about `12.4%` of quotient cosets for `n=16,32,64,128`; the top
  `|eta_b|` rows in the scan all had `rho_4=1`.
- `d=8`: all-same-sign fibers occur at about `0.78%` of quotient cosets; nevertheless the adversarial or
  near-adversarial rows repeatedly still hit `rho_8=1` (e.g. `n=16,64,128`, and top rows at `n=32`).

Lean: `Frontier/_DoorIVMultiPieceSignCoherence.lean` proves axiom-clean real-analysis constraints
`multiPieceCoherence_eq_one_of_nonneg`, `_of_nonpos`, and `_of_sameSign`: for any finite family of real
pieces, if all pieces have one sign and the total is nonzero, `|sum A_i|/sum |A_i| = 1`.

VERDICT: this is not CORE and not a moment/completion route.  It refutes the naive refinement hope
"split the coset halves into more negation-stable cosets and get automatic phase anti-concentration":
same-sign fibers survive and saturate exactly.  A surviving door-(iv) theorem must use a genuinely
non-negation-stable/asymmetric statistic or new arithmetic of `{b*x^m}`, not only a finer subdivision of
negation-stable cosets.

Co-authored-by: wakesync <shadow@shad0w.xyz>

## [door-iv-real-sign-mass-slack] any real refinement needs minority sign mass, not just more pieces (2026-06-18, g55)

Lane: Door-(iv) localized coherence object, Lane 3 constraint.  After the half-coherence and multi-piece
sign-saturation bricks, the exact obstruction can be stated in one real formula.  For any negation-stable
refinement, the piece periods are real.  Compress the positive pieces to total mass `P ≥ 0` and the
negative pieces to total mass `N ≥ 0`.  The coherence becomes `|P-N|/(P+N)`, and its slack from `1` is
exactly twice the minority sign mass divided by total mass.

Lean: `Frontier/_DoorIVRealSignMassSlack.lean` proves axiom-clean:
- `signMassCoherence_eq_one_sub_twice_neg`: if `N ≤ P`, then coherence is `1 - 2N/(P+N)`.
- `signMassCoherence_eq_one_sub_twice_pos`: if `P ≤ N`, then coherence is `1 - 2P/(P+N)`.
- `signMassCoherence_le_one`: nonnegative sign masses always have coherence at most `1`.

VERDICT: this does not close CORE.  It pins the burden for any surviving real/negation-stable door-(iv)
refinement: prove a genuine lower bound on the minority sign mass.  Subdivision alone is empty; same-sign
or highly imbalanced fibers keep coherence near `1`.

Co-authored-by: wakesync <shadow@shad0w.xyz>

## [door-iv-common-ray-coherence] constraint — ray-collinear piece decompositions have rho=1, so subdivision alone cannot supply anti-concentration (2026-06-18, g55 subagent)

Lane: Door-IV / Lane 3 constraint lemma for the localized worst-frequency coherence object
`rho = |Σ pieces| / Σ |pieces|`.

VERDICT: Any split whose complex pieces lie on one closed ray has exact triangle-inequality
saturation: if pieces are nonnegative real multiples of a fixed unit complex direction, then
`rho = 1`. This generalizes the earlier real same-sign / proper-coset real-piece obstruction to
arbitrary complex common-ray decompositions. Therefore a proposed door-(iv) anti-concentration
argument must first prove genuine angular spread of the pieces at the adversarial `b`; merely
subdividing the sum into more ray-collinear pieces cannot create cancellation slack.

Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DoorIVCommonRayCoherence.lean` proves
`sum_commonRay`, `sum_abs_commonRay_of_unit_of_nonneg`, and
`complexPieceCoherence_eq_one_of_commonRay_nonneg`, axiom-clean. No CORE/capacity claim.

## [door-iv-common-ray-epsilon-drop] constraint — strict coherence gain requires triangle-defect/angular spread (2026-06-18, g55 subagent)

Follow-up to `[door-iv-common-ray-coherence]` after concurrent two-piece same-ray work landed.  The
finite-list extension now also proves the universal triangle ceiling `rho <= 1` for arbitrary complex
piece lists and the epsilon-drop obstruction: if a nonzero common-ray decomposition has `rho = 1`,
then no positive `rho <= 1 - eps` bound can hold.  Thus any anti-concentration claim on the localized
Door-IV coherence must exhibit a genuine triangle-inequality deficit (angular spread/non-collinearity)
for the adversarial pieces; an epsilon improvement cannot be obtained from bookkeeping alone.

Lean: extended `Frontier/_DoorIVCommonRayCoherence.lean` with `norm_sum_le_sum_norm`,
`complexPieceCoherence_le_one`, and `commonRay_not_complexPieceCoherence_le_one_sub`, axiom-clean.
No CORE/capacity claim.

## [door-iv-sector-coherence] constraint — near-ray sectors still block strict coherence drops (2026-06-18, g55 subagent)

Lane: Door-(iv) Lane 3 constraint lemma, following the common-ray and two-piece same-ray
obstructions.  Common-ray saturation (`ρ=1`) is not the only trap: if every complex piece has
projection at least `c·‖z‖` along one unit direction, then the normalized piece coherence satisfies
`c ≤ ρ`.  Therefore any claimed bound `ρ ≤ θ` must prove that the worst-frequency phase pieces escape
every sector with projection floor `c > θ`; merely proving a decomposition is not exactly collinear,
or subdividing it further, is insufficient.

Machine-checked brick: `Frontier/_DoorIVSectorCoherence.lean` proves
`sector_floor_le_complexPieceCoherence` and `not_complexPieceCoherence_le_of_sector_floor` by real
projection and the complex norm bound.  This is a constraint theorem only, not a CORE/cancellation
claim: it localizes the door-(iv) obligation to quantitative angular spread of the pieces.
