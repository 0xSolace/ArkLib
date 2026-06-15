# I031 next-steps audit: orbit-reduction, sup-comparison, cumulant/Stepanov (#444, 2026-06-15)

Honest status of the four I031 follow-ups dispatched after the quotient-chaining decider.
I031 = the campaign's live lead: the Gauss period over the smooth `2^μ`-subgroup `μ_n ⊆ F_p^*`
is **orbit-invariant** (`η_{ζb}=η_b` for `ζ∈μ_n`), so there are only `m=(p-1)/n` distinct
periods indexed by the quotient `F_p^*/μ_n`. The hope: group-invariant chaining on the
quotient collapses the metric entropy from `log p` (the wall) to `log(p/n)` (the floor),
recovering exponent `1/2` in `M ≲ C·√(n·log(p/n))`. The OPEN LEMMA (b) is the
deterministic→matched-Gaussian sup comparison `M ≤ C·E sup_b|G_b|` with bounded `C`.

## TL;DR — the strongest result first

**The orbit-reduction LANDED axiom-clean (the deterministic prerequisite of I031 is now
formal Lean).** Five theorems in `SubgroupGaussSumOrbitReduction.lean`, all
`#print axioms == [propext, Classical.choice, Quot.sound]`, no `sorryAx`. They prove
`ζ•G = G` for `ζ∈G`, orbit-invariance `η_{ζb}=η_b`, coset-constancy, and the period-count
bound `|{distinct η_b}| ≤ |T|` for any coset cover `T` (→ `≤ (p-1)/n + 1` for a transversal).
This is the metric-entropy index reduction `log p → log m`, formalized.

**The sup-comparison HELD with a bounded constant — but that constant is NOT a chaining gain,
and the residual leaked exactly onto the BGK/Lamzouri wall.** The covariance and chaining
metric of the matched Gaussian are pinned exactly and axiom-clean
(`I031MatchedGaussianCovariance.lean`, six theorems). But the quotient metric is **flat**
(`d(b,b') ≈ √(2n)` for almost every pair), so Dudley/Talagrand chaining **collapses to the
union bound** over the `m` orbits — chaining buys nothing beyond the index reduction the
orbit-brick already gave. The whole comparison therefore reduces to ONE inequality: a
per-period sub-Gaussian tail with proxy `O(n)` at depth `r≈log m`. That is the BGK short-
character-sum wall, restated. Empirically bounded (`M/E sup|G| ∈ [1.26,1.42]`,
`sig_eff²/n ∈ [0.57,0.92]`, no creep to `n=512`) but **knife-edge**: the accessible 16× range
cannot distinguish a true bounded constant (= handle, exponent 1/2) from an extremely slow
`loglog n` creep (= BGK `n^{o(1)}` wall).

**NET: I031 is now a SHARPER, PARTIALLY-FORMALIZED handle, but the open lemma leaked back to
BGK.** The geometry is closed (and Lean-clean): there is no multi-scale chaining shortcut. The
entire residual is the single per-period sub-Gaussian-tail inequality — identical to the
Lamzouri value-distribution CLT extended from length `p^{o(1)}` to a fixed power `p^{1/8}`.
The honesty is: I031 sharpened the *statement* of the open problem to one clean inequality and
discharged its deterministic half axiom-clean, but did NOT produce a new technique to beat the
BGK wall on the analytic half.

## (a) Orbit-reduction brick — LANDED, axiom-clean, a real (deterministic) handle

File: `ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumOrbitReduction.lean`
(commit `1f343e5a0`). Built on `SubgroupGaussSumDilationRecursion` (`dilate`, `eta_dilate`,
`card_dilate`) and `SubgroupGaussSumSecondMoment` (`eta`). Uses a Finset multiplicative-closure
hypothesis `MulClosed G := ∀ a∈G, ∀ b∈G, a*b∈G` (Finset form of a finite multiplicative
subgroup / `n`-th roots of unity).

Five theorems, **all five `#print axioms == [propext, Classical.choice, Quot.sound]`**
(re-verified 2026-06-15 via `lake env lean` axiom audit; no `sorryAx`, no `native_decide`):

- `dilate_eq_self_of_mem` : `ζ•G = G` for `ζ∈G, ζ≠0` (subset from closure, equality from
  `card_dilate` + injectivity).
- `eta_orbit_invariant` : `η_{ζ·b}(G) = η_b(G)` for `ζ∈G` — ORBIT-INVARIANCE.
- `eta_const_on_coset` : the same, framed as constancy on the coset `b·G`.
- `eta_image_subset_of_cosetCover` / `card_distinct_eta_le` : QUOTIENT FACTORING — for any
  coset-covering `T`, `univ.image(η·) ⊆ T.image(η·)`, hence `|{distinct η_b}| ≤ |T|`. A
  transversal gives `≤ [F^*:G]+1 = (p-1)/n+1` distinct periods.

This is genuinely useful and genuinely new in-tree: it is the formal `log p → log m` index
reduction. It is the *deterministic prerequisite* of I031; it is NOT the open lemma.

## (b) Deterministic→matched-Gaussian sup comparison — HELD with bounded C, but is the union bound, and the residual = the BGK wall

File: `ArkLib/Data/CodingTheory/ProximityGap/I031MatchedGaussianCovariance.lean`
(commit `add859591`). Six theorems, **all six axiom-clean** (re-verified 2026-06-15:
`pg-iterate` axiom audit reports `[propext, Classical.choice, Quot.sound]` for all; real
`lake build` previously passed, 3312 jobs, `autoImplicit=false`).

**Step (i) — covariance PINNED EXACTLY (Lean).** Matched Gaussian `G_b = Σ_x g_x ψ(bx)` has
`Cov(b,b') = E[G_b conj G_{b'}] = Σ_{x∈μ_n} ψ((b−b')x) = η_{b−b'}` — the covariance IS the
period at the difference frequency (a subgroup correlation). Variance `Cov(b,b)=η_0=n`; chaining
metric `d(b,b')² = 2n − 2Re η_{b−b'}`. Lean: `matchedCov`, `matchedSqMetric`, `matchedCov_diag`,
`matchedSqMetric_{diag,symm}`, `matchedCov_conj_symm`, `matchedSqMetric_nonneg_le` (`0≤d²≤4n`),
`matchedCov_l2_average` (`Σ_c‖η_c‖² = p·n`, from the second-moment substrate). No Weil.

**Step (ii) — the quotient chaining metric is FLAT.** Probe
`probe_i031_metric_flatness_vs_collapse.py`: `d_med ≈ √(2n)` exactly (n=4..64); fraction of
pairs within ½·diam: `0.163 → 0.077 → 0.012 → 0.000 → 0.000`. No multi-scale geometry ⟹
Dudley/Talagrand **collapses to the union bound** over the `m=p/n` orbit reps. The
"collapse `log p → log m`" is the index-count reduction (= the orbit brick), NOT a chaining
gain. Independently reconfirms the Salem-Zygmund self-refutation
(`deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`).

**Step (iii) — the comparison HOLDS with a bounded constant.** Probes
`probe_i031_det_vs_random_transfer` / `probe_i031_deeptail_anomaly`: deterministic `M` vs
matched-Gaussian `E sup|G_b|` (orbit reps) gives `M/E sup|G| ∈ [1.26,1.39]` across n=4..128,
NO growth. (Floor-audit probe, fixed seed, n=16..128, β=2.1..2.4: ratio `∈ [1.255,1.423]`,
`M/√(n log m) ∈ [1.265,1.472]` — consistent.) So the deterministic worst case is tracked by
the matched-Gaussian sup within a bounded factor — the favorable direction of LEMMA (b).

**Step (iv) — the OPEN content = the per-period sub-Gaussian tail at depth (the BGK wall).**
Flat metric ⟹ comparison reduces to ONE inequality: `Re(ζ̄ η_c)` sub-Gaussian with proxy
`O(n)` uniformly at the deep tail. Read off `sig_eff² := M²/(2 log m)`:
`sig_eff²/n ∈ [0.57,0.92]` (n=8..512, non-monotone, saturating). Denoised 3-primes regression
n=8..128: `⟨sig_eff²/n⟩` flat at 0.68–0.73; fits — constant c=0.676 (SSE .0110),
`a + b·loglog n` b=+0.131 (SSE .0033, best), `a + b·log n` b=+0.038 (SSE .0041). Extrapolation
to prize `n=2^30`: loglog-model → 0.92, log-model → 1.33 (both bounded). β-sweep (thinning,
BGK-harder regime): `sig_eff²/n` DECREASES `0.70→0.59` as β:3.0→5.0, no thin-subgroup inflation.

**HONEST KNIFE-EDGE:** over the accessible 16× range the data cannot distinguish a bounded
constant (= handle, exponent 1/2) from an extremely slow `loglog n` creep (= BGK `n^{o(1)}`
wall). The comparison is structurally closed; the entire residual is this single per-period
sub-Gaussian-tail inequality, identical to the BGK/Lamzouri short-character-sum wall, with
chaining adding nothing the union bound did not.

## (c) I099 cumulant ladder — bounded, FAVORABLE, supports the handle (probe-only)

Probes (axiom-N/A, Python, proper `μ_n` only; commits `ca8ee8de4` original + `4b522fc92`
adversarial verify): `probe_i099_deep_cumulant_ladder`, `_samplingnoise_control`,
`_floor_implication`, plus the verify suite. VERDICT: standardized cumulants ARE bounded to the
needed depth; NO inflation at `r ≈ β+1`. The value distribution is sub-Gaussian-leaning.

1. `kappa_4` is the only genuine arithmetic deviation and equals **`-3n` EXACTLY**,
   n-uniformly (`-48.05/-96.06/-192.15` for n=16/32/64; re-verified 2026-06-15 by
   `probe_i099_verify_kappa4_arithmetic`, ratio 8x vs the iid-phase model `-3n/8` ⟹ genuinely
   arithmetic, not noise). Standardized `kappa_4/σ^4 = -3/n → 0`. NEGATIVE = lighter-than-
   Gaussian tails = the FAVORABLE (sub-Gaussian) direction, NOT heavy-tailed arithmetic excess.
2. Deep cumulants r=6,8,10,12 (including critical depth `r≈β+1`): EVERY one lands inside the
   iid-arcsine sampling-noise band (`|z|<1.7`). Raw small-prime blow-ups (k10=77, k12=-1131)
   are pure finite-sample estimator variance; they shrink as `m` grows (49k→28M). The
   forced-anomaly that kills the DEAD even-moment route does NOT appear in the standardized
   value-distribution (tail-shape) cumulants — the key distinction, confirmed.
3. Floor implication: `M = max_b|η_b|` stays strictly BELOW `√(2n log(p/n))`; ratio
   `∈ [0.73,0.92]`, no upward creep as β grows (at fixed n it drifts DOWN) — the favorable
   direction of LEMMA (b).

HONESTY: reproducible-probe numerical evidence, NOT a proof of LEMMA (b). Establishes only that
the MARGINAL tail shape is sub-Gaussian-leaning with bounded, favorable, n-uniform cumulants; it
does NOT establish the sub-Gaussian-INCREMENT/comparison principle the chaining argument needs.
The `kappa_4 = -3n` closed form is a sharp new quantitative fact (next: derive it from a
quotient fourth-moment identity, the axiom-clean analogue of `subgroup_gaussSum_secondMoment`).

## (c′) I015 multivariate Stepanov — NO-GAIN, fell

Probe `probe_i015_multivar_dyadic_stepanov.py` (commit `43475be29`). The multivariate
dyadic-digit Stepanov construction collapses to a single rational curve `y_{i+1}=y_i²`;
exponent pinned at 1.000 — the same single-orbit wall as I001/I006/I008. Not a handle. The
Stepanov family on `μ_n` is now exhausted across univariate and multivariate; do NOT re-attempt
any Stepanov/multiplicity-on-`μ_n` construction.

## The exact remaining open content (one line)

> Prove a bounded-constant deterministic→matched-Gaussian sup comparison for the cyclotomic
> quotient process `{η_b : b ∈ F_p^*/μ_n}`. With the flat metric this is exactly: the per-period
> real marginal `Re(ζ̄ η_c)` is sub-Gaussian with proxy `O(n)` uniformly at depth `r ≈ log m`.
> Equivalently: extend Lamzouri's value-distribution CLT for subgroup periods from length
> `p^{o(1)}` to a fixed power `p^{1/8}` with sub-Gaussian proxy `O(n)`. No chaining shortcut
> exists; attack that CLT extension directly, not the geometry.

## Concrete next moves

1. Lean-formalize the union-bound consumer "flat metric + per-index sub-Gaussian proxy
   `σ²=Cn` ⟹ `M ≤ √(2Cn log m)`" as a named-conditional bridge (the SG-MGF Prop), wiring
   `matchedSqMetric` / `matchedCov_l2_average` in. This lands the whole comparison axiom-clean
   modulo ONE cited sub-Gaussian-tail hypothesis — the project's modularity convention.
2. Push the `sig_eff²/n` proxy-creep regression to n=512–1024 with full-`m` (needs a faster
   max kernel / numba) to sharpen the constant-vs-`loglog`-creep call — the single decisive
   empirical question.
3. Derive `kappa_4 = -3n` from a quotient fourth-moment identity (axiom-clean Lean brick
   extending the second-moment substrate), pinning the leading non-Gaussian correction.

## Files

- `ArkLib/Data/CodingTheory/ProximityGap/SubgroupGaussSumOrbitReduction.lean` (commit `1f343e5a0`)
- `ArkLib/Data/CodingTheory/ProximityGap/I031MatchedGaussianCovariance.lean` (commit `add859591`)
- `scripts/probes/probe_i031_{metric_flatness_vs_collapse,deeptail_anomaly,det_vs_random_transfer,proxy_creep_regression,quotient_floor_audit}.py`
- `scripts/probes/probe_i099_{deep_cumulant_ladder,samplingnoise_control,floor_implication,verify_kappa4_arithmetic}.py`
- `scripts/probes/probe_i015_multivar_dyadic_stepanov.py`
- `docs/kb/deltastar-i031-gaussian-sup-comparison-2026-06-15.md`,
  `docs/kb/deltastar-444-i031-quotient-floor-audit-2026-06-15.md`
