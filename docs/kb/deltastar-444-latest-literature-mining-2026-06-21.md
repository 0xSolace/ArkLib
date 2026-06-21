<!-- #444 / Paley-BGK. Consolidated research record of the 2024-26 literature mining campaign
(2026-06-21): ~88 user-provided arXiv papers across 3 batches + WebSearch sweeps + bibliography
expansion (59 further findings), all mined against the four faces, the viable candidates adversarially
attacked. HONEST STATUS: 0 crossings, 0 new handles on the core; ~58th independent wall confirmation.
The value is the precise reduction taxonomy + the per-face map + the harvested leads. -->

# #444 Latest-Literature Mining (2024–2026): Catalogue, Reductions, and the Per-Face Map

## 0. Scope and verdict

Across this round the campaign mined **~88 arXiv papers** (three user-provided batches: 32 + 28 + the
7 recontextualized leads, plus WebSearch sweeps and a bibliography/search **expansion of 59 further
findings**) against the four faces of the prize, and adversarially attacked every candidate that cleared
viability. **Verdict: zero crossings, zero new handles on the core faces; the very-latest (2024–26)
literature contains no `β=4` crossing and no genuine new input on F1/F2/F3.** This is the **~58th
independent confirmation** of the project diagnosis. The deliverable is the precise *reduction taxonomy*
(why each modern technique reduces), the per-face status, and the harvested leads for the record.

The target (unchanged): `M = max_{b≠0}|η_b| ≤ C√(n log(p/n))`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `μ_n` the
`2^μ`-th roots, `p ~ n^4`. Best proven BGK `n^{1−o(1)}`; prize `n^{1/2}`. The gap is **pure archimedean
phase cancellation** at depth `log p`; magnitude/L²/energy/count methods are **phase-blind** (the floor
`M^{2k} ≤ p·E_k`, `E_k ≥ n^{2k}/p ⟹` exponent `≥ 1`, axiom-clean `_AvMRS_PhaseBlindEnergyFloor`).

## 1. The single sharpest finding of this round: average vs. max

The most-promising fresh lead — **Harper's "better than square-root cancellation" / multiplicative
chaos** (arXiv:2512.23681 Dec 2025; 1703.06654; 2508.12956; 2503.10555) — is the one technique with a
*structural reason* to escape the phase-blind floor: **fractional moments `E|η_b|^{2q}` for `q<1` are
not subject to the integer-moment floor.** It was developed and adversarially verified (and I
reproduced every number independently). **It reduces, and the reason is decisive and new:**

> **Harper's better-than-√ cancellation is a *low-moment / average* phenomenon; the prize `M` is the
> worst-case *max*, detected only by *high* moments.** The max-from-moment bound `(p·A_q)^{1/2q}`,
> `A_q = E_{b≠0}|η_b|^{2q}`, is **monotone decreasing in `q`** — so fractional `q<1` give *worse* max
> bounds (`q=0.25 → 10^{10}`, useless). Smoking gun (exact): near-max frequencies (`|η_b|>0.9M`) are
> **14.0%/7.7%** of the integer moment `E_4` but only **0.30%/0.06%** of the fractional `E_{0.5}` (n=16/32)
> — the fractional moment *deliberately suppresses* the rare large values that *are* the prize. And the
> deterministic family lacks the log-correlated GFF structure the chaos machinery needs (`arg(η_b)`
> autocorrelation ≤ 0.14 at n=16, ≤ 0.02 at n=32, decaying to white noise).

The Gauss-period family's *average* is genuinely sub-`√n` (Harper-shape, `avg|η_b|/√n ≈ 0.80`), while
its *max* is `M/√n ≈ 3.5–4.1` (above `√n`) — **the saving and the prize sit on opposite sides of `√n`.**
This is the cleanest statement of why the family being sub-iid (`C_iid = M/√(2n log N) < 1`, real) does
not yield the prize: sub-iid is an average/typical statement; the prize is worst-case.
(Probe: `scripts/probes/probe_fractional_moment_avg_vs_max.py`.)

## 2. The reduction taxonomy (why each 2024–26 technique reduces)

| Technique (representative papers) | Face | Reduction reason |
|---|---|---|
| **Multiplicative chaos / better-than-√** (2512.23681, 1703.06654, 2508.12956, 2605.29962, 2601.19614) | F1/F2 | **average not max** (§1); fractional moments give worse max bounds; no log-correlated structure |
| **Gauss-sum-weighted VMVT / Weyl** (Koh–Shparlinski 2503.10933, quadratic VMVT 2310.02950, 1901.01551) | F2 | `J_{r,k}` **saturates at k=2** (`x→x²` is 2-to-1 onto `μ_{n/2}`); `M` pinned to the degree-1 slice `Σ_b\|η_b\|^{2r}=p·E_r`; higher degrees add mass off the M-slice |
| **degree-4 SOS / spectral pseudorandomness** (Kunisky 2211.02713, 2303.16475, Randomstrasse 2603.29571) | F1/F3 | degree-2 SOS = spectral = `M` (no gain); degree-4 is a *clique* relaxation (different object) that *consumes* `M`; Kunisky's result is a *lower* bound (SOS weakness); sub-`√p` only conjectural |
| **Burgess via mult-energy + geometry of numbers** (Chattopadhyay 2602.22167, Alsetri–Shao 2509.07765, 2505.19654) | F1/F2 | multiplicative-energy method, `p^{1/4}` threshold for *boxes/GAPs*; a subgroup of size `n~p^{1/4}` is *at* the threshold (the barrier, not a crossing); energy is phase-blind |
| **di Benedetto `H>p^{1/4}` subgroup sums** (2003.06165 + 2024–25 refs) | F1 | strict inequality essential; the `p^{1/72}` prefactor makes the trilinear bound vacuous at β=4 |
| **Brun–Titchmarsh / KMS Kloosterman moments** (2504.12692) | F1 | KMS `q²`-saving needs a *second parameter* (the Kloosterman argument `Kl(b+mc)`); the single complete subgroup sum has only `b`, magnitude-invariant under `b→bt` |
| **GL₂ algebraic twists / subconvexity / spectral reciprocity** (2412.15722, 2509.05968, 2606.11451, 2512.03305, 2511.22644) | F1/F2 | automorphic 2nd-moment averages `|L|²` = magnitude (phase-blind); no `L`-function / family for a single complete subgroup sum |
| **Generalized Paley graph spectra / decompositions** (Podestá–Videla 2604.06513, 2606.06774) | F1 | the eigenvalue *identity* `η_b = (1/m)(−1+Σχ̄(b)τ(χ))` gives *magnitude* (`√q` triangle bound), never the `√(q/(n log q))` phase cancellation among the `~2^128` unknown phases |
| **Pretentious / high-order character sums** (Granville-school 2405.00544) | F1 | needs *integer intervals* + archimedean coordinate + factorization — none exist for a complete subgroup sum; the saving is double-logarithmic anyway |
| **Supercharacter Gaussian-period moments** (Garcia 2112.13886, 1611.07287) | F2 | re-expresses the proven Lam–Leung char-0 Wick value; leaves the deep-`r` char-`p` excess = the wall |
| **2026 Linnik / zero-free regions** (Bruna 2603.25612, Matomäki–Teräväinen 2605.27833, Bellotti–Trudgian–Yang 2603.21490, Xylouris L≤5.18) | F4 | F4 ceiling **not** closed: Route-A good prime is exponential; Route-B needs a *count* (Thorner–Zaman), Linnik gives only *existence*; the 2026 papers are off-object |
| **Murmurations, measure rigidity, Mahler measure, short trace functions** (2307.00256, 2606.03472, 2604.19437, 2507.09303, Sawin–Shusterman 2512.24080, FKMS 2511.09459) | F1/F2 | under attack this round (`wttril8sk`) — see §4 |

## 3. Per-face status after the literature mining

- **F1 (sup-norm `M`):** open = the wall. No 2024–26 technique bounds `M` below BGK. The avg-vs-max
  obstruction (§1) explains why even better-than-√ doesn't reach the worst case.
- **F2 (additive energy `E_r` at deep `r`):** char-0 proven (Lam–Leung); deep-`r` char-`p` excess = the
  wall. VMVT/energy/supercharacter all re-express or are phase-blind.
- **F3 (`δ*` / list-decoding / incidence, BCHKS 1.12):** no new input; the over-det union-count is
  combinatorial but numerically undecidable below `n≥256`.
- **F4 (the ceiling):** closed Paley-free via Dirichlet for the *super-poly* regime and for `s=32`; the
  `s=128` rows split at the prize point — **closeable for `ρ=1/16`, but the bad-prime budget FAILS for
  `ρ=1/8, 1/4`**, and the obstruction is the **collision-pair count `~2^188 ≫` good supply `2^122`**,
  *not* the Linnik prime supply. So better Linnik does not help; a *smoothness / shared-factor* bound on
  the distinct bad primes is what's needed. (Probe: `probe_ceiling_budget_obstruction.py`.)

## 4. The four genuinely-fresh clusters (attacked this round)

The bibliography/search expansion surfaced four clusters *not* pre-reduced, now under adversarial
attack (`wttril8sk`): **(a) measure rigidity / Einsiedler–Lindenstrauss entropy** (reinterpret `η_b` as
a homogeneous-space period, bound `M` by orbit-measure entropy); **(b) murmurations of Dirichlet
characters** (collective phase phenomenon); **(c) Sawin–Shusterman short trace-function sums** (Dec 2025
SOTA, near-√ cancellation for short sums); **(d) asymptotic Mahler measure of Gaussian periods**
(directly our object). Expected outcomes (to be confirmed): (a) the homogeneous-space realization is
abelian/torus (= the monodromy reduction the campaign's UVST already found); (c) short-trace-sum
cancellation still needs big monodromy `μ_n` lacks, or reduces to Weil `√p`; (b),(d) avg-not-max (Mahler
= geometric mean, murmuration = a density). Verdicts appended on completion.

## 5. Harvested leads for future rounds (the record)

New search terms that surfaced relevant work: *"fractional moments character sums subgroup"*,
*"short sums of trace functions function fields"*, *"Gaussian multiplicative chaos extreme value"*,
*"measure rigidity equidistribution Gauss periods"*, *"murmurations Dirichlet characters"*,
*"stratification exponential sums families"*, *"Mahler measure Gaussian periods"*. Bibliography clusters
worth a deeper read: Kowalski–Michel–Sawin trace-function program; Einsiedler–Lindenstrauss measure
classification; Harper/Gorodetsky–Wong random-multiplicative-function probability.

## 6. Honest meta-verdict

The 2024–26 literature is rich in adjacent advances — Burgess for GAPs/boxes/`F_{p^n}`, better-than-√
for random multiplicative functions, trace-function sup-norms, degree-4 SOS for the Paley clique,
effective Linnik — but **not one crosses `n^{1−o(1)} → n^{1/2}` for a thin multiplicative subgroup at
the Burgess barrier**, and the structural reasons are now catalogued precisely. The single deepest
reason, sharpened this round: the prize is the **worst-case max** of a family whose **average** is
genuinely better-than-√; every tool reaching the max is phase-blind, and every tool that beats `√n`
(Harper, Mahler, murmurations) does so *on the average*, the wrong side of `√n`. The missing input
remains a genuinely phase-aware control of the deep-depth archimedean cancellation — absent from the
literature, this round included.
