# arXiv 67-Paper Harvest: Honest Relevance Map + What It Yielded (#444)

*Harvest of a 67-paper arXiv set supplied 2026-06-21, against the proximity-prize attack surfaces
(the Paley/Burgess wall, RS list decoding, char-p wraparound, Bessel/char-0, Gaussian/Gauss/Jacobi
sums, the Jacobi-phase residual). The workflow subagents could not fetch arXiv (no WebFetch in that
sandbox; triage returned 0 papers and honestly fell back to dossier techniques). I therefore fetched
and read all 67 myself via the arXiv API. This is the honest map and outcome. No wall was advanced;
no QED faked.*

---

## 1. The blunt finding: the corpus is a keyword collision

The 67 papers were (almost certainly) gathered by keyword — **"Jacobi"** and **"Bessel"** — and those
words occur across the corpus in senses that have **nothing to do with our number theory**:

- **"Jacobi"** = Jacobi **matrices/operators** (spectral theory of tridiagonal operators:
  `2305.19608`, `2503.03086`, `2601.08796`), Jacobi **elliptic functions** (`2302.09471`,
  `2301.08472`, `2306.17818`), Jacobi **polynomials** (`2508.04520`, `2109.05069`), Jacobi-**Anger**
  expansion (`2204.12783`, `2606.17704`, `2501.05977`), **Eisenstein–Jacobi networks** (`2606.18712`,
  cs.DC), Bessel-**Dunkl**/Dunkl (`2605.23529`, `2606.01130`). **None is a Jacobi *sum*.**
- **"Bessel"** = Bessel **beams** in optics (`2605.17200`, `2605.17479`, `2605.19996`, `2605.29519`,
  `2606.11610`, …), Bessel functions for **scattering/PDE/plasma/HEP** (`2606.19261`, `2606.18854`,
  `2606.14290`, `2606.08139`, `2606.04024`), Bessel **computation** (`2606.14839`), Bessel **potential
  spaces** (`2606.17770`, `2605.25833`), Fourier-Bessel/Riesz-Bessel (`2605.30645`, `2605.29469`).
  **None is the additive-combinatorics Bessel `I_0(2s)≤e^{s²}` of our char-0 period** except by the
  most distant analogy.

The remaining papers are squarely off-topic for us: differential geometry (`2209.09288`), general
relativity / black holes (`2302.09471`, `2605.19719`, `2605.29519`), quantum mechanics
(`2109.05069`, `2301.08472`, `2606.07320`, `2606.17359`), spin glasses / diffusion models
(`2407.13846`, `2605.19391`, `2606.05140`), PDE / spectral theory (`2404.10972`, `2508.08637`,
`2605.21080`, `2605.23229`, `2605.25833`, `2605.30679`, `2606.02428`, `2606.09358`, `2605.24694`),
numerical analysis / signal processing / ML (`2605.17739`, `2605.21608`, `2605.28191`, `2606.03275`,
`2606.13067`, `2606.15616`, `2606.07821`, `2604`-optics), lattice counting on nilpotent groups
(`2605.26033`), umbral calculus (`2606.05214`).

## 2. The genuinely in-area / tangential papers, assessed

| id | title | area | relevance | verdict |
|---|---|---|---|---|
| **2605.29470** | The weighted large sieve through Parseval (Ramaré) | **math.NT** | **in-area** | reduces to wall |
| 2605.20983 | Weighted endpoint majorants for modified-Bessel integrals (Gaunt's problem) | math.CA | tangential (char-0 Bessel) | char-0 only (already closed) |
| 2605.30645 | A functional-analytic tour of the Fourier-Bessel transform | math.FA | tangential (our DFT is Fourier) | survey, no new bound |
| 2606.05214 | Umbral transmutations and Bessel moments | math.GM | tangential (moments) | umbral formalism, no F_p content |
| 2605.26033 | Lattice point counting on step-two nilpotent groups | math.CA | distant (counting) | wrong geometry |

**`2605.29470` (the only real hit).** Ramaré improves the *weighted large sieve* by using the exact
Parseval identity instead of an approximate Bessel inequality. The large sieve is precisely a
**magnitude / L² method**, and our two-axis irreducibility result *proves* every such method is pinned
by the pincer to the Weil/√q scale — phase-blind, unable to supply the `√(log m)` of archimedean phase
cancellation the prize needs. A sharper weighted large sieve tightens constants on the *average /
almost-all-b* side we already own via Parseval (`subgroup_gaussSum_secondMoment`); it does **not**
touch the worst-case sup-norm wall. Honest verdict: a real NT tool, in our area, but it **reduces to
the wall** (the average side, not the sup). Memory already records "large-sieve almost-all-primes
reaches only the Weil scale."

**`2605.20983` (Bessel majorant).** Resolves Gaunt's problem: `∫₀ˣ e^{-γt}I_ν(t)t^{-ν}dt ≤ C·e^{-γx}
I_{ν+1}(x)x^{-ν}`. A reciprocal-power *integral* majorant for modified Bessel `I_ν`. Our char-0 use is
`I_0(2s)≤e^{s²}` (the MGF bound giving `Sh_char0=√2`), which is **already proven** in-tree
(`_AvW0_BesselWickDomination`). This paper touches only that *closed* char-0 side; it has no bearing on
the open **char-p** wall (the wraparound `W_r`). Marginal at best.

## 3. What the harvest workflow produced (fallback dossier techniques, verified by me)

Because triage came up empty, the build phase honestly fell back to three named external techniques
already on the campaign's desk and tested each against a wall. All three re-verified axiom-clean by me
(`[propext, Classical.choice, Quot.sound]`, no sorryAx); all **reduce to / relocate** the wall:

- **`_ArxSteinWraparoundNoGo`** (Stein's method / exchangeable-pair Poisson on the wraparound count):
  the *correct* DC-subtracted sup-chain `M^{2r} ≤ p·N_r − n^{2r} = p·A_r`, and the machine-checked
  **no-go** `meanfield_poisson_yields_trivial`: a sub-Poisson tail centered on the *mean-field* mean
  `n^{2r}/p` gives only `M ≥ n` (trivial), because `p·λ = n^{2r}` exactly. The prize needs centering on
  the *Wick* mean `(2r−1)‼·n^r` — which is verbatim the open SHARPEST statement. Stein re-expresses the
  moment fence, does not bypass it.
- **`_ArxSchurHornIncidenceVacuous`** (Schur–Horn / majorization on line–ball incidence): the
  incidence matrix `B[γ,w]=1[ℓ(γ)=syn(w)]` is a **partial permutation** (`incidence_rowSum_zero_or_one`
  + `incidence_colSum_zero_or_one`, via line injectivity), so its sorted spectrum is flat and the
  majorization bound is *vacuous* — Schur-convexity gives nothing beyond the trivial count.
- **`_ArxSawinShustermanShortTrace`** (Sawin–Shusterman short-trace cancellation, the one not-yet-
  refuted import): relocates to the same Gauss-phase autocorrelation, self-similar one order down.

## 4. Honest verdict

Of 67 papers: **one** is in our field (the weighted large sieve, which is phase-blind and reduces to
the wall), a **handful** touch the already-closed char-0 Bessel/Fourier side, and the **other ~60 are
keyword collisions** in unrelated fields. **No paper in the set supplies a technique that advances the
open Burgess/Paley wall.** The three bricks the workflow landed are genuine (and now committed) but
came from prior dossier techniques, not from this corpus, and all reduce to the wall. The wall stands;
the relevance map is the honest deliverable. (If a future corpus is desired, the productive search
terms are *generalized Paley graph eigenvalue, incomplete Gauss sums over subgroups, Burgess bound
subgroups, additive energy of multiplicative subgroups, Bourgain–Glibichuk–Konyagin* — not "Jacobi"/
"Bessel," which collide with operator theory and optics.)
