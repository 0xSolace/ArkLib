# Working backward from the empirical bound — full result (#444, 2026-06-15)

User directive: assume the empirical prize bound `M(n) ~ √2·√(n ln m)` as a conjecture and hunt the
transformation that proves it. Ran a 6-angle backward-proof workflow + a 5-angle grind on the convergence
point, all adversarially audited for CIRCULARITY. **Honest verdict: every non-circular bridge converges on —
and reduces to — the same wall, now localized to its sharpest minimal form. No closure; genuine localization.**

## 1. Backward bridges (6 angles)
| Angle | non-circular? | closes? | outcome |
|---|---|---|---|
| 1 Dyadic bootstrap | YES | no | step factor → 2 (trivial), not √2 — see align_cos below |
| 2 Deterministic chaining (EVT-derand) | no | no | circular: needs the sub-Gaussian tail it's trying to prove |
| 3 Single-saddle MGF | YES | **partial** | the closest; the convergence target |
| 4 Algebraic rigidity (house bound) | no | no | M *is* the house; no proven height bound reaches √2√(n log m) |
| 5 Conservation/fixed-point | YES | no | **reduces to angle 3** (single-saddle MGF) |
| 6 Transfer-operator spectral radius | YES | no | **reduces to angle 3** |

**Convergence:** the four non-circular bridges (1,3,5,6) all funnel to ONE inequality — the single-saddle MGF
`Σ_{b≠0} cosh(η_b y*) ≤ q²` at `y*=√(2 ln q/n)`, which gives `M ≤ √2·√(n ln q)`.

**Why the dyadic bootstrap (angle 1) can't close — a clean structural fact.** Doubling
`η_b(μ_{2n})=η_b(μ_n)+η_{ζb}(μ_n)`. Measured at the worst `b*`: `align_cos = 1.000` exactly across n=8,16,32
(the two halves add *perfectly coherently*, forced by reality `−1∈μ_n`). So the step factor `M(2n)/M(n)` is
pushed toward 2 (telescopes to trivial `n`), not the √2 the prize needs. The bootstrap is non-circular but
structurally cannot give factor √2.

## 2. Grind on the single-saddle MGF (5 angles) — all reduce to the wall
| Angle | outcome |
|---|---|
| A Moment problem (low moments cap MGF?) | **NO** — see depth analysis below: bulk needs depth R~ln q |
| B Gaussian majorization / concentration | reduces-to-wall: η_b deterministic (not random) so Hoeffding inapplicable; an O(1)-proxy sub-Gaussian period IS BGK |
| C Saddle/Legendre | circular + reduces to per-r Wick |
| D Reality/coherence lever | reduces to per-r Wick |
| E Depth truncation + proven tail | reduces to per-r Wick (DC/trivial tail too weak) |

**Angle A closed by direct computation (the sharpest result).** Fraction of `Σcosh(η_b y*)` captured by
depth R, vs `R/r*` (r*=ln q = saddle depth):

| R/r* | 0.18 | 0.45 | 0.96 | 1.5 |
|---|---|---|---|---|
| captured (n=64) | 0.0002 | 0.03 | **0.88** | 1.0 |

The bulk arrives ONLY at `R ~ r* = ln q ≈ 89`. Low (provable) moments capture <5%. So the deep moments at
`r~log q` are load-bearing — the moment-problem escape fails. This is a sharp quantitative restatement of the
meta-theorem *at the saddle*: no finite/low-moment method controls the saddle MGF.

## 3. The robust reframing (the genuine keepable insight)
The sharp `S=Σcosh(η_b y*) ≤ q²` is VIOLATED at structured primes (n=64, v₂=8: S=2.57·q²). BUT the violation is
*cheap*: since `M ≤ (log S)/y*`, a constant-factor violation of `S≤q²` inflates C only through a **log**
(S=2.57q² → C≈1.48, still O(1)). So the genuine sufficient target is the far weaker
> **`S ≤ q^{O(1)}`  ⟺  `log_q S` bounded  ⟺  `C=O(1)`  ⟺  the Gauss period μ_n is sub-Gaussian with some O(1)
> variance proxy** (`Σ_{b≠0} exp(η_b²/(cn)) ≤ q^{O(1)}`).

Empirically `log_q S → 2` (since the max term alone gives `√2·C·ln q` and C→√2). This is the **weakest-sufficient
form of the prize** — qualitative BGK (any constant), not the sharp √2. It is the cleanest statement of exactly
what must be proven, and it is still the wall: an O(1)-proxy sub-Gaussian tail for the thin 2-power subgroup
period is precisely the BGK/Paley statement, open at the Burgess barrier.

## 4. Bottom line
Working backward does reveal the bridge — and the bridge is *one* well-posed inequality (the single-saddle MGF
in its robust `q^{O(1)}` form). But proving that inequality from PROVEN facts requires controlling the deep
moment at depth `r~log q` (shown: the bulk lives exactly there), which is the BGK wall. Every non-circular
backward route lands on it. The arc's value is the sharpest localization to date: the prize ⟺ an O(1)-proxy
sub-Gaussian tail for the period, controlled by moments at depth exactly `r*=ln q` — no shallower. Refutations
and localization, not closure. The wall is the unattained sharp endpoint of Bourgain's BGK program.
