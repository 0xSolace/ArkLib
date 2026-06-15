# A3 (#444): does the BGK wall encroach on δ* as n→∞?  Clearing prime stays POLYNOMIAL ⟹ candidate SAFE

**Verdict (honest, NOT a closure): the BGK "clearing prime" p*(n) grows POLYNOMIALLY at fixed
distance-to-capacity, so it does NOT outrun the prize prime ~ n·2¹²⁸; and the floppy (under-det/r=1)
band's lower edge stays strictly ABOVE the candidate crossing δ\* for all n. Both A3 sub-questions
resolve in favor of the candidate's safety. Evidence is 2 clean octaves (n=16,32) + an analytic
scaling law; n=64 is a confirming point (computationally heavy, C(64,5)=7.62M solves/prime).**

## Setup
Far-line incidence `I_p(δ)` via the prime-size-independent (k+1)-subset solve (per (k+1)-subset of
μ_n solve the (k+1)×(k+1) system for (g of deg<k, γ); `I_p(w)=#distinct γ with agreement ≥ w`).
Two regimes (established #407):
- **OVER-DET / RIGID** (bands `w ≥ k+2`): char-independent outside finite bad primes; **determines δ\***.
  Each near-capacity band's `I_p(w)` GROWS with p (mod-p sumset pollution) then **saturates** to the
  char-0 value above a **clearing/saturation prime p\*(sat)**.
- **UNDER-DET / FLOPPY / r=1** (band `w = k+1`): `I_p(k+1) ~ Θ(p)` grows forever (the BGK/Paley
  sup-norm wall). Its lower edge in δ is fixed at `δ_floppy = 1 − (k+1)/n`.

## Q1 — clearing prime p\*(n): POLYNOMIAL, stays below the prize prime
Saturation threshold `p*(sat)/n³` measured at fixed distance-to-capacity (`probe_nearcap_saturation_scaling.py`,
k=4, ρ=4/n; band w near capacity; p\*=smallest prime ≥95% of saturated value, restricted to p>n³):

| n  | dist-to-cap | p\*(sat)/n³ | I_sat |
|----|-------------|-------------|-------|
| 16 | +0.125      | 1           | 23    |
| 16 | +0.062      | 10          | 1992  |
| 32 | +0.094      | 2           | 18    |
| 32 | +0.062      | 17–24       | 49088 / 228 |
| 32 | +0.031      | 36          | 98336 |

**Matched distance (+0.062):** p\*/n³ = 10 (n=16) → 17–24 (n=32) — a **1.7–2.4× rise per octave**,
i.e. the multiplier ~ n^{0.8–1.3} and **p\*(sat) ~ n^{3.8–4.3}, POLYNOMIAL**. Closer to capacity the
multiplier rises (~1/dist): at dist +0.031 it is 36.

**Extrapolation to prize scale** (worst-pencil fit `log₂ p\* ≈ 4.26·log₂ n − 1.7`, and the steeper
`mult ~ c/dist` law applied to the candidate band's shrinking distance `dist = log₂(n)/n` ⟹
`p\* ~ n⁴/log₂ n`):

| n     | log₂ p\*(sat) | log₂(prize n·2¹²⁸) | result |
|-------|---------------|--------------------|--------|
| 2⁸    | ~30–32        | 136                | p\* ≪ prize (SAFE) |
| 2¹⁶   | ~60–66        | 144                | p\* ≪ prize (SAFE) |
| 2³²   | ~120–135      | 160                | p\* ≪ prize (SAFE) |

A polynomial `p\* ~ n^c` is exponentially below the prize prime (which carries a fixed `2¹²⁸`
factor) at every n. **The clearing prime does NOT outrun the prize prime.** Even the steepest
plausible law (mult ∝ 1/dist applied to the candidate band, dist = log₂ n/n) gives `p\* ~ 2¹²²` at
n=2³², still 25+ bits under the prize `2¹⁶⁰`. ⟹ the char-0 over-det crossing is **faithful at prize
scale**; the rigidity reduction holds.

## Q2 — floppy edge vs candidate: floppy stays ABOVE the candidate (margin = (log₂ n − 1)/n > 0)
Candidate (rigid crossing, char-0): `δ\* = (1−ρ) − log₂(n)/n`, i.e. crossing band `w_cross = k + log₂ n`.
Floppy band is `w = k+1`, so `δ_floppy = 1−(k+1)/n` and
`δ_floppy − δ\* = log₂(n)/n − 1/n = (log₂ n − 1)/n > 0` for all n ≥ 4.

The floppy/BGK band lives strictly at `δ ≥ δ_floppy > δ\*` — in the already-failed region — so it
**cannot lower δ\* below the candidate**. The candidate crossing band (`w = k+log₂ n`, an OVER-DET
band) is char-0-faithful (Q1). The `log₂(n)−1` over-det bands between floppy and crossing are exactly
the ones whose clearing primes Q1 bounds. The margin `(log₂ n − 1)/n → 0⁺` as n→∞: the floppy edge
**approaches but never reaches** the rigid crossing (a one-band, ~1/n separation persists).

## Honest caveats / residual
- Only 2 clean octaves (n=16, 32) drive the p\*(n) fit; n=64 (C(64,5)=7.62M solves/prime) is a heavy
  confirming point. The growth could in principle accelerate beyond polynomial at n>32 — the n=64
  multiplier is the decisive datum to rule that out.
- `p\*(sat)` is the saturation threshold of the over-det bands; the genuine SOTA BGK bound
  `max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log p)` (prize β>4 outside every explicit theorem) is NOT
  proven by this — A3 is empirical evidence that the wall does not encroach, not a proof of the bound.
- ρ=4/n (k=4) for the saturation sweep vs the candidate's ρ=1/8; the floppy-vs-candidate margin is
  k-independent ((log₂ n−1)/n) but the absolute p\*(n) law was fit at k=4.

## Probes
- `scripts/probes/probe_nearcap_saturation_scaling.py` (prior-art, n=16,32 the clean data here)
- `scripts/probes/probe_a3_bgk_wall_encroachment.py` (per-band clearing prime + floppy/candidate compare + extrapolation)
- `scripts/probes/probe_a3_clearing_prime_n64.py` (feasible n=64 single-pencil 4-prime saturation bracket)
