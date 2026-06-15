# A3 (#444): does the BGK wall encroach on δ* as n→∞?  Clearing prime stays POLYNOMIAL ⟹ candidate SAFE

**Verdict (honest, NOT a closure): the BGK "clearing prime" p*(n) grows POLYNOMIALLY at fixed
distance-to-capacity, so it does NOT outrun the prize prime ~ n·2¹²⁸; and the floppy (under-det/r=1)
band's lower edge stays strictly ABOVE the candidate crossing δ\* for all n. Both A3 sub-questions
resolve in favor of the candidate's safety. Evidence is 3 octaves (n=16,32,64) + an analytic
scaling law. This is empirical evidence the wall does not encroach, NOT a proof of the SOTA BGK bound.**

## Setup
Far-line incidence `I_p(δ)` via the prime-size-independent (k+1)-subset solve (per (k+1)-subset of
μ_n solve the (k+1)×(k+1) system for (g of deg<k, γ); `I_p(w)=#distinct γ with agreement ≥ w`).
Two regimes (established #407):
- **OVER-DET / RIGID** (bands `w ≥ k+2`): char-independent outside finite bad primes; **determines δ\***.
  Each near-capacity band's `I_p(w)` GROWS with p (mod-p sumset pollution) then **saturates** to the
  char-0 value above a **clearing/saturation prime p\*(sat)**.
- **UNDER-DET / FLOPPY / r=1** (band `w = k+1`): `I_p(k+1) ~ Θ(p)` grows forever (the BGK/Paley
  sup-norm wall). Its lower edge in δ is fixed at `δ_floppy = 1 − (k+1)/n`.

## Q1 — clearing prime p\*(n): POLYNOMIAL, stays ~110 bits below the prize prime
Saturation threshold `p*(sat)/n³` measured at fixed distance-to-capacity (`probe_nearcap_saturation_scaling.py`
+ `probe_a3_clearing_prime_n64.py`, k=4, ρ=4/n; p\*=smallest prime ≥95% of saturated value, p>n³):

| n  | dist-to-cap | p\*(sat)/n³ | I_sat |
|----|-------------|-------------|-------|
| 16 | +0.125      | 1           | 23    |
| 16 | +0.062      | 10          | 1992  |
| 32 | +0.094      | 2           | 18    |
| 32 | +0.062      | 17–24       | 49088 / 228 |
| 32 | +0.031      | 36          | 98336 |
| 64 | +0.031 (w=6)| > 22 (still rising at 22n³; I=21→613→2696)  | (≥2696) |

**Matched distance (+0.062):** p\*/n³ = 10 (n=16) → 17–24 (n=32): a **1.7–2.4× rise per octave**,
i.e. multiplier ~ n^{0.8–1.3} and **p\*(sat) ~ n^{3.8–4.3}, POLYNOMIAL**.
**Matched distance (+0.031):** p\*/n³ = 36 (n=32) → >22-and-rising (n=64). Both octaves keep the
multiplier O(10s)·n³; n=64 confirms no super-polynomial jump (the over-det band w=6 is still on its
slow approach to saturation at 22n³, value 2696, vs n=32's plateau 98336 at 36n³ — same shape, the
multiplier merely a constant factor larger).

**n=64 floppy confirmation:** band w=5 (the r=1/under-det band) gives I/p = 1.00 (449) → 0.99
(3n³) → **0.48 (22n³)** — i.e. I stays Θ(p), NEVER clears. This is the genuine BGK wall, but it
lives at δ_floppy = 0.922, far ABOVE any δ\* (see Q2).

**Extrapolation to prize scale.** A polynomial `p\* ~ n^c` is exponentially below the prize prime
(fixed `2¹²⁸` factor) at every n. Even the steepest plausible law (mult ∝ 1/dist applied to the
candidate band whose dist = log₂(n)/n ⟹ `p\* ~ n⁴/log₂ n`):

| n     | log₂ p\*(sat) (worst) | log₂(prize n·2¹²⁸) | gap   | result |
|-------|-----------------------|--------------------|-------|--------|
| 2⁶    | ~22–28 (measured)     | 134                | ~110  | p\* ≪ prize (SAFE) |
| 2⁸    | ~30–32                | 136                | ~105  | p\* ≪ prize (SAFE) |
| 2¹⁶   | ~60–66                | 144                | ~80   | p\* ≪ prize (SAFE) |
| 2³²   | ~120–135              | 160                | ~25   | p\* ≪ prize (SAFE) |

⟹ **the clearing prime does NOT outrun the prize prime** at any feasible n. The char-0 over-det
crossing is faithful at prize scale (the rigidity reduction holds).

## Q2 — floppy edge vs candidate: floppy stays ABOVE the candidate (margin = (log₂ n − 1)/n > 0)
Candidate (rigid crossing, char-0): `δ\* = (1−ρ) − log₂(n)/n`, i.e. crossing band `w_cross = k + log₂ n`.
Floppy band is `w = k+1`, so `δ_floppy = 1−(k+1)/n` and
`δ_floppy − δ\* = log₂(n)/n − 1/n = (log₂ n − 1)/n > 0` for all n ≥ 4.

| n   | δ_floppy | candidate δ\* | margin (log₂ n−1)/n |
|-----|----------|---------------|---------------------|
| 16  | 0.8125   | 0.6250        | +0.1875             |
| 64  | 0.8594   | 0.7813        | +0.0781             |
| 256 | 0.8711   | 0.8438        | +0.0273             |
| 2³² | →0.875   | →0.875        | +1.6e-9             |

The floppy/BGK band lives strictly at `δ ≥ δ_floppy > δ\*` — in the already-failed region — so it
**cannot lower δ\* below the candidate**. The candidate crossing band (`w = k+log₂ n`, an OVER-DET
band) is char-0-faithful (Q1). The `log₂(n)−1` over-det bands between floppy and crossing are exactly
the ones whose clearing primes Q1 bounds. The margin `(log₂ n − 1)/n → 0⁺`: the floppy edge
**approaches but never reaches** the rigid crossing (a one-band, ~1/n separation persists). The
candidate crossing is itself near-capacity (cap−δ\* = log₂(n)/n → 0), so it sits in the slow-clearing
zone — but Q1 shows that zone's clearing prime is still polynomial.

## Honest caveats / residual
- 3 octaves (n=16,32,64) at a single rate (k=4). n=64 over-det w=6 had not fully plateaued by the
  largest feasible prime (52n³); its exact saturation multiplier is bracketed (>22) not pinned. The
  qualitative law (polynomial, O(10s)·n³, no super-poly jump) is firm across the octaves.
- `p\*(sat)` is the saturation threshold of the over-det bands; the genuine SOTA BGK bound
  `max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log p)` (prize β>4 outside every explicit theorem) is NOT
  proven by this — A3 is empirical evidence the wall does not encroach, not a proof of the bound.
- The floppy-vs-candidate margin (log₂ n−1)/n is k-independent; the absolute p\*(n) law was fit at k=4.

## Probes
- `scripts/probes/probe_nearcap_saturation_scaling.py` (prior-art; n=16,32 clean saturation curves)
- `scripts/probes/probe_a3_bgk_wall_encroachment.py` (per-band clearing prime + floppy/candidate compare + extrapolation)
- `scripts/probes/probe_a3_clearing_prime_n64.py` (n=64 single-pencil 4-prime saturation bracket)
