# δ* (#444): the bounded-K / DC-Wick moment route is DEAD at β=4 — exact-arithmetic refutation

**Date:** 2026-06-17. **Probe:** `scripts/probes/probe_ktransfer_deeptail_decisive.py`
(exact integer arithmetic; reproducible). **Status:** route-elimination (negative), honest.

## What was claimed before (now corrected)

A prior reading held the char-`p` → char-`0` energy transfer to be a **clean positive
target**: with `E_r^{(p)}(μ_n) ≤ K^r · Wick_r`, `Wick_r := (2r−1)‼·n^r`, the anomaly ratio
`R(r) := (E_r^{(p)}/Wick_r)^{1/r}` and `K_eff := sup_r R(r)` were measured **flat ≈ 0.62–0.66
across n=32..512 with NO growth**, suggesting `K` is bounded and the prize floor would follow
from a bounded-`K` theorem via the moment method (`M^{2r} ≤ q·E_r`, optimize at `r≈ln q`).
That measurement only reached `r ≤ 5`, `n ≤ 512`, and used a float-FFT with rounding.

## What the exact computation shows

Re-done with **exact integer arithmetic** (int cyclic-convolution mod `p` of the `μ_n`
indicator, big-int accumulation of `Σ_v N(v)²`; validated against the closed forms
`E_2 = 3n(n−1)`, `E_3 = 15n³−45n²+40n`, and the char-0 lattice baseline). At `β=4`
(smallest prime `p ≡ 1 (mod n)` with `p ≥ n⁴`; cross-checked over **4 distinct such primes**
per `n`, so the effect is generic, not a single-bad-prime artifact):

| | n=16 | n=32 | n=64 |
|---|---|---|---|
| depth reached (exact) | r=18 | r=16 | r=14 |
| `R(r)` crosses 1 at | never (≤18) | r ≈ 9 | r ≈ 6 |
| `K_eff` over computed `r` | 1.000 | 1.127 | 1.848 |
| `R` at deepest `r` | R(18)=0.643 | R(16)=1.127 | R(14)=1.848 |

Two independent growth axes:
- **At fixed `n`,** `R(r)` is non-monotone but turns upward and **crosses 1**.
- **At fixed depth `r ≥ 2`,** `R(r)` **increases monotonically with `n`** (fixed-depth
  cross-cut `R(64)/R(16)`: `1.025` at r=2 → `2.41` at r=12 → `2.63` at r=14).
- **The onset depth of `R>1` shrinks as `n` grows** (n=16: clean to r≥18; n=32: ~r=9;
  n=64: ~r=6). The earlier "flat K≈0.6, no growth" reading was a **pre-onset artifact** of
  staying at `r ≤ 5`, `n ≤ 512` — the char-`p` anomaly switches on just past those depths.

β-sensitivity confirms `β=4` is the live regime: `β=3` shows the same (worse) growth onset;
`β=5` stays healthy (`R<1`, decreasing). I.e. the picture only flips to "alive" by pushing
`p` much larger relative to `n` than the prize (`β≈4`) allows.

## Verdict and scope

**The DC-Wick / moment route with a uniform bounded constant `K` cannot prove the prize floor
at `β=4` to depth `r≈89`.** The char-`p` additive energy exceeds the Gaussian/Wick baseline
beyond an onset depth that shrinks with `n`, so `E_r ≤ K^r·Wick_r` with bounded `K` fails
uniformly in the prize regime. This **eliminates the moment method as a route to the floor**.

**This does NOT disprove the prize floor itself.** `M(n) ≤ C√(n·log m)` may still hold — it
would then have to come from the actual BGK/Paley short-character-sum cancellation, NOT from a
moment/energy bound. So this finding is fully consistent with the terminal picture
(`prize δ* = the open BGK wall`): it removes one of the last "positive target" hopes and shows
why — the energy is genuinely super-Gaussian at the relevant depths.

**Honest caveat:** exact data reaches `n=64`. The `n=2^30` conclusion is an extrapolation of a
clear, monotone, multi-prime trend (onset depth shrinking with `n`; fixed-depth `R` rising with
`n`), explicitly flagged as extrapolation in the probe — not a direct measurement.

## Reproduce

```
python3 scripts/probes/probe_ktransfer_deeptail_decisive.py
```
(~80s; ~270 MB RAM for the β=5/n=32 case. `ALLOW_N128=1` attempts n=128, needs ~2 GB.)
