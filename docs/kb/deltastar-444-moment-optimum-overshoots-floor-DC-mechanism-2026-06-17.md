# δ* (#444): the optimized moment method overshoots the floor at β=4 — and the floor itself is numerically TRUE

**Date:** 2026-06-17. **Probe:** `scripts/probes/probe_moment_optimum_vs_floor.py` (exact integer
`E_r`; high-precision `M(n)` with Parseval certificate). **Status:** route-elimination (sharpened) +
a positive sub-fact (floor validated). Companion to
`deltastar-444-ktransfer-bounded-K-DEAD-exact-2026-06-17.md`.

## Question

The bounded-K finding showed `E_r^{(p)} ≤ Kʳ·Wick` fails (K grows). But that alone does not kill the
**optimized** moment bound `M ≤ M_bound* := min_r (q·E_r)^{1/(2r)}` — maybe the optimal depth `r*` sits
below the anomaly onset and the bound still lands at the floor `F(n)=√(2n·ln m)`, `m=(p−1)/n`. This
probe settles it.

## Data (β=4, `p` = smallest prime ≡1 mod n with `p ≥ n⁴`; EXACT to n=64)

| n | p | m | r* | M_bound\* | true M(n) | F(n)=√(2n ln m) | Mb\*/F | M/F | M/√n |
|---|---|---|----|-----------|-----------|------|--------|-----|------|
| 16 | 65537 | 4096 | 18 | 16.04 | 13.84 | 16.32 | 0.98 | 0.85 | 3.46 |
| 32 | 1048609 | 32769 | 16 | 32.00 | 22.98 | 25.80 | **1.24** | 0.89 | 4.06 |
| 64 | 16777601 | 262150 | 14 | 64.00 | 38.53 | 39.96 | **1.60** | 0.96 | 4.82 |

## Verdict — the optimized moment method is dead at β=4 (mechanism identified)

- **`r*` is the deepest computed depth** — `M_bound(r)` is monotone-decreasing in `r`, so the optimum
  sits AT/ABOVE the R>1 anomaly onset (n=32 onset r≈9; n=64 onset r≈6), never below it.
- **`M_bound*/F` grows with n** (0.98 → 1.24 → 1.60; per-octave ≈1.27): the optimum overshoots the
  floor and the overshoot compounds with scale.
- **Mechanism (load-bearing):** `Σ_b |η_b|^{2r} = q·E_r` always contains the DC term
  `η_0^{2r} = n^{2r}`, so `(q·E_r)^{1/(2r)} ≥ n` for **every** `r`. The optimized moment bound is
  structurally **floored at `n`**, whereas the true `M(n)` and the target `F(n)` both scale like
  `√(n·log m) ≪ n`. Hence `M_bound*/F ≥ n/F = √(n/log m) → ∞` (computed √(n/log m) = 1.39, 1.75, 2.26 —
  tracks `Mb*/F`). Even the **DC-subtracted** variant `(q·E_r − n^{2r})^{1/(2r)}` still grows
  (0.92 → 1.01 → 1.13): the residual overshoot is exactly the `R(r)>1` anomaly excess in the off-axis
  term. So removing DC does not rescue it.

**Bottom line:** at β=4 the optimized moment method yields `M ≲ n`, NOT `M ≲ √(n log m)`. Any
energy/moment route is structurally floored at `n` by the DC mass — it provably cannot see the floor.
This is a stronger, mechanistic form of the bounded-K death: it eliminates the *entire* even-moment
family, not just the uniform-constant version.

## Positive sub-fact: the floor itself is numerically TRUE

The **true** sup-norm satisfies `M(n)/F(n) = 0.85, 0.89, 0.96 < 1` across n=16,32,64, and `M(n)/√n`
grows only mildly (3.46 → 4.06 → 4.82 — the genuine `√log` excess, Ramanujan exponent ½ up to √log
slack). So `M(n) ≤ C√(n·log m)` holds at β=4 to n=64 with a bounded constant — the prize floor is
**correct**; what is missing is a *proof technique* that captures the phase cancellation the moment
method discards (= the BGK wall).

## Reproduce
```
python3 scripts/probes/probe_moment_optimum_vs_floor.py
```
(~40s; `ALLOW_N128=1` attempts n=128, needs ~2 GB. M(n) is float64 with a Parseval rel-err certificate
1.5e−5/9.5e−7/6.0e−8 at n=16/32/64 — high-precision, not arbitrary-precision; exact data reaches n=64.)
