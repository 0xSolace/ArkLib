# Direct measurement of the prize wall M(n), and an exact Rust δ* engine (2026-06-15)

Two fast standalone Rust tools (`scripts/probes/rust/`, `rustc -O <f>.rs -o <f>`), built to
unblock the compute-walled CPython probes and to **independently re-verify** the campaign's
wall characterization.

## 1. `mn_wall.rs` — the prize object directly
`M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|` over coset reps, stratified by `v₂(p−1)`, at `β=log_n p ≈ 4`
(the prize regime `p ≈ n⁴`). Measured (float64 periods; coset-constant so range b over the `m=(p−1)/n` cosets):

| n | v₂(p−1) | p | M | M/√n | C = M/√(n·ln(p/n)) |
|---|---|---|---|---|---|
| 16 | 4 | 200017 | 13.79 | 3.45 | 1.122 |
| 16 | 11 | 202753 | 11.81 | 2.95 | 0.960 |
| 32 | 8 | 1049857 | 23.20 | 4.10 | 1.272 |
| 64 | 7 | 16777601 | 33.92 | 4.24 | 1.200 |
| 64 | **8** | **16778497** | **42.02** | **5.25** | **1.487** ← Fermat-rich spike (matches wf-LA R=1.465) |
| 128 | 7 | 268438913 | 58.98 | 5.21 | 1.366 |

**Finding (independent confirmation, NOT a new result):** `C` is **bounded ≈ 0.96–1.49** across n=16–128
(worst case the Fermat-rich high-`v₂` prime), with `M/√n ≈ C·√(ln(p/n))` — i.e. `M(n) ≈ C√(n log(p/n))`
with `C=O(1)` **empirically true** in range. The open prize is *proving* `C=O(1)` for all n (the 25-year
BGK/Paley wall), not establishing its truth. `v₂(p−1)` does NOT linearly predict `C` (highest AND lowest C
both at high `v₂`), independently corroborating wf-IWA (no clean 2-adic interpolation law).

## 2. `deltastar_farline.rs` — exact far-line δ* (the Johnson-side incidence object)
Faithful Rust port of `probe_farline_incidence_exact.incidence`; `δ* = (largest r with max-far-incidence ≤ n)/n`.
Validated EXACT vs the in-tree reference and RB's engine: **n=16,k=4 → δ*=9/16=0.5625, bad r=10, binder x⁴, incidence 89** (triple-confirmed); n=8 → 3/8. Confirms the over-determined far-line stratum is Johnson-locked (`δ*=½+1/n`), far below the window-interior floor — the BGK-decoupling lead is dead from this side too.

Both tools are ~100–1000× the CPython probes and reach n=128 (M) / exact n≤24 (δ*) in seconds–minutes on 8 cores;
n≥256 (M) and exact n≥32 (δ*) remain compute-walled on CPU (GPU port is the next step if deeper points are wanted).
