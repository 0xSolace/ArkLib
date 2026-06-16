# δ* — THE WALL, FOUND: complete map of why every route reduces to one object (#444)

**Date 2026-06-16. Status: the wall is found and characterized to its sharpest statement.** This is the
terminal map after an exhaustive grind across both grand challenges, all 8 in-tree open Props, the 41 new
bricks O199–O231, the archimedean assault, and the complete 2023–2026 literature. **No closure** — δ* is
pinned to its *form* but the single open constant is a recognized open problem. Every thread is accounted for.

## The wall, stated exactly

δ* (the MCA threshold for explicit smooth-domain RS) `= 1 − ρ − Θ(1/log n)`, equivalently the per-frequency
sup-norm
```
M(μ_n) = max_{b≠0} |η_b| ≤ C·√(n·log(q/n)),   η_b = Σ_{x∈μ_n} e_p(bx),
```
`μ_n` = the 2-power subgroup (`n=2^μ`) of `F_p^*`, `p≈n^4` (β=4), `q/n≈n^3`, prize `n~2^30`. The **whole open
problem is whether `C` is bounded** (= BGK/Paley graph conjecture for thin subgroups = BCHKS-1.12 = explicit-RS
list-decoding beyond Johnson; three-way equivalent, Ben-Sasson–Carmon ECCC TR25-169).

## Empirical δ* (what the data says — exact, n=8…128, β=4)
`M(n)/√(n log(q/n))` = 1.07, 1.20, 1.26, **1.36, 1.28** — oscillating ≈1.25 (the Wick value), the n=128
turn-down a mild signal **for** bounded `C`. Doubling ratio `M(2n)/M(n)` → √2. `M/√(2n ln q)` = 0.65→0.78
(below the moment bound throughout). Period distribution: variance exactly `n`, **light-tailed** (excess
kurtosis `κ₄/κ₂² = −3/n → 0`), `house/√(2n ln m) ∈ [0.76,0.96]`. **Mildly favorable to the prize being TRUE**,
but boundedness of `C` is unprovable by numerics (an `n^{−o(1)}`-slow divergence is indistinguishable at finite n).

## The 8 in-tree open Props are ALL this one wall
`BCHKS1_12`, `DepthLogSubGaussian`, `GaussianEnergyBound`, `MStarGrowthLaw`, `NearRamanujanSqrtLog`,
`PrizeFloorStatement`, `ResonanceConjecture`, `WickEnergyBound` — all proven (this campaign) to reduce to
`M(μ_n) ≤ C√(n log q)`. The `ResonanceConjecture` (`T_r=(1/m)Σ_k S_k^r`), the cumulant ladder (`= log I₀(2t)^{n/2}`),
the moments `E_r`, and the Bessel-MGF are **literally one char-0 object** in four costumes; the open core is
uniformly the char-p excess `W_r` (= `Spur_r`) at depth `r≈ln q`.

## Every route — closed, with the precise reason
| route | status | reason |
|---|---|---|
| moment / energy `E_r` | **provably blocked** | char-0 Lam–Leung bound `E_r≤(2r−1)‼n^r` is FALSE in char-p at depth `r_cross≈5 ≪ r_prize≈120`; method yields only the trivial `‖η‖≤n`. (Dvir PC/SoS-hard.) |
| flat spectrum | **house-blind** | `A_0=p−n, A_d=−n ∀d≠0` exact, `|η̂_k|²=p`; but flat-spectrum sequences range `house∈[√(2n ln m), √p]` — only the phases pin it |
| finite-prime invariants | **house-blind** | `disc(Ψ)=p^{m−1}f²` CFT-fixed; Newton polygon, SVP, defect all ramification-fixed (discnogo) |
| 2-power phase sub-tower | **no lever** | dual chars mostly odd-order; `corr(v₂(m),ratio)≈0`; more 2-power structure mildly *raises* house |
| chaining / extreme-value | **vacuous** | period process embeds in 1-D ℝ; Dudley gives only the range, no √log gain |
| dedup-strictness (A3) | **leans wall** | slack fraction `1−N_r/C(n,r) ~ (log n)²/2n → 0` |
| over-det far-line | **Johnson proxy** | full-direction `m*=n/4−1` linear, δ*→Johnson (not the true floor) |
| Gauss-phase randomness | **provably dependent** | Rojas-León 2207.12439: only conj+Galois+Hasse–Davenport relations; DOF `m→n/4` |
| list-decoding 2023–26 | **needs design freedom** | BGM/Guo–Zhang/AGL need random points; folded/multiplicity/subcodes change the code; capacity provably OUT for fixed domain (CS25 2025/2046); SOTA = Johnson |
| Salem–Zygmund | **needs randomness** | SZ upper bound open even for genuine randomness (Hardy 2401.16256); phases deterministic+dependent |

## What is PROVEN (axiom-clean, landed this campaign)
The entire **char-0 face**: energy closed form `E_r(ℂ)=(2r)![z^r]f^{n/2}`, subset-sum spectrum `N_r=ΣC(m,k)2^k`,
the **Bessel-MGF** `I₀(2y)^{n/2}≤e^{ny²/2}` (the char-0 sub-Gaussian/prize bound). Plus the favorable correction:
`Spur_3=0` at the *real* `2^128` prize prime for `n≲1024` (`maxprime(n)~exp(0.85(log₂n)²)` crosses `2^128` at
`n≈1024`).

## The single missing input (the wall)
> An **effective Gauss-period / Jacobi-phase equidistribution bound at a fixed prize prime** — uniform in `b`,
> growing `n`, at β=4 (`n ≤ q^{1/4}`), **thinness-essential** (false at β≈2.3–3.2 structured primes).
> Equivalently: the `m=(p−1)/n` Gauss-sum phases `{arg g(χ_j)}` satisfy `max_{β≠0}|Σ_j e(βj/m + arg g(χ_j))|=o(m)`
> with Salem–Zygmund saving. This does NOT exist in the literature; no technique reaches exponent `1/2` at β=4.

## Verdict
**The wall is found.** It is archimedean (every finite-prime/second-order/flat-spectrum/algebraic handle is
provably house-blind), it is the deep-`r` Gauss/Jacobi-phase equidistribution at the fixed prize prime, and it
is equivalent across all 8 in-tree Props and both grand challenges. The empirical δ* is the conjectured value
(`C≈1.25`, mildly favorable to the prize), the char-0 face is proven, and the boundedness of `C` is the genuine
open frontier — a recognized analytic-number-theory problem requiring a new theorem absent from the literature.
δ* is pinned to its form; its exact constant is the wall. No route I or the swarm can generate escapes it.
