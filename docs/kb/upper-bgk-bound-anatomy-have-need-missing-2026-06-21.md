# The Upper BGK Bound: What We Have, What We Need, What We're Missing (#444)

*A precise anatomy of the upper bound `M ≤ C√(n log m)` at β=4 (`n=2^a`, `p≈n^4`, `m=(p−1)/n`,
`M=max_{b≠0}|η_b|`, `η_b=Σ_{x∈μ_n}e_p(bx)`). Every "proven" below is machine-checked axiom-clean
in-tree this campaign. Written 2026-06-21 as the upper-bound reference; the running mechanism census
will refine the exponent table.*

---

## 1. The exponent ladder (where we sit)

| bound | value at β=4 | status | why |
|---|---|---|---|
| trivial | `M ≤ n` | proven | triangle ineq, `n` terms |
| Parseval floor (lower) | `M ≥ √n` | proven | max ≥ RMS, `Σ_{b≠0}|η_b|²=qn−n²` |
| **prize target** | `M ≤ C√(n log m) = n^{1/2+o(1)}` | **OPEN** | the upper BGK/Paley bound |
| Weil / Deligne | `M ≤ (m−1)√p ≈ n^{5/4}` | proven but **vacuous** | `μ_n` is 0-dimensional ⟹ main term = the count |
| di Benedetto–Solymosi–White | power saving for `2<β<4`; at β=4 gives `n^{73/72} > n` | proven, **vanishes at the endpoint** | saving `δ(β)` is affine, hits 0 as β→4⁻ |
| **BGK (sum-product)** | `M ≤ n^{1−o(1)}` | **proven (SOTA)** | Bourgain–Glibichuk–Konyagin; the only nontrivial bound at β≥4 |

The gap is **`n^{1−o(1)} → n^{1/2+o(1)}`** — a full half-power. BGK is a *working* bound (a theorem),
and the task is to drive its `o(1)` down to `1/2`.

## 2. What we HAVE (proven, axiom-clean)

**(H1) The moment method is sufficient and sharp.** `M^{2r} ≤ Σ_{b≠0}|η_b|^{2r} = q·E_r − n^{2r} =: A_r`
(Parseval spine, exact). Optimizing `M ≤ A_r^{1/2r}` at the saddle `r* ≈ ⌈log p⌉` gives the prize *iff*
`E_r ≤ K^r(2r−1)‼·n^r`:
> `_ProveSingleDepthWickSaddle`: a single-depth Wick bound at `q ≤ e^{k+1}` yields `M ≤ √e·√((k+1)n)`.

So the upper bound is **not** missing a method — it is missing one **energy input**.

**(H2) The char-0 (no-wraparound) Wick bound is proven.** `E_r^{char0} ≤ (2r−1)‼·n^r`
(Lam–Leung antipodal balance / Bessel `I_0(2s)≤e^{s²}`; `_AvW0_BesselWickDomination`). Exact low
moments: `E_2 = 3n²−3n`, kurtosis 3 (Gaussian-like).

**(H3) The split and the onset.** `E_r = E_r^{char0} + W_r`, where `W_r` is the **wraparound** count
(genuine `F_p` collisions `Σx_i ≡ Σy_j (mod p)` that are nonzero in `ℂ`). `W_r = 0` below the onset
`(2r)^{n/2} < p` (`_OnsetNoWraparoundGeneral`) — but at β=4 this is vacuous for `r ≥ 2`, so wraparound
is *present and dominant* exactly in the regime the prize needs (`r ~ log p ≫ 4`).

**(H4) The DC-subtracted variance identity.** `A_r = q·Var(freq)` exactly (`_ProveFreqVarianceIdentity`),
and `W_r` has DC mean `n^{2r}/p`. So `A_r = q·E_r^{char0} + q·(W_r − mean)`.

**(H5) Five machine-checked equivalent forms of the missing input** (so we can attack any face):
1. **Wick energy:** `E_r ≤ K^r(2r−1)‼·n^r` at `r≈log p`.
2. **Wraparound Variance Law:** `Var(W_r) = O(Wick)` to depth `log p`.
3. **Twisted-DFT:** `max_k|Σ_{j<m} g_j ζ^{jk}| ≤ C√(m log m)`, `g_j=`Gauss sums, `|g_j|=√q`.
4. **Jacobi autocorrelation:** the off-diagonal `A(s)=Σ_j g_j\overline{g_{j+s}}` is sub-Gaussian.
5. **Subgroup character sum (sharpest, magnitude-free):** `|T(s)| ≤ C√n` for the `n`-term incomplete
   multiplicative character sum `T(s)=Σ_{t∈μ_n}χ^s(t−1)`.

**(H6) The Jacobi machinery to manipulate it.** `|J(χ,φ)|=√q` (`norm_jacobiSum_eq_sqrt`, *not* in
Mathlib), the Gauss-sum recurrence, the self-similar descent `A(s) → T(s)`, `m·η_b=Σ_j χ^j(b)^{−1}g_j`.

**(H7) Two-axis irreducibility (what does NOT work).** Proven: no *reduction* escapes — the analytic
faces P/B/D/V/L are Parseval-dual (transfers relocate), the off-cluster protocol faces are
Johnson-gated. So the upper bound needs a **direct** analytic estimate, not a reduction.

## 3. What we NEED (the single input, stated five equivalent ways — §2 H5)

Any one of the five suffices. The most concrete is **(H5.5)**: an effective, uniform-in-`s`,
square-root-cancellation bound for the `n`-term incomplete multiplicative character sum over the thin
subgroup, `|Σ_{t∈μ_n}χ^s(t−1)| ≤ C√n`. This is the BGK/Paley/Burgess statement localized to an
`n`-term object.

## 4. What we're MISSING (the precise obstruction — why each known tool stops)

The needed estimate must have **four properties simultaneously**, and no known technique supplies all
four at β=4:

1. **Effective** (explicit constant, not `o(1)`). — BGK's exponent has an ineffective `o(1)`; it does
   *not* sharpen to `1/2`.
2. **Uniform in the frequency `b`/`s`** (worst-case, not average). — Parseval/large sieve give the
   *average* (`√n` RMS) for free; the large sieve is phase-blind, pinned to the Weil scale `√q` for
   the worst case (the pincer).
3. **At the working depth `r ≈ log p`** (non-perturbative in `r`). — Sum-product controls `E_r` for
   *small* `r` (`r=2,3` give `n^{1−δ}` with `δ` fixed-small); the exponent does **not** improve to the
   Wick floor as `r` grows. Burgess's `2r`-th-moment saving infimum is exactly `1` at β=4.
4. **Archimedean / phase-aware** (sees the cancellation in the Gauss-sum *phases*, not just
   magnitude). — Weil over-bounds at `√p` (vacuous, `μ_n` 0-dim); the **no-go trilogy** proves the
   size of `W_r` cannot be certified by any algebraic-invariant / LP-Delsarte / congruence-parity
   certificate (p-adic data sees valuations, not archimedean modulus).

**In one sentence:** we can prove the char-0 Wick bound and the moment method *conditionally on it*,
but we cannot control the **char-p wraparound energy `W_r` at depth `log p`**, and that control is
exactly an effective, uniform, archimedean √-cancellation estimate for the thin subgroup `μ_n` — the
open Burgess barrier at β=4, supplied by no technique (sum-product stalls at `n^{1−o(1)}`, Weil is
vacuous, di Benedetto vanishes at the endpoint).

## 5. The most promising routes to the missing input (ranked)

1. **Sum-product energy at growing depth** (the BGK engine, the running census's focus): `μ_n` is a
   *perfect* multiplicative group (`E_×=n³` maximal), so sum-product *forces* additive energy small;
   the open question is whether the best exponent (Rudnev/Shkredov) drives `E_r` to the Wick floor at
   `r~log p` rather than stalling. **This is the most direct shot** and is exactly "BGK is the floor."
2. **The subgroup character sum `T(s)`** (H5.5): a Weil/Stepanov bound *specific to the order-`n`
   subgroup* — but the naive Weil degree `m≈n³` makes it vacuous; need a subgroup-adapted argument.
3. **Effective Katz–Jacobi equidistribution** of the bounded-conductor horizontal family
   `j↦J(χ^j,χ^{−(j+s)})` (`_JacKatzBoundedConductorFamily` — conductor *is* bounded, the genuine
   opening) pushed to the extra `√(log m)` reach on the thin slice.
4. **Phase-aware / cyclotomic-sensitive** new machinery satisfying all four §4 properties — the
   genuinely-new tool the no-go's say is *required* (does not yet exist).

## 6. Honest bottom line

The upper bound is one inequality short: **`E_r ≤ Wick` at `r ≈ log p`**, i.e. control of the
wraparound energy `W_r` at logarithmic depth. Everything upstream (the reduction, the moment method,
the char-0 bound, the equivalences, the Jacobi machinery) is proven; everything that *reduces* is
proven not to escape (two-axis). The missing input is a single effective-uniform-archimedean-deep
√-cancellation estimate for the thin subgroup — the Burgess barrier at β=4 — and the live, most-direct
route is the sum-product energy engine ("BGK is the floor"), whose best exponent versus the Wick floor
is precisely what the running census is measuring. No QED is faked; the gap is named exactly.
