# The Proximity Prize, reduced to one estimate — an open problem for analytic number theorists

*Expert-facing statement (#444), 2026-06-21. This is a **problem statement, not a solution.** It records the exact analytic inequality the $1M Ethereum Proximity Prize reduces to (proven, machine-checked, multi-face), states it in the four equivalent forms a specialist would recognize, delimits precisely what is known and what is missing, and gives the computational evidence. Everything here is either proven in-tree (Lean, axiom-clean) or exact `F_p` computation; the central inequality itself is open. No claim of a proof is made.*

---

## 1. The object

Let `p` be prime, `n = 2^a \mid p-1`, and `μ_n ⊂ F_p^×` the subgroup of `n`-th roots of unity. Write `e_p(t)=e^{2πit/p}` and define the **Gauss period**
$$\eta_b \;=\; \sum_{x\in μ_n} e_p(bx)\qquad(b\in F_p),\qquad M(n,p)\;=\;\max_{b\neq 0}\,|\eta_b|.$$
`η_b` is constant on cosets `bμ_n`, so it takes `m=(p-1)/n` distinct values off `b=0`. The non-principal eigenvalue of the generalized Paley (Cayley) graph `Cay(F_p, μ_n)` is exactly `M(n,p)` (Liu–Zhou).

**Prize regime.** `n=2^a→∞`, `p≡1 \bmod n`, `p\asymp n^4` (the Burgess threshold `β=4`, `n\asymp p^{1/4}`), `m\asymp n^3`.

## 2. The open inequality

> **Conjecture (the wall).** There is an absolute constant `C` with
> $$M(n,p)\;\le\;C\,\sqrt{n\,\log m}\qquad\text{for all }n=2^a,\ p\equiv1\ (\mathrm{mod}\ n),\ p\asymp n^4.$$
> Computationally `C=\sqrt2` is the apparent sharp value (§5). This is the **Paley Graph Conjecture for the thin dyadic subgroup at the Burgess barrier**.

**Why it is *the* prize.** The Ethereum Proximity Prize asks to pin the smooth-RS mutual-correlated-agreement threshold `δ*` strictly inside the window `(1-\sqrt\rho,\,1-\rho)` at `ε^*=2^{-128}`. We have proven (Lean, axiom-clean, multiple independent bridges — `deltaStar_definitive`, `_FinalDichotomyCapstone`) that **`δ*` reaches the window interior iff the wall holds**. So the prize is *equivalent* to the inequality above. It is not "related to" the wall; it *is* the wall.

## 3. Four equivalent analytic forms (pick your weapon)

Forms (A)-(C) are proven equivalent in-tree; (D) is the exact orthogonal-polynomial restatement (`M=` top of the Jacobi matrix of `μ_η`), verified to machine precision; each is the breaking point of a standard method.

**(A) Wick moment bound at logarithmic depth.** Let `E_r=\#\{(x,y)\in μ_n^{2r}:\sum x_i=\sum y_j\ \text{in}\ F_p\}` be the additive energy. Then `M^{2r}\le \sum_{b\neq0}|\eta_b|^{2r}=p\,E_r-n^{2r}`, and optimizing at `r=\lceil\log p\rceil` shows
$$\big(E_r\le K^r(2r-1)!!\,n^r\ \text{to depth}\ r\approx\log p\big)\ \Longrightarrow\ M\le\sqrt{Ke}\,\sqrt{n\log p}.$$
The char-0 (no-wraparound) part `E_r^\infty\le(2r-1)!!\,n^r` is **proven** (cosine-independence/Bessel for `2^a`-th roots; `_AvW0_BesselWickDomination`). The open part is the **wraparound** `W_r=E_r-E_r^\infty` for `r>4`.

**(B) Square-root cancellation of the Gauss-sum-phase DFT.** With `ω` a generator of `\widehat{F_p^\times}`, the order-`m` subgroup `H=\{ω^{jn}\}` annihilates `μ_n`, and
$$\eta_b=\tfrac{n}{p-1}\Big(-1+\sqrt p\,\sum_{j=1}^{m-1} e\!\big(\tfrac{-j\,\mathrm{ind}(b)}{m}\big)\,u_j\Big),\qquad u_j=\frac{G(ω^{jn})}{\sqrt p}\ \ (|u_j|=1).$$
So `M=\tfrac{\sqrt p}{m}\max_{k\bmod m}|\widehat u(k)|`, and the wall is **`\max_k|\widehat u(k)|\le C\sqrt{m\log m}`** — uniform-in-`k` square-root cancellation of the `m`-point DFT of the unit Gauss-sum phases. This is *effective, finite, worst-case-uniform* vertical Sato–Tate. (Katz gives the qualitative/distributional equidistribution; the effective uniform sup at growing order is open.)

**(C) The Wraparound Variance Law.** Forms (A)+(B) collapse to a single second-moment statement: the wraparound count `W_r` has DC mean `\mathbb E[W_r]=n^{2r}/p\,(1+o(1))=n^{2r-4}` (which for `r>4` *exceeds* the Wick term and is removed by DC-subtraction, `_DCEnergyCorrection`), and
$$\textbf{Wall}\iff W_r-\mathbb E[W_r]=O^r\big((2r-1)!!\,n^r\big)\ \text{uniformly to depth}\ r\approx\log p,$$
i.e. an *arithmetic central limit theorem*: the coincidences `\sum_i\zeta^{a_i}\equiv\sum_j\zeta^{b_j}\bmod\mathfrak p` among short (`\le 2\log q`-term) sums of `2^a`-th roots of unity concentrate at their mean with square-root fluctuations.

**(D) Early turnover of the orthogonal-polynomial recurrence (Jacobi-matrix form).** Let `μ_η=\frac1{p-1}\sum_{b\neq0}\delta_{\eta_b}` be the empirical spectral measure of the (real) periods, and let `(a_k,b_k)` be the three-term recurrence coefficients of its orthonormal polynomials — the entries of the tridiagonal Jacobi matrix `J`. Then `M` is **exactly** the top of the spectrum of `J` (no `L^{2r}` overshoot — this closes the moment→sup conversion that costs the half-power in form (A)). The `b_k` follow the **Hermite law `b_k^2=n\,k`** (the recurrence of the Gaussian/Wick measure `N(0,n)`) up to a *turnover depth* `k^\*`, then fall; and `M=2\max_k b_k=\sqrt{2n\,k^\*}\,(1+o(1))`. Hence
$$\textbf{Wall}\iff k^\*=O(\log p),$$
i.e. the recurrence coefficients **deviate from the Hermite law `b_k^2=nk` by depth `k\approx\log p`** — *early*, long before the trivial support cutoff `b_k\le n/2` (which would only force turnover at `k=n/4\gg\log p`). Equivalently: the orthogonal polynomials of the period measure are Hermite to degree `\approx\log p`. This is the wall as a statement about a Jacobi matrix / a discrete integrable (Toda) system — the half-power is the *earliness* of the Hermite-to-cutoff transition. (The recurrence coefficients are a *sharper, bounded* invariant than the moments `E_r`: they stay `O(\sqrt{n\log p})` while `E_r` explodes, and they *discriminate* the bad primes that `E_r`'s bulk averages out.)

## 4. What is known, and the precise gap

| bound | regime | reaches `M\le C\sqrt{n\log m}`? |
|---|---|---|
| trivial | all | `M\le n` (no) |
| Weil (complete monomial sum `\sum e_p(bx^m)`, `m\asymp p^{3/4}`) | all | `(m-1)\sqrt p\asymp p^{5/4}` — **vacuous** |
| di Benedetto–Solymosi–White, Bourgain–Garaev (sum-product) | `n>p^{1/4}` | power saving that **vanishes exactly at `β=4`** |
| **BGK (Bourgain–Glibichuk–Konyagin)** | `n>p^{ε}` | `M\le n^{1-o(1)}` — **best known**, but `o(1)` ineffective; off the target by a full half-power |

The gap is the **entire half-power** of cancellation, at the single hardest point `n=p^{1/4}`. No 2024–2026 technique closes it (verified literature sweep, 2026-06-18 and 2026-06-21; SOTA unchanged).

## 5. Structural constraints any proof must respect (proven)

- **Magnitude methods cannot suffice.** Every functional blind to the phases `\arg u_j` — moments, Schatten/trace norms, Weil eigenvalue bounds — is pinned to `\sqrt p` (incoherent) or `\ge n` (Johnson), both missing `\sqrt n` (`moment_ladder_exceeds_prize`, `_AmplifiedLargeSieveSaturates`, the pincer). The cancellation lives in the phases.
- **The proof must be archimedean.** A no-go trilogy (Lean, axiom-clean) shows the energy excess `W_r` size cannot be certified by any algebraic-invariant, LP/Delsarte, or congruence/parity certificate. p-adic/Stickelberger data sees valuations, not the complex modulus.
- **No structural handle exists.** The phase sequence `(u_j)` is statistically indistinguishable from random conjugate-symmetric phases at the DFT level (`KS\to0`: `0.014,0.008,0.002` at `n=16,32,64`); the worst-case sup sits at the 14th–62nd percentile of the random ensemble. So a phase-aware method cannot exploit non-randomness — it must *establish* the randomness. The required tool is **phase-aware, cyclotomic-sensitive, and non-perturbative in `r`** — and is not in the literature.

## 6. Computational evidence (exact `F_p`, this campaign)

- `Sh(n,p):=M/\sqrt{n\log m}` over ~190 thin primes lies in `[1.07,1.49]` and **plateaus at `\sqrt2`**; no counterexample.
- **At the prize regime `β=4`, worst-case (highest `v_2(p-1)`) primes:** `Sh=1.199,\,1.214,\,1.336,\,1.389` for `n=16,32,64,128` — all **below `\sqrt2`**, approaching from below (the `C=\sqrt2` plateau). (`_wvl_disproof_search_v3.py`.)
- **Regime-gating (thinness-essential):** `Sh>\sqrt2` occurs *only* below `β=4` (e.g. `Sh=1.614` at the Fermat prime `p=65537`, `β=3.2`); at `β=4` the same prime gives `1.199`. A proof must therefore *use* the thinness `n\le p^{1/4}` — a thickness-uniform method would contradict the `β<4` values.
- **Recurrence-coefficient (form D) evidence:** `top\,eig(J)=M` to machine precision by truncation depth `\approx\log p`; the `b_k` obey the Hermite law `b_k^2/k=n` at shallow `k` (verified `14.5\approx16,\ 30.5\approx32,\ 62.5\approx64`) and turn over at `k^\*\approx(\log p)/2` (`k^\*=5,7,7` at `n=16,32,64` vs `(\log p)/2=5.5,6.9,8.3`); `M/(2\max_k b_k)=0.96\text{–}1.00`. Across fixed-`n` prime windows `2\max_k b_k` *tracks* `M`'s prime-to-prime variation while the shallow energy `E_5/\mathrm{Wick}\approx0.50` is flat — the recurrence coefficients carry the arithmetic signal the moments average out. (`/tmp/paley-probes/jacobi_tool.py`, `jacobi_scaling.py`, `toda_freud.py`.)

## 7. The ask, stated three ways (any one wins)

Prove, with an absolute constant uniform over `n=2^a` and `p\equiv1\ (\mathrm{mod}\ n)`, `p\asymp n^4`, **any** of:
1. `\displaystyle\max_{b\neq0}\Big|\sum_{x\in μ_n}e_p(bx)\Big|\le C\sqrt{n\log\tfrac{p}{n}}`;
2. `E_r(μ_n)\le K^r(2r-1)!!\,n^r` for `r\approx\log p` (equivalently `W_r-\mathbb E[W_r]=O^r((2r-1)!!\,n^r)`);
3. `\max_{k}\big|\sum_{j<m}e(jk/m)\,G(ω^{jn})/\sqrt p\big|\le C\sqrt{m\log m}`;
4. the orthogonal-polynomial recurrence coefficients of `μ_η` satisfy `\max_k b_k\le C\sqrt{n\log p}` — equivalently the Hermite-law turnover depth `k^\*=O(\log p)` (form D).

A *disproof* — a sequence `n\to\infty` with `Sh(n,p_n)\to\infty` at `β=4` — would refute the prize; §6 found none up to `n=128`.

---

*Honest status: the reduction (prize ⟺ §2) and the equivalences (§3) are machine-checked axiom-clean; §4–§6 are proven bounds / exact computation. The inequality §2 is **open** — it is the Burgess barrier. Companion derivations: `the-wraparound-variance-law-essay-2026-06-21`, `proximity-prize-complete-theory-2026-06-19`, `the-arithmetic-uncertainty-principle-essay-2026-06-19`. In-tree Lean index in `proximity-prize-complete-theory`. No proof of §2 is claimed or implied.*
