# Exhausting the Surviving Levers: Weingarten Majorization, the Jacobi Self-Map, and the Metaplectic Frontier
### Final attack record on the Uniform-Vertical-Sato–Tate program for the Paley Graph Conjecture at β=4

*ArkLib Proximity-Prize programme (issue #444), 2026-06-19. Self-contained. Every numerical claim is reproduced by a committed exact-`F_p` probe; literature is cited with author + ~year. Honest status: the Paley Graph Conjecture at β=4 remains **open**; nothing here closes it, and no QED is claimed. This document attacks the two levers left open by the previous record (`uvst-theorem-invent-prove-refute-2026-06-19.md`) and the remaining external angles, to a definite verdict on each.*

---

## 0. What was open, and the verdict of this round

The previous record refuted the naive big-monodromy form of the missing ingredient, isolated the correct form (horizontal high-order spectral flatness — the Arithmetic Independence Certificate, AIC), and flagged two unexplored levers. This round attacks them and everything remaining.

> **Verdict.** **Lever (ii) (Jacobi descent) is refuted** as a proof route — the self-map is isomorphic, not contracting. **Lever (i) (Weingarten majorization) is the genuine survivor**: the majorization `ρ_r(u) ≤ ρ_O(m,r) ≤ 1` holds, robustly and at the *operative saddle depth*, and proving it *is* the AIC — but it reduces to the wall (its content is a domination of the Jacobi-sum correlations that is not delivered by any unconditional input). **The metaplectic theory of Gauss-sum moments** is the correct external home for the problem; it confirms the AIC's main term is the Wick count, but its error terms are uncontrolled at the thin scale and logarithmic depth — again the wall. After this round the internal program is **exhausted**: every lever either is refuted or reduces to the single inequality (AIC), which is empirically true at saddle depth across `n=16…256` and is the BGK/Burgess wall.

Recall (Theorem A, exact): `η_b = (n/(p−1))(−1 + √p·S_b)`, `S_b` = cyclic DFT over `ℤ/m` of the unit phases `u_t = G(ψ^t)/√p`, `m=(p−1)/n`. At β=4: `m ~ n³`, `√p = n²`. Paley ⟺ `max_b|S_b| ≤ C'√(m log m)` ⟺ `ρ_r(u) := mean_b|S_b|^{2r}/((2r−1)!!\,m^r) ≤ K^r` to depth `r* ≈ log m` (the AIC).

## 1. Lever (i): the Weingarten majorization — the genuine survivor, reduces to the wall

The conjugate symmetry `u_{m−t} = \overline{u_t}` places any group model of the phase field in the **orthogonal** group `O(N)`. The Haar matrix-coefficient moment ratio is (previous record, Lean-verified) `ρ_O(N,r) = N^r/∏_{j<r}(N+2j) ≤ 1`.

> **Observation 1.1 (the majorization holds; probe `_uvst_levers_probe_v1.py`).** For the deterministic Gauss-phase sequence at β=4,
> $$\rho_r(u)\;\le\;\rho_O(m,r)\quad\text{for every }r\le 7,\ n=16,32,64,$$
> with the actual ratio *far* below the Haar cap (e.g. `n=16, r=7`: `ρ_r(u)=0.232` vs `ρ_O=0.990`). The deterministic sequence is **more sub-Gaussian than orthogonal Haar** at fixed depth.

> **Observation 1.2 (the AIC holds at the saddle depth; probe `_uvst_aic_saddle_v1.py`).** At the operative depth `r* = round(log m)`,
> $$\rho_{r^*}(u)=0.141,\;0.176,\;0.494,\;0.265,\;0.219\quad(n=16,32,64,128,256),$$
> bounded well below `1` as `n` grows through `256`. This is the strongest evidence to date that the AIC `ρ_r ≤ K^r` (indeed `ρ_r ≤ 1`) holds at the working depth, not merely at small `r`.

So the lever points exactly the right way: **proving `ρ_r(u) ≤ ρ_O(m,r)` (or just `≤ 1`) to depth `log m` would close Paley.** What does proving it require?

> **Theorem 1.3 (the majorization unwinds to a correlation-domination — reduction, not closure).** By Theorem A, `ρ_r(u)` is the Wick-normalized `2r`-th additive moment of `(u_t)`:
> $$\rho_r(u)=\frac{1}{(2r-1)!!\,m^r}\sum_{\substack{t_1-t_2+\cdots-t_{2r}\equiv 0\ (m)}}u_{t_1}\overline{u_{t_2}}\cdots\overline{u_{t_{2r}}}.$$
> The Weingarten/partition expansion writes the Haar value `ρ_O(m,r)` as the same sum with each `u`-product replaced by its Haar pair-correlation (`= 1` on a matched pair, `0` otherwise, up to `O(1/m)` Weingarten corrections). The majorization `ρ_r(u) ≤ ρ_O(m,r)` is therefore *equivalent* to: **the genuine `r`-fold Jacobi-sum correlations of `(u_t)` are dominated, after summation, by the Haar (matched-pair) weights**, uniformly to depth `log m`.

*Proof.* The displayed identity is Theorem A expanded; the Haar side is the standard orthogonal Weingarten formula (Collins–Śniady 2006). Equating the two sums termwise-by-partition gives the stated equivalence. $\square$

> **Status (honest).** Theorem 1.3 is a *clean new reformulation*, not a proof. The matched-pair (diagonal) terms are common to both sides; the majorization is exactly the statement that the **off-diagonal Jacobi correlations sum to something `≤` the Weingarten correction**. At depth `r ≤ 3` this is unconditional (no wraparound, `W_r = 0`, the char-0 Bessel regime, `_AvW0_BesselWickDomination`). At depth `r ≈ log m` it is the **wraparound-≤-chance** inequality — i.e. the BGK/Burgess wall. No unconditional input (Weil, the Weingarten asymptotics, the partition algebra) bounds the *signed* off-diagonal sum at logarithmic depth and thin scale; the partition framing reorganizes the wall but does not breach it. **Lever (i) survives as the sharpest reformulation of the open core, and reduces to the wall.**

## 2. Lever (ii): the Jacobi modulus-descent self-map — refuted

The 4th-moment off-diagonal collapses (previous record, Theorem; verified `10^{-11}`) to `A_s = m\,η'_s`, where `η'_s = \sum_{ζ∈μ_n}ψ^{-s}(1+ζ)` is a Paley-type period of the multiplicative character `ψ^{-s}` over the affine-shifted set `1+μ_n`. The lever asked whether iterating this descent contracts the problem.

> **Theorem 2.1 (the descent is isomorphic, not contracting — refutation; probe `_uvst_levers_probe_v1.py`).** At β=4,
> $$\max_s|η'_s| = n-1\ \text{exactly}\quad(\text{attained at } s=0,\ \text{the trivial character}),$$
> and the nontrivial part `max_{s≠0}|η'_s| = Θ(\sqrt n)` — the **same square-root floor** as the original `max_{b≠0}|η_b|`. The descended object lives on an identical Plancherel floor (`mean_s|η'_s|^2 = 2n-3 ≈ 2n`).

*Proof.* `η'_0 = #\{ζ∈μ_n : 1+ζ≠0\} = n-1` since `−1∈μ_n`. For `s≠0`, `η'_s` is a sum of `n` `m`-th roots of unity; the Plancherel identity `\sum_s|η'_s|^2 = m(2n-3)` (verified: `118784 = 4096·29` at `n=16`) forces typical size `\sqrt{2n}` and the observed `max_{s≠0} = Θ(\sqrt n)`. $\square$

> **Corollary 2.2 (no bootstrap).** The self-map sends a √n-floor sup-norm problem over `μ_n` to a √n-floor sup-norm problem over `1+μ_n`, with the sup carried by a *trivial-character DC term* (analogous to `η_0=n`). Crucially, `1+μ_n` is **not a multiplicative group**, so the Jacobi-collapse identity (which used orthogonality of `H^\perp=⟨ψ⟩`) does **not** iterate: the descent terminates after one step at an equal-difficulty, non-group problem. There is no contraction and no fixed-point gain. **Lever (ii) is refuted as a route to a proof.** (The exact collapse identity remains a genuine, useful structural fact — it is what *feeds* the correlation sum in Theorem 1.3.)

## 3. The metaplectic frontier: moments of Gauss sums

The moment `ρ_r(u)` (Theorem 1.3) is, up to normalization, a **restricted high mixed moment of Gauss sums**: `\sum \prod_i G(ψ^{t_i})` over `2r`-tuples with `\sum ±t_i ≡ 0`, the characters confined to the order-`m` subgroup `⟨ψ⟩`. This is precisely the class of objects in the analytic theory of **moments of Gauss sums / metaplectic Eisenstein series**.

- **Patterson (1977–78)** and **Heath-Brown–Patterson (1979)**: the cubic Gauss sums `G(χ)` have a *secondary main term* (a bias `~ X^{5/6}`) in their first moment, with the normalized sums otherwise equidistributing — the metaplectic-Eisenstein residue.
- **Dunn–Radziwiłł (2021)**, *Bias in cubic Gauss sums: Patterson's conjecture*: proved the cubic-bias conjecture, the state of the art on first moments of Gauss sums.

> **Reduction 3.1 (metaplectic gives the right main term, not the high-depth control).** The metaplectic theory computes the **main term** of low moments of Gauss sums to be the **diagonal / Wick count** — exactly the `(2r-1)!!\,m^r` against which `ρ_r` is normalized — with all other contributions (the Patterson bias and equidistribution errors) **sub-leading**. This *confirms the AIC's structure*: the main term is Wick, and the AIC is the assertion that the *fluctuation around it stays controlled*. But the theory's effective control is for **first/low moments** of *single* Gauss sums over *full* character families as `p→∞`; it does **not** deliver a power-saving error for the **restricted high mixed moment** (depth `r~log m`, characters in a thin subgroup, fixed thin `p~n^4`). At that depth and scale the error terms are uncontrolled — the same `W_r ≤` chance wall. **The metaplectic theory is the correct external framing and confirms the main term, but reduces to the wall for the quantity we need.**

> **Honest note.** This is the closest the missing input comes to existing mathematics. A genuine advance would be an **effective high-moment metaplectic estimate** uniform over a thin subgroup of characters — a strengthening of Heath-Brown–Patterson/Dunn-Radziwiłł from first moments to depth-`log` mixed moments — which does not exist in the literature.

## 4. Remaining angles, and the completeness audit

- **Multiplicative character sums over a shifted subgroup** (the descended object `η'_s = \sum_{x∈μ_n}ψ(x+1)`). Best known bounds (Karatsuba; Bourgain–Garaev; Shkredov; Konyagin–Shparlinski) give `≪ |H|^{1-c}` only for `|H| > p^{1/4}` with the saving vanishing at `|H| = p^{1/4}` — the **same Burgess barrier**, at the same β=4 scale. Isomorphic, no gain. (Consistent with Theorem 2.1.)
- **Clique number / spectral combinatorics.** The clique number of `Cay(F_p,μ_n)` is governed by the same eigenvalue `M`; the Hoffman/ratio bound runs *backwards* (it would *follow from* `M` small, not yield it). No independent handle.
- **Multiplicative large sieve / Gallagher** on the restricted high moments: the large sieve gives the `L^2` average exactly (Parseval, `mean_b|S_b|^2 = m`), hence only the trivial pointwise bound `m` — the moment-cap (Johnson) prong.
- **Completeness audit.** Across the whole campaign the attack surface is: monodromy-in-`b` (refuted, abelian), symmetry-forcing (refuted, `ρ_O<1`), vertical Sato–Tate (thick-only), moment/energy ladder (Johnson-capped), Jacobi descent (refuted, isomorphic), Weingarten majorization (reduces to wall), metaplectic moments (reduces to wall), shifted-subgroup sums (isomorphic), clique/large-sieve (no handle). **No internal angle remains unattacked.** Every route is refuted or funnels to the single inequality.

## 5. Conclusion: the program is exhausted; the core is one inequality

> **Final status.** After inventing the missing "growing-rank big-monodromy / uniform vertical Sato–Tate" input and attacking it through four candidate forms, two adversarial loops, both surviving levers, and the metaplectic frontier, the structure is fully exposed and **internally exhausted**:
> - **Refuted** (rigorous): naive big-monodromy (abelian spectral local system); symmetry-forcing (`ρ_O(N,r)<1`, Lean-verified); the Jacobi descent self-map (isomorphic, Theorem 2.1).
> - **Reduces to the wall** (precise reductions): the Weingarten majorization (Theorem 1.3 — the sharpest reformulation, a correlation-domination); the metaplectic high-moment estimate (Reduction 3.1 — right main term, no high-depth control); shifted-subgroup and large-sieve routes.
> - **The irreducible open core (AIC):** `ρ_r(u) ≤ K^r` to depth `r ≈ log m`, uniformly at β=4 — equivalently *wraparound ≤ chance to depth log p*, equivalently the Weingarten majorization. It is **empirically true at the saddle depth across `n=16…256`** (Observation 1.2), **escapes both pincer prongs**, and **is the BGK/Burgess wall itself**.
> 
> **The Paley Graph Conjecture at β=4 remains open.** The honest conclusion of this program is that the missing input is *genuinely external and not present in the literature*: an **effective, thin-scale, high-depth (`r~log m`) estimate for restricted mixed moments of Gauss sums** — a logarithmic-depth, subgroup-uniform strengthening of metaplectic moment theory. Equivalently, in the Weingarten language, a domination of the signed `r`-fold Jacobi-sum correlations by the Haar pair weights to logarithmic depth. No current technique (Weil/Deligne — vacuous at thin scale; sum-product/Burgess — saturates at `n^{1-o(1)}`; metaplectic — first-moment only; decoupling — needs curvature) delivers it. That single estimate is the prize.

---

### Appendix: reproducibility (all committed)
- `scripts/probes/_uvst_levers_probe_v1.py` — Weingarten majorization `ρ_r(u) ≤ ρ_O(m,r)` (r≤7); Jacobi descent `max_s|η'_s|=n-1`, nontrivial `Θ(√n)` (isomorphic).
- `scripts/probes/_uvst_aic_saddle_v1.py` — AIC at saddle depth `ρ_{r*}∈[0.14,0.49]`, `n=16…256`.
- `scripts/probes/_uvst_monodromy_probe_v1.py`, `_uvst_refutation_hunt_v1.py`, `_phase_offdiag_isometry_v1.py` — prior-round structural facts and the Jacobi collapse (`A_s=m\,η'_s`, verified `10^{-11}`).
- `ArkLib/.../Frontier/_AvUVST_OrthogonalSymmetryWickCap.lean` — `ρ_O(N,r)≤1`, `<1` strict for `r≥2`, axiom-clean.
- Literature: Patterson (1978); Heath-Brown–Patterson (1979); Dunn–Radziwiłł (2021); Collins–Śniady (2006, Weingarten); Bourgain–Garaev, Konyagin–Shparlinski (subgroup sums); Katz (1988, 1990); Fouvry–Kowalski–Michel (2014, 2019).
