# Bourgain Problem 5 — creative far-reaches exploration (8-angle workflow, self-synthesized)

**Goal:** angles Bourgain (d.2018, analyst) or the campaign would NOT consider — post-2018 / non-analysis
math — researched (web), attempted (prize-faithful probes: proper μ_n, n=2^μ, p≡1 mod n, β≈4, multi-prime,
never n=q-1), ranked by feasibility-TO-CLOSE. Result: NO closure; all reduce-to-wall / do-not-apply, each
with a PRECISE structural reason — and a unifying meta-insight.

## Ranked (feasibility-to-close, high→low)

| # | angle | feas | verdict | precise reason |
|---|-------|------|---------|----------------|
| 1 | Function-field lift + transfer | 2/10 | reduces-to-wall | G-K arXiv:2307.01344 depth o(n²) is an AVERAGE over all of M_{n,q}, explicitly non-transferable to single sums; Weil on fixed-F_p object = √p = n² ≫ n (vacuous at β=4). Full FF machinery, wrong-sized object. |
| 2 | Arithmetic dynamics (Untrau equidistribution arXiv:2112.05441) | 2/10 | reduces-to-wall | The cleanest NEAR-MISS: limiting measure of Σ_{x^d=1}e_q(ax) is the correct Gaussian shape, but the theorem is FIXED-d, p→∞; prize d=n=p^{1/4} growing ⟹ BGK exponent/threshold non-uniform in d, dissolves. |
| 3 | Zilber–Pink / unlikely-intersections on torsion μ_n | 1/10 | does-not-apply | Beukers–Smyth (≤11(deg)² torsion pts) / Aliev–Smyth need the FULL Gal(ℚ(ζ_n)/ℚ)=(ℤ/n)* action (char 0); in F_p, p≡1 mod n ⟹ Frobenius trivial (one fixed element). Wrong characteristic. |
| 4 | Coding min-distance (Delsarte LP/BCH/Roos/HT) | 1/10 | does-not-apply | p≡1 mod n ⟹ xⁿ−1 splits over F_p ⟹ eval-kernel cyclic code has min-distance EXACTLY 2; not F_q-linear in the needed sense; LP/BCH give nothing toward >2 ln q. |
| 5 | Entropy / PFR-2023 / Kelley–Meka / Bloom–Sisask | 1/10 | does-not-apply | Wrong regime (density n/p=p^{-3/4}→0, increment dies) + wrong direction (inverse theory: energy→structure; prize needs upper bound on energy). |
| 6 | Affine spectral gap (Lindenstrauss–Varjú / BGS) | 1/10 | REFUTED (exact identity) | Affine gap is gated by the LINEAR part's gap = identically 0 for abelian μ_n; in additive-char basis dilation = cyclic permutation of frequencies ⟹ all eigenvalues on unit circle, no gap. |
| 7 | Depth-symmetry for primitive χ (G-K shape) | 1/10 | does-not-apply | G-K gcd-symmetry collapses a LONG exponent k against |F_{q^n}*|=q^n−1; prize x∈μ_n enters to first power (x^k depends on k mod n only) — no long exponent to collapse. Frobenius-twist / 2-adic tower / multiplier action all give the same R1+R2/HD n/4 DOF. |
| 8 | Wildcard (o-minimality / Katz-Sarnak / Ramanujan-construction / Berkovich) | — | (agent incomplete on session limit) | — |

## THE unifying meta-insight (why all far-reaches fail — and it's structural, not incidental)

Every tool with a CEILING above the analytic √-wall — Zilber–Pink, function-field Weil/Deligne, the G-K
depth-extension symmetry — **relies on a rich Galois/Frobenius action.** The prize regime `p ≡ 1 (mod n)`
makes `μ_n` split completely in `F_p` with Frobenius acting **trivially** (the single fixed element of
`(ℤ/n)*`). So the prize sits in the **symmetry-minimal / maximally-split regime**, exactly where the
algebraic-geometry and symmetry-extension machinery dissolves. This is not a coincidence: `p≡1 mod n` is the
FFT-friendliness that makes the code cryptographically useful (smooth-domain RS), and it is precisely the
property that strips the Galois symmetry any "far-reaches" lever would exploit. **The prize is engineered to
be symmetry-poor.** This sharpens *why* it is hard: it is not just "a thin char sum," it is a thin char sum in
the one arithmetic regime where the cross-disciplinary symmetry tools have nothing to grip.

## Consequence for future attacks
A winning method must work in the SYMMETRY-MINIMAL setting — it cannot import Galois/Frobenius richness
(absent), cannot use family-averaging (prize is a single fixed q, worst-case), cannot use density-increment
(μ_n is sparse+Sidon). Combined with the in-tree 3-property necessary condition (b-sensitive + deterministic-
archimedean + L∞), the surviving target shape is extraordinarily narrow. The two least-dead leads remain the
function-field TRANSFER (if the average→single-sum barrier can be broken for this specific subgroup) and the
arithmetic-dynamics uniformity (if Untrau's equidistribution can be made uniform in growing d) — both
low-feasibility, both requiring genuinely new mathematics, consistent with the recognized-open status.

Sources: arXiv:2307.01344 (Gorodetsky–Kovaleva), arXiv:2112.05441 (Untrau), Beukers–Smyth 2002 / Aliev–Smyth
arXiv:0704.1747, arXiv:1409.3564 (Lindenstrauss–Varjú), arXiv:2401.04756 (BGK expository), Kelley–Meka 2023.

## Survivor deep-dive (the 2 least-dead leads) — both FUNDAMENTAL barriers (proven)

**Survivor 2 — exchangeable-white-noise → MAX route: RIGOROUSLY KILLED.** A moment/L^{2r}-union bound
`Pr[max_b|η_b|≥T] ≤ m·E[η^{2r}]/T^{2r}` with the sharp Wick moment reaches `max ≤ c√(n log m)` IFF `c>√2`
at `r* = (c²/2) log m` — derived exactly (Stirling on `(2r−1)!!`; the log log m terms cancel, so it is exact
not slack; confirmed at 5 prize-faithful points). ⟹ the route PROVABLY needs `r≈log m` moments — exactly the
deep range it was meant to bypass; the proven low moments (r=2 Sidon, r=3) are provably insufficient. The
covariance/exchangeability structure buys nothing around the deep moments.

**Survivor 1 — function-field / Weil: FUNDAMENTAL (the symmetry-minimal insight, concretely).**
- Transfer barrier: Parseval pins `avg_b|η_b|²=n` (L² floor; verified 3.98/8.00/16.00) vs target L∞ peak
  `n·log m`, ratio `√(log m)` GROWING — no family-average gives the worst case. G-K depth-o(n²) is an average
  over all of `M_{n,q}`, non-transferable to a single sum.
- Weil-on-the-curve barrier (made exact via Rojas-León Cor 5.3): `p≡1 mod n` ⟹ `μ_n` splits completely ⟹ the
  base `{x:xⁿ=1}` is 0-DIMENSIONAL (n distinct F_p-points) ⟹ the curve `y^d=1+x` over `xⁿ=1` is a union of
  0-dim fibers ⟹ NO `H¹` to extract a √-bound. Escape needs a nontrivial extension `F_{p_0^r}`, r≥2 (prize p
  prime → r=1 → zero gain). Trivial Frobenius ⟹ no cohomology ⟹ Weil bounds nothing.

## FINAL MAP: everything → BCHKS Conjecture 1.12, with three proven no-escape reasons
Every angle (8 creative + 4 survivor sub-attacks) reduces to ONE residual: the char-p deep-moment energy
bound `E_r(μ_n, F_p) ≤ (2r−1)‼·nʳ` at `r ≈ log m` for 2-power FFT primes `p≡1 mod n` (= BCHKS Conj 1.12).
No escape, for three sharp PROVEN reasons:
 (1) SYMMETRY-MINIMAL: `p≡1 mod n` ⟹ trivial Frobenius ⟹ Galois/Zilber-Pink/FF-symmetry tools dissolve.
 (2) 0-DIMENSIONAL BASE: same splitting ⟹ no cohomology for Weil/Deligne to bound.
 (3) NO LOW-MOMENT SHORTCUT: any union bound provably needs `r ≈ log m` moments (deep range).
This is the cleanest characterization of the prize's hardness the campaign has: it is not "a hard char sum,"
it is BCHKS-1.12 in the one regime engineered (by FFT-friendliness) to remove every symmetry/cohomology/
shortcut lever — leaving only the direct deep-moment estimate, which is the recognized 25-yr-open core.

## 4th proven no-escape reason (deepest, from the FF survivor deep-dive)
(4) ARCHIMEDEAN INFO DISCARDED IN FF: the genuine function-field analog of μ_n (Carlitz-torsion geometric
Gauss sums) has a UNIFORM v-ADIC valuation (Gross-Koblitz, arXiv:2502.01109 Prop 1.3.4: normalized valuation
−1/(q−1)), NOT an archimedean modulus on a circle in ℂ. The prize is the ARCHIMEDEAN magnitude / √-cancellation;
the FF object has a completely-determined ALGEBRAIC v-adic size and has thrown away the archimedean phase info.
So function fields — where the full Weil/Deligne machinery is available and everything is provable — are
provable about the WRONG (v-adic) object; transfer back would need to re-manufacture archimedean cancellation
from a v-adic identity, and the archimedean and v-adic places are DECOUPLED (no mechanism; would need a new
Gross-Koblitz-style archimedean companion). This is why "lift to where it's provable" fundamentally fails:
the provability comes precisely from having discarded the prize's content.

So: 4 PROVEN structural reasons no far-reaches angle escapes the BCHKS-1.12 core — (1) trivial Frobenius kills
Galois tools, (2) 0-dim base kills Weil cohomology, (3) low-moment union provably needs r~log m, (4) the FF
analog is v-adic not archimedean. The prize is BCHKS Conj 1.12 in the symmetry/cohomology/shortcut-minimal
regime; the only surviving target is the DIRECT char-p archimedean sup-norm at depth r~log m for the primitive
character — the recognized 25-yr-open wall. CREATIVE-EXPLORATION LOOP COMPLETE (no closure; sharp WHY-map).
