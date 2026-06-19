# External research: the β=4 subgroup-sum / BGK wall in the 2022–2026 literature (#444)

**Date:** 2026-06-18. **Method:** targeted web search + primary-source fetch (arXiv PDFs, journal
pages). **All citations verified by fetch** (no fabricated IDs — a prior hazard in this campaign).

## The question

Bound `M(μ_n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|` for the thin 2-power multiplicative subgroup
`μ_n ⊂ F_p^*` (`n=2^μ`) at the prize aspect `|μ_n| = n ≈ p^{1/4}` (β=4). Target `M ≤ C√(n log q)`
(= the Paley-graph / BGK conjecture at β=4). Is there ANY 2022–2026 external result that beats the
additive-combinatorics SOTA `n^{1-o(1)}` (di Benedetto et al.) for this **linear** subgroup sum?

## Verdict: NO external breakthrough. The wall is confirmed external, open, and unbroken as of 2026.

The three method-families that could conceivably help each hit a **proven barrier or structural
exclusion** — and each matches, independently, a wall this campaign found internally.

### 1. Algebraic geometry / Weil sums — STRUCTURALLY EXCLUDES the linear case

**Ostafe–Shparlinski–Voloch, "Weil Sums over Small Subgroups"** (arXiv:2211.07739, Math. Proc.
Camb. Phil. Soc., online Aug 2023). Gets bounds on `Σ_{x∈H} e_p(f(x))` nontrivial where the classical
Weil bound is already trivial — BUT only for `deg f = d ≥ 2` (absolutely irreducible). The period is
the **linear** case `f(x)=bx` (`d=1`); via the monomial bridge it is `Σ_{x∈F_p^*} e_p(b x^m)`,
`m=(p-1)/n ≈ p^{3/4}`, where Weil gives `(m-1)√p ≈ p^{5/4}` — vacuous (the di Benedetto starting
point). **AG methods do not touch the period.** (Matches our internal "0-dim Weil-vacuity" finding.)

### 2. SDP / sum-of-squares — PROVEN Ω(p^{1/3}) barrier

The degree-4 SOS relaxation of the Paley clique has value `≥ Ω(p^{1/3})` (Kunisky–Yu / Kobzar–Mody;
"A Degree 4 SOS Lower Bound for the Clique Number of the Paley Graph", LIPIcs.CCC.2023.30; spectral-
pseudorandomness, *Experimental Mathematics* 34(4) 2024, doi:10.1080/10586458.2024.2400182). So SDP/SOS
**provably cannot** reach the conjectured `polylog`/`√(n log)` scale; numerics suggest only a polynomial
improvement may ever be possible. **This independently confirms our flag-algebra/SDP mechanic refutation.**

### 3. Stepanov's method — THICK-subgroup only (β ≤ 3)

**Hanson–Petridis, "Refined Estimates Concerning Sumsets Contained in the Roots of Unity"**
(arXiv:1905.09134): clique number of the Paley graph `≤ √(p/2)+1` via Stepanov, for the **quadratic
residue** subgroup (density 1/2, `|H| ≈ p/2`, β≈1). Stepanov is nontrivial only for thick subgroups;
at the thin β=4 prize point it is trivial (`M ≪ n`), exactly as our Track-1 `STEPANOV_DIRECT` (HBK
`k=(p-1)/n ≈ p^{3/4}` lands in the trivial range) found. Does **not** transfer to thin `μ_n`.

## Adjacent recent results (real, but do not move the sup at β=4)

- **Yip, "Exact values and improved bounds on the clique number of cyclotomic graphs"** (arXiv:2304.13213,
  Designs Codes Cryptogr. 2025): first nontrivial clique bound for ALL generalized Paley graphs of
  non-square order: `ω(Cay(F_q,S)) ≤ √|S/S| + √(q/p)`. For `S=μ_n` (a group, `S/S=μ_n`) over `F_p`:
  `ω ≤ √n + 1`. This is the **clique** number (a Hoffman/ratio-bound consequence), NOT the second
  eigenvalue `M = max|η_b|`; the ratio bound does not require `M` small, so it does not bound the period sup.
- **Shkredov** (medium subgroups): `E^×(Γ+x) ≪ |Γ|² log|Γ|` for `|Γ| ≈ √p` — multiplicative energy of a
  *shifted* subgroup, *medium* size; not the additive energy of a *thin* one.
- **Yip 2024** (arXiv:2304.13801): a large multiplicative subgroup is not `A+A` or `A+B+C` nontrivially
  (additive *decomposition*, not an energy upper bound).
- **Kowalski**, expository proof of BGK (arXiv:2401.04756, Jan 2024): exposition, no new bound.
- **"Necklace character sums"** (the genuinely-new 2024 object, *Exp. Math.* 2024): estimates would imply
  Paley spectral-distribution convergence — but it targets the **bulk/spectral distribution** (the
  *average*), not the deterministic **sup** `M`. Conditional, and on the wrong side of the average-vs-sup
  split that is this campaign's recurring wall.
- **Randomstrasse101 Open Problems of 2025** (arXiv:2603.29571): the Paley clique / character-sum-over-
  subgroups problem is still listed open; the flagged 2025 frontier is "explicit degree-4 SOS certificates"
  — already known to be barriered at `Ω(p^{1/3})`.

## Honest conclusion

The shallow target `E_2(μ_n)=O(n²)` for thin subgroups (= our `BoundedRep2` / cubic char-sum) is **not
resolved in the literature** — all unconditional additive-energy / sumset estimates for roots of unity in
the literature are for **thick** subgroups (QR-scale). The deterministic sup at β=4 sits in a genuine gap
between three barriered method-families. The wall this campaign identified is the *same* wall the field is
stuck at; there is no off-the-shelf external theorem to import. The most tractable concrete external problem
remains the **cubic character-sum cancellation** `Σ_{t≠0} η_t³ e_p(-t) = O(pn)` (⟺ `E_2(μ_n)=O(n²)` at the
prize prime) — a fixed-degree, genuinely-shallower-than-the-deep-wall object, still open, and the natural
target for any future progress. This is a literature-grounded confirmation, not a closure.
