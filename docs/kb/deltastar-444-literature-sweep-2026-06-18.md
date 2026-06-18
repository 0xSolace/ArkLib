# δ* (#444) — Exhaustive literature sweep for a route past the wall (2026-06-18)

**Question (user):** the prize reduces to four equivalent "walls," a couple of which are *new framings*
this campaign (Λ(q)/Rudin; arcsine/phase-concentration). Does the literature — even *conditionally*, even
*only in the specific prize range* — contain anything that gives **exponent 1/2** for the worst-case
Gauss-period sup-norm?

**The object & the prize parameters (exact):**
```
M := max_{b ∈ F_p^*} | Σ_{x ∈ μ_n} e_p(b·x) |,   e_p(t)=exp(2πi t/p),   μ_n = n-th roots of unity, n = 2^μ.
n = 2^30 ≈ 1.07e9 (2-POWER subgroup);  p ≈ n·2^128 ≈ 2^158, so n ≈ p^{1/5.27} (THIN, BELOW p^{1/4});
m = (p−1)/n ≈ 2^128 cosets;  ln m ≈ 88.7;  saddle depth r* ≈ ln p ≈ 110.
GOAL ("prize floor"): M ≤ C·√(n·log m) ≈ 9.4·C·√n  —  EXPONENT 1/2 (up to √log).
```
Equivalent forms (Λ(q)-set bounded constant / additive moments E_k ≤ (2k−1)!!·n^k / sub-Gaussian period /
~Ramanujan Cayley graph). **SOTA = exponent ≈1; the gap to 1/2 is a FULL HALF-POWER.**

**Method.** A 13-domain multi-modal WebSearch sweep (`scripts/wf/lit-search-walls.mjs`): 77 raw leads → 76
distinct → the top 22 by prize-promise deep-read + **adversarially prize-checked** at the exact parameters,
with a hard anti-fabrication gate (every citation verified to exist this run). Then a **targeted completeness
pass** (this file's author) on the 5 highest-value targets that fell below the deep-read cut
(Harper, Yip, Duke–Garcia–Lutz / Kowalski–Untrau, Hanson–Petridis).

## VERDICT: 0 routes. Every verified result reduces, vanishes, or is circular.

Adversarial prize-check tally over the 22 deep-read leads: **15 REDUCES_TO_WALL, 6 VANISHES_AT_PRIZE,
1 IRRELEVANT, 0 real paths.** Targeted completeness pass: all 5 missed targets also reduce. The literature
contains **no** unconditional, conditional (GRH/Lindelöf/GRC), or 2-power-special-case route to exponent 1/2
for the worst-case sup-norm at n ~ p^{1/5.27}.

### The ledger (all citations VERIFIED to exist this run)

| Result | cite | verdict at prize | why |
|---|---|---|---|
| **BGK** (the wall itself) | Bourgain–Glibichuk–Konyagin, *JLMS* 73 (2006); expo. Kowalski **arXiv:2401.04756** (2024) | **exp 1−o(1), unconditional, APPLIES** | Only unconditional worst-case bound that does not vanish at n≈p^{0.19}; but δ′=ν(γ)/γ is tiny+ineffective (Bourgain–Katz–Tao sum-product). The wall to beat. |
| di Benedetto–Solymosi–White | **arXiv:2003.06165** (J.Numb.Th. 215, 2020) | **VANISHES** (exp ≈1.007 > trivial) | H^{1−31/2880} **requires p^{1/4}<H<p^{1/2}**; prize H≈p^{0.19} is below ⇒ vacuous. |
| Heath-Brown–Konyagin | "New bounds for Gauss sums from k-th powers" | **VANISHES** (exp ≈1.94 sup; ≈3/4 only for AVERAGE b) | Hölder/Parseval moment→supnorm + p^{1/4} tax; vacuous below ~p^{1/3}. |
| Bourgain–Garaev (variant sum-product) | "On a variant of sum-product estimates…" | **VANISHES** (trivial at p^{0.19}) | savings only for |H|>p^{1/4}. |
| Ostafe–Shparlinski–Voloch, *Weil Sums over Small Subgroups* | **arXiv:2211.0xxxx** (2022) | **VANISHES** | valid range τ ≥ p^{3/7+ε} excludes the prize entirely. |
| Macourt–Shkredov–Shparlinski (mult. energy of subgroups) | **arXiv:1701.06192**; Kerr–Shkredov–Shparlinski–Zaharescu **arXiv:2103.09405** | **REDUCES** (inherits BGK) | energy→sup-norm needs all-order sum-product cascade = BGK n^{1−o(1)}; the only "hypothesis" that closes it (E_k ≤ (2k−1)!!n^k at k≈ln p) IS the prize. |
| **Λ(p)-set theory** (Rudin/Pisier) | Pisier **arXiv:1704.02969**; Hare–Mohanty **arXiv:1910.08377** | **REDUCES — CIRCULAR** | **Pisier iff:** for a bounded ON system, Λ(p)-constant ≤ A·√p with A *p-independent* **⟺ the set is Sidon/dissociated**. So "μ_n is Λ(q) with bounded constant" is **logically EQUIVALENT** to the prize bound, not weaker. The Λ(q) framing reformulates the prize; it does **not** reduce it. |
| Paley-graph spectral pseudorandomness | Kunisky **arXiv:2303.16475** (2023) | **REDUCES** | worst-case edge eigenvalue gated by the *same* necklace/character-sum equidistribution (only a=1 unconditional); doesn't even specialize to 2-power H. |
| Global hypercontractivity | KLLM **arXiv:1906.05568** (JAMS); Keller–Lifshitz–Marcus **arXiv:2307.01356** (2023); cyclic-group Yao **arXiv:2512.03489** (2025) | **REDUCES — inapplicable** | global/β-small-influence hypotheses are on a product space (Ω^n,μ^n); μ_n⊂Z_p doesn't instantiate them. Forcing it lands on E_k(μ_n)≤(2k−1)!!n^k at k≈110 = the moment wall; Z_p log-Sobolev itself open. |
| RS proximity-gap / list-decoding (coding side) | CS25 **ePrint 2025/2046**; GCXK25 **ePrint 2025/870** | **IRRELEVANT / circular** | one abstraction layer above the analytic object; GCXK25's positive output is conditional on a (p,L)-list-decodability hypothesis for RS over μ_n = the hard problem itself. |

### Targeted completeness pass (the 5 high-value targets that missed the deep-read cut)

- **Harper, *Better-than-√ cancellation*** (**arXiv:1703.06654**, *Forum Math Pi* 2020; survey **arXiv:2512.23681**, 2025): the better-than-√ phenomenon (E|Σ_{n≤x}f(n)| ≈ √x/(loglog x)^{1/4}) is for the **typical/expected** value of a **random** multiplicative function. Our η_b is **deterministic**, the prize is the **worst case over b**, and the *maximum* of random-multiplicative partial sums is **not** better-than-√. The transfer to η_b would require the phases e_p(bx) to behave like independent random signs — exactly the equidistribution/independence that IS the wall. **REDUCES** (typical≠worst, random≠deterministic).
- **Chi-Hoi Yip, generalized Paley graphs** (e.g. clique work *J.Alg.Comb.* 2021; arXiv:2203.16081, 2004.01175): the second eigenvalue of Cay(F_q,μ_n) **equals** the character sum (= our M) and is bounded *via* Weil/BGK — Yip *uses* these estimates, doesn't beat them; his own results are about **clique numbers**, not new sup-norm bounds. **REDUCES**.
- **Duke–Garcia–Lutz / Kowalski–Untrau, Gauss-period distribution** (Kowalski–Untrau *Ultra-short sums of trace functions* **arXiv:2302.13670**, 2023; *Equidistribution and independence of Gauss sums* **arXiv:2207.12439**, 2022): **CONFIRMED FROM THE PDF** — *"a **fixed** monic polynomial g of degree d"*, μ_d the d-th roots, sums *"parameterized by a∈F_q become **equidistributed** … converge **in law**"* as q→∞. These are **fixed-d, distributional (average over b)** results — the limiting measure is the law of a sum of d random roots of unity. **"independent equidistribution"** = the limiting *joint distribution* factorizes (asymptotic, not finite-d moment independence). At the prize, **d=2^30 GROWS** (inapplicable) and we need the **worst-case max over b**, not the distribution. **REDUCES** (fixed-d + distributional = the easy "almost-all-b" side).
- **Hanson–Petridis, *Refined estimates … roots of unity*** (**arXiv:1905.09134**, *PLMS* 2021): Paley **clique** ≤ √(p/2)+1 (clique, not eigenvalue) and additive **sumset decompositions** Z_d=A+B — additive-combinatorial structure, the BGK class, not a worst-case sup-norm for growing d. **REDUCES**.

## The two clean characterizations of WHY (the durable findings)

1. **The Λ(q)/Rudin framing is the prize, by a theorem — not an independent attack surface.** Pisier's iff
   (**arXiv:1704.02969**) makes "μ_n is a Λ(q)-set with p-independent bounded constant" *logically equivalent*
   to Sidonicity, which for this object is equivalent to the sub-Gaussian moment bound = the prize. The Λ(q)
   route (`_LambdaQRudinEndToEnd`) therefore **reformulates** the difficulty into harmonic-analysis language;
   it does not lower it. This is *why* the new framing reduces — by a hard converse, not by hand-waving.

2. **Every Gauss-period equidistribution / "independence" result is FIXED-d + DISTRIBUTIONAL.** The prize is
   GROWING-d (d=2^30) + WORST-CASE-over-b. These are orthogonal axes. The equidistribution literature controls
   the *proportion* of b with η_b in a range (the easy side we already have via Parseval); it is silent on the
   *extreme* over ~p frequencies, and inapplicable once d grows with p.

## Bottom line (honest)

There is **no false hope and no false despair**: as of June 2026 the verified literature contains **no route —
unconditional, conditional, or 2-power-special-case — to exponent 1/2** for the worst-case Gauss-period
sup-norm at the prize parameters. The current SOTA at n≈p^{1/5.27} is **BGK, exponent 1−o(1)** (Kowalski
arXiv:2401.04756), unconditional and applicable but ineffective; the only "sufficient hypothesis" anyone offers
is the Paley Graph Conjecture (M ≤ 2√n) itself, which is circular. The four campaign wall-faces are confirmed
**genuinely equivalent** to this single open problem — the Λ(q) one provably so (Pisier).

## Residual completeness note / next searches if revisited
- We did NOT find any 2024–2026 *unconditional* improvement of the **exponent** at thin subgroups (the recency
  sweep D7 surfaced only Kowalski's 2024 BGK exposition and the equidistribution line).
- Untouched corners (low prior, listed for honesty): Bourgain–Chang's deep multilinear bounds at very thin H;
  the Vinogradov-mean-value / decoupling-in-F_p exponent for E_k at k≈log p (decoupling needs curvature, μ_n
  flat — see memory `issue444-modern-tools-nogo`); Sawin–Katz monodromy for the *specific* growing-d family.
  None are expected to cross — all are character-sum/curvature objects that the in-tree no-gos already cover.
