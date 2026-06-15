# Paley / Shifted-Subgroup Character-Sum Assault — Synthesis

**Object.** Bound the shifted 2-power subgroup multiplicative character sum
  S(χ) = Σ_{ζ∈μ_n} χ(1+ζ),  μ_n = the 2^μ-th roots of unity in F_p, n = 2^μ, p ≈ n^4 (β = 4), m = (p−1)/n ≈ 2^128.
**Target.** S(χ) ≤ C·√(n·log m) (√-cancellation up to a polylog) at the Burgess barrier |H| = n ≈ p^{1/4}.
**Equivalences.** This is (i) the multiplicative dual of the additive Gauss period M(n) = max_{b≠0}|Σ_{ζ∈μ_n} e_p(bζ)|;
(ii) the eigenvalue of the generalized Paley/Cayley graph Cay(F_q, μ_n) (Liu–Zhou arXiv:1809.09829, Thm 115); and
(iii) an instance of the **Paley Graph Conjecture** (Bourgain; Kim–Yip–Yoo arXiv:2309.09124, Conj 2.12). The bound
S ≤ 2√n is exactly "Cay(F_q,μ_n) is Ramanujan."

Six independent angles were developed and probed (exact discrete-log / FFT, β = 4, exhaustive over **all** characters
where feasible). **All six report `crosses-burgess = no`. None survives.**

---

## 1. Did any angle cross the Burgess barrier? — RANKED BY PROMISE

**No.** Not one angle produced an unconditional bound below the trivial-up-to-o(1) n^{1−o(1)} at n = p^{1/4}, and
**none even matched, let alone beat, the additive-BGK exponent n^{0.989}** at the barrier. Ranked by residual promise
(highest = most worth remembering, still all negative):

| Rank | Angle | Best unconditional output at β=4 | Reduces to | New exact artifact (the keeper) |
|---|---|---|---|---|
| 1 | **sum-product on A = 1+μ_n** | none beyond ineffective n^{1−o(1)} | circular / open J_k | **E_×(1+μ_n) = 2N²−N exactly** (perfect mult. Sidon, MINIMAL order-2 energy, N = n−1); additive spike-at-2 from −1∈μ_n |
| 2 | **dyadic/squaring recursion** | none (triangle-ineq only) | circular | **Σ_ζ χ(1−ζ)χ(1+ζ) = 2·S_{n/2}(χ)** (exact, 2-power-specific) |
| 3 | **wildcard 2-power (closure + telescope)** | none | circular | same squaring identity + telescope log χ(2) = log χ(1−ζ) + Σ_i log χ(1+ζ^{2^i}) |
| 4 | **multiplicative-dual S vs M** | none (negative structural result) | open-conjecture | exact Fourier duality S(χ) = Ḡ(χ)^{−1} Σ_t χ̄(t) e_p(t) η(t); worst χ is trivial on μ_n |
| 5 | **Stepanov in shifted coords** | strictly WORSE than additive Stepanov | open-conjecture | exact mod-p conditions-rank = full (degeneracy 0): (X−1)^n−1 is squarefree → no high-order vanishing |
| 6 | **literature pin** | n/a (confirms no mechanism exists) | open-conjecture | the SOTA citation map (see §2) |

The "promise" ordering reflects which exact identities are most likely reusable downstream, **not** any progress toward
the bound — every row's net contribution to the prize is zero.

---

## 2. THE LITERATURE FINDING — true SOTA for Σ_{x∈H} χ(x+a) at |H| ~ p^{1/4} (the key fact)

**Shifted-subgroup multiplicative character sums are governed by the SAME machinery as the additive subgroup
exponential sum, with no better exponent at the barrier.** They are Fourier duals on F_q and are bounded by identical
Bourgain–Glibichuk–Konyagin (BGK) sum-product / multiplicative-energy amplification. Precise SOTA, with the regime each
requires:

- **di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo (2020)**, *New estimates for exponential sums over
  multiplicative subgroups and intervals*, J. Number Theory 215, 261–274 (arXiv:2003.06165): the best EXPLICIT subgroup-sum
  exponent, max_{(a,p)=1}|Σ_{x∈H} e_p(ax)| ≤ H^{1−31/2880+o(1)} = **H^{0.98924}**. **Valid only for H > p^{1/4} STRICTLY**;
  the saving → 0 as H ↓ p^{1/4}. *This is the named SOTA in the prompt and it is VACUOUS at the barrier by its own hypothesis.*
- **Bourgain–Garaev (2009)**: limiting iteration at H ~ p^{1/4} gives only H^{1−175/9437184} = H^{0.99998} (saving ≈ 1.85×10⁻⁵).
- **BGK (Bourgain–Glibichuk–Konyagin 2006)**: nontrivial for any H > p^ε, but the saving β(ε) is ineffective and → 0 as ε → 0.
- **Heath-Brown–Konyagin (2000, Stepanov)** & **Garcia–Voloch**: intersection/energy facts |G∩(G+μ)| ≤ 4|G|^{2/3},
  |Γ+Γ| ≫ |Γ|^{3/2} — incidence/energy, not √-cancellation char sums; feed char sums only with a √-loss and only above p^{1/4}.
- **Shkredov / Macourt–Shkredov–Shparlinski**: shifted multiplicative energy E_×(Γ+a) ≪ |Γ|² log|Γ| — *exactly our measured
  object* (confirms 1+μ_n is near-Sidon) but yields a char-sum bound that is non-vacuous only for |H| comfortably above p^{1/4}.
- **Konyagin–Shparlinski / Shparlinski**: nontrivial subgroup sums for |H| ≫ p^{3/8}, p^{3/7} — far above the barrier.
- **Karatsuba's method / Bourgain–Garaev double sums**: require a *second* set (bilinear N^ε ≤ q ≤ N^{2−ε}); they do not
  apply to a single thin subgroup at the barrier and are in the same BGK–di Benedetto lineage (no separate exponent).

**Is the Paley Graph Conjecture proven anywhere relevant?** **No, not at or below |H| = p^{1/4}.** It is proven only:
under small-doubling / structure hypotheses (Shkredov, Hanson) that an unstructured subgroup does not satisfy; in
many-variable extensions (Bourgain, k ≥ C/δ variables); and the clique/Ramanujan improvements (Hanson–Petridis 2019,
arXiv:1905.09134, clique ≤ √(p/2)+1) live at |H| = (p−1)/2 (β = 2) and give **no** char-sum bound at β = 4. The single-set
double-sum Paley Graph Conjecture is OPEN for density δ ≤ 1/2 and ~25 years old.

**Bottom line of §2:** the target √(n log m) (exponent 1/2) is a **full half-power of n below** every published unconditional
bound at β = 4. The shifted framing has **no secret better SOTA** than the additive Gauss-period BGK — they are the same wall.

---

## 3. The 2-power-specific leads — any genuine traction?

Three structural handles unique to the 2-power tower were pushed. **All are exact and verified; none reduces the sum.**

**(a) Dyadic / squaring recursion.** From −1 ∈ μ_n and (1−ζ²) = (1−ζ)(1+ζ) under the 2-to-1 squaring push-forward:
`Σ_{ζ∈μ_n} χ(1−ζ)χ(1+ζ) = 2·S_{n/2}(χ)` — **exact** (independently re-verified this session, residual ≤ 6×10⁻⁸ across
n = 4…64; see /tmp/prizepaper/confirm_headline.py). Fatal flaw: it converts a level-(n/2) sum into a level-n *bilinear
correlation of two different sums* (at +1 and −1). The only bound for the LHS is Cauchy–Schwarz
≤ √(Σ|χ(1−ζ)|²)·√(Σ|χ(1+ζ)|²) = n, giving the trivial |S_{n/2}| ≤ n/2. The recursion **points the wrong way** (descends
into a larger object) and has no lower-bound coupling to drive a descent. In the additive coset split A_n = A_{n/2} + B,
the two cosets are orthogonal **only in the L²-average** over χ (E|A_n|² ≈ n, = Parseval, the known/easy direction); at the
**worst-case χ they phase-align (measured cos ≈ +1.0)**, so the max obeys only the triangle inequality with per-level
factor ≈ 2 (→ trivial n), not √2 (the √-law). This is the identical multiplicative-loss wall already documented for the
additive bilinear tower.

**(b) Stepanov in shifted coordinates.** The points {1+ζ} are the n distinct **simple** roots of (X−1)^n − 1 (squarefree:
value −1 at X = 1). Exact mod-p computation of the order-M Hasse-vanishing conditions gives **degeneracy exactly 0
(rank = M|V|) for M = 2,3,4** — the conditions are full-rank, so deg ≥ M|V| is forced → trivial/circular. Contrast verified:
the *additive* representation set carries TWO relations (both x^n=1 and (c−x)^n=1), producing a genuine order-2 collapse
Q = (c−X)^{n+1}+X^{n+1}−c; the shifted **sum** set has only ONE relation (the norm ∏(1+ζ) = ±n), so the saving mechanism is
structurally absent. This is strictly worse than the additive single-poly Stepanov (already vacuous, n^{5/4} at β = 4).

**(c) Low-genus / Weil curve.** The associated curve {x^n = 1, y^m = 1+x} has y-degree m ~ 2^128 (the worst χ is generic
full-order), hence genus ~ nm/2; Weil/Stepanov give |S| ≤ C·m·√p — vacuous, and the m-dependence **is** the Burgess wall.
The structural reason: μ_n is **0-dimensional** with only n = p^{1/4} points; √p = n² is exactly p^{1/4}-too-big to land below
n. Weil needs a positive-dimensional family; a pure subgroup has none. This is precisely *why* Burgess is a barrier.

**Verdict on §3:** the 2-power structure yields clean exact algebra (one genuinely-new, possibly-underused identity in (a)),
but **every route reduces to a trivial bound, a same-hardness circular object, or a dimensionally-vacuous Weil estimate.**
The deep object the bound actually requires — the k-fold multiplicative energy J_k(1+μ_n) ~ k!·N^k at depth k ~ log p —
**empirically EXPLODES** (measured ratio J_k/(k!N^k): 1.0, 0.98, 1.02, 1.20, 1.81, 3.69, 9.6, 28.1 for k = 1…8 at μ = 5),
because the exact global norm relation ∏(1+ζ) = ±n and its sub-products make the high multiplicative moments non-random.
The order-2 energy is already at the Sidon minimum (no lever left), and the minimality does **not** propagate to the depth
that matters. This is the same "2-power norm-tower / deep char-p moment at r ≍ log m" wall recorded across the #407/#389 memory.

---

## 4. HONEST BOTTOM LINE

**The shifted-subgroup / Paley framing opened NO unconditional crack. It is the same Burgess-barrier wall as the additive
M(n) — stated plainly: two names for one open object.**

- **Same magnitude (re-verified this session).** On the same μ_n at β = 4, exact max_χ|S| = 3.00, 6.99, 14.50, 25.36, 43.47
  for n = 4…64; the dual additive Gauss period M(n) tracks within ~10% (ratio M/S ≈ 1.31 → 0.91, crossing 1). The shifted
  sum is **not structurally smaller** — for n ≥ 16 it is marginally *larger*.
- **Ratio to target climbs past √2 in reach.** max_χ|S| / √(n log m) = 0.74, 0.99, 1.26, 1.39, 1.54 (monotone increasing
  through n = 64). This is a finite-size / 2-adically-structured-prime artifact (Fermat-type p = n^4 + small), **not** a
  refutation of the conjecture, but it shows **no clean sub-√2 cancellation is observable** at accessible scale — consistent
  with the worst case being genuinely hard rather than sitting at the √-floor.
- **The conjecture is plausibly TRUE but tight** (ratio ≈ 1 with slow log growth), which is exactly why it resists an easy
  unconditional proof. The exact Fourier duality S(χ) = Ḡ(χ)^{−1} Σ_t χ̄(t) e_p(t) η(t) is real but its quantitative
  transfer is √p-lossy; only the worst-case alignment (confirmed) ties S and M, and that alignment is what blocks any easier route.
- **LARP flags raised and cleared.** (i) Any claim that Karatsuba / Bourgain–Garaev / Shkredov / di Benedetto "apply" at
  β = 4 to give √(n log m) is FALSE — all require |H| strictly above p^{1/4}. (ii) A mid-probe false-positive (random
  character sampling made S look like n^{0.46}, sub-√n) was caught and killed by exhaustive enumeration: **the worst χ is
  trivial on μ_n (order exactly m = (p−1)/n), a measure-zero family random sampling misses** — always enumerate exactly. No
  closure is claimed; no Lean lemma is dischargeable from this cone; **no git commit made.**
- **Net scientific value:** a *literature-confirmation negative result* that rules out "the shifted framing has secretly
  better SOTA," plus a precise localization of the obstruction (the high-order multiplicative norm tower J_k at k ~ log p,
  NOT a lack of order-2 cancellation), plus the exact identities E_×(1+μ_n) = 2N²−N and Σχ(1−ζ)χ(1+ζ) = 2S_{n/2}(χ).

---

## Executive Summary

- **Best lead: NONE crosses Burgess.** Highest residual interest is the sum-product angle's exact fact
  **E_×(1+μ_n) = 2N²−N** (1+μ_n is multiplicatively Sidon, order-2 energy already at its minimum) and the 2-power squaring
  identity **Σ_{ζ∈μ_n} χ(1−ζ)χ(1+ζ) = 2·S_{n/2}(χ)** — both exact, both reusable, **neither yields a bound** (the squaring
  identity descends the wrong way; the Sidon minimality does not propagate to the depth k ~ log p that matters, where the
  energy J_k explodes 28× by k = 8 due to the exact norm relation ∏(1+ζ) = ±n).
- **Literature SOTA:** for Σ_{x∈H}χ(x+a) at |H| ~ p^{1/4}, the best explicit exponent is di Benedetto et al. (2020)
  **H^{1−31/2880} = H^{0.98924}, valid only for H > p^{1/4} (vacuous at the barrier)**; at exactly p^{1/4} only Bourgain–Garaev
  H^{0.99998} survives. The shifted framing is the **Fourier dual** of the additive subgroup sum and has **no better exponent**.
  The **Paley Graph Conjecture is OPEN for density ≤ 1/2** and proven nowhere relevant to an unstructured subgroup at β = 4.
- **Crosses Burgess? NO** — by any angle, unconditionally, even the weak "beat n^{0.989}" bar. The shifted/Paley framing is
  the **same Burgess-barrier wall** as the additive Gauss period M(n); it is structurally restricted (worst χ trivial on μ_n)
  but the restriction confers **no size advantage**. The needed √(n log m) is a full half-power of n below all known bounds.

*Synthesis file: /tmp/prizepaper/PALEY_SHIFTED_SUM_ASSAULT.md. Re-verification: /tmp/prizepaper/confirm_headline.py
(exact max_χ|S| via FFT-of-dlog-histogram + squaring identity check, residual ≤ 6e-8). No git commit.*
