# Verdict: candidate BEAT of di Benedetto et al (arXiv:2003.06165) for the RS proximity-gap prize (#444)

**Status: CONFIRMED-BEAT (with one honest caveat stated in §5).**
**Date: 2026-06-15. Verified directly against the arXiv LaTeX e-print source `/tmp/ExpSum-IntSubgr.tex` (single-file `ExpSum-IntSubgr.tex`, 6 authors). All exponents re-derived from scratch (no reliance on prior summaries).**

Paper: V. M. Di Benedetto, M. Z. Garaev, V. C. Garcia, D. Gonzalez-Sanchez, I. E. Shparlinski, C. A. Trujillo,
"New estimates for exponential sums over multiplicative subgroups and intervals in prime fields" (13 Mar 2020).

---

## 1. Is the substitution VALID? (T2, T3 = additive energy of H itself, modular, no coupling)

**YES — the substitution is direct and valid.** The energy object is unambiguously the additive energy of the
subgroup H *itself*, with all variables ranging over H. Decisive quotes, verbatim from the source:

**Definition (eq. `defTm`, lines 203–207):** T_m(H) is "the number of solutions of the congruence
> h_1 + ... + h_m ≡ h_{m+1} + ... + h_{2m} (mod p),  h_1, ..., h_{2m} ∈ H."

All 2m variables lie in H. There is NO sumset X = H+H+H, NO coupled (X,Y,Z) configuration, NO difference set
in the *definition* of the energy. T_m(H) is exactly the m-th additive energy of H.

**The two energy lemmas (verbatim):**
- Lemma `lem: T2 energy`: "Let H < √p. Then T_2(H) ≪ H^{49/20} log^{1/5} H."
- Lemma `lem:tri-sum-energy`: "Let H < √p. Then T_3(H) ≪ H^4 log H."
(both attributed to Murphy–Rudnev–Shkredov–Shteinikov, [Thm 3 and Cor 7]{MRSS2017}.)

**Where the energies enter the proof — the make-or-break step (verbatim, lines ~455–465):**
After a dyadic pigeonhole producing G_1 ⊆ H^3, the paper sets X = {x_1+x_2+x_3 : (x_1,x_2,x_3) ∈ G_1}\{0} and J(x) =
#representations of x as such a sum, then states:
> "Clearly Σ_x J(x) = |G_1| and **Σ_x J(x)² ≤ T_3(H)**.
> Applying the Cauchy–Schwarz inequality ... by Lemma [lem:tri-sum-energy] ... |X∪{0}| ≥ |G_1|²/T_3(H) ≳ H²Δ⁶/Δ_1²."

The step `Σ_x J(x)² ≤ T_3(H)` is a **subset inequality**: Σ J² counts pairs of triples in G_1×G_1 with equal sum;
since G_1 ⊆ H^3, dropping the G_1 restriction to all of H^3 gives exactly T_3(H) and can only increase the count.
This is valid for ANY subgroup, and for H = μ_n the right-hand side is **exactly** the machine-verified Sidon-floor
full-group energy T_3(μ_n) = 15n³−45n²+40n (leading order n³). The same pattern recurs identically:
- |Y|: `eq: large Y`, again G_2 ⊆ H^3, bounded by **T_3(H)**.
- |Z|: `eq: large Z`, G_3 ⊆ H^2 (a *difference* set), bounded by **T_2(H)** (Lemma `lem: T2 energy`).

In all three uses the energy is of H itself. The sumset/difference images X, Y, Z enter the rest of the proof
**only through their cardinalities** |X|, |Y|, |Z| (which the energy bounds lower-bound), and through the trilinear
Lemma which is stated for *arbitrary* sets. **No energy of a sumset is ever used. No coupling. The substitution
T_3 → 15n³−... and T_2 → 3n²−3n is direct.**

Adversarial sub-checks (all passed):
- **Log factors:** μ_n energies have NO log factor and strictly smaller power. Since |X| ≥ |G_1|²/T_m, a smaller T_m
  only *strengthens* the bound. The log loss in the general lemmas is harmless to the substitution.
- **Lower-order terms** (−3n in T_2; −45n²+40n in T_3): they shrink the energy further ⇒ only strengthen. Leading
  powers t_2 = 2, t_3 = 3 govern the asymptotic exponent.
- **Antipodal collapse (−1 ∈ μ_n):** −1 inflates the x=0 fiber J(0), but J(0)² ≤ T_3 still holds and the {0}
  removal costs ≤ 1 element, negligible vs H²Δ⁶/Δ_1². No collapse.

---

## 2. Exact improved exponent + threshold (confirmed/corrected)

The exponent formula is **modular** and was re-derived symbolically from the source. Writing T_3 ~ H^{t3}, T_2 ~ H^{t2}:

  |X| ~ H^{6−t3}·(Δ-part)   |Y| ~ H^{6−t3}·(Δ-part)   |Z| ~ H^{4−t2}·(Δ-part)
  Trilinear comparison (verbatim, after raising to the 4th power):  **|X|·|Y|·|Z|^{1/2}·Δ_3⁴ ≪ p**
  (the |Z|^{1/2} arises from the trilinear |Z|^{7/8}: (1−7/8)·4 = 1/2 — verified.)

  ⇒  **Hexp = (6−t3) + (6−t3) + ½(4−t2)**

The Δ-collapse to Δ⁷² (`eq: penult`) uses ONLY the dyadic relations Δ_1 ≳ Δ³, Δ_2 ≳ Δ_1³, Δ_3 ≳ Δ_2²
(eqs. Set G1/G2/G3): Δ⁶·(Δ³)⁴·(Δ¹⁸)³ = Δ^{6+12+54} = Δ⁷². **This exponent 72 is energy-INDEPENDENT** — it is the
same for the general and the 2-power cases. The p-power is likewise fixed: p ≳ H^{Hexp}·Δ⁷² ⇒ **Δ ≲ p^{1/72} H^{−Hexp/72}**,
so |S_a(H)| = HΔ ≲ p^{1/72} H^{1−Hexp/72}. At H > p^{1/4}, p^{1/72} ≤ H^{4/72}, giving |S_a(H)| ≲ H^{1−(Hexp−4)/72}.

| case | (t2, t3) | Hexp | full bound | saving s=(Hexp−4)/72 | exponent at H>p^{1/4} | threshold H>p^θ |
|---|---|---|---|---|---|---|
| **General (di Benedetto)** | (49/20, 4) | 191/40 = 4.775 | H^{2689/2880}p^{1/72} | **31/2880 ≈ 0.01076** | **2849/2880 ≈ 0.98924** | θ>40/191 ≈ 0.2094 |
| **2-power μ_n (Sidon floor)** | (2, 3) | **7** | H^{65/72}p^{1/72} | **1/24 ≈ 0.04167** | **23/24 ≈ 0.95833** | θ>1/7 ≈ 0.14286 |

- **General case reproduced EXACTLY:** Hexp = 191/40 ⇒ full exponent 2689/2880 (matches Theorem `thm:SingleSum`
  verbatim) and saving 31/2880 at H>p^{1/4} (matches "in particular H^{1−31/2880}" verbatim). The reproduction of the
  paper's own published number from the modular formula is the strongest internal consistency check.
- **2-power case:** Hexp = 7, exponent **23/24 ≈ 0.9583**, threshold **H > p^{1/7}**.

**Does it beat 0.9892 (= 1 − 31/2880)?  YES.** 0.9583 < 0.9892: the 2-power saving 1/24 is ≈ 3.87× the general
31/2880. The improvement is genuine, not marginal.

**Does it cover the prize regime?  YES, qualitatively.** The prize subgroup μ_n has |H| = n ~ p^{1/β} with β ≈ 4–5,
i.e. θ ≈ 0.20–0.25. The 2-power threshold θ > 1/7 ≈ 0.143 is *below* the prize θ, so the bound is non-trivial there,
**whereas di Benedetto's stated theorem requires H > p^{1/4} (θ > 0.25) and its argument's own threshold θ > 40/191
≈ 0.209 sits right at the edge of / above the prize regime.** So in the prize window the 2-power specialization gives
a non-trivial cancellation where the general theorem is at or past its boundary.

---

## 3. Obstructions found?

**NONE that invalidate the substitution or the exponent.** All five candidate obstructions were probed and refuted:

1. **Sumset-vs-set mismatch:** REFUTED. The energy is T_m(H) of H itself (eq. `defTm`); the Σ J² ≤ T_m(H) step is a
   valid subset inequality (G_i ⊆ H^m). Sumsets X,Y,Z enter only via cardinality and via the arbitrary-set trilinear
   lemma — never via their own energy.
2. **Descent re-introducing general energy:** REFUTED. There are exactly three energy uses (|X|,|Y|,|Z|), each is
   T_m(H) of the subgroup; the recursion re-applies the *same* T_m(H), never a sumset energy. The Δ⁷² collapse is
   energy-independent.
3. **t3 floor coupling:** REFUTED. t_3 = 3 is the genuine leading order of T_3(μ_n) (machine-verified exact 15n³−...),
   not a coupled artifact; it enters linearly and uncoupled in Hexp = 2(6−t3)+½(4−t2).
4. **Antipodal collapse:** REFUTED (see §1). −1 ∈ μ_n does not break the |X| nontriviality.
5. **Second origin of the p^{1/4} barrier:** REFUTED as a hard floor. The "H > p^{1/4}" in di Benedetto's *statement*
   is the nontriviality threshold for the *general* 31/2880 saving, NOT an independent structural barrier. The trilinear
   p^{1/4} *prefactor* is energy-independent and enters identically in both cases (it produces the common p^{1/72} after
   the 4th-power raising). The single genuine threshold is θ > 1/Hexp, which the 2-power case lowers to 1/7.

---

## 4. Can the trilinear prefactor also be improved (combined gain)?

**Not within this argument, and not claimed.** The trilinear Lemma (`tri`, = Petridis–Shparlinski [Thm 1.1]{PS2019},
"Bounds of trilinear and quadrilinear exponential sums", arXiv:1604.08469), quoted verbatim:
> "For any sets X, Y, Z ⊆ F_p* and any complex α_x,β_y,γ_z with |·|≤1:
>  Σ_{x,y,z} α_x β_y γ_z e_p(axyz) ≪ p^{1/4} |X|^{3/4} |Y|^{3/4} |Z|^{7/8}."

This is an **arbitrary-set** bound; its p^{1/4} is energy-independent and the Sidon structure of μ_n does NOT enter it.
Crucially, the sets X, Y, Z to which it is applied are **sumset/difference images** of subgroup triples/pairs (X = sums
of three μ_n-elements, Z = differences of two), NOT μ_n itself — so even a hypothetical subgroup-specialized trilinear
bound would not directly apply to X, Y, Z without a separate structural input on these sumsets. **Conservative position:
the prefactor is taken as-is; no combined gain is claimed.** The entire beat comes from the energy substitution alone.
(A trilinear improvement, if found for these specific sumsets, would *add* to the gain — but it is open and not part of
this verified result.)

---

## 5. FINAL VERDICT

**CONFIRMED-BEAT.** The substitution of μ_n's Sidon-floor additive energies (t_2 = 2, t_3 = 3, leading order, exact and
p-invariant) into the di Benedetto et al single-sum argument is **valid and direct** — the energies are of the subgroup H
itself (eq. `defTm`, the Σ J² ≤ T_m(H) subset step), with no sumset coupling, no descent re-introduction of general
energy, and no antipodal or second-barrier obstruction. The modular exponent formula Hexp = 2(6−t3) + ½(4−t2) was
re-derived from the source and **reproduces the paper's own published 2689/2880 / 31/2880 exactly** in the general case,
which certifies the derivation.

**What we can claim, precisely and conservatively:**
> For the 2-power subgroup μ_n ⊂ F_p* (n = 2^μ-th roots of unity, |μ_n| = n), the di Benedetto et al argument,
> specialized via the exact Sidon-floor energies T_2(μ_n) = 3n²−3n, T_3(μ_n) = 15n³−45n²+40n, yields
>     max_{(a,p)=1} |Σ_{x∈μ_n} e_p(ax)|  ≲  |μ_n|^{65/72} p^{1/72}  =  |μ_n|^{1 − 1/24} p^{1/72},
> non-trivial for |μ_n| > p^{1/7}; in particular for |μ_n| > p^{1/4} this is ≲ |μ_n|^{23/24}.
> This improves the di Benedetto exponent from 1 − 31/2880 ≈ 0.9892 to 1 − 1/24 ≈ 0.9583 (saving ≈ 3.87× larger),
> and extends below the p^{1/4} threshold to p^{1/7}, into / through the prize regime θ ≈ 1/β (β ≈ 4–5) where the
> general theorem is at or past its boundary.

**Caveats / what remains open (honesty):**
- The result is the **asymptotic leading-order** specialization: t_2 = 2, t_3 = 3 are the leading powers; the exact
  closed forms only strengthen the bound (smaller energy ⇒ stronger), so the asymptotic exponent is safe, but a fully
  rigorous writeup should carry the explicit constants/log-free forms through (straightforward; only improves things).
- **This is NOT a prize closure.** 0.9583 ≫ 1/2. The prize needs an exponent giving M(n) ≤ C√(n log m), i.e. a saving
  of order 1/2 (exponent → 1/2), not 1/24. The beat is an improvement on the *closeness* SOTA in the prize regime, not
  the wall itself. Per the project's standing meta-result, reaching exponent 1/2 at β ≈ 4 is the BGK/BCHKS wall and is
  untouched by this energy substitution (the saving 1/24 is energy-driven and bounded by the Δ⁷² descent, which caps the
  attainable exponent regardless of how small the energy is — even T_m at the absolute Sidon floor gives only Hexp = 7).
- The Petridis–Shparlinski trilinear bound was verified by its **verbatim quotation inside di Benedetto's Lemma `tri`
  (cited [Theorem 1.1]{PS2019})** and the matching arXiv:1604.08469 title; the standalone PS abstract page does not carry
  the theorem body, but the load-bearing statement is the one used in 2003.06165, which is what we verified.

**Bottom line:** a genuine, source-verified improvement on the state-of-the-art single-sum cancellation for 2-power
subgroups in the prize regime — exponent 23/24 (saving 1/24) valid for |H| > p^{1/7} — but firmly on the high side of
the wall, not a path to the prize.
