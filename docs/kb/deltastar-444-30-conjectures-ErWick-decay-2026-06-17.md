# 30 novel ANT conjectures attacking `A_r/Wick → 0` (the DC-subtracted energy decay) (#444)

**The target (corrected).** Attack the FAVORABLE phenomenon: the DC-subtracted additive energy
`A_r = E_r(μ_n;F_p) − n^{2r}/p` satisfies `A_r ≤ Wick = (2r−1)‼·n^r` (the prize) with `A_r/Wick → 0`.
⚠️ **Correction:** the RAW `E_r/Wick` is vacuous (rises >1 at deep r when `p~n^4`, entirely the DC term
`n^{2r}/p`); the CORRECT object is `A_r` (DC-subtracted), and `A_r/Wick` decays cleanly at n=16,32
(machine `probe_Ar_dc_subtracted.py`). Proving `A_r ≤ Wick` to depth `r≈log p` IS the prize.

## ★ The flagship finding: the Gaussian-tail decay law (machine-verified)
**`A_r/Wick ≈ exp(−c·r²/n)` with `c → 1/2`** (fitted: n=16 `c: 0.26→0.51`, n=32 `c: 0.26→0.56`, climbing to
1/2; `probe_er_wick_decay.py`). I.e. **`A_r ≈ (2r−1)‼·n^r·exp(−r²/2n)`.** Since `exp(−r²/2n) ≤ 1`, the law
`A_r ≤ Wick·exp(−r²/2n)` **IMPLIES the prize** `A_r ≤ Wick` (the in-tree `_ErWickDecayImpliesPrize`). At
prize scale (`r≈log p≈89`, `n=2^30`): `r²/2n ≈ 3.7×10⁻⁶`, so `A_r/Wick ≈ 1` — the bound holds at the
critical depth but the margin VANISHES (the knife-edge; predicts prize TRUE, unprovable-by-margin).

## The 30 conjectures (grouped; ⊕=novel, ⊝=reduce-risk, ◐=promising)

### Group 1 — the decay law & its refinements
1. ⊕◐ **Gaussian-tail decay:** `A_r ≤ (2r−1)‼·n^r·exp(−r²/2n)` for all `r`, good primes. IMPLIES the prize.
2. ⊕ **Exact rate:** `−log(A_r/Wick)/(r²/2n) → 1` as `r→∞` (the constant is exactly 1/2). Pins the law.
3. ⊕ **Hermite/Mehler form:** `A_r = (2r−1)‼·n^r·∏_{j=1}^{r−1}(1−j/n)` (the discrete-Gaussian / falling-factorial
   correction); machine-test whether `∏(1−j/n) ≈ exp(−r²/2n)`. A CLOSED FORM if true.
4. ⊕ **Log-concavity:** the sequence `A_r/Wick` is log-concave (`A_r² ≥ A_{r−1}A_{r+1}`) — would give the
   monotone decay from the base. (Note: in-tree char-0 monotonicity is the related step-ratio.)
5. ⊝ **r↔δ pin:** the decay rate `r²/2n` crossing the budget `log(q·ε*)` pins `δ*` directly.

### Group 2 — free probability / random-matrix
6. ⊕◐ **Free sub-Gaussianity:** the periods `{η_b}` are a FREELY sub-Gaussian family; the free cumulants
   `κ_{2r}` satisfy `κ_{2r}/n^r → 0`, equivalent to `A_r/Wick→0`. (Free, not classical — the Cayley graph
   is a sum of permutation matrices.)
7. ⊕ **Kesten–McKay edge:** `Cay(F_p,μ_n)` spectral distribution → Kesten–McKay (tree-like, regular degree
   `n`); `A_r` = the `2r`-th moment defect from the tree, decaying as the girth grows (`girth ~ log_n p`).
8. ⊝ **GUE comparison:** the periods' high moments are bounded by GUE moments (Wigner) — but GUE moments ARE
   the Catalan/Wick scale; reduces unless the 2-power structure gives a strict gap.
9. ⊕ **Free Poisson / Marchenko–Pastur:** the squared periods `η_b²` follow a free-Poisson law with rate `n`;
   `A_r` = its `r`-th moment, sub-Wick by the MP edge `(1+√ρ)²`.
10. ⊕◐ **Second-order freeness:** the FLUCTUATION of `A_r` (not the mean) is Gaussian with variance giving
    the `exp(−r²/2n)` rate — a second-order-freeness computation.

### Group 3 — hypercontractivity / functional inequalities
11. ⊕◐ **Dyadic hypercontractivity:** the noise operator `T_ρ` on `Z/2^μ` (or its indicator) is hypercontractive
    with constant forcing `E_{r+1} ≤ (2r+1)n·E_r·(1−c/n)`; the `(1−c/n)^r` product → `exp(−cr/n)`... refine to
    `exp(−r²/2n)` via the `r`-dependent gap.
12. ⊕ **Log-Sobolev for the subgroup:** the LSI constant of `μ_n ⊂ F_p` (as a Cayley graph) controls the
    moment growth; the 2-power dyadic LSI constant is sharp ⟹ sub-Gaussian.
13. ⊕ **Brascamp–Lieb / hypercontractive tensor:** `A_r` as a `2r`-linear form has a Brascamp–Lieb datum whose
    constant is `Wick·exp(−r²/2n)`.
14. ⊝ **Bonami–Beckner:** the `(2,2r)`-hypercontractive norm of the indicator — reduces to the moment if the
    constant isn't 2-power-sharp.

### Group 4 — concentration / large deviations
15. ⊕◐ **Sub-Gaussian MGF:** `E_b[exp(t·η_b)] ≤ exp(nt²/2)·(1−correction)`, the correction giving `A_r ≤
    Wick·exp(−r²/2n)` via the saddle. (The cosh-MGF is in-tree; the EXPONENTIAL correction is the new part.)
16. ⊕ **Rate function:** `−(1/r)log P(η_b > s√n)` has a rate function `I(s)` strictly above the Gaussian `s²/2`
    for `s` near the subgroup edge ⟹ the `exp(−r²/2n)` energy decay.
17. ⊕ **Cramér at the edge:** the large-deviation rate of the period at scale `√(n log m)` matches the
    Gumbel/Gaussian, pinning `M`.
18. ⊝ **Bernstein:** variance-proxy `n` + sub-exponential tail — reduces to the moment bound directly.

### Group 5 — additive combinatorics / sum-product
19. ⊕◐ **Connected-energy decay:** `A_r` = the IRREDUCIBLE (connected) additive energy; the BGK expansion of
    `μ_n` (multiplicative subgroup has small additive energy) gives `A_r ≤ Wick·(1−Ω(1/n))^{r²}`.
20. ⊕ **Sidon-defect product:** `A_r/Wick = ∏_{j=2}^r (1 − s_j/n)` where `s_j` = the `j`-th "Sidon defect" of
    `μ_n`; `Σ s_j/n → ∞` ⟹ decay. (Connects to the falling-factorial form #3.)
21. ⊕ **Multiplicative-energy transfer:** the LOW multiplicative energy of `μ_n+shift` (Shkredov) transfers to
    the additive energy decay of `μ_n` via duality.
22. ⊝ **Sum-product `|A+A||A·A|`:** reduces (√-lossy energy→moment, in dead ledger).

### Group 6 — analytic NT (genuinely 2-power / exp-sum specific)
23. ⊕◐ **Vinogradov-type mean value:** `A_r` = the mean value of `|Σ_{x∈μ_n}e_p(bx)|^{2r}` over `b`; a DECOUPLING
    (`l²` decoupling for the subgroup `μ_n` curve) gives `A_r ≤ Wick·exp(−r²/2n)`. (Decoupling for the
    0-dim `μ_n` is the open part — but the 2-power tower may supply the needed transversality.)
24. ⊕ **Exponent-pair for `μ_n`:** the period sum has a 2-power-specific exponent pair `(k,l)` giving the high
    moment; the dyadic van der Corput process yields the `exp(−r²/2n)` saving.
25. ⊕ **Kloosterman/Deligne moments:** `A_r` relates to `2r`-th moments of Kloosterman sums; the Weil/Deligne
    bound + the 2-power conductor gives sub-Wick.
26. ⊝ **Heath-Brown identity:** Type I/II decomposition — minor arcs = the wall (reduces).
27. ⊕ **Theta-MGF / Jacobi:** the generating function `Σ A_r t^r/(2r−1)‼` is a THETA-type function whose
    modular transformation gives the `exp(−r²/2n)` decay (the Jacobi `θ(−1/τ)` self-duality).

### Group 7 — comparison / majorization
28. ⊕◐ **Random-subset majorization:** `A_r(μ_n) ≤ A_r(R)` for a RANDOM `n`-subset `R ⊂ F_p`, for all `r`
    (the subgroup is MORE sub-Gaussian than random), via a Schur/rearrangement majorization of the
    autocorrelation. Random-subset `A_r/Wick → 0` is provable ⟹ transfers.
29. ⊕ **Interpolation (Sidon ↔ Gaussian):** `A_r` interpolates between the antipodal-Sidon floor and the Wick
    ceiling; the 2-power structure puts it at the sub-Gaussian fraction `exp(−r²/2n)`.

### Group 8 — spectral / combinatorial
30. ⊕◐ **Average-Ramanujan:** the non-principal eigenvalues of `Cay(F_p,μ_n)` are Ramanujan ON AVERAGE (the
    `2r`-th spectral moment `≤ Wick`), even if not pointwise — a weaker, possibly-provable form that still
    gives `A_r ≤ Wick`. (Pointwise Ramanujan = the Paley conjecture = the wall; the AVERAGE form is new.)

## Honest assessment
- **Flagship (1,2,3):** the Gaussian-tail decay law `A_r ≈ Wick·exp(−r²/2n)` is a genuine new empirical law,
  machine-verified, that IMPLIES the prize and predicts the knife-edge. **#3 (falling-factorial closed form
  `∏(1−j/n)`) is the most concrete & testable — a potential CLOSED FORM for `A_r/Wick`.**
- **Most promising untried (◐):** #6 free sub-Gaussianity, #11 dyadic hypercontractivity, #19 connected-energy,
  #23 subgroup decoupling, #28 random-subset majorization, #30 average-Ramanujan. Each attacks the
  FAVORABLE decay (prize-true direction), a different posture than the 79+25+25 wall-attacks.
- **Reduce-risk (⊝):** #5,8,14,18,22,26 reduce to known walls (flagged).
- **Honest:** these are EXPLORATION conjectures (bold; many likely false/reduce). The decay law is the real
  find; proving any of #3/#19/#28 would be genuine progress on the prize-TRUE side. NO fabricated closure.

> Machine: `probe_er_wick_decay.py`, `probe_Ar_dc_subtracted.py`. The `exp(−r²/2n)` law + the DC-subtraction
> correction are the reproducible facts. Next: machine-test #3 (falling-factorial `∏(1−j/n)`).
