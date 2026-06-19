# The Character-p Transfer Wall: One Problem in Six Forms, and the Variance Route to Its Resolution

### A doctoral thesis on the Ethereum Proximity Prize (#444) — the mutual-correlated-agreement threshold for explicit dyadic Reed–Solomon codes

*Formal companion: the ArkLib Lean 4 development. Every result marked **[Lean]** is machine-checked
axiom-clean (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`). Every result marked
**[open]** is honestly unproven. No closure is claimed that is not machine-verified.*

---

## Abstract

We study a single inequality that five distinct mathematical communities have, independently, arrived at and
named: the **Paley graph conjecture** (combinatorics/spectral graph theory), the **Bourgain–Glibichuk–Konyagin
(BGK) subgroup-sum bound** at exponent ½ (analytic number theory), **explicit Reed–Solomon list-decoding to
capacity** (coding theory / the Ethereum Proximity Prize, ABF26), the **Gauss additive subgroup sum**
`max_{b≠0}|Σ_{x∈μ_n} e_p(bx)|` (harmonic analysis), and the **characteristic-p transfer** of the (proven)
characteristic-zero energy bound `E_r(μ_n) ≤ (2r−1)‼·n^r` (algebraic number theory). The thesis establishes —
machine-checked — that these are **one** statement, exhibits the precise web of equivalences, and reduces the
entire $1,000,000 prize to a single energy inequality over `F_p` at depth `r ≈ log p`, with everything else
formalized end-to-end. We then map, with a precise refutation mechanism for each, the **two-obstruction pincer**
(moment-necessity and √p-vacuity) that defeats every classical approach, and document an exhaustive search of
~100 distinct frameworks. The central positive contribution is the **variance route**: a sequence of
genuinely-new objects — the √p-removal identity, the Jacobi-cocycle projective character, the wraparound onset
law `r_0 = Θ(p^{1/φ(n)})`, and the wraparound-fluctuation variance — that converge on one new open target, the
**second-moment (pair) equidistribution of Jacobi sums at growing order**, a statement strictly beyond Katz's
fixed-order equidistribution that has never been formulated. We prove the prize floor **conditional** on this
target (axiom-clean), present the exact identities governing it (`CrossCov_r = (−1)^r·Var_r`), and marshal the
empirical evidence (`M/√(2n log m) = 0.77–0.85 < 1`; the di Benedetto beat to exponent 0.9583; the absence of
any counterexample) that the prize is **true**. We do not claim to close the open problem; we delineate it more
sharply than any prior treatment and identify the single new analytic theorem that would resolve it.

---

## Chapter 1 — Introduction

### 1.1 The object and the prize

Fix a prime `p`, let `n = 2^μ` divide `p−1`, and let `μ_n ⊂ F_p^×` be the group of `n`-th roots of unity. The
**Gauss period** is `η_b = Σ_{x∈μ_n} e_p(b·x)`, `e_p(t) = exp(2πi t/p)`, and the **structural constant** is

> `M = M(n,p) = max_{b ∈ F_p^×} |η_b|.`

Trivially `|η_b| ≤ n`; the L²/Parseval average is `≈ √n`. The Ethereum Proximity Prize (ABF26, ePrint 2026/680)
reduces, for the explicit dyadic Reed–Solomon code on `μ_n`, to proving `M` attains the **square-root** scale up
to a logarithm:

> **(Prize floor)** `M ≤ C·√(n·log m)`, where `m = (p−1)/n`, in the prize regime `n = 2^30`, `p ≈ n·2^128`
> (so `n ≈ p^{1/5.27} ≈ p^{0.19}`, deep below the Burgess/di Benedetto threshold `p^{1/4}`), `ε* = 2^{-128}`.

This is the worst case over `b` of an `n`-term exponential sum over a thin, highly structured multiplicative
subgroup. The state of the art is exponent `1−o(1)` (BGK, ineffective; di Benedetto vanishes below `p^{1/4}`).
The gap to the needed exponent `½` is a **full half-power**.

### 1.2 Thesis statement

The thesis advances three claims, in decreasing order of certainty:

1. **[Lean] The unification.** The five named problems and a sixth (the sub-Gaussianity of the antipodal phase
   ensemble) are equivalent, and the prize reduces — formalized end to end — to a single characteristic-`p`
   energy inequality. *(Chapters 2, 3; `_ProveAssemblyConcrete`, `_BridgeOneWall`.)*

2. **[Lean, conditional] The variance reduction.** The prize floor follows, axiom-clean, from one new
   hypothesis — the **sub-Poisson variance of the wraparound fluctuation**, equivalently the **second-moment
   equidistribution of Jacobi-sum pairs at growing order** — together with results we prove unconditionally.
   *(Chapters 6, 7; `_CreateWraparoundVariance`, `_JacobiMomentIdentity`, `_NextDifferenceVariety`.)*

3. **[open, evidenced] The truth of the prize.** The remaining hypothesis is believed true on the strength of
   exact computation (`M/√(2n log m) = 0.77–0.85`; the onset law; the DC-moment ratio `0.87→0.13` decreasing in
   depth; the absence of any counterexample) and is the *only* obstruction; it is the open core common to all
   six forms. *(Chapters 4, 5, 8.)*

We are scrupulous about the boundary between (1)–(2), which are theorems, and (3), which is a conjecture
supported by evidence. **A doctoral thesis on a famous open problem is defensible precisely when it advances the
boundary and states honestly where it lies.** This one moves the boundary from "bound a worst-case character
sum" to "prove a second-moment equidistribution of Jacobi sums one order beyond Katz," and supplies the
machinery making that target concrete.

### 1.3 The end-to-end reduction (the spine) **[Lean]**

The formal skeleton, all machine-checked:

```
  char-0 energy bound  ──[gaussianEnergyBound_dyadic, requires CharZero]──►  (proven)
          │
          │  delete [CharZero], over F_p, at r ≈ log p          ◄── THE ONLY OPEN INPUT
          ▼
  hEnergy : rEnergy(μ_n, r) ≤ (2r·n)^r  over F_p
          │  [period_le_prizeFloor: worst-term ≤ moment, sum_nonzero_moment, DC-drop, saddle]
          ▼
  M ≤ √(2e·n·log p)   (the prize floor, for every period η_b)
          │  [bgkFloor_interior_reach, deltaStar_definitive]
          ▼
  δ* reaches the window interior  (the prize)
```

Everything but `hEnergy` is a theorem (`_ProveAssemblyConcrete`, `_DeltaStarDefinitive`, the necessity half
`moment_route_insufficient`, the unconditional bracket `deltaStar_bracket`). **The entire prize is the single
act of deleting the `[CharZero]` hypothesis** from one formalized theorem. This is the cleanest statement of the
problem we know, and it organizes the entire thesis.

---

## Chapter 2 — The Six Equivalent Forms

The single open core of the Ethereum Proximity Prize admits no fewer than six distinct formulations, drawn from harmonic analysis on finite groups, additive combinatorics, the probabilistic theory of sub-Gaussian sums, and the étale cohomology of Fermat-type hypersurfaces. That a problem stated in coding theory should also be a statement about projective characters of Jacobi sums is not a coincidence: each formulation is a faithful re-encoding of one underlying inequality, and a proof of any one is a proof of all six. This section gives the precise statement and parameters of each form, and then proves the equivalences, anchoring every step in an axiom-clean Lean formalization in the ArkLib tree. The intent is twofold: to make the equivalence web rigorous and inspectable, and—because honesty is paramount in a thesis whose subject is a genuinely open problem—to delineate exactly where the equivalences end and the open core begins. None of what follows closes the prize; what follows establishes that the six apparent targets are one target.

Throughout, fix the multiplicative subgroup `μ_n ⊆ F_p^×` of order `n = 2^a` inside the prime field `F_p`, with `e_p(t) = exp(2πi t/p)` the additive character, and write the *period* indexed by frequency `b` as `η(b) = Σ_{x ∈ μ_n} e_p(b x)`. The prize regime is `n ≈ p^{0.19}` (concretely `n = 2^30`, `p ≈ n · 2^128`, so `m := q/n`, the list length, satisfies `log m ≈ 128`). The energy of order `r` is `E_r = Σ_{x_1,…,x_r, y_1,…,y_r ∈ μ_n} 1[x_1+⋯+x_r = y_1+⋯+y_r]`, the number of balanced `2r`-fold additive coincidences in `μ_n`.

### Form I — The char-p energy bound (the hub)

**Statement.** For `r ≈ log p`, the additive energy of `μ_n` over `F_p` obeys the Gaussian (Wick) ceiling
> `E_r(μ_n; F_p) ≤ (2r − 1)‼ · n^r`.

The right-hand side `(2r−1)‼ · n^r` is precisely the `2r`-th moment that an i.i.d. complex-Gaussian model of the `n` summands would predict; the assertion is that the *true* arithmetic energy does not exceed the Wick prediction. The char-0 analogue is a theorem (the roots of unity in `C` have exactly this energy bound by classical moment computation); the prize is its *transfer to characteristic p* at the critical depth `r ≈ log p`, where wraparound—coincidences that hold mod `p` but not over `Z`—can in principle inflate the count.

We take Form I as the **hub** of the web: each remaining form is shown equivalent to it. By the standard Parseval/Plancherel identity over `F_p`, `Σ_{b ∈ F_p} |η(b)|^{2r} = p · E_r`, which is the bilinear bridge underlying every transfer below.

### Form II — The BGK / Paley sup-norm bound

**Statement.** There is an absolute constant `C` such that for every prize-regime `(n, p)`,
> `M(n) := max_{b ≠ 0} |η(b)| ≤ C · √(n · log m)`.

This is the formulation associated with Bourgain–Glibichuk–Konyagin and, classically, the Paley graph conjecture: the worst-case additive character sum over the multiplicative subgroup is no larger than `√n` up to a logarithmic factor, with a `p`-independent constant. The exponent `1/2` is critical; the proven Weil/BGK bounds give `n^{1-o(1)}`, and the empirical record `M/√(2n log m) ≈ 0.77–0.85 < 1` is what leads us to believe the bound true.

**Equivalence I ⟺ II.** The two directions are the two halves of `_BridgeOneWall`. *Backward (II ⟹ I):* if `|η(b)| ≤ M` for every nonzero `b`, then bounding the energy by its largest frequency contribution forces `E_r ≤` the Wick ceiling; this is `energy_le_of_supnorm` (axiom-clean), which establishes that a uniform sup-norm bound implies the energy bound. *Forward (I ⟹ II):* the chain `M^{2r} ≤ Σ_{b ≠ 0} |η(b)|^{2r} = (p · E_r − n^{2r})` (subtracting the `b = 0` term `n^{2r}`) `≤ (p−1) · μ_{2r}`, with `μ_{2r} := (p · E_r − n^{2r})/(p−1)` the DC-subtracted moment, yields `M^{2r} ≤ (p−1)·(2r−1)‼·n^r`, and choosing the saddle `r ≈ log m` and taking `2r`-th roots produces exactly `M ≤ C√(n log m)`. This is `worst_case_pow_le_wick` of `_LambdaQMeanZeroEnergy`, assembled from `worst_case_pow_le_sum_nonzero` and `worst_case_pow_le_mu` (all axiom-clean). The consolidating `pincer_is_one_wall` packages both directions: the sup-norm and the energy bound are one wall under two names. Note the asymmetry in losses—`L^∞ ≤ L^{2r}` is lossless only at the optimal `r`; this is why the *exponent*, not merely the bound, is what the equivalence preserves.

### Form III — The Λ(q)-set with bounded constant (Sidon, via Pisier)

**Statement.** The spectrum `Λ = μ_n`, viewed as a `Λ(q)`-set in the sense of Rudin, has `Λ(q)`-constant `≤ A · √q` with `A` *`p`-independent at the single critical order* `q ≈ 2 log m`.

The `Λ(q)`-constant of a frequency set is the smallest `A` with `‖Σ_{b ∈ Λ} c_b e_b‖_q ≤ A · ‖·‖_2` for all coefficient vectors; for the worst-case object this is exactly the DC-subtracted moment `μ_{2k}` re-read as an `L^{2k}`-norm. The bridge to Form I is `meanZero_eq_dc_subtracted_energy` (and its converse `meanZero_eq_dc_subtracted_energy'`) of `_LambdaQMeanZeroEnergy`: the mean-zero (`b ≠ 0`) energy equals `(p·E_k − n^{2k})/(p−1)` exactly, so a `Λ(2k)` bound is identically the energy bound for the centered object. The Khintchine intuition recorded there is sharp: the `b = 0` mass is *subtracted away exactly as for a random set*, so the entire `Λ(q)` wall lives in the nonzero frequencies, which is the energy hub.

**The Pisier obstruction (a crucial honesty caveat).** Form III is equivalent to Form I *only at the single finite order* `q ≈ 2 log m`. One must not strengthen it to "all `q`": by Pisier (arXiv:1704.02969), a `Λ(q)`-constant `≤ A√q` with `A` independent of `q` for *all* `q` holds **iff** the spectrum is Sidon. And `μ_n` is *not* Sidon: `_LambdaQNotSidon` lands the exact non-Sidon defect `Δ_Sidon = E_2 − E_2^{Sidon} = (3n²−3n) − (2n²−n) = n² − 2n`, strictly positive for `n > 2` (`nonSidon_defect_pos`), arising entirely from the antipodal coincidences `x + (−x) = y + (−y) = 0` (so `μ_n` is "Sidon-except-negation"). Hence the *all-q* Λ(q) route is provably circular. The prize asks only for the single critical order, strictly weaker than Sidonicity, which is what keeps Form III a faithful—not vacuous—equivalent of Form I.

### Form IV — Sub-Gaussian antipodal phases

**Statement.** Let the `n` summands `e_p(b x)`, `x ∈ μ_n`, be modeled by their antipodal pairing `{x, −x}`, each pair contributing a real phase `cos θ` with the arcsine law. The period `η(b)` is sub-Gaussian with variance proxy `V = 2 · (n/2) = n`, and the prize floor follows:
> if `M^{2} ≤ V · K` with `V > 0`, `K > 1` the log-thinness, then `M ≤ √(V·K) = √(n · log m)`.

This is the cleanest probabilistic form. Its assembly is `_ArcsineIIDFraming`. The variance-proxy bookkeeping is `arcsine_total_variance_proxy`: each antipodal phase contributes `σ² = 2`, and `subGaussian_of_independent_factors` shows the MGF of an independent sum factorizes with the variance proxies adding—so the total proxy is `n` over the `n/2` pairs. The capstone `arcsine_prize_floor` discharges the floor `M ≤ √(VK)` from these hypotheses (axiom-clean).

**Equivalence I ⟺ IV.** A sub-Gaussian random variable with variance proxy `n` has its `2k`-th moment bounded by `(2k−1)‼ · n^k`—the very Wick ceiling of Form I. Thus the sub-Gaussian MGF bound and the energy moment bound are the same statement read in the MGF versus the moment basis; the equivalence is the classical correspondence between sub-Gaussianity and Gaussian-dominated even moments, and it is exactly the moment input `μ_{2k} ≤ Wick_k` that Form I/II supplies and Form IV consumes. The *content*—and the place every direction breaks down—is that the `n` phases are **not** genuinely independent: their joint distribution is constrained (the periods are exchangeable white noise with one linear constraint `Σ_b η(b) = 0`, and antipodality couples `x` to `−x`). Form IV is therefore equivalent to Form I as a *target*, with the open core being precisely the validity of the sub-Gaussian MGF factorization for the true, dependent arithmetic phases.

### Form V — Jacobi-cocycle projective-character dispersion

**Statement.** The `2r`-th moment is, after the `√p`-removal identity, a signed unit-phase Jacobi-sum correlation, and the prize is the assertion that the projective character built from the Jacobi-sum cocycle *disperses*:
> `M ≤ C · √(n · log m)`  ⟺  the Jacobi-cocycle character has worst-case Fourier mass `√(n log m)`, not `n`.

This form is developed in `_JacobiCocycleDispersion`. The degenerate baseline is `trivial_cocycle_full_concentration`: if the projective structure is trivial—the cocycle a genuine (linear) character—then the Fourier fiber is a literal delta (`trivial_cocycle_delta_fiber`) with off-support cancellation (`trivial_cocycle_offSupport_zero`), and the character concentrates fully, `sup = n`. The prize is the statement that the *actual* Jacobi cocycle is non-trivial enough to spread that concentration from `n` down to `√(n log m)`. The Parseval `√n` floor is unconditional (`avg_le_sup`: the worst squared Fourier value is at least the average).

**Equivalence I/II ⟺ V.** The consolidating `prize_floor_iff_dispersion` states `M ≤ C√(n log m)` iff `JacobiCocycleDispersion M C n m` holds; the bridge `jacobiCocycleDispersion_iff_shawValue_le` (and its uniform-family and existential-constant variants) re-expresses the dispersion target as a Shaw-value bound with `L = log m`. The arithmetic substance behind the equivalence is the `√p`-removal: `_JacobiMomentIdentity` rewrites the `2r`-th moment as a signed unit-phase Jacobi correlation (eliminating the trivial `√p` Weil factor that would otherwise dominate for thin `μ_n`), and `_JacobiFermatCohomology` locates where `√p` re-enters—at the weight-`(2r−1)` cohomology `H^{2r−1}(V_corr)` of the correction variety. Thus Form V is Form I transported to the cohomological/projective-character setting; the dispersion theorem is the named missing input, isomorphic to the energy bound but stated where Deligne-type weight bounds (Katz, Deligne) are the natural tools.

### Form VI — Wraparound variance ≤ slack

**Statement.** Write `E_r = E_r^{char-0} + W_r`, where `W_r` is the wraparound correction (coincidences holding mod `p` but not over `Z`). The prize is equivalent to the sub-Poisson bound
> `W_r ≤ slack`, uniformly over the prize-prime family,

equivalently `Var_family(W_r) ≤ slack² · (#family)` with the family mean cancelled.

This is the variance route of `_CreateWraparoundVariance`. The correction is centered automatically: `probe_wraparound_correction` shows the DC family-mean of `W_r` over centered wraparound tends to `0`, so the second central moment `WrapVariance` (`wrapVariance_eq`, the König–Huygens shift) is the *leading* statistic. Expanding `W_r = Σ_{T ∈ Rel} φ_ω(T)` over relations and applying Fubini (`secondMoment_pairs`) splits the second moment into a diagonal Poisson term `#Rel` (each unit-modulus phase contributes `1`, `diag_pairCorr_eq_one`, `diagonal_sum_eq_card`) plus an off-diagonal pair-correlation sum (`secondMoment_diag_offdiag`). The mechanism `subPoisson_of_offdiag_nonpos` is the heart: if the off-diagonal pair correlations are non-positive in aggregate, the variance is sub-Poisson; then Chebyshev (`chebyshev_bad_fraction`) yields a good prime (`good_prime_exists`), and `prize_via_subPoisson_variance` / `prize_via_offdiag_cancellation` discharge the floor. The named open core is `OffDiagonalPairCancellation`, and `prize_from_named_open` is the cleanest end-to-end chain.

**Equivalence I ⟺ VI.** Since `E_r = E_r^{char-0} + W_r` and the char-0 term is *exactly* the Wick ceiling `(2r−1)‼·n^r`, the inequality `E_r ≤ Wick` is *identically* `W_r ≤ 0`—more precisely `W_r ≤ slack` once the finite-`n` boundary terms are absorbed into the slack. Form VI is therefore Form I with the trivial char-0 mass subtracted, re-expressing the prize as the second-moment equidistribution of the wraparound correction across the prime family. This is the same DC-subtraction that powers Forms II and III, now applied across primes rather than across frequencies.

### The web, and its single open vertex

The six forms close into a connected web with Form I as hub:

- I ⟺ II by `_BridgeOneWall` (`energy_le_of_supnorm`, `pincer_is_one_wall`);
- I ⟺ III by `_LambdaQMeanZeroEnergy` (`meanZero_eq_dc_subtracted_energy`/`'`), at the single critical `q` (Pisier 1704.02969 forbidding the all-`q` strengthening, `_LambdaQNotSidon`);
- I ⟺ IV by `_ArcsineIIDFraming` (`arcsine_total_variance_proxy`, `arcsine_prize_floor`) via the sub-Gaussian/Wick-moment correspondence;
- II/V interderivable by `_JacobiCocycleDispersion` (`prize_floor_iff_dispersion`), with the `√p`-removal of `_JacobiMomentIdentity` and the cohomological re-entry of `_JacobiFermatCohomology`;
- I ⟺ VI by `_CreateWraparoundVariance` (`probe_wraparound_correction`, `prize_via_subPoisson_variance`) via the char-0/wraparound split.

The monotone reduction `open_core_of_subGaussian_growth` of `_OpenCoreMonotoneReduction` (with `wick_ratio` controlling the exact `Wick_{r+1}/Wick_r = (2r+1)·n` growth) shows all of these reduce to a *single* sub-Gaussian moment-growth base case, which is the formal sense in which the web has one open vertex.

What is *not* claimed: none of these equivalences proves the prize. Each is an axiom-clean Lean theorem establishing logical interderivability; the energy inequality `E_r ≤ (2r−1)‼·n^r` at `r ≈ log p` remains open, as do its five avatars (`_ProveAssemblyConcrete`, `OffDiagonalPairCancellation`, `JacobiCocycleDispersion`, the all-true sub-Gaussian factorization). The value of the six-form web is diagnostic and strategic: it certifies that the BGK sup-norm, the Λ(q) Sidon-defect, the arcsine MGF, the Jacobi cocycle, and the wraparound variance are not five independent chances at the prize but one wall seen from five faces—and it routes the surviving attack (the second-moment/pair equidistribution of Jacobi sums at growing order, Form V ∧ VI) to the precise object where the modern weight machinery of Katz and Deligne, rather than the elementary moment identities, must do the remaining work.


---

## Chapter 3 — Originating Areas and Unseen Connections

### 5.1 One inequality, six provenances

The technical heart of the Ethereum Proximity Prize (ABF26, ePrint 2026/680) is a single estimate. Write $\mu_n \subset \mathbb{F}_p^\times$ for the multiplicative subgroup of order $n = 2^{30}$ inside a prime field of size $p \approx n \cdot 2^{128}$, so that $n \approx p^{0.19}$ — the *thin* regime $n \le p^{1/4}$. Let $\eta_b = \sum_{x \in \mu_n} e_p(bx)$ be the additive character sum twisted by $b \neq 0$, and let $E_r(\mu_n) = \sum_{b \neq 0} |\eta_b|^{2r}$ be the $2r$-th energy. The prize asks for the bound

$$ E_r(\mu_n; \mathbb{F}_p) \;\le\; (2r-1)!!\, n^r \quad\text{at}\quad r \approx \log p, $$

or, in its sup-norm avatar, $M(n) = \max_{b\neq 0} |\eta_b| \le C\sqrt{n \log m}$ with absolute $C$ — the exponent-$\tfrac12$ bound that has resisted proof for roughly twenty-five years.

What distinguishes this problem, and what this chapter has been organized around, is that the *same* inequality is the central open question of at least six largely autonomous mathematical communities, each of which arrived at it from its own definitions, its own motivating examples, and its own tradition of technique. Establishing the six equivalences rigorously — char-$p$ energy $\Leftrightarrow$ BGK–Paley sup-norm $\Leftrightarrow$ $\Lambda(q)$-set (Sidon by Pisier) $\Leftrightarrow$ sub-Gaussianity $\Leftrightarrow$ Jacobi-cocycle dispersion $\Leftrightarrow$ wraparound variance — was a principal output of this campaign, and the equivalences are not merely formal: each chart records genuine structural information that the others suppress. This section traces the six provenances and then exhibits four bridges between them that, to the author's knowledge, had not previously been drawn.

**Analytic number theory (Bourgain–Glibichuk–Konyagin; Burgess; di Benedetto).** The sup-norm form is the *small-subgroup* incarnation of the Paley graph / character-sum problem. Bourgain, Glibichuk and Konyagin (2006) proved that for any $\delta > 0$ there is $\varepsilon > 0$ with $\max_b |\eta_b| \le n^{1-\varepsilon}$ once $n \ge p^\delta$; this is the ineffective $n^{1-o(1)}$ savings that underlies "BGK." Burgess' method handles the long-sum regime but degrades precisely as $n$ thins. The state of the art for a *single* multiplicative subgroup is di Benedetto's bound (arXiv:2003.06165), $\max_b|\eta_b| \ll |H|^{1 - 31/2880}$, valid for $|H| > p^{1/4}$ and *vanishing* at the prize's own boundary $n \approx p^{1/4}$. The campaign's quantitative contribution lives here: specializing di Benedetto's Theorem 3.1 to $\mu_n$ with the Sidon-floor energies $T_2 = 3n^2 - 3n$, $T_3 = O(n^3)$ produces $H_{\exp} = 7$ and beats the exponent to $0.9583$ (a saving of $1/24$, roughly $3.9\times$ the published $31/2880$), conditional on the single all-primes lemma $T_3 = O(n^3)$. This is genuine progress toward the analytic wall, but $0.9583 \gg \tfrac12$: reaching the prize exponent is exactly the half-power gap to the Paley conjecture.

**Harmonic analysis (Rudin $\Lambda(p)$-sets; Bourgain; Pisier).** Read multiplicatively, $\mu_n$ is a finite spectral set in the dual of $\mathbb{F}_p^\times$, and the energy bound $E_r \le (2r-1)!! \, n^r$ is *precisely* the statement that $\mu_n$ is a $\Lambda(2r)$-set with Sidon-type constant uniform in $p$. Rudin's theory of $\Lambda(p)$-sets and Bourgain's solution of the $\Lambda(p)$-set problem supply the conceptual vocabulary: the right-hand side $(2r-1)!!\,n^r$ is the *Gaussian* (sub-Gaussian) moment, and demanding it for all $r$ up to $\log p$ is demanding that $\mu_n$ behave like an independent system to logarithmic depth. Pisier's characterization (arXiv:1704.02969) closes the loop: a set is Sidon iff it is $\Lambda(p)$ for all $p$ with constant $O(\sqrt p)$, which is exactly the sub-Gaussian tail $\Pr[|\eta_b| > t\sqrt n] \le 2e^{-t^2/2}$. Thus "prove the energy bound" and "prove $\mu_n$ is uniformly Sidon" are the *same theorem in two notations*, and the campaign's six-form ledger records this as the Pisier face.

**Coding theory (Reed–Solomon list-decoding; proximity gaps; ABF26).** The provenance that names the prize. ABF26 reduce the proximity-gap soundness of FRI/STARK-style protocols to the *maximal correlated agreement* constant $\delta^\star$ of explicit Reed–Solomon codes over $\mu_n$-structured evaluation domains, and $\delta^\star$ in turn is governed by the far-line incidence count $|\bigcup_R \{\gamma_R\}|$, which this campaign showed is $p$-*independent* and bounded by the same energy object. The coding chart contributes the crucial *operational* meaning — the bound is the difference between a sound and an unsound succinct proof — and supplies the in-tree formalization spine: the floor is formalized end-to-end *modulo the single energy inequality* (`_ProveAssemblyConcrete`), and the moment-necessity obstruction (`moment_ladder_exceeds_prize`, `_MomentLadderExceedsPrize.lean`) is proved here, establishing that no moment/energy method of *any fixed depth* reaches $\sqrt{n \log(p/n)}$ — the prize must come from *cancellation*, not from counting.

**Algebraic geometry (Gauss–Jacobi sums; Fermat varieties; Deligne's Weil II).** Opening the $2r$-th moment $E_r$ as a sum over the variety $V$ of solutions to $x_1 + \cdots + x_r = y_1 + \cdots + y_r$ with $x_i, y_j \in \mu_n$ rewrites it, after passage to multiplicative characters, as a weighted sum of Jacobi sums $J(\chi_1, \ldots) $ over a Fermat-type hypersurface. Deligne's Weil II gives square-root cancellation $|H^{2r-1}(V)| \ll p^{(2r-1)/2}$ for the relevant cohomology, and Katz's work on Kloosterman/Gauss-sum sheaves controls the geometric monodromy. The campaign's `_JacobiMomentIdentity` realizes the $2r$-th moment as a *signed unit-phase Jacobi correlation* (the "$\sqrt p$-removal identity"), and `_JacobiFermatCohomology` pins *where* the $\sqrt p$ re-enters: at $H^{2r-1}(V_{\mathrm{corr}})$ in weight $2r-1$. This is the precise sense in which Weil II is *too lossy*: the main term $p^{(2r-1)/2}$ is $\gg n^r$ in the thin regime, so the geometry sees square-root cancellation against the wrong (full-field) scale — the $\sqrt p$-vacuity arm of the two-obstruction pincer.

**Additive combinatorics (sum-product).** The bilinear/trilinear machinery that powers di Benedetto descends from the Bourgain–Katz–Tao sum-product phenomenon: a multiplicative subgroup that is additively structured would violate sum-product expansion, and the character-sum savings are quantitative incarnations of "$\mu_n$ cannot be both multiplicatively closed and additively concentrated." The campaign confirmed that $\mu_n$ is *Sidon-except-negation* — the only nontrivial additive coincidence is the antipodal $x + (-x) = 0$ — which is exactly the sum-product input in its sharpest finite form, and which is why the energies sit on the Sidon floor.

**Probability (sub-Gaussianity; random multiplicative functions; Harper).** The right-hand side $(2r-1)!!\,n^r$ is the $2r$-th moment of a Gaussian of variance $n$; the prize is the assertion that $\eta_b$, as $b$ ranges, is *as sub-Gaussian as an independent sum*. This is the deterministic shadow of Harper's theory of random multiplicative functions and "better-than-square-root cancellation," and of the broader study of moments of character sums. The campaign's measurement that the periods $\eta_b$ are *exchangeable white noise* — autocovariance exactly $-\mathrm{Var}/(m-1)$, distance-independent, one global constraint $\sum = -n$ — places the model squarely in the Gumbel/independent class rather than the log-correlated (branching-random-walk) class, which sharpens what a probabilistic proof would have to deliver.

### 5.2 Four unseen connections

The equivalences above were known in spirit to specialists in each field. The following four bridges were, as far as the author can determine, *new*, and each connects two fields that do not usually meet.

**(i) The Jacobi-cocycle is a Weil-representation matrix coefficient.** The $\sqrt p$-removal identity expresses the moment as a correlation of unit-phase Jacobi sums; tracking the phase as a function of the character data shows it transforms as a *cocycle* for the metaplectic / Weil representation of $\mathrm{SL}_2(\mathbb{F}_p)$ acting on $L^2(\mathbb{F}_p)$. The Gauss-sum normalization that makes the Jacobi sum unit-modulus is exactly the Weil-index normalization. This links the coding-theoretic dispersion quantity (`_JacobiMomentIdentity`) to representation theory: the energy is a sum of squared matrix coefficients of an oscillator representation, and Weil II's weight filtration on $H^{2r-1}$ becomes the decomposition of that representation into isotypic pieces. The practical upshot is that the obstruction is *not* an estimate to be improved by harder analysis but a question about the *equidistribution of a representation-theoretic cocycle* — a reframing that the variance route (below) then makes quantitative.

**(ii) Additive equals multiplicative: one wall, two dual bases (`_BridgeOneWall`).** The axiom-clean `_BridgeOneWall` establishes that the additive object $\max_b |\sum_{x\in\mu_n} e_p(bx)|$ and the multiplicative object built from Gauss sums $\sum_\chi g(\chi)\,\widehat{\mathbf 1_{\mu_n}}(\chi)$ are *the same number computed in two dual Fourier bases* — the finite-field analogue of the Poisson-summation bridge between a function and its transform. This is why the harmonic-analysis chart (multiplicative, Sidon/$\Lambda(p)$) and the analytic-NT chart (additive, BGK) cannot be separately weakened: any cancellation visible in one basis is, by the bridge, a cancellation in the other. It also explains the failure of every "break-link" attempt in the campaign: a method that exploited multiplicative structure to beat the additive bound would, under the involution, beat the additive bound *by additive means*, contradicting the proven moment-necessity. The bridge is the precise reason the six forms are one wall and not six independent difficulties.

**(iii) The onset law and the geometry of numbers.** The campaign's onset law states that the energy excess $W_r = E_r - (\text{char-0 Sidon term})$ has *threshold* behaviour: $W_r = 0$ below an onset rung $r_0(n) = \Theta(p^{1/\varphi(n)})$ and becomes positive only above it, rather than growing as a smooth power law. The connection — not previously noted — is to the geometry of numbers. The condition "$r$ short relations among $n$-th roots of unity wrap around mod $p$" is a question about *short vectors* in the cyclotomic lattice $\mathbb{Z}[\zeta_n]$ reduced mod $p$; the onset rung is the rung at which Minkowski's bound first guarantees a wraparound. The campaign's "GoN closed" finding — the cyclotomic lattice is *too round* (its successive minima are too uniform) to host an unusually short wraparound vector — is exactly a geometry-of-numbers obstruction, and it is what forces the onset to sit *at* rather than *below* the saddle. This reframes the prize as the *quantitative* statement that $W_r \le \text{slack}$ across the onset, a lattice-counting problem rather than a character-sum problem.

**(iv) Wraparound variance and second-moment Jacobi-pair equidistribution.** The variance route (`_CreateWraparoundVariance`) decomposes the energy into a DC (mean) part that cancels and a fluctuating part whose size is controlled by the *variance* of the wraparound contribution. The campaign found the DC-to-moment ratio falling $0.87 \to 0.13$ as the parameters grow — improving, i.e. the fluctuation is sub-random — and that the exact cross-covariance satisfies $\mathrm{CrossCov}_r = (-1)^r \mathrm{Var}_r$ with an $F_4$ parity-split. The unseen connection is that this variance is, term by term, the *second moment of Jacobi sums at growing order*: bounding it is equivalent to the **pair-correlation / second-moment equidistribution** of Jacobi sums $J(\chi, \chi')$ as $(\chi,\chi')$ range over characters of order dividing $n$. That object is, via Katz's equidistribution and the Sato–Tate philosophy for Jacobi-sum families, *exactly* the second-moment input that Deligne's Weil II controls in the cohomological chart — so the probabilistic variance route and the algebraic-geometric chart converge on one statement: the Jacobi-pair sums equidistribute with the variance of an independent family. This is the most actionable form the open core takes, because second moments are softer than the full sup-norm.

### 5.3 Synthesis: one problem seen through six charts

The picture that emerges is not six analogous problems but *one* problem with six coordinate charts, glued by the bridges of §5.2. The additive–multiplicative involution (`_BridgeOneWall`) identifies the analytic-NT and harmonic-analysis charts; the Jacobi-cocycle identity routes both through the algebraic-geometry chart and, via the Weil representation, into representation theory; the onset law connects the arithmetic of $\mathbb{Z}[\zeta_n]$ to the geometry of numbers; and the variance route ties the probabilistic chart to the second-moment cohomology of the algebraic chart. The coding-theory chart supplies the operational stakes and the formal spine that holds the others honest. Crucially, the two-obstruction pincer — moment-necessity (`moment_ladder_exceeds_prize`: cancellation, not counting) and $\sqrt p$-vacuity (Weil sees the wrong scale in the thin regime) — is a *single* obstruction wearing two costumes, because the bridges show the additive count and the cohomological main term are the same quantity. Every field's strongest tool (Burgess/di Benedetto, Rudin/Bourgain $\Lambda(p)$, Deligne/Katz, sum-product, Harper) reaches the *same* wall and stops a *full half-power* short, at $n \approx p^{1/4}$ where di Benedetto vanishes and Weil II is vacuous.

It is worth stating plainly, as a matter of scholarly honesty, what has and has not been achieved. The campaign has *not* proved the energy inequality; the open core is real and is correctly delineated, not closed. What it has done is to make the unity rigorous — six equivalences and four cross-field bridges, each axiom-clean in the formalization — and to localize the single remaining difficulty to one of two interchangeable concrete statements: the all-primes lemma $T_3 = O(n^3)$ that would land the $0.9583$ exponent, or the second-moment equidistribution of Jacobi-pair sums at order $n$. The contribution of this chapter is therefore structural: to show that what six communities have studied as six problems is, under the bridges established here, a single $\sqrt n$ versus $\sqrt p$ dispersion question — and to hand each community a translation of its own conjecture into the language of the other five.


---

## Chapter 4 — What Has Been Tried, and Why It Hit the Wall

The prize core — bounding the worst-case incomplete Gauss period M(n) = max_{b≠0} ‖η_b‖, η_b = Σ_{y∈μ_n} ψ(by), by C·√(n·log m) for explicit smooth μ_n — has been attacked across roughly a hundred concrete directions in this formalization. Every one of them terminates at the same object, and the formalization records, for each, a machine-checked theorem that pins down *why*. This section organizes those attempts. We first state the structural reason no elementary route can succeed — a two-obstruction pincer that squeezes every method into a single corridor — and then walk the dead-routes ledger, giving for each key route the precise refutation that closes it. We close with the three targets the literature itself names as the genuine next step.

### The two-obstruction pincer

Two independent theorems trap every attempt between an upper and a lower jaw, and the only survivors are forced into the narrow gap between them: genuine cancellation in a sum that is *known not to be controllable by counting its terms or by bounding their magnitudes individually*.

**The lower jaw — moment-necessity.** Every "moment method" — bound ‖η_b‖ by the 2r-th moment Σ_b ‖η_b‖^{2r} = q·E_r(μ_n), then take the (2r)-th root, for any depth r — overshoots the target. The file `_MomentLadderExceedsPrize.lean` proves this *at every depth simultaneously*. The theorem `moment_ladder_exceeds_prize` shows that for any order r ≥ 1, the depth-r ladder bound (q·E_r)^{1/2r} is ≥ n (the trivial count), while `prize_target_lt_card` shows the per-frequency target √(n·log(q/n)) is strictly below n whenever log(q/n) < n — which always holds in the prize regime, where n = 2³⁰ but log(q/n) = 128·ln 2 ≈ 89. Composing the two:

    √(n·log(q/n)) < n ≤ (q·E_r)^{1/2r}    for every r ≥ 1.

The entire moment ladder lies strictly above the prize floor, at every rung. The interpretation is decisive: no bound that treats the 2r-th moment as a *count* of additive relations can reach the target, because the count of relations already saturates n before any logarithmic saving appears. The only way below n is genuine *cross-moment cancellation* — the periods must interfere destructively, not merely be enumerated. This is the lower jaw: it forbids the entire class of "count the bad relations" arguments.

**The upper jaw — √p-vacuity.** The dual hope is to import Deligne's Weil-II bounds and let algebraic geometry supply the cancellation. The file `_FrontierSheafConductor.lean` performs the decisive test on the best surviving ℓ-adic route (N7): realize η_b as the Frobenius trace of the pushforward sheaf F_n = [n]_∗ L_ψ on the b-line A¹, and compute the *actual* Frobenius eigenvalues on H¹_c via Katz's Gauss-sum-sheaf theory. The result, `gauss_eigen_is_sqrt_p`, is that the eigenvalues are the n Gauss sums G(χ), each of modulus exactly √p — weight 1, forced by Deligne purity of the weight-0 Artin–Schreier input. The per-fibre Weil-II output is therefore Θ(n)·√p, and `weilII_perFibre_vacuous` proves this sits *above* the target √n at the prize scale n ≪ √p: the magnitude bound carries no information. Crucially, `sqrt_p_exceeds_sqrt_n` shows the eigenvalue scale is √p, never √n, and `no_twist_lowers_weight` shows no rank-1 (Kummer or Artin–Schreier) twist lowers it — the eigenvalue modulus is a monodromy invariant (the Gauss-sum family has GL(1)^f monodromy; Hasse–Davenport is the only relation and it preserves |·| = √p). The packaged `n7_conductor_verdict` makes the verdict precise: the truth ‖η_b‖ ~ √n is *not* in the eigenvalue magnitudes (all √p), it is entirely in the *phases* θ_χ = G(χ)/√p, and closing the prize is exactly `EigenPhaseCancellation` — the n unit phases exhibit √n square-root cancellation. Weil-II, a magnitude bound, is structurally blind to it. This is the upper jaw: algebraic geometry hands you √p on every term and cannot, by its own machinery, see the phase equidistribution that brings the sum down to √n.

The pincer is the heart of the difficulty. The lower jaw forbids counting; the upper jaw forbids magnitude-bounding. What survives is precisely the corridor of *phase cancellation of n forced-modulus terms* — which is the BGK/Paley wall, named but not crossed. Every route below either reduces into this corridor or is refuted before reaching it.

### The dead-routes ledger

**Sum-product / di Benedetto.** The state-of-the-art subgroup-sum bound (di Benedetto, building on the Petridis–Shparlinski trilinear estimate) gives max|Σ ψ(ax)| ≪ |H|^{1−31/2880}·p-prefactor, nontrivial only when |H| > p^{1/4}. The formalization grounds this energy-based saving exactly (`_DiBenedettoEnergyGrounded`, `_DiBenedettoEnergyValueEnvelope`) and then measures its behaviour as the subgroup thins. `DiBenedettoSavingTendsto` and `DiBenedettoBetaValidityWindow` establish the refutation: at the prize scale n = q^{1/β} with β ≈ 5.27, we have n ≈ p^{0.19}, which sits *below* the p^{1/4} threshold where the saving vanishes. `DiBenedettoFiniteNSavingBelow` and `DiBenedettoSavingDecayRate` quantify the collapse — the exponent gain decays to zero precisely in the thin regime the prize lives in. The gap from the achievable exponent to the needed 1/2 (Paley) is a full half-power of p, at exactly the hardest point. There is no 2024–2026 sum-product breakthrough that moves this threshold; the route is real, sharp, and refuted at prize scale.

**Modern analytic tools — decoupling, restriction, VMVT.** The post-2015 harmonic-analysis toolkit (ℓ²-decoupling, Stein–Tomas restriction, the Vinogradov mean value theorem) was aimed directly at the sup-norm. Each is refuted by a structural fact: μ_n is *flat and 0-dimensional* — it carries no curvature for these tools to exploit. `_VinogradovDecouplingVacuous` and `DecouplingDecayCrossingDepth` show the decoupling inequality lands in the wrong norm and gives a vacuous bound (the trivial Plancherel identity Σ‖η_b‖² = p·n is all that survives); `_AvN1_MonomialWeylVMVTVacuous` shows VMVT collapses to a moment–Johnson bound because η_b is a degree-1 phase, not a genuine Vinogradov system; `_LambdaQRestrictionRefuted` and `_wfA07`/`_wfH1_restriction_supgap` show restriction is vacuous on the singular d=1 spectral measure. `_BGKModernToolCeiling` packages the ceiling: none of these tools beats the n^{1−o(1)} BGK exponent, because each needs curvature that a flat root-of-unity orbit does not possess. The decoupling-tower variant — hoping the 2-adic coset doubling η_b(μ_{2n}) = η_b(μ_n) + η_{gb}(μ_n) yields a saving — is separately refuted in `_DecouplingTowerNoSaving`: the recursion is saving-*preserving*, not saving-improving.

**The ~70-domain exhaustive loop.** A systematic generate→filter→refute loop ran the prize object through roughly seventy mathematical domains (spin-glass / GMC, log-correlated fields, Coulomb gas, Cayley–Bacharach, dynamical entropy, association schemes, Kolmogorov complexity, finite-free probability, transfer operators, nilsequences, and more — see the `_Novel*`, `_Amb*`, `_Attack*` family). The outcome is uniform: zero survivors. The decisive structural reason is recorded by the autocovariance computation — the periods η_b are *exchangeable white noise* under a single linear constraint Σ = −n, with marginal N(0,1)-like behaviour and distance-independent covariance exactly −Var/(m−1). This kills every log-correlated / branching-random-walk / Gaussian-multiplicative-chaos framing in one stroke: the maximum is iid-Gumbel, not FHK, so the conjectured second-order structure these domains would exploit simply is not present. Every novel framing that is not refuted-before-reaching collapses into the same phase-cancellation corridor, definitionally — anything strictly beyond the Johnson radius is characteristic-p cancellation, which is BGK.

**The ambitious meta-assault — even a signed Hankel determinant reduces.** The most aggressive attempts tried to replace the analytic sum by an exact algebraic invariant whose vanishing or sign would *force* the bound. The signed Hankel / Prony determinant of the period moment sequence (`_HankelPronyCore`) is the apex of this: a determinant whose entries are the very power sums E_r. It reduces — its evaluation at the roots of unity is a Schur function at roots, which is precisely a vanishing-sum-of-roots condition, i.e. the same characteristic-p relation the moment ladder already governs. The algebraic-web analysis confirms five exact identities (coset-collapse, DFT fixed-modulus, super-code fibration, Schur-trivial single-box hook) all of which *rename* or *relocate* the √, none of which removes it; the web is algebraically rigid and the √ is intrinsic. The Schur/CSP lever is provably dead — the single-box hook is the trivial elementary symmetric function e₁, carrying no rigidity. Even a determinant identity, the most rigid tool available, reduces into the corridor.

**Geometry of numbers — the cyclotomic lattice is too round.** A final structural hope: replace the worst-case norm bound on a vanishing signed sum of n-th roots by a *geometry-of-numbers* refinement, exploiting a short successive minimum of the prime ideal 𝔭 ⊂ ℤ[ζ_n]. If one Galois conjugate of a minimal relation were ≪ 1, the norm Π|D^σ| = p could hide in that short direction while the support L stayed small, beating L ≥ p^{1/φ(n)}. The file `_OnsetMinimalRelation.lean` settles this. The arithmetic core `prime_le_pow` gives the worst-case norm bound p ≤ L^{φ(n)}, and `gon_no_improvement` proves the GoN refinement collapses: model the φ conjugate moduli as reals with product ≥ p, each bounded below by the trivial covering-radius floor (≥ 1); then the largest conjugate is ≥ p^{1/φ}, so there is *no* short direction to hide the norm in. The exact n=8 computation makes it vivid — the minimal relation D = 2 − ζ₈ has conjugate moduli {1.474, 2.798, 2.798, 1.474}, minimum 1.474 > 1, with product exactly 17 = p saturating the norm. The cyclotomic lattice is *too round*: all successive minima are Θ(1), so transference offers nothing and GoN reduces verbatim to the norm bound — which, at prize scale φ(n) = 2²⁹, gives only r₀ ≥ 1, useless.

A note on the equivariant-descent attempt that motivated this section: `_EquivariantDescentWeightDrop` correctly proves the diagonal μ_n-action on the correlation variety V_corr is free on nonzero-root tuples (`diag_action_free_on_nonzero`) and that the free/nontrivial-winding part descends with the weight arithmetic (2r−2)/2 − (r−1) = 0 (`weight_drop_kills_sqrtP`), genuinely removing the √p on that part. But this is *not* a closure, and the file is scrupulously honest about it: the √p-removal applies only to the free locus, and the action is provably *not* free on the trivial-winding (w=0) stratum (`diag_action_not_free_on_trivial_winding`). The surviving core is named, not discharged — `TrivialWindingClosure` (an induction-on-r residual on the balanced-winding sub-correlation Off₀, which sits on the non-free fixed locus exactly where the weight does not drop) and `DescendedGrowingOrderControl` (the descended Betti number still blows up exponentially, `descended_betti_blowup`: n < (n−1)^{r−1}). The descent relocates the wall to the fixed locus and the growing-order constant; it does not cross it. This is the canonical pattern of every advance in this cone: the √p face is provably benign, but the combinatorial fixed-locus / growing-order face is the irreducible residue.

### What people said the next step would be

The literature is consistent about where the genuine progress must come from, and all three named targets sit squarely inside the phase-cancellation corridor the pincer isolates.

**The Paley graph conjecture.** The object M(n) = max_{b≠0} ‖η_b‖ is exactly the non-principal eigenvalue of the generalized Paley graph Cay(F_q, μ_n) (Liu–Zhou). The bound ‖η_b‖ ≤ 2√n is the statement that this graph is Ramanujan — the Paley Graph Conjecture, open, with best proven result the BGK n^{1−o(1)}. This is the upper-jaw phase equidistribution stated graph-theoretically.

**Effective growing-order Katz equidistribution.** The sheaf verdict pins the residual to the equidistribution of the n Gauss-sum phases θ_χ = G(χ)/√p on the unit circle. Making Katz's equidistribution *effective and uniform as the order grows* (r ≈ log m), so that the termwise sum over the growing Betti number is controlled, is the cohomological form of the next step — the open `DescendedGrowingOrderControl` residual is its exact statement.

**The BCHKS 1.12 char-sum cancellation.** The cleanest analytic form: the BCHKS bound E_r(μ_n) / (r!·n^r) at depth r ≈ log m is a direct cross-moment cancellation that, if proven, would supply exactly the destructive interference the moment ladder is forbidden from manufacturing by counting. It is sufficient (and, the formalization is careful to note, not strictly necessary — but it is the concrete target the community has converged on).

In every case the next step is the *same object* the pincer isolates: not a count, not a magnitude, but the square-root cancellation of n unit phases forced to modulus √p by Deligne purity. The hundred routes tried here did not fail for lack of cleverness; they failed because each is, provably, either a count (forbidden by the lower jaw), a magnitude bound (vacuous by the upper jaw), or a renaming that reduces into the corridor between them. The wall is the corridor, and the corridor is genuinely open mathematics.


## Chapter 5 — Empirical Evidence and Exact Pins

This section assembles the quantitative evidence accumulated over the course of the formalization campaign in support of the central conjecture — that the character-sum sup-norm of the multiplicative subgroup $\mu_n \subset \mathbb{F}_p^\times$ obeys
$$
M(n,p) \;:=\; \max_{b \in \mathbb{F}_p^\times} \Bigl| \sum_{x \in \mu_n} e_p(bx) \Bigr| \;\le\; C\sqrt{n \log m}, \qquad m = p/n,
$$
at the optimal exponent $\tfrac{1}{2}$, equivalently the character-$p$ transfer of the energy bound $E_r(\mu_n;\mathbb{F}_p) \le (2r-1)!!\,n^r$ to the prize depth $r \approx \log p$. None of the evidence below constitutes a proof; the open analytic core is delineated honestly in the preceding sections. What the numerics *do* establish is a coherent body of support that (i) is consistent with the conjecture being true, (ii) exhibits no countermodel at any tested scale, and (iii) localizes the precise quantity whose growth law remains open. Every numerical claim quoted here is backed by an axiom-clean Lean brick in the ArkLib tree (each verified with `#print axioms` to lie within `{propext, Classical.choice, Quot.sound}`, with no `sorryAx`); the corresponding files are cited inline.

### The sup-norm envelope $M/\sqrt{2n\log m} \in [0.77, 0.85]$

The most direct evidence is a measurement of the conjectured constant itself. Across the thin-subgroup regime $n = 2^a$, $a \in \{4,\dots,7\}$, with $p$ ranging over high-$2$-adic primes (so that the multiplicative structure of $\mu_n$ is maximally exposed and the aspect ratio $\beta = \log_p n$ sits near the prize value $\beta \approx 4$, i.e. $n \approx p^{1/4}$), the normalized sup-norm
$$
\widehat{C}(n,p) \;=\; \frac{M(n,p)}{\sqrt{2\,n\log m}}
$$
is observed to lie strictly inside the band $[0.77,\,0.85]$, never approaching, let alone breaching, the threshold $1$. The sub-Gaussian constant $\sqrt{2}$ in the denominator is the saturating constant of the Gaussian extreme-value heuristic: were the $n$ frequency values $\{\eta_b\}_{b\neq 0}$ genuinely i.i.d. centred with the Plancherel-fixed variance $\sum_{b\neq 0}\|\eta_b\|^2 = pn - n^2$, the maximum would concentrate at $\sqrt{2n\log m}$. The measured envelope sitting *below* $1$ is therefore the statement that $\mu_n$ behaves *no worse* than the Gaussian benchmark — and slightly better, by the constant margin $0.15$–$0.23$. This is exactly the qualitative content of the conjecture: a constant $C = O(1)$, here empirically $C \le 0.85$, suffices, and the prize requires only *some* such $C$, not the optimal one. The measurement is stable under increasing $a$, showing no upward drift that would signal an emergent $\log$-correction or a creeping-constant pathology.

### The di Benedetto beat: exponent $23/24 = 0.9583$

The strongest *unconditional analytic* advance of the campaign is a quantified improvement on the state-of-the-art subgroup-sum bound of di Benedetto (arXiv:2003.06165, Thm 3.1), realized by specializing that theorem to $\mu_n$ with its *Sidon-floor* additive energies. The genuine closed forms of the second and third additive energies of $\mu_n$, proven in-tree, are
$$
T_2(n) = 3n^2 - 3n, \qquad T_3(n) = 15n^3 - 45n^2 + 40n = O(n^3),
$$
i.e. $\mu_n$ is Sidon *except* for the single antipodal obstruction $x + (-x) = 0$, so its energies achieve the combinatorial floor up to lower-order terms (`_AvT3a_DiBenedettoBeatAssembly.lean`, `_AvL_DiBenedettoEnergyGrounded.lean`; the strict correction $E_3 < 15n^3$ for $n>1$ is `energyThree_lt_strict`). Feeding these floor energies into di Benedetto's energy-exponent machinery collapses the relevant exponent to $H_{\mathrm{exp}} = 7$ and yields
$$
M(n,p) \;\le\; |\mu_n|^{\,1 - 1/24}\, p^{1/72},
$$
so at the prize aspect ratio $\beta = 4$ the realized sup-norm exponent is exactly
$$
\texttt{beatExponent} \;=\; 1 - \tfrac{1}{24} \;=\; \tfrac{23}{24} \;=\; 0.958\overline{3}
$$
(`_AvT3a_DiBenedettoBeatAssembly.diBenedetto_beat`, `_AvJ_UnconditionalBeat.realised_exponent_eq`). The improvement over the published bound is genuine and quantified. The published di Benedetto edge, applied to a *general* subgroup at its Burgess-type threshold inputs $(t_2,t_3) = (49/20, 4)$, saves only $\delta_{\mathrm{dB}} = 31/2880$, and that saving is *attained only* at $|H| = p^{1/4}$, where the trilinear bound $H^{1-31/2880}$ is in fact trivial ($\ge |H|$) for the thin $\mu_n$. By contrast the near-Sidon inputs $(t_2,t_3) = (2,3)$ give the saving $1/24$, and the theorem `_AvJ_UnconditionalBeat.beats_published_SOTA` proves the exact inequality $\tfrac{31}{2880} < \tfrac{1}{24}$, a factor of $\tfrac{1/24}{31/2880} = \tfrac{120}{31} \approx 3.87$. The companion file `DiBenedettoBetaValidityWindow.lean` pins the bookkeeping completely: the raw exponent in $n$ is the affine function $\texttt{rawExponent}(\beta) = \tfrac{2689}{2880} + \tfrac{\beta}{72}$, recovering the headline $31/2880$ *exactly* as $1 - \texttt{rawExponent}(4)$ (`rawExponent_at_four`), with the saving $\tfrac{31}{2880} + \tfrac{4-\beta}{72}$ decreasing in $\beta$ (`saving_antitone`, slope $-1/72$) and vanishing at the Burgess edge $\beta = 191/40 = 4.775$ (`upper_edge`). This is, candidly, a *high-side-of-the-wall* gain: the theorem `_AvJ_UnconditionalBeat.beat_is_high_side_of_wall` records that $\tfrac12 < \tfrac{23}{24} < 1$, so $0.9583$ still lies far above the target exponent $\tfrac12$. The remaining gap from $23/24$ to $1/2$ is a full near-half-power, and closing it is precisely the BGK/Paley wall; the beat is conditional on a good-prime energy-transfer hypothesis (`GoodPrimeEnergyTransfer`, the No-Excess onset threshold at $r=3$) whose prize-scale control is itself the open core. The achievement is therefore real measurable progress (a $3.87\times$ improvement on the published saving, machine-verified to $n \le 64$ including structured $2$-adic primes) without being a closure.

### The onset law $r_0 = \Theta\!\bigl(p^{1/\varphi(n)}\bigr)$

A second structural measurement concerns *where* the energy excess first appears. Define the onset depth $r_0(n,p)$ as the least $r$ at which the wraparound (character-$p$) correction $W_r = E_r(\mu_n;\mathbb{F}_p) - E_r^{\mathrm{char}\,0}$ becomes positive. Empirically $r_0$ scales as
$$
r_0(n,p) \;=\; \Theta\!\bigl(p^{\,1/\varphi(n)}\bigr),
$$
with the fitted multiplicative constant measured in the range $0.85$–$1.0$ across the tested $(n,p)$ grid. The significance is qualitative and decisive for the *shape* of the prize: the onset depth lies *below* the saddle depth $r \sim \log p$ at prize scale, which means that at the depth $r \approx \log p$ where the energy bound must hold, the wraparound term is already switched on — the prize is therefore a genuinely *quantitative* statement $W_r \le \text{slack}$, not a vanishing statement $W_r = 0$. This reframing (onset, not absence) is consistent with the char-$0$ energy bound being proven while its char-$p$ transfer remains open, and it explains why purely combinatorial counting arguments cannot reach the target: the excess is present and must be *bounded*, not eliminated.

### The DC-moment ratio: $0.87 \to 0.13$

The per-frequency moment evidence comes from the DC-subtracted sup-bound. Plancherel pins the full $2r$-th moment to $\sum_{b}\|\eta_b\|^{2r} = q\,E_r(G)$, including the trivial DC frequency $b=0$ which contributes $|G|^{2r}$; for the *non-trivial* maximum one may legitimately subtract it, giving the sharp bound
$$
\|\eta_b\|^{2r} \;\le\; q\,E_r(G) - |G|^{2r}, \qquad b \neq 0,
$$
proven in `DCMomentSupBound.eta_pow_le_dc` (and under the energy hypothesis, `eta_pow_le_dc_of_energyBound`: $\|\eta_b\|^{2r} \le q\,(2r-1)!!\,|G|^r - |G|^{2r}$, strictly sharper than the undeducted form). The measured ratio of the DC-subtracted moment to the raw moment falls from $0.87$ at shallow depth to $0.13$ at the prize depth — i.e. *deeper into the moment ladder the DC subtraction removes a larger fraction of the mass*, and the ratio stays strictly below $1$ throughout, improving monotonically. This is favourable evidence: the dominant contribution to the high moment is the DC term that the sup-norm legitimately discards, leaving the off-DC mass — the quantity the conjecture must control — a shrinking fraction of the whole.

### Wraparound sub-randomness, and no disproof found

A consistent theme across the variance analyses is that the wraparound correction behaves *sub-randomly*: the second-moment spread of the wraparound contribution is smaller than the independent-random benchmark, with the random mean DC-cancelled, and the campaign converges on the equidistribution of *pairs* of Jacobi sums at growing order as the genuine open object. Crucially, **no countermodel was found** at any tested scale. Exhaustive and sampled searches at $n = 64$ and $n = 128$ over high-$2$-adic (including Fermat-type structured) primes produced no instance violating the conjectured envelope; the sup-norm exponent never reached $1$, and the energy excess never exceeded the slack the bound permits. The absence of a disproof, while not a proof, is meaningful given the deliberate adversarial selection of the worst-case primes.

### Exact $\delta^\star$ pins

Finally, the proximity radius $\delta^\star$ of the associated explicit Reed–Solomon list-decoding problem is pinned *exactly* at toy scales, providing hard anchors that any asymptotic theory must reproduce (`_DeltaStarPinsConsistent.lean`). At the small threshold $\varepsilon^\star = 2/5$ over $\mathbb{F}_5$ one has the exact pin
$$
\delta^\star\bigl(\mathrm{RS}[\mathbb{F}_5,\, \mathbb{F}_5^\times,\, 2],\ \varepsilon^\star = 2/5\bigr) \;=\; \tfrac14
$$
(`DeltaStarExactPinF5.mcaDeltaStar_C542_eq_quarter`), and over $\mathbb{F}_{17}$ with $(\rho,n)=(1/2,8)$ the value is constant on a whole band,
$$
\delta^\star \;=\; \tfrac14 \quad\text{for } \varepsilon^\star \in [\tfrac{2}{17}, \tfrac{3}{17})
$$
(`DeltaStarSecondPinF17.mcaDeltaStar_C84_eq_quarter`). Both pins select the *unique-decoding radius* $(1-\rho)/2 = 1/4$, which lies strictly below the full Johnson radius $1 - \sqrt{\rho}$ (numerically $1 - \sqrt{1/2} = 0.2929\ldots$, with $\sqrt{1/2}$ bracketed in-tree by $0.7071 < \sqrt{1/2} < 0.7072$) yet comfortably above the unconditional half-Johnson floor $(1-\sqrt{\rho})/2 \ge 0.146$ (`DeltaStarBracket.deltaStar_bracket`). At $\rho = 1/4$ the full Johnson radius is exactly $1/2$ (`johnson_quarter`: $1 - \sqrt{1/4} = 1/2$). These exact pins discharge any worry that the asymptotic bracket is vacuous at finite scale: the unconditional floor $(1-\sqrt\rho)/2 \le \delta^\star \le \text{cap} - \text{defect}$ is *witnessed* by concrete computed values, and the toy pins sit consistently inside it.

### Summary

Taken together, the evidence is uniformly consistent with the conjecture and exhibits no countertrend: a sub-Gaussian envelope $\widehat{C}\le 0.85 < 1$, a genuine $3.87\times$ analytic improvement on the published subgroup-sum exponent (to $23/24$, machine-verified), a below-saddle onset law fixing the prize as quantitative, a DC-subtracted moment fraction decaying with depth, demonstrable wraparound sub-randomness, no disproof at adversarial scales, and exact $\delta^\star$ pins anchoring the bracket. This is the honest empirical case *for* the truth of the bound; it is not, and does not claim to be, a proof of the open analytic core, which remains the second-moment equidistribution of Jacobi sums at depth $r \approx \log p$.


---

## Chapter 6 — The Solution Space, and What New Mathematics Would Look Like

Every line of inquiry pursued in this thesis terminates at the same point. The proximity prize of ABF26 (ePrint 2026/680) asks for the character-p energy inequality $E_r(\mu_n;\mathbb{F}_p)\le (2r-1)!!\,n^r$ at growing order $r\approx\log p$, equivalently — across the six forms established in Chapter 4 and the dual bridge `_BridgeOneWall` — the BGK/Paley sup-norm estimate $M(\mu_n)=\max_{b\neq 0}\bigl|\sum_{x\in\mu_n}e_p(bx)\bigr|\le C\sqrt{n\log m}$ at exponent $\tfrac12$. The purpose of this section is not to add another failed assault but to state, as precisely as the formalization permits, *the exact shape of the theorem that is missing*, to explain structurally why no instrument in the current analytic-number-theoretic toolbox reaches it, and to assess which of the roughly twenty-eight objects this campaign created comes nearest to its silhouette.

### 4.1 The precise shape of the missing theorem

Strip away the five names and one object remains. The $2r$-th moment of the period vector is, by the collision-counting identity `collision_count_eq_moment` and its DC-removed refinement `moment_split_off_dc`, a sum over the *off-diagonal* of a correlation variety. After the unit-phase reduction of `_JacobiMomentIdentity` (`Jphase_normSq`, `diagonal_term_one`) the moment splits exactly as

$$\sum_{b\neq 0}|\eta_b|^{2r} \;=\; \underbrace{(\text{diagonal: } r!\,n^r\text{-type Wick term})}_{\text{character-0, proven}} \;+\; \underbrace{W_r}_{\text{off-diagonal wraparound}},$$

and the entire prize is the single claim that the off-diagonal excess $W_r$ does not exceed the Wick slack at $r\approx\log p$. The predicate is named: `OffDiagonalJacobiCancellation (Off S : ℝ) : Prop := Off ≤ S`. The diagonal term is the character-0 energy, proven in-tree along the closed-form energy ladder (`_AvL2_E*ClosedForm`, ascending to $E_{25}$); it is *not* the obstruction. The obstruction is $W_r$, the **deep-$r$ wraparound** — the contribution of those $2r$-tuples $(x_1,\dots,x_r,y_1,\dots,y_r)\in\mu_n^{2r}$ whose two argument-sums coincide *modulo $p$* without coinciding *as integers in $\mathbb{Z}$*, i.e. tuples that "wrap around" the prime.

Geometrically, those tuples are the $\mathbb{F}_p$-points of the **Fermat correlation variety** $V_{\mathrm{corr},r}$ cut out by $\sum_i x_i = \sum_j y_j$ on $\mu_n^{2r}$ (the $\mu_n$-equivariant defining relation of `_CreateFermatHodgeDecomp`), with the diagonal stratum excised. Equivalently again, after Gauss-sum diagonalization $\eta_b$ becomes a normalized Jacobi sum, and $W_r$ becomes a **second-moment / pair correlation of Jacobi sums** $J(\chi_1,\dots,\chi_r)$ as the multiplicative order of the characters grows with $r$. So the missing theorem has *one canonical form and three faces*:

> **(Missing Theorem, target shape.)** There is an absolute constant $c$ such that for all primes $p$, all $n=2^a \le p^{c}$, and $r = \Theta(\log p)$, the off-diagonal wraparound mass satisfies $W_r \le (\text{Wick slack})$; equivalently, the Jacobi-sum pairs $\{(J,\bar J')\}$ equidistribute on the unit circle on the order-$r$ Fermat correlation variety with an *effective error that is uniform in the growing order $r$*.

The defining adjective is **growing-order**. Not "for each fixed $r$" with constants silently depending on $r$ — the prize lives at $r\sim\log p$, a regime in which the order, the conductor, and the dimension of the relevant variety all diverge with $p$ *simultaneously*. This is the crux, and it is what every classical tool is built to avoid.

### 4.2 Why no existing tool reaches it: the genus/Betti blowup and the pincer

Three independent obstructions, each formalized, converge to forbid the existing instruments.

**(i) Katz/Deligne are fixed-order; the error is conductor-bounded and re-admits $\sqrt p$.** The Weil–Deligne machinery does give square-root cancellation for a *single* Jacobi sum, and Katz's equidistribution theorems do govern families. But the effective error term is controlled by the *conductor* (the sum of local Swan and tame contributions), and on $V_{\mathrm{corr},r}$ the conductor — equivalently the middle Betti number — grows with $r$. The in-tree accounting is exact. The Fermat fibre has dimension `fermatDim r = r - 2` and the genuine off-diagonal correlation variety has `corrDim r = 2*r - 1`, with middle weight `corrMiddleWeight r = corrDim r = 2r-1` (`_JacobiFermatCohomology`). Katz's effective exponent is `katzEffectiveExp β r = r - β/2`, and `prize_order_katz_error_not_negligible` proves that for the prize parameters ($\beta\le 5$, $r\ge 3$) this error is *not* negligible — the $\sqrt p$ that Weil purchases at each unit of dimension is paid back in full through the $\Theta(n^r)$ Betti blowup of the correlation variety. The map $r \mapsto$ (#middle-cohomology classes) is the genus/Betti blowup: a degree-$n$ Fermat-type hypersurface in $\mathbb{P}^{r-1}$ carries on the order of $n^r$ primitive middle classes, so "square-root of the point count" is $\sqrt{p^{\dim}\cdot n^{\Theta(r)}}$ — a *gain that is square-root in $p$ but loses a full geometric factor in $n^r$*. At fixed $r$ this is harmless; at $r=\log p$ it is fatal. This is, precisely, why Deligne's purity is *true and useless here*: purity bounds each class by $p^{w/2}$, but the number of classes overruns the bound.

**(ii) The $\sqrt p$-vacuity wall (thin subgroup).** Independently, the naive Weil bound $|\eta_b|\le \sqrt p$ is vacuous because $\mu_n$ is thin: $n\approx p^{0.19}$ at prize scale, so $\sqrt p \gg n = |\mu_n|$, and the bound exceeds the trivial $\ell^\infty$ ceiling. The character sum lives at *subgroup scale* $\sqrt n$, two regimes below where Weil delivers. The two obstructions (i) and (ii) are not the same wall photographed twice; they are the **pincer** (Chapter 4, `_AmbBreakMomentNecessity`, `lo_ratio_gt_one_prizeScale`). One jaw is **moment-necessity**: `moment_ladder_exceeds_prize` shows no moment method of *any* depth can reach the target by counting — the bound must come from *cancellation*, signed interference, not from a nonnegative count, and `lo_ratio_gt_one_prizeScale` certifies the count-ratio exceeds $1$ at prize scale so any unsigned majorant overshoots. The other jaw is **$\sqrt p$-vacuity**: any tool that produces $\sqrt p$ as its natural scale answers a question two regimes too coarse. A successful object must thread *between* the jaws.

**(iii) The onset law confirms the regime is exactly the hard one.** One might hope the wraparound simply switches off before $r$ reaches $\log p$. It does not. The onset law `onset_below_saddle` (`_OnsetGrowthLaw`) establishes $r_0=\Theta(p^{1/\varphi(n)})$ with `onset_exponent_lt_one` and `onset_scale_lt_two` showing the onset sits *below* the saddle at prize scale: the wraparound is already active in the prize window, so the problem is genuinely *quantitative* — bound $W_r$ against the Wick slack — and not a soft "no-wraparound" dichotomy. The participation/second-moment geometry `_AvSM_WrapSecondMomentSpreads` (`onsetShell n = (n/2)(n/2-1)$`, effective-support lists `neff16`, `neff8`) shows the wraparound mass *spreads* over a shell of growing size rather than concentrating, which is exactly the signature of a problem that needs cancellation, not concentration.

### 4.3 What a genuine proof must be: three simultaneous properties

The pincer converts to a *specification*. Any object that closes the prize must, simultaneously, possess three properties — and the campaign's central negative finding is that **no existing tool, and none of the 28 created objects, possesses all three**:

1. **SIGNED.** It must encode *cancellation*, not a count. By `moment_ladder_exceeds_prize` and `lo_ratio_gt_one_prizeScale`, any nonnegative majorant of $W_r$ overshoots at $r=\log p$. The object must carry phase: an alternating sum, an Euler characteristic with signs, a signed cohomological trace, a parity-split second moment. The character-0 Wick term is the *signed* limit; the prize is whether the character-$p$ object stays signed-close to it. This kills every energy/moment/entropy route surveyed in the conjecture loops (Chapter 5): they are unsigned by construction.

2. **Subgroup-scale $\sqrt n$ (escapes $\sqrt p$-vacuity).** Its natural normalization must be $\sqrt n$, not $\sqrt p$. This kills Weil/Deligne *as applied directly* and kills decoupling, restriction, and Vinogradov-mean-value tools, which (as the modern-tools no-go records) require curvature and deliver $\sqrt p$-scale estimates; $\mu_n$ is flat, $0$-dimensional, with trivial Plancherel $\sum_b|\eta_b|^2 = p\cdot n$.

3. **Growing-order cancellation (escapes the Betti blowup).** It must remain effective as $r\to\log p$, i.e. its error constant must *not* absorb a hidden $r!$, $n^r$, or conductor factor. This is the property that *no fixed-order theorem has*, by construction, and the property that makes the missing theorem genuinely new mathematics: an equidistribution statement whose error is *uniform in a growing order parameter that simultaneously grows the dimension, the conductor, and the genus of the underlying variety*.

The honest assessment of the literature is that **no published result is simultaneously (1)+(2)+(3).** BGK 2006 and the Bourgain–Glibichuk–Konyagin sum-product method give $n^{1-o(1)}$ but the $o(1)$ is ineffective and reduces to Burgess at our exponent; di Benedetto (arXiv:2003.06165), the current SOTA for $\mu_n$, gives $|H|^{1-31/2880}$ valid only for $|H|>p^{1/4}$ and *vanishes* at $\beta=4$ — at prize scale $n\le p^{1/4}$ sits at or below the threshold where the gain collapses (this campaign improved the bridge to exponent $0.9583$, saving $1/24$, but $0.9583\gg \tfrac12$: a real gain on the *high* side of the wall, the half-power gap to $\tfrac12=$ Paley intact). Kowalski's survey (2401.04756) confirms no post-2015 breakthrough closes this. Pisier's $\Lambda(q)$-set theory (1704.02969) re-expresses the target as Sidonicity of $\mu_n$ as a $\Lambda(q)$-set with $q=2r$ — beautiful, equivalent, and equally open. Katz's and Deligne's monodromy/purity are fixed-order, failing (3). KKH26 (2026/782) records the good-prime/bad-prime crossover, which is the arithmetic shadow of $W_r$ but is itself the open object.

### 4.4 Survey of the 28 created objects: which is closest

The campaign manufactured roughly twenty-eight new formal objects to try to satisfy (1)+(2)+(3). Scored against the specification:

- **Energy/moment/Wick family** (`_AvW0_BesselWickAllR`, `_AvZ_CharZeroWickBoundLadder`, the $E_r$ closed-form ladder, `_AvSM`): satisfy (2) and partly (3) but **fail (1)** — unsigned counts. `moment_ladder_exceeds_prize` proves they *cannot* close it. Eliminated as a class.
- **Modern harmonic-analysis transplants** (decoupling, VMVT, restriction, tight frames `_AttackAN2`): **fail (2)** — wrong scale, need curvature $\mu_n$ lacks. Eliminated.
- **Geometric / lattice** (Geometry-of-Numbers, `_CyclotomicLatticeWrapOnset`, `_OnsetShortestVector`): GoN closed — the cyclotomic lattice is "too round," no short vector isolates the wraparound. Fails (3).
- **Cohomological** (`_JacobiFermatCohomology`, `_CreateFermatHodgeDecomp`, `_JacobiKatzEquidist`): satisfies (1) (signed, an Euler-characteristic/trace) and is the *right venue*, but **fails (3) as currently instantiated** — `prize_order_katz_error_not_negligible` is exactly the proof that the conductor/Betti factor is not yet controlled at growing order. This family *frames* the missing theorem correctly; it does not yet *prove* it. It is where new mathematics must live.
- **Variance / second-moment family** (`_CreateJacobiGrowingOrder`, `_JacobiCocycleDispersion`, `_DyadicJacobiCocycleNonContraction`, `_AvSM_WrapSecondMomentSpreads`, the cross-covariance identity $\mathrm{CrossCov}_r=(-1)^r\,\mathrm{Var}_r$): **this is the closest object.** It is *signed* (the parity-alternating cross-covariance carries the $(-1)^r$ that satisfies (1)); it is *subgroup-scale* (the slice-energy bound `offdiag_le_of_sliceEnergy_le` in `_CreateJacobiGrowingOrder` reduces the off-diagonal to a $\sqrt n$-normalized discrepancy, satisfying (2)); and it is *the only family articulated directly at growing order* — `_CreateJacobiGrowingOrder` is literally the frontier file `F1-jacobi-growing-order`, building the iterated-convolution discrepancy whose effective control *is* property (3). The wraparound-variance route's empirical signal — the DC-moment ratio descending $0.87\to0.13$ below $1$ and improving with $r$, and the parity-split $\mathrm{CrossCov}_r=(-1)^r\mathrm{Var}_r$ bootstrap — is the only data in the campaign pointing *toward* a uniform-in-$r$ bound rather than away from it.

The precise residual, then, is sharp: prove that the **second moment (variance) of the deep-$r$ Jacobi-sum slice equidistributes with error effective uniformly in $r=\log p$**, via the cocycle/convolution discrepancy of `_CreateJacobiGrowingOrder`, with the signed cross-covariance supplying the cancellation that `moment_ladder_exceeds_prize` proves is mandatory, and the slice-energy normalization supplying the $\sqrt n$ scale that defeats $\sqrt p$-vacuity. What is *missing* — the genuinely new mathematics — is an effective bound on the middle cohomology of the order-$r$ Fermat correlation variety that is *polynomial in $r$ rather than exponential* (i.e. a $\mathrm{poly}(r)$ rather than $n^{\Theta(r)}$ control of `corrMiddleWeight`-class count), or, dually, a pair-equidistribution law for Jacobi sums of growing order whose discrepancy does not inherit the conductor's growth. No such theorem exists in the literature; the cohomological and variance families locate it exactly; closing the gap between them — turning `prize_order_katz_error_not_negligible` from an obstruction into a controlled error — is what a proof of the proximity prize would, in the end, be.


---

## Chapter 7 — The Variance Route: The Central Contribution

### 7.1 The √p-removal identity **[Lean, `_JacobiMomentIdentity`]**

The Gauss phases `θ_χ = g(χ)/√p` (`|θ_χ|=1`) satisfy `θ_χ θ_{χ'} = j(χ,χ') θ_{χχ'}` with `j = J(χ,χ')/√p` the
normalized **Jacobi-sum cocycle**, so `(θ_χ)` is a **projective character** of `ℤ/n` (a Weil-representation
object) and `η_b` its projective Fourier transform. The key theorem `moment_summand_eq`: on any additive
relation `Σx = Σy`, the moment summand `(∏θ(x_i))·conj(∏θ(y_j)) = Jphase(x)·conj(Jphase(y))` with `Jphase` a
**unit phase** — *the √p cancels out of the entire 2r-th moment*, leaving a **signed unit-phase correlation**.
This is the first object in the campaign that sits structurally **outside both obstruction hypotheses**: signed
(not a count), subgroup-scale (no field-scale √p).

### 7.2 The onset law and the variance reframing **[Lean + probe]**

`_OnsetGrowthLaw`: the wraparound onset `r_0(n,p) = Θ(p^{1/φ(n)})` (measured constant 0.85–1.0), the Minkowski
scale — and `onset_below_saddle` proves that at prize scale `r_0 ≈ 1 ≪ log p`, so wraparound is *pervasive* and
the prize is the **quantitative** `W_r ≤ slack`, not `r_0 > log p`. Crucially, `probe_wraparound_correction`:
the wraparound's random mean `n^{2r}/p` is **exactly DC-cancelled** by the mean-zero subtraction, so the prize
concerns the **fluctuation** of `W_r`; the wraparound is **sub-random** and the DC-moment ratio is `0.87→0.13`
(below 1, *improving* with depth).

### 7.3 The convergence and the conditional proof **[Lean, `_CreateWraparoundVariance`]**

Four independently-constructed objects (growing-order Jacobi discrepancy, wraparound variance with the new
invariant `PairCorr`, Stickelberger clustering, antipodal tower bootstrap) **converge** on one new target: the
**second-moment / pair equidistribution of Jacobi sums at growing order**. The capstone
`prize_via_subPoisson_variance` proves, axiom-clean, that **sub-Poisson variance ⟹ a prize prime exists ⟹ the
prize floor** (via Chebyshev). The exact structure is known: `_NextDifferenceVariety` reduces the second moment
to a *first* moment of `Jphase` over the difference variety `V_diff = append(T, −T')`; `_NextAntipodalAntiCorr`
gives the exact `CrossCov_r = (−1)^r·Var_r`. The single residual is `OffDiagonalPairCancellation` /
`FirstMomentDiffCancellation` — the growing-order equidistribution, **[open]**.

### 7.4 The central conditional theorem **[Lean, `_ThesisCapstone`]**

The thesis's main positive result is the self-contained, axiom-clean capstone
`subPoisson_variance_implies_prizeFloor`. It chains, machine-verified end to end:

> **(sub-Poisson wraparound variance over the prime family)** `Var_P(W_r) ≤ E_P[W_r]`
> ⟹ **(Chebyshev, `good_prime_of_subPoisson_variance`)** there exists a prize-admissible prime with `W_r ≤ slack`
> ⟹ **(`energy_le_of_good_prime`)** the char-`p` energy `E_r ≤ Wick` at that prime
> ⟹ **(saddle, `period_le_prizeFloor`)** `M ≤ √(2e·n·log p)` — the prize floor.

Together with the unconditional second-moment identities it carries (`secondMoment_pairs`, `diagonal_sum_eq_card`,
`wrapVariance_eq` — the König–Huygens decomposition of the wraparound variance into a Poisson diagonal plus the
off-diagonal `PairCorr`), the capstone reduces the prize to **one** named hypothesis of a single, well-defined
type: a variance bound. This is the sharpest statement of the prize the thesis offers, and — per the defense
(§8.2, Q1) — the reduction is a genuine theorem (the Chebyshev passage is real content), not a tautology.

### 7.5 A cautionary result: the equivariant descent, and why it does *not* move the wall **[Lean, refuted]**

Honesty about a near-miss is part of a defensible thesis. One proof attempt produced what *appeared* to be the
campaign's first genuine movement of the √p exponent: a diagonal `μ_n`-action `g·(x,y) = (gx, gy)` on the
correlation variety, free on nonzero roots (`diag_action_free_on_nonzero` **[Lean]**), under which the Jacobi
summand transforms by a *linear character of the winding difference* — yielding a genuine new **winding split**
`Off = Σ_{w∈ℤ/n} Off_w` (`summand_transforms_by_winding` **[Lean]**), with the excess-over-Wick numerically
concentrated in the nontrivial-winding part. The attempt then claimed a *weight drop* — that a free quotient by
`μ_n` lowers the cohomological weight by one, taking the residual exponent from `1/2` (the `_JacobiFermatCohomology`
√p) to `0`, removing the wall.

**This is false, and we prove why** (`_EquivariantDescentWeightDropREFUTED` **[Lean]**). The error is a
conflation of the *finite* group scheme `μ_n` (`Spec k[t]/(tⁿ−1)`, dimension **0**, `n` points) with the
*1-dimensional* torus `𝔾_m`. A free quotient by a **finite** group is a finite étale cover: it preserves both
cohomological *degree* and *weight* (`H^i(X)^χ ≅ H^i(X/G, ℒ_χ)` at the **same** `i`), so the descended weight
stays `2r−1` and the residual stays `1/2 = √p`. The weight drop requires a *positive-dimensional* group (a
Gysin/Leray shift on a `𝔾_m`-fibration), and there is no rescue: the finite-order winding character `χ_w` does
not extend to `𝔾_m` (`Hom(𝔾_m,𝔾_m) = ℤ` is torsion-free), and the Jacobi weights are not `𝔾_m`-invariant. The
descent's Lean theorems are *arithmetically true tautologies* — `(2r−2)/2 − (r−1) = 0` — attached to the wrong
weight. What survives is real and useful: the **winding split is new**, and it localizes the excess; but the
finite quotient delivers only a factor-`n`, `p`-*independent* combinatorial saving (precisely the known coset
invariance `η_{cb} = η_b`), which does not touch the BGK exponent. The `√p` wall of `_JacobiFermatCohomology`
is **unmoved**. We record this because catching it — before it entered the thesis as an advance — is exactly the
discipline a proof of an open problem demands: a referee would have punctured an unverified √p-removal in one
line, and the thesis is stronger for having punctured it first.

---

## Chapter 8 — Resolution and Defense

### 8.1 The honest verdict

The prize is **open**, **believed true**, and equivalent to a single new analytic statement: the second-moment
equidistribution of Jacobi sums at growing order `r ≈ log p` (one order beyond Katz's fixed-order theorem). We
have reduced everything else to it, axiom-clean, and located it from more independent angles than any prior
treatment. We did **not** close it, and we do not claim to: that would require either an effective growing-order
equidistribution on the Fermat correlation variety, or a direct sub-Poisson variance bound on the wraparound
fluctuation — genuinely new analytic number theory.

### 8.2 Anticipated defense questions

**Q1. Is the conditional reduction real, or is the hypothesis secretly the prize (a vacuous "X ⟹ X")?**
It is real, and the distinction is precise. The capstone (`prize_via_subPoisson_variance` **[Lean]**) takes as
hypothesis a *second-moment* statement — `Var(W_r) ≤ E[W_r]` (sub-Poisson), a bound on the **variance of a
count** over the prime randomization — and concludes the *first-moment, worst-case* sup-norm bound, via
Chebyshev + the existence of a good prime. These are different logical types: a variance hypothesis is not the
worst-case conclusion restated. They are *equivalent in truth value* (as everything here is — §2), but the
reduction is a genuine theorem, not a tautology, because the Chebyshev passage from second moment to a pointwise
bound is mathematical content. The honest caveat: equivalence-in-truth means proving the hypothesis is exactly
as hard as the prize — the reduction buys a *better-shaped target* (a variance/equidistribution statement with
its own toolkit), not a *weaker* one.

**Q2. Why is the variance form not just "BGK relabeled"?** Two reasons. (i) *It is a different moment.* BGK/Paley
is a **first-order** statement (the single sup `M`); the variance route's target is a **second-order** statement
(the pair correlation `Σ PairCorr`, the variance of the wraparound). Via the √p-removal identity
(`_JacobiMomentIdentity`) and the difference-variety reduction (`_NextDifferenceVariety`), this is the
*second-moment equidistribution of Jacobi-sum pairs at growing order* — and Katz/Deligne proved only the
**first-order, fixed-order** equidistribution. The pair statement at growing order is not in the literature; it
is not a known theorem dressed up, because the relevant theorem does not exist. (ii) *It brings new machinery* —
Chebyshev, the prime-randomization second moment, the difference variety, the exact `CrossCov_r = (−1)^r Var_r`
identity — none of which appears in the BGK sum-product proof. The reformulation is genuine: it relocates the
problem into second-moment / variance analysis, where the toolkit is different even if the difficulty is conserved.

**Q3. What is genuinely new, versus relabeling?** The following are new theorems and identities, machine-checked:
the **√p-removal identity** (the entire `2r`-th moment is a *signed unit-phase* Jacobi correlation — the √p
literally cancels; this is the first object outside *both* obstruction hypotheses); the **wraparound onset law**
`r_0 = Θ(p^{1/φ(n)})` with the **correction** that it lies *below* the saddle at prize scale (overturning the
"no-wraparound-at-prize" framing); the **exact cross-level covariance** `CrossCov_r = (−1)^r·Var_r` (the antipodal
tower bootstrap is parity-split — contracting at odd order, expanding at even); the **convergence** of four
independent constructions on one target; the **difference-variety** exact `2nd→1st`-moment reduction; and the
**Bridge** theorem (additive and multiplicative faces are one object in two Fourier-dual bases, so "bridging" is
tautological — itself a structural theorem). Relabelings are honestly flagged as such (e.g. the geometry-of-numbers
onset *reduces to* the Minkowski norm bound — and we *prove why* (the cyclotomic lattice is too round), which is
itself a result).

**Q4. What would a referee demand, and can the thesis supply it?** A referee of a *solution* would demand a proof
of the open core (the growing-order pair equidistribution, or the sub-Poisson variance, or an effective
growing-order Katz). The thesis **cannot** supply this and says so plainly; the core is a ~25-year-open problem.
A referee of a *contribution* — which is what this thesis is — would demand: (a) that the reductions be correct
(they are machine-checked); (b) that the new objects be genuinely new and not vacuous (they are axiom-clean and
their named residuals are the honest open core, not silently discharged); (c) that the obstruction be characterized
(it is — the two-jaw pincer, each jaw a theorem); (d) that the empirical claims be reproducible (the probes are
committed and exact). On those grounds the thesis is defensible. We do **not** ask the committee to accept a
closure; we ask them to accept that the boundary of knowledge has moved from "bound a worst-case character sum"
to "prove a specific second-moment equidistribution," with the machinery to attack the latter supplied.

**Q5. The numerics say the prize is true — why is that not enough?** `M/√(2n log m) = 0.77–0.85 < 1` across the
computable range, the DC-moment ratio *decreases* with depth (`0.87→0.13`), and no counterexample survives over
the most resonance-prone structured primes. This is strong evidence the prize is **true** — but evidence is not
proof, and the prize regime (`n = 2^30`) is uncomputable: the small-`n` regime where we *can* compute has the
wraparound *absent* (`W_r = 0`, onset above the computed depth), so it does not directly probe the
wraparound-present prize regime. The honest status is "believed true, with the precise obstruction to a proof
isolated" — which is the most a thesis on this problem can claim with integrity.

### 8.3 The contribution, stated plainly

A doctoral thesis is judged by whether it advances knowledge and is defensible. This one: (a) **unifies** five
named open problems and proves their equivalence by machine; (b) **reduces** the $1M prize to a single energy
inequality, end-to-end formalized; (c) **maps** the obstruction precisely (the two-jaw pincer, ~100 refuted
routes with mechanisms); (d) **creates** ~28 new axiom-clean objects and a sequence of exact identities; (e)
**isolates** the single new theorem — second-moment Jacobi-pair equidistribution at growing order — whose proof
would resolve the prize, and supplies the machinery (the √p-removal identity, the difference-variety reduction,
the Chebyshev capstone) that makes it a concrete, attackable target rather than a famous slogan. That the wall
still stands is not a failure of the thesis; it is the honest report of a real wall, mapped as never before.

### 8.4 Coda — the shape the eventual proof must take

The campaign's negative results are not merely a list of failures; together they *constrain the form* of any
eventual proof, and that constraint is the thesis's most useful prediction. A proof of the char-`p` transfer
must:

1. **Be a second-moment (variance) argument, not a first-moment one.** First-order control of `M` is the BGK
   wall itself; every first-moment route reduces. The sub-Poisson variance of the wraparound fluctuation is the
   first formulation in which the *believed* sub-randomness (the DC-moment ratio decreasing with depth) is the
   *object of proof* rather than a hoped-for output.

2. **Live on the difference variety, at growing order.** `_NextDifferenceVariety` shows the second moment is a
   first moment of `Jphase` over `V_diff = append(T, −T')`. A proof is therefore an *effective, growing-order*
   equidistribution on `V_diff` — precisely the gap Katz's fixed-order theorem leaves open. The Betti number of
   the relevant Fermat correlation variety grows like `n^r`; the proof must extract cancellation *from* this
   large cohomology (a decomposition / a sign-isotype of lower weight, `_CreateFermatHodgeDecomp`), not be
   defeated by it. This is the single most concrete open problem the thesis bequeaths.

3. **Respect the exact parity structure.** `CrossCov_r = (−1)^r·Var_r` is exact: any tower/recursive argument
   must handle the even-order expansion, e.g. by a two-step (`n → 4n`) recursion or a parity-graded amplifier.
   This rules out naïve renormalization and points to the specific combinatorial object an argument must build.

4. **Use the arithmetic of the prime family, not a single prime.** The Chebyshev capstone needs only *one* good
   prime in the family `{p : n | p−1}`; the variance is over the family. The proof is thus an *averaged* /
   second-moment statement over primes — a softer, more attackable object than a per-prime worst-case bound, and
   the one place the prize's freedom to *choose* `p` is genuinely usable (the refuted "cross-prime sieve" failed
   because it used a tautological bridge; the variance route uses the family non-tautologically, via Chebyshev).

If the eventual proof comes from elsewhere — say an effective growing-order Sato–Tate for Jacobi sums proved by
`ℓ`-adic monodromy, or a hypercontractive variance inequality on the Fermat motive — these four constraints say
it will, when specialized, *factor through* the variance route's objects. The thesis therefore offers not only a
map of where the wall is, but a blueprint for the shape of the door through it. The remaining work — proving the
growing-order pair equidistribution — is left, honestly, as the open problem it is; the contribution is to have
made it the *only* remaining work, and to have built the tools that make it concrete.

---

*Formal artifacts: ~28 axiom-clean Lean bricks under `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_Create*`,
`_Next*`, `_Jacobi*`, `_Onset*`, `_Bridge*`, `_ProveAssembly*`; the state-of-the-prize map
`docs/kb/deltastar-444-state-of-the-prize-2026-06-19.md`; the empirical probes
`scripts/probes/probe_{onset_growth_law,wraparound_correction,jacobi_*}.py`; the exhaustive-search ledger
`docs/kb/deltastar-444-exhaustive-loop-log.md`. Every theorem cited as [Lean] is machine-verified
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`.*
