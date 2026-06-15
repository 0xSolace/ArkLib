# 100 alien ideas for the δ\* open core M(μ_n) — sum-product / Stepanov sweep + top-8 stabs (#444, 2026-06-15)

> **The genuine open core (pinned, intrinsic — relocation is proven futile this campaign):**
> `M(μ_n) := max_{b≠0} | Σ_{x∈μ_n} e_p(b·x) |`, where `μ_n` = the 2-power multiplicative subgroup
> of `F_p*` (`n = 2^μ`, `n | p−1`). **Target (the prize floor):** `M(μ_n) ≤ C·√(n·log(p/n))`.
> **Regime:** `p` prime `~ n^β`, `β ∈ [4,5]` (`n < p^{1/4}`, `n ≪ √p`), `m = (p−1)/n` the index,
> prize `n ~ 2^30`. **Known:** trivial `M ≤ n`; `L²`-average `= √n` exactly (Parseval); SOTA in
> this regime is `M ≤ n^{1−o(1)}` (Bourgain–Glibichuk–Konyagin, **ineffective**); di Benedetto
> `n^{0.989}` needs `n ≥ p^{1/4}` (outside prize); Weil/`√p` vacuous (`n ≪ √p`). **The gap to
> close:** from exponent `1−o(1)` down to `1/2`.

> **`M(μ_n)` IS, verbatim:** the non-principal spectral radius of `Cay(F_p, μ_n)`; the largest
> cyclotomic Gauss period of order `m`; an incomplete/short character sum over a thin subgroup; the
> peak structure-factor of `{e_p(x): x∈μ_n}` on the unit circle; the max cross-correlation of a
> Gauss-sum sequence family; the mutual coherence of the cyclotomic frame; a short
> Kloosterman/Gauss exponential sum.

> **Honesty contract.** Everything below is **exploration**. The 8 leading entries were stabbed
> (agent-attacked + adversarially verified, probes committed to `scripts/probes/`); their verdicts
> are reported faithfully. The remaining 92 are **un-stabbed proposals** grouped by lens — many are
> likely false, each is a falsifiable target, none is claimed proven. The campaign-wide DEAD list
> (do **not** re-propose as-is) is restated below so the catalog does not regress.

## DEAD families (campaign-proven futile — restated, do not re-propose as-is)

- plain Weil (vacuous `n < √q`); plain Stepanov (`n^{2/3}`); **all** additive-energy / moment
  methods (forced anomaly past `r = β+1`, cap at Johnson; the conservation law — every even moment
  is phase-blind to the argmax); ineffective BGK as-is; di Benedetto (wrong regime `n ≥ p^{1/4}`);
  Mahler / flat-Littlewood; antipodal / Mann (= the boundary only); **relocation** to
  parameter / `p`-adic / entropy (Terwilliger op-norm `= M` exactly; dilation action amenable;
  `p`-adic tower period is a unit; chaining metric entropy `= Θ(log q)`).
- **Pre-screen rule (from I025/I027):** if a candidate's load-bearing input is an even moment / `L⁴`
  / autocorrelation / merit-factor / additive-energy quantity, it is the wrong **direction** by
  construction (lower bound on coherence, or class-`2k` average blind to the sup). Reject before
  probing.

---

# THE STABBED TOP 8 (verdicts, with committed probes)

Lenses touched: `expander-near-ramanujan`, `compressed-sensing-coherence`, `stepanov-2adic`
(×3), `sequence-correlation` (×2), `effective-sumproduct`. One real handle (`I031`).

### I031 — Group-invariant Dudley chaining on the dilation **quotient** (compressed-sensing-coherence) — **PROMISING-PARTIAL ★ (HANDLE)**
- **New lemma.** `|X_b| = |Σ_{x∈μ_n} e_p(bx)|` is **exactly** dilation-invariant (`b ↦ ζb`,
  `ζ∈μ_n`), so `M` is a sup over only `m = (p−1)/n` orbit representatives. Chain over the
  **quotient** `F_p*/μ_n`, not the full index, collapsing the chaining entropy from `log p` (the
  wall) to `log(p/n)`.
- **Verified (probes, machine precision, proper regime `n=4..64`, `p` prime, `n|p−1`, `p≫n³`,
  `m>1`, never `n=p−1`):** orbit invariance exact (`probe_i031_orbit_invariance.py`); full-set
  `maxlogN/logp = 1.000` (wall) vs quotient `≈0.58–0.66 ≈ log m/log p` (`probe_i031_fullset_vs_quotient.py`);
  quotient `γ₂` slope `log(γ₂q)` vs `log(log m)` `= 0.41 ≤ 1/2` at fixed `n`
  (`probe_i031_dudley_exponent.py`) — recovers the **floor exponent 1/2 in `log(p/n)`**, not BGK
  `1−o(1)`.
- **The remaining open content (shrunk, not closed).** The random sub-Gaussian model with the
  Gauss-period covariance provably obeys the floor `E sup|G| ≤ C√(n log m)` (KMR / Rudelson–Vershynin
  RIP; `rand/floor = 0.74–0.95`), and the deterministic `M` is a **bounded, stable** factor
  `M/rand ~ 1.3–1.4` above it (`probe_i031_det_vs_random_transfer.py`). No theorem currently supplies
  the deterministic→random transfer (Maurey gives a good row-subset, not sup equality), and the
  constant `C = M/floor` creeps `1.07 → 1.36` over `n=4..64` with `maxlogNq/log m → 1`.
- **Verdict: HANDLE — the open problem shrinks from the full BGK exponent gap to a bounded-constant
  deterministic→random sup transfer for one specific cyclotomic frame.** See MOST PROMISING LEADS.

### I037 — Bordenave non-backtracking trace on the character-weighted period multigraph (expander-near-ramanujan) — **NO-GAIN**
- **Claim.** Catalan-not-Wick suppression of the non-backtracking (Hashimoto) spectral radius gives a
  near-Ramanujan bound below `M`.
- **Found.** (1) UNWEIGHTED `Cay(F_p,μ_n)`: the non-principal Hashimoto eigenvalue reconstructs
  `M = μ₊ + (n−1)/μ₊` **exactly** (Ihara–Bass makes NBT a deterministic reparametrization of `M` —
  zero new info; `2.5638→3.7339` at `n=4`, `5.2219→6.5624` at `n=8`). (2) The char-weight
  `w(x,y)=χ(x−y)` does break the tie and gives a recovered bound numerically **below** `M₀`, but it
  brackets the **twisted** period `M_χ = max_b|Σ χ(u)e_p(bu)|`, a **different** sum than the prize
  `M`. (3) Catalan-vs-Wick is real but on the wrong matrix (NBT moments `T₄=0.59 ≪ C₄=14 ≪ Wick 105`,
  adjacency moments track Wick). **Fatal logic:** minimizing `ρ(B_χ)` over `χ` minimizes `M_χ`; a
  number `< M₀` cannot upper-bound `M₀`; the bridge `ρ(A)≤ρ(B)+1/ρ(B)` is a theorem only unweighted,
  where it reconstructs `M` exactly. No weighted bridge to the untwisted `M` exists.
- **Verdict: NO-GAIN** — multiplicative-weight relocation changes the sum being bounded
  (proven-futile relocation pattern). `probe` committed (`5326fd999`).

### I006 — q-difference (Jackson) confluent Stepanov: μ_n is one D_ζ-orbit (stepanov-2adic) — **REFUTED**
- **Found.** The q-confluent kernel collapses on its own orbit; a derivation cannot make multiplicity
  where it has a single orbit. `probe_i006_qdifference_stepanov.py`.
- **Verdict: REFUTED.** Abandon orbit-derivation Stepanov. Any Stepanov vanishing must come from a
  **second, transverse** structure not invariant under `X↦ζX` (e.g. across **levels** of the tower
  `μ_2 ⊂ μ_4 ⊂ … ⊂ μ_n`), not within a single orbit.

### I008 — Walsh / Haar-packet dyadic-tower auxiliary (stepanov-2adic) — **NO-GAIN**
- **Claim.** `Q = ∏_{i=1}^{μ}(X^{2^{i−1}} − s_i)` accumulates vanishing across `log n` levels.
- **Found.** Exact closed-form (vs sympy): each factor has a **unit** derivative at `x₀∈μ_n`, hence a
  **simple** root; `mult_Q(x₀) = #{i: s_i = x₀^{2^{i−1}}}`, a count of order-1 contributions. Stepanov
  needs **common** multiplicity `M`: `M·|Z| ≤ Σ_i gcd(2^{i−1},n) = n−1 = deg Q` — exactly the trivial
  degree bound. Exhaustive shift-vector search: best common multiplicity `= 1` (wanted `log n`).
  Recovered `M`-exponent `0.95–0.97` (sitting at BGK SOTA the idea claimed to beat).
  `probe_i008_walsh_dyadic_stepanov.py`.
- **Verdict: NO-GAIN.** Separability of `X^n−1` (char `p`, `p∤n`) forbids any auxiliary order-2 contact
  on `μ_n` at sub-`(M·n)` degree. The only un-refuted residual of the family: a **multivariate**
  Stepanov over the dyadic-digit coordinate ring (`x↦x²` digit recursion), not univariate in `X`.

### I001 — Artin–Schreier additive (Ore) auxiliary Stepanov (stepanov-2adic) — **NO-GAIN**
- **Claim.** An Ore/additive polynomial vanishing on `μ_n` with `μ = log₂ n` Frobenius–Hasse
  derivatives gives `|μ_n ∩ Z(L)|·(μ+1) ≤ deg L` via a Moore-minor rank-defect `≥ μ`.
- **Found (FALSE every reading; 4 sub-tests, `probe_i001_ore_moore_frobenius_stepanov.py`).**
  (1) An Ore poly is `F_p`-linear; `Z(L)` is an `F_p`-subspace; `μ_n ⊂ F_p` is **1-dimensional** over
  `F_p`, so the only Ore poly vanishing on `μ_n` is `X^p−X` (degree `~q`, vacuous); Frobenius is the
  identity on `F_p`. (2) The `(μ+1)`-Hasse-jet matrix is **full rank**, defect `= 0` (separability),
  cancelled exactly by the `(μ+1)`-fold degree cost ⇒ count `≤ n`. (3) The Moore matrix `[a_i^{p^j}]`
  over `F_p` has rank 1 (Frobenius collapse) — the wrong defect; the genuinely full-rank object is the
  exponent/character Vandermonde already used by Parseval. (4) Best `M`-bound = trivial `n`.
- **Verdict: NO-GAIN.** Root cause: `μ_n ⊂ F_p` is 1-dim over `F_p` AND `X^n−1` separable ⇒ no
  additive/Frobenius multiplicity `>1` to manufacture.

### I012 — Subgroup-trilinear: kill the p^{1/4} in di Benedetto (effective-sumproduct) — **REFUTED**
- **Claim.** Beukers–Smyth cyclotomic incidence in `μ_n³` removes the `p^{1/4}` from
  Petridis–Shparlinski's trilinear bound.
- **Found (read di Benedetto arXiv:2003.06165 + exact probe, `probe_i012_subgroup_trilinear.py`).**
  (A) **DIRECT reading is circular:** `μ_n` mult-closed ⇒ `xyz` ranges over `μ_n` with constant
  multiplicity `n²`, so `T(a) = n²·η_a` **exactly**; product-energy `E_prod(μ_n³)=n^5` (maximally
  coset-concentrated, opposite of the wanted `Θ(n)` isolated incidences). The lemma `|T|≤n^{2+1/4−η}`
  is literally `|η|≤n^{1/4−η}` — **stronger** than the prize, and FALSE as stated (`M=7.56/13.30/22.98`
  for `n=8/16/32 ≫ n^{1/4}`). (B) **di-Benedetto reading has a factually wrong premise:** Lemma 4.1 is
  fed additive **sumsets** `{x₁+x₂+x₃}` and a **difference** set `{z₁−z₂}`, NOT multiplicative tori
  (measured fraction inside `μ_n`: `8.3%/2.3%`, `0%/0%`). The `p^{1/4}` is a field-size term, not a
  collinear-triple count.
- **Verdict: REFUTED** (logged to `DISPROOF_LOG.md`, committed `c8f0af3e3`). Mult-closure makes any
  all-subgroup product-form collapse to `n²·η` (circular).

### I025 — Levenshtein weighted higher-moment bound on the cyclotomic correlation family (sequence-correlation) — **NO-GAIN**
- **Found.** (1) **DIRECTION (fatal):** Welch/Levenshtein/Delsarte-LP are **lower** bounds on family
  max-coherence given size (LP duality); the prize needs an **upper** bound on the fixed family `μ_n`.
  Measured family-Welch `2.68/3.88/5.57 ≤ M = 6.86/10.94/17.25`. (2) The only valid upper-bound reading
  is Markov `ν_{b*}·M^{2k} ≤ Σ_b ν_b|η_b|^{2k}`; the best legitimate over-weight bound is always `≥M`,
  reaching `M` only once all mass concentrates on the worst coset (= knowing argmax), never `√n`. The
  over-weight step **is** the forbidden `L^∞`-from-moments step.
  `probe_levenshtein_weighted_moment_I025.py`, `probe_levenshtein_kernel_I025b.py`.
- **Verdict: NO-GAIN** (same Welch-`√n` trap).

### I027 — PAPR↔merit-factor duality (sequence-correlation) — **NO-GAIN**
- **Found.** Established the exact Jedwab/Borwein–Lockhart identity `‖p‖₄⁴ = N²(1+1/F)`: bounded merit
  factor = bounded `L⁴/L²` ratio (a 4th-moment flatness statement). **Premise TRUE** (coset spectrum
  is `L⁴`-flat, `L⁴/L²=1.267–1.325`, `L²=√n` exactly) but `M = L^∞(η)` is **not** controlled by it
  (`M/√n = 2.43–5.15` grows; `(M/√n)/√log m` drifts up, no stabilization). **Parameter-free kill:**
  holding the spectrum at the real merit factor (`ρ₄=3`), bounded merit allows `L^∞` up to `~(mn)^{1/4}
  ~ n^{1.75}`; `(allowed L^∞)/√(n log m)` grows as a power of `n` (`2.30 → 6043` at `n=2^20`). So
  bounded merit factor is **consistent with `M` up to `~n^{1.75}`**.
  `probe_papr_merit_duality_I027.py`, `_I027b.py`, `_I027c.py`.
- **Verdict: NO-GAIN** (class-4 average, blind to the sup — same wall as I025).

**Stab scoreboard:** 1 HANDLE (I031), 2 REFUTED (I006, I012), 5 NO-GAIN (I037, I008, I001, I025,
I027). All probes proper-regime; refutations logged.

---

# THE 100 IDEAS, GROUPED BY LENS

Tags: `[Φ]` phase/sign · `[π]` non-archimedean (2-adic) · `[H]` entropy/rare-event · `[SP]` effective
sum-product/structural · `[X]` cross-domain transfer. Status: `★` = stabbed-this-sweep (see above) ·
`☆` = un-stabbed live proposal · `†` = pre-screened DEAD (restated to prevent regression).

## Lens 1 — effective-sumproduct (quantified BGK exponent; family (i))

1. **I012 ★†** subgroup-trilinear / Beukers–Smyth kills `p^{1/4}` — REFUTED (circular: `T=n²η`).
2. **☆ [SP]** Quantified Stepanov-feed into BGK: replace BGK's ineffective `δ`-iteration with an
   explicit `n^{2/3}` Stepanov seed and count growth steps `≤ log m` ⇒ explicit exponent — *new
   lemma:* growth of `μ_n` under `+` has effective doubling `|μ_n+μ_n| ≥ c·n^{1+κ}` with quantified
   `κ` from the 2-power gcd structure.
3. **☆ [SP]** Konyagin–Shkredov explicit `T₃(μ_n) ≤ n^{3−c}` with **named** `c` for 2-power subgroups
   (the third-multiplicative-energy growth, effective version).
4. **☆ [SP]** Rudnev point-plane with the 2-power constraint baked into the plane family
   (incidences of `{(x, y, xy): x,y∈μ_n}`) — *non-circular only if* planes come from off-torus sums.
5. **☆ [SP]** Murphy–Petridis–Roche-Newton–Shkredov–Vinh "few-sums-many-products" effective form
   restricted to `n=2^μ` (do the 2-power gcds give a better Plünnecke exponent?).
6. **☆ [SP]** Shkredov's `|μ_n − μ_n|` lower bound `≥ n^{1+ν}` with explicit `ν(β)` — feed into
   Garaev's `max|η_b|² ≤ p·n / |μ_n−μ_n|` style inequality at quantified strength.
7. **☆ [SP]** Bourgain–Garaev explicit sum-product exponent for subgroups of size `< p^{1/4}` with
   the constant tracked — the one regime where di Benedetto **fails** but quantification may survive.
8. **†** di Benedetto `n^{0.989}` directly — wrong regime (`n ≥ p^{1/4}`).
9. **†** ineffective BGK `n^{1−o(1)}` as-is — `o(1)` not quantified (the named open Prop).
10. **☆ [SP]** Effective Balog–Wooley decomposition of `μ_n` into a low-energy `+` part and low-energy
    `×` part with explicit thresholds (the 2-power subgroup is `×`-perfect ⇒ all energy is `+`-side).

## Lens 2 — stepanov-2adic (auxiliary vanishing at bad frequencies; family (ii))

11. **I001 ★†** Artin–Schreier / Ore additive auxiliary — NO-GAIN (`μ_n` 1-dim over `F_p`).
12. **I006 ★†** q-difference (Jackson) confluent Stepanov — REFUTED (single-orbit collapse).
13. **I008 ★†** Walsh / dyadic-tower product auxiliary — NO-GAIN (all roots simple, trivial bound).
14. **†** plain confluent Stepanov with Hasse multiplicities — stalls at `n^{2/3}` (W3).
15. **☆ [π]** **Multivariate** Stepanov over the dyadic-digit coordinate ring (the one un-refuted I008
    residual): lift `x∈μ_n` to its digit vector under `x↦x²`, build a bivariate auxiliary whose
    multiplicity comes from the **digit recursion**, not univariate tangency.
16. **☆ [π]** Tower-transverse Stepanov: auxiliary vanishing across **levels** `μ_2⊂μ_4⊂…⊂μ_n`
    (each level's value-condition genuinely new; transverse to the `X↦ζX` orbit that killed I006).
17. **☆ [π]** Hensel-lifted auxiliary in `Z_2[[T]]`: build the vanishing in the 2-adic completion of
    the cyclotomic tower, then reduce — *risk:* A4 showed the tower period is a `b`-independent unit.
18. **☆ [π]** Carlitz/Drinfeld-module analogue auxiliary (additive `F_p[T]`-module multiplicity in
    place of Frobenius) — sidesteps the rank-1 Moore collapse that killed I001.
19. **☆ [π]** Mahler-basis auxiliary using `binom(x,2^i)` digit functions — *risk:* Mahler/flat-
    Littlewood is on the DEAD list; only viable if vanishing (not flatness) is the lever.
20. **☆ [SP]** Garcia–Voloch / Heath-Brown–Konyagin 2-variable count `|G ∩ (G+λ)| ≤ 4|G|^{2/3}` used
    as a Stepanov **degree** input rather than an energy input — *risk:* reduces to additive energy.

## Lens 3 — compressed-sensing-coherence (mutual coherence / RIP / chaining)

21. **I031 ★** Group-invariant Dudley chaining on the dilation quotient — **HANDLE** (floor exponent
    1/2 recovered; open piece = deterministic→random sup transfer; bounded constant `M/floor~1.4`).
22. **☆ [H]** Deterministic-to-random transfer theorem for the cyclotomic Gauss-period frame: prove
    `M ≤ C·E sup_b|G_b|` (the isolated I031 residual). *Sub-target 1:* covering-number bound
    `log N(F_p*/μ_n, d_q, ε) ≤ log(p/n)` + a chaining lemma that the deterministic sup `≤ √n·γ₂ + excess`.
23. **☆ [H]** Push the I031 constant probe to `n=128,256` at fixed thin `β` (numba/GPU; orbit-rep
    enumeration is `O(p)`) to test whether `M/rand` stays bounded or eventually grows.
24. **☆ [H]** Welch-bound-improving frame argument: the cyclotomic frame is **not** equiangular;
    bound its worst coherence via a Gerzon/Levenstein **gap** above the Welch floor — *risk:* Welch is
    a lower bound (I025 direction trap), only the **excess** is exploitable.
25. **☆ [H]** Talagrand `γ₂`-functional majorizing measure on the quotient with the **exact**
    Gauss-period increment metric `d(b,b') = √(Σ|η_b−η_{b'}|²)`-type — does the metric have dimension
    `log m` not `log p`?
26. **☆ [H]** Restricted-isometry of the partial cyclotomic DFT (rows `= μ_n`-orbit reps): if the
    `m×n` submatrix has RIP-`δ`, then `M ≤ √n(1+δ)` deterministically — verify `δ` is bounded.
27. **☆ [H]** Bourgain–Tzafriri restricted-invertibility on the quotient frame (extract a large
    near-orthonormal column set, bound the residual).
28. **☆ [H]** Chevet / Gordon's min-max for the deterministic sup via a Gaussian comparison with the
    **exact** covariance `Σ_{b,b'} = ⟨η_b, η_{b'}⟩` (not the random surrogate).

## Lens 4 — sequence-correlation (cross-correlation / merit factor / Welch)

29. **I025 ★†** Levenshtein weighted higher-moment — NO-GAIN (lower-bound direction; argmax-encoding).
30. **I027 ★†** PAPR↔merit-factor duality — NO-GAIN (bounded merit ⇏ `M=O(√(n log m))`; allows `n^{1.75}`).
31. **†** plain Welch / Sidelnikov bound — lower bound on family coherence (wrong direction).
32. **†** Delsarte LP / Boyd merit factor — `L⁴` flatness, sup-blind.
33. **☆ [Φ]** **Signed** cross-correlation discrepancy: the prize `M` = max over phases; track the
    **sign pattern** of the partial-sum walk `S_k = Σ_{x∈μ_n, x<k} e_p(bx)`, not `|S|²` — does the
    sign-balanced walk have a `√log`-bounded maximal excursion (law-of-iterated-logarithm flavor)?
34. **☆ [Φ]** Rudin–Shapiro-style flat-correlation construction restricted to `μ_n` — *risk:* Rudin–
    Shapiro flatness already REFUTED in-tree (`deltastar-rudin-shapiro-flatness-REFUTED`).
35. **☆ [Φ]** Aperiodic vs periodic autocorrelation gap of the `μ_n`-indicator sequence — the prize is
    the **aperiodic** sup; periodic is Parseval-`√n`; is the gap `√log`?

## Lens 5 — expander-near-ramanujan (spectral graph / trace method)

36. **I037 ★†** Bordenave NBT on char-weighted period multigraph — NO-GAIN (weighted bridge bounds `M_χ`).
37. **†** unweighted near-Ramanujan / Ihara–Bass on `Cay(F_p,μ_n)` — `M` IS the non-principal radius;
    NBT is exactly Ihara–Bass, zero new info; trace moments = the Johnson-capped energy ladder (W2).
38. **☆ [Φ]** Friedman/Bordenave **second-eigenvalue concentration** for the *random* lift of
    `Cay(F_p,μ_n)`, then a deterministic→random transfer (same shape as I031, different vehicle).
39. **☆ [Φ]** Kesten–McKay vs empirical-spectral-distribution **tail**: the prize is the **edge** of
    the spectrum (`λ₂`), a tail event; bound it via a tail large-deviation for the period spectrum,
    not the bulk moments — *risk:* tail LDP needs the very phase info moments lack.
40. **☆ [Φ]** Murty–Wong / Lubotzky-style explicit spectral gap for the **abelian** Cayley graph using
    that the dilation group is `Z/m` acting — *risk:* A8 showed dilation is amenable (no expansion).
41. **☆ [SP]** Cayley graph **girth × spectral-gap** tradeoff: `μ_n` gives a specific girth; does the
    Alon–Boppana floor leave room for `λ₂ = √(n log m)` (between Ramanujan `2√(n−1)` and trivial `n`)?

## Lens 6 — geometry-of-numbers / lattice (the point set on the circle)

42. **☆ [Φ]** Structure-factor / diffraction peak of `{e_p(x):x∈μ_n}` on `S¹`: bound the peak via the
    **Beurling–Selberg** extremal majorant of the indicator (sharp `L¹`→`L^∞` for exponential sums).
43. **☆ [Φ]** Erdős–Turán inequality applied to the equidistribution defect of `μ_n` mod 1 — gives
    `M ≤ Σ_{k≤K} |η_k|/k + p/K`; the prize is whether the **truncated** discrepancy sum is `√(n log)`.
44. **☆ [H]** Montgomery's "repulsion of large values" / large-values theory for Dirichlet polynomials
    transplanted to the period sequence (`η_b` are values of a Dirichlet-poly-like object).
45. **☆ [SP]** Cyclotomic lattice collision: `M` large ⇔ many `x∈μ_n` cluster in a short arc `[b, b+p/n]`
    ⇔ a short vector in the lattice of `μ_n`-differences; bound short vectors via the 2-power structure
    of the difference lattice (`deltastar-cyclotomic-lattice-collision-core` in-tree).
46. **☆ [Φ]** Favard length / self-similar projection of the 2-power Cantor-like set `{x^{2^i}}` —
    *risk:* `deltastar-favard-length-selfsimilar-route` exists in-tree, likely already triaged.
47. **☆ [H]** Selberg's sieve / large sieve on the orbit reps to bound the number of `b` with
    `|η_b| > T`, then sum — *risk:* large-sieve dimension obstruction noted in-tree (`deltastar-407-large-sieve-dimension-obstruction`).

## Lens 7 — automorphic / theta / modular (the relocation tier — high-risk)

48. **†** automorphic sup-norm / theta-sum lens — quadratic-vs-geometric wall confirmed (`b3c79a23f`).
49. **☆ [Φ]** Horocycle-lift sub-idea (noted live in `b3c79a23f`): lift the geometric phase `e_p(bx)`,
    `x∈μ_n` to a **horocycle** integral and use sup-norm bounds — the one un-killed automorphic residual.
50. **†** Hejhal/Sarnak quantum-unique-ergodicity sup-norm — wrong (quadratic) phase.
51. **†** Eisenstein/Maass period = Gauss period reduction — relocation, period is the wall.
52. **☆ [X]** Subconvexity for the relevant `L`-function (the period generating Dirichlet series) —
    *risk:* needs open NT/GRH input (`✗inc`); only catalogued for completeness.

## Lens 8 — entropy / information / rare-event (the [H] tier)

53. **†** generic chaining on the full `u₀`-process — REDUCES-TO-WALL (`Θ(log q)`; the I031 fix is the quotient).
54. **†** Croot–Sisask almost-periodicity — REFUTED (`M/(2avg) ~ √log`, reproduces floor excess).
55. **†** entropy-compression — runs backwards (lower-bounds the list).
56. **☆ [H]** Bobkov–Götze / transport-entropy concentration for the **deterministic** phase sum read
    as a function on the orbit-quotient with a log-Sobolev constant from the 2-power structure.
57. **☆ [H]** Maximal-inequality for the lacunary-flavored sequence `x^{2^i}` (the dyadic exponents are
    **lacunary** ⇒ Salem–Zygmund `√(n log)` maximal bound) — *risk:* `deltastar-salem-zygmund-gausssum-chaining`
    in-tree; check whether the lacunarity is genuine on the **exponent** side.
58. **☆ [H]** Talagrand convex-distance concentration of the worst-`b` event as a rare deviation of the
    empirical phase distribution from uniform.
59. **☆ [Φ][H]** Moment-zeta with complex `s` (`Z(s)=Σ_b|η_b|^{2s}`, analytic continuation, Phragmén–
    Lindelöf on `Re s∈[1,log m]`) — reads **inter-moment** correlations integer moments throw away
    (proposal N2 from the 50-directions manifesto; un-stabbed).

## Lens 9 — Galois / Stickelberger / cyclotomic algebraic-number-theory

60. **☆ [π]** Stickelberger factorization of the Gauss sum `g(χ)` whose `m`-th coset combination is
    `η_b`: bound the **archimedean** size of a Z[ζ_m]-element by its prime factorization — *risk:*
    `473202e5f` showed depth-`R` Stickelberger gives bad prime `~ n^{Θ(log n)}` (generic-prize refuted).
61. **☆ [π]** Gross–Koblitz `p`-adic Gamma formula for `g(χ)`, transported — *risk:* A4 (tower period unit).
62. **☆ [SP]** Galois-conjugate spread: `η_b` and its `Gal(Q(ζ_p)/Q)`-conjugates are the `m` periods;
    bound the max by the **house** (max conjugate) of the cyclotomic integer via Mahler measure /
    Schur–Siegel–Smyth — *risk:* A6 (Schur–Siegel–Smyth reduces to Johnson).
63. **☆ [π]** Bad-prime mechanism (`deltastar-galois-prime-badprime`): localize the worst `b` to primes
    where the cyclotomic factorization degenerates; bound the **measure** of bad primes.
64. **☆ [SP]** Lehmer-conjecture-style lower bound on Mahler measure of the period minimal polynomial,
    inverted to an upper bound on the house — likely `✗inc`.

## Lens 10 — additive-energy / moment (the conservation-law DEAD tier — restated)

65. **†** `E(μ_n) ≤ n^{2+o(1)} ⇒` list — `√`-loss, sub-Johnson (W2).
66. **†** higher energies `E_r` moment ladder — same `√`-loss every rung; `→√q` only.
67. **†** moment-step deeper `r` — REDUCE-TO-WALL (`1−g(r,n)≈r/n`, BGK knife-edge every rung; `r*~120` @ `n=2^30`).
68. **†** Turán–Newton power-sum (C13) — SURVIVES-AS-WALL (= moment step).
69. **†** signed additive energy `E^Φ_r` (manifesto N1) — only escapes if the **sign** weight is
    genuine; un-stabbed but pre-flagged as energy-adjacent.
70. **†** Plünnecke–Ruzsa / BSG / Sanders Bogolyubov on `μ_n` sumsets — structure, not the count `≤n`.

## Lens 11 — value-concentration / list-decoding-combinatorial (the in-tree δ\* bridge)

71. **☆ [SP]** Per-direction list bound: `N(u₀) ≤ 2·avg(N)` directly via a beyond-Johnson list-size
    atom for the dim-`(k+1)` MDS-derived code — the in-tree `rs_johnson_lambda_nat_le` floor consumer.
72. **†** Guruswami–Sudan / GS interpolation — = Johnson radius exactly (`✗J`).
73. **†** Guruswami–Rudra folded capacity — needs folding; prize is unfolded.
74. **☆ [SP]** Value-concentration attack (`deltastar-valueconcentration-attack`): bound the number of
    `x∈μ_n` with `e_p(bx)` in a fixed arc by a polynomial-degree (Stepanov-flavored) argument on the
    arc-indicator — the geometric form of family (ii).
75. **☆ [SP]** Far-line incidence (`farline-RIGOROUS-upper-bound-on-mca`) — rigorous upper bound exists;
    check if it transports to `M` or only to the Plotkin proxy (`farline-incidence-is-plotkin-proxy`).

## Lens 12 — cross-domain / dynamical / ergodic transfer

76. **☆ [X][Φ]** Furstenberg-correspondence: realize `M` as a sup over an `Z/m`-action's ergodic
    averages; bound via a quantitative mean ergodic theorem — *risk:* amenable action (A8) gives no rate.
77. **☆ [X]** Host–Kra / nilsequence decomposition of the phase `e_p(bx)` along `μ_n` — the dyadic
    exponent recursion `x↦x²` is a (non-abelian) skew-product; bound the **non-structured** part.
78. **☆ [X][Φ]** Bourgain's pointwise-ergodic maximal inequality for the lacunary sequence `2^i` applied
    to the exponent walk (cousin of #57 in the dynamical category).
79. **☆ [X]** Sarnak-Möbius-disjointness flavor: treat the period sequence as a "deterministic" sequence
    and seek a disjointness/cancellation bound — speculative, likely `✗inc`.
80. **☆ [X]** Quantitative equidistribution of `(x, x²) : x∈μ_n` via a Weyl-sum on the **product**
    variety, transferring 2-dimensional cancellation back to 1-dimensional `M`.

## Lens 13 — pseudorandomness / derandomization / construction

81. **†** Rudin–Shapiro / flat-Littlewood explicit construction — DEAD (Mahler/flat-Littlewood; refuted).
82. **☆ [Φ]** Gauss-phase pseudorandomness (`deltastar-407-route3-gauss-phase-pseudorandomness`): treat
    `{e_p(bx)}` as a PRG output and bound the sup by a fooling/`ε`-bias argument — *risk:* circular if
    the bias **is** `M`.
83. **☆ [SP]** Subspace-evasive / extractor construction: `μ_n` as a source with min-entropy `log n`;
    a 2-source extractor's error = `M`-type bound — check if the 2-power structure gives an explicit rate.
84. **☆ [SP]** Sparse cyclic code lens (`deltastar-sparse-cyclic-code-lens`): the `μ_n`-spectrum =
    a sparse cyclic code's weight; bound max weight via BCH/Roos — *risk:* `✗J` (dual-BCH ⇒ Johnson).

## Lens 14 — operator / functional-analytic (the relocation tier — restated DEAD + one residual)

85. **†** Terwilliger algebra operator norm (A5) — = `M` exactly (REDUCES-TO-WALL).
86. **†** dilation / Bourgain–Gamburd multiplicative gap (A8) — amenable, affine block = period.
87. **†** Kelley–Meka / PFR (A9) — energy/moment, wrong directional theorem (no-go brick landed).
88. **☆ [Φ]** Non-commutative Khintchine on the period operator with the **correct** (Gauss-period)
    covariance, retaining the off-diagonal phase that the diagonal Parseval read discards.
89. **☆ [Φ]** Free-probability `R`-transform of the period spectral measure — the **free** convolution
    edge vs the classical (Wick) edge; does the 2-power structure give a free (Catalan) law on the
    correct matrix (contrast I037 which had the wrong matrix)?

## Lens 15 — analytic-NT / sieve / circle-method (high `✗inc` density)

90. **†** Heath-Brown / Konyagin incomplete-Gauss-sum bounds — give `√q` not `√(n log)` (W4).
91. **†** Burgess on short intervals — `q^{1/4}`-type, past-Johnson not capacity (`✗J`).
92. **†** Vinogradov mean-value / efficient congruencing on the phases — no mult structure (`✗triv`).
93. **☆ [SP]** Circle-method major/minor-arc split of `Σ_{x∈μ_n}e_p(bx)`: major arcs are the `m`
    coset peaks; bound minor-arc contribution via the 2-power Weyl differencing — *risk:* the peak IS `M`.
94. **☆ [SP]** Karatsuba double-sum / Vaughan identity adapted to the multiplicative subgroup support.
95. **☆ [SP]** Postnikov-character / `p`-adic-logarithm expansion of `e_p(bx)` on `μ_n` (since `μ_n`
    lifts to a 2-adic disc) — *risk:* `p`-adic period is a unit (A4); only the **archimedean** projection matters.

## Lens 16 — second-moment-refinement / cumulant (phase-aware moment surrogates)

96. **†** cumulant diagonal dominance (CDD, `deltastar-CDD-cumulant-diagonal-dominance-conjecture`) —
    in-tree conjecture; cumulant-not-moment is the right idea but `deltastar-cumulant-dichotomy`
    shows the dichotomy still caps at the wall for these spectra.
97. **☆ [Φ]** Free cumulants (vs classical) of the period spectrum — the free 4th cumulant isolates the
    **edge**; conjecture: free-cumulant decay forces `λ₂ ≤ √(n log m)` (contrast moment #68 which is classical).
98. **☆ [Φ]** Bessel-even-moment law (`deltastar-bessel-even-moment-law-PROOF`) extended with a **phase**
    insertion — the proven even-moment Bessel law is real; does an oscillatory variant survive?
99. **☆ [Φ]** Healthy-cumulant prize-regime probe (`deltastar-407-prize-regime-healthy-cumulant`):
    measure whether the **standardized** period spectrum has bounded higher cumulants at prize depth ⇒
    sub-Gaussian tail ⇒ `√log` sup — the cleanest [Φ]+[H] hybrid that is NOT pre-refuted.
100. **☆ [Φ]** Tensor-power / hypercontractivity of the phase function on the `Z/2^μ` exponent group
     (Bonami–Beckner with the 2-power Fourier weights) — bound `‖·‖_∞` by `‖·‖_4` with a 2-power-
     improved hypercontractive constant — *risk:* hypercontractivity is the `L^4`→`L^∞` step that I027
     showed loses to `n^{1.75}`; only viable if the 2-power weights give a **dimension-free** constant.

---

# MOST PROMISING LEADS (exact next steps)

Only **one** stab returned a genuine handle; two un-stabbed [Φ]+[H] proposals are the cleanest
not-pre-refuted candidates. Honest ordering:

### Lead 1 — I031 deterministic→random sup transfer (the only HANDLE). `[H]`, compressed-sensing-coherence.
The open problem has **shrunk** from the full BGK exponent gap (`1−o(1) → 1/2`) to a single
bounded-constant transfer: prove `M ≤ C·E sup_b|G_b|` for the cyclotomic Gauss-period frame on the
quotient `F_p*/μ_n`. The random-model floor `E sup|G| ≤ C√(n log m)` is a theorem (KMR/RV); the
deterministic `M` sits a **bounded, stable** `~1.4×` above it. Two concrete sub-targets:
1. **Volumetric chaining lemma (Lean-formalizable, axiom-clean).** Covering number
   `log N(F_p*/μ_n, d_q, ε) ≤ log(p/n)` is rigorous; the wanted lemma is that the deterministic sup is
   dominated by `√n·γ₂ + controlled excess`. Also formalize the **orbit-invariance + sup-over-quotient
   reduction** (`η_b` orbit-invariant ⇒ `M = max over m reps`) as a reusable brick — this is the
   highest-confidence axiom-clean deliverable in the whole sweep.
2. **Constant `n`-uniformity probe.** Push to `n=128,256` at fixed thin `β` (numba/GPU; orbit-rep
   enumeration `O(p)`). If `M/rand` stays bounded ⇒ floor exponent `1/2` with explicit constant; if it
   grows ⇒ the RISK bites and it degrades to no-gain. **This probe is the deciding experiment for the
   whole compressed-sensing lens.**

### Lead 2 — I099 standardized-spectrum healthy-cumulant. `[Φ]+[H]`, second-moment-refinement (un-stabbed).
Cleanest candidate that is **not** pre-refuted by the conservation law: it targets the **tail** of the
standardized period spectrum, not a fixed even moment. Next step: a prize-depth probe measuring the
**standardized** higher cumulants `κ_r/σ^r` of `{η_b}` (already partly in
`deltastar-407-prize-regime-healthy-cumulant`); if they are **bounded uniformly in `n`**, sub-Gaussian
concentration forces `√log` sup. Pre-screen: this is viable **only** if the cumulants are genuinely
standardized-bounded — if they grow with `n`, it collapses to the moment ladder (W2). Run the probe
**before** any theory.

### Lead 3 — I015 multivariate digit-recursion Stepanov. `[π]`, stepanov-2adic (un-stabbed, family (ii)).
The single un-refuted residual of three stabbed Stepanov ideas (I001/I006/I008). All three failed for
the **same** reason: `μ_n` is one orbit / 1-dimensional / separable, so no **univariate** auxiliary can
manufacture multiplicity. The escape: a **multivariate** Stepanov over the dyadic-digit coordinate ring,
where multiplicity comes from the `x↦x²` digit **recursion** (a transverse structure), not univariate
tangency. Next step: write `probe_i015_digit_recursion_stepanov.py` — build the bivariate ideal of
`{(x, x²): x∈μ_n}`, check whether a low-degree auxiliary in the digit ring has common order `≥ log n` on
`μ_n` (exact, proper regime). High-risk (separability is a hard wall) but it is the **only** Stepanov
direction not yet collapsed.

---

## Bottom line (honest)

- **Stab scoreboard:** 1 HANDLE (I031), 2 REFUTED (I006, I012), 5 NO-GAIN (I037, I008, I001, I025, I027).
- **No fabricated breakthrough.** The prize floor `M(μ_n) ≤ C√(n log(p/n))` is **not** closed.
- **The conservation law held everywhere it was tested:** every even-moment / `L⁴` / merit / energy /
  unweighted-spectral object is provably blind to the argmax (I025, I027, I037-unweighted, the moment
  ladder). The pre-screen rule (reject moment-direction inputs before probing) is reconfirmed.
- **The one real shrink:** I031 reduces the open content to a **bounded-constant deterministic→random
  sup transfer** on the dilation quotient — and its orbit-reduction is an axiom-clean Lean brick worth
  landing regardless of the transfer's fate.
- **Families the campaign still wants pushed** (both attack the sup directly, not via a phase-blind
  moment): (i) effective sum-product with **quantified** constants (Lens 1, none stabbed); (ii)
  **multivariate** 2-adic Stepanov (Lens 2, I015 the lone residual).

*Probes (proper regime: `p` prime, `n=2^μ`, `n|p−1`, `p≫n³`, `m>1`, never `n=p−1`):*
`scripts/probes/probe_i031_*.py`, `probe_i037_*` (committed `5326fd999`),
`probe_i001_ore_moore_frobenius_stepanov.py`, `probe_i006_qdifference_stepanov.py`,
`probe_i008_walsh_dyadic_stepanov.py`, `probe_i012_subgroup_trilinear.py` (`c8f0af3e3`),
`probe_levenshtein_*_I025*.py`, `probe_papr_merit_*_I027*.py`. Refutations logged in
`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`.
