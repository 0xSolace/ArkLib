# δ* / #444 — Deep & Exotic DIRECT-Sup-Norm Attack Catalogue (18 techniques, 2026-06-17)

**Target (sharpened).** `M(n) = max_{b∈F_p^*} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`, `μ_n` the
order-`n=2^μ` multiplicative subgroup of `F_p^*`; prize scale `n~2^30`, `p = n^β ~ 2^120`
(`β=4`), `p ≡ 1 mod n`. `M(n) = λ₂(Cay(F_p,μ_n))` = the largest nontrivial generalized-Paley /
Gauss-period eigenvalue = the 25-year BGK/Paley sup-norm wall. Floor wanted:
`M(n) ≤ C·√(n·log(p/n))`.

**Why this round is different — the energy route is DEAD.** Exact-integer (not float-FFT) counts
show `K_eff = (E_r/[(2r-1)‼·n^r])^{1/r}` CROSSES 1 and GROWS (1.000 / 1.127 / 1.848 at n=16/32/64),
onset depth SHRINKING with n. So `E_r(μ_n) ≤ K^r·Wick` with bounded K is FALSE at prize scale;
`M^{2r} ≤ q·E_r` is too weak; `RatioDecreasing R(r)≤1` is numerically FALSE
(`deltastar-444-ktransfer-bounded-K-DEAD-exact-2026-06-17.md`). The energy inflates but the prize can
still hold because the inflated energy SPREADS over the `m=(p-1)/n` cosets so the MAX stays
√(n log)-bounded. ⇒ the sup must be bounded DIRECTLY; any route that funnels back to `E_r ≤ K^r·Wick`
is dead (fence **F12**), distinct from "reduces to the open wall".

**Fence map (kill mechanisms; naming a route's fence = its verdict).** F0 conservation law
(domain 2nd-order arithmetic caps at Johnson √n; the √log excess is a rare-event/L∞ tail invisible
to 2nd moments). F1 moment/energy/cumulant = conjugate to the wall. **F12** bounded-K energy
transfer DEAD at β=4. F2 Weil/Deligne vacuous (n<√q) or config-variety Weil-error dominates. F3
p-adic alone archimedean-blind. F4 generic chaining no γ₂ gain. F5 spectral gap / Bourgain–Gamburd
zero (abelian torus). F6 almost-periodicity vacuous below L² at q*=β/(β−1)=4/3. F7 entropy Rényi-2 =
additive energy. F8 association-scheme/Terwilliger degenerates to √q. F9 supply-side count cap. F10
FKM sheaf conductor ≥ rank ~ n. F11 object-change synonyms (conjugate-norm count; product-formula
sign-reversal; rank collapse; `p≡1 mod n ⇒ Frob_p=id`).

---

## VERDICT TABLE (18 techniques, 5 clusters)

| ID | Cluster | Technique (one line) | Verdict | Fence / why-vacuous |
|----|---------|----------------------|---------|---------------------|
| H1 | Automorphic | Iwaniec–Sarnak AMPLIFIED 2nd moment, dilation-Hecke amplifier | REDUCES | F1 + F5 (+F0) |
| H2 | Automorphic | Kuznetsov/Petersson/relative trace formula amplification | REDUCES | F5 + F1/F12 |
| H3 | Automorphic | Subconvexity / root-number ceiling (Petrow–Young, Garcia–Young) | REDUCES | F2 + F0; thin-coset vacuity |
| I1 | Decoupling | Discrete restriction / small-cap decoupling (DGW, Guth–Maldague) | VACUOUS-AT-PRIZE | F1/F12; wrong variable, no curvature |
| I2 | Decoupling | Exponent pairs / vdC A-B / Bombieri–Iwaniec | REDUCES | F1 + F2/F9 aspect-ratio + F0 |
| J1 | Diophantine | Subspace / S-unit relation-count (ESS, Conway–Jones, Dvornicich–Zannier) | REDUCES | F9 + F1/F12 + F0/F11 |
| J2 | Diophantine | Pila–Wilkie / Bombieri–Pila / determinant-for-character-sums | REDUCES | F0 + F2 |
| J3 | Diophantine | Prismatic / syntomic / q-de-Rham cohomology of Gauss-sum motive | REDUCES | F3 (+F2) |
| J4 | Diophantine | Effective equidistribution / Ratner / EMV / BLMV | REDUCES | F0 + F5 + circular discrepancy |
| K1 | Quantum | Arithmetic QUE / quantum-variance + graph-QUE | REDUCES | F5 → F1/F12 + F0 |
| K2 | Quantum | Katz–Sarnak symmetry / RMT extreme value / FHK log-correlated max | REDUCES | F0 + F11 (FHK: white noise) |
| K3 | Quantum | Berry–Tabor / Poisson spacing → EVT | REDUCES | F0 (+F12 at threshold) |
| L1 | Alien | Circle method / Weyl differencing / Vinogradov minor-arc | REDUCES | F1/F12 (+F0) |
| L2 | Alien | Selberg / Gallagher larger sieve / Bombieri–Vinogradov (file `_wfH47`) | REDUCES | F0 (count≠sup) + VACUOUS Gallagher |
| L3 | Alien | Berkovich / Chambert-Loir COUPLED adelic equidistribution | REDUCES | F0 + F3 + F11 |
| L4 | Alien | Gowers `U^k` / GTZ inverse theorem / nilsequences | REDUCES | F1/F7 + F0 + F11 (fold) |
| L5 | Alien | Geometric Langlands / perverse / Deligne–Lusztig / theta (cluster) | REDUCES | F10 + F2 + F1 |

**Net: 0 NEW-DIRECT-HANDLE · 0 PARTIAL-HANDLE · 0 live OPEN-LEAD · 17 REDUCES-TO-FENCE · 1
VACUOUS-AT-PRIZE.** 17 axiom-clean Lean no-go files (`⊆{propext,Classical.choice,Quot.sound}`), all
registered in `ArkLib.lean`.

---

## CLUSTER 1 — Automorphic / amplification (H1, H2, H3)

The contract's flagged "one structurally-promising class": the Iwaniec–Sarnak sup-norm method is
DESIGNED to beat the 2nd moment for sup-norms, so least-obviously conservation-blind. **All three
reduce.** The common kill: `Cay(F_p,μ_n)` is an ABELIAN Cayley graph (eigenvectors = additive
characters, eigenvalues = Gauss periods `η_b`); the only natural Hecke operators are dilations
`T_l: η_b ↦ η_{lb}`, whose algebra is commutative and 1-dimensional per frequency.

**H1 — IS amplified SECOND moment** (`_wfH1_AmplifiedSecondMomentProjection.lean`,
`probe_wfH1_amplified_second_moment.py`, `probe_wfH1_kernel_structure.py`). Lit: IS95 "L∞ norms of
eigenfunctions"; Templier/Blomer–Maga/Marshall/Saha sup-norm program; Nelson orbit-method
arXiv:2503.06224; GL(3) Beacom/Templier arXiv:1412.5022. The deepest non-reducing attempt — one level
past the existing first-moment flat-spectrum no-go (`_AmplificationGainOne.lean`). The EXACT pre-trace
kernel `K(t)=Σ_b η_b conj(η_{tb}) = q·#{(x,y)∈μ_n²: x=ty} = q·n·1_{t∈μ_n}` is `q·n` times the SUBGROUP
INDICATOR = a SCALED RANK-m ORTHOGONAL PROJECTION onto the m averaging characters (flat eigenvalue
`q·n²`, 0 elsewhere). ⇒ amplified form `Q(x)=⟨x,Kx⟩ ≤ q·n‖x‖²` for EVERY amplifier, equality only on
the averaging direction ⇒ certifies only RMS/Johnson √n. IS gain requires (i) non-abelian Hecke
algebra, (ii) genuine eigenvalue variation, (iii) a Diophantine off-diagonal to save on — the EXACT
kernel kills all three at once (the `−n²` "off-diagonal" in the probe is the b=0 trivial-frequency
subtraction, NOT Diophantine cancellation). The b₀-detecting amplifier makes the bound WORSE
(amp/M: 2.76→7.89→21.3→53.2 at n=4..32). **REDUCES F1+F5.**

**H2 — Kuznetsov / Petersson / relative trace formula** (`_wfH2_kuznetsov_rtf_geometric_side.lean`,
`probe_wfH2_kuznetsov_rtf_geometric_side.py`). Lit: Kuznetsov 1980, Petersson, Deshouillers–Iwaniec
large sieve; Podestá–Videla arXiv:1911.08549. The amplified pre-trace GEOMETRIC SIDE is
POSITIVE-DEFINITE: `A(h)=Σ_b e_p(−hb)|η_b|² = p·#{(x,y)∈μ_n²: x−y=h}` (additive autocorrelation of
μ_n; every term a nonneg count), `A(0)=p·n`, off-diag total `(n−1)·A(0)` — a GROWING multiple, never
the `o(diagonal)` cancellation amplification needs. Kuznetsov wins only on an OSCILLATORY Kloosterman
(GL(2)) geometric side; `η_b` is a GL(1)/abelian Gauss period, not a Kloosterman sum (sibling of the
refuted Kowalski–Sawin C29). Stress-tested the genuine MULTIPLICATIVE IS amplifier `a_b=Σ_l x_l χ_l(b)`:
the localization mass is SPREAD over 15–30% (growing) of all ~m modes — only the full-length ORACLE
amplifier localizes the worst b (= knowing the profile = the open problem). **REDUCES F5/F1.**

**H3 — Subconvexity / root-number ceiling** (`_wfH3_subconvexity_rootnumber_ceiling.lean`,
`probe_wfH3_rootnumber_ceiling.py`). Lit: Petrow–Young Weyl bound (Annals 192 (2020),
arXiv:1811.02452); Garcia–Young thin-coset 2nd moment (Forum Math Sigma 13 (2025) e83); Dunn–Radziwiłł
Patterson bias arXiv:2109.07463; Michel–Venkatesh GL(2) subconvexity. `η_b = (√q/m) Σ_χ conj(χ)(b)
ε(χ)` is a √q-weighted sum of root numbers `ε(χ)=τ(χ)/√q`. But `|τ(χ)|=√q` EXACT (flat spectrum) ⇒
subconvexity bounds only the L-value SIZE, which carries ZERO content; the entire prize cancellation
lives in the modulus-1 PHASE = the open BGK/Paley wall. Modulus-only → triangle → `|η_b|≤√q` (vacuous,
n<√q = F2). At β=4 the subgroup `n=q^{1/4}` sits at the Burgess endpoint (exponent vanishes); the
family `m=q^{3/4}` is ABOVE q^{1/2} (too thick for Garcia–Young, which is also a 2nd-moment AVERAGE
with a √q secondary BIAS term, not a sup). **REDUCES F2+F0; VACUOUS thin-coset.**

## CLUSTER 2 — Decoupling / harmonic (I1, I2)

**I1 — Discrete restriction / small-cap decoupling** (`_wfH1_restriction_supgap.lean`,
`probe_wfH1_restriction_supgap.rs`). Lit: Demeter–Guth–Wang small-cap exponential-sum conjecture;
Guth–Maldague arXiv:2206.01574; moment curve R⁴ arXiv:2605.27065 Cor 1.4; di Benedetto–Garaev
arXiv:2003.06165; Kemp arXiv:1908.07002. Three independent failures: (a) WRONG VARIABLE — the canonical
estimate `∫_Ω|Σ c_f e(x·f)|^p dx ⪅ N^{p/2}|Ω|` is an L^p SPATIAL average over x, never a sup, never
over the multiplier b; spatial sup at x=0 = total mass n (trivial). (b) NO CURVATURE — μ_n's frequency
set is a flat level set of `x^n=1`, zero curvature, no small-cap gain. (c) the L^{2r} input over μ_n IS
`E_r` (E_2=3n(n−1), E_3=15n³−45n²+40n exact) ⇒ `M^{2r}≤q·E_r` gives `(qE_r)^{1/2r}≥n` (F1/F12). The
correctly-matched FINITE-FIELD restriction extension `(Ef)(b)=Σ e_p(bx)` IS over b and still collapses
to `q·E_s` (`_wf2NA_restriction_moment_collapse.lean`). **VACUOUS-AT-PRIZE; only content reduces F1/F12.**

**I2 — Exponent pairs / vdC A-B / Bombieri–Iwaniec** (`_wfHi2_ExponentPairNoCrossing.lean`,
`probe_wfH_i2_exponent_pair.py`). Lit: Graham–Kolesnik; Huxley; toward-optimal exponent pairs
arXiv:2306.05599; LP-over-exponent-pairs arXiv:1402.1993; finite-field vdC arXiv:2312.02525. Three
axes: (i) A-process = Weyl differencing = 2nd moment — differenced phase set `b(h^t−1)·μ_n` is a dilate
of the SAME subgroup (F1). (ii) B-process needs phase curvature `f''≥λ>0` / monomial derivative growth;
the discrete 2nd difference of the multiplicative phase is perfectly sign-balanced (+8/−8, +16/−16),
O(1)-equidistributed, with f' monotone-violating at exactly half the points — a pseudorandom
permutation, no curvature. (iii) ASPECT RATIO `N=n < √T=n²` at β=4 — strictly below the entire
exponent-pair regime. Every pair gives n-exponent `k(β−1)+l ≥ 1` (Bourgain(13/84,55/84)→1.119,
vdC→2=Weil, trivial→1, conjectural-optimal(0,1/2)→1/2=Johnson, never below). Bombieri–Iwaniec is also
an L²-mean-square = average not sup. **REDUCES F1 (+F2/F9 + F0).**

## CLUSTER 3 — Diophantine / model-theory (J1, J2, J3, J4)

**J1 — Subspace / S-unit relation-count** (`_wfHJ1_SubspaceSUnitCountVacuous.lean`,
`probe_wfH_J1_subspace_count_vacuity`, `probe_wfH_J1c`). Lit: Evertse–Schlickewei–Schmidt Annals 155
(2002); Evertse-1999 root-of-unity count `(k+1)^{3(k+1)²}`; Conway–Jones Acta Arith. 30 (1976);
Lam–Leung math/9511209; Dvornicich–Zannier Archiv Math. 79 (2002). (1) F9: even where ESS applies, the
count log-exponent ≥ 12r² is super-quadratic vs the linear `log₂ q` union budget at depth r∼ln q (count
= 10^900498 vs ~480-bit budget) — tightens no union bound. (2) F1/F12: ESS/CJ/Lam–Leung are
CHARACTERISTIC-0; for μ_n 2-power the only char-0 relations are antipodal/Mann pairs = the (2r−1)‼ Wick
matchings = the dead energy. (3) F0/F11: Dvornicich–Zannier mod-l is l-INDEPENDENT, only bounds the
ORDER of roots, no length lower bound `k≥c log p`, √q-blind. Exact-int MITM finds NO genuine char-p ±1
relation up to the horizon (2-power-norm-protected; consistent with the floor but no rate). The genuine
char-p defect `W_r` is correctly left as the irreducible open wall. **REDUCES F9 + F1/F12 + F0/F11.**

**J2 — Pila–Wilkie / Bombieri–Pila / determinant-for-character-sums**
(`_wfHJ2_LevelSetDeterminantMethod.lean`). Lit: Pila–Wilkie Duke 133 (2006); Bombieri–Pila /
Heath-Brown Ann. Math. 155 (2002), survey arXiv:2312.12890; HBK/Konyagin/Shkredov arXiv:1311.5726;
Kowalski "Exponential sums over definable subsets" Israel J. Math. 2007 (arXiv:math/0504316);
André–Oort/Pila–Zannier. Two facts: (O1) multiplicative rigidity `|η_{ub}|=|η_b|` for `u∈μ_n` ⇒ the
level set `L(T)={b:|η_b|²≥T}` is an exact union of full μ_n-cosets = 0-dimensional; PW needs positive-
dim transcendental, BP/determinant need positive-dim variety counting EQUATIONS not sublevel
inequalities. (O2) the only count `L(T)` admits is the EXACT Parseval 2nd moment `Σ_{b≠0}|η_b|²=np−n²`,
Markov `|L(T)|≤(Σw)/T = Θ(q/log)` = Johnson scale. Determinant-for-character-sums IS the BGK wall
`n^{1−δ}`, vacuous at `n=p^{1/4}` (best known `H^{1−31/2880}` ≈ 2^29.68 vs target 2^17.98).
**REDUCES F0 + F2.**

**J3 — Prismatic / syntomic / q-de-Rham cohomology** (`_wfJ3_prismatic_frobenius_archblind.lean`).
Lit: Katz "Crystalline cohomology, Dieudonné modules, Jacobi sums"; Otsubo–Yamazaki "Motivic Gauss and
Jacobi sums" arXiv:2402.06072; Bhatt–Scholze "Prisms and prismatic cohomology" arXiv:1905.08229;
Bhatt–Lurie absolute prismatic arXiv:2201.06120; Scholze q-de-Rham. Exhaustive dichotomy: a p-adic
cohomology theory outputs exactly (Newton polygon = p-adic valuations, Hodge–Tate weights, integral
lattice/Nygaard filtration). The complex |Frobenius eigenvalue| is the WEIGHT = purity `|τ|=√q` (= F2,
vacuous since `M(n)` is a DFT combination of m equal-modulus eigenvalues). Everything finer prismatic
adds over crystalline (Nygaard, q-de-Rham/Aomoto) refines the p-adic FILTRATION = F3 archimedean-blind.
No comparison theorem with an archimedean place; `p≡1 mod n ⇒ Frob_p=id` kills b-sensitive Galois
levers. No third output channel. **REDUCES F3 (+F2).**

**J4 — Effective equidistribution / Ratner / EMV / BLMV** (`_wfHJ4_EquidistDiscrepancyBlind.lean`).
Lit: Einsiedler–Margulis–Venkatesh Invent. Math. 177 (2009) arXiv:0708.4040; Einsiedler survey;
Bourgain–Lindenstrauss–Michel–Venkatesh ETDS 29 (2009); Venkatesh Ann. Math. 172 (2010);
Erdős–Turán–Koksma; Katz Sato–Tate of Gauss-sum families. Three legs: (a) F0 — equidistribution is
weak-*/discrepancy against fixed test functions, caps at the average (the √log sup excess is the L∞
tail). (b) F5 — the dilation `b↦g^{(p-1)/n}b` is the abelian cyclic rotation on Z/m = a torus with ZERO
spectral gap; EMV's polynomial rate REQUIRES semisimple + finite centralizer. (c) the only effective
abelian rate (ETK) is CIRCULAR — bounds discrepancy BY the very exponential sums whose sup we want.
Katz Sato–Tate is a q→∞ limiting-distribution statement; worst-b at fixed q is out of scope.
**REDUCES F0 + F5 + circular.**

## CLUSTER 4 — Quantum / physics (K1, K2, K3)

**K1 — Arithmetic QUE / quantum-variance + graph-QUE** (`_wfK1_que_quantum_variance.lean`,
`probe_wfK1_que_hecke_flatness.rs`). Lit: Lindenstrauss 2006; Soundararajan; Holowinsky–Soundararajan
arXiv:0809.1636/0809.1640 (QUE → shifted-convolution sums of multiplicative Hecke eigenvalues); IS95;
Brooks–Lindenstrauss arXiv:1006.3583; Naor et al Israel J Math 2023 arXiv:2207.05527; circulant DQUE
arXiv:2411.09028. Two prongs: (a) the QUE quantum-variance functional `V=Σ_b|η_b|⁴ = q·E_2`, `E_2=
3n(n−1)` exact (= F1/F12; `que_variance_blind_to_sup` gives only `M²≤√q·n ~ n³`, far above the floor =
F0). (b) the multiplicative dilation-Hecke direction is a FLAT projection `s(l)=n·1_{μ_n}` exactly (max
over `l∉μ_n` = 0), no Ramanujan–Petersson variation, so the L–S sieve has zero fuel (F5). Graph-QUE is
about eigenVECTOR delocalization, not the eigenVALUE `λ₂=M(n)`; abelian Cayley graphs have ergodicity
measure 0 in the character basis (not quantum-ergodic). **REDUCES F5→F1/F12+F0.**

**K2 — Katz–Sarnak / RMT extreme value / FHK** (`_wfHK2_katz_sarnak_extreme_value.lean`,
`probe_wfHK2_logcorr_field.rs`). Lit: resonance method (Soundararajan; Bober–Goldmakher
arXiv:1109.1786; Bondarenko–Seip arXiv:1507.05840); FHK/Arguin–Belius–Bourgade arXiv:1602.08875;
Katz–Sarnak/Iwaniec–Luo–Sarnak n-level density; Garcia–Hyde–Lutz "Gauss hidden menagerie"
arXiv:1501.07507. Resonance gives only LOWER bounds (constructive large values), no upper analogue. The
ONLY route below the iid-Gaussian extreme value is the FHK sub-Gaussian log-correlated max law — but a
NEW exact-integer probe MEASURES WHITE NOISE: `Cov(log|η_b|,log|η_{b'}|)/Var` at archimedean lags
d=1..512 AND 2-adic lags is ~0 (|cov/var|<0.01, no −ln d slope), at every generic prime up to n=256 ⇒
FHK INAPPLICABLE ⇒ the sharpest EVT sub-route is CLOSED. Only the iid extreme value remains, whose
optimizer `√(2n log(p/n))` EQUALS the open BGK floor verbatim (F11; `m·exp(−(√(2n log m))²/2n)=1`
exact). Empirical max tracks iid (ratio 0.78→0.89 rising) NOT FHK (0.51→0.35 falling). The Sato–Tate
law is the complex Gaussian (support all of C, no compact edge — "symmetry-group edge bounds the max"
is a category error). The GHL geometric handle is the MOMENT route (F1/F12-dead). **REDUCES F0+F11.**

**K3 — Berry–Tabor / Poisson spacing → EVT** (`_wfHK3_berry_tabor_poisson_evt.lean`,
`probe_wfH_K3_berry_tabor_evt.rs`). Lit: Berry–Tabor (Marklof ICMP2000); Leadbetter D(u_n)/D'(u_n)
PTRF 1974; Leadbetter–Lindgren–Rootzén 1983; extremal index; Bourgain–Rudnick–Sarnak / Kurlberg
lattice-points-on-circles arXiv:2112.08522 Invent. Math. 2025. The spectrum IS provably Poisson-spaced
at β~4 (de-tied gap-ratio ⟨r⟩=0.387–0.421, dead-on Poisson 0.386 vs GUE 0.603) — the question is
well-posed, NOT vacuous. But (1) F0: ⟨r⟩ is a bulk statistic invariant under a single-coordinate tail
warp — multiplying the single largest |η_b| by K leaves ⟨r⟩=0.3869 IDENTICALLY (K=1,2,5,20,100) while
max scales ×K; so the spacing law carries ZERO information about the one tail event = the prize sup. (2)
F12 at the threshold: the rigorous Leadbetter upgrade (Gumbel iff long-range mixing + anti-clustering)
needs control to moment-order `r∼log m` at `u_n=√(2n log m)` = the dead energy. **REDUCES F0 (+F12).**

## CLUSTER 5 — Alien / cross (L1, L2/H47, L3, L4, L5)

**L1 — Circle method / Weyl / Vinogradov** (`_wfHL1_circle_method_supform.lean`,
`probe_wfHL1_circle_method_supform.rs`). Lit: Tao "Bounding short exponential sums on smooth moduli";
BGK J. LMS 2006; Shakan expository; Vinogradov mean value (Wooley; Bourgain–Demeter–Guth
arXiv:1707.00119). The circle method has exactly two Fourier-dual handles, both moments: (i) Weyl/vdC
on the degree-1 phase returns the additive autocorrelation = 2nd moment (F0/F1; differencing a LINEAR
phase has no degree to reduce); (ii) the power sum `Σ_b η_b^{2r}=q·E_r` (F12, `(qE_r)^{1/2r}≥n`). The
Weyl SAVING needs interval structure μ_n lacks (it meets every length-p/n window in O(1) pts, probe
3/3/5 at n=16/32/64). The multiplicative×additive clash (sum-product) is invisible to arc decomposition
— exactly why BGK ABANDONED the circle method for additive combinatorics. **REDUCES F1/F12 (+F0).**

**L2/H47 — Selberg / Gallagher larger sieve / Bombieri–Vinogradov**
(`_wfH47_SelbergLargerSieveLargeValues.lean`, `probe_wfH47_sieve_largeset_structure.rs`,
`probe_wfH47_sieve_suptip.rs`). Lit: parity problem (Selberg 1949; Tao 2007); Gallagher larger sieve
(Croot–Elsholtz); Bombieri–Vinogradov; Darbar–Kerr–Munsch–Shparlinski arXiv:2604.02960 Thm 2.7. Two
kills: (K1/F0) M is POINTWISE — `M>T ⟺ A_T≠∅`, and a cardinality cap `|A_T|≤N` with N≥1 caps nothing;
only `|A_T|=0` bounds M, never reached at the floor (Markov count `(qn−n²)/T² ≫ 1`). The count is
2nd-order Parseval data = Johnson, blind to the oscillatory tail. (K2/VACUOUS) Gallagher's LARGER sieve
(the genuinely-F1-dodging one — bounds |A| via residue occupancy ν(l), NOT L²) needs `ν(l)≪l`; exact
probe measures `ν(l)=l` (FULL residue occupancy) for `l∈{3,5,...,23}` and the sup-tip spread over all
residues/parities, at n=16..256, β=4. With ν(l)=l the Gallagher bound is ≤0. **REDUCES F0 + VACUOUS.**

**L3 — Berkovich / Chambert-Loir COUPLED adelic equidistribution**
(`_wfHL3_berkovich_chambertloir_equidist.lean`). Lit: Baker–Rumely AMS Surv. Monogr. 159 (2010);
Chambert-Loir J. reine angew. Math. 595 (2006) arXiv:math/0304023; Favre–Rivera-Letelier Math. Ann.
335 (2006); Petsche Int. J. NT 5 (2009); Fili arXiv:1508.01498; Duke–Garcia–Lutz/Habegger "Norm of
Gaussian Periods" arXiv:1611.07287. The honest escape mechanism (arch+non-arch energy coupling) was
scrutinized and fails on three grounds: (A) F0 — Chambert-Loir's conclusion is WEAK-* convergence; the
House is the L∞ support edge; moving one conjugate (mass 1/m) to radius R raises House to R while
perturbing any `W_q` by `O(m^{−1/q})` (`house_unbounded_under_weakstar_rate`). (B) small-point
hypothesis (height→0) UNMET — the period's conjugates have √(log m)-wide support (`avg2_exceeds_one`).
(C) F3+F11 — the only Berkovich sup-control is the non-arch max-modulus (Shilov boundary), arch-blind;
energy minimization + product formula give a LOWER bound on spread (`coupled_energy_is_lower_bound`) and
adding nonneg non-arch energies cannot flip it — because the product formula IS the source of F11.
**REDUCES F0 + F3 + F11.**

**L4 — Gowers `U^k` / GTZ inverse theorem** (`_wfL4_gowers_quadratic_fold.lean`,
`probe_wfH_L4_gowers.py`, `probe_wfH_L4_fold.py`). Lit: Green–Tao–Ziegler Ann. Math. 176 (2012)
arXiv:1009.3998; Tao–Ziegler/BTZ finite-field; Garcia–Lorenz–Todd arXiv:2112.13886. Three stacked: (a)
F1/F7: `‖1_{μ_n}‖_{U²}^4 = Σ_b|η̂_b|⁴ = E_2/p³` = additive energy; the U² inverse theorem returns the
linear phase = the η_b. (b) F0: monotonicity `‖f̂‖_∞ ≤ ‖f‖_{U²} ≤ ‖f‖_{U³} ≤ …` makes higher norms
LARGER hence LOOSER ceilings; the inverse theorem is existence/lower-bound-only, never caps M. (c) F11:
the one quadratic hope `Q(n)=max_c|Σ_{x∈μ_n}e_p(cx²)|` (which DOES exceed M, Q/M=1.06→1.62) folds
EXACTLY — x↦x² is 2-to-1 onto μ_{n/2}, so `Q(n)=2·M(μ_{n/2})` (|Q−2M_half|=0) = the SAME BGK wall one
level down the 2-power dilation tower; U⁴,U⁵,… iterate to μ_{n/4},μ_{n/8}. **REDUCES F1/F7+F0+F11.**

**L5 — Geometric Langlands / perverse / Deligne–Lusztig / theta (ONE completeness cluster)**
(`_wfHL5_GeometricSupNormCharCycleFloor.lean`, `probe_wfH_L5_charcycle_rank_floor.rs`). Lit: Sawin
arXiv:1907.08098 (geometric sup-norm = stalk-cohomology dim / char-cycle polar multiplicities); theta
fourth-moment sup-norm arXiv:2009.07194; Aubert finite-field theta arXiv:2603.25658; BGK revisited
arXiv:2401.04756; Connes NCG / crossed-product. The completeness meta-obstruction: every far-depth
technique realizes `η_b` as a Frobenius trace of a sheaf on the b-line and produces a bound of the SAME
shape `|η_b| ≤ (effective rank R = char-cycle polar multiplicity) · (per-point weight w)`. The exact 2nd
moment `Σ_b‖η_b‖² = q·n` FORCES R = n ⇒ trivial `M≤n`; the √n cancellation (n constituents in general
position) is the per-moment content = the open BGK/Paley wall. Sawin requires GL2(F_q(T)) non-abelian
newforms / Hitchin nilpotent cone (the Weyl saving); η_b is an ABELIAN sheaf (rank-n sum of Artin–
Schreier pieces). theta sup-norm realizes a FOURTH MOMENT = E_2 (F1/F12-dead). Connes/NCG: cyclic μ_n ⇒
Schur multiplier `H²(Z/n,T)=0` ⇒ crossed-product cb-norm 1 (F5/T21). This is the SECOND boundary after
Johnson: the **boundary of geometric/automorphic relocation**. **REDUCES F10 + F2 + F1.**

---

## Bottom line

**NO genuine new thread.** The amplification flagship H1 — the deepest, least-conservation-blind attempt
(the genuine IS amplified SECOND moment) — collapses to a scaled rank-m projection = the energy, on an
EXACT pre-trace kernel identity. Every cluster's closest approach is stopped by a NAMED fence that
applies STRUCTURALLY at `p~n^4 / β=4 / n=2^30` (the kills rest on subgroup facts —
abelian-ness, `K=q·n·1_{μ_n}`, `Σ_b‖η_b‖²=q·n` — true at every scale, not regime-gated). The √(log) sup
excess is a rare-event/L∞ tail (F0) invisible to every 2nd-moment/bulk/weak-*/discrepancy/spacing/
quantum-variance functional; the only objects that DO see it are energy moments at depth `r∼log q`, which
are F12-dead at β=4. The **no-escape terminal is reinforced once more**, now with a second boundary:
relocating the cancellation into the sheaf / Langlands / QUE / trace-formula / Berkovich universe buys
nothing, because every such bound is linear in the rank-n second moment. The sharpest remaining open
statement is unchanged and irreducible: the genuinely-char-p coherence of the m unit-modulus phases
`conj(χ)(b)ε(χ)` at the worst b = the BGK/Paley sup-norm wall = the conjugate-norm count
`#{c : p | N(c)}`. Floor `M(n) ≤ C√(n log(p/n))` stays OPEN. Formal cone: 17 axiom-clean Lean no-go
files, all registered in `ArkLib.lean`. This is a method-boundary census, not a closure or a refutation.
