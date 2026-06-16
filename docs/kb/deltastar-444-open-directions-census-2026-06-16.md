# #444 δ* — Open-Directions Census (2026-06-16, full comment + dossier mine)

**Purpose.** A single, deduplicated map of *every open direction still available* on the proximity
prize (δ* for explicit dyadic RS codes), built from a full mine of all 392 #444 comments + the KB
dossiers + the in-tree ground truth. Companion to the issue body (the consolidated narrative); this
file is the **action menu** — what to try, what is already dead (and why), and what is only
*numerically* open. Honesty contract applies: a "named residual" is the modularity convention, not a
closure; numerically-undecidable ≠ proven; every dead end carries its kill reason.

## 0. Orientation — the single core (everything funnels here)

The prize is **ON-BGK** and the wall is **two-sided** (proven, axiom-clean: `_MomentLadderExceedsPrize`
method-necessity + `_EnergyRatioMonotoneReduction` `ERM-at-r ⟺ max_c‖η_c‖²≤(2r+1)n`). The single open
core, in its sharpest form:

> **CORE.** char-p transfer of the DC-subtracted Lam–Leung energy bound
> `A_r := E_r(μ_n) − n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r ≈ ln q ≈ 89`, `n = 2^30`
> ⟺ `M(n) = max_{b≠0}‖η_b‖ ≤ C√(n log m)` (BGK/Paley sup-norm at the Burgess barrier).

char-0 is **closed for all r** (`_CharZeroWickEnergy.gaussianEnergyBound_dyadic`, Lam–Leung antipodal
pairing; Bessel face `I₀(2y)^m ≤ exp(my²)`). The entire residual is the **char-p excess `W_r ≤ slack_r`
at deep r** = the 25-year-open BGK problem; numerically verified `n ≲ 40`, OPEN at `n = 2^30`. **No
in-tree path to a complete proof exists**; a genuinely new analytic-NT / effective-equidistribution /
monodromy input is required and **none in the literature crosses `n^{0.989}→n^{1/2}` at β=4**.

Everything below is either (i) a more-attackable *equivalent form* of this wall, (ii) an *untried
literature lever* that might supply the missing input, (iii) the *off-BGK combinatorial* reframing
(real but shown to collapse to Johnson or equal the wall), or (iv) a *decisive computation* that is
numerically-undecidable at feasible scale. **None reaches closure — that gap IS the prize.**

---

## 1. LIVE open directions (the action menu)

### 1.1 Char-p energy/Wick attack forms — the most-attackable equivalent shapes of the wall
*(All reduce to the CORE; they are the cleanest handles, several with sorry-free reduction skeletons.)*

| lane | statement | in-tree status |
|---|---|---|
| **W3** hypercontractive step-antitonicity | all-r `A_r ≤ Wick` ⟺ `R(r)=M(r+1)/((2r+1)s·M(r)) ≤ 1` (one monotone ratio + finite base) | `_wf7W3_HypercontractiveStepAntitone` **sorry=0** (reduction real; ratio condition = wall) |
| **W5** dyadic-tower K-stability | finite base + per-level K-stability of the exact dyadic split ⟹ all-n bound | `_wf7W5_kstability_tower` **sorry=0** (`kstability_step`/`kstability_tower`) |
| **W1** Wick→Gaussian MGF | per-r `a_r ≤ K^r(2r−1)‼·n^r` ⟹ `exp(Kny²/2)` (all-r-at-once converter) | `_wf7W1_WickToGaussianMGF` 1 sorry = named residual |
| **W7** Newton-slope DC-dominance | `(1−ζ_p)`-adic NP slope split `E_r=E_r^{(0)}+DC+GEN`; `GEN ≤ 0 ⟹ K=1` | `_wf7W7_NewtonSlopeDCDominance` 1 sorry = `GEN≤0` (the wall) |
| **κ6** r=3 DC-Wick rung | `κ_6 = 40n + S`, gate `S ≤ 45n²−40n` (first rung past r≤2) | `Kappa6R3DCWickRung` — **conditional on char-0 `E_3=15n³−45n²+40n` as hypothesis** (probe-verified, not Lean-proven); only `κ_4=−3n` unconditional |
| **W6** theta-series count | `#{v∈L_p : v≠0, ‖v‖²≤φ(n)·2r} ≤ ε·(2r−1)‼·n^r` on the index-p sublattice `L_p⊂ℤ[ζ_n]` | `_wf7W6_shortvector_spur` — successive-minima product valid but **loose at small β** (exceeds Wick at low depth) |
| **MGF/saddle** | `‖η_{b₀}‖ ≤ log(2q²)/y*`, `y*²=2log q/n`; target-shape constant **C=3** pinned (`CoshMGFSaddleTargetShape`, axiom-clean) | conditional on the single open MGF inequality; ⚠️ **raw `E_r` MGF is VACUOUS** (DC term `cosh(ny*)>q²`) — must use DC-subtracted |
| **Poisson-averaged MGF** | the *slacker* target `Ψ(y*)≤q²` = Poisson(log q)-weighted avg of `A_r/Wick≤1`, tolerates ~2–6× per-r violations | `PoissonAveragedMGF` — strictly weaker than per-r Wick; the most forgiving equivalent form |
| **M1** principal-subtraction | direct proof of char-p `A_r ≤ Wick` via principal-term subtraction | lalalune's active route; `K_eff<1` empirically |

**Additional sorry-free reduction lanes onto the same crux** (each an independent axiom-clean *angle*,
all bottoming out at the char-p object — collect them because a future proof may attack whichever shape
is most tractable):
- **M1 count route** (c96,c99 — flagged "the single highest-value Lean reduction lane"): prize ⟸
  `Spur_r(p) = #{antipodal-free T, |T|≤2r : p | N(Σ±ζ_n^i)} ≤ ε·(2r−1)‼·n^r`. The reduction chain
  `mahler_norm_bound → countRoute_energy_bound → countRoute_prize_constant` is axiom-clean; the open
  step is the effective-Chebotarev count (§1.5). A **[π] non-archimedean object explicitly OFF the
  2nd-moment wall.** Pre-screen `Spur=0` for weight≤8 at prize primes; one genuine witness at
  exceptional `p=665857`.
- **M3 recursion route** (c96,c99): prize ⟸ `M3CrossStepBound`: per-step cross-energy slack
  `cross_r ≤ 2r·(2r−1)‼·n^{r+1}` in the proven recursion `E_{r+1}=n·E_r+cross_r`. Pre-screen holds while
  char-0-faithful (ratio 0.5–0.9), breaks (>1) exactly at the mod-p wraparound. A second independent
  axiom-clean angle onto the M1 object.
- **GaussianStepLaw** (c140, wf-F1): the uniform-in-r bound ⟸ ONE local per-step inequality
  `E_{r+1} ≤ (2r+1)·n·E_r` (`ρ(r)≤2r+1`), telescoping via `gaussian_moment_bound_of_stepLaw`
  (axiom-clean). Hypercontractivity-shaped, strictly more tractable. ⚠️ **β-conditional:** robust
  `β≳3.5`, VIOLATED at small β (n=128, β≈2.02: maxR=2.22>R(1)=0.89) — needs "β large enough" as a
  hypothesis (small-β mod-p coincidences suppressed at large β).
- **MOM / Salem–Zygmund deterministic MGF assembly** (c94): the randomness-free engine
  `(MOM) E[Z^{2r}]≤(2r−1)‼ ⟹` prize sup bound (`card_large_le_of_moment`, `sup_le_of_moment_bound`,
  axiom-clean, assembly constant `C_asm→1.43`). Verified equivalence `deterministic S-Z MGF ⟺ MOM`.
- **(P2-Slack)** (c122, wf-P2): `Spur_r(p) ≤ (2r−1)‼·n^r − A_r^ℤ(μ_n)` (spurious fits in the proven
  char-0 Lam–Leung slack). Sharp `K=1` (ε=0) form; numerically `Spur/Slack≤0.11` (≥9× margin) n∈{8,16,32}.
- **I031 SubGaussianTailBound** (c125): the cleanest isolated form — `#{v∈S:v>s}≤m·exp(−s²/2C) ⟹
  M(μ_n)≤√(2C₀n·log m)` (bridge `subgaussian_max_le` axiom-clean). = Lamzouri value-distribution CLT
  extended from `p^{o(1)}` to fixed `p^{1/8}` with sub-Gaussian proxy `O(n)`.
- **max-fiber `R_r = max_t N_r(t)`** (O227, comment 349): bound the depth-r dyadic-Sidon max-fiber at
  `r≈log m` — `E_r(G) ≤ R_r·|G|^r`.

**Why all reduce to the wall:** `ERM-at-r ⟺ M ≤ √((2r+1)n)`, so the energy route at `r≈ln q` *is* the
sup-norm bound. These lanes are valuable as the **cleanest forms to attack** (a single monotone ratio,
a per-level cross bound, a short-vector count, a per-period sub-Gaussian tail) — but the residual in
each is the same char-p crux.

### 1.2 Untried literature levers — need prize-regime instantiation (the "missing input" hunt)
*(Ranked by the campaign's F-lane scoring; NONE yet instantiated at thin `n=2^30`, multi-prime. These
are the genuine "could supply the missing analytic input" candidates — the highest-value untried work.)*

- **F1 ★ Wasserstein-tail upgrade of Kowalski–Untrau** (arXiv:2302.13670, 2505.22059): KU give the
  limiting *distribution* of `b↦Σ_{x∈μ_n}e_p(bx)` (sub-Gaussian scale) + an effective quantitative
  rate; a W₁ extreme-value upgrade over the `m=2^128` cosets would bound the max. **Untried in the thin
  regime** (the no-go was at thick scale).
- **F2 Kesten–McKay / ESD spectral-edge localization** (Kunisky arXiv:2303.16475): prove the empirical
  spectral distribution of `Cay(F_p,μ_n)` converges (local law) and localize the edge, instead of
  bounding `λ₂` directly.
- **F5 Subconvexity ⟹ effective equidistribution** (cat-map QUE / Hecke–Maass, arXiv:2402.14050):
  reframe `M ≤ C√(n log)` as an effective equidistribution rate for the μ_n-orbit.
- **F6 Multiplicative-chaos / log-correlated max + frequency-side chaining**: treat `b↦η_b` as a
  near-log-correlated field over `m=2^128` cosets; bound max via GMC / Fyodorov–Hiary–Keating. *(Caveat
  §4: periods are exchangeable white-noise — `Cov=−Var/(m−1)` distance-independent — which the
  meta-theorem says KILLS naive log-correlation; the lever must use frequency-side, not period-side,
  correlation.)*
- **F7 Stepanov/Rédei polynomial-method on the eigenvalue M(n) directly** (ported from generalized-Paley
  clique bounds, Hanson–Petridis/Yip arXiv:2304.13213): an auxiliary polynomial vanishing to high order
  on μ_n — non-2nd-moment, algebraic-multiplicity. **Untried for the eigenvalue (only the clique number).**
- **F8 Hidden-coset / average-over-m-coset entropy** (Legendre-PRF QR reduction, eprint 2024/1252):
  bound the advantage AVERAGED over a secret shift, push hardness into QR — a way to avoid the
  worst-case sup.
- **F9 Pseudocyclic-defect reinterpretation** (van Dam–Muzychuk association schemes): in a pseudocyclic
  scheme all nontrivial `|η|=√v` EXACTLY (= the prize bound); the cyclotomic scheme on μ_n is
  *almost* pseudocyclic — quantify the defect.
- **F10 Conway–Jones / Poonen–Rubinstein minimal-relation RIGIDITY → approximate cancellation**: the
  repo has Mann-style *exact* vanishing weight-sets but NOT the primitive-relation rigidity
  classification; transfer it to *approximate* cancellation.
- **F12 FKM Fourier-stability transport** (arXiv:1508.00512): `M(n)` is literally a DFT of `1_{μ_n}`;
  FKM prove a sub-√p estimate is STABLE under the DFT — transport a sub-√p input.
- **Liu–Zhou subgroup-restriction dyadic-tower eigenvalue recursion** (arXiv:1809.09829):
  `λ ≤ λ₂(Cay(Γ_k,T∩Γ_k)) + λ₂(Cay(Γ,T∖Γ_k))` recurses λ₂(μ_{2^μ}) on the index-2 sublattice — a true
  multiscale/dyadic-tower handle (note: dyadic crossCell descent itself is dead §4, but the *eigenvalue*
  recursion is distinct).
- **OSV short-Weil curve-blend** (arXiv:2211.07739) instantiated for the dilation family `b·μ_n`: the
  only F3 paper built for the thin regime where the classical Weil bound is trivial. *(Caveat: the
  generic OSV floor is `p^{3/7} ≫ p^{1/4}` — door shut at the prize point UNLESS the μ_n-specific
  instantiation beats the generic floor; that specialization is the untried part.)*
- **Murphy–Rudnev–Shkredov 49/20 energy** (arXiv:1712.00410) fed into **entropy / Kelley–Meka density
  increment** (NOT Cauchy–Schwarz): the standard energy→sup-norm step is the lossy Cauchy–Schwarz that
  strands at `n^{1−o(1)}`; replacing it with entropy-compression could in principle save the half-power.
- **Shifted-subgroup colinear-triple energy** (Macourt–Shkredov–Shparlinski arXiv:1701.06192): carries
  the additive shift `s` as a FREE parameter over the `m=2^128` cosets — the campaign only used
  collinearity at fixed shift.
- **Martingale / Azuma–Freedman over the 2-power tower filtration**: attacks the proven recasting
  `M(n)=√n·∏ρ(2^i)`, prize ⟺ `∏ρ(2^i) ≤ C√(log m)`; a Freedman/Bernstein bound on `Σ log ρ(2^i)` with
  predictable quadratic variation.

### 1.3 Collapse-audit survivors — the [Φ]/phase-aware methods that survived the meta-theorem
*(The §4 meta-theorem kills every 2nd-order/magnitude-only method; these four retain phase/valuation
information the meta-theorem cannot prune. The single most credible "third route" candidates.)*

- **N13 phase-aware contractive transfer operator** (the strongest survivor): `(𝒯f)(b)=f(b)+e^{iθ_b}f(ζb)`
  retains the relative dilation phase `θ_b=arg(η_{ζb})−arg(η_b)` that the FALSE magnitude recursion
  `M²≤2M(n/2)²` drops. Its spectral radius is the open object — needs the θ_b phase law.
- **N7 2-adic Newton polygon + Stickelberger squeeze**: NP slopes are `v_2(η_b)` (p-adic valuations),
  NOT functions of archimedean even power sums — two spectra with identical real moments differ here, so
  it escapes the meta-theorem's moment-blindness. Divisibility/Stickelberger squeeze on the period max.
- **N10 structured-net generic chaining**: metric entropy `N(ε)` under the dilation metric is an [H]
  quantity; generic chaining ABSORBS `√log` rather than estimating it. *(Caveat: N10 κ=O(1) was refuted
  as a window-MIDPOINT artifact — holds only where the worst word is consecutive; the prize-edge worst
  word is non-consecutive `x^15+x^4`, list ≈ n². So N10 must handle the gapped/edge regime.)*
- **E12 three-gap positional rigidity**: three-distance theorem structure on the orbit positions.

### 1.4 The off-BGK combinatorial core — distinct-γ union-count growth law
*(Real, p-independent, OFF the char-sum wall — but shown to collapse to Johnson at the proxy. The
remaining open question is its asymptotic growth law, which numerics cannot decide.)*

- **The object:** `U(n) = |⋃_{R∈binom(μ_s,k+1)} {γ_R}|`, `γ_R = −h_{a−k}(R)/h_{b−k}(R)` (forced bad
  scalars). **Formalized this session** as `_SpecF8_DistinctGammaUnionFloor`: the honest chain
  `#bad ≤ U ≤ n` (conditional on named `FarLineBudget`) + the Galois/rotation orbit structure of `U`,
  isolating the **single open obligation `DistinctGammaUnionGrowthLaw`** (poly-in-n ⟹ floor/prize holds;
  super-poly ⟹ fails). Has a machine-checked falsifiability witness (Prop is non-vacuous).
- **Equivalent face:** `#clique-orbits(m) = ` cyclotomic γ-collision structure of Schur-ratio level sets
  (`D*(m) = (orbit-size n)·#clique-orbits(m)`). The orbit machinery is fully proven (equivariance: this
  session's `_SpecS1`/`_SpecS3`); the open piece is the *count* of clique-orbits.
- **Why open / why numerically undecidable:** Johnson and the floor separate only at `n ≥ 256`
  (`C(256,128) ~ 10^75`); shallow-rung growth is super-linear (`oc₃~n²/32`, `oc₄~n³/512`, O196). The
  over-det count is `Θ(n³) ≫ budget n` (`OverdetIncidenceMaxClosedForm`), so it **collapses to Johnson**
  — meaning U *at the over-det binding* is the proxy, not the prize. **The genuine open question is
  whether the growth law admits a structural (generating-function / polynomial-method) bound.**
- **The most-promising structural sub-leads** (would give the decay if proven):
  - **`deg(#bad_r) < r` for all r** (c269 item 6, c274 — flagged PROMISING): the growing-slack
    mechanism; if `#bad_r` is a polynomial of degree `< r` in n, the budget crossing gives bounded `m*`.
  - **Single-orbit persistence `O_P = 1` at the binding imprimitive `d=2` direction for all `n=2^μ`**
    (c295, c289, c318 — PROMISING; `_Close27_RealImprimitive`/`_AngleC_PlateauBenignOrbitFloor`): via
    the `n→n/2` even/odd descent on the Schur-ratio. `O=1`/`j*=2` persistence (`SchurMinorStaircase`,
    c274 item 4) is the same object. ⚠️ the `_Close27_*` "decision" bricks are prose-only tautologies
    (§4) — the *persistence* is the real open question, not those bricks.
  - **`maxRatioMult` upper bound at the binding radius** (c269 item 3, c274): the union/fiber dual of U.
  - **Imprimitive `d=2` clean recursion (B27 plateau)** — bound `|oddPart|` (c274 item 3, c279).
- **⚠️ Spectrum-route caveat (this session, O237 DISPROOF_LOG):** the *char-free complete-homogeneous*
  upper bound on this object, `#{distinct h_r(R)} ≤ poly(n)·chooseCH`, is **REFUTED with poly(n)=n at
  s=32** and is exponentially loose for #bad regardless (§3.1). So the growth law must be attacked on
  the **union** count `U` directly (the realized distinct-γ), NOT the per-subset spectrum. The binding
  fold's `o(n)`-vs-`Θ(n)` dichotomy for `M_cross/c*(n)` (c376, c377) is the crisp open sub-question.

### 1.5 Good-prime / collision residual — the BGK p-dependence boundary
*(The combinatorial half is landable; the quantitative existence at polynomial field size is the wall.)*

- **Formalized this session** as `_SpecF7_GoodPrimeCollisionCount` (axiom-clean, real `lake build`):
  (A) h_r values **reduce compatibly mod p** (from the crown-jewel naturality `dividedDifferencePow_map`,
  `_SpecS3`); (B) a char-0 distinction survives mod p UNLESS `p | Norm(Δ)`, so the bad-prime set is
  **FINITE** (`card ≤ log₂ N`), union over pairs finite; (C) the named-open residual
  `EffectiveGoodPrimeExists` = a prime `Θ(n^β)` avoiding the finite bad set = **effective Linnik /
  Lagarias–Odlyzko / Thorner–Zaman PNT-in-AP**.
- **Crossover located** (`probe_hr_collision_badprimes.py`, this session): good primes EXIST below
  `n^4` at s=8,16 (combinatorial half holds), BUT the ratio `first_good/n^4` **CLIMBS** sharply
  (s=8: ~0.005 → s=16: ~0.1–0.44) as the spectrum `D0` grows exponentially. **That climb is the
  good/bad-prime crossover = the BGK p-dependence boundary** — quantitative good-prime existence at
  `n^β` as `n→∞` is the open analytic residual.
- **The deterministic ceiling is landed; the relative bound is the wall** (c130, wf-C1): the total bad
  set has `card ≤ Nconf·(φ(n)/2)·(log₂(2r)+1)` (axiom-clean `chebotarev_badprime_ceiling`), but
  `Nconf ≈ Σ_{k≤2r} C(φ(n),k)·2^k` is **super-polynomial at depth `r≈ln p`**. Turning this into the
  RELATIVE `Spur_r(p) ≤ ε·(2r−1)‼·n^r` (the M1 target, §1.1) needs the **PNT-in-AP band count to
  dominate = effective-Chebotarev EQUIDISTRIBUTION** (Lagarias–Odlyzko), NOT a ℕ-arithmetic fact.
  Realised bad density 0 (n=16) / 0.36% (n=32). **This is the single concrete analytic-NT input the M1
  count route needs** — and the same Linnik object as F7's `EffectiveGoodPrimeExists`.
- **Related:** `_AvW2` Spur_r(p) effective-Chebotarev count; the surviving `p≡1 mod 8` density-1/4 class
  IS the prize-prime class (Chebotarev/sum-of-two-squares cut is a SUPPORT constraint, not a Spur_r
  bound). Spur receipts: pre-screen `Spur_r(p)=0` weight≤8 at prize primes (finite check); genuine
  witnesses at exceptional `p=665857`, Fermat `641` — bad primes finite & small.

### 1.6 I031 dilation-quotient chaining (the surviving empirical non-BGK lead)
- `M(n) ≤ C·E[sup|G_b|]` over the `(p−1)/n` dilation-orbit reps — chaining on `F_p*/μ_n` collapses the
  metric entropy `log p → log(p/n)`. Substrate axiom-clean (`I031DilationOrbitReduction`: free action,
  `(p−1)/n` size-n orbits, sup-transversal collapse). **The campaign's strongest empirical signal for a
  bounded C** (`M/√(n log(p/n))` stable in `[1.15,1.40]`, slightly DECREASING at β=4, no upward trend to
  n=256). **Next:** a Lamzouri-type union bound at depth over the collapsed index set; verify whether
  `log(p/n)` vs `log p` actually changes the achievable constant.

### 1.7 Decisive computations — numerically-open, most decision-relevant
- **★ GPU n=64/128 D*(m) via the orbit-count recursion** (NOT brute enumeration — `C(64,22)~10^17`
  infeasible): the single most decision-relevant computation. The plateau-width law `w(n)` of the
  worst-direction cascade decides bounded-`m*` (prize-consistent) vs `log₂n` (Johnson). Needs a
  non-enumeration algorithm for the free-orbit count.
- **Deep-rung `A_r/Wick` trajectory at `r*≈log m`, n≥128** (worst bad prime): all exact probing confined
  to `r≤6` at sub-prize p; consistent with BOTH prize-true and BGK-tight.
- ⚠️ **Numerics provably cannot decide the prize** (§3 of the issue): the wall lives at `r≈log m`,
  `n=2^30`, unreachable; a closure needs a *proof* with external analytic NT.

---

## 2. What LANDED this session (2026-06-16, substrate — none a δ* pin)

All axiom-clean (`{propext, Classical.choice, Quot.sound}`), real `lake build` verified, on fork/main:
- `_SpecS1` — rotation-equivariance `h_r(ζR)=ζ^r·h_r(R)` (`7354afb27`).
- `_SpecS2` — multiset-count identity `Σ c_m = C(k+r,r)` + coeffVec reduction (`26666266f`).
- `_SpecS3` — **CROWN JEWEL** `dividedDifferencePow_map`: hypothesis-free naturality of the divided
  difference (hence `schurH=h_r`) under ANY ring hom (char-agnostic, total) + `schurH_galois`. The tool
  for reduction-mod-p collision analysis (`26666266f`). *(0xSolace independently re-landed the same fact
  as `_SpecS3_RingHomNaturality`/`dividedDifferencePow_ringHom`, `dbb6c778d` — distinct theorem names,
  coexist.)*
- `_SpecS6` — honest vacuous-regime record (`leading_exponent_pinned` holds only ABOVE the crossing fold
  = the vacuous large-r regime) (`26666266f`).
- `_SpecF7` — good-prime collision count (§1.5) (`ea81a1dbc`).
- `_SpecF8` — distinct-γ union floor + `DistinctGammaUnionGrowthLaw` (§1.4) (`26666266f`).
- Probes: `probe_spectrum_polyN_REFUTED_s32.py`, `probe_spectrum_provable_forms.py`,
  `probe_hr_collision_badprimes.py` (`e93c2de23`).

---

## 3. What did NOT work — deduped dead ledger (do NOT re-attempt)

### 3.1 ⛔ Reduces to the BGK/Paley sup-norm wall (real machinery, not a bypass)
The complete §8 issue-body ledger stands. Highlights + this session's addition:
- **★ Complete-homogeneous SPECTRUM floor REFUTED as a δ* pin (THIS SESSION, sharpens §6.2):** the bound
  `#distinct h_r(R) ≤ n·C(s+r−1,r)` ("poly(n)=n") is **FALSE at the prize scale s=32** (sample exceeds
  ceiling at r=2,3; `probe_spectrum_polyN_REFUTED_s32.py`); exact s=24,28 need poly=389,3444. Deeper
  kill: `#distinct h_r` is EXPONENTIAL while actual `#bad ~ n`, so the spectrum is **exponentially loose
  for #bad** — proving it would bound #bad by an exponential, NOT n, so it cannot pin δ* at any fold.
  Three regimes: small-r false, medium-r holds, large-r vacuous. The F1-F6 chain is conditional
  scaffolding with a refuted-as-stated central input. (Dossier `…-BCHKS-correct-object…` §D4/D4.1.)
- BCHKS-1.12 `|Σ_r|≤budget` as the prize object (`|Σ_r|` grows ≫ budget, vacuous); line-decoding/
  collinearity escape; crossCell dyadic-tower iteration (floors at `log₂n` ⟹ trivial `M≤n`);
  even-moment/additive-energy `A_r` (thin = neg-closed-random, grows with r); restriction/extension,
  Gross–Koblitz/Newton-polygon-as-magnitude, theta/AFE+de Finetti, circle method, Elekes–Szabó/
  sum-product (√-lossy), polynomial-method/slice-rank (`n^{0.92}`), hyper-Kloosterman/FKM (conductor too
  large), HOMDS/Schur-at-roots, random-RS capacity transfer, cosh-MGF/Bessel-saddle (raw MGF VACUOUS —
  DC term `cosh(ny*)>q²`, self-caught C72), deep-r Wick-deficit compounding, phase-alignment/per-coset
  descent (`−1∈μ_n` forces real = a SIGN not a phase), LP/SDP "third route", 50/100/140-conjecture
  sweeps (0 survivors), negacyclic crossCell calculus, theta/ideal-lattice (rank `φ(n)=n/2` ⟹
  `exp(Θ(n/2))` weight count = √n-deficit in disguise).
- **`discnogo`:** `disc(Ψ)=p^{m−1}·f²` class-field-fixed ⟹ symmetric/discriminant constraints give only
  a LOWER bound on M (wall provably archimedean).
- **Stepanov FULLY CLOSED** (`61187fbe0`): μ_n 0-dimensional, `μ_n⊂F_p` kills Frobenius, vanishing-rank
  saturates at n; the whole curve/Stepanov door shut. *(Caveat: §1.2 F7 is Stepanov on the EIGENVALUE,
  a different object — not yet closed.)*
- **discriminant/disc, completion-sum `Σ_j G_j`** (= open BGK content, phase-blind, O221), **OSV generic
  floor `p^{3/7}`**, **band dichotomy** (consecutive lacunary is benign-contiguous; floor witness must be
  GAPPED), the **off-BGK over-det/complete-homog/single-orbit/dyadic-recursion escapes** (all collapse
  to Johnson or equal the wall), **`delsartelpnogo`** (Delsarte/LP/Beurling–Selberg can't beat Parseval),
  **10 "new-math" relocations** (M(μ_n) is framing-INTRINSIC).

### 3.2 ⛔ Reduces to Johnson / Plotkin proxy
- Even/over-det far-line construction (`δ*_farline=1/2+1/n→1/2`, `m*=n/4−1` LINEAR); Hab25 (vacuous AT
  Johnson); antipodal-domination (pins `δ*=Johnson+1/n`); r=2 L4 rung (`n^{1.5}` overshoots); O191
  plateau dichotomy (proxy face, `m*(64+)` recursion-extrapolated not measured).

### 3.3 ❌ REFUTED-FALSE (machine countermodel)
- Odd/signed-moment thin-cancellation; additive large sieve (wrong side); fewnomial/Khovanskii;
  reverse LD⟹MCA; "window list constant L=2" (= dilation-invariant-word list only); char-0
  `δ*=(1−ρ)−log₂n/n`; base-case+monotonicity `A_r≤Wick` (n=64 kills it, `f(r)` 1.000→1.911);
  CensusDomination-via-K; wf-D3 pinch; shallow-band budget-conflation; v2(p−1)-gated 2-adic law; C8
  weight-bounded surrogate.

### 3.4 ⚠️ Finite-size artifact / 🚫 Larp / ↪️ Out-of-regime
- thin-Sidon `r_min` advantage (drops 11→8 at n=64); decoupling `c*=Θ(n)` (actually O(1)); DFT-uncertainty
  (Donoho–Stark `0.8n` above Johnson; Tao UP needs n prime); N9 `|V_4|=48`; BChKS admissibility (ε* defeats
  at FRI params); effective Katz/Deligne at fixed q (discrepancy `~m/√q=2^48≫1`).

---

## 4. ⚠️ Suspect / laundered / phantom watch (so future agents don't re-launder)

The campaign is **overwhelmingly honest** — nearly every overclaim was *self-retracted by its own
author* within the same session. Recurring patterns to not be fooled by on a merge:
- **"REDUCED-TO-CLOSED" / "one scalar inequality" framings** (W-lane, RhoContractiveAtDepth, `c_r≤1`,
  M3CrossStepBound, DCWickBound): all *true reductions* but the residual `= the BGK wall` (open). A
  reduction to the wall is not closure.
- **"K=1, prize-favorable, C≈1.25" numerics:** all at `n≤32–64` (brute-forceable band); `K_eff(n)`
  sometimes DRIFTS UP (0.55→0.66); cannot decide the asymptotic.
- **Self-retracted overclaims (recorded so they're not revived):** "δ* climbs to capacity / m*~log n"
  (engine `b<s` direction-cap artifact; far-line is Johnson-locked proxy); "prize ⟺ BCHKS-1.12 tight"
  (vacuous); "RepThree above p>12^{n/4}" (Injective-hypothesis covers only ±1 shapes); cosh-MGF saddle
  bridge (raw MGF vacuous); A41-A45 "char-0 defect=0 end-to-end" (A45 trinomial hyp = k=2 only); E6 even
  half "complete proof" (numeric only, lands B05 odd core); "0/10 lenses refuted" (4 cut by rate limit);
  the di Benedetto 3.9× "improvement" (Shkredov E3 is a SUMSET bound not the 6-fold energy);
  `_e04/_e09` M→δ* exponent bridge (does not compile).
- **PHANTOM bricks** (cited axiom-clean, verified ABSENT — §11): `_DstarGrowthLaw`, `_OPSingleOrbit`,
  `_DyadicRecursionDstar`, `PrizeEquivalencePin`, `FloorResonanceEnergyBridge`, `EffectiveTZLowerBound`,
  `_DefectOnsetOvershoot`/`SubsetSumThreePowExact` (re-created honestly), and ~14 more. The ON-BGK
  *conclusion* stands on VERIFIED bricks; the phantom *brick names* do not.
- **κ6 / E_3 dependence:** `κ_6≤45n²` is CONDITIONAL on char-0 `E_3=15n³−45n²+40n` carried as a
  hypothesis (probe-verified, not Lean-proven); only `κ_4=−3n` unconditional.

---

## 5. Honest bottom line

The prize is **OPEN and ON-BGK**. The campaign eliminated every elementary / second-order / off-BGK
route *as a theorem*, built the full axiom-clean substrate (energy ladder to E₇, Bessel char-0 face,
the spectrum-structure/minor-degree/orbit/naturality bricks, the necessary-condition theorem, the tight
two-sided reduction, this session's S1/S2/S3/S6/F7/F8), corrected the record (BCHKS-vacuous;
`capacity−δ*=m*/n`; the proxy artifact; the spectrum-route refutation; phantom bricks), and *proved
numerics cannot settle it*. The single core is the char-p Lam–Leung / BGK √-cancellation
`E_r(μ_n) ≤ (2r−1)‼·n^r` at `r≈ln q≈89`, `n=2^30` — proven char-0, numerically verified `n≲40`, OPEN at
prize scale. Evidence is **mildly favorable to the floor being TRUE** (`K_eff→1` from below; `a_r≤1`
Lam–Leung; wall-constant `C≈1.25` non-divergent) — but "mildly favorable" is not a proof.

**The highest-value OPEN work** (in priority order): (1) the §1.2 untried literature levers — F1
Wasserstein/Kowalski-Untrau, F5 subconvexity-QUE, F7 Stepanov-on-eigenvalue, the Liu–Zhou tower
recursion — these are the only candidates that could supply the *new analytic input* the wall demands;
(2) the §1.3 phase-aware survivors (N13 transfer operator, N7 2-adic NP) — the only "third routes" the
meta-theorem cannot prune; (3) the §1.4 distinct-γ growth law via the polynomial/generating-function
method (the off-BGK reframing, my F8); (4) the §1.7 GPU `D*(m)` orbit-count computation at n=64/128
(the decisive distinguisher). The char-p Wick lanes (§1.1) are the cleanest *forms* but their residual
is the wall itself.
