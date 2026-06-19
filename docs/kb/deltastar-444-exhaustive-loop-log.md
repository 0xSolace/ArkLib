# δ* (#444) — Exhaustive invent→refute loop log

**Protocol.** Each batch invents N genuinely-novel approaches to the char-p energy bound (the prize core),
from mathematical domains NOT yet tried, then adversarially refutes each. Verdict per approach:
- `REDUCES` — collapses to BGK / the moment-necessity or √p-vacuity obstruction / a known result.
- `NOT_NOVEL` — already tried this campaign or present in the literature.
- `REFUTED` — the claim is false (machine countermodel).
- `SURVIVES` — provably novel + escapes both obstructions + would-close + axiom-clean skeleton + un-refuted.
  **Only a SURVIVES triggers a stop + hard verification.**

**The two obstructions any approach must clear** (else REDUCES): (i) moment-necessity (must be cancellation,
not a count); (ii) √p-vacuity (Weil sees √p ≫ n for the thin subgroup n≈p^{0.19}). Plus the bridge result:
additive↔multiplicative is tautological (`_BridgeOneWall`), so a survivor must use genuinely joint/new structure.

**Already tried (avoid — all REDUCED/REFUTED):** joint-cumulant, excess-variety, p-adic-Iwasawa,
transfer-operator, Stickelberger-Stark, anti-concentration, ℓ-adic-sheaf/conductor/Swan, finite-free-edge,
cross-prime-sieve, Shaw-invariant, nilsequence/GTZ, Lorentzian/Hodge-log-concavity, subconvexity, relative-trace,
o-minimal/Pila-Wilkie, mixed-energy, Bourgain-Gamburd, explicit-Gauss-phase/HD/Gross-Koblitz, sum-product census,
LO/Halász, flag-SDP, Shearer, Berkovich, Drinfeld, restriction/decoupling/VMVT, Λ(q)/Rudin, dissociativity, B_h[g],
expander-mixing, eigenvalue-interlacing, NA-moment, good-prime-density.

---

## Running tally

| metric | value |
|---|---|
| batches run | 6 (domains 1–48 — POOL COMPLETE) |
| approaches invented | 55 (+1 failed) |
| REDUCES | 47 |
| NOT_NOVEL | 1 |
| REFUTED | 7 |
| **SURVIVES** | **0** |

> POOL (48 domains) exhausted at batch 6, 0 survivors. Batch 7+ = extended fresh domains + cross-domain
> hybrids. Also running in parallel: `ambitious-deep-assault` (meta-attack: break the obstructions
> themselves, backward-construction, non-Fourier/Walsh, RG bootstrap, holonomic/WZ, info-theoretic, wild
> leap; repair-before-refute).

> Note: domains 1–8 were independently invented+refuted **twice** (an `args`-propagation bug re-ran batch 1
> before being fixed); both runs gave 8/8 REDUCES with *different* inventions — strong independent confirmation.
> Batch index is now hardcoded in the workflow; batch 2 = domains 9–16.

## Per-batch log

### Batch 1 — domains 1–8 (8/8 REDUCES, 0 survivors)
- `condensed/pyknotic` → REDUCES: condensed math handles topological completions of non-discrete objects; the energy is finite/discrete — no purchase.
- `prismatic / q-de Rham` → REDUCES: Frobenius diagonal on the monomial basis; μ_n is 0-dim étale ⟹ q-de Rham in degree 0, no higher cohomology for the excess.
- `topological cyclic homology / TC` → REDUCES: the Verschiebung splitting is the already-refuted tower-2 coset-doubling (tautological bridge).
- `motivic / A¹-homotopy` → REDUCES: a motivic measure is a ring hom; energy-as-point-count fails; variety 0-dim (Weil-vacuous).
- `free entropy dimension` → REDUCES: a regularity/dimension invariant, insensitive to the spectral edge.
- `subfactors / planar algebras` → REDUCES: planar-algebra trace is a positive tracial state ⟹ τ(T^{2r}) is a genuine 2r-th moment = moment-necessity.
- `quantum groups / Hecke at roots of unity` → REDUCES: R-matrix/Yang–Baxter/skein relations live in ℚ(ζ_n) ⊂ ℂ = char-0 ⟹ √p-vacuity (cyclotomic door).
- `modular tensor categories / TQFT` → REDUCES: MTC S-matrix is a one-sided Fourier with quadratic-form phases; √p-vacuity worse, not escaped.

### Batch 2 — domains 9–16 (7 REDUCES, 1 REFUTED, 0 survivors)
- `vertex operator algebras / conformal blocks` → REDUCES: the tautological bridge in modular language; modular-coefficient bound is √p-vacuity.
- `Bethe ansatz / Yang–Baxter` → REDUCES: μ_n is abelian ⟹ lands on the FREE (zero-scattering) integrable point; every R-matrix lever is vacuous.
- `RMT loop equations / Tracy–Widom` → REDUCES: loop-equation edge power comes entirely from ensemble self-averaging (1/N expansion); a deterministic matrix has none.
- `determinantal point process` → REDUCES: √p re-entry as a coefficient; subgroup-scale DPP variance can't reach the worst-case sup.
- `matroid / Lorentzian DEEP` → REDUCES: the energy is a square `E_r=Σ_c c(c)²` (a 2nd moment of rep-counts); the per-element form is literally the moment.
- `property (τ) / Lindenstrauss–Margulis` → **REFUTED**: the named spectral-gap datum is false/vacuous (the averaging operator's eigenvalues ARE the periods — circular; explicit countermodel).
- `unipotent / effective Ratner` → REDUCES: the generator-type hypothesis is violated — the dilation orbit is abelian/degenerate, all effective-Ratner refinements vacuous.
- `heat-kernel / spectral-zeta` → NOT_NOVEL+REDUCES: already catalogued (DISPROOF_LOG D8-1); heat trace is a moment of the spectrum.

### Batch 3 — domains 17–24 (8/8 REDUCES, 0 survivors)
- `quantum ergodicity / QUE` → REDUCES: QUE equidistributes only above Planck scale ℏ=1/p ⟹ √p-vacuity floor.
- `property (T) / Kazhdan` → REDUCES: category error — the acting group (translations) is abelian ⟹ no property (T).
- `Delsarte LP / SOS hierarchy` → REDUCES: exact Lasserre/Putinar SOS↔moment duality — the degree-r SOS cone IS the degree-r moment hierarchy = moment-necessity.
- `Nullstellensatz / polynomial calculus` → REDUCES: algebraic-proof-system dual of the Bezout no-go; an NS/PC certificate is a count = moment-necessity.
- `slice rank / Croot–Lev–Pach` → REDUCES: the wraparound excess tensor has an EMPTY diagonal ⟹ CLP/slice-rank is vacuous.
- `incidence geometry / Guth–Katz` → REDUCES: `Σ_s I(s)²` is itself the additive-energy count; a partitioning bound on it is a nonneg count = moment-necessity.
- `geometric complexity theory` → REDUCES: Kronecker/plethysm coefficients are dimensions ≥ 0 (positivity) — no cancellation.
- `theta correspondence / Weil rep` → REDUCES: the Weil θ-kernel for e_p is the quadratic Gauss-sum kernel ⟹ √p-vacuity + tautological bridge.

### Batch 4 — domains 25–32 (6 REDUCES, 2 REFUTED, 0 survivors)
- `trace formula (Arthur–Selberg)` → REDUCES: μ_n is an abelian torus ⟹ elliptic term is the tautological bridge; escapes neither obstruction.
- `Cohen–Lenstra (effective)` → **REFUTED**: Cohen–Lenstra controls the class group (unit-invariant) — the wrong object; false derivation, in-tree countermodel.
- `heights / Bilu equidistribution` → REDUCES: weak-* convergence controls the bulk `∫f dμ`, not the sup (worst case).
- `Baker linear forms in logs` → REDUCES: archimedean Baker attacks the wrong side; irrelevant to the upper-bound norm chain at deep r.
- `Schmidt subspace theorem` → REDUCES: the height floor `p^{2/n} → 1+o(1)` at prize thinness — excludes nothing.
- `Ruelle resonances / thermodynamic` → REDUCES: the partition function `Σ|η_b|^{2r}` is a nonneg sum ⟹ its rate is a moment = moment-necessity.
- `persistent homology / TDA` → **REFUTED**: persistence diagrams are distance-based (VR/Čech), provably blind to phase cancellation; machine countermodel.
- `optimal transport / Wasserstein` → REDUCES: OT is a theory of non-negative mass; forming the measure collapses the n-unit-phase cancellation.

### Batch 5 — domains 33–40 (6 REDUCES, 1 NOT_NOVEL, 1 failed, 0 survivors)
- `quantum walk / amplitude amplification` → REDUCES: Szegedy correspondence `λ↦arccos(λ/n)` is an antitone bijection — the walk phase is the same period spectrum.
- `online learning / regret minimax` → REDUCES: the "regret triangle" is just the triangle inequality maxed over b; clears neither obstruction.
- `tensor network / MPS` → REDUCES: the discrete-log carry bond is volume-law ⟹ Schmidt rank = n across every cut (no low-bond-dimension bound).
- `noncommutative geometry / spectral triple` → REDUCES: the heat trace equals η_b only at t=0 (spectrum drops out); damping only for t>0 where it ≠ η_b.
- `p-adic Hodge / (φ,Γ)-modules / Sen weights` → REDUCES: Sen/Hodge–Tate weights are p-adic-valuation data, archimedean-blind (in-tree `_ValuationClassBarrier`); energy is an archimedean magnitude.
- `crystalline / Newton-above-Hodge` → REDUCES: bounds the p-adic *slopes* (wrong column); the energy count is governed by archimedean magnitudes.
- `Drinfeld modular / function-field` → FAILED (transient server error; not counted — re-roll candidate).
- `Bourgain–Gamburd affine (deep)` → NOT_NOVEL: already in-tree (`_wfA11_affine_bg_gap`, `_wfT24_affine_koopman_density`).

### Batch 6 — domains 41–48 (4 REDUCES, 4 REFUTED, 0 survivors) — POOL COMPLETE
- `large deviations / Gärtner–Ellis` → **REFUTED**: the GE rate is a Legendre–Fenchel transform, *always* convex — structurally blind to the multiplicative structure.
- `free convolution / rectangular R-transform` → REDUCES (NOT_NOVEL core): already `_NovelFiniteFreeEdge`/`_wfA15`.
- `Cohn–Elkies LP dual` → REDUCES: the dual magic-function certificate consumes the moment ladder = moment-necessity.
- `cluster algebra / pentagon identity` → **REFUTED**: a pentagon constrains only 5 named terms' phases, modulus-locked at √p — can't improve the m-term sum.
- `Kontsevich–Zagier period` → **REFUTED**: KZ is an *independence* statement (lower bound on transcendence degree) — the wrong direction (we need an upper bound).
- `tropical / non-archimedean Monge–Ampère` → **REFUTED**: total MA mass = normalized Newton-polytope volume = a count (Chambert–Loir).
- `continuous model theory / metric stability` → REDUCES: tame-counting controls the *cardinality* of distinct types, never the *magnitude* of one value.
- `Host–Kra nilfactor (deep Gowers)` → REDUCES: the bottom Gowers rung `‖𝟙_{μ_n}‖_{U²}^4 = p^{-3}Σ_b|η_b|^4` IS the moment ladder.

(batches appended below as they complete)
