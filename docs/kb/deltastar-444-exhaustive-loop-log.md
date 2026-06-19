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
| batches run | 2 (domains 1–16) |
| approaches invented | 24 |
| REDUCES | 23 |
| NOT_NOVEL | 0 |
| REFUTED | 1 |
| **SURVIVES** | **0** |

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

(batches appended below as they complete)
