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
| batches run | 1 |
| approaches invented | 8 |
| REDUCES | 8 |
| NOT_NOVEL | 0 |
| REFUTED | 0 |
| **SURVIVES** | **0** |

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

(batches appended below as they complete)
