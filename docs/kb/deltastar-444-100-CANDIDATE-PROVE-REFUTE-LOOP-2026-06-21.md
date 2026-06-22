# The 100-candidate propose→refute loop on the Paley half-power

*#444, 2026-06-21. 100 bold candidate proofs of `M(μ_n) ≤ C√(n log p)` across 20 mathematical domains, each
proposed then adversarially refuted, with independent verification of any claimed survivor. Result: **0/100
survive.** Honesty contract: every candidate is a labeled attempt; none is a proof. This is the most
comprehensive single refutation pass of the campaign, and it produced new family-killing no-go insights.*

---

## Verdict: 0 survivors / 100

20 agents (one per domain) each invented 5 genuinely-bold, well-researched candidate proofs distinct from the
~74 already-refuted angles, then harshly self-refuted each; claimed survivors got an independent adversarial
refuter. **Self-claimed survivors: 0. Verified survivors: 0.** Every candidate broke at a precise step, each
relocating to one of the three proven obstructions (phase-blind pins to `√p`/`≥n`; archimedean modulus not
algebraically certifiable; randomness must be *established* not exploited) or a named already-refuted angle.

Domains swept: analytic NT (Kuznetsov/spectral-large-sieve, subconvexity, delta-method, van der Corput in the
exponent), probability (LSI/Herbst, Talagrand T2 transport, Efron–Stein, Chatterjee exchangeable-pairs,
Strong-Rayleigh negative dependence), additive combinatorics (Croot–Sisask, slice-rank on the complex phase,
Gowers inverse, dependent random choice), arithmetic geometry (perverse sheaves/weights at growing `r`,
effective Katz, motivic/Hodge), orthogonal polynomials/RMT (Riemann–Hilbert, edge universality, Coulomb-gas
loop equations), spectral graph (interlacing families/MSS, non-backtracking, zig-zag), harmonic analysis
(decoupling, multilinear Kakeya, broad-narrow restriction), representation theory, ergodic/dynamics, extremal
combinatorics, SOS/convex (complex-modulus Lasserre, hyperbolic polynomials), info/coding, cyclotomic/Galois,
math-physics (QUE/Hecke sup-norm, Bethe ansatz), model theory (Pila–Wilkie), operator algebras (free entropy),
arithmetic dynamics (equidistribution of small points), TCS (extractors), geometry of numbers (Cohn–Elkies LP),
and invented cross-domain syntheses.

## The closest 5 (and the exact missing step)

1. **Kantorovich/transport duality** `|η_b| ≤ n·W₁(P_{μ_n}, U)` — the *only* genuinely non-phase-blind candidate
   (an `L∞`-over-Lipschitz, not `L²`, statement). Missing: an upper bound `W₁ = O(√(log p/n))`. But `W₁` is
   governed by the *entire* discrepancy; bounding it = controlling *all* Fourier coefficients at once — strictly
   harder than the one coefficient asked for. Relocates "bound one coefficient" → "bound the whole discrepancy."
2. **Croot–Sisask almost-periodicity** — the unique additive-combinatorics tool with native `L∞`/high-`Lᵖ`
   output (right *shape*). Missing: a variant that does not collapse on indicators (`‖1_A‖_p^p = |A|`); it must
   see the phase `Lᵖ` norm as genuinely sub-Gaussian = *prove* the phase CLT (obstruction 3).
3. **Strong-Rayleigh / negative-dependence** (Pemantle–Peres) — a genuine `L∞` sub-Gaussian tail with no
   independence. Missing: a non-degenerate *measure*. `μ_n`'s repulsion is deterministic algebraic rigidity, not
   a negatively-dependent law; manufacturing randomness forces the phases into the coefficients (phase-blind).
4. **Chatterjee exchangeable-pair TAIL** (not the CLT theorem) — concludes variance-driven Bernstein tails, the
   `variance≍n` vs `range≍n` distinction the prize needs. Missing: the conditional second moment
   `E[(η_b−η_b')²|η_b]` bounded by the constant proxy `n` — but it is **self-referential**, `≍ |η_b|²` exactly on
   the rare large-period event the tail targets. Stalls at energy.
5. **Efron–Stein / entropy method** — variance-not-range Bernstein (correct mechanism in principle). Missing: a
   product/resampling structure; `μ_n` is a single deterministic configuration, and the Efron–Stein bound
   provably *equals* the iid-comparison bound, delivering the prize only where independence is already assumed.

## Genuinely-new no-go insights (family-killers, worth formalizing)

1. **The period Gram is a circulant** with eigenvalues `{|η_b|²}` and eigenvectors the additive characters.
   Crisp impossibility: any spectral/Rayleigh certificate equals `M` restated, and a non-phase-blind test vector
   **must literally be the top eigenvector `e^{−i·arg η}`** — you cannot write one without already knowing the
   phases. *The cleanest statement of why all spectral routes are circular.*
2. **The self-referential-remainder diagnosis** (`remainder ≍ |η_b|²` on `{|η_b| large}`) kills the **entire**
   Stein / Chatterjee / exchangeable-pair family (CLT *and* tail flavor) in one structural stroke — the
   conditional-variance controlling functional grows like the square of the value precisely on the event the
   bound targets, so the constant proxy `n` is never valid there. One brick retires a whole method class.
3. **`η_b =` exact inverse-DFT of the `n` Gauss-sum phases `{arg τ(χ): χⁿ=1}`**, each of pinned modulus `√p` —
   the canonical statement of the open core, isolating exactly where subconvexity has no purchase (it sees an
   `L`-moment over a family, never a single phase). Heath-Brown–Kummer territory.
4. **The LSI-gap relocation**: the orbit-symmetry (cyclic-shift) walk has spectral gap `≍ 1/n²`, so Herbst
   over-counts the variance proxy by exactly `n²` (giving `n^{3/2}`, worse than trivial) — pinpointing *where*
   the `√n` is lost in every log-Sobolev attempt.

## Conclusion

100 fresh, domain-diverse, well-researched candidate proofs; **0 survive adversarial refutation.** The wall is
now confirmed irreducible across essentially the entire relevant mathematical landscape — analytic NT,
probability, additive combinatorics, arithmetic geometry, RMT, spectral graph theory, harmonic analysis,
representation theory, ergodic theory, SOS, coding, Galois, math-physics, model theory, operator algebras,
arithmetic dynamics, TCS, geometry of numbers. Every route relocates to the one missing theorem: an effective,
uniform-in-`p`, worst-case CLT for short cyclotomic coincidences at depth `log p`. Not closure — the most
thorough demonstration yet that the proof awaits a genuinely-new theorem, with four new family-killing no-gos
identified for formalization.

---

## Loop 2 (exotic frameworks): 0/100 survivors — 200/200 total refuted

A second 100-candidate loop over 20 *exotic* frameworks (Langlands functoriality, beyond-endoscopy Ψ-operator,
theta/Weil oscillator representation, relative trace formula, cyclic base change, condensed/perfectoid/
Fargues–Fontaine, nilsequences over the multiplicative group, effective Chebotarev/Sato–Tate, RMT
moment-conjecture/CFKRS recipe, Berkovich/tropical, vanishing-cycles, quantum groups/Bethe ansatz, traffic free
probability, Schmidt subspace, Macdonald/crystals, mod-Gaussian convergence, motivic regulators, QUE/Hecke
sup-norm, arithmetic microlocal, non-abelian Bourgain–Gamburd, persistent homology, resurgence, and a
maximally-invented swing). **0 self-claimed survivors, 0 verified survivors.** Every candidate relocates by the
same **double-orthogonality**: *p-adic + average* (what the geometric/automorphic machinery delivers) vs
*archimedean + worst-case* (what the prize demands). Every functorial/geometric lift collapses to **rank-1
abelian Kummer** (`_A5TwistedMonodromyAbelianVerdict`) and transfers nothing.

### The 3 closest (exact missing step)
- **Effective Chebotarev bad-prime count** (closest, genuinely arithmetic). Bound #bad-at-depth-`r` prize-primes
  by (#prime-divisors of one norm ≤ `log₂ N`) × (#norms). *Missing:* the Chebotarev error is governed by the
  compositum discriminant = the resultant height `b(r)^{φ(n)/2}` — **exponential** in `n`, so the rate beats
  `√p` only for `n = O(log p)`, polynomially short of `n ~ p^{1/4}`. (`_wf6C1` formalizes the count side.)
- **Mod-Gaussian / quantitative CLT for the Gauss-sum phases** — the *only surviving shape* (phase-aware +
  archimedean + establishes a uniform CLT). *Missing:* effective-in-`p`, order-`r≈log p` cumulant decay of
  `u_j = G(ω^{jn})/√p`. Every cumulant input is either the energy `E_r` (phase-blind floor) or a Weil bound
  (pins `√p`); the order-`>log p` decay *is* the conjecture.
- **Strong-Szegő / `H^{1/2}`-critical restatement** (genuinely-new analytic framing). The Gauss-phase symbol sits
  *exactly* at the `H^{1/2}` critical regularity — the Szegő-convergence boundary. *Missing:* prove the symbol is
  on the good side of `H^{1/2}` **uniformly in `p`**; every nearby tool needs `H^{1/2+ε}`, and the `ε` is the
  entire half-power. The sharpest analytic statement of "off by an epsilon."

### Three new obstruction-sharpening insights (worth formalizing as no-go bricks)
1. **Discriminant / phase-DOF dichotomy:** any `p`-independent algebraic invariant of `μ_n` carries
   bounded-discriminant magnitude/count data only, while the archimedean phase has `~n^{3/2}` free DOF forcing
   *exponential* discriminant — so no effective-Chebotarev constant can be simultaneously `p`-uniform AND
   phase-controlling. Subsumes the whole Chebotarev/equidistribution-count lane.
2. **Zero-density ⊥ far-tail:** ratios/CFKRS/L-function-statistics are *small-value* (zero-repulsion) technology;
   Paley-max is *large-value* (far-tail). For a deterministic family there is no proven `zero-density ⟹ max`
   implication — explaining why the entire L-function-statistics shelf is structurally orthogonal to the prize.
3. **`H^{1/2}`-criticality (definitional):** makes obstruction-1's "phase-blind methods miss by a power" precise
   as "the symbol is `H^{1/2}`-critical and the prize is the good-side-uniform statement."

**Verdict (loops 1+2):** 200 fresh candidate proofs across ~40 mathematical domains — including the most
advanced functorial, geometric, probabilistic, and analytic machinery — **0 survive**. The wall is irreducible;
the proof awaits the one missing theorem (effective, uniform-in-`p`, worst-case, order-`r>log p` phase CLT for a
single deterministic abelian configuration), which the mod-Gaussian framing names most precisely and the
`H^{1/2}`-criticality restates most sharply. Not closure.
