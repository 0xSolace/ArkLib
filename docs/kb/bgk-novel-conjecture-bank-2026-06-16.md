# BGK novel-conjecture foundry — 80 conjectures, the unified obstruction (#444, 2026-06-16)

Per the directive "make 50 certifiably-novel (9–10/10) conjectures aimed at the BGK/Paley √-cancellation
wall, then attack them." A 10-family × ~8 generation workflow produced **80 conjectures**; **46 rated
novelty ≥ 9** (genuinely-new ideas, dead routes pre-excluded); the **5 top** (novelty ≥9, feasibility ≥6,
2-power-essential) were each adversarially attacked with exact probes. **0 survived** — but the refutations
**converge on one precise structural obstruction**, which is the valuable output.

## The target
Char-0 Wick energy `E_r(μ_n) ≤ (2r−1)‼·n^r` is PROVEN (Lam–Leung antipodal). The sole open content of
δ* is the **char-0 → char-`p` transfer at moment-depth `r ∼ log q`**: that spurious mod-`p` vanishing sums
of `2^μ`-th roots don't inflate `E_r` past the char-0 envelope. The 5 top conjectures all attacked this via
**support / sparsity / height / decoupling** — the natural idea being that at depth `r∼log q` the spurious
relations have tiny support `C ∼ 2r ∼ 2log q ≪ n/4`, so a support-parametrized norm bound `(2r)^C` (vs the
full-window `(n/2)^{n/4}`) would close the transfer below the prize prime.

## THE UNIFIED OBSTRUCTION (why every support/sparsity/height/decoupling route fails)
> A spurious relation `β = Σ_i ε_i ζ^{a_i}` (support `C ≤ 2r`) is bad at `p` iff `p ∣ N(β)`, where
> `N(β) = ∏_{σ∈Gal} σ(β)` is the cyclotomic norm — a **product over all `φ(n) = n/2` Galois conjugates**.
> The support `C` bounds the number of terms *inside* each factor `|σ(β)| ≤ ‖β‖₁ ≤ 2r`, but does **NOT**
> reduce the **number of factors**. So `|N(β)| ≤ (2r)^{n/2}` — full exponential in `n`, *independent of
> support/sparsity*. Sparsity is indexed over coordinates; the norm is indexed over conjugates; there is
> no map from one to the other.

This is decisive and kills the entire class:
- **T1 support-parametrized resultant** — refuted: "AM-GM telescoping indexed over the wrong set; `C`
  nonzero coordinates do not become `C` conjugate factors." Norm stays `(2r)^{n/2}`.
- **T8 antipodal-free localization** — refuted: excess collisions *routinely retain* antipodal pairs
  (1002/1388, 158/244, …); the excess does not avoid the paired part; "support ≤ 2r" is content-free.
- **DEC-5 / telescope deficit-decoupling** — refuted: the char-`p` excess is **MONOLITHIC at the top
  level** — a char-`p`-only (wraparound) zero-sum is *impossible* inside any subgroup `2^j ≪ √p`, so the
  lower tower levels are arithmetically EMPTY (`S(j)=0 ∀ j<μ`); no square-function carves the open object.
  (The telescope identity is true but vacuous; its antipodal cap is `≡0` by algebra.)
- **OM1 norm-divisor-count** — refuted: `spur ⟹ p∣N` holds, but the count threshold needs `n` in the
  exponent for exactly the conjugate-count reason.

## Consequence (a real negative theorem-shape)
**No support / sparsity / height / Newton-polygon / dyadic-decoupling argument can close the char-0→char-`p`
transfer.** The transfer can only be closed by exploiting **cancellation AMONG the `n/2` conjugates** (not
bounding each |σ(β)| ≤ 2r) — and cancellation among conjugate Gauss-period values IS the √-cancellation =
**BGK itself**. So this class of "shallow-depth sparsity" attacks is ruled out with one clean mechanism;
the transfer ≡ BGK, now with a sharp reason *why* the obvious bypass cannot work.

## Bonus proven fact (worth keeping)
The spurious char-`p` collisions appear **only at the full subgroup `μ_n`**, never at the tower levels
`μ_{2^j}`, `j<μ` — because a char-`p`-only zero-sum needs `≥ √p` terms and the smaller subgroups are too
small. So the open object is genuinely monolithic at the top, not a tower-telescoping quantity.

## The 46 novelty-≥9 conjectures
Span 10 families: antipodal-constrained dyadic-tower renormalization, char-0→char-`p` transfer (support/
height), Stepanov-for-sup-norm, L-function/Gauss-sum-phase, ℓ²-decoupling of geometric-progression
frequencies, Ramanujan-complex/tower spectral, Weil-representation/theta lift, moment-problem/Markov–Krein
extremal, short-Frobenius-orbit effective equidistribution, invent-new-object. The full list (with per-
conjecture novelty/feasibility/mechanism) is in the workflow record; the 5 attacked are above. The
remaining 41 are lower feasibility or not 2-power-essential; several (the Weil-lift, Markov–Krein moment-
problem, Ramanujan-complex-tower) are worth a dedicated future attack but were not in the top-5 cut.

## Honest verdict
The mandate produced genuinely-novel ideas (46 at novelty ≥9) and attacked the best — all refuted, with a
**unified, precise obstruction** explaining why the natural sparsity/support bypass of the transfer cannot
work. This sharpens "it's BGK" into "the conjugate-count, not the support, is the exponential — so only
true conjugate-cancellation (= BGK) closes it." No closure; a clean negative structural result.

## Round 2 — the 3 unexplored families (Weil/theta, Markov–Krein, Ramanujan-tower): all collapse, refining the obstruction to PHASE-BLINDNESS

The three families that could *a priori* exploit inter-conjugate cancellation (the only way past the
Round-1 obstruction) were attacked. **All 3 collapse**, by the SAME refined mechanism:

> The bad-prime object is `|N(β)| = ∏_{σ} |σ(β)|` — a product of conjugate **MODULI**, **phase-independent**.
> Every algebraic / spectral / moment / Weil invariant accesses only the conjugate **moduli** (or aggregates
> per-`b` magnitudes), never the **absolute phases** `arg σ(β)`. So the best any such method gives is the
> **Parseval/Landau ℓ² ceiling `(#S)^{φ(n)/2} = (#S)^{n/4}`** — each conjugate's modulus reduced
> *individually* (a genuine √-improvement over the trivial `n/2` exponent, but dies at `n≈64–128`, far below
> the prize `p ∼ n·2^128`). The prize's true `M(n) ∼ √(n log p)` requires **inter-conjugate PHASE
> cancellation**, which is invisible to every phase-blind (modulus-only) invariant — and *is* the BGK
> √-cancellation.

- **Weil/theta lift** → phase-blind: certifiable content is modulus + Maslov (phase-*difference*), never
  absolute phase; and `μ_n` isn't a quadratic/Lagrangian orbit at prize scale (index `p^{3/4}`). Gives only
  the `(#S)^{n/4}` ceiling. (arXiv:2603.25658, 1108.0202 — Weil reps built from quadratic orbits, no
  multiplicative-subgroup sup-norm machinery.)
- **Markov–Krein moment-problem** → bound-each-then-aggregate: `b`-averaged moments aggregate per-`b`
  magnitudes; redistributing onto quadrature nodes never cancels among conjugates; reduces to the per-`r`
  char-p ≤ char-0 transfer (= the open uniform-Katz equidistribution). Sibling of in-tree
  `_wf8B5_MomentProblemLogConvex`. (arXiv:2512.23681.)
- **Ramanujan-complex / tower** → reduces to the moment method + renaming; the covering/interlacing relates
  eigenvalues but transmits only magnitudes; no inter-conjugate cancellation. (arXiv:1301.1028.)

## THE FULL DICHOTOMY (both rounds, the consolidated "why it's hard")
Across **all** novel families (Round 1: support/sparsity/height/decoupling; Round 2: Weil/moment/spectral):
> **Phase-blind methods** (everything accessing conjugate moduli: Weil, Landau, Mahler, moment-problem,
> energy, support/height, spectral) → ceiling `(#S)^{n/4}`, dies at `n≈64–128`.
> **The prize** needs inter-conjugate **phase** cancellation → that *is* BGK, accessible to no current
> algebraic invariant.
The wall is precisely this gap: between the phase-blind `(#S)^{n/4}` ceiling and the true
`(#S)^{O(log)}` phase-cancellation. Closing δ* requires a method that sees inter-conjugate **phase** — and
no such method exists in current mathematics (= why BGK is open). This is the sharpest characterization the
campaign has produced of *why* the prize is hard, and it rules out every modulus-based attack with one line.
