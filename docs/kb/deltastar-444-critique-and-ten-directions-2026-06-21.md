<!-- #444 / Paley-BGK. Criticism of the b-summation-dichotomy / per-b* paper + 10 ledger-verified
ranked novel directions (2026-06-21). The dichotomy is now a LANDED axiom-clean theorem
(_MixedMomentPhaseBlind, commit 51437057c). The criticism: its stated generality leaks on phase
functionals, but the substance holds (every door reflects the same archimedean crux). The 10 directions
all reduce or are not-yet-tested, with DIR9 (ordered-walk Doob majorant) the sharpest surviving frontier:
the first object both a tight majorant of M AND provably off the b-sum. -->

# Criticism of the b-Summation Dichotomy, and Ten Ranked Novel Directions

## 0. Status

The b-summation dichotomy is now a **formalized, axiom-clean theorem**
(`_MixedMomentPhaseBlind.mixed_moment_eq` + `mixed_moment_nonneg_real`, commit `51437057c`, real
`lake build`): `Σ_{b∈F} η_b^a conj(η_b)^c = q·N_{a,c}` (a non-negative integer count), so every
`b`-summed polynomial in `(η_b, conj η_b)` is phase-blind. This document criticizes the *paper built on
it* (the per-`b*` program), then gives ten ledger-verified ranked directions.

## 1. Criticism: what the paper missed, got wrong, didn't go far enough

**(a) Overstated generality (the real logical flaw).** The headline "any `b`-summed tool is phase-blind
⟹ the only escape is per-`b*`" is proven *only* for **polynomials** in `(η_b, conj η_b)` and magnitude
level-sets. It silently conflates two different sets: *phase-blind* (the `b`-sum kills cross-phase) is
not the same as *magnitude-only* (a property of polynomial/level-set functionals). A `b`-summed
functional with a **non-polynomial phase weight** — e.g. the phase-windowed moment
`Σ_b |η_b|^{2k}·1[arg η_b ∈ arc]`, or a dyadic **phase square function** `Sup_t Σ_I |Δ_I S^{(t)}|²` —
is `b`-summed yet *outside* the ring the dichotomy quotients by. The honest scope is "any `b`-summed
*polynomial* functional, and any magnitude-threshold count, is phase-blind." The leap to "ANY `b`-summed
tool" is the genuine miss.

**(b) The blind spot is real but already filled — and reduces.** I verified the coupling is *non-trivial*:
the `|η_b|^{2k}`-weighted mass is **~5.5× non-uniform across 12 phase arcs** (probe
`probe_phase_amplitude_coupling.py`) — so phase functionals are not vacuous. But the campaign already
built the sharpest instance, `_PhaseSquareFunctionMajorant`, and it reduces: the `b`-sum/Parseval pincer
(`Σ_b ‖η_b‖² = q·n`) controls only the **average** over the parameter; the **sup** is the wall. Every
phase-functional file in the cone (`_PhaseCorrelationOrbitCollapse`, `_PhaseLinearFormDecoupling`,
`_PhaseMartingaleConcentration`, `_DyadicPhaseChaining`) collapses the same way.

**(c) Didn't go far enough on its own per-`b*` machineries.** It presented the five per-`b*` tools as
live escapes; in fact the campaign's instantiations *demonstrably reduce* — Stepanov-at-`b*` collapses
to the trivial degree bound (multiplicity 1 on `μ_n`; `_StepanovStructuredVacuous`), cyclotomic-height
is exponential (`b(r)^{n/2}`, `_AvRH_ResultantHeightSharp`), clustering is Johnson-gated. A deeper paper
would have *proven* these reductions rather than crediting them as open.

**(d) The sharp meta-theorem it should have proven ("every door is a mirror").** The right statement is
not "`b`-summed ⟹ blind" but: *any functional admitting an `L²`/averaging control over **any** auxiliary
parameter (over `b`, over `t`, over an ordering) is controlled only at its average and leaves the
**sup** = the wall; and per-`b*` localization buys nothing because at `b*` the certificate is the same
archimedean cancellation `Σ_{x∈μ_n} e_p(b*x) = o(√(n log p))`.* This is the equivalence the cone keeps
re-deriving from every angle (Stepanov→trivial-degree, height→exponential, square-function→sup-over-`t`,
decoupling→PairEquidistributed). The paper stops at a partition with a hole; the deeper theorem is that
the hole is a mirror.

**Honest balance:** the criticism sharpens the *proof* (it needs a phase-equidistribution input it
didn't state, and its generality leaks), but the *conclusion* — that the surviving niche is per-`b*`,
order/sequence-dependent, archimedean-phase functionals — is correct and is exactly where the ten
directions concentrate.

## 2. The ten directions (ledger-verified, ranked by feasibility × originality × insight × non-reduction)

| # | Direction | score | ledger | verdict |
|---|---|---|---|---|
| **9** | **Ordered partial-sum walk / Doob maximal-excursion at `b*`** | **1120** | genuinely untried | the standout — see §3 |
| 7 | Tower-cut entanglement spectrum (Schmidt rank) of the period state | 960 | untried | `b*` near-max-entangled; area-law misses it |
| 3 | Multiplicative Gauss-sum dual / spectral-reciprocity swap | 630 | barely-tried | hits Fekete sign-reversal + p-blind discriminant |
| 4 | Berkovich reduction-graph / tropical-skeleton house upper bound | 504 | barely (2×) | house = exponential, reduces to cyclotomic wall |
| 5 | Concentration-compactness profile of the worst-`b*` sequence | 504 | untried | profile `c_1=η_{b*}/n`; dichotomy (compact=structured / vanishing=sub-G) — untested |
| 6 | Per-`b*` variational stationarity + cyclotomic-reality tension | 504 | untried | Łojasiewicz/coercivity — self-refutes/conditional |
| 8 | Alien-calculus / Stokes-automorphism on the wraparound resurgence | 360 | untried (Stokes) | non-perturbative phase — feas low |
| 2 | Nevanlinna inner–outer (Jensen/Mahler) factorization | 168 | barely | Mahler = avg-not-max |
| 10 | Kontsevich–Zagier exponential-period weight-graded effective bound | 160 | barely (1×) | period-algebra; feas very low |
| 1 | Phase-windowed `b`-summed moment `Σ_b |η_b|^{2k}1[arg∈arc]` | 160 | mostly-tried-adjacent | the criticism's blind spot — reduces (avg-over-arc) |

Four (3,7,2,1) are novel only by grep and reduce in substance; three (6,10,4) self-refute or are
conditional-ineffective. Three (9, 5, and the underlying per-`b*`-order principle) live in the one
surviving niche.

## 3. The standout: DIR 9 (ordered-walk / Doob), and its honest status

Order `μ_n = {g_0^0, g_0^1, …}` by the subgroup generator; the partial sums
`S_k = Σ_{j<k} e_p(b·g_0^j)` form a **walk** whose endpoint is `η_b = S_n`, and
`R(b) := sup_k |S_k| ≥ |η_b| = M`. This is the **first campaign object that is simultaneously**:
- **a tight majorant of `M`** (`R/M = 1.0026` at the argmax — verified), so bounding `R` bounds `M`;
- **provably orthogonal to the b-summation dichotomy**: `Σ_b signedArea(b) = 0` exactly (an order-dependent
  functional, *not* a `Σ_b` polynomial), so the dichotomy's no-go does **not** apply to it;
- **per-`b*` and order-dependent** — the surviving niche.

**Decisive test I ran** (`probe_ordered_walk_doob_majorant.py`): the *worst-case constant* of `R` equals
that of `M` — `C_R/C_M = 1.003/1.008/1.018` at `n=16/32/64` (ratio slowly *growing*). So **`R`'s value
reduces to the wall** (ordering buys no slack in the bound). **What remains genuinely open** is the
*proof route*: `R` is a maximal function, so a **Doob martingale maximal inequality** or a **van-der-Corput
second-derivative** estimate on the ordered phases `φ_k = b·g_0^k mod p` could in principle bound `R(b*)`
*without* passing through the char-sum — and that is the one route the dichotomy cannot exclude. The
maximal-inequality bound would have to be as strong as Paley itself (since `C_R = C_M`), so it is not a
shortcut, but it is a genuinely-new *formulation* whose provability is untested. **Next test:** the
van-der-Corput run-count of `{φ_{k+1}-φ_k}` at the worst `b*` (bounded monotone-runs ⟹ vdC applies).

## 4. Honest verdict

The 1389-file ledger has saturated every `Σ_b` / magnitude / energy / valuation / abelian-monodromy
face. The criticism's blind spot (phase functionals) is real but filled-and-reduced. Of the ten
directions, none is a likely crossing; the three that survive their own tests all live in the single
under-mined niche — **per-`b*`, order/sequence-dependent, dichotomy-orthogonal archimedean-phase
functionals** — with **DIR 9 (the ordered-walk maximal function)** the sharpest: a tight majorant of `M`
that is provably off the b-sum, whose value equals the wall but whose maximal-inequality proof-route is
the one genuinely-open per-`b*` question the campaign has surfaced. That is the honest frontier.
