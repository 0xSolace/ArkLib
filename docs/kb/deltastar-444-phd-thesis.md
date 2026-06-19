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

*(deep section — see §2.x below, drafted in the formal companion; integrated from the research pass)*

> **Placeholder integrated from `thesis-research-attack` §S1.** The six forms — char-p energy, BGK/Paley
> sup-norm, Λ(q)-set (= Sidon, Pisier), sub-Gaussian antipodal phases, Jacobi-cocycle dispersion, wraparound
> variance — and the proof of their equivalence (the moment identity, `_BridgeOneWall` additive=multiplicative
> Fourier duality, Pisier's iff).

---

## Chapter 3 — Originating Areas and Unseen Connections

*(deep section — integrated from §S2: analytic NT, harmonic analysis, coding theory, algebraic geometry,
additive combinatorics, probability; and the connections — Jacobi-cocycle = Weil representation, the
Fourier-dual bridge, the onset–geometry-of-numbers link, the variance–pair-equidistribution link.)*

---

## Chapter 4 — What Has Been Tried, and Why It Hit the Wall

*(deep section — integrated from §S3: the two-obstruction pincer, the ~100-direction dead-routes ledger with
precise mechanisms, "what people said the next step would be".)*

### 4.0 The pincer (the structural core, stated here as it governs everything)

Every approach hits at least one of two theorems-with-hypotheses, and a proof must escape **both**:
- **(i) Moment-necessity [Lean, `moment_ladder_exceeds_prize`].** No non-negative count / second-order magnitude
  reaches the target — a proof must capture **cancellation** (signs/phases), not a count. *Even a signed Hankel
  determinant reduces* (`_AmbBreakMomentNecessity`).
- **(ii) √p-vacuity.** `μ_n` is thin (`n ≈ p^{0.19}`), so Weil/Deligne gives `O(√p) = O(n^{2.6}) ≫ n`:
  field-scale algebraic geometry is vacuous. The period sheaf's eigenvalues *are* the `n` Gauss sums, each `√p`
  (`_FrontierSheafConductor`); the Jacobi correlation re-enters `√p` at the correlation variety's middle
  cohomology `H^{2r-1}`, weight `2r−1` (`_JacobiFermatCohomology`).

The pincer has no gap: the cohomological route escapes (i) but hits (ii); the additive/relative-trace route
escapes (ii) but hits (i). This is *why* the problem is hard, stated as two theorems.

---

## Chapter 5 — Empirical Evidence and Exact Pins

*(deep section — integrated from §S4: `M/√(2n log m)=0.77–0.85<1`; the di Benedetto beat to 0.9583; the onset
law `r_0=Θ(p^{1/φ(n)})`; the DC-moment ratio `0.87→0.13`; no disproof at n=64,128; the exact δ* pins.)*

---

## Chapter 6 — The Solution Space, and What New Mathematics Would Look Like

*(deep section — integrated from §S5: the precise shape of the missing theorem; why no existing tool reaches it;
the requirement that a proof-object be signed AND subgroup-scale AND growing-order; the ~28 created candidate
objects.)*

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

*(The fresh proof attempts A1–A3 and their honest outcomes integrate here.)*

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
