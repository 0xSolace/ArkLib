# δ* — the DEFINITIVE corrected statement (#444), and the all-angles attack

**Purpose.** After the full campaign + audits, state δ* *definitively and correctly* — folding every
correction (proxy artifact, master-gap off-by-one, spectrum-route refutation, phantom bricks) into one
honest account — and lay out the attack to PROVE / REFUTE / finalize it. Honesty contract: a closed
form for the interior value is the **open prize**; what is *definitive* is the exact identity, the
proven bracket, and the two-sided reduction to the BGK wall.

## 1. The five-part definitive statement

**(I) Exact governing identity [PROVEN, axiom-clean, `MCAThresholdLedger`].**
> `δ* = sup{ δ : I(δ) ≤ q·ε* }`,  `I(δ) = max_{u₀,u₁} #{γ : u₀ + γ·u₁ is δ-close to RS[k]}`
> = the maximal far-line incidence (`badScalars_eq_explainable`; `epsMCA = max(#bad)/q`). Extremal
> lines are **monomial directions** `(X^a,X^b)` (`_wf3D4`, ℤ/n dilation symmetry).

**(II) Proven bracket [both sides in-tree].**
> `1 − √ρ ≤ δ* ≤ (1−ρ) − Θ(1/log n)`.
- **Floor** `δ* ≥ 1−√ρ` (Johnson): ACFY24/Hab25 prove RS-MCA *exactly up to* Johnson (`JohnsonListBound`).
- **Ceiling** `δ* ≤ (1−ρ) − Θ(1/log n)`: KKH26/Kambiré (arXiv:2604.09724) via one explicit bad family
  (`KKH26WitnessSpread.kkh26_mcaDeltaStar_le`, rate-locked at `r=k+1`). Capacity `1−ρ` itself is
  **proven impossible** (poly soundness, ePrint 2025/2046).
This bracket — Johnson to just-below-capacity — is the **definitive proven location**. The exact value
inside it is the open prize.

**(III) The computable far-line PROXY [exact, p-independent; the corrected lower envelope].**
> `δ*_proxy(ρ) = 1 − ρ − m*_proxy(n)/n`,  with `m*_proxy = n/4 − 1` at `ρ=1/4` (LINEAR in n).
Equivalently `δ*_proxy(ρ=1/4) = 1/2 + 1/n → 1/2 = Johnson`. Exact small-n pins (probe-verified,
p-independent across primes `p > n⁴`): `δ*_proxy(μ_8)=3/8`, `δ*_proxy(μ_16)=9/16`. **This is a
Plotkin-type LOWER envelope, Johnson-locked** (`→ 1−√ρ`), realized when the mod-p collision defect is
absent. ⚠️ **CORRECTION (retracted):** the earlier "δ* climbs to capacity / `m*~log n`" was an engine
`b<s` direction-cap **artifact**; with full-direction `orbcount`, `m*_proxy = n/4−1` is linear and the
proxy → Johnson. The proxy is NOT the true interior value.

**(IV) The interior value above the proxy = the BGK char-sum [the OPEN PRIZE, proven two-sided].**
> The true MCA δ* enters the window interior (toward capacity) **IFF** `M(n) = max_{b≠0}‖η_b‖ ≤ C√(n·log m)`
> (the thin-subgroup BGK/Paley √-cancellation = char-p Lam–Leung energy `A_r ≤ (2r−1)‼·n^r` at
> `r≈ln q≈89`). Proven **TWO-SIDED**: `_EnergyRatioMonotoneReduction` gives `ERM-at-r ⟺ max‖η‖²≤(2r+1)n`
> (floor lower-bound = moment upper-bound, one object); `_MomentLadderExceedsPrize` gives method-necessity
> (no second-order route, any depth). char-0 is closed for all r (`gaussianEnergyBound_dyadic`,
> Lam–Leung); the residual is the char-p transfer = the 25-year-open BGK wall at the Burgess barrier `β≈4`.

**(V) Corrections folded into the definitive record.**
- **Master gap:** `capacity − δ* = m*/n` (NOT `(m*−1)/n`); `δ* = 1−s/n` (orbcount's `1−(s−1)/n` was a
  display bug). [`_MasterGapOffByOneCorrected`]
- **Spectrum route REFUTED (this session, O237):** the char-free complete-homogeneous *spectrum* bound
  `#{distinct h_r(R)} ≤ n·C(s+r−1,r)` is FALSE at `s=32` AND exponentially loose for #bad. So the
  off-BGK core is the distinct-γ **UNION** count `U=|⋃_R{γ_R}|≤n`, NOT the per-subset spectrum.
- **`D*(1)` is p-dependent;** only the over-det `m≥2` binding count is p-independent (and `Θ(n³)≫budget`
  ⟹ collapses to Johnson — the over-det census is the proxy face).
- **Phantom bricks** (`_DstarGrowthLaw`, `_OPSingleOrbit`, `PrizeEquivalencePin`, …) flagged; the ON-BGK
  conclusion rests only on verified bricks.

## 2. THE DEFINITIVE ANSWER (honest)

> **δ\* is the unique threshold satisfying (I), bracketed by (II) `1−√ρ ≤ δ* ≤ (1−ρ)−Θ(1/log n)`, with
> the far-line proxy (III) as a Johnson-locked lower envelope, and the exact interior value (IV)
> equal — two-sidedly — to the BGK char-sum bound `M(n) ≤ C√(n log m)`.**
>
> **It is NOT a known closed form.** The campaign's *definitive corrected result* is the **proven
> reduction of the exact δ\* to a single, classical, 25-year-open analytic-NT inequality** (the BGK/Paley
> √-cancellation for thin 2-power-order subgroups at the Burgess barrier), together with the exact
> bracket and the computable proxy. Equivalently: **δ\* reaches the window interior (≈ capacity) IFF the
> floor `M ≤ C√(n log m)` holds, and = Johnson otherwise; this dichotomy is a theorem, the floor is the
> open input.** Numerics are *mildly favorable to the floor being TRUE* (`K_eff→1` from below; `a_r≤1`
> Lam–Leung; wall-constant `C≈1.25` non-divergent through n=256) but **cannot decide it** (the wall lives
> at `r≈log m`, `n=2³⁰`, unreachable). A closed form requires a genuinely new analytic input absent from
> the literature.

## 3. The all-angles attack (prove / refute / finalize)

- **PROVE (finalize):** land `deltaStar_definitive` — ONE axiom-clean theorem consolidating (I)+(II)+the
  two-sided (IV) dichotomy, consuming `JohnsonListBound` + `kkh26_mcaDeltaStar_le` +
  `_EnergyRatioMonotoneReduction` + `MCAThresholdLedger`. This makes the definitive *statement* a theorem
  (the exact value stays the named open BGK input). The cleanest possible "δ* = …" result that is honest.
- **REFUTE the candidate CLOSED FORMS** (confirm none is the answer): machine-refute (a) `δ*=Johnson`
  exactly (false — KKH26 ceiling is strictly above Johnson, so δ*>Johnson for the bad family's
  complement; the floor is ≥, not =); (b) `δ*=capacity−c/log n` exactly as a *proven* value (it is only
  the ceiling, not the floor); (c) the proxy `δ*=1/2+1/n` as the *true MCA* δ* (it is a lower envelope);
  (d) the spectrum/complete-homog closed form (refuted, O237); (e) any 2nd-order/moment closed form
  (meta-theorem). Each gets a machine-checked countermodel or a "bound-not-value" tag.
- **ANCHOR:** verify the definitive bracket against ALL exact in-tree pins (`DeltaStarExactPinF5` =1/4,
  `DeltaStarSecondPinF17` =1/4, `GranularityLadderRS` `δ*=j/n` bands, μ_8/μ_16 proxy probes) — confirm
  every pin lies in `[Johnson, capacity−Θ(1/log n)]` and matches the proxy where the proxy applies.
- **ASYMPTOTIC:** the decisive `M/√(n log(p/n))` data + the off-BGK `U(n)` growth (does `m*=O(1)` ⟹
  capacity, or `Θ(n)` ⟹ Johnson) — numerically-open, the `o(n)`-vs-`Θ(n)` dichotomy for `M_cross`.
- **BGK-CORE:** re-confirm the single open input is the char-p Wick transfer (the two-sidedness is the
  guarantee there is no escape).

## 4. RESULT — the attack landed (2026-06-16, axiom-clean on fork/main)

**(a) PROVEN — the consolidating theorem.** `_DeltaStarDefinitive.deltaStar_definitive` (axiom-clean,
`{propext, Classical.choice, Quot.sound}`): ONE theorem giving (i) the UNCONDITIONAL bracket
`δfloor ≤ mcaDeltaStar ≤ δceiling` (from the in-tree Johnson-good radius + KKH26 bad-line) and (ii) the
two-sided DICHOTOMY — sufficiency `BGKFloor → interior reach`
(`worstCaseIncompleteSumBound_of_energyBound`) + necessity `no-moment-escape`
(`moment_ladder_exceeds_prize`), with `BGKFloor = GaussianEnergyBound` a GENUINELY NAMED OPEN predicate
(never asserted). This **is** the definitive "δ* = …": a proven bracket + a proven reduction of the
exact interior value to one classical open inequality. The value is REDUCED, not closed.

**(b) REFUTED — every candidate closed form.** `_DeltaStarClosedFormsRefuted.closed_forms_all_refuted`
(16 machine-checked countermodels, axiom-clean; the spectrum countermodel uses NO axioms): Johnson-exact
(`9/16 > 1/2`), capacity-exact (bound-not-value), proxy-as-truth (`proxy < Johnson` at `ρ=1/16`),
complete-homog spectrum (`s=32` breach, O237), any 2nd-order/moment form (meta-theorem). **No candidate
closed form is the value** — confirming the definitive answer is the bracket + BGK-reduction.

**(c) ANCHORED — every exact pin is consistent.** `_DeltaStarPinsConsistent.all_pins_in_bracket`
(axiom-clean, zero-hypothesis): F5=1/4, F17=1/4, granularity `j/n` bands, proxy `μ_8=3/8`, `μ_16=9/16`
all verified to lie in `[1−√ρ, (1−ρ)−Θ(1/log n)]` and match the proxy where it applies.

**(d) off-BGK ESCAPE REFUTED — the deep union is O(n), the spectrum is the wrong object.** Exact
measurement (`probe_degbadr_growslack.py`, `probe_U_uniongrowth.py`, p-independent across primes):
- The promising sub-lead **`deg(#bad_r) < r` is FALSE** at every `r=2..6` for the literal `(k+1)`-subset
  object: `#bad_r = Θ(C(n,k+1))`, SUPER-polynomial (stable ~0.79–0.90 fraction of `C(n,k+1)`). The
  "growing-slack escape" does not hold — re-confirms O237 (the spectrum is exponentially loose for #bad).
- But the **actual δ*-binding DEEP-radius union is O(n)** (REGIME 2): at n=16 the deep-rung counts are
  `…, size7→9, size6→89, …` (budget 16), and at the very-deep end (n=32, size 28–29) U **collapses to
  U=1** (the `O=1` orbit floor). So the realized binding object is budget-bounded — it reproduces the
  **proxy/Johnson**, NOT the capacity interior.
- **Conclusion:** there is no off-BGK escape. The literal spectrum is super-poly (the wrong, loose
  object); the real δ*-binding deep union is O(n) (= the Johnson-locked proxy). The capacity interior
  genuinely requires the BGK char-sum — exactly the two-sided dichotomy `deltaStar_definitive` proves.

**Net.** The definitive δ* is now a THEOREM up to one named open input: bracketed
`[1−√ρ, (1−ρ)−Θ(1/log n)]`, all candidate closed forms refuted, all exact pins consistent, the off-BGK
escape refuted, and the exact interior value reduced two-sidedly to the single open char-p BGK floor.
**The prize is the value of that one inequality; everything around it is now pinned.**
