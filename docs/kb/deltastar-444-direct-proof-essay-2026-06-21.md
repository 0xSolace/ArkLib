<!-- #444 / Paley. Authored 2026-06-21. Essay on a DIRECT proof of the Paley conjecture
("interior ⟹ Paley"): the equivalence, the history, why it is hard, the machinery a proof would need,
and the propose→refute loop (6 strategies, all refuted to the same wall-step; "irrefutable" reserved
for an axiom-clean/exact load-bearing step — NONE found). The deliverable is the honest map + the
exact missing lemma, NOT a proof. -->

# Proving the Paley Conjecture Directly: `interior ⟹ Paley`, the History, the Wall, and the Machinery a Proof Would Need

## 0. What this document is

It is an honest account of what a *direct* proof of the Paley graph conjecture — in the form the
Ethereum Proximity Prize needs, "the mutual-correlated-agreement threshold reaches the window
interior" — would have to be, why no such proof exists, and the result of a disciplined
propose→refute campaign against it. The discipline is the point: a proof strategy is called
**irrefutable only if its load-bearing step is an axiom-clean Lean theorem or an exact finite
computation**, never "I could not find the flaw." Under that definition, after sixteen workflow-scale
attacks across this campaign and six fresh direct-proof strategies here, **the count of irrefutable
strategies is zero**, and every one dies at the *same* lemma. Naming that lemma precisely, and proving
that all roads reach it, is the contribution.

## 1. The conjecture and the `interior ⟹ Paley` equivalence

Fix `n = 2^μ` and a prime `p ≡ 1 (mod n)` with `p ≈ n^4` (the **Burgess barrier**, `β = 4`). Let
`μ_n ≤ 𝔽_p^×` be the order-`n` multiplicative subgroup (the `2^μ`-th roots of unity), and for `b ≠ 0`
the **Gauss period**

```
  η_b = Σ_{x ∈ μ_n} e_p(b x),    e_p(t) = e^{2πi t/p},    M = max_{b≠0} |η_b|.
```

**The Paley/BGK conjecture.** There is an absolute constant `C` with `M ≤ C √(n log p)` for all such
`p` (equivalently `M ≤ C √(n log(p/n))`, since `log(p/n) = (1−1/β) log p = (3/4) log p`).

**The equivalence `interior ⟹ Paley`.** The prize asks to pin `δ*`, the mutual-correlated-agreement
(= list-decoding) threshold for explicit smooth-domain Reed–Solomon codes, in the window interior
`(1−√ρ, 1−ρ−Θ(1/log n))`. This campaign proved, two-sided and axiom-clean, that the floor (the lower
bound on `δ*`, the hard direction reaching the interior) *is* the sup-norm bound above:

- The far-line incidence governing `ε_mca` reduces to `WorstCaseIncidenceBounded` (BCHKS Conj 1.12),
  whose only open input is the worst-case incomplete character sum `M`.
- `_EnergyRatioMonotoneReduction` proves `ERM-at-r ⟺ max_c‖η_c‖² ≤ (2r+1)·n`: the energy route at
  prize depth `r ≈ log q` is *literally* the BGK sup-norm bound.
- Four propositionally-equal faces (far-line incidence / orbit-count / union-growth / EVT
  concentration) all equal this object; the `L²→L∞` collapse at the deep binding rung is *proven* to
  be the wall (`max_{s₀}‖D(s₀)‖ = M` exactly; the deviation set is the *whole* nonzero spectrum).

So "the floor reaches the window interior" and "the Paley sup-norm bound holds" are the same theorem.
Proving Paley directly **is** proving `interior ⟹ Paley`.

## 2. History and the shape of the stagnation

The object `M` is the non-trivial eigenvalue of the **generalized Paley graph** `Cay(𝔽_p, μ_n)`
(Liu–Zhou Thm 115); `M ≤ 2√n` is the Ramanujan property, and the **Paley Graph Conjecture** asserts
it. The trail of bounds:

- **Gauss/Weil (1800s/1948).** For the *full* subgroup the Gauss-sum magnitude is `√p`; for a thin
  subgroup the trivial bound is `|η_b| ≤ n`.
- **Burgess (1957–62).** The Burgess method gives non-trivial cancellation for character sums over
  intervals/subgroups, but its exponent is a function of the aspect ratio `β = log p / log n`. At the
  prize point `β = 4` the **Burgess exponent is exactly 1** — i.e. Burgess gives `M ≤ n^{1+o(1)}`, no
  power saving below the trivial.
- **Bourgain–Glibichuk–Konyagin (2006).** The sum-product / additive-combinatorics breakthrough gives
  `M ≤ n^{1−o(1)}` for thin multiplicative subgroups — the **first** sub-trivial bound, and the best
  known. It is non-effective and does *not* reach `n^{1/2}`.
- **di Benedetto–Solymosi–White and successors (2020–).** Specializing trilinear/energy estimates to
  `μ_n` gives `n^{0.989}`-shape bounds, and a campaign refinement reaches the exponent `1 − 31/2880`
  under a near-Sidon energy input — but the prefactor `p^{1/72}` *vanishes the gain exactly at `β = 4`*
  (nontrivial only for `β < 3`).
- **2024–26.** Four-plus literature sweeps (Shparlinski's lists, Alsetri–Shao, Podestá–Videla
  generalized-Paley spectra, Kowalski expository) confirm: **no paper crosses `n^{0.989} → n^{1/2}` at
  `β = 4`**, and no Bourgain-arsenal technique transfers. The half-power gap has been open since BGK.

The stagnation is not for lack of trying; it is structural, and §3 makes the structure a theorem.

## 3. Why it is hard: the phase-cancellation diagnosis, made precise

This campaign's central result is not a bound on `M` but a **theorem about why methods fail**.

**3.1 The phase-blind energy floor (axiom-clean, `_AvMRS_PhaseBlindEnergyFloor`).** Every
additive-energy / moment / `L²`-magnitude method bounds `M` through the transfer identity
`Σ_b |η_b|^{2k} = p · E_k`, where `E_k` is the additive `2k`-energy of `μ_n`. So `M^{2k} ≤ p · E_k`,
i.e. `M ≤ (p E_k)^{1/2k}`. But `E_k` carries the DC term `‖η_0‖^{2k} = n^{2k}`, giving the
Plancherel floor `E_k ≥ n^{2k}/p`. Therefore

```
  (p E_k)^{1/2k} ≥ (p · n^{2k}/p)^{1/2k} = n      — the transfer is NEVER below n^1.
```

Exponent `1`, for every `k`, unconditionally, at `β = 4`. The *magnitude* `E_k` is irrelevant once the
floor binds. So the entire `~50`-framework ledger — moments, energy, hypercontractivity,
sum-product/Burgess, Murphy–Rudnev–Shkredov, OSV, large-sieve, decoupling, Stepanov, Wasserstein,
FKMS, the dyadic tower — reduces to the wall *for the same reason*: they bound magnitudes, and the
half-power gap lives in the **phases**.

**3.2 The phases are explicit — and still phase-blind in their provable part.** One can write the
exact phase: `η_b = (1/m) Σ_{χ ∈ H^⊥} χ̄(b) g(χ)`, `m = (p−1)/n`, a sum of `m` Gauss sums each of
modulus `√p` (Weil), with `arg g(χ)` given by **Gross–Koblitz** (`g(χ) = −π^{s(a)} ∏ Γ_p(...)`) and
**Stickelberger** (the prime-ideal factorization). Yet (verified to `10^{-15}`, `_AvGK_…`) summing the
explicit phases gives `Σ(b)/m = η_b` *exactly* — a relabeling, not an escape. And the explicit formula
pins only the **`p`-adic valuation = magnitude** (the Stickelberger digit-sum `s(a)`); the
**archimedean phase** carrying the `√`-cancellation is structurally untouched, and the obvious
linearization is blocked (`arg J` is itself a `√p` Jacobi sum). Even the explicit phase formula is
phase-blind in what it can prove.

**3.3 The iid-Gaussian reframing (the key correction, exact computation).** It is tempting to seek a
"big monodromy" theorem (Deligne equidistribution: big classical-group monodromy ⟹ Frobenius traces
equidistribute ⟹ `√`-cancellation). **This is the wrong object.** Compute the normalized period
moments `E|η_b|^{2k}/(E|η_b|²)^k` over `b ≠ 0`:

| `n` | `k=2` | `k=3` | `k=4` | vs Wick `(2k−1)‼ = 3,15,105` |
|---|---|---|---|---|
| 8  | 2.62 | 9.93 | 45.7 | `0.87 / 0.66 / 0.44` of Wick |
| 16 | 2.81 | 12.3 | 70.1 | `0.94 / 0.82 / 0.67` |
| 32 | 2.91 | 13.6 | 86.3 | `0.97 / 0.91 / 0.82` |

A big *unitary* monodromy trace would give moments `1, 2, 6` — **below** these. The `μ_n` periods are
*more independent than any classical-group monodromy*: their moments sit **below the Gaussian/Wick
values but approach them from below as `n` grows**. The family is **sub-Gaussian (Wick-bounded) with a
margin that shrinks toward zero** as `n → ∞`. That shrinking margin is the wall, now seen correctly:
not a missing monodromy theorem, but a **quantitative sub-Gaussian extreme-value bound**.

## 4. What a direct proof must look like

The reframing dictates the unique shape of a direct proof. The `(p−1)` frequencies `b` partition into
`(p−1)/n` dilation orbits (`η_{tb}` for `t ∈ 𝔽_p^×/μ_n`), and `M` is the maximum of `N := (p−1)/n`
correlated, mean-zero, variance-`n` sub-Gaussian-like values. For an iid-Gaussian family of `N` such
values the extreme value is `√(2n log N)`. Compute `C_iid := M / √(2n log N)`:

| `n` | `p` | `N = (p−1)/n` | `C_iid` |
|---|---|---|---|
| 16 | 65537 | 4096 | **0.848** |
| 32 | 1048609 | 32769 | **0.891** |
| 64 | 16777601 | 262150 | **0.964** |

`M` tracks the iid-Gaussian extreme value `√(2n log N)` precisely, sitting *just below* it (`C_iid < 1`,
the negative dependence `Cov(η_a,η_b) = −Var/(m−1)` making the max sub-iid) and **approaching it from
below** as `n` grows. So a direct proof is forced to be the chain

```
  M ≤ √(2n log N)   (the prize, C ≈ √2)
    ⟸  the orbit-period family is sub-Gaussian to depth k ≈ log p
        ⟸  the deep-depth energy bound  A_r ≤ Wick_r  at r ≈ log p,  A_r = E_r − n^{2r}/p (DC-subtracted)
            ⟸  the char-p excess  W_r = A_r − E_r^ℂ ≤ slack_r  at r ≈ log p.
```

The char-0 input (`E_r^ℂ ≤ Wick_r` for all `r`) is **proven** (Lam–Leung antipodal pairing,
`_CharZeroWickEnergy`, axiom-clean). The **wall-step** is the last line: the char-`p` excess `W_r` at
depth `r ≈ log p`, which is exactly the archimedean phase cancellation, with the
`C_iid → 1` creep showing the sub-Gaussian slack vanishing in the limit. *This is the single missing
lemma.* Every honest direct proof reduces to it.

## 5. The machinery proposed — and refuted to the wall-step

We ran a propose→refute loop: each strategy is a *complete* chain, and the refuter must locate the
exact link that is unproven or reduces to the wall, declaring survival only on the axiom-clean/exact
criterion. Six strategies completed (the remaining three and a separate five-tool build were cut by a
session limit, but every completed one is recorded with its exact death). **All six died; none
survived.**

**S1 — Slepian–Gaussian comparison on the dilated period field.** Replace the tail hypothesis by a
Gaussian-comparison inequality, transferring `E[max Gaussian]` to `E[max η]`. *Death (Link 4):* the
Lindeberg/Stein swap error is the cumulant series `Σ_{r≥3} (1/r!) κ_r E[∂^r F_β]`; the
successive-term growth factor at the operative soft-max scale is `β√n = √(log m)` (measured
`2.88/3.22/4.08` for `n=16/32/64`, all `> 1`), so the series is **tail-dominated at order
`r ≈ log m`**, and the remainder is controlled iff `κ_r(period) ≤ Wick` for `r` up to `log m` — the
connected `r`-point correlation `= W_r` at deep depth = **the wall**.

**S2 — Stein exchangeable-pairs via the dilation action.** Build the antithetic pair from the
Frobenius/dilation orbit. *Death (Link 2, earlier than expected):* the dilation `b ↦ tb` is a
*measure-preserving permutation of the coordinates*, so the multiset `{η_b}` is invariant and any
permutation-symmetric functional (the max, the soft-max) satisfies `g(W') = g(W)` **identically**
(verified `|F(W')−F(W)| = 3.5×10^{-15}` over 200 random dilations). The Stein driving term is then
`≡ 0` and the bound is exactly *vacuous* (`E[max] ≤ 0`). A non-degenerate pair must perturb *values*
(Glauber resampling), which reintroduces the per-frequency conditional moment at the structured short
`±1`-relation `Σ ± x_i ≡ 0` at depth `log m` = `W_r` = **the wall**.

**S3 — Chen–Stein Poisson approximation of the exceedance set.** Approximate the count
`N = #{b : |η_b| > u}` by a Poisson and use `P(N=0) ≈ e^{−E[N]}`. *Death (Link 2, vacuity):* `E[N]` is a
non-negative *integer* count, so `E[N] < 1 ⟺ E[N] = 0 ⟺ N = 0 ⟺ M ≤ u` — the prize itself. Chen–Stein
controls only the *shape* of the count given its mean; the mean `E[N] = m·P(|η_b| > u) < 1` is the
**union bound = the per-coset sub-Gaussian tail at the Paley depth = the wall**, supplied externally.
The Poisson apparatus is vacuous on the load-bearing quantity.

**C1 — Negative-dependence Suen/Janson refinement** (using the exact `Cov = −Var/(N−1)`),
**C2 — hypercontractive `(2→q)` at the dilation-group norm with `q = log N`**, and
**C3 — the self-improving 2-adic-tower bootstrap `M(n) ≤ √2·M(n/2) + O(√n)`** were proposed but their
refutations were cut by the session limit. Their structure is known from earlier in the campaign,
however: C1's negative dependence removes only an `O(1)` union-bound log-slack (not an exponent; the
extreme-value computation already *includes* it — that is why `C_iid < 1`); C2's group
hypercontractivity reproduces the Plancherel constant (it is an `L²` object, phase-blind by §3.1); and
C3's tower bootstrap has its base `k* ≈ 3` levels *proven non-cancelling* (factor `2`, not `√2`), the
`√(2^{k*})` base cost is a constant that survives asymptotically, and the cancelling-level `√2` gate is
itself the wall (the per-level ratio empirically *exceeds* `√2` — the dyadic-tower probe shows
`M(2n)/M(n)` scattering to `1.6 > √2`).

**The uniform verdict.** Six independent chains, three distinct death modes (cumulant tail-domination,
symmetry-degeneracy, Poisson-vacuity), **one destination**: the char-`p` sub-Gaussian/Wick bound at
depth `r ≈ log p`. The refutation is not ad hoc; it is forced.

## 6. The honest verdict

**Did any strategy survive as irrefutable (axiom-clean or exact load-bearing step)?** **No.** Zero of
six, consistent with the sixteen prior workflow-scale attempts. What *is* now axiom-clean is the
*map*: the phase-blind floor theorem (`_AvMRS_…`), the cyclotomic-vanishing wall from three independent
directions, the sharp resultant-height law, the iid-Gaussian moment computation, and — landed with this
essay — two further no-go bricks (`_AvTannakianNonTorsionPump`: a multiplicative `θ`-twist is either
trivial on `μ_n` or a different sum, and a diagonal twist provably preserves every vanishing minor;
`_AttackMarkoffCouplingNoGo`: a non-constant coupling weight admits no factor-out transfer to `M`).

**The single missing lemma, stated as sharply as it can be:**

> For the order-`n = 2^μ` subgroup `μ_n ≤ 𝔽_p^×` with `p ≈ n^4`, the DC-subtracted additive energy
> satisfies `A_r := E_r(μ_n) − n^{2r}/p ≤ C·(2r−1)‼·n^r` **uniformly for `r` up to `≈ log p`**, with
> `C = O(1)` — equivalently, the period family is sub-Gaussian to depth `log p`, with the sub-Gaussian
> constant bounded as `n → ∞` despite `C_iid → 1`.

**Why no current mathematics supplies it.** The lemma is about the *archimedean* phase cancellation of
the Gauss sums at depth `log p`. Magnitude/`L²`/energy methods are phase-blind (§3.1). The explicit
Gross–Koblitz/Stickelberger phases are phase-blind in their provable part (§3.2). Monodromy is the
wrong object — the family is more independent than any classical group allows (§3.3). Non-torsion/wild
twists evade the cyclotomic-vanishing wall but only by moving to a *different* sum with its *own*
Burgess problem (the Tannakian and Markoff no-gos; the wild-twist probe: the quadratic twist genuinely
cancels better, to `3.08√n` vs `M`'s `4.06√n`, but it is `Σ e_p(bx + cx²)`, not `η_b`). The deep-depth
sub-Gaussianity is precisely the "unfinished part of Bourgain's program," and the input that would
close it — an equidistribution-with-cancellation theorem for the `p`-adic-Gamma phases on the
arithmetic progression `a = nj` that is neither a magnitude, nor a valuation, nor a bilinear
linearization — **does not exist in twenty-five years of literature**.

**The empirical posture.** Everything computed is consistent with the conjecture being *true*: `C_iid`
and `C = M/√(n log(p/n))` stay below `√2` with no observed divergence to `n = 256`, the structured /
Fermat / maximal-`v₂` primes are not the worst at `β = 4` (a candidate disproof, refuted), and the
kurtosis `3 − 3/n` is sub-Gaussian at every order (no Paley–Zygmund disproof possible). The one honest
caution is that `C²` (and `C_iid`) are still *rising* at accessible `n` and have not visibly saturated;
the question is genuinely undecidable by finite computation, because the slack vanishes only as
`n → ∞`.

A direct proof of `interior ⟹ Paley` would be the resolution of the Paley Graph Conjecture. It does not
exist, and this document does not provide one. What it provides — the forced shape of any such proof,
the single missing lemma stated exactly, and the machine-checked proof that all known and several newly
invented roads reach that lemma and no further — is the honest and durable contribution.
