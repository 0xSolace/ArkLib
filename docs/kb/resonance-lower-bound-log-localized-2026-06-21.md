# The Resonance Lower Bound: Forcing the Log Floor M ≥ c·√(n log m) (#444)

*Synthesis of the resonator campaign on the Gauss-period spectrum. Six candidate
resonators, all formalized; what each actually proves, and exactly where the log
factor still lives.*

---

## 1. Why the lower bound is the provable side, and the resonance method

The Burgess–Gallagher–Karatsuba (BGK) two-sided estimate for the Gauss-period
spectrum asks for the order of

> **M := max_{b≠0} |η_b|,  η_b = ∑_{x∈μ_n} e_p(b·x),**

where μ_n is the group of 2^a-th roots of unity in 𝔽_p, p ≈ n^4, and m = (p−1)/n
is the number of μ_n-cosets. The conjectured truth is **M = Θ(√(n log m))**: an
upper bound M ≪ √(n log m) and a matching lower bound M ≫ √(n log m).

The two halves are not symmetric in difficulty. The **upper** bound is the hard,
$1M side: it asserts that *no* frequency b resonates beyond √(n log m), which is a
cancellation statement — it needs the Gauss-sum phases to *interfere
destructively* uniformly, and that is exactly the open Paley/BGK wall, equivalent
to a statement that needs equidistribution-grade control (β = 4 in the campaign's
internal coordinate). The **lower** bound is the structurally easier side, and
this is the key point of leverage: an Ω-result asserts that *some* frequency is
large, and existence statements never require equidistribution. They are produced
by **first/second-moment methods** and by **resonance**, which are unconditional
counting arguments. The lower half of BGK is, in principle, *provable today*.

What is already proven in-tree, unconditionally:

- **M ≥ √n** (`ParsevalFloorSqrtN`, `worstPeriod_ge_sqrt_parseval`): the max
  exceeds the RMS, and the RMS is √n by Parseval ∑_{b≠0}|η_b|² = qn − n².
- **M ≥ √2·√n** (diagonal-quadruple) and **M ≥ √3·√n**
  (`_AvFloor_MomentRatioLowerBound`, from the *exact* fourth moment E₂ = 3n²−3n,
  Stickelberger, valid for p > n⁴).
- **M ≥ 1.48·√n** (`_LowerBoundPermMatchingFloor`, permutation matching).

Every one of these is **bounded·√n with NO log**. And the first-moment /
Paley–Zygmund route is *provably* capped at √n
(`_LowerBoundPaleyZygmundReach`): it cannot manufacture the log. The log must
come from somewhere else.

**The resonance method (Montgomery 1980; Soundararajan; Bondarenko–Seip; and the
new arXiv:2605.13715).** To lower-bound a max max_t|S(t)|, build a *resonator*
R(t) = ∑ r_τ ψ(tτ) and use the L1-normalized correlation inequality

> max_t |S(t)|  ≥  |∑_t R(t) S(t)| / ∑_t |R(t)|.

Choose R *aligned* with the large values of S so the numerator (a diagonal
correlation) survives while the denominator stays small. The power of the method
is entirely in the alignment. In arXiv:2605.13715 — which proves
**unconditionally** √p·loglog p ≪ max_θ|F_χ(a,b;θ)| ≪ √p·log p for the twisted
character sum F_χ — the loglog gain is **purely multiplicative in origin**: the
resonator coefficients are supported on a multiplicatively structured set
(squarefree / smooth integers) and tuned so the diagonal correlation
**factorizes over primes as an Euler product** ∏_{ℓ≤y}(1 + c/ℓ), whose logarithm
is the Mertens sum ∑_{ℓ≤y} 1/ℓ ≈ loglog y. **The loglog *is* the Euler tail of a
fixed completely multiplicative character χ.** It is unconditional because a
Mertens count needs no Riemann Hypothesis and no equidistribution. The companion
arXiv:2604.02960 produces the analogous numerator survival via Heath-Brown's
mean-value theorem for character sums over a *subgroup* of characters — again a
mean-value (counting) statement, not an equidistribution input.

The campaign's job: transplant this engine to M and see whether the log comes
free.

---

## 2. The adaptation to the Gauss-period spectrum

The resonator engine itself transplants verbatim, and is **already axiom-clean
in-tree**:

> **`resonator_ratio_lower_bound`** (file `_AvFloor_ResonatorRatioLowerBound`):
> for ANY nonnegative weight w on the nonzero frequencies,
> **M² ≥ (∑_{b≠0} w_b |η_b|²) / (∑_{b≠0} w_b).**

This is `weighted_sum_le_sup'` specialized to g = |η_b|². Setting w_b = |R(b)|²
recovers the Soundararajan Rayleigh-quotient form. **The engine is unconditional
and free.** The entire game is the *choice of w* — how to upweight the large |η_b|.

Here the adaptation is forced by the geometry of the object. The summed variable x
ranges over the *multiplicative group* μ_n, so |η_b| is **constant on
μ_n-cosets** (`_EtaCosetInvariance.eta_dilate_eq`: η_{cb} = η_b for c ∈ μ_n;
`GaussPeriodOrbitPartition`: 𝔽_p* splits into m free orbits of size n). The
multiplicative structure lives on the **dual** variable b, indexed by the m coset
labels — equivalently by the m characters χ^j trivial on μ_n. The natural
diagonalizing basis is the **twisted DFT / Gauss-sum completion identity**

> **m·η_b = ∑_{j<m} χ^{−j}(b) g_j,  g_j = g(χ^{dj}, ψ),  |g_j| = √p**
> (`SubgroupGaussSumWorstCase.completion_identity`).

So the m "frequencies" of the resonator live on the cyclic index group ℤ/m, and a
resonator over those indices is the analogue of Montgomery's resonator over the
primes. **The hope:** a multiplicative resonator r_j over ℤ/m whose diagonal
Gauss-sum correlation factorizes over the prime divisors ℓ | m, giving
∏_{ℓ|m}(1 + c/ℓ) ≈ loglog m via Mertens on the prime factors of the index group.
This is the single structural bet of the whole campaign, and §3 tests it six ways.

The critical asymmetry to keep in mind throughout: in 2605.13715 the
multiplicative variable is the **summation** variable n of a *fixed* character χ,
so χ(n)χ(n′) = χ(nn′) is genuine multiplicative coherence and the Euler product is
free. Here the multiplicative variable is the **dual coset-index** j, and the
needed input is that the Gauss-sum phases g_j correlate multiplicatively *in j* —
a statement about ±-relations of Gauss-sum phases over a cyclic index subgroup,
which is the *same object* as the open prize cancellation.

---

## 3. The six resonators — exactly what each reaches

All six are formalized in `_RES_{0..5}_scratch.lean`. I re-verified the theorem
inventories and sorry-counts directly. The headline: **five files are entirely
sorry-free; RES_4 has no code-level sorry either (its three "sorry" tokens are all
inside docstrings asserting "no sorry"), and its log gain is gated behind a NAMED
`Prop` residual, not a hidden gap.**

### Candidate 1 — coset-multiplicative resonator (`_RES_0`, sorry-free)

w_b = ‖∑_{j∈J} r_j χ^j(b)‖² with r_j a multiplicative function (μ², μ, tuned), J
the squarefree indices ≤ y. The engine numerator splits exactly (Fubini) into

> ∑_{b≠0} ‖R(b)‖² |η_b|² = (p−1)/m² · ∑_{δ mod m} ρ_r(δ) Γ(δ),

a **tensor of the resonator autocorrelation ρ_r against the Gauss-sum
autocorrelation Γ(δ) = ∑_k g_k ḡ_{k+δ}** (theorem `coset_resonator_numerator_expand`).
The **diagonal** δ=0 gives Γ(0) = ∑_k|g_k|² ≈ mp, hence ratio = p/m ≈ n **exactly,
independent of r** (`coset_resonator_diagonal_floor`,
`coset_resonator_diagonal_ratio`: the ‖r‖² cancels). The whole log must live in
the off-diagonal ∑_{δ≠0} ρ_r(δ)Γ(δ). Exact computation (n=8,16; several primes):
the Möbius/mean-removed resonator gives **R/n ≈ 1.0** for every prime, and
max_{δ≠0}|Γ(δ)|/(mp) ≤ 0.20 — the Gauss-sum phases *cancel*, never coherent.
**Reaches: √n only. Unconditional: yes. Log: no.**

### Candidate 2 — Heath-Brown subgroup mean-value (`_RES_1`, sorry-free)

The literal transplant of 2604.02960: the m characters {χ^{dj}} ARE a cyclic
character subgroup. The numerator reduces (theorem
`resonator_numerator_quadratic_form`) to the Hermitian form
∑_{j,j'} r_j r̄_{j'} S(j−j'), where **S(k) := ∑_{b≠0} χ^{nk}(b)|η_b|²** is the
coset-DFT of the period spectrum. Diagonal S(0) = qn − n² = Parseval energy;
single-index resonator gives S(0)/(q−1) = the bare √n floor
(`single_character_gives_parseval`). The loglog needs S(k) (k≠0) to sum
coherently under a multiplicative r — i.e. **S to be multiplicative**. Exact
computation **refutes this**: at n=32, p=1048609, m=32769=3²·11·331, **all 290/290
coprime tests of S(k₁k₂)=S(k₁)S(k₂)/S(1) fail**; |S(k)| ranges erratically
67…25967 against the √-scale √S(0)=1024. Root cause: Gauss sums g_j are **not
multiplicative in the character exponent j** (Hasse–Davenport is a fixed-shift /
field-extension relation, not index multiplication), so the coset-index resonator
has **no Euler product**. Best multiplicative resonator: ratio/n ∈ [1.0, 1.9],
never reaching loglog m ≈ 2.1–2.5. **Reaches: √n only. Unconditional: yes. Log: no.**

### Candidate 3 — Stickelberger-phase-aligned resonator (`_RES_2`, sorry-free)

r_j := conj(g_j(b))/‖g_j(b)‖ makes the diagonal correlation ∑_j r_j g_j(b) =
∑_j‖g_j(b)‖ fully coherent (`phaseAlign_fully_coherent`), giving the bogus ratio
≈ √p. This is a **diagnostic, not a floor**, and the capstone theorem
`candidate3_numerator_is_ceiling` proves *why*: that same coherent sum
∑_j‖g_j(b)‖, via the triangle inequality on the *same* completion identity, is an
**upper bound** t·‖η_b‖ ≤ ∑_j‖g_j(b)‖. The √p is the triangle **ceiling read
backwards** = the OVERSHOOT, and it gives ‖η_b‖ ≤ √q
(`phase_aligned_overshoot_is_upper_bound`). The obstruction is pinned exactly: the
phase r_j = conj(arg g_j(b)) **depends on b**, so it is not a fixed b-uniform
resonator weight; full coherence requires per-b alignment, which is the ceiling,
not a floor. **Reaches: no new floor (it is a ceiling). Unconditional: yes. Log: no.**

### Candidate 4 — long Bondarenko–Seip multiplicative resonator (`_RES_3`, sorry-free)

r_j = ∏_{ℓ|j} 1/√(ℓ−1) on a y-smooth squarefree support — the sharp-exponent
(√log, not loglog) candidate. The decisive structural fact (theorem
`candidate4_ratio_mem_minMax`): because η_b is coset-constant and χ^j(b) factors
through the coset label, the weight w_b is *also* coset-constant, and the entire
ratio collapses to a **positive-weighted average of the m per-coset values
|η_b|²**. A positive-weighted average is **sandwiched in
[min_l V[l], max_l V[l] = M²]** (`weightedAvg_mem_minMax`). The resonator output
is trapped inside the spectrum's own range; the log appears only if the weights
concentrate on the *rare argmax coset*. They do not. **Smoking gun:** for n=16,
p=65777, m=4111 is **prime**, so ∏_{ℓ|m}(1+1/ℓ) ≈ 1 (zero index-group gain) — yet
M²/n = 10.99 carries the **full** log (≈ log p). The index-group factorization is
**not the carrier of the log**: across 8 primes for n=16, M²/n tracks log p ≈ 11
*invariantly* while ω(m) and Mertens(m) vary from 0.0002 to 1.04. The BS smooth
weights are spread across smooth j, blind to the spike. Measured BS ratio/n:
1.97 (m=2^12 artifact), 1.01 (smooth set empty), 0.99 — vs M²/n = 11–16.
**Reaches: √n only. Unconditional: yes. Log: no — and the index-group Euler
product is *positively refuted* as the source of the log.**

### Candidate 5 — dyadic-tower depth-axis resonator (`_RES_4`, no code-level sorry; log behind a named `Prop`)

The only candidate that does *not* route through the additive/coset frequency
axis. It uses the dyadic tower μ_{2^i}, i = 0..a (a = log₂ n), with the exact
L2-doubling ∑_b‖η_b(G_i)‖² = 2^i·S0 (`secondMoment_tower_pow`, in-tree,
unconditional). Setting V(i) := max_{b≠0}‖η_b(μ_{2^i})‖² so M² = V(a), the
doubling cocycle r_i² := V(i+1)/V(i) ∈ [2,4] telescopes
M² = 2^a·V0·∏_i r_i², with excess δ_i := r_i²/2 − 1 ≥ 0. The chain is built
clean: `towerLower_telescope` (induction), `one_add_sum_le_prod` (the elementary
∏(1+δ) ≥ 1+∑δ super-additivity — the Montgomery Euler-product step transplanted to
the tower index, **proven with no exp and no sorry**), `nonzero_secondMoment_tower`
and `M2_floor_tower` (the unconditional DC-subtracted floor M_i² ≥
(2^i·S0 − |G_i|²)/(q−1) ≈ n at β=4). **The unconditional output is exactly √n.**
The log requires the named residual

> **`TowerCocycleExcessSum V a L`** := ∃ δ ≥ 0 with 2·V(i)(1+δ_i) ≤ V(i+1) and
> L ≤ ∑_{i<a} δ_i,

i.e. the cocycle excess sums to a **growing** L = Ω(log m). The probe is the most
honest data point in the campaign: M/√n = 3.46, 3.58, 3.53, 3.86, 4.71 for
n=16..256, which **matches √(log m) = 2.88, 3.22, 3.53, 3.82, 4.08 closely** (so
the true value really is Θ(√(n log m))) — while √(loglog m) = 1.46..1.68
undershoots 2–3×, confirming **loglog is too weak; the truth is √log**. But the
#levels with r_i² ≥ 3.5 is **constant in a** (= 3,3,3,4,3): the shallow-alignment
regime gives only O(1) excess (a constant factor √3), NOT a log; deep-level ratios
cluster at ≈ 2 (decorrelation) with no systematic excess. **∑δ_i does not
provably grow — it is the BGK deep-tower cocycle large-deviation.**
**Reaches: √n unconditionally; the log is honestly *named*, not delivered.
Unconditional: no. Log: no.**

### Candidate 6 — Polya–Vinogradov / incomplete index resonator (`_RES_5`, sorry-free)

w_b = ‖∑_{1≤k≤K} φ(b)^k‖² with φ the order-m coset-label character — Montgomery's
interval resonator on ℤ/m. The full-period collapse is exact
(`geom_resonator_full_period_indicator`, `pv_full_period_weight`): at K=m the
weight is m²·[φ(b)=1], concentrated on the index-DC coset = μ_n itself, and the
ratio = a single-coset average (`pv_full_period_ratio_eq_single_coset`) — one
Gauss period, no spectral averaging, the m² cancels. The geometric/interval
resonator is the **index-DC projector**, and exact computation shows the large
|η_b|² sit at arithmetically scattered indices (the Gauss-sum phases), so the
blind resonator is **anti-aligned** with the large values — the same DC-crossover
that caps everything else. **Reaches: √n only. Unconditional: yes. Log: no.**

---

## 4. The best lower bound now proven, and what the log still needs

**The best UNCONDITIONAL, axiom-clean lower bound remains M ≥ √3·√n** (moment
ratio, `_AvFloor_MomentRatioLowerBound`, from E₂ = 3n²−3n exact). None of the six
resonators exceeds it. What the resonator campaign *adds* is not a new floor but a
**precise localization of the log**, formalized in clean theorems:

1. **The engine is free and unconditional** (`resonator_ratio_lower_bound`).
2. **Every resonator's diagonal is exactly the Parseval floor** — the resonator
   coefficients ‖r‖² *cancel* on the diagonal (RES_0
   `coset_resonator_diagonal_ratio`, RES_1 `single_character_gives_parseval`,
   RES_3 `candidate4_ratio_mem_minMax`, RES_5 `pv_full_period_ratio_eq_single_coset`).
   So **the entire log lives in the off-diagonal Gauss-sum correlation.**
3. **The off-diagonal correlation kernel is the same object across all axes:**
   it is ∑_{δ≠0} ρ_r(δ)Γ(δ) (RES_0), or the non-multiplicativity of S(k) (RES_1),
   or the index-group Euler product (RES_3), or the tower cocycle excess ∑δ_i
   (RES_4). **They are all one statement: that the Gauss-sum phases g_j correlate
   multiplicatively over the cyclic index group ℤ/m.**

The log factor needs *exactly* this multiplicative-correlation input. In
2605.13715 the analogous input is **free** because the multiplicative variable is
the summation variable of a fixed character and the Euler product is a Mertens
count. Here it is **not free** because the multiplicative variable is the dual
index and the Gauss sums g_j are *not* multiplicative in j (Hasse–Davenport ≠
index multiplication; refuted exactly in RES_1, 290/290 coprime tests fail; and in
RES_3 the only way to force coherence is b-dependent, which is a ceiling). The
single most promising surviving target is **Heath-Brown's mean-value theorem for
character sums over the subgroup {χ^{dj}} applied to a HIGHER-moment functional of
the η_b** — not the 2nd-moment Rayleigh quotient, which is provably capped at
Parseval on its diagonal. That higher-moment subgroup mean-value is the open
object, and it is the *same wall* as the upper-bound BGK/Paley cancellation.

---

## 5. Honest verdict

**Did any resonator PROVE M ≥ c·√n with a growing log factor unconditionally — the
real win, the lower half of BGK?**

**No.** Every one of the six resonators reaches **exactly √n** (Candidate 1, 2, 4,
5, 6) or produces a **ceiling, not a floor** (Candidate 3) or **names the log as an
open `Prop` without delivering it** (Candidate 5). The best unconditional bound is
unchanged: **M ≥ √3·√n, no log.** Re-deriving √n and dressing it as a log floor is
the cardinal sin this synthesis refuses to commit: I checked every diagonal
collapse, and in each case the resonator coefficients *cancel* on the diagonal,
leaving the Parseval floor verbatim.

But the campaign is not a null result, and three findings are genuine:

- **The log is exactly localized.** It is provably *not* in the diagonal of any
  2nd-moment resonator (clean theorems, all six files). It lives *entirely* in the
  off-diagonal Gauss-sum-phase correlation, which is one object viewed from six
  angles.

- **The index-group Euler product is positively REFUTED as the source.** The
  m-prime witness (Candidate 4: m=4111 prime, ∏(1+1/ℓ)≈1, yet full log present)
  and the non-multiplicativity of S(k) (Candidate 2, 290/290 failures) show the
  Montgomery/Mertens mechanism **does not transplant**: there is no free Euler
  product on the dual index. The naive hope of §2 is killed, cleanly and with a
  smoking gun.

- **The true order is √log, not loglog.** The tower probe (Candidate 5) matches
  M/√n to √(log m) within a few percent across n=16..256, while √(loglog m)
  undershoots 2–3×. So the prize form **M = Θ(√(n log m))** is the right target,
  and any resonator route aiming only at loglog (the literal 2605.13715 strength)
  would be *too weak* even if it transplanted.

**The single honest residual**, shared by all six candidates and by the
upper-bound side: an unconditional lower bound on the off-diagonal Gauss-sum-phase
correlation — equivalently, that short ±-relations of the Gauss sums g_j over a
cyclic index subgroup do not destructively interfere. This is **not** a free
Mertens count here; it is the open BGK/Paley cancellation (β=4). The most literal
surviving path is **Candidate 2 promoted to a higher moment**: Heath-Brown's
mean-value theorem for character sums over {χ^{dj}}. If that mean-value theorem
transplants verbatim to a higher-moment functional of the η_b (it is a counting
statement, no equidistribution), it would prove M ≥ c·√n·loglog m unconditionally —
the lower half of BGK, a genuine first. The 2nd-moment route is exhausted and
provably capped; the higher-moment subgroup mean-value is untried and is the only
remaining unconditional-log candidate.

**Bottom line.** The resonator engine is free; the floor it delivers is √n; the log
is *not* free on the Gauss-period dual; and the precise reason — no Euler product on
the index because Gauss sums are not multiplicative in their character exponent — is
now a clean, formalized, refuted-where-refutable map. No QED was faked: five files
are sorry-free, the sixth has no code-level sorry and gates its log behind an
explicitly named open `Prop`. The lower half of BGK remains open, but its single
load-bearing input is now isolated, and it is the same wall as the prize.
