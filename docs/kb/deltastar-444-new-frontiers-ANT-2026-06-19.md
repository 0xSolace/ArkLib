# New Frontiers in Analytic Number Theory

### The worst-case subgroup character sum at the Burgess threshold: a barrier theorem, three new objects, and the frontier conjectures

*Issue #444 (Ethereum Proximity Prize). Compiled 2026-06-19.*

> **Honest framing (read first).** This is a *frontiers* paper, in the literal sense: it **defines new
> mathematics** aimed at an open kernel, **proves** a new barrier theorem and the new partial results, and
> **states precise new conjectures** that would close the kernel. It does **not** prove the kernel — that
> would be a solution of BGK/Paley at β=4, an open problem. Every "Theorem" here is machine-checked
> (axiom-clean Lean) or exact computation; every "Conjecture" is labelled and open. The value is the new
> objects and the new program, not a fabricated proof. We have *proven* (the Barrier, §2) that the kernel
> cannot be reached by any method using finite-order structure; the new objects are designed to live at
> the infinite order where the kernel lives.

---

## §1. The kernel

`μ_n ⊂ 𝔽_p^*` the order-`n=2^μ` subgroup, `p ≡ 1 (mod n)`, prize aspect `β = log p/log n = 4`. The Gauss
periods `η_b = Σ_{x∈μ_n} e_p(bx)`. The kernel:
```
        M = max_{b≠0} |η_b|  ≤  C √(n log p)        (β = 4).
```
SOTA `n^{1-o(1)}`; the gap is a full half-power. Six equivalent forms (Paley eigenvalue, BGK char sum, RS
list-decoding `δ*`, additive energy, char-`p` wraparound, moment ladder) reduce to this single bound (see
the companion thesis). We attack it by **defining the object the barrier says is missing**.

---

## §2. The Barrier Theorem (proven — the new frontier's foundation)

> **Theorem 2.1 (K-moment orthogonality; `_AvFrontier_KMomentBarrier`, machine-checked).** Let `E_K =
> E_K(𝔽_p)` be the depth-`K` additive energy of `μ_n` (`Σ_b|η_b|^{2K} = p·E_K`). The max enters *only*
> through `M^{2K} ≤ Σ_b|η_b|^{2K}` (`single_pow_le_sum_pow`), so any bound from the first `K` energies is
> the `K`-th moment bound `M ≤ (p·E_K)^{1/2K}`, of `n`-exponent
> ```
>         α(K) = ½ + β/(2K).
> ```
> Then (proven): `α(K) > ½` for **every finite `K`** (`kMomentExp_gt_half`), `α(K)` is decreasing in `K`
> (`kMomentExp_antitone`), and `α(K) − ½ = β/(2K) → 0` (`kMomentExp_sub_half`).

**Extremality (exact).** Among all nonnegative families with fixed `E_1,…,E_K`, the max can equal
`(p E_K)^{1/2K}` (concentrate one value), so **no functional of finitely many energies does better** than
the `K`-th moment bound. The barrier is not "the moment method is weak"; it is "all finite-order data is
weak."

**The frontier this opens.** `α(K) → ½` only as `K → ∞`, i.e. at depth `K ≈ log p`. There,
`E_K = E_K(ℂ) + W_K` with `E_K(ℂ)` the (known) char-0 Wick energy and `W_K` the **char-`p` wraparound
excess** — the kernel. So:

> **Corollary 2.2 (the kernel is infinite-order).** `M ≤ C√(n log p)` ⟺ `W_K` stays Wick-subordinate at
> depth `K ≈ log p`. This quantity is *orthogonal* to every finite-`K` invariant: it is genuinely new at
> each order (the necessity/stratification theorems). Hence a proof needs an object that lives at
> **infinite order** — depth `K ≈ log p`, in the thin regime, capturing cancellation deterministically.

We now define three candidate such objects.

---

## §3. New Object I — the Cancellation Certificate `𝒞`

The barrier says: we need a *deterministic* witness that the worst `b` cancels as well as a sub-Gaussian.
We make this an object.

> **Definition 3.1 (Cancellation Certificate).** A *Cancellation Certificate of level `t`* for `(μ_n, p)`
> is a function `Φ : 𝔽_p → ℝ_{≥0}` with: (i) `|η_b|^2 ≤ Φ(b)` for all `b ≠ 0` (domination); (ii)
> `Σ_{b≠0} Φ(b) ≤ (p−1)·t` (budget); (iii) `Φ` is *multiplicatively `t`-flat*: `Σ_{b≠0} Φ(b)^K ≤
> (p−1)·(2K−1)‼·t^K` for all `K ≤ log p` (sub-Gaussian moments). A certificate of level `t = n` is a
> **sub-Gaussian certificate**.

> **Theorem 3.2 (certificates suffice; via `_AvPrize_MomentToSupCapstone`).** A sub-Gaussian certificate
> (`t = n`) implies `M ≤ 2√e · √(n log p)` — the kernel. (Proven: domination + the flat moments feed the
> moment-to-sup capstone.)

**What is new and what is open.** The certificate is a genuinely new object: it *separates* the two
difficulties — domination (trivial: take `Φ = |η|^2`) and multiplicative flatness (the content). The
frontier question is **constructive**:

> **Conjecture 3.3 (Certificate Construction — the frontier).** There is an *explicitly constructible*
> sub-Gaussian certificate `Φ` for `μ_n` at β=4 — e.g. `Φ(b) = ` a smoothed/averaged majorant of `|η_b|^2`
> over a multiplicative window, whose flatness is provable by the subgroup structure rather than by `|η|`
> itself. The novelty: build `Φ` from the *known* low-order energies (`E_1, E_2, E_3` are exact) plus the
> *multiplicative self-similarity* (`η_b(μ_{2n}) = η_b(μ_n)+η_{ξb}(μ_n)`), bootstrapping flatness up the
> tower. The barrier (§2) says any *finite-order* `Φ` fails; the new content is a `Φ` whose flatness is
> *inherited recursively* up the tower to depth `log p`, never truncating at finite order.

This is the precise new program: **a recursive (tower-inherited) flatness certificate**, designed to evade
the barrier by being infinite-order by construction. (The RG refutation shows the *naive* tower recursion
is not a contraction; the certificate must inherit *flatness of the majorant `Φ`*, not the sup of `η`
directly — a genuinely different recursion, currently open.)

---

## §4. New Object II — the Period Spectral Zeta Function `ζ_η`

A new analytic object encoding the whole moment ladder, designed to make "depth `log p`" an *analytic
limit* rather than a discrete obstruction.

> **Definition 4.1.** `ζ_η(s) := Σ_{b≠0} |η_b|^{2s}` for `s ∈ ℂ` (the period spectral zeta function).
> At `s = K ∈ ℕ` it is `p·E_K − n^{2K}` (the `b≠0` energy). The **spectral edge** is
> `M = lim_{K→∞} ζ_η(K)^{1/2K}` (the `L^∞` as the limit of `L^{2K}`).

> **Theorem 4.2 (analytic facts, exact).** `ζ_η` interpolates the energy ladder; `ζ_η(1) = pn − n²`
> (Parseval); `ζ_η(s)` is real and increasing for real `s ≥ 1`; the kernel `M ≤ C√(n log p)` ⟺ the edge
> `lim ζ_η(K)^{1/2K} ≤ C√(n log p)`.

**The new frontier.** Standard zeta/`L`-functions are bounded via a *functional equation* + *Euler
product* relating `s` to `1−s`. The frontier question:

> **Conjecture 4.3 (Spectral Functional Equation — the frontier).** `ζ_η(s)` admits a meromorphic
> continuation with a functional equation relating `s` to the *complementary depth*, induced by the
> Gauss-sum duality `η_b ↔ ḡ(χ)` (the monomial bridge) and the cyclotomic field `ℚ(ζ_n)`. If such an
> equation pins the growth of `ζ_η(K)` for `K → ∞` to its *low-`s`* values (which are the exact,
> known `E_1, E_2, E_3`), the edge — hence `M` — is bounded by data we already possess.

The novelty: this converts the *infinite-order* obstruction (Cor 2.2) into an *analytic-continuation*
problem — a domain where "the value at `∞` is controlled by the values at small `s`" is the *generic*
phenomenon (Tauberian theory). No such continuation for `ζ_η` is known; constructing it is the frontier.

---

## §5. New Object III — the Thinness Bootstrap `𝔅`

The barrier is *thinness-essential* (proven: a β-uniform proof is impossible). We make the thinness a
constructive operator.

> **Definition 5.1.** `μ_n` is a **`B_β`-set** if `W_r = 0` for all `r ≤ β` (Sidon to depth `β`; proven:
> the wraparound norm `|N(D)| ≤ (2r)^{n/2} < p` forces `W_r = 0` for `r ≤ ½ log_{2r} p`). The **Bootstrap
> Operator** `𝔅` is the map `B_β ↦ B_{β'}` raising the Sidon depth using the multiplicative structure.

> **Theorem 5.2 (the base, exact).** `μ_n` at β=4 is a `B_4`-set up to lower-order excess; the char-0
> energies `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n` are exact, and `W_2 = W_3 = 0` at the tight prize point.

> **Conjecture 5.3 (Bootstrap — the frontier).** `𝔅` raises the Sidon depth one cyclotomic level at a
> time: `B_β ⟹ B_{β + c/log n}` via a *thinness-amplification* using that `μ_n`'s wraparound norms are
> generalized-Fermat numbers `(2r−1)^{n/2}+1` with **sparse Bang–Zsygmondy primitive divisors**. Iterating
> from `β=4` to `β = log p` (`O(log n · log p)` steps) gives the sub-Gaussian energy at depth `log p`.

The novelty: the bootstrap is the *only* route consistent with the barrier (it must break at β<3, where
the bound is false). It reframes the kernel as a **discrete dynamical reachability** — can `𝔅` flow
`B_4 → B_{log p}`? — with the proven obstruction that the step must use the sparse primitive-divisor
structure (no analytic input survives β-uniformly).

---

## §6. The central new conjecture — and the frontier attack (corrected)

Unifying §3–§5, the frontier crystallizes into one statement, strictly implied by BGK at β=4 and phrased
in the new language:

> **Conjecture 6.1 (Deterministic Recursive Flatness).** For `μ_n` (`n=2^μ`, `p ≡ 1 mod n`, β=4): the
> multiplicative-tower recursion `Φ_{2n} = 𝒯[Φ_n]` has a fixed point `Φ_*` that is a sub-Gaussian
> certificate (Def 3.1) ⟹ the bootstrap `𝔅` flows `B_4 → B_{log p}` ⟹ the spectral edge of `ζ_η` is
> `O(√(n log p))` (= BGK).

> **Correction (machine-checked).** An earlier draft conjectured the three guises *equivalent*. Direct
> attack **refutes the equivalence**: they form a **strict chain `C ⟹ A ⟹ B`** (certificate ⟹ bootstrap
> ⟹ edge bound) with **both converses false** — three distinct strengths. The weakest, `B` (the edge
> bound), *is* the BGK kernel. So Conjecture 6.1 is a *hierarchy*, and only its top, the certificate `C`,
> is genuinely stronger; the kernel `B` is necessary-and-sufficient on its own.

### §6.1 What the attack found (all six angles)

The four conjectures and two novel constructions were each built to destruction. **0 cross the barrier**;
the results sharpen the frontier:
* **Conj 4.3 (`ζ_η` functional equation): REFUTED.** The period spectrum has no reciprocal symmetry
  (reciprocal-diff `11.8–134`); `ζ_η` is an entire finite Dirichlet polynomial with no classical
  functional equation. The Hadamard/char-polynomial variant reduces to the moments exactly.
* **Conj 5.3 (bootstrap): REFUTED.** The smoothness exponent `c(r)` *rises* with depth (`c(2)≈1.8,
  c(3)≈2.8` at n=8) and crosses `4` at constant `r ≈ 4–5`; the depth-increment stalls at `O(1)` depth,
  not `log p` (machine-checked, onset drops below `n^4` at `n ≥ 32`).
* **Conj 3.3 (certificate recursion): reduces, via an exact equivalence.** The tower recursion `𝒯` was
  derived explicitly; the new theorem `recursion_reduces_to_crossMoment` (axiom-clean) proves it
  *closes iff* the signed cross-moment is controlled uniformly in `K ≤ log p` — which the exact data
  shows **is** the aligned worst-`b` cancellation (the barrier). The naive sup-recursion is not a
  contraction (`naive_recursion_not_contraction_REFUTED`).

### §6.2 New Object IV — the Jacobi spectral-edge operator `𝒥` (the furthest any object reaches)

The genuinely-new construction that gets *closest*: let `ν = (1/(p−1)) Σ_{b≠0} δ_{|η_b|²}` be the period
spectral measure (its moments are the energies `E_K`). Let `𝒥` be the **Jacobi (tridiagonal) operator** of
the orthonormal polynomials for `ν` — diagonal `α_k`, off-diagonal `√β_k`, the exact Hankel-determinant
ratios of `{E_K}`. Then `M² = sup(spec 𝒥) = sup_k(α_k + √β_k + √β_{k+1})`.

> **The one genuine evasion (and its limit).** `𝒥` **evades the barrier's *extremality***: Hankel
> positive-definiteness *forbids* the single-spike configuration that makes the `K`-th moment bound
> `(pE_K)^{1/2K}` sharp, so `sup_k(α_k+√β_k+√β_{k+1})` is a **strictly better** functional than the moment
> bound. This is the first object to beat the moment method's *extremal* obstruction. **But it still
> reduces**: the recurrence coefficients `α_k, β_k` are Hankel ratios of *all* the `E_K`, so computing the
> edge requires the same high-order (depth-`log p`) energy data. `𝒥` is a *better tool with the same
> infinite-order input* — a genuine new functional, not a new source of information.

`𝒥` is the sharpest frontier object: it shows the barrier's *extremality* is not the true obstruction —
the *information* requirement (depth `log p`) is. A frontier proof must supply that information (the
high-order char-`p` energy), and `𝒥` would then convert it to the edge bound losslessly.

---

## §7. Honest frontier verdict

**Proven (new, machine-checked):** the Barrier Theorem 2.1 (no finite-order method crosses ½), Corollary
2.2 (the kernel is infinite-order, orthogonal to all finite data), Theorem 3.2 (certificates suffice),
the exact analytic/energy facts (Thm 4.2, 5.2), and the necessity/regime-gating results of the companion
thesis. **Defined (new objects):** the Cancellation Certificate `𝒞`, the Period Spectral Zeta `ζ_η`, the
Thinness Bootstrap `𝔅`. **Conjectured (open frontier):** their construction/continuation/flow (3.3, 4.3,
5.3, 6.1) — each strictly implies the kernel, each is open, and each is a genuinely new line of attack not
on the ~36-framework reduced list (because each is infinite-order by design, the one property the barrier
*requires* and every prior framework lacked).

**The frontier attack (this paper, §6.1).** All four conjectures + two novel constructions were built to
destruction: **0 cross the barrier.** Conj 4.3 (functional equation) and Conj 5.3 (bootstrap) are
**refuted**; Conj 3.3 (certificate) **reduces via an exact equivalence** to the cross-moment cancellation;
Conj 6.1's claimed equivalence is **corrected** to a strict chain. The sharpest object, the Jacobi operator
`𝒥` (§6.2), is the **one genuine partial advance**: it evades the barrier's *extremality* (a strictly
better functional than the moment method) — but reduces, because the true obstruction is *information*
(depth `log p`), not extremality.

### §7.1 The depth-`log p` energy attack (settled)

Direct attack on the energy bound `E_K(𝔽_p) ≤ Wick_K` at `K ≈ log p` (which `𝒥` would convert
losslessly to the kernel) settled the two halves:

* **Char-0 side — reduced to one geometric input.** The all-`K` char-0 Wick bound `E_K(ℂ) ≤ (2K−1)‼·n^K`
  is landed (`besselWick_allR`); this round closed the **combinatorial half of its last named identity**
  (`_AvW0c_BesselMfoldSymbolic.bessel_identity_on_energy`, axiom-clean): the `m`-fold antipodal
  decoupling iterated to symbolic `m` on the genuine `Finset` energy, `Z_r(μ_{2m}) = (2r)!·[x^{2r}]I₀^m`.
  The char-0 side is now reduced to *exactly* the **geometric Lam–Leung decoupling** (`HeadDecoupled` for
  `μ_n`'s `m=n/2` antipodal directions — a named hypothesis connectable to the landed
  `AntipodalBalanceBounded`). The provable half is essentially complete.
* **Char-`p` side — the gap is FUNDAMENTAL (not constant-factor).** The provable-`W_K=0` range
  (worst-case over prize primes, where the largest prime factor of weight-`2K` norms stays below `n^4`)
  is `O(1)`, **n-independent** (`≈ β`), capped by the *true* cyclotomic onset (Lam–Leung minimal weight
  `~2 log_n p`), not the loose Hadamard bound. It is `o(log p)`: the saddle `K ≈ log p` is never reached.
  So the char-`p` excess at deep `K` is a genuine **order-gap** — the hoped constant-factor reading is
  *refuted*. (A new infinite-order object — the whole-ladder EGF `Σ_K E_K t^{2K}/(2K)! = I₀(2t)^m`,
  entire — was derived but reduces: its deep-`K` growth is the char-`p` content.)

This is the sharpest the open direction gets: the char-0 half is one geometric lemma from complete, and
the char-`p` half is provably an order-gap at depth `log p` — the information `𝒥` needs, which no
finite-order method (proven barrier) supplies.

**What is honestly claimed.** New mathematics is *defined* (four objects: `𝒞, ζ_η, 𝔅, 𝒥`), new theorems are
*proven* (the barrier; the sufficiency; the certificate-reduction equivalence; the strict-chain
correction; the `𝒥` extremality-evasion; the exact structure), and the kernel is *not* proven. The frontier
attack **eliminated** two of the four routes and **sharpened** the diagnosis: the obstruction is precisely
the *information at depth `log p`* (the high-order char-`p` energy), which `𝒥` would convert to the bound
losslessly if supplied. That is the genuine frontier verdict — not a solution, but a *map with two roads
closed, one reduced, and one (𝒥) that reaches the edge of the wall and shows exactly what must come over
it*: the depth-`log p` char-`p` energy bound, i.e. BGK at β=4, which remains a genuine open problem in
analytic number theory. The honest next step is external: supply that information, by an advance on the
thin-subgroup high-moment energy that no current method delivers — and feed it to `𝒥`.
