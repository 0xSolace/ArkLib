# A Manifesto for the δ* Prize: Why the Domain Is the Wrong Place to Look
### (an argument from the future for a new form of cancellation mathematics)

*Written in the voice of a researcher looking back, after the fact, at why the 2026 campaign
stalled — and what the new mathematics had to be. Grounded entirely in the in-tree findings:
the 100-route catalog, the open-avenue inventory, the route-elimination meta-theorem, and the
50-conjecture sweep (0 survivors).*

---

## I. The shape of the failure

Read the ledger and a single pattern screams from every dead route. The prize object is the
worst-case far-line incidence, which reduces (exactly, in-tree) to the sup-norm of an incomplete
character sum over a thin 2-power subgroup:

> `M(μ_n) = max_{b≠0} | Σ_{x∈μ_n} e_p(b x) |  ≤  C·√(n·log(p/n))`,   `n = 2^μ ≪ √q`.

Every one of the ~120 attacked routes tried to find this cancellation **on the domain μ_n** — the
`n` points `x` over which the sum runs. Weil completes the sum to `√q` and is *vacuous because
`n < √q`*. Stepanov builds an auxiliary polynomial vanishing on the domain and *stalls at `n^{2/3}`*.
The moment ladder `(qE_r)^{1/2r}` reads the domain's additive energy and *forced-anomalies past
`r=β+1`*. BGK's sum-product is a domain statement, *ineffective at `n^{1-o(1)}`*. Antipodal/Mann
counts the domain's vanishing relations and *pins exactly the boundary = Johnson*. The Cayley
graph `Cay(F_p, μ_n)` has its spectral gap *equal to* `M(μ_n)` — the graph **is** the wall.

The meta-theorem is therefore not a coincidence; it is a **conservation law**. Any estimate whose
only input is the domain's first- and second-order arithmetic (size, additive energy, Sidon-ness,
the spectral radius) is *blind to the phase information* that distinguishes the worst `b` from the
average `b`. Cauchy–Schwarz on the domain gives `√(Σ) = √(p·n)`-scale or, per-word, the Johnson
`n^{1/2}`. The `√log` excess that separates Johnson from the floor is a **rare-event / tail**
phenomenon, and tail phenomena are invisible to second moments. This is why energy methods cap and
why the moment method needs depth `r ≍ log q` (where char-p anomalies kill it). **The domain does
not contain the answer.**

## II. The three places the answer could live (and nobody looked)

If the cancellation is not on the domain, where is it? The campaign's own `★`-flagged-but-never-
attacked routes, read together, point to exactly three relocations — three different mathematical
universes in which the same number `M(μ_n)` becomes *computable* because the obstruction `n<√q`
no longer applies.

**(A) The parameter space, not the domain.** The far-line incidence is a function of the offset
`u₀` (and direction `u₁`), ranging over `q^{k+1}` points — a space **vastly larger than `√q`**.
Deligne's theorem is vacuous on the `n`-point domain but *sharp* on a `(k+1)`-dimensional parameter
family of bounded conductor. The Krawtchouk weight in the reduced sum `𝒮(u₀)` **is** a trace
function (Kloosterman-type, route 57); if `u₀ ↦ 𝒮(u₀)` is the trace of a geometrically irreducible
ℓ-adic sheaf of bounded conductor, Fouvry–Kowalski–Michel give `√`-cancellation **uniformly in
`u₀`** — and `u₀` lives where Deligne bites. *The cancellation we need is in the parameter, not
the domain.* Nobody computed the sheaf or its conductor. (Routes 56/57, ★, never attacked.)

**(B) The non-archimedean completion, not the complex absolute value.** `M(μ_n)` is a complex
magnitude, but `μ_n` is 2-power — its deepest structure is `2`-adic, not archimedean. Mann's
theorem (the only thing that works) is the *archimedean* shadow (vanishing sums over ℂ). The
**2-adic Newton polygon** of the pencil polynomial counts roots-of-unity by 2-adic valuation,
a genuinely different and possibly sharper count past the boundary; and the period, viewed along
the dilation tower `b ↦ ζb`, **interpolates to a `p`-adic measure** whose Amice transform / Iwasawa
`μ,λ`-invariants would bound the sup. The whole `p`-adic / Iwasawa universe is absent from the
ledger (`Amice: 0`, `Iwasawa: 0`). The archimedean wall need not be the `p`-adic wall.

**(C) The information functional, not the estimate.** Route 54 is the sharpest unexploited idea in
the catalog: *the worst-`u₀` excess is the supremum of a Gaussian-like process, and generic chaining
(Talagrand majorizing measures) bounds it by the **entropy** of the index metric.* Plain chaining
reproduces `√log` (= W4). But the index here is **not generic** — it is the RS/smooth-domain
parameter, self-similar under the 2-adic dilation tower. *If the chaining entropy of the RS-structured
`u₀`-process is `o(log q)`, the `√log` is **absorbed**, not estimated* — and the floor follows. This
is the one place the catalog explicitly says the prize barrier could dissolve. It was never computed.
Adjacent: a Shannon entropy-compression / communication-complexity lower bound on the subset-sum
distribution (open-avenue C7, never attacked) measures the same rare-event content from the other side.

## III. The new mathematics

The thesis is then sharp and falsifiable: **δ* is not a theorem about the arithmetic of a thin
set; it is a theorem about the geometry of a thick family.** The "new form of math" the prize
demands is a *transfer of the cancellation locus*:

1. From the `n`-point domain (where `n<√q` forbids completeness) **to** the `q^{k+1}`-point
   parameter family (where Deligne/FKM are sharp) — via the sheaf-theoretic identity of the
   Krawtchouk-weighted dual-code sum.
2. From the complex absolute value **to** the 2-adic Newton polygon / Iwasawa measure — exploiting
   that `μ_n` is 2-power, so its hardest structure is `2`-adic, not archimedean.
3. From a *pointwise estimate* **to** a *chaining/entropy functional* on the parameter process —
   where the RS self-similarity (the dilation tower, already formalized in-tree as the L²-doubling
   recursion) shrinks the metric entropy below `log q` and absorbs the excess.

Each of these is a *different mathematical universe* in which `M(μ_n)` is the same number but the
fatal obstruction (`n<√q`, ineffective BGK, char-p anomaly) **does not exist**. The campaign proved,
exhaustively, that the number cannot be reached *from the domain*. It did not — could not, given
the tools deployed — test whether it is reachable *from the family, the prime, or the entropy.*

That is the gap. The ten attempts below are the first probes into it.

## IV. The ten angles (each: never-attacked, reduces to nameable proven math once the new lemma is invented, escapes Johnson, targets δ*)

1. **Krawtchouk-as-trace-function + FKM sheaf bound on the `u₀`-family** (route 57, ★). Cancellation
   in the parameter; Deligne sharp where `n<√q` is irrelevant. New lemma: bounded conductor of the
   Krawtchouk-weighted dual-code sheaf.
2. **Generic chaining with RS-structured entropy** (route 54, ★). New lemma: chaining entropy of the
   `u₀`-process is `o(log q)` via dilation-tower self-similarity ⟹ `√log` absorbed.
3. **2-adic Newton polygon root count of the pencil polynomial** (truly novel). New lemma: the 2-adic
   NP gives a root-of-unity count sharper than Mann past the boundary.
4. **Amice/Iwasawa `p`-adic interpolation of the period along the dilation tower** (truly novel,
   `Amice/Iwasawa: 0` in-tree). New lemma: the tower period is a `p`-adic measure with bounded
   Amice transform.
5. **Terwilliger-algebra operator-norm of the Krawtchouk-weighted subcode sum** (route 85, ★). New
   lemma: `D` sits in a low-dim Terwilliger module ⟹ operator-norm bound.
6. **Schur–Siegel–Smyth trace problem on the period polynomial** (truly novel, `0` in-tree). New
   lemma: the largest period root is bounded by the absolute-trace structure of the 2-power period
   polynomial.
7. **Croot–Sisask almost-periodicity → Bohr-set forcing of the worst `u₀`** (route 30, ★). New lemma:
   the almost-period Bohr set of `1_C * 1_Ball` is large enough to force the worst case `≤ 2·avg`.
8. **Bourgain–Gamburd spectral gap / superstrong approximation for the *multiplicative* dilation
   action** (open-avenue C7, never attacked; distinct from the additive Cayley graph #49=W4). New
   lemma: a uniform gap for the 2-power dilation Cayley structure.
9. **Kelley–Meka / Polynomial-Freiman-Ruzsa (2023, NOT in the 100) structure of the bad-γ locus**
   (open-avenue B2). New lemma: PFR forces the vanishing-subset locus into `≤n` cosets past Johnson.
10. **Entropy-compression / Shannon bound on the subset-sum distribution** (open-avenue C7, never
    attacked). New lemma: the worst-case list ≤ the entropy of the `(r+1)`-subset-sum measure, which
    the 2-power rigidity caps below the budget.

If any one survives an honest attack, it is the first crack in the wall in the parameter/prime/
entropy direction — the new math. If all ten fall, we will have mapped the *second* boundary
(after Johnson): the boundary of what relocating the cancellation locus can buy, which is itself a
result worth having.
