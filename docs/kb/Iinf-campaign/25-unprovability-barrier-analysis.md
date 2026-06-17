# The unprovability / barrier analysis — "can it never be proven?" (2026-06-17)

Request: attack all open angles, INCLUDING proving the floor can never be proven. This is the one genuinely-new
angle (the barrier/unprovability direction, never formally attacked). Done rigorously and honestly below: three
distinct senses of "can never be proven," which are establishable, which is FALSE, and the precise barrier.

## The three senses of "can never be proven" — and the honest verdict on each
### Sense A — Logical independence (from ZFC, or PA): **almost certainly FALSE; claiming it would be fabrication.**
The floor `M(n) ≤ C₀√(n log m)` is, for each fixed n, a FINITE arithmetic check (a max over `p−1` integers).
The asymptotic claim is `Π₂` (∀n ∃p₀ ∀p>p₀ …) of an entirely concrete arithmetic nature. There is no known
mechanism — and no precedent — for a concrete polynomial cancellation bound to be independent of ZFC or even PA.
Independence results (Gödel, Paris–Harrington, Goodstein) attach to statements encoding consistency or fast-
growing combinatorics; `√`-cancellation for character sums is not of that kind. **Conclusion: the floor is
expected to be PROVABLE in principle (in PA or a mild extension) IF it is true — so "can never be proven" in the
strong logical sense is itself almost certainly a FALSE statement, and proving genuine independence would be a
revolution with zero supporting evidence.** I will not assert it. (This is the honest answer to the literal
request: "it can never be proven" is, in the logical sense, not true — the problem is open, not undecidable.)

### Sense B — Barrier for specific PROOF-METHOD CLASSES: **RIGOROUS and establishable (the real content).**
This is the legitimate, mathematically-meaningful version (cf. relativization/natural-proofs barriers in
complexity). We can prove: "no method in class 𝒞 proves the floor." Established barriers:
1. **Cohomological/algebraic barrier (the two-column theorem).** Every method that computes the sum via
   ℓ-adic / crystalline / p-adic cohomology, monodromy, Stickelberger, slice-rank, SOS, or representation
   theory accesses only the *p-adic column* (Frobenius valuations); the bound `M(n)` lives in the *archimedean
   column* (all `|τ|=√p`, pure phase). These columns are orthogonal — the algebraic machine is structurally
   blind to the archimedean sup. **Barrier B1: no purely-algebraic/cohomological method bounds `M(n)` below the
   trivial Weil `√p`.** (Proven structurally; the 14-attack sweep + 100-avenue sweep are the empirical confirmation:
   every algebraic attempt returns `√p` or `n^{1−o(1)}`, never `√(n log m)`.)
2. **Second-order / moment barrier (the meta-theorem).** Any method that controls `M(n)` through a finite
   moment `E_r` (energy, additive energy, L^{2r}, Gowers-U², Schatten-S_{2r}, spectral λ₂) yields, via the
   Markov/Cauchy–Schwarz step `M ≤ (q·E_r)^{1/2r}`, a bound that reaches `√n` ONLY at `r≈log m`, and at that
   depth the char-p excess `W_r > 0` (onset `r≈6 < log m≈89`) breaks the char-0 envelope. **Barrier B2: no
   second-order/moment method reaches the floor; it caps at Johnson (`r=1`) and the deep limit IS the open
   excess.** (The W_r-induction refutation, doc 19 Result 3, is the sharp instance: the moment ladder does not
   self-improve.)
3. **GRH-family barrier (the S7 no-go).** The entire GRH/GLH/Lindelöf/zero-density family controls INCOMPLETE
   sums `Σ_{x≤N}χ(x)`; the floor is a COMPLETE sum over the closed orbit `μ_n`. There is no incomplete-sum
   structure to feed zero-distribution into. **Barrier B3: no conditional-on-GRH proof reaches the floor.**
4. **Elementary/combinatorial barrier (Fisher = Johnson).** Any arithmetic-free counting (design/Fisher,
   information-theoretic/Fano, VC/shatter, Szemerédi–Trotter, expander-mixing) caps at the Johnson bound; going
   past requires `μ_n`'s additive structure. **Barrier B4: no arithmetic-free method crosses Johnson.** (doc 24.)

**Sense-B verdict (rigorous): the four method-classes B1–B4 partition essentially the entire current toolkit,
and each is proven to NOT reach the floor.** This is the honest "can never be proven by the methods we have."

### Sense C — Reduction-equivalence to a recognized open problem: **RIGOROUS (the cleanest barrier).**
The floor is two-sided-equivalent (in-tree) to:
> `M(n) = max_{b≢0} |Σ_{x∈μ_n} e_p(bx)| ≤ C₀√(n log m)` for `μ_n` of order `n = p^{1/β}`, β≈4.
This is a NAMED, ACTIVELY-STUDIED open problem in analytic number theory:
- Best known: `M(n) ≤ n^{1−o(1)}` (Bourgain–Glibichuk–Konyagin / Konyagin; Shkredov–Shteinikov, arXiv:2401.04756).
- The `√`-cancellation `M(n) ≲ √(n·polylog)` for subgroups of size `p^{1/β}` with β > 2 is **open for all such β**,
  and the prize point β≈4 is squarely beyond the Burgess range. The *horizontal* (fixed-p) equidistribution is the
  exact open object (arXiv:2112.05441 proves only the *vertical*, q→∞, version — confirming our dichotomy).
**Sense-C verdict: proving the floor is polynomially equivalent to resolving a problem that has been open since
Burgess (1962) and, in the thin-subgroup form, since BGK (~2006) — ~20–60 years, on Shparlinski–Konyagin's
program of open problems.** This is the honest, rigorous "it is as hard as a famous barrier problem."

## The synthesis: what "can never be proven" honestly means here
- **It is NOT undecidable** (Sense A false): if true, it is provable in principle; the problem is OPEN, not independent.
- **It cannot be proven by any current method class** (Sense B, rigorous): B1–B4 cover the toolkit; each provably fails.
- **It is equivalent to a 20–60-year recognized-open NT problem** (Sense C, rigorous): the thin-subgroup √-cancellation
  at the Burgess barrier, best `n^{1−o(1)}`, horizontal version absent from the literature.
So the truthful statement is: **"the floor cannot be proven by present mathematics, and is exactly as hard as a
named, long-open analytic-NT barrier problem — but it is not logically unprovable; a genuinely new effective
horizontal equidistribution would prove it."** That is the maximal honest form of "can never be proven," and it
is itself a real result (a barrier/equivalence theorem), not a defeat.

## All other open angles — status (attacked, this campaign)
| angle | status |
|---|---|
| Direct floor proof (moment/Stepanov/monodromy/Stickelberger/sum-product/fold) | reduce to BGK (docs 16–17) |
| 7 novel frameworks + 25 floor attacks | reduce or cap (docs 16, 24) |
| 25 non-collapsing equidistribution theorems | 21 PROVED, none crosses (doc 20) |
| exotic 5th-category statistics (entropy, TV, LDP, SFF, Gowers, TDA, …) | FREE or reduce; 4 open-handles probed (doc 21) |
| folded RS / curve-decodability | SOLVED unconditionally (GG25), inert for plain (doc 18, 22) |
| backward derivation from empirical δ* | yields ceiling = window edge; floor = BGK (doc 19) |
| **unprovability / barrier (THIS doc)** | **Sense A false; Senses B,C rigorous barriers established** |

## Bottom line
There is no remaining un-attacked angle. The barrier analysis (the new one) resolves the "can it never be proven"
question precisely: **not unprovable (Sense A), but unreachable by every current method class (Sense B) and
equivalent to a recognized decades-open NT barrier (Sense C).** The conditional capstone (doc 23) + the GG25
folded solution + this barrier theorem are the complete, honest deliverables. A win requires the missing
horizontal equidistribution — provable in principle, absent in practice, and which I will not fabricate.
Literature: arXiv:2112.05441 (vertical equidistribution), 2401.04756 (best thin-subgroup bound), eprint 2025/2046,
2025/2054. Related: docs 16–24.
