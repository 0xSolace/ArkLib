# The Paley Gap: what it is, what would have to exist to close it, and a new machinery program

*A detailed essay (#444), 2026-06-21. Honesty contract: the Paley conjecture is OPEN; nothing here is a proof.
This essay states the gap precisely, characterizes the exact missing theorem, explains why every known tool
relocates to it, and proposes — and stress-tests — a new machinery program. Where a sub-result is "proven" it
is axiom-clean Lean; the central inequality is not.*

---

## I. The gap, exactly

For `p` prime, `n = 2^a | p−1`, `μ_n ⊂ F_p^×` the `n`-th roots of unity, the **Gauss period** is
`η_b = Σ_{x∈μ_n} e_p(bx)` and `M(n,p) = max_{b≠0}|η_b|`. The prize regime is the **Burgess barrier** `n ≍ p^{1/4}`
(`β=4`). The conjecture — equivalent to the $1M proximity prize via the proven bridge `δ* reaches the window
interior ⟺ the wall holds` — is

> **`M(n,p) ≤ C√(n log p)`, uniform in `n,p`** (apparent sharp constant `C = √2`).

The **proven floor** is BGK `n^{1−o(1)}` (Bourgain–Glibichuk–Konyagin, via Balog–Szemerédi–Gowers + Rudnev
point-plane), effective form di Benedetto `δ = 31/2880`, i.e. `M ≤ n^{0.989}`. The **gap is the entire half-power**
`n^{1−o(1)} → n^{1/2}`, and it is concentrated at the single hardest point `n = p^{1/4}` (the sum-product saving
vanishes exactly at `β=4`, *proven* in-tree as the dilution/stall theorem).

It is **one inequality**, with four faces, each the breaking point of a standard method (all proven equivalent
in-tree; see the companion expert statement `proximity-prize-open-problem-for-number-theorists-2026-06-21.md`,
forms A–D):

- **(A) Deep Wick energy.** `E_r(μ_n) ≤ (2r−1)‼·n^r` (DC-subtracted) to depth `r ≈ log p`. Sharpest local form
  (`CharPWickConditionalPin`): `c_r := (E_{r+1}−nE_r)/(2rn·\text{Wick}_r) ≤ 1` for all `r` — the **single open
  inequality**. Base `c_1 = 1 − 1.5/n < 1` proven; the char-0 part `E_r^∞ ≤ (2r−1)‼ n^r` proven for all `r`
  (Bessel/Lam–Leung, `_AvW0`); open part is the **wraparound** `W_r = E_r − E_r^∞`, equivalently
  `W_{r+1} ≤ (2r+1)n·W_r`.
- **(B) Gauss-phase DFT.** `M = (√p/m)·max_k|û(k)|`, `u_j = G(ω^{jn})/√p` unit Gauss-sum phases; wall =
  `max_k|û(k)| ≤ C√(m log m)` = effective, **worst-case-uniform** vertical Sato–Tate at growing order `m = (p−1)/n`.
- **(C) Wraparound Variance Law.** `W_r − E[W_r] = O^r((2r−1)‼ n^r)` — an arithmetic CLT for short (`≤ 2log q`-term)
  `±1` coincidences of `2^a`-th roots of unity mod `𝔭`.
- **(D) Early recurrence turnover (new, this campaign).** `M = ` top of the Jacobi matrix of the period measure
  `μ_η`; the recurrence coefficients obey the Hermite law `b_k² = nk` until a turnover depth `k^*`, and
  `M = √(2n·k^*)`; **wall ⟺ `k^* = O(log p)`** — the orthogonal polynomials of `μ_η` are Hermite to degree `log p`.

## II. What would have to exist to close it

The four faces converge on **one missing theorem**, which can be stated in increasing sharpness:

1. **Coarse:** an *effective, uniform-in-`p`, worst-case* equidistribution of Gauss-sum phases at growing order.
   Deligne/Katz give the *qualitative, distributional, average-over-the-family* equidistribution (the `u_j` become
   equidistributed on the unit circle as `p → ∞`); the prize needs the **sup over `k` of an `m`-point DFT of the
   `u_j`**, bounded *uniformly* over all `p`, including the worst prime in every window. The gap between
   "average/distributional" (proven) and "worst-case/uniform-effective" (needed) **is the half-power**.

2. **Sharp (arithmetic):** the wraparound bound `W_{r+1} ≤ (2r+1)n·W_r` to depth `r ≈ log p`, uniform in `p ≍ n^4`.
   `W_r` counts the short cyclotomic relations `Σ ζ^{a_i} ≡ Σ ζ^{b_j} (mod 𝔭)` that hold mod `𝔭` but not over `ℂ`.
   The required statement is that these mod-`𝔭` coincidences **do not over-accumulate** at depth `log p` — an
   *arithmetic central limit theorem* for vanishing sums of roots of unity modulo a prime, with `√`-scale
   fluctuations, uniform in the prime. **No such theorem exists.** The closest extant tools (Stickelberger,
   heights of cyclotomic integers) control the `𝔭`-adic *valuation* (= magnitude), not the archimedean modulus,
   and the relevant heights are *exponential* with no Iwasawa/descent handle.

3. **Geometric (form D):** that the recurrence coefficients of the period measure **leave the Hermite law early**,
   by degree `log p` rather than the trivial support degree `n/4`. Equivalently the equilibrium measure of the
   potential `V = −log(\text{density of } μ_η)` has support edge `≍ √(n log p)` — but the density's far tail is
   the sub-Gaussianity, so this needs the same input.

These are the **same theorem in four languages**. It is genuinely absent from current mathematics — not a trick
we have failed to find, but a structural result (effective worst-case equidistribution of a one-parameter family
of arithmetic phases, uniform in the modulus, at logarithmic depth) that no existing framework produces.

## III. Why every known tool relocates — the three proven obstructions

Three machine-checked structural constraints explain the ~63-angle, ~390-paper relocation, and **any** future
tool must respect them:

- **Phase-blindness pins to the wrong scale.** Every functional of the *magnitudes* `|η_b|` — moments `E_r`,
  Schatten/trace norms, Weil eigenvalue bounds, large sieve, Delsarte LP — is pinned to `√p` (incoherent
  completion) or `≥ n` (Johnson), both off the target `√(n log p)` by a power of `n`. The `√n` cancellation lives
  entirely in the **phases** `arg u_j`. (Proven: `moment_ladder_exceeds_prize`, `_AmplifiedLargeSieveSaturates`,
  the two-obstruction pincer.) *Consequence: the tool must be phase-aware.*

- **The proof must be archimedean.** A no-go trilogy shows the modulus of `W_r` cannot be certified by any
  algebraic-invariant, LP/Delsarte/Krein, or congruence/parity certificate. `p`-adic data sees valuations, not the
  complex modulus where the cancellation lives. *Consequence: the tool cannot be purely algebraic or `p`-adic.*

- **The randomness must be established, not exploited.** The phase sequence `(u_j)` is *statistically
  indistinguishable from random* conjugate-symmetric phases at the DFT level (`KS → 0`: `0.014, 0.008, 0.002` at
  `n = 16, 32, 64`); the worst-case sup sits at the 14th–62nd percentile of the random ensemble, and the
  Gauss-phase max-DFT is even *amplified* `+1.4σ` to `+5.6σ` vs random (the Jacobi-cocycle correlations make the
  worst case slightly worse than random, by a *bounded* factor). So a phase-aware method **cannot exploit
  non-randomness** — there is no structural defect to leverage; it must *prove* that the bounded amplification
  stays `≤ √2`. *Consequence: the tool must be non-perturbative in `r` and must establish a quantitative CLT.*

The unique surviving shape: **a phase-aware, archimedean, cyclotomic-sensitive, non-perturbative-in-`r`
quantitative CLT for the arithmetic phases, uniform in the modulus.** Each of the four equivalent forms is one
face of demanding exactly this.

## IV. A new machinery program (proposed; under adversarial stress-test)

Three programs aimed squarely at the surviving shape. Each is developed to its limit and honestly marked
*escape* or *relocate*; the verdicts below are the campaign's current best adversarial assessment.

**Program 1 — Arithmetic Riemann–Hilbert for the recurrence coefficients (form D).** Set up the Deift–Zhou
steepest-descent / equilibrium-measure analysis for the orthogonal polynomials of `μ_η`. The turnover `k^*` is the
Mhaskar–Rakhmanov–Saff number where the equilibrium support reaches the spectral edge. *What it would need:* the
far-tail of the density of `μ_η` (the potential `V` near the edge), at the precision that distinguishes
`√(n log p)` from the trivial `n`. *Verdict:* **relocates** — the density tail *is* the sub-Gaussianity. *But it
is the right language:* it converts the wall into an equilibrium-measure edge problem, where RH asymptotics are a
mature toolkit, and the new input it isolates (the arithmetic potential `V`'s edge behavior) is a cleaner target
than the moment ladder. *Buildable residue:* the exact `M = topeig(J)` identity and the Gershgorin upper bound
`M ≤ max_k|a_k| + 2max_k b_k` (true; relocates to the deep `b_k`).

**Program 2 — Stein / arithmetic-CLT for the wraparound (form C).** Apply Stein's method (exchangeable pairs or a
size-bias coupling) to `W_r`, whose dependence is *local* in the relation graph. *What it would need:* a bound on
the Stein remainder (the coupling discrepancy) that is itself `O((2r−1)‼ n^r)`. *Verdict:* **relocates** — the
remainder is a higher additive-energy term; locality does not survive to depth `log p` because the relation graph
is *not* sparse there (the very over-accumulation we are trying to rule out is the failure of local dependence).
*But:* Stein is the correct *engine* (it needs only local dependence, not the full MGF that independence-based
methods require), and it isolates the obstruction to a single explicit coupling term — the sharpest finite
statement of "the coincidences are locally controlled."

**Program 3 — Effective vertical equidistribution by positive-definite amplification (form B).** Average
`M(μ_n;p)²` over `p ∈ [P, 2P]`, `p ≡ 1 (mod n)`, against a non-negative mollifier concentrated on the bad
(high-`v_2(p−1)` / Fermat-like) primes. *What it would need:* the exceptional set to be mollifiable — finite or
positive-density-structured. *Verdict:* **relocates** — there are infinitely many `p` with `v_2(p−1) ≥ k` for
every `k`, and the bad set is *not* thin enough to mollify away; an effective average does not give the pointwise
worst case. *But:* it correctly localizes the difficulty to the *exceptional-prime structure*, and converts the
problem to a second-moment-over-`p` plus exceptional-set analysis — the only framework in which "uniform in `p`"
is naturally expressible.

**The honest synthesis.** All three relocate, *for the same reason*: each needs, at one precise step, the
far-tail / worst-case / deep input that *is* the missing theorem. But they are not failures — they are the
**right four languages** (equilibrium edge, Stein coupling, exceptional-prime amplification, recurrence turnover),
each turning the wall into a problem a *different* mathematical community has tools for (RH/integrable systems,
probability/Stein, analytic number theory/sieves, orthogonal polynomials/random matrices). The value of stating
the gap four ways is that the missing theorem may be visible — and provable — from one of those four sides by
someone holding that side's machinery, even though it is invisible from the others.

## V. What is buildable now, and what is not

*Buildable (true, axiom-clean):* the exact identities and the floor — `M = topeig(J)` (modulo formalizing the OP
machinery Mathlib lacks), the Gershgorin upper `M ≤ max|a_k| + 2max b_k`, the sharper lower bounds (`√5·√n`
landed), the conditional reductions (`c_r ≤ 1 ⟹ M ≤ √(2n log p)`, `_BGKTwoSided`, `CharPWickConditionalPin`), and
the structural no-gos. These are the formal skeleton around the wall.

*Not buildable:* the wall itself — `c_r ≤ 1` / `W_{r+1} ≤ (2r+1)n W_r` / `max_k|û(k)| ≤ C√(m log m)` /
`k^* = O(log p)` — because it requires the missing theorem. No amount of formalization of the surrounding
skeleton produces it; that is the precise meaning of "open."

## VI. Conclusion

The Paley gap is not a gap in our ingenuity but a gap in mathematics: it asks for an *effective, worst-case,
uniform-in-modulus* central limit theorem for short cyclotomic coincidences modulo a prime, at logarithmic depth,
where current tools supply only the average/distributional version. We have reduced the $1M prize to exactly this
one statement, proven its four-way equivalence, named the missing theorem as sharply as it can be named, and
built the entire formal skeleton around it. The proof awaits a genuinely new theorem of analytic number theory —
and the four equivalent forms are the four doors through which it might arrive.

*Not closure. The single open inequality stands; the skeleton around it is machine-checked.*
