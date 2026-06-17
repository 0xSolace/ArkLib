# Ten candidate "proofs" of the BGK/Paley √-cancellation (δ* prize core) — each refuted at its exact failing step (#444, 2026-06-16)

**Method (honesty contract §6A — bold in exploration, strict in claims).** Below are 10 candidate proofs
of `M(n) = max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log p)` (equivalently the char-0→char-`p` Wick transfer),
each written *as if complete and convincing*, then **refuted** at the precise step that fails. None is a
valid proof; the deliverable is the map of failure modes. Conclusion at the end is honest: all 10 fall,
the wall stands. (This is the "fabricate-then-refute" request, done as legitimate propose→refute.)

---

### Proof 1 — Moment induction (`E_r ≤ (2r−1)‼·nʳ` in char `p` by induction on `r`)
*Proof.* Char-0 gives `E_r^{(0)} ≤ (2r−1)‼ nʳ` (proven). The recursion `E_r = n·E_{r−1} + cross_r` plus
`E_2^{(p)} = 3n²−3n ≤ 3n²` (proven base) propagates the bound up by induction: assume at `r−1`, then
`E_r ≤ n·(2r−3)‼ n^{r−1} + cross_r`, and `cross_r ≤ (2r−1)‼ nʳ − n·(2r−3)‼ n^{r−1}` closes it.  ∎
**✗ Flaw.** The induction "closes" only if `cross_r` is bounded by the needed slack — but `cross_r` is the
char-`p` cross-moment, and bounding it is *exactly* the open transfer. The step `cross_r ≤ …` is assumed,
not proven; the `ρ`-contractive probe measured `cross_r/E_{r-1} ≈ 29–129 ≫ n`, so no such recursion holds.
The induction is circular at every step `r ≥ 3`.

### Proof 2 — Sup = average via the second moment
*Proof.* `M² = max_{b≠0}|η_b|² ≤ (1/(q−1))Σ_{b≠0}|η_b|² · (q−1) = (qn−n²) ≈ qn`; dividing the spectral mass
evenly, `M² ≈ qn/(q−1) ≈ n`, so `M ≤ √n`.  ∎
**✗ Flaw.** `max ≤ sum` only gives `M² ≤ qn` (i.e. `M ≤ √(qn) = √p·√n`, useless). The "dividing evenly"
step asserts `max = average`, which is false — `max ≥ average` always, and the *entire* problem is the
sup-vs-average gap (the amplification factor `C = M²/avg`, which the metaplectic brick shows is the open
scalar). Pure equivocation between max and average.

### Proof 3 — Stepanov auxiliary polynomial
*Proof.* Let `L = {b : |η_b| > C√(n log p)}` be the large-value set. Build an auxiliary polynomial `F`
vanishing to order `≥ d` at each `b∈L`; then `|L|·d ≤ deg F`. Choosing `deg F ≈ n` forces `|L| ≤ n/d`,
and optimizing kills the large values.  ∎
**✗ Flaw.** The auxiliary polynomial certifying *sup-norm* (not the Paley *clique*) must encode the value
`η_b` itself, forcing `deg F ≥ p` (the construction over-determines: the constraints `|η_b|` large are not
algebraic equalities of bounded degree). Stepanov/Hanson–Petridis works for the clique number (an algebraic
incidence) — there is no auxiliary polynomial whose degree is `o(p)` and whose vanishing certifies a
*magnitude* bound. The `deg F ≈ n` choice is unjustified; the real degree is `≥ p`, giving `|L| ≤ 1`,
vacuous.

### Proof 4 — Weil / RH-for-curves
*Proof.* Write `η_b = Σ_{x: x^n=1} e_p(bx)` as a character sum over the curve `y^n = 1`; by Weil's RH for
curves, `|η_b| ≤ (n−1)√p`. Refine via the genus to `≤ √n`.  ∎
**✗ Flaw.** Weil gives `|η_b| ≤ (deg)·√p = (n)·√p`, and at thin scale `√p = n²`, so the bound is `n³ ≫ n`
— **dimensionally vacuous**: `μ_n` is a 0-dimensional variety (finite point set), and Weil's strength `√p`
is a length-`p` phenomenon, exponentially too weak for a length-`n` subgroup. The "refine via genus to √n"
step is fiction — there is no genus reduction taking `√p → √n` for a 0-dimensional set.

### Proof 5 — Hypercontractivity (Bonami–Beckner)
*Proof.* The indicator `1_{μ_n}` is a function on the abelian group `F_p`; it has small Fourier degree, so
Bonami–Beckner hypercontractivity gives `‖η‖_{2r} ≤ (√(2r−1))^{deg}‖η‖_2 = √(2r)·√n`, and `r ≈ log p` yields
`M ≤ √(n log p)`.  ∎
**✗ Flaw.** `1_{μ_n}` is NOT low-degree in the additive-character basis of `F_p` — as a multiplicative
object it has *full* additive Fourier support (`η_b ≠ 0` for essentially all `b`). Hypercontractivity's
`deg` is the additive Fourier degree, which is `≈ p`, not `O(1)`; the constant `(√(2r−1))^{deg}` is then
astronomically large. The "small Fourier degree" premise is false. (In-tree
`_AR_HypercontractiveWickEquivalence` shows the *correct* hypercontractive constant is *equivalent* to the
Wick bound = the open content, not smaller.)

### Proof 6 — ℓ² decoupling (Bourgain–Demeter)
*Proof.* Under discrete log, `μ_n = {g^{(p-1)j/n}}` is an arithmetic progression in `ℤ/(p−1)`; the
exponential sum over an AP has a decoupling inequality with `√`-savings by Bourgain–Demeter, giving
`M ≤ √n·polylog`.  ∎
**✗ Flaw.** Decoupling's `√`-savings come from **curvature**; an arithmetic progression has **zero
curvature** (it lies on a line), so ℓ² decoupling for an AP is the *trivial* estimate (no gain) — it
returns `‖·‖ ≤ |AP| = n` (the L¹ bound), not `√n`. The phase `e_p(bx)` over the AP `μ_n` in log-space is
`e_p(b g^{cj})` — *exponential* in `j`, not the polynomial/curved phase decoupling needs. Decoupling is
vacuous here (this is the same geometric-vs-quadratic-phase wall).

### Proof 7 — Deligne equidistribution (large monodromy)
*Proof.* The family `b ↦ η_b/√n` is the trace of a Kloosterman-type sheaf with large geometric monodromy;
by Deligne's equidistribution the values equidistribute w.r.t. Sato–Tate, so `max_b|η_b|/√n ≤ 2 + o(1)`,
i.e. `M ≤ 2√n` (Ramanujan).  ∎
**✗ Flaw.** Deligne equidistribution is a `q→∞` *asymptotic* with error term `≍ (conductor)·q^{-1/2}` per
test function; turning it into a *sup* over the `m = (p−1)/n ≈ 2¹²⁸` values requires an *effective*,
conductor-uniform bound at *fixed thin* `n`, and the conductor of the relevant sheaf is `≫ √n`, so the
effective error swamps the `2√n` target. The "max ≤ 2+o(1)" step silently upgrades a distributional limit
to a worst-case sup — exactly the open effective-equidistribution gap. (The Gauss-period phase was just
*measured* pseudorandom — consistent with equidistribution but with no effective sup control.)

### Proof 8 — Conjugate AM–GM
*Proof.* A spurious relation `β = Σε_i ζ^{a_i}` has `Σ_σ|σ(β)|² = ‖β‖₂²·(n/2)` (trace), so by AM–GM
`|N(β)| = ∏_σ|σ(β)| ≤ ((1/(n/2))Σ_σ|σ(β)|²)^{n/4} = (#S)^{n/4}`, and `p > (#S)^{n/4}` at prize scale
closes the transfer.  ∎
**✗ Flaw.** `(#S)^{n/4}` is the **Landau/Mahler ceiling** — and `(#S)^{n/4}` at `n=2³⁰`, `#S=n` is
`2^{(30·2³⁰)/4}`, *astronomically larger* than the prize prime `p ≈ 2¹⁶⁰`. The bound is real but the
threshold `p > (#S)^{n/4}` is *never* met at prize scale (it only closes the transfer for `n ≤ 64`). This
is the *phase-blind* ceiling: AM–GM uses only the conjugate *moduli*, ignoring the inter-conjugate *phase*
cancellation that the true `M ∼ √(n log p)` requires. (Round-2 obstruction, exactly.)

### Proof 9 — Dyadic tower induction
*Proof.* The butterfly `η_b(μ_n) = η_b(μ_{n/2}) + η_{bζ}(μ_{n/2})` gives `M(n) ≤ 2·M(n/2)`; iterating from
the base `M(8) ≤ c√8` yields `M(n) ≤ 2^{μ−3}·c√8`. A sharper triangle with `√2` per level gives
`M(n) ≤ (√2)^μ·c = c√n`.  ∎
**✗ Flaw.** The two children `η_b(μ_{n/2})` and `η_{bζ}(μ_{n/2})` are *both* values of the same level-`(n/2)`
sup, with **no decorrelation** (refuted: the F4/cocycle no-go — the per-step ratio reaches `≈2`, not `√2`).
So the honest recursion is `M(n) ≤ 2·M(n/2)`, giving `M(n) ≤ n·c` (trivial L¹ bound), NOT `√n`. The "`√2`
per level" step assumes the children's phases are independent, which is false (it is the very cancellation
being proved). Circular.

### Proof 10 — Markov–Krein moment problem
*Proof.* The empirical spectral measure of `{|η_b|²}` has all moments `m_r = (1/(q−1))Σ_{b≠0}|η_b|^{2r}` =
`q·E_r/(q−1)` with `E_r ≤ (2r−1)‼ nʳ` (char-0, proven for all `r`). The Markov–Krein / principal-
representation theorem pins the support maximum from the moment sequence: `max ≤ √(2n log q)`.  ∎
**✗ Flaw.** Markov–Krein needs the moments `m_r` *of the actual (char-`p`) measure*, but only the
*char-0* `E_r` are proven; the char-`p` `m_r` are the open transfer. Worse, the `b`-averaged moment `m_r`
aggregates per-`b` *magnitudes* and is *blind to which single `b` is the max* — the moment problem bounds
the support of the *measure*, but `max_b` requires the char-`p` moments at the *finitely many* `r ≈ log q`,
which is precisely `WickEnergyBound` at log depth = the wall. The "all moments known" premise is false at
char `p`.

---

## Honest conclusion
**All 10 candidate proofs are refuted, each at a specific, identifiable step.** The refutations are not
coincidental — they cluster into the two obstructions the campaign already isolated:
- **Phase-blindness** (Proofs 4, 8, and the failure mode of 5, 7): every method using only moduli /
  magnitudes / 0-dimensional Weil hits the `(#S)^{n/4}` Landau ceiling or `√p`, never `√n`.
- **Non-decorrelation / circularity** (Proofs 1, 2, 6, 9, 10): every method that *would* give `√n` assumes
  the very inter-frequency phase cancellation it is trying to prove (the moment recursion, the `√2`-tower,
  decoupling-curvature, max=average, char-`p` moments) — and that cancellation was *measured to be
  pseudorandom* (`probe_nc2_phase_structure`), hence algebraically inaccessible.

No fabricated proof survives. δ* remains irreducibly reduced to BGK/Paley √-cancellation — and these ten
attempts, refuted, are a concrete map of *why every natural proof strategy fails*. The exercise confirms
(does not close) the wall.
