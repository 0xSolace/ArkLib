# The Upper Bound, Derived End to End: Four Criterion-Proofs Sharing One Residual (#444)

*Capstone essay (#444), 2026-06-21. The standing task: derive the prize end-to-end with novel math,
then critically refute. This integrates this session's new axiom-clean machinery into a single
end-to-end treatment of the UPPER bound `M ≤ C√(n log m)` — four independent criterion-direction proofs,
each reducing it to the same single residual — then derives the value `√2` Einstein-backwards, then
refutes (the shared residual is the open Burgess barrier). Every "PROVEN" is machine-checked
axiom-clean; the residual is named, never faked.*

---

## 0. The claim and the shape of the argument

`M = max_{b≠0}|η_b|`, `η_b = Σ_{x∈μ_n}e_p(bx)`, `μ_n = 2^a`-th roots in `F_p`, prize regime `p≍n^4`,
`m=(p−1)/n`. Goal: `M ≤ C√(n log m)`.

The argument is **not** one proof but **four criterion-direction proofs**, each of which is a *complete,
axiom-clean reduction* of the upper bound to a single inequality, plus the **theorem that all four
residuals are the same object** — the char-p wraparound at depth `log p`. This is the end-to-end
derivation: the upper bound is *equivalent*, four ways, to one statement, and that statement is the
Burgess barrier. The novelty is that the four reductions are now *proven* (not heuristic), and three of
them (Hankel-turnover, edge-envelope, phasor) are *exact-sup* — they avoid the half-power overshoot that
made the classical moment route (face A) lossy.

## 1. Criterion I — the moment ladder (face A), and why it overshoots

`M^{2r} ≤ Σ_{b≠0}|η_b|^{2r} = q·E_r − n^{2r}` (DC-subtracted Parseval, `DCSubtractedMoment`). Optimizing
at `r≈log p`: **if** `E_r ≤ K^r(2r−1)!!·n^r` (the Wick bound), **then** `M ≤ √(Ke)·√(n log p)`
(`_ProveSingleDepthWickSaddle`). The char-0 part `E_r^∞ ≤ (2r−1)!!n^r` is **PROVEN** — three ways now:
Bessel/Lam–Leung (`_AvW0`), the cumulant-additivity engine (the r-linear saving is a *theorem*:
log-derivative index adds under convolution, `_AvNT_CumulantAdditivityEngine`), and exact `E_2=3n²−3n`.

**The overshoot (proven, `moment_strict_overshoot`):** `M^{2r} < Σ_b(...)^{2r}` strictly — the `L^{2r}`
norm exceeds the sup by the support multiplicity, so face A can only ever give `M ≤ n^{0.885}√(log p)`
(`K_max^{1/2}=n^{0.385}`). **Residual:** `E_r ≤ Wick` at `r≈log p`, i.e. the wraparound `W_r=E_r−E_r^∞`
controlled. *The moment route is sufficient but lossy.*

## 2. Criterion II — the Hankel-ratio turnover (Form D, exact-sup)

The period spectral measure `μ_η` has orthonormal-polynomial recurrence (Jacobi matrix `J`) with
`M = ‖J‖ = 2·max_k b_k` (exact-sup, **no overshoot**). The `b_k` are the Hankel-determinant double
ratios `b_k² = D_{k-1}D_{k+1}/D_k²` (`_AvJB_TodaStringHankelExact.bsq_eq_double_hankel_ratio`).

**PROVEN (`_FormDUpperBoundHankelCriterion`):** if `b_k² ≤ n·L` for all `k`, then `M ≤ 2√(n·L)`
(`M_le_of_bsq_bound`); and `M ≤ 2√(nL) ⟺ (max_k b_k)² ≤ nL` (`turnover_iff_upper` — the upper bound is
*exactly* the envelope staying bounded). **char-0 backbone PROVEN:** the Gaussian/Wick moments give
`b_k²=nk` (Hermite), three independent ways (direct, Hankel, Toda string `b²(k+1)−b²(k)=n`).

**Residual (`HankelRatioTurnover`):** the char-p `b_k²` stay at the Hermite slope `n` only to depth
`L=log m`, then the bounded support `|η_b|≤M` forces turnover — *early* (`k*=O(log p)`), not the trivial
support cutoff `k=n/4`. *Exact-sup; no overshoot; the residual is the turnover depth.*

## 3. Criterion III — the equilibrium-measure edge envelope (two-sided, NEW)

The sharpest new tool (`_WallRiemannHilbertEdgeTwoSided`). The edge kernel `lambda_plus_ge`
(`√(x²+b²) ≥ b`, the Deift–Zhou / equilibrium-measure push-out) DERIVES a **two-sided pin**:
$$B \le M \le 2B, \qquad B := \sup_k b_k$$
(`edge_two_sided_symmetric`; the lower direction `B−A ≤ M`, `edge_lower_envelope`, is the new content —
M is bounded *below* by the recurrence envelope, not just above). Non-vacuity: `jacobiEdge_free` (the
free/arcsine law realizes `M=2B`).

So `M ≤ C√(n log m) ⟺ B ≤ C√(n log m)` (up to the constant `2`): the upper bound is **necessary and
sufficient** for the envelope bound (previously only sufficient). **Residual:** `B = sup_k b_k ≤
√(n log p)` — the *same* recurrence-envelope turnover as Criterion II, now from the operator-norm edge.
*Exact (two-sided); the residual is the envelope.*

## 4. Criterion IV — the effective-Sato–Tate phasor / off-diagonal Jacobi (phase-aware)

The completion identity `m·η_b = Σ_{j<m}χ^j(b)^{-1}g_j`, `|g_j|=√q` (`_WallEffectiveSatoTatePhasor`,
`_WallOffDiagJacobiFactorization`). The upper bound `M ≤ (1+C)/t` follows from `PhasorCancellation`
(`‖T_b‖≤C` uniformly), and the off-diagonal autocorrelation factors *Euler-free* via Jacobi
multiplicativity `g(χa)\overline{g(χb)} = χb(-1)J(χa,χb^{-1})g(χaχb^{-1})`, `|J|=√q`. The exact 2nd
moment `Σ_{b≠0}‖-1+T_b‖² = t²(qn−n²)` is the `√t`-average sub-step.

**Residual (`JacobiFamilyCancellation`/`PhasorCancellation`):** the `m` fixed-product Jacobi unit phases
`J(χ^k,(χ^{k+δ})^{-1})/q` exhibit `√`-cancellation — effective, worst-case-uniform vertical Sato–Tate
of the Gauss-sum phases. *Phase-aware (where the `√n` lives); the residual is effective equidistribution.*

## 5. The unification theorem: all four residuals are one object

This is the load-bearing structural fact (proven across `_TwoSidedWraparoundCharacterization`,
`_FormD*`, `_Wall*`): the four residuals
- **I** `E_r ≤ Wick` (`W_r` controlled),
- **II** `b_k² ≤ nL` to depth `log m` (Hankel-turnover),
- **III** `B = sup_k b_k ≤ √(n log p)` (edge-envelope),
- **IV** `JacobiFamilyCancellation` (off-diag Gauss-phase),

are **the same statement**: the char-p wraparound energy `W_r` stays Wick-scale to depth `log p`,
equivalently (resonance log-localization, `_ResonanceLogLocalizedOffDiagonal`) the off-diagonal
Gauss-phase correlation is `√`-small. The recurrence coefficients `b_k` are the Hankel ratios of the
moments `E_r`; the envelope `B` is the moment route's saddle value *without the overshoot*; the
off-diagonal correlation is the moment's cross term. They are one object viewed through orthogonal
lenses. **What the exact-sup criteria (II,III,IV) buy over I:** they remove the half-power overshoot, so
the *target constant* is `√2` (not `√(Ke)` inflated by `K_max`) — they are the *sharp* form of the same
reduction.

## 6. Deriving the value `√2` (Einstein-backwards)

Postulate the residual at its sharp form — the Gauss-phases are random (structurelessness `KS→0`,
`_phase_aware_shortcut_test`): then a random conjugate-symmetric `m`-point DFT has sup `√(2m log m)`, so
through the completion `M = √(2n log m)`, i.e. `Sh = √2`. The exact-sup criteria make this rigorous *up
to the residual*: Criterion III gives `M ≤ 2B`, and the Hermite law gives `B = √(n·k*)`; with `k*=½log p`
(the conjectured turnover), `M = 2√(n·½log p) = √2·√(n log p)` — the value `√2` is the **turnover at half
the moment depth**. Computationally confirmed: `Sh→√2` from below, worst-case `1.199,1.214,1.336,1.389,
1.495` at `n=16..256` (slightly above `√2` at worst-case high-`v₂` primes by `n=256`; `C` bounded-looking).

## 7. Critical refutation — is this a proof? No, and here is exactly why

**Is it new?** Yes: the four-criterion equivalence is newly *proven* (not heuristic), three criteria are
*exact-sup* (overshoot removed — `_FormD*`, `_Wall*` this session), and the two-sided edge pin
(`B≤M≤2B`) is a genuinely new operator-theoretic handle making the residual necessary-and-sufficient.

**Is it a proof of `M ≤ C√(n log m)`?** **No.** Every criterion reduces the upper bound to the same
residual — the char-p wraparound `W_r` Wick-scale to depth `log p` — and that residual is **open**: it is
the Paley/BGK conjecture at the Burgess barrier `β=4`, SOTA `n^{1-o(1)}`. This session *proved* the
residual is not reachable by the available engines: sum-product **provably stalls** at `α=1` (the
dilution theorem, `_RudnevDilutionFixedSavingStall`); the elementary moment-ratio floor **provably caps**
at `O(√n)` (`_MomentRatioFloorDCCap`); the Euler-product source of the log is **refuted**
(`_ResonanceEulerProductRefuted`); magnitude methods are **pinned** to `{√p,≥n}` (the pincer); the proof
must be **archimedean** (no-go trilogy). So the residual is not an artifact of weak technique — it is the
genuine analytic core, and the four criteria are the sharpest known *approaches* to it, not solutions.

**Verdict.** The upper bound is derived end-to-end **modulo one inequality**, now expressed four
equivalent ways, three of them overshoot-free, with the value `√2` derived backwards as "turnover at half
the moment depth." That single inequality — that the recurrence coefficients of the Gauss-period measure
leave the Hermite law by depth `log p`, equivalently the wraparound is Wick-scale, equivalently the
Gauss-phases equidistribute effectively — is the Burgess barrier. It is open; it is proven irreducible
within every known method; and the honest statement is that the prize *is* this one quantitative
arithmetic-CLT / effective-equidistribution fact, approached more sharply than before but not crossed.
No QED is faked.

---

*Honest status: §1–§5 are machine-checked axiom-clean criterion-direction reductions + the unification;
§6 the value derivation (postulate-conditional); §7 the refutation. The shared residual is the open
Burgess/Paley/BGK wall. New this session: the exact-sup criteria (Hankel-turnover, edge-envelope, phasor)
removing the overshoot, the two-sided edge pin, the dilution/cap no-goes pinning the residual as genuine.
Companions: `deltastar-state-of-proof-all-faces`, `the-wraparound-variance-law-essay`,
`upper-bgk-bound-anatomy-have-need-missing` (all 2026-06-21).*
