<!-- #444 / Paley-BGK. The two-sided "value" record (2026-06-21): the NEW provable lower bound
M >= sqrt(3) sqrt(n) (floor brick _AvFloor_MomentRatioLowerBound), and the DC-crossover symmetry
showing the sqrt(n log p) LOG FACTOR is blocked at the SAME deep depth r ~ ln p on BOTH the upper
and lower side. Plus the closing of the generic-chaining escape hatch. Honest: the value IS
sqrt(n log p) empirically; the log factor on both sides is the open deep-depth archimedean core. -->

# The Paley/BGK Value from Both Sides: a Lower Floor, and the DC-Crossover Symmetry

## 0. Target and verdict

`M = max_{b!=0} |eta_b|`, `eta_b = sum_{x in mu_n} e_p(bx)`, `mu_n` the `2^mu`-th roots in `F_p^*`,
`p ~ n^4`. The prize is `M <= C sqrt(n log(p/n))`. This note records the **two-sided** state after
attacking *both* bounds: a **new provable lower floor**, and the precise reason the **log factor**
remains open on **both** sides — they are blocked at the *same* deep depth.

Empirically `M / sqrt(n log(p/n)) ~ 1.04, 1.09, 1.18` at `n = 16, 32, 64` (climbing toward `sqrt 2`),
so the **value is `sqrt(n log p)`-scale** and every conjecture is right. What is *proven* is the
`sqrt(n)`-scale on both sides; the matching `log` factor is the open core.

## 1. NEW: a provable lower floor `M >= sqrt(3)·sqrt(n)`

The trivial Parseval floor is `M >= sqrt(n)` (`max >= avg`, `sum_{b!=0}|eta_b|^2 = pn - n^2`). We
improve it. The elementary **moment-ratio** inequality (for nonnegative `a_b = |eta_b|^2`)

> `M^2 = max_{b!=0} |eta_b|^2 >= (sum_{b!=0} |eta_b|^4) / (sum_{b!=0} |eta_b|^2) = A_2 / A_1`

(because `max(a)·sum(a) >= sum(a^2)`), combined with the exact moment identities
`A_1 = q·E_1 - n^2 = qn - n^2` and `A_2 = q·E_2 - n^4`, gives

> **`M^2 >= (q·E_2 - n^4) / (q·n - n^2)`.**

For `mu_n` (with `n = 2^mu`) the additive quadruple count is **`E_2 = 3n^2 - 3n` exactly**, and the
char-`p` wraparound excess `W_2 = E_2 - E_2^{char0} = 0` for all `p > n^4` (Stickelberger). Hence

> **`M >= sqrt((q(3n^2-3n) - n^4)/(qn - n^2)) -> sqrt(3)·sqrt(n)`** as `n -> infinity`.

Exact verification (`/tmp/bgk_floor_4thmoment.py`, no `eta` enumeration; `A_2/A_1` via the `O(n^2)`
sum-histogram for `E_2`):

| n | p | E_2 (=3n^2-3n) | W_2 | A_2/A_1 | M >= ... | /sqrt(n) |
|---|---|---|---|---|---|---|
| 16 | 65617 | 720 | 0 | 44.95 | 6.704 | 1.676 |
| 64 | 16777601 | 12096 | 0 | 188.99 | 13.747 | 1.718 |
| 256 | 4294968833 | 195840 | 0 | 765.00 | 27.659 | 1.729 |
| 1024 | 1099511630849 | 3142656 | 0 | 3069.0 | 55.399 | **1.731 = sqrt 3** |

**Formalized (axiom-clean, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`):**
`Frontier/_AvFloor_MomentRatioLowerBound.lean` —
- `sum_sq_le_sup'_mul_sum` (the pure `max·sum >= sum^2`),
- `fourthSum_le_sup'_sqSum` (`M^2·A_1 >= A_2`),
- `nonzero_moment` (`sum_{b!=0}|eta_b|^{2r} = q·rEnergy G r - n^{2r}`, off the substrate moment id),
- `energy_moment_floor` (`q·E_2 - n^4 <= M^2·(q·E_1 - n^2)`).

The unconditional `M >= sqrt(2)·sqrt(n)` follows from the diagonal quadruples alone (`E_2 >= 2n^2-n`);
the `sqrt 3` uses the exact `E_2`. This is the first "the value strictly exceeds the naive `sqrt n`"
result. It does **not** reach the `log` factor — by design (see Section 2).

## 2. The CRUX: the DC-crossover blocks the log factor on BOTH sides at the same depth

Both bounds reduce to the additive energy `E_r` at depth `r`:
- **Upper** `M <= C sqrt(n log p)` needs `E_r <= Wick_r = (2r-1)!! n^r` at `r ~ ln p` (i.e. the char-`p`
  excess `W_r <= slack`). This is the open conjecture.
- **Lower** `M >= c sqrt(n log p)` needs `A_r = q·E_r - n^{2r}` **large** at `r ~ ln p`.

The **only provable** energy control is `E_r >= Wick_r` (the Gaussian/Wick value is the minimum). Feed
it into the lower bound: the provable lower bound on `A_r` is `q·Wick_r - n^{2r}`, which is **positive
only while `q·Wick_r > n^{2r}`**, i.e. `(2r-1)!! > n^{r-4}`. At prize scale this **fails at a small
constant depth** `r_0 ~ 5`, whereas the `log` factor lives at `r ~ ln p ~ 55-83`:

| n | ln p | crossover r_0 (n^{2r} overtakes q·Wick_r) |
|---|---|---|
| 2^10 | 27.7 | 5 |
| 2^16 | 44.4 | 5 |
| 2^20 | 55.5 | 5 |
| 2^30 | 83.2 | 5 |

(`/tmp/dc_crossover.py`.) So the provable energy bound is **vacuous exactly where the log appears**.

> **Symmetry:** the upper log needs `E_r` not-too-big at `r ~ ln p` (`W_r <= slack`); the lower log
> needs `E_r` big-enough at `r ~ ln p`; and the provable bound `E_r >= Wick` only controls small `r`.
> The moment method — in **both** directions — is blocked at the identical DC/wraparound crossover.
> The `log` factor is a pure **deep-depth (`r ~ ln p`) archimedean** phenomenon.

This is *why* ~60 frameworks reduced: every moment/energy/`b`-summed tool is a small-`r` (or
`b`-averaged) object, and the prize lives at `r ~ ln p` in the phase.

## 3. The generic-chaining escape hatch is closed

The one sup-control method that controls a *max* via metric entropy (not orthogonal averaging) —
Dudley / Talagrand generic chaining — also reduces: the natural `L2` metric on `{eta_b}`,
`d(b1,b2)^2 = || psi_{b1} - psi_{b2} ||^2 = 2n - 2 Re(eta_{b1-b2})`, is itself a **phase-blind
Parseval quantity** (diameter `~ 2 sqrt n`). So Dudley's bound is `Theta(diam · sqrt(log N)) =
Theta(sqrt(n log N))` = the union/BGK scale, **not** `sqrt n`. Chaining reproduces the union bound;
it does not escape (verified against `{eta_b}`, `n = 8,16,32`). This removes the last non-orthogonal
sup-control hope and reinforces Section 2: the metric carrying the geometry is phase-blind.

## 4. Honest two-sided summary

| direction | proven (axiom-clean / exact) | open (the log factor) |
|---|---|---|
| upper | `M <= n^{1-o(1)}` (BGK) | `M <= C sqrt(n log p)` = `W_r <= slack` at `r ~ ln p` |
| lower | **`M >= sqrt(3)·sqrt(n)`** (new, this note) | `M >= c sqrt(n log p)` (matching Omega-result) |

The value is `sqrt(n log p)` (empirically `C_M -> sqrt 2`-ish). Connecting every proven brick yields
the tightest two-sided `sqrt n`-scale sandwich and the precise single open object on each side — but
**not** the log factor, which is blocked, symmetrically, at the deep-depth DC-crossover. No QED is
faked; the prize remains the open deep-depth archimedean core.

## 5. Follow-up: the connect-all conditional, the resonance reduction, and the sharper floor

**(5a) The whole prize = one inequality (`_B6ConnectAll.connect_all_prize`, axiom-clean).**
`M <= 2 sqrt(e) sqrt(n log p)` follows from **exactly one** open hypothesis, the **SaddleEnergyBound**
`sum_{b!=0} ||eta_b||^{2r} <= (p-1) E_r^char0` at `r ~ ln q` (equivalently `A_r <= Wick`). The
moment=energy spine, the char-0 Wick anchor (Lam-Leung, *proven* in-tree), and the optimization
last-mile are all machine-checked. Companion axiom-clean bricks: `_AvgMaxExponentGapBarrier` (every
`b`-summed/moment route is trapped at exponent `>= 1`, the floor `qE_k >= n^{2k}` *derived* for the
real periods), `_AvB1_WeilTransferVacuous` (per-Gauss-sum Weil forces energy floor `n^{4r} >> Wick`),
`_AvSD_StickelbergerOnsetVacuous` (onset `r_0 ~ p^{1/phi(n)} ~ 4-5 << saddle r* ~ ln q`).

**(5b) The resonance / concentration LOWER-bound construction definitively reduces (no log).** Both
natural routes cap at bounded`*sqrt n`:
- *Dirichlet / pigeonhole* — vacuous: concentrating all `n` dilates `{b x mod p}` needs `K = n^{4/n} > 4`,
  but `K <= 2.0` at `n=16` and `-> 1` (at `beta=4`, `p = n^4` is too small for simultaneous approximation).
  The concentration at the worst `b` (empty arc `> 50%` of the circle at moderate `n`) is *statistical*,
  not constructible; it weakens as `M/n = sqrt(log p / n) -> 0`.
- *Montgomery-Soundararajan resonator* (`_AvFloor_ResonatorRatioLowerBound`, axiom-clean) — equals the
  moment-ratio in disguise: `resonator_one_*` show the `r=1` resonator on `S = G` gives inner sum `= eta_b`,
  weight `||eta_b||^2`, collapsing to the `sqrt 3` floor; the optimal degree-`r` gain is `A_r/A_{r-1} =
  (2r-1)n`, capped by the same DC-crossover.

So the lower `log` is the matching open Omega-result (same far-tail control as the upper bound).

**(5c) Sharper floor `M >= sqrt(5) sqrt(n)`** (`_AvFloor_SqrtFiveMomentRatio`, axiom-clean): the
moment *ratio* `M^2 >= A_3/A_2 = (q E_3 - n^6)/(q E_2 - n^4) -> 5n`, via the new weighted engine
`weighted_sum_le_sup'_mul_sum` (`h = ||eta||^2`, `g = ||eta||^4`) and the exact char-0 energies
`E_3 = 15 n^3 - 45 n^2 + 40 n`, `E_2 = 3 n^2 - 3 n` (`W_2 = W_3 = 0` for all `p > n^4`). Supersedes the
`sqrt 3` floor of Section 1; the ratio climbs (`2.09, 2.16, 2.39, 2.52, ...`) but caps at bounded`*sqrt n`.

**(5d) Method-space is closed.** Two further mining rounds (170 + 50 user-provided papers, mined for
*methods* not theorems, the ~22 already-reduced technique families filtered out): **0** genuinely-new
non-reducing methods promoted. Every technique producing a bound on a `b`-summed / moment / energy /
spectral object is phase-blind by `Sum_b eta_b^a conj(eta_b)^c = q * (real lattice count)`, hence capped
at `n^{1-o(1)}` (upper) and `sqrt n` (lower). The two structural escape-hopes are *theorems about why
they fail*: multiplicative chaos's better-than-`sqrt` is the *average* not the worst-case max (opposite
side of `sqrt n`); big monodromy is *abelian* (Kummer/Gauss-sum), pinning the average not the sup. The
prize stands as the single SaddleEnergyBound at `r ~ ln q` — the 25-year Paley/BGK wall at `beta = 4`.
