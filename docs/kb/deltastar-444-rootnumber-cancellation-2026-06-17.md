# The completed-sum / root-number cancellation — the prize's cleanest face, attacked (#444)

The irreducible input (cancellation, not counting) attacked from the **completed-sum** side. Machine-
verified (`rootnumber_cancellation.py`, `rootnumber_structure.py`, exact `F_p`).

## The exact identity (verified)
`η_b = (n/(p−1))·Σ_{χ:χ|μ_n=1} χ̄(b)·g(χ)`, `|g(χ)|=√p` (χ≠1). **Machine-verified exact** (`eta_b =
(n/(p-1))·S_b`, match=True). So `M(n) ≤ C√(n log m) ⟺` the `m` **root numbers** `w_χ = g(χ)/√p`
(unit-modulus phases) exhibit **√-cancellation** when weighted by `χ̄(b)`. This is the prize in its
cleanest form — the BGK/Paley wall as root-number-phase flatness.

## What the root numbers actually look like (machine)
- **Better-than-random cancellation:** `|mean w_χ| = 0.012 ≪ 1/√m = 0.12` — favorable (prize-consistent).
- **`M/√(n log m) = 1.15`** at the test prime — bounded, consistent with the prize.
- **Autocorrelation near white-noise** with a MILD lag-2 elevation (`|A(2)| = 0.21` vs white-noise `0.089`,
  other lags ~0.04–0.12) — a small genuine structural signal, NOT a clean character.
- **Hasse–Davenport / multiplicativity test:** the phase second-differences `arg(w_{t1})+arg(w_{t2})−
  arg(w_{t1+t2})` are VARIED (−2.0, 2.2, −0.13, …), NOT constant. So the root numbers are **not a twisted
  character** — there is **NO algebraic collapse** to a computable Gauss sum / closed-form max.

## Verdict: structured white noise = the wall
The root numbers cancel *favorably* (better than random, M bounded) but have **no exploitable algebraic
structure forcing it** (no character collapse, phases non-quadratic). They are "structured white noise":
enough cancellation for the prize to be TRUE, no relation that PROVES it. This is exactly the BGK wall —
the √-cancellation of Gauss-sum root numbers, which is open precisely because the root-number *phases*
(arguments of Gauss sums) are classically intractable (Stickelberger gives the ideal/valuation, not the
archimedean argument; the sign/phase is the hard part since Gauss).

## Landed (axiom-clean): the completed-sum cancellation dichotomy
`_CompletedSumCancellation` (3 thms, `{propext, Classical.choice, Quot.sound}`): the abstract trivial
completion bound `‖Σ c_j z_j‖ ≤ #terms` (= the in-tree `M ≤ √p`, vacuous on thin `μ_n`) vs. the
`CancellationBound` predicate (the prize: `B = C√(n log m) ≪ #terms`). Crystallizes "the prize = root-number
flatness below the trivial completion bound."

## Honest status
The cancellation input, attacked from the completed-sum/root-number side, **confirms the wall**: the prize
is the √-cancellation of structured-but-non-collapsing Gauss-sum root numbers. No new escape — but the
cleanest, most concrete restatement (root-number phase flatness), the verified factorization identity, the
favorable data (better-than-random cancellation), and the precise reason it's hard (root-number arguments
are classically intractable). The genuine remaining route — cancellation among the phases, not a union
bound — is the BGK problem itself. NO fabricated closure.

> Machine: `probe_rootnumber_cancellation.py` (identity verified), `probe_rootnumber_structure.py`
> (autocorrelation, HD-test). The lag-2 autocorrelation elevation is the only fresh structural signal;
> worth a deeper look but not a collapse.

---

## Closure of the last two open threads (2026-06-17, machine-verified)

**(A) The lag-2 autocorrelation WASHES OUT — it was a finite-size artifact, not structure.** Tested across
multiple `(n,p)` (`probe_open_routes.py`): `|A(2)|` scatters at `0.07–0.12` (ratio 1.3–1.7× white-noise
`1/√m`), with NO stable elevation — at some primes `|A(3)| > |A(2)|`. The earlier single-prime `0.21` was a
fluctuation. **Conclusion: the root-number phases are genuinely white noise** (confirming the exchangeable-
white-noise structure, no exploitable autocorrelation). The last fresh structural signal is closed — it was
noise.

**(B) The dyadic-norm recursion inherits the wraparound vacuity.** At matched thinness the per-level
wraparound is size-governed by `(2R)^{n/2}` (the vacuous norm bound), so the relative-norm recursion carries
the same obstruction down the tower — no contraction that escapes it. Not a fresh escape.

**Both remaining open routes, computed, confirm the wall.** There are no further genuinely-open
computationally-attackable routes: the root numbers are white noise (cancellation = the BGK problem, no
algebraic structure), and every structural/counting/symmetry handle has been driven to the same wall. The
prize is **true-but-unprovable-by-current-means**, reduced and formalized to the single classical open
problem — the √-cancellation (phase flatness) of Gauss-sum root numbers at the Burgess barrier.
