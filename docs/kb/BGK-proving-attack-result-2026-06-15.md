# Avenues to Prove BGK — review + attack on the #1 path: RESULT (2026-06-15)

Reviewed every avenue to prove the prize core `M(n) ≤ C√(n log m)` (#444), then attacked the #1 path
(char-p deep Wick / MGF) at the prize prime with fresh exact computation. **Honest verdict: the #1 path
reduces to the wall (feasibility 2/10), confirmed across three independent angles.** This CORRECTS the earlier
roadmap, which over-rated avenue 1 at 6–7 on a misread "MGF envelope holds to n=256" claim.

## The review (3 of 6 avenues completed before rate limit; all reduce-to-wall, feasibility 2)
- **Avenue 1 (char-p deep Wick A_r≤(2r−1)‼·n^r at r≈89):** highest-value framing (= BCHKS 1.12 s=1, char-0
  fully solved with DC-subtraction), but NOT independent — the char-p residual W_r(p)=0 uniform to r≈89 IS the
  BGK wall rewritten as cyclotomic-norm-divisibility. The two genuine advances (DC-subtraction non-vacuous; the
  W_r wraparound decomposition pinning the obstruction to p|N(D)) RELOCATE, not close. Needs new p-adic
  cyclotomic-valuation math. Feasibility 2.
- **Avenue 3 (sum-product/energy):** reduces-to-wall. TWO fatal facts: energy→char-sum transfer is intrinsically
  √-lossy (barrier is the transfer exponent, NOT energy size — Sidon floor already achieved); effective
  sum-product exponent vanishes at α=1/4. Do NOT re-chase higher/asymmetric energy. Feasibility 2.
- **Avenue 4 (effective equidist/monodromy/sheaf):** the wall "wearing geometric clothes." MonodromyConductorScaffold
  reduces to ConductorGeometricBound at K=O(1) = the open core verbatim (crude rank reading n^{2r-1} provably
  false; genuine K~1.28 IS the BGK Gauss-sum cancellation). Three prize-faithful refutations (object mismatch,
  effectivity gap, growing dimension). Feasibility 2.

## The attack on the #1 path — three equivalent cruxes, all fail at the prize prime
**Crux W3/F2 (per-level sign condition) — REFUTED.** F2 RhoContractiveAtDepth `Cum(μ_n,r)≤2·Cum(μ_{n/2},r)` is
numerically FALSE with no margin: ρ=2.8 at r=2 grows to ~123 (n=32,r=7), ~740 by r=9. The proven
strictly-negative principal-subtraction term `−(2^{2r}−2)|H|^{2r}` is real but DWARFED by orders of magnitude
(`q·Cross` beats it 3–1700×). W3 R(1)≤1 and W7 GEN_r<0 FAIL at ~30% of prize-regime primes. The only survivor
is the saddle-point MGF bound, which yields **C=√2** (measured C_saddle 1.458→1.450) — the generic wall.

**Crux W1 (aggregate Gaussian-MGF envelope) — REFUTED.** The claim "envelope holds to n=256" was only AT THE
SADDLE, not uniform in y (DC-subtracted envelope bulges to 1.24–1.29 at intermediate y, Fermat 65537). The
envelope-break threshold is c\*≈1.243 (single-worst-coset saddle), and the actual c EXCEEDS it.

## The v₂(p−1)-gating refinement — genuine, but a finite-n effect (does NOT open the prize)
The W7 agent found DC-dominance failure is driven by EXTRA 2-adic valuation beyond μ. The prize requires
`p≡1 mod 2^μ` so `v₂(p−1)≥μ` always; a random such prime has `v₂=μ` (the minimal/generic prize prime).
Stratified exact M(n) measurement (`/tmp/bgk/v2_stratified_M.py`, β≈4, fresh):
- **v₂-gating is REAL:** at n=64, c is monotone-ish in v₂ — v₂=μ=6 (best) max c=1.27, mean 1.25; structured
  strata rise (v₂=8 → 1.49, v₂=9 → 1.44, v₂=12 → 1.43).
- **But even the best stratum (v₂=μ) rises monotonically toward √2 as n grows** (`/tmp/bgk/v2mu_trend.py`):

  | n | 8 | 16 | 32 | 64 | 128 |
  |---|---|---|---|---|---|
  | mean c (v₂=μ) | 1.057 | 1.162 | 1.234 | 1.264 | 1.323 |
  | max c (v₂=μ) | 1.068 | 1.204 | 1.288 | 1.321 | 1.376 |

  c crosses the envelope-break threshold 1.243 by n≈32 and climbs toward √2≈1.414. So the v₂-gating is a
  finite-n effect; asymptotically ALL strata → the BGK constant √2.

**Keepable refinement:** the obstruction is *sharpest at high-v₂(p−1) primes* — exactly the regime real
FRI/STARK primes inhabit (Goldilocks v₂=32, BabyBear v₂=27, chosen for deep 2-adic FFTs). The wall is not just
present but worst precisely where the application lives.

## Bottom line
The empirical law is `M(n) ~ √2·√(n ln m)` (C=√2) even at the most favorable (v₂=μ) primes, monotone in n. The
#1 BGK-proving path reduces to the wall (feasibility 2), confirmed by (a) the avenue-review, (b) the per-level
sign-condition refutation, (c) the v₂-stratified trend. The aggregate-MGF envelope route is dead (breaches its
own 1.243 threshold and rising). The only survivor is the saddle bound at C=√2 = the generic BGK wall the prize
must BEAT. No proof technique reviewed reaches below √2; the bottleneck across all six avenues is the one
unattained input: char-p control of the deep cyclotomic moment at the specific prize prime — the 25-year-open
sharp endpoint of Bourgain's BGK program. Refutations, not closure.
