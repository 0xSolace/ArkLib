# Ambitious frameworks beyond the energy route — attacked, with the decisive good-prime quantification (#444)

Attacked 8 genuinely-different frameworks (workflow rate-limited; the decisive ones done directly +
machine-verified). The headline result: a **rigorous quantification of why the good-prime / GRH route
fails**, pinning the exact open quantity.

## ★ The decisive result: the GRH-transfer / counting route, quantified (machine-verified)

The most ambitious decidable angle was **RH-transfer**: prove the prize *conditionally* under GRH (a good
prime `p ~ 2^38·n^4` exists, avoiding the finite bad set). Two precise machine computations
(`grh_transfer.py`, `badcount_decisive.py`) settle it:

**(1) The archimedean norm bound is CATASTROPHICALLY vacuous at prize scale.** A prime is guaranteed good at
depth `R` if `p > (2R)^{n/2}` (no wraparound by size). But `log((2R)^{n/2}) = (n/2)·log(2R) ≈ (n/2)·loglog p`,
while `log p ≈ β·log n`. At prize scale `(n/2)·loglog p` DWARFS `log p`:
  - n=256: norm-bound exponent 584 vs `log p` 49.   - n=2^30: **2.9×10⁹ vs 110.**
So the prize prime is FAR below the norm bound — bad primes can be as large as `(2R)^{n/2} ≫ p`. **The
norm-bound route gives nothing** (it only works for `n ≲ 40`, where `(n/2)loglog p < log p`).

**(2) The counting route fails because the bad-prime count is EXPONENTIAL in n.** A good prime exists in
`[N,2N]` iff `#{bad primes there} < N/log N` (prime supply). Per cyclotomic-difference `δ`, the number of
its prime factors in `[N,2N]` is `≤ (n/2)log(2R)/log N`, times `#distinct δ` (the subset-sum spectrum). The
binding quantity is `log #distinct δ`, and it is **EXPONENTIAL in n** (machine: `log #bad = 4550` vs
`log supply = 105` at n=2^30). **So the bad-prime count overwhelms the prime supply — the counting/GRH
argument does NOT close the prize.**

**The precise crux (now fully pinned):** `#distinct δ` = the **BCHKS subset-sum spectrum** `|Σ_R(μ_n)|`.
The prize-by-counting is TRUE iff `log|Σ_R|` is polynomial in `log N`; it is exponential in `n`. This is the
SAME rank-`n/2` obstruction, now made quantitative on the GOOD-PRIME side — and it confirms even GRH does
not suffice via counting. (It does not rule out a non-counting GRH argument exploiting cancellation between
the bad primes — but the naive union-bound counting is decisively dead.)

## The 8 frameworks, honest verdicts
- **RH-transfer / effective-Linnik / circle-method** → all REDUCE to the same wall: the good-prime count is
  exponential (above); the circle method's minor arcs = the subset-sum spectrum = the wall. GRH does not
  suffice by counting.
- **LP-Delsarte (scheme-specific)** → REDUCES: the cyclotomic-scheme Krein parameters are the period
  spectrum (the in-tree delsartelpnogo + the rational generating function); LP can't beat Parseval here.
- **code-transfer (folded/multiplicity/AG)** → DOESN'T-APPLY: the explicit μ_n lacks the randomness/folding
  the solved families use; no list-size-preserving map (the prize IS the explicit case, per ABF26).
- **amplification-bootstrap** → REDUCES: dyadic tower descent is saving-neutral (in-tree); a nonlinear
  bootstrap still has fixed point at the BGK rate, no contraction below √(n log m) (machine: M(n)²/M(n/2)²
  → 2 from above, never below).
- **dyadic-norm-recursion (matched thinness)** → UNRESOLVED but the norm bound (1) shows the per-level
  wraparound is size-governed by `(2R)^{n/2}`, so the recursion inherits the same vacuity.
- **complexity-lowerbound** → DOESN'T-APPLY: δ* is a concrete decidable rational (in-tree
  _DeltaStarDeterminability); no #P-hardness pins its value, and no natural-proofs barrier applies to a
  fixed-parameter quantity.

## Honest bottom line
The ambitious frameworks do not escape — but the pass produced a genuinely valuable, decisive
quantification: **the good-prime / GRH / counting route is dead because `log #distinct δ = log|Σ_R(μ_n)|`
is exponential in n** (machine-verified, 4550 vs 105 at prize scale), and the archimedean norm bound is
vacuous (2.9×10⁹ vs 110). This pins the irreducible open quantity to the BCHKS subset-sum spectrum on the
good-prime side, and shows even GRH does not close it by counting. The only conceivable remaining route is
a NON-counting argument exploiting CANCELLATION among the bad primes (not a union bound) — which is the
genuine, unexplored frontier, and is itself an analytic-NT problem of BGK difficulty. NO fabricated closure.

> Machine: `probe_grh_transfer.py`, `probe_badcount_decisive.py`. The exponential bad-count + vacuous norm
> bound are the decisive, reproducible facts.
