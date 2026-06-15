# The proof of top1≤C·n·log m SPLITS: moment route fails at bad primes, needs a direct anomalous-period bound

## The decisive structural fact (from the dual-track agents + analysis)
At the BAD prime p=16778497 (n=64): c_r GROWS with depth (c_4=1.019, c_5=1.163, c_6=1.432, c_7=1.845, climbing)
— so the moment route (c_r≤K for fixed K) FAILS (no finite K survives to depth log m). YET top1=max|η_b|²
≈2.21·n·log m is BOUNDED (M/√(2n log m)=1.0514). So the moment method is LOSSY at bad primes but the bound HOLDS.
⟹ THE PROOF SPLITS CLEANLY:
- GOOD primes (δ_r<0 ∀r ≤ log m; no spurious weight-≤2r relation): the conditional pin / moment route gives
  M≤√(2n log m), C=√2. [The remaining open part here = the deep-tail CLT at good primes = no spurious relation
  to depth log m, equivalently the norm condition p∤Norm(any weight-≤2log m relation).]
- BAD primes (p|Norm(short relation), e.g. weight-6 z^0+z^1+z^7−z^9−z^10−z^61, Norm=2^3·p): moment route fails
  (c_r→∞); need a DIRECT bound on the single ANOMALOUS period |η_{b*}|² where the spurious relation concentrates.
  worst-case top1 PLATEAUS ~2.2 n log m (worst M/√(2n log m)~1.05, n=16..256), so the anomalous period stays
  O(n log m) — but a PROOF of that direct bound is open.

## Consequence for the proof attack
The right architecture is a GOOD/BAD SPLIT, not a single moment argument:
1. GOOD primes: discharge the conditional pin (deep-tail CLT / no-spurious-relation to depth log m) — the wall,
   but now restricted to primes with NO short spurious relation (a cleaner, norm-theoretic condition).
2. BAD primes: a DIRECT bound on the anomalous period associated with the explicit spurious relation R
   (|η_{b*}|²≤C n log m), exploiting that R is a SINGLE weight-6 (in general weight-2r_0) relation with
   Norm=O(1)·p — so b* is a SPECIFIC algebraic direction, boundable by Weil/completion on the curve cut out by R.
C=O(1) UNIFORM holds empirically (worst-C plateaus ~1.5/top1~2.2 n log m to n=256); the proof is the two-part
split. This is the cleanest decomposition: the moment method is provably inadequate at bad primes (c_r→∞), so a
direct period bound is NECESSARY there — focusing the bad-prime work on a single explicit resonant direction.

## Open obligations (both)
(a) GOOD-prime deep-tail CLT (= p∤Norm(weight-≤2log m relation) ⟹ A_r≤Wick to depth log m): the wall, restricted.
(b) BAD-prime direct anomalous-period bound (|η_{b*}|²≤C n log m for the b* of the spurious relation R): new,
    concrete, possibly Weil-tractable (R is a single low-weight algebraic relation, not a thin-subgroup sum).
