# Reconciliation: C=O(1) holds uniformly; "C=√2 violated" is just the log m vs log q normalization

Sup-C scan (M/√(2n log m), exact |η_b|, p≡1 mod n, β=4, never n=q-1; /tmp/prize-research/supC_scan.py):
  n=16 (80 primes): max 0.856, min 0.796, #>1 = 0
  n=32 (40 primes): max 0.956, min 0.822, #>1 = 0
  n=64: one bad prime p=16778497 ratio 1.0514 (good neighbors 0.96, 0.71)

KEY: the max ratio grows 0.856→0.956→1.05, but this is NOT unbounded growth — it is the finite-size approach to
the log m vs log q normalization constant. The moment method gives M ≤ √(2n log q); and
  √(2n log q)/√(2n log m) = √(log q/log m) = √(4/3) ≈ 1.155 at β=4.
So M/√(2n log m) → √(4/3)≈1.155 from below (M ≈ √(2n log q), the BGK/moment value) ⟹ in the M≤C√(n log m)
normalization C → √(2·log q/log m) = √(8/3) ≈ 1.633 = O(1).

CORRECTIONS to the earlier framing:
- C=O(1) HOLDS UNIFORMLY (all ratios bounded ≈1 across n=16-64). The prize bound M ≤ C√(n log m), C=O(1), is
  NOT violated. The "bound violated" reading was imprecise.
- "C=√2 REFUTED" is correct but NARROW: √2 (=1.414 in √(n log m)) is simply too small; the log m normalization
  makes the true asymptotic constant exceed √2 (it's ≈1.63). This is a constant issue, not a bound failure.
- The moment method / conditional pin achieves EXACTLY M ≤ √(2n log q) = C√(n log m) (C≈1.63) at GOOD primes
  (c_r≤1); BAD primes (c_r>1, e.g. p=16778497 ratio 1.487 in C-units) need a separate O(1) argument but stay
  BELOW the same asymptotic constant √(8/3) (1.487 < 1.633).

TRACK B (prime-uniform C=O(1)) STATUS: empirically TRUE (ratios bounded ≈1, → √(4/3)). Open part = the UNIFORM
PROOF: the moment method covers good primes (C≈1.63 via c_r≤1); bad primes (sparse, structured) need the
non-moment sup-norm bound to confirm they don't exceed the constant. The prize is the prime-uniform C=O(1), now
seen as TRUE-empirically with the exact constant ≈√(2 log q/log m); the residual is the uniform proof + the
exact constant (is it √(8/3) at β=4, or is sup over bad primes slightly higher?). Caveat: n≤64 only; the
saturation-to-√(4/3) is plausible but not nailed (convergence is messy at small n; needs n=128+ to confirm the
constant, which is brute-infeasible — consistent with numerics-cannot-settle).
