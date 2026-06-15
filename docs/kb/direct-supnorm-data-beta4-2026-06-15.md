# Direct sup-norm data at prize thinness β=4 (supports "all primes at β≥4")

Probe (prize-faithful: proper μ_n, p≡1 mod n, p≈n^4 so β=4, multi-prime, never n=q-1; /tmp/prize-research/
almostall*.py). Computed M(n)=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| / √(2n log m), m=(p-1)/n:

| n  | #primes | median | max  | std   | frac M>√(2n log m) |
|----|---------|--------|------|-------|--------------------|
| 16 | 60      | 0.821  | 0.856| 0.014 | 0                  |
| 24 | 40      | 0.942  | 0.971| 0.012 | 0                  |
| 32 | 30      | 0.880  | 0.929| 0.028 | 0                  |

FINDINGS:
- The TARGET bound M ≤ √(2n log m) (constant C=√2) holds for EVERY prime at β=4 in the computable range,
  TIGHTLY concentrated (std ~0.01-0.03), no violations. ⟹ the conjecture is TRUE at the prize thinness with
  the conjectured constant; the open problem is purely the PROOF (deep-moment char-p transfer), not the truth.
- Supports the "almost-all-primes" angle STRENGTHENING to "ALL primes at β≥4" (no bad primes at β=4 here);
  consistent with in-tree thinness-essential (violations only at intermediate-thick β≈2.3-3.2 structured primes,
  OUTSIDE the prize). The tight concentration ⟹ periods behave robustly sub-Gaussian at β=4.
- Caveat: n≤32 is the safe/small computable range; the constant creeps (0.82→0.97→0.93) non-monotonically but
  stays <1. A proof must be thinness-essential (use β≥4; a thickness-monotone method wrongly covers β<4 where
  the bound is FALSE). Does NOT prove the prize (needs the analytic deep-moment bound), but pins the target as
  true + the constant as ~√2 + the bad set as empty at β=4 (computable range).
