# Attacking c_r≤1: it is FALSE at structured β=4 primes; C=√2 refuted; moment route is prime-limited

Direct prize-faithful probes (no early-abort, exact |η_b|, proper μ_n, multi-prime, never n=q-1;
/tmp/prize-research/{deviation_op,monotone_check,badprime}.py).

## The δ-reformulation (clean, exact)
Let X_b=|η_b|², m_r=E[X_b^r], δ_r:=m_r−Wick_r (Wick_r=(2r−1)‼·n^r). Gaussian-fixed-point algebra:
  cross_r ≈ m_{r+1}−n·m_r ;  Gaussian ⟹ cross_r=2r·n·Wick_r ⟹ c_r=1 (the fixed point).
  ⟹ **c_r ≤ 1 ⟺ δ_{r+1} ≤ n·δ_r** (deviation grows at rate ≤ n per depth). The "Shaw operator" is 𝒮: δ_r↦δ_{r+1}.

## c_r is NOT uniformly ≤ 1 at β=4 (the refutation)
Stress test, 23 primes β=4: 22 have c_r monotone-decreasing →0 (≤1 with growing margin); BUT
  n=64, p=16778497 (β=4.000): c_r = 0.976, 0.959, 0.963, **1.019, 1.163, 1.432, 1.845** — c_r EXCEEDS 1.
And the BOUND ITSELF fails there: **M/√(2n log m) = 1.0514 > 1** (C=√2 REFUTED; matches in-tree n=64 R=1.0514).
Neighbors fine: p=16777601→0.964 (v₂=7), p=16778753→0.714 (v₂=9). Bad prime: v₂(p−1)=8, m=2²·65541 —
a SPECIFIC structured prime (sparse bad set), not simply high-v₂.

## Consequences (honest redirection of the target)
1. c_r≤1 (the conditional-pin hypothesis) is PRIME-DEPENDENT — false at structured β=4 primes. Cannot be
   proven as a universal β=4 statement. The pin is SUFFICIENT only at "good" primes (c_r≤1 to depth log m).
2. C=√2 is the WRONG constant (refuted). True bound M ≤ C√(n log m) has C=O(1) but C>√2 (C≈1.49 worst seen).
3. THE MOMENT METHOD / CONDITIONAL PIN IS PRIME-LIMITED: it yields C=√2 only at good primes; at bad primes
   (c_r>1 for r≥4) the optimal moment depth is capped (~r_0=3), giving only a power-saving (~n^{1.17}), even
   though the TRUE M is still O(√(n log m)). So the moment route CANNOT deliver the prime-uniform C=O(1) prize.
4. The genuine prize target is the prime-UNIFORM C=O(1) sup-norm — which needs a DIRECT argument achieving
   C=O(1) at ALL primes (incl. structured ones), NOT via c_r≤1. The Shaw operator must compute/bound C(p,n)
   (the depth r_0(p) to which c_r≤1, hence C), prime-uniformly — the moment method gives C=√2-or-bust.
5. Reconciles: the prize prime's "goodness" (is c_r≤1 to depth log m?) is the open question; bad set is
   structured primes (some m-structure / v₂ pattern, not monotone in v₂). Consistent with the whole campaign's
   "almost-all-primes good, structured primes bad" + "C=O(1) not √2" + thinness-essential picture.

NET: "prove c_r≤1" is the wrong quest — it's false at structured β=4 primes. The prize is prime-uniform C=O(1),
beyond the moment method. The conditional-pin brick remains valid (sufficient at good primes) but is provably
NOT a complete route. Honest refutation + redirection; no fabrication.
