#!/usr/bin/env python3
"""
probe_smooth_listsize_energy.py  (#389 — proximity prize, list-decoding side)

QUESTION PROBED
  Does the multiplicative structure of a smooth domain mu_n = <g> in F_q (the prize's
  evaluation set for plain Reed-Solomon RS[mu_n, k]) HELP or HURT the list size in the
  beyond-Johnson window  delta in (1 - sqrt(rho), 1 - rho),  rho = k/n  — versus a generic
  evaluation set of the same size?

  The list at agreement threshold t is  max over words w of  #{ deg-<k polys p : p agrees
  with w on >= t coords of mu_n }.  For k=2 this is the count of distinct lines through >= t
  of the n points (x_i, w_i); for general k it is interpolants of k-subsets, deduped.

WHY IT MATTERS
  The prize reduces (via I(delta) <= ell/(delta'-delta), ell = close-codeword curve degree)
  to bounding the list size of plain RS on mu_n in the window. Combinatorial / moment methods
  give only Johnson; the open question is whether mu_n's structure keeps the list poly (prize
  TRUE) or blows it up (prize FALSE / delta* pinned below capacity).

KEY REPRODUCIBLE FINDING (field sweep, n=8, k=2, t=3, in the window k<t<sqrt(nk)=4)
    q      E/n^2   Sidon(q>2^n)   maxlist mu_n    maxlist generic
    17     4.12    no             7               7
    41     3.12    no             7               6
    73-113 2.62    no             5               5
    257+   2.62    yes            4               4     (q=1153: mu_n=4, generic=3)
  => The list size TRACKS the additive energy E(mu_n) and DROPS to near-generic as the field
     grows and E/n^2 reaches the Sidon floor 3 - 3/n = 2.625. The small-field "mu_n hurts"
     (7 vs 6) is a HIGH-ENERGY artifact, not the prize regime. In the prize regime (large
     field, mu_n ~ Sidon) the list is SMALL (4 vs capacity 8), comparable to generic.

HONEST CAVEATS (do not overclaim)
  * This supports the prize being plausibly TRUE for large-field plain RS, but the energy->list
    map is provably sqrt-LOSSY (issue389-additive-energy-crux): even E=t^2 gives list n^{3/2},
    sub-Johnson not capacity. So energy is NOT a tight prize lever; this is confirmatory, not a
    proof technique.
  * The growth-with-n probe (rho=1/4, n=8,12,16) is INCONCLUSIVE: random word sampling
    under-estimates the worst-case list for larger n (word space q^n explodes), so the small
    observed values (2-5) are a sampling floor, NOT a proven asymptotic bound. Use exhaustive
    adversarial-word search (or a structured worst-word constructor) before drawing asymptotic
    conclusions.

USAGE
  python3 probe_smooth_listsize_energy.py        # runs the field sweep (n=8,k=2)
"""
import itertools, math, random
from collections import Counter


def find_subgroup(q, n):
    """Return sorted mu_n = order-n multiplicative subgroup of F_q (q prime, n | q-1)."""
    if (q - 1) % n != 0:
        return None
    for prg in range(2, q):
        order, x = 1, prg % q
        while x != 1:
            x = (x * prg) % q
            order += 1
        if order == q - 1:  # primitive root found
            h = pow(prg, (q - 1) // n, q)
            S, v = set(), 1
            for _ in range(n):
                S.add(v)
                v = (v * h) % q
            return sorted(S)
    return None


def add_energy(S, q):
    """Additive energy E(S) = #{(a,b,c,d) in S^4 : a+b = c+d}."""
    c = Counter()
    for a in S:
        for b in S:
            c[(a + b) % q] += 1
    return sum(v * v for v in c.values())


def line_through(x1, y1, x2, y2, q):
    m = ((y2 - y1) * pow((x2 - x1) % q, q - 2, q)) % q
    return (m, (y1 - m * x1) % q)


def max_list_lines(q, D, t, trials, seed=7):
    """k=2: max over sampled words of #{distinct lines hitting >= t of (x_i, w_i)}."""
    n = len(D)
    random.seed(seed)
    best = 0
    for _ in range(trials):
        m0, b0 = random.randrange(q), random.randrange(q)
        w = [(m0 * x + b0) % q for x in D]
        for _ in range(random.randint(1, n)):
            w[random.randrange(n)] = random.randrange(q)
        rich = set()
        for i in range(n):
            for j in range(i + 1, n):
                L = line_through(D[i], w[i], D[j], w[j], q)
                if L in rich:
                    continue
                if sum(1 for a in range(n) if (L[0] * D[a] + L[1]) % q == w[a]) >= t:
                    rich.add(L)
        best = max(best, len(rich))
    return best


def main():
    n, t, TR = 8, 3, 200000  # k=2 lines; window k=2 < t=3 < sqrt(nk)=4
    print(f"n={n} k=2 t={t}  Johnson-agree={math.sqrt(2 * n):.2f}  Sidon E/n^2 -> {(3 * n * n - 3 * n) / n**2:.2f}")
    print(f"{'q':>6} {'E/n^2':>7} {'Sidon?':>7} {'maxlist mu_n':>13} {'generic':>8}")
    for q in [17, 41, 73, 89, 97, 113, 257, 401, 1153]:
        if (q - 1) % n != 0:
            continue
        D = find_subgroup(q, n)
        E = add_energy(D, q)
        ml = max_list_lines(q, D, t, TR)
        mlg = max_list_lines(q, list(range(1, n + 1)), t, TR)
        print(f"{q:>6} {E / n**2:>7.2f} {str(q > 2**n):>7} {ml:>13} {mlg:>8}")


if __name__ == "__main__":
    main()
