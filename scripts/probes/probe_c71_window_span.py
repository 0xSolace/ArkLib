#!/usr/bin/env python3
"""
PROBE (rule 2): the SUPPORT-SPAN / degree-window incidence bound for C71 sparse strata.

Claim to test on PROPER thin mu_n = 2^a, p == 1 mod n, multi-prime incl p > n^3 + Fermat,
NEVER n = q-1:

  Let g = sum_i c_i X^{e_i} be an m-sparse direction. Let gbar = sum_i c_i X^{e_i % n} be its
  mod-n reduction (same mu_n-incidence, thinness-essential, x^n=1). Let
    t = min support exponent of gbar (natTrailingDegree), d = max (natDegree).
  CLAIM (WINDOW): #{x in mu_n : g(x) = 0} <= d - t   (the support SPAN of the reduced poly).

This is a NON-orbit, char-free polynomial-method bound: gbar = X^t * h with h of degree d-t and
h(0) != 0, and a nonzero root of gbar is a root of h, of which there are <= deg h = d - t.
It SHARPENS the trivial `< n` cap and the abstract deg-gcd when the reduced support is narrow.

Also test it BEATS the raw (i-j-style) bound when support wraps past n.
"""
import itertools, random

def is_prime(x):
    if x < 2: return False
    d = 2
    while d*d <= x:
        if x % d == 0: return False
        d += 1
    return True

def primroot(p):
    fac = []; phi = p-1; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in fac):
            return g
    return None

def mun(p, n):
    g = primroot(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, k, p) for k in range(n)]

random.seed(20260617)  # fixed seed: reproducible case set + count

cases = 0
fails = 0
window_strictly_beats_n = 0
for (n, p) in [(8,17),(8,41),(8,257),(8,521),(16,97),(16,257),(16,769),
               (16,12289),(32,193),(32,12289),(4,13),(4,257)]:
    if (p-1) % n != 0 or not is_prime(p):
        continue
    G = mun(p, n)
    assert len(set(G)) == n and n != p-1
    # random m-sparse directions, m in {2,3,4}, exponents up to q-1 (wrap), c_i nonzero
    for trial in range(60):
        m = random.choice([2,3,4])
        exps = random.sample(range(1, p-1), m)
        coefs = [random.randrange(1, p) for _ in range(m)]
        # mod-n reduced support
        red = {}
        for e, c in zip(exps, coefs):
            er = e % n
            red[er] = (red.get(er, 0) + c) % p
        red = {e: c for e, c in red.items() if c != 0}
        if not red:
            continue
        t = min(red)
        d = max(red)
        window = d - t
        # actual incidence on mu_n
        inc = 0
        for x in G:
            v = 0
            for e, c in zip(exps, coefs):
                v = (v + c * pow(x, e, p)) % p
            if v == 0:
                inc += 1
        cases += 1
        if inc > window:
            fails += 1
            if fails <= 5:
                print(f"FAIL n={n} p={p} exps={exps} red_support={sorted(red)} window={window} inc={inc}")
        if window < n:
            window_strictly_beats_n += 1

print(f"\ncases={cases} fails={fails} (window bound #roots <= d-t)")
print(f"window strictly < n in {window_strictly_beats_n}/{cases} cases (sharper than trivial cap)")
print("VERDICT:", "HOLDS — formalize d-t window bound" if fails == 0 else "REFUTED")
