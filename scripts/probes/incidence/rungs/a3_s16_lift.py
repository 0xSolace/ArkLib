#!/usr/bin/env python3
"""A3 — second-prime lift of the s=16 (n=32) lambda-configurations.

Dense/witness codewords are uniquely determined by their agreement sets (deg<16
interpolation through >=17 of 32 points), and agreement sets are ABSTRACT index
subsets of Z_32 (exponents of zeta_32) — prime-independent. So the BabyBear census
for a lambda-configuration transfers to the second production prime
P2 = 3*2^30+1 without a kernel run: re-embed lam = -e1(rep) at P2, interpolate the
word over each agreement set, verify the agreement set reproduces EXACTLY, then
re-run the all-pairs exactness test at P2.

What this proves / does not prove (honest scope): if a violating pair's excess
persists at P2 at the same abstract index, it is (empirically, two independent
large split primes) a char-0 cyclotomic identity, like the canonical q-root class;
if it disappears, it was a BabyBear bad-prime accident. Exactness of all other
pairs at BOTH primes is strong evidence of char-0 exactness. This lift does NOT
certify that P2's own list has no additional members beyond the transferred ones
(that would need a P2 kernel sweep) — it certifies the transferred configuration.

Usage: python3 a3_s16_lift.py <lam_babybear> <rep_indices_csv> 'out_<lam>/c17_*.txt'
"""
import sys, glob
from itertools import combinations
from collections import Counter
import numpy as np

P1, G1 = 2013265921, 31
P2, G2 = 3221225473, 5   # smallest primitive root (range(2,200) convention)


def make_domain(P, G0):
    h = pow(G0, (P - 1) // 32, P)
    H = [pow(h, i, P) for i in range(32)]
    G16 = [pow(h * h % P, i, P) for i in range(16)]
    return H, G16


def pmul(a, b, P):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: out[i + j] = (out[i + j] + x * y) % P
    return out


def peval(c, x, P):
    r = 0
    for co in reversed(c): r = (r * x + co) % P
    return r


def interp(xs, ys, P):
    n = len(xs); out = [0] * n
    for i in range(n):
        num = [1]; den = 1
        for j in range(n):
            if j == i: continue
            num = pmul(num, [(-xs[j]) % P, 1], P)
            den = den * ((xs[i] - xs[j]) % P) % P
        s = ys[i] * pow(den, P - 2, P) % P
        for d in range(len(num)): out[d] = (out[d] + s * num[d]) % P
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out


LAM1 = int(sys.argv[1])
rep = tuple(int(t) for t in sys.argv[2].split(","))
pats = sys.argv[3:]

# ---- BabyBear side: recover agreement sets from raw rows ----
H1, G16_1 = make_domain(P1, G1)
assert (P1 - sum(G16_1[i] for i in rep)) % P1 == LAM1, "rep does not embed to LAM at BabyBear"
w1 = [(pow(x, 18, P1) + LAM1 * pow(x, 16, P1)) % P1 for x in H1]
rows = set()
for pat in pats:
    for f in sorted(glob.glob(pat)):
        for line in open(f):
            rows.add(tuple(map(int, line.split())))
Tsets = sorted(frozenset(i for i in range(32) if v[i] == w1[i]) for v in rows)
print(f"LAM(BabyBear)={LAM1}, rep={rep}: {len(Tsets)} codewords "
      f"({sum(1 for T in Tsets if len(T) >= 18)} witnesses) -> lifting to P2={P2}")

# ---- P2 side: re-embed and reconstruct ----
H2, G16_2 = make_domain(P2, G2)
LAM2 = (P2 - sum(G16_2[i] for i in rep)) % P2
w2 = [(pow(x, 18, P2) + LAM2 * pow(x, 16, P2)) % P2 for x in H2]
print(f"LAM(P2) = {LAM2}")

M = np.empty((len(Tsets), 32), dtype=np.uint64)
agct = []
for r, T in enumerate(Tsets):
    pts = sorted(T)[:16]
    c = interp([H2[i] for i in pts], [w2[i] for i in pts], P2)
    assert len(c) <= 16, f"lifted codeword deg>=16 for T={sorted(T)}"
    vals = [peval(c, x, P2) for x in H2]
    ag = frozenset(i for i in range(32) if vals[i] == w2[i])
    assert ag == T, f"agreement set changed under lift: {sorted(T)} -> {sorted(ag)}"
    M[r] = vals
    agct.append(len(T))
print(f"LIFT GATE: all {len(Tsets)} codewords reconstruct at P2 with IDENTICAL "
      f"agreement sets -> PASS")

W = np.array(w2, dtype=np.uint64)


def ptype(i, j):
    return {36: "WW", 35: "X", 34: "DD"}[agct[i] + agct[j]]


ex = {"WW": Counter(), "X": Counter(), "DD": Counter()}
viol = []
L = len(Tsets)
for i in range(L - 1):
    eq = (M[i + 1:] == M[i])
    z0 = eq.sum(axis=1)
    tt = (eq & (M[i] == W)).sum(axis=1)
    exc = (z0 - tt).astype(int)
    for off in np.nonzero(exc)[0]:
        j = i + 1 + int(off)
        extra = tuple(int(t) for t in range(32)
                      if M[i][t] == M[j][t] and M[i][t] != W[t])
        viol.append((tuple(sorted(Tsets[i])), tuple(sorted(Tsets[j])), extra))
    for t, cnt in Counter(zip((ptype(i, j) for j in range(i + 1, L)), exc)).items():
        ex[t[0]][int(t[1])] += cnt
print(f"P2 all-pairs exactness (full C({L},2) = {L*(L-1)//2}):")
for t in ("WW", "X", "DD"):
    print(f"  {t}: {sum(ex[t].values())} pairs, excess hist {dict(sorted(ex[t].items()))}")
print(f"P2 violating pairs as (T1,T2,extra) triples: {len(viol)}")
for T1, T2, extra in viol:
    print(f"  T1={T1} T2={T2} extra={extra}")
