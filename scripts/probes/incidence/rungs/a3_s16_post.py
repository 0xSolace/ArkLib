#!/usr/bin/env python3
"""A3 — rigidity beyond the max-fiber configuration, rung s=16 (n=32) post-pass.

Consumes raw census-kernel rows produced with the LAM override:
  gcc -O3 -march=native -DA=17 -DLAM=<lam>UL census_kernel.c -o census17_<lam>
  for i in $(seq 0 15); do ./census17_<lam> $i out_<lam>/c17_$i.txt & done; wait
  python3 a3_s16_post.py <lam> 'out_<lam>/c17_*.txt'

Per lambda: dedupe rows -> distinct value-vectors; verify deg<16 via IDFT; classify
layers by agreement; GATE the agree-18 layer against the independently constructed
fiber witnesses u_S(X^2) (S = the 9-subsets of mu_16 with e1(S) = -lam — the GENERAL
fiber, no antipodal-pair structure assumed); then test the exactness law
|Z0(c-c')| = |T cap T'| on EVERY pair (full C(L,2), no sampling — the value-vector
formulation makes the cap unnecessary: excess = #{i : v1[i]=v2[i] != w[i]}).
Violating pairs are printed fully (loci, coefficient vectors, negation flag,
antipodal-mechanism check). Byproduct: per-lambda list sizes (new census data,
preliminary). Exact integer arithmetic throughout (numpy used for uint64 equality
comparisons only).
"""
import sys, glob
from itertools import combinations
from collections import Counter, defaultdict
import numpy as np

P = 2013265921; G0 = 31
def pw(b, e): return pow(b, e, P)
INV = lambda a: pow(a, P - 2, P)

def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y: out[i + j] = (out[i + j] + x * y) % P
    return out
def peval(c, x):
    r = 0
    for co in reversed(c): r = (r * x + co) % P
    return r
def interp(xs, ys):
    n = len(xs); out = [0] * n
    for i in range(n):
        num = [1]; den = 1
        for j in range(n):
            if j == i: continue
            num = pmul(num, [(-xs[j]) % P, 1])
            den = den * ((xs[i] - xs[j]) % P) % P
        s = ys[i] * INV(den) % P
        for d in range(len(num)): out[d] = (out[d] + s * num[d]) % P
    while len(out) > 1 and out[-1] == 0: out.pop()
    return out

LAM = int(sys.argv[1])
pats = sys.argv[2:]
h32 = pw(G0, (P - 1) // 32); H32 = [pw(h32, i) for i in range(32)]
G16 = [pw(h32 * h32 % P, i) for i in range(16)]
w32 = [(pw(x, 18) + LAM * pw(x, 16)) % P for x in H32]
HINV = [INV(x) for x in H32]; inv32 = INV(32)
def idft(vals):
    return tuple(sum(vals[i] * pw(HINV[i], d) for i in range(32)) % P * inv32 % P
                 for d in range(32))

# ---- fiber witnesses (general: ANY 9-subset of mu_16 with e1 = -lam) ----
target_e1 = (P - LAM) % P
fiber = [sub for sub in combinations(range(16), 9)
         if sum(G16[i] for i in sub) % P == target_e1]
witnesses = {}
for sub in fiber:
    S = [G16[i] for i in sub]
    u = interp(S, [(pw(s, 9) + LAM * pw(s, 8)) % P for s in S])
    assert len(u) <= 8, f"fiber witness deg(u)>7 at {sub}"
    c = [0] * 16
    for j, co in enumerate(u): c[2 * j] = co
    key = tuple(c)
    ag = frozenset(i for i in range(32) if peval(list(key), H32[i]) == w32[i])
    assert len(ag) == 18, f"fiber witness agreement {len(ag)} != 18 at {sub}"
    witnesses[key] = ag
print(f"LAM={LAM}: fiber size {len(fiber)} (9-subsets of mu_16 with e1=-lam); "
      f"{len(witnesses)} constructed witnesses, all agree exactly 18")

# ---- ingest raw rows ----
raw_lines = 0; rows = set()
for pat in pats:
    for f in sorted(glob.glob(pat)):
        for line in open(f):
            raw_lines += 1
            rows.add(tuple(map(int, line.split())))
print(f"raw kernel rows: {raw_lines} lines (functional passes), "
      f"{len(rows)} distinct value-vectors")

dense = {}; wit_seen = set(); ag_hist = Counter()
for vals in sorted(rows):
    cs = idft(list(vals))
    assert all(co == 0 for co in cs[16:]), "deg >= 16 candidate emitted"
    key = cs[:16]
    ag = frozenset(i for i in range(32) if vals[i] == w32[i])
    ag_hist[len(ag)] += 1
    if len(ag) >= 18:
        assert key in witnesses and witnesses[key] == ag, \
            f"agree-{len(ag)} codeword NOT a constructed fiber witness: {key}"
        wit_seen.add(key)
    elif len(ag) == 17:
        dense[key] = ag
    else:
        raise AssertionError(f"row with agreement {len(ag)} < 17 emitted")
gate = (wit_seen == set(witnesses))
exp_raw = 18 * len(witnesses) + len(dense)
print(f"GATE: witnesses {len(wit_seen)}/{len(witnesses)} bit-exact, "
      f"dense={len(dense)}, agreement hist {dict(sorted(ag_hist.items()))}, "
      f"pass-accounting {raw_lines} raw vs expected {exp_raw} = "
      f"18*{len(witnesses)} + {len(dense)} -> "
      f"{'PASS' if gate and raw_lines == exp_raw else 'FAIL'}")
if not (gate and raw_lines == exp_raw): sys.exit(1)
print(f"CENSUS (byproduct, preliminary): LAM={LAM} list size = "
      f"{len(witnesses) + len(dense)} = {len(witnesses)} witnesses + {len(dense)} dense "
      f"(canonical max-fiber reference: 1379 = 35 + 1344)")

# ---- exactness on EVERY pair (full, no sampling) ----
items = sorted(witnesses.items()) + sorted(dense.items())
keys = [k for k, _ in items]
agct = [len(a) for _, a in items]
M = np.empty((len(items), 32), dtype=np.uint64)
for r, (k, _) in enumerate(items):
    M[r] = [peval(list(k), x) for x in H32]
# row-level audit: numpy values match the raw kernel value-vectors
audit_rows = {tuple(int(v) for v in M[r]) for r in range(len(items))}
assert audit_rows == rows, "value-matrix mismatch vs raw kernel rows"
W = np.array(w32, dtype=np.uint64)
nw = len(witnesses)

def ptype(i, j):
    a, b = agct[i], agct[j]
    return "WW" if a + b == 36 else ("X" if a + b == 35 else "DD")

ex = {"WW": Counter(), "X": Counter(), "DD": Counter()}
violations = []
L = len(items)
for i in range(L - 1):
    eq = (M[i + 1:] == M[i])                       # pairwise pointwise equality
    z0 = eq.sum(axis=1)                            # |Z0(c_i - c_j)|
    tt = (eq & (M[i] == W)).sum(axis=1)            # |T_i cap T_j|
    exc = (z0 - tt).astype(int)
    for off in np.nonzero(exc)[0]:
        violations.append((i, i + 1 + int(off), int(exc[off])))
    for t, cnt in Counter(zip((ptype(i, j) for j in range(i + 1, L)), exc)).items():
        ex[t[0]][int(t[1])] += cnt
npairs = {t: sum(c.values()) for t, c in ex.items()}
print(f"\nALL-PAIRS exactness (full C({L},2) = {L*(L-1)//2}, cap not needed):")
for t in ("WW", "X", "DD"):
    print(f"  {t}: {npairs[t]} pairs, excess hist {dict(sorted(ex[t].items()))}")

def neg_key(c): return tuple((co if j % 2 == 0 else (P - co) % P)
                             for j, co in enumerate(c))
print(f"\nviolating pairs ({len(violations)}), printed fully:")
for i, j, e in violations:
    v1, v2 = M[i], M[j]
    a1 = frozenset(int(t) for t in np.nonzero(v1 == W)[0])
    a2 = frozenset(int(t) for t in np.nonzero(v2 == W)[0])
    extra = [int(t) for t in range(32) if v1[t] == v2[t] and v1[t] != W[t]]
    anti = all((t + 16) % 32 in (a1 & a2) for t in extra)
    print(f"  pair ({i},{j}) type {ptype(i,j)}: excess {e}, extra idx {extra}, "
          f"negation-pair={keys[j] == neg_key(keys[i])}, "
          f"all-extras-antipodal-to-common-agreement={anti}")
    print(f"    T1={sorted(a1)}\n    T2={sorted(a2)}")
    print(f"    c ={keys[i]}\n    c'={keys[j]}")
if not violations:
    print("  (none — every pair is exact at BabyBear)")
