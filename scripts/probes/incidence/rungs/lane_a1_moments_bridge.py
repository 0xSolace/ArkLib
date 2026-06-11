#!/usr/bin/env python3
"""LANE A1 — the incidence-moments bridge (HYPOTHESES.md A1), exact at s=8 (n=16, C19).

SETUP. Fix the received word u and a finite codeword family L (here: the proven-complete
radius-7 list of the canonical max-fiber configuration at n=16 — 19 codewords).
T_p = {x in D : p(x) = u(x)}; agreement spectrum a_j = #{p in L : |T_p| = j}.
For a t-subset sigma of D, the multiplicity  M_t(sigma) = #{p in L : sigma subset T_p};
the DUAL (transposed) spectrum is  b^(t)_m = #{sigma : M_t(sigma) = m}.

THE BRIDGE IDENTITY (proof = one double count). For all r >= 1, t >= 0:

    sum_{sigma in C(D,t)} C(M_t(sigma), r)  =  sum_{R in C(L,r)} C(|T_R|, t),
    where T_R = intersection of T_p over p in R.                         (BRIDGE)

Proof: both sides count pairs (R, sigma), R an r-subset of L, sigma a t-subset of D,
with sigma contained in T_p for every p in R. Fix sigma: the codewords containing sigma
number M_t(sigma), giving C(M_t(sigma), r) choices of R. Fix R: sigma ranges over
t-subsets of T_R, giving C(|T_R|, t).  QED.

CONSEQUENCES (the corrected A1 statement):
 (r=1)  sum_sigma M_t(sigma) = sum_j a_j * C(j,t):  ALL factorial moments of the
        agreement spectrum a_j are single-codeword sums — the pre-registered guess
        ("pair overlaps are the combinatorial core of M3 of a_j") is FALSE in the a_j
        variable: sum_j a_j j^3 = sum_j a_j [j + 3j(j-1) + j(j-1)(j-2)] has no pair term.
 (r=2)  sum_sigma C(M_t(sigma), 2) = sum_{p<p'} C(|T_p cap T_p'|, t):  the moment equal
        to the t-th binomial moment of the PAIR-OVERLAP distribution (the O129 object)
        is the SECOND binomial moment of the DUAL spectrum — the transpose of the
        codeword-point incidence matrix, not a higher moment of a_j.
 (t=1 power form) with N(x) = M_1({x}):
        sum_x N^2 = sum_j a_j j   + 2 sum_{p<p'} |T cap T'|
        sum_x N^3 = sum_j a_j j   + 6 sum_{p<p'} |T cap T'| + 6 sum_{p<p'<p''} |T cap T' cap T''|
        i.e. the third moment whose second-order core IS the pair-overlap distribution
        lives in the dual variable; the genuinely new third-order content is the
        triple-overlap mass.
 (centered form) sum_x (N - Ibar/n)^2 = sum_{p,p' ordered} (|T_p cap T_p'| - |T_p||T_p'|/n):
        the centered dual-M2 measures overlap EXCESS over the uniform-placement baseline.

EXACTNESS CONSUMPTION. Always T_p cap T_p' subset Z0(p - p') (both agreeing with u at x
forces p(x) = p'(x)). The exactness law (|Z0| = |T cap T'|) upgrades this to equality,
so |T_p cap T_p'| = n - d_H(p, p') on D: the entire pair-overlap distribution — hence by
(BRIDGE, r=2) every binomial moment of the dual spectrum's pair content — is computable
from the LIST'S DISTANCE GEOMETRY alone, no further reference to u.

VERIFICATION HERE (all exact integer arithmetic):
  gate:   reproduce C19 = 3 witnesses (agree 10, even support) + 16 dense (agree 9);
  bridge: all nine (t, r) in {1,2,3}^2 — LHS by sigma-enumeration, RHS by R-enumeration;
  power:  the N^2 / N^3 and centered decompositions; the a_j j^3 single-codeword anatomy;
  exact:  |Z0(p-p')| vs |T_p cap T_p'| on ALL 171 pairs (3 wit-wit pairs are NEW data —
          the published n=16 reference covered cross 48 + dense-dense 120 only);
  demo:   measured pair mass vs the worst-case cap (deg < 8 => |T cap T'| <= 7).

Exit 0 iff every exact check passes.
"""
import sys
from itertools import combinations
from math import comb
from collections import Counter

P = 2013265921
G0 = 31
LAM = 284861408
FAILS = 0


def check(name, lhs, rhs):
    global FAILS
    ok = lhs == rhs
    if not ok:
        FAILS += 1
    print(f"  {name}: LHS={lhs} RHS={rhs} -> {'PASS' if ok else 'FAIL'}")


# ---------- polynomial helpers (verbatim conventions of probe_incidence.py) ----------
def pw(b, e):
    return pow(b, e, P)


INV = lambda a: pow(a, P - 2, P)


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] = (out[i + j] + x * y) % P
    return out


def peval(c, x):
    r = 0
    for co in reversed(c):
        r = (r * x + co) % P
    return r


def interp(xs, ys):
    n = len(xs)
    out = [0] * n
    for i in range(n):
        num = [1]
        den = 1
        for j in range(n):
            if j == i:
                continue
            num = pmul(num, [(-xs[j]) % P, 1])
            den = den * ((xs[i] - xs[j]) % P) % P
        s = ys[i] * INV(den) % P
        for d in range(len(num)):
            out[d] = (out[d] + s * num[d]) % P
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


# ---------- the C19 configuration at s=8 (n=16) ----------
def calibrate_n16():
    n, k, A = 16, 8, 9
    h = pw(G0, (P - 1) // n)
    H = [pw(h, i) for i in range(n)]
    w = [(pw(x, 10) + LAM * pw(x, 8)) % P for x in H]
    found = {}
    for sub in combinations(range(n), A):
        c = interp([H[i] for i in sub], [w[i] for i in sub])
        if len(c) <= k:
            key = tuple(c + [0] * (k - len(c)))
            if key not in found:
                found[key] = frozenset(i for i in range(n) if peval(list(key), H[i]) == w[i])
    return H, w, found


n = 16
H, w, found = calibrate_n16()
wit = {c: a for c, a in found.items() if len(a) == 10}
den = {c: a for c, a in found.items() if len(a) == 9}
even = sum(1 for c in wit if all(co == 0 for j, co in enumerate(c) if j % 2 == 1))
gate = len(found) == 19 and len(wit) == 3 and len(den) == 16 and even == 3
print(f"GATE n=16: list={len(found)} = {len(wit)}+{len(den)}, wit-even={even} -> "
      f"{'PASS' if gate else 'FAIL'}")
if not gate:
    sys.exit(1)

L = sorted(found.items())                      # 19 x (codeword, T_p)
T = [a for _, a in L]
a_spec = Counter(len(t) for t in T)
print(f"agreement spectrum a_j (within the list): {dict(sorted(a_spec.items()))}")

# ---------- the bridge, all nine (t, r) ----------
print("\n== BRIDGE: sum_sigma C(M_t,r) = sum_{r-subsets R} C(|T_R|,t), (t,r) in {1,2,3}^2 ==")
for t in (1, 2, 3):
    M = Counter()
    for sigma in combinations(range(n), t):
        ss = frozenset(sigma)
        M[ss] = sum(1 for tp in T if ss <= tp)
    for r in (1, 2, 3):
        lhs = sum(comb(m, r) for m in M.values())
        rhs = 0
        for R in combinations(range(len(T)), r):
            inter = T[R[0]]
            for i in R[1:]:
                inter = inter & T[i]
            rhs += comb(len(inter), t)
        check(f"t={t} r={r}", lhs, rhs)
    if t == 1:
        b1 = Counter(M.values())
        print(f"  dual spectrum b^(1) (point-multiplicity census): {dict(sorted(b1.items()))}")

# ---------- power-moment anatomy at t=1 ----------
print("\n== POWER FORM (t=1): where the 'third moment' pair content actually lives ==")
N = [sum(1 for tp in T if x in tp) for x in range(n)]
F1 = sum(len(tp) for tp in T)
P2 = sum(len(T[i] & T[j]) for i, j in combinations(range(len(T)), 2))
P3 = sum(len(T[i] & T[j] & T[k]) for i, j, k in combinations(range(len(T)), 3))
check("sum_x N   = sum_j a_j j        ", sum(N), F1)
check("sum_x N^2 = F1 + 2*P2          ", sum(v * v for v in N), F1 + 2 * P2)
check("sum_x N^3 = F1 + 6*P2 + 6*P3   ", sum(v ** 3 for v in N), F1 + 6 * P2 + 6 * P3)
# centered dual-M2 = overlap excess over the uniform baseline (rational check, exact via *n)
lhs_n = n * sum(v * v for v in N) - F1 * F1          # n * sum (N - F1/n)^2
rhs_n = sum(n * len(T[i] & T[j]) - len(T[i]) * len(T[j])
            for i in range(len(T)) for j in range(len(T)))
check("n*sum(N-F1/n)^2 = sum_{p,p'}(n|TcapT'|-|T||T'|)", lhs_n, rhs_n)
# the a_j side: j^3 decomposes into SINGLE-codeword factorial moments only
m3a = sum(cnt * j ** 3 for j, cnt in a_spec.items())
m3a_fact = sum(cnt * (j + 3 * j * (j - 1) + j * (j - 1) * (j - 2)) for j, cnt in a_spec.items())
check("sum_j a_j j^3 = single-codeword factorial sum (NO pair term)", m3a, m3a_fact)
print(f"  numbers: F1={F1}  P2(pair-overlap mass)={P2}  P3(triple mass)={P3}  "
      f"sum N^2={sum(v*v for v in N)}  sum N^3={sum(v**3 for v in N)}  a_j-M3={m3a}")

# ---------- exactness on ALL 171 pairs (incl. the 3 witness-witness pairs: new data) ----------
print("\n== EXACTNESS |Z0(p-p')| vs |T cap T'| on all 171 pairs ==")
kind = lambda i: 'W' if len(T[i]) == 10 else 'D'
ex = {('W', 'W'): Counter(), ('W', 'D'): Counter(), ('D', 'D'): Counter()}
ov = {('W', 'W'): Counter(), ('W', 'D'): Counter(), ('D', 'D'): Counter()}
exact_all = True
for i, j in combinations(range(len(T)), 2):
    d = [(x - y) % P for x, y in zip(L[i][0], L[j][0])]
    z0 = sum(1 for x in range(n) if peval(d, H[x]) == 0)
    tt = len(T[i] & T[j])
    kk = tuple(sorted((kind(i), kind(j)), reverse=True))
    ex[kk][z0 - tt] += 1
    ov[kk][tt] += 1
    if z0 != tt:
        exact_all = False
        print(f"  EXCESS pair ({i},{j}) [{kk[0]}{kk[1]}]: |Z0|={z0} |TcapT'|={tt}")
for kk in (('W', 'W'), ('W', 'D'), ('D', 'D')):
    print(f"  {kk[0]}-{kk[1]}: excess hist {dict(sorted(ex[kk].items()))} | "
          f"overlap |TcapT'| hist {dict(sorted(ov[kk].items()))}")
print(f"  exactness on all 171 pairs: {'HOLDS' if exact_all else 'FAILS (excess above)'}")
if exact_all:
    # consequence: pair overlap = list distance geometry, |T cap T'| = n - d_H(p,p') on D
    dh_ok = all(len(T[i] & T[j]) == n - sum(1 for x in range(n)
                if peval(list(L[i][0]), H[x]) != peval(list(L[j][0]), H[x]))
                for i, j in combinations(range(len(T)), 2))
    check("|T cap T'| = n - d_H(p,p') for all pairs (distance-geometry form)", dh_ok, True)

# ---------- what the moments channel consumes (measured vs worst case) ----------
print("\n== CONSUMPTION DEMO: measured pair mass vs the degree worst case ==")
worst = comb(len(T), 2) * 7    # deg(p-p') < 8 and p != p'  =>  |T cap T'| <= |Z0| <= 7
print(f"  sum_x C(N(x),2) = P2 = {P2}  (worst-case cap C(19,2)*7 = {worst}; "
      f"ratio {P2/worst:.3f})")
print(f"  mean pair overlap {P2/comb(len(T),2):.3f} vs cap 7; "
      f"dual-M2 binomial sum_x C(N,2) carries it exactly (BRIDGE t=1,r=2)")

print()
if FAILS:
    print(f"RESULT: {FAILS} FAILURES")
    sys.exit(1)
print("RESULT: ALL EXACT CHECKS PASS")
sys.exit(0)
