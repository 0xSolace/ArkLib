#!/usr/bin/env python3
"""A3 — rigidity beyond the max-fiber configuration, rung s=8 (n=16), EXHAUSTIVE.

Pre-registered (rungs/HYPOTHESES.md A3, sharpened in the lane brief): the exactness
law |Z0(c-c')| = |T cap T'| holds at EVERY lambda-configuration of the word family
w(x) = x^10 + lam*x^8 on mu_16, lam = -e1(S) over 5-subsets S of mu_8 — not just the
canonical max-fiber lam. Falsifier: any pair at any lambda with excess zeros.

Scope upgrade vs the brief (cheaper than expected, so stronger): the s=8 fiber
spectrum has 40 distinct e1 values (fiber sizes {1:32, 3:8}; NO fiber-2 exists), so
this runs ALL 40 lambdas, full C(16,9)=11440 sweep each, ALL pairwise difference
tests (every pair, all types WW/X/DD) — and repeats everything at a second split
prime P2 = 3*2^30+1 (same abstract configurations via the index embedding) to make
"char-0-style" more than a one-prime claim. Configurations are matched across primes
by agreement sets (subsets of Z_16 exponent indices — prime-independent), which
determine codewords uniquely (deg<8 interpolation through 9+ points).

Byproduct (preliminary, first measurement): the lambda-spectrum of list sizes at
fixed radius (A=9) at s=8.

Machine rules respected: exact integer arithmetic only; this script is light
(~2 min single-core); /tmp not used — output goes to stdout, redirect to rungs/.
"""
import sys
from itertools import combinations
from collections import Counter, defaultdict

P1, G1 = 2013265921, 31          # BabyBear 15*2^27+1, g0=31 (program convention)
P2 = 3221225473                   # 3*2^30+1, the second production prime
LAM_CANON = 284861408             # canonical max-fiber lambda at BabyBear


def smallest_proot(p, factors):
    for g in range(2, 200):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root < 200")


G2 = smallest_proot(P2, [2, 3])


def pmul(a, b, P):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[i + j] = (out[i + j] + x * y) % P
    return out


def peval(c, x, P):
    r = 0
    for co in reversed(c):
        r = (r * x + co) % P
    return r


def interp(xs, ys, P):
    n = len(xs)
    out = [0] * n
    for i in range(n):
        num = [1]
        den = 1
        for j in range(n):
            if j == i:
                continue
            num = pmul(num, [(-xs[j]) % P, 1], P)
            den = den * ((xs[i] - xs[j]) % P) % P
        s = ys[i] * pow(den, P - 2, P) % P
        for d in range(len(num)):
            out[d] = (out[d] + s * num[d]) % P
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def neg_key(c, P):
    return tuple((co if j % 2 == 0 else (P - co) % P) for j, co in enumerate(c))


def run_prime(P, G0):
    """Full A3 battery at one prime. Returns (partition, results) where results is
    keyed by the fiber's lex-min representative subset (prime-independent)."""
    h = pow(G0, (P - 1) // 16, P)
    H = [pow(h, i, P) for i in range(16)]
    G8 = [pow(h * h % P, i, P) for i in range(8)]
    INVD = [[0] * 16 for _ in range(16)]
    for i in range(16):
        for j in range(16):
            if i != j:
                INVD[i][j] = pow((H[i] - H[j]) % P, P - 2, P)

    fib = defaultdict(list)
    for sub in combinations(range(8), 5):
        fib[sum(G8[i] for i in sub) % P].append(sub)
    partition = sorted(tuple(sorted(v)) for v in fib.values())

    results = {}
    for e1, subs in sorted(fib.items(), key=lambda kv: min(kv[1])):
        lam = (P - e1) % P
        rep = min(subs)
        w = [(pow(x, 10, P) + lam * pow(x, 8, P)) % P for x in H]

        # constructed witnesses: u_S, deg<=3 forced by e1(S) = -lam; c = u_S(X^2)
        wit_expect = {}
        for sub in subs:
            S = [G8[i] for i in sub]
            u = interp(S, [(pow(s, 5, P) + lam * pow(s, 4, P)) % P for s in S], P)
            assert len(u) <= 4, f"lam={lam}: witness u has deg>3"
            c = [0] * 8
            for j, co in enumerate(u):
                c[2 * j] = co
            key = tuple(c)
            ag = frozenset(i for i in range(16) if peval(list(key), H[i], P) == w[i])
            assert len(ag) == 10, f"lam={lam}: witness agreement {len(ag)} != 10"
            wit_expect[key] = ag

        # full C(16,9) sweep with the kernel's functional prefilter (leading
        # divided difference == 0 <=> the 9-point interpolant has deg<=7)
        found = {}
        for sub in combinations(range(16), 9):
            s = 0
            for t in sub:
                lt = w[t]
                row = INVD[t]
                for u_ in sub:
                    if u_ != t:
                        lt = lt * row[u_] % P
                s += lt
            if s % P == 0:
                c = interp([H[i] for i in sub], [w[i] for i in sub], P)
                assert len(c) <= 8
                key = tuple(c + [0] * (8 - len(c)))
                if key not in found:
                    vals = tuple(peval(list(key), x, P) for x in H)
                    ag = frozenset(i for i in range(16) if vals[i] == w[i])
                    assert len(ag) >= 9
                    found[key] = (vals, ag)

        ag_hist = Counter(len(a) for _, a in found.values())
        top = {k for k, (_, a) in found.items() if len(a) >= 10}
        wit_gate = (top == set(wit_expect)
                    and all(found[k][1] == wit_expect[k] for k in wit_expect))

        # exactness on EVERY pair
        items = sorted(found.items())
        ex = {"WW": Counter(), "X": Counter(), "DD": Counter()}
        violations = []
        for (k1, (v1, a1)), (k2, (v2, a2)) in combinations(items, 2):
            extra = tuple(i for i in range(16) if v1[i] == v2[i] and v1[i] != w[i])
            t = {20: "WW", 19: "X", 18: "DD"}[len(a1) + len(a2)]
            ex[t][len(extra)] += 1
            if extra:
                anti = all((i + 8) % 16 in (a1 & a2) for i in extra)
                violations.append((tuple(sorted(a1)), tuple(sorted(a2)), extra,
                                   t, k1, k2, k2 == neg_key(k1, P), anti))
        results[rep] = dict(lam=lam, e1=e1, fiber=len(subs),
                            list_size=len(found), ag_hist=dict(sorted(ag_hist.items())),
                            wit_gate=wit_gate,
                            ex={t: dict(sorted(c.items())) for t, c in ex.items()},
                            violations=violations,
                            agsets=frozenset(tuple(sorted(a)) for _, a in found.values()))
    return partition, results


print(f"second prime P2={P2}, smallest primitive root g0={G2}")
part1, res1 = run_prime(P1, G1)
part2, res2 = run_prime(P2, G2)
print(f"fiber partition of the 56 5-subsets identical at both primes: {part1 == part2}")
print(f"lambdas: {len(res1)} (fiber sizes {dict(sorted(Counter(r['fiber'] for r in res1.values()).items()))})")

# canonical calibration gate against the published run (RESULTS-INCIDENCE.md / run2)
canon = [r for r in res1.values() if r["lam"] == LAM_CANON]
assert len(canon) == 1
c = canon[0]
gate = (c["list_size"] == 19 and c["fiber"] == 3 and c["ag_hist"] == {9: 16, 10: 3}
        and c["wit_gate"] and c["ex"]["X"] == {0: 48} and c["ex"]["DD"] == {0: 120})
print(f"GATE canonical lam={LAM_CANON}: list=19=3+16, X extra {{0:48}}, DD extra {{0:120}} -> {'PASS' if gate else 'FAIL'}")
if not gate:
    print("  got:", {k: c[k] for k in ('list_size', 'ag_hist', 'wit_gate', 'ex')})
    sys.exit(1)

print("\n== per-lambda census + exactness (BabyBear) ==")
print("rep-subset       lambda      fiber list  agree-hist        wit-gate  "
      "WW-pairs X-pairs DD-pairs  excess-pairs")
tot_pairs = Counter()
tot_excess = 0
for rep in sorted(res1):
    r = res1[rep]
    npairs = {t: sum(cnt.values()) for t, cnt in r["ex"].items()}
    nexc = sum(c_ for t in r["ex"] for e, c_ in r["ex"][t].items() if e > 0)
    tot_excess += nexc
    for t in npairs:
        tot_pairs[t] += npairs[t]
    print(f"{str(rep):16} {r['lam']:>10}  {r['fiber']:>4} {r['list_size']:>4}  "
          f"{str(r['ag_hist']):17} {str(r['wit_gate']):8}  "
          f"{npairs['WW']:>7} {npairs['X']:>7} {npairs['DD']:>8}  {nexc}")
print(f"\nTOTAL pairs tested (BabyBear): {sum(tot_pairs.values())} "
      f"({dict(tot_pairs)}); pairs with excess zeros: {tot_excess}")

print("\n== violating pairs, printed fully (both primes) ==")
nv = 0
for tag, res in (("BabyBear", res1), (f"P2={P2}", res2)):
    for rep in sorted(res):
        for (T1, T2, extra, t, k1, k2, isneg, anti) in res[rep]["violations"]:
            nv += 1
            print(f"[{tag}] lam={res[rep]['lam']} (fiber {res[rep]['fiber']}, rep {rep}) "
                  f"type {t}: T1={T1} T2={T2} extra-idx={extra} "
                  f"negation-pair={isneg} all-extras-antipodal-to-common-agreement={anti}")
            print(f"    c ={k1}\n    c'={k2}")
if nv == 0:
    print("(none — every pair at every lambda at both primes is exact)")

print("\n== cross-prime agreement (char-0-style corroboration) ==")
mismatch = 0
for rep in sorted(res1):
    a, b = res1[rep], res2[rep]
    same = (a["fiber"] == b["fiber"] and a["list_size"] == b["list_size"]
            and a["ag_hist"] == b["ag_hist"] and a["ex"] == b["ex"]
            and a["agsets"] == b["agsets"]
            and [(v[0], v[1], v[2], v[3]) for v in a["violations"]]
            == [(v[0], v[1], v[2], v[3]) for v in b["violations"]])
    if not same:
        mismatch += 1
        print(f"MISMATCH at rep {rep}: BabyBear {a['list_size']}/{a['ex']} vs P2 {b['list_size']}/{b['ex']}")
print(f"per-lambda incidence structure (list sizes, agreement-set families, excess "
      f"histograms, violation loci) identical at both primes: "
      f"{mismatch == 0} ({len(res1) - mismatch}/{len(res1)} lambdas)")

print("\n== byproduct: lambda-spectrum of list sizes at radius A=9, s=8 (preliminary) ==")
spec = defaultdict(Counter)
for r in res1.values():
    spec[r["fiber"]][r["list_size"]] += 1
for f in sorted(spec):
    print(f"fiber {f}: list-size histogram {dict(sorted(spec[f].items()))}")
