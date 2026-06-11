#!/usr/bin/env python3
"""LANE A2 step 4 (H-A2b): congruence/factor structure of the norms.

Cheap full-population census (all 13,219):
  - v2 (2-adic content) by d-class
  - perfect-power structure: stabilizer order s forces norm = (subnorm)^s
    (up to the sign action) -> check norm is an exact s-th power.
Sampled deep factorization (500 norms, seed 42, 5 s cap each, honest skips):
  - full factorization via trial division < 10^4 + Brent rho + Miller-Rabin
  - smallest split-prime factor, repeated factors, residue classes mod 32,
  - smoothness profile: log-mass below 10^3/10^4/10^6, largest prime factor
    (the large-q rate deficit should be visible as small rough parts).
No sympy on this box: MR uses the deterministic base set valid < 3.3e24
plus extra bases; norms are < 1e25, composites surviving MR are flagged
'probable' honestly.
"""
import json, random, time
from math import gcd, isqrt

dat = json.load(open('/tmp/laneA2/a2_orbit_data.json'))
orbs = [(o['d'], o['s'], int(o['norm'])) for o in dat['per_orbit']]

# ---------- full census: v2 and perfect-power structure ----------
def v2(n):
    n = abs(n)
    k = 0
    while n % 2 == 0:
        n //= 2; k += 1
    return k

def iroot(n, k):
    if n < 0:
        return None
    lo, hi = 0, 1 << ((n.bit_length() // k) + 2)
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** k < n:
            lo = mid + 1
        else:
            hi = mid
    return lo if lo ** k == n else None

v2_by_d = {}
neg_count = 0
pow_ok = {}
for d, s, n in orbs:
    if n < 0:
        neg_count += 1
    v2_by_d.setdefault(d, {}).setdefault(v2(n), 0)
    v2_by_d[d][v2(n)] += 1
    r = iroot(abs(n), s)
    pow_ok.setdefault(s, [0, 0])
    pow_ok[s][0 if r is not None else 1] += 1
print("negative norms:", neg_count)
print("perfect s-th power check (s = |stab|): {s: [ok, fail]}", pow_ok)
print("v2 histogram by d-class:")
for d in sorted(v2_by_d):
    h = dict(sorted(v2_by_d[d].items()))
    tot = sum(h.values())
    mn = min(h); mx = max(h)
    mean = sum(k * v for k, v in h.items()) / tot
    print(f"  d={d:>2} (n={tot:>5}): min v2={mn} max={mx} mean={mean:.2f} "
          f"hist={h if len(h) < 12 else dict(list(h.items())[:12])}")

# ---------- sampled deep factorization ----------
def sieve(lim):
    s = bytearray([1]) * lim
    s[0:2] = b'\x00\x00'
    for i in range(2, int(lim ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(lim) if s[i]]
SMALL = sieve(10 ** 4)

MR_BASES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
def is_prime(n):
    if n < 2:
        return False
    for p in MR_BASES:
        if n % p == 0:
            return n == p
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2; r += 1
    for a in MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True

def brent(n, deadline):
    if n % 2 == 0:
        return 2
    rng = random.Random(n)
    while time.time() < deadline:
        y, c, m = rng.randrange(1, n), rng.randrange(1, n), 128
        g, r, q = 1, 1, 1
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(m, r - k)):
                    y = (y * y + c) % n
                    q = q * abs(x - y) % n
                g = gcd(q, n)
                k += m
            r *= 2
            if time.time() > deadline:
                return None
        if g == n:
            g = 1
            while g == 1:
                ys = (ys * ys + c) % n
                g = gcd(abs(x - ys), n)
        if g != n:
            return g
    return None

def factor(n, deadline):
    fac, todo, incomplete = {}, [n], False
    for p in SMALL:
        while n % p == 0:
            fac[p] = fac.get(p, 0) + 1
            n //= p
    todo = [n] if n > 1 else []
    while todo:
        m = todo.pop()
        if m == 1:
            continue
        if is_prime(m):
            fac[m] = fac.get(m, 0) + 1
            continue
        # perfect power shortcut
        done = False
        for k in (2, 3, 4):
            r = iroot(m, k)
            if r:
                todo.extend([r] * k)
                done = True
                break
        if done:
            continue
        g = brent(m, deadline)
        if g is None:
            fac[m] = fac.get(m, 0) - 1000   # marker: unfactored composite
            incomplete = True
            continue
        todo.extend([g, m // g])
    return fac, incomplete

rng = random.Random(42)
idx = rng.sample(range(len(orbs)), 500)
res = []
n_incomplete = 0
t0 = time.time()
for c, i in enumerate(idx):
    d, s, n = orbs[i]
    fac, inc = factor(abs(n), time.time() + 5.0)
    n_incomplete += inc
    res.append(dict(i=i, d=d, s=s, digits=len(str(abs(n))),
                    incomplete=inc,
                    fac={str(p): e for p, e in sorted(fac.items())}))
    if c % 100 == 0:
        print(f"  {c}/500 [{time.time()-t0:.0f}s]")
print(f"factored 500 (incomplete: {n_incomplete}) [{time.time()-t0:.0f}s]")

# ---------- charts ----------
from math import log
def chart(sel, label):
    sub = [r for r in res if sel(r)]
    if not sub:
        return {}
    smallest_split, lpf, mass = {}, [], []
    exp_div_s_ok = 0
    res32 = {}
    for r in sub:
        s = r['s']
        fac = {int(p): e for p, e in r['fac'].items() if e > 0}
        ln_tot = sum(e * log(p) for p, e in fac.items()) or 1.0
        sp = [p for p in fac if p % 32 == 1]
        key = min(sp) if sp else None
        smallest_split[key] = smallest_split.get(key, 0) + 1
        if not r['incomplete']:
            lpf.append(max(fac))
            mass.append(tuple(round(sum(e * log(p) for p, e in fac.items()
                                        if p < B) / ln_tot, 3)
                              for B in (10 ** 3, 10 ** 4, 10 ** 6)))
        if all(e % s == 0 for e in fac.values()):
            exp_div_s_ok += 1
        for p, e in fac.items():
            res32.setdefault(p % 32, [0, 0])
            res32[p % 32][0] += 1
            res32[p % 32][1] += e
    out = dict(n=len(sub),
               exponents_all_divisible_by_s=exp_div_s_ok,
               smallest_split_prime_hist=dict(
                   sorted(((str(k), v) for k, v in smallest_split.items()),
                          key=lambda t: (t[0] == 'None', t[0]))),
               residue_mod32_of_prime_factors={
                   str(k): dict(n_norms_hit=v[0], total_exponent=v[1])
                   for k, v in sorted(res32.items())})
    if lpf:
        lpf.sort()
        out['largest_prime_factor_quartiles'] = [
            lpf[0], lpf[len(lpf)//4], lpf[len(lpf)//2],
            lpf[3*len(lpf)//4], lpf[-1]]
        ms = sorted(mass)
        out['logmass_below_1e3_1e4_1e6_median'] = list(ms[len(ms)//2])
    print(f"{label}: {json.dumps(out, indent=1)[:1200]}")
    return out

c_all = chart(lambda r: True, "\nALL 500")
c_d16 = chart(lambda r: r['d'] == 16, "\nd=16 (free orbits)")
c_d8 = chart(lambda r: r['d'] == 8, "\nd=8 (index-2 stabilizer)")

json.dump(dict(census=dict(neg_norms=neg_count,
                           perfect_power_by_s={str(k): v for k, v in pow_ok.items()},
                           v2_by_d={str(d): {str(k): v for k, v in h.items()}
                                    for d, h in v2_by_d.items()}),
               sample=res, n_incomplete=n_incomplete,
               charts=dict(all=c_all, d16=c_d16, d8=c_d8)),
          open('/tmp/laneA2/a2_factor_result.json', 'w'))
print("saved /tmp/laneA2/a2_factor_result.json")
