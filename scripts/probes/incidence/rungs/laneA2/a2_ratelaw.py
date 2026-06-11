#!/usr/bin/env python3
"""LANE A2 step 3: corrected rate law test.

Model (H-A2a): a split prime q (q = 1 mod 32) divides the norm of orbit i
iff v_i lies in one of d_i "sign-classes" of the 16 primes above q, where
d_i = 16/|Stab_G(v_i)|.  Under per-class uniformity:
    P_i(q) = 1 - (1 - 1/q)^{d_i}
    E[bad(q)] = sum_i P_i(q)            (first order:  D/q, D = sum d_i)
    Var[bad(q)] = sum_i P_i(q)(1-P_i(q))  (independent-orbit model)
Generic law to reject: every d_i = 16 (c = 16).

Tests:
  T1: 30-prime sweep (q = 97..3361): measured vs corrected vs generic-16,
      z-scores, aggregate z, chi-square dispersion.
  T2: 1/q shape over the FULL range: decade bins of all split q < 2e6
      (zero-count primes included), measured vs corrected totals.
"""
import json
from math import sqrt

dat = json.load(open('/tmp/laneA2/a2_orbit_data.json'))
dhist = {int(k): v for k, v in dat['d_hist'].items()}
norms = [int(o['norm']) for o in dat['per_orbit']]
n_orb = dat['n_orbits']
D = dat['sum_d']
print(f"orbits={n_orb}  D=sum d={D}  mean d={D/n_orb:.4f}")

# all split primes < 2e6
def sieve_primes(lim):
    s = bytearray([1]) * lim
    s[0:2] = b'\x00\x00'
    for i in range(2, int(lim ** .5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(lim) if s[i]]
split = [q for q in sieve_primes(2 * 10 ** 6) if q % 32 == 1]
print(f"split primes < 2e6: {len(split)}")

# measured: recompute divisibility counts via gcd with split-prime product
M = 1
for q in split:
    M *= q
measured = {q: 0 for q in split}
from math import gcd
for n in norms:
    g = gcd(abs(n), M)
    if g > 1:
        for q in split:
            if g % q == 0:
                measured[q] += 1
                while g % q == 0:
                    g //= q
            if g == 1:
                break
# cross-check against committed certificate
cert = json.load(open('/home/nubs/Git/ArkLib/scripts/probes/incidence/'
                      'exactness/norms_result.json'))['small_bad']
mism = [q for q in split
        if measured[q] != cert.get(str(q), 0)]
print(f"cross-check vs committed small_bad: "
      f"{'EXACT MATCH' if not mism else f'MISMATCH at {mism[:5]}'}")

def expected(q, generic=False):
    e = v = 0.0
    for d, cnt in dhist.items():
        if generic:
            d = 16
        p = 1 - (1 - 1 / q) ** d
        e += cnt * p
        v += cnt * p * (1 - p)
    return e, v

# T1: 30-prime sweep
sweep = split[:30]
print(f"\nT1: 30-prime sweep  q = {sweep[0]}..{sweep[-1]}")
print(f"{'q':>6} {'meas':>5} {'corr E':>8} {'z_corr':>7} {'gen16 E':>8} {'z_gen':>7}")
rows = []
sm = se = sv = se16 = sv16 = chi2 = 0.0
for q in sweep:
    m = measured[q]
    e, v = expected(q)
    e16, v16 = expected(q, generic=True)
    zc = (m - e) / sqrt(v)
    zg = (m - e16) / sqrt(v16)
    chi2 += zc * zc
    sm += m; se += e; sv += v; se16 += e16; sv16 += v16
    rows.append(dict(q=q, measured=m, expected_corrected=round(e, 1),
                     z_corrected=round(zc, 2),
                     expected_generic16=round(e16, 1),
                     z_generic16=round(zg, 2)))
    print(f"{q:>6} {m:>5} {e:>8.1f} {zc:>7.2f} {e16:>8.1f} {zg:>7.2f}")
z_tot_c = (sm - se) / sqrt(sv)
z_tot_g = (sm - se16) / sqrt(sv16)
print(f"TOTAL  meas={sm:.0f}  corrected E={se:.1f} (z={z_tot_c:+.2f})  "
      f"generic16 E={se16:.1f} (z={z_tot_g:+.2f})")
print(f"chi2(corrected, 30 dof) = {chi2:.1f}  -> dispersion factor "
      f"{chi2/30:.2f}")

# T2: full-range decade bins (includes zero-count primes via the sieve)
print("\nT2: 1/q-shape, full split-prime range, decade bins")
bins = [(97, 1000), (1000, 10 ** 4), (10 ** 4, 10 ** 5),
        (10 ** 5, 10 ** 6), (10 ** 6, 2 * 10 ** 6)]
brows = []
for lo, hi in bins:
    qs = [q for q in split if lo <= q < hi]
    m = sum(measured[q] for q in qs)
    e = sum(expected(q)[0] for q in qs)
    v = sum(expected(q)[1] for q in qs)
    e16 = sum(expected(q, generic=True)[0] for q in qs)
    z = (m - e) / sqrt(v)
    zg = (m - e16) / sqrt(sum(expected(q, True)[1] for q in qs))
    brows.append(dict(lo=lo, hi=hi, n_primes=len(qs), measured=m,
                      expected_corrected=round(e, 1), z_corrected=round(z, 2),
                      expected_generic16=round(e16, 1), z_generic16=round(zg, 2)))
    print(f"[{lo:>7},{hi:>7})  n_q={len(qs):>5}  meas={m:>6} "
          f" corrE={e:>8.1f} (z={z:+6.2f})  gen16E={e16:>8.1f} (z={zg:+6.2f})")

json.dump(dict(D=D, mean_d=D / n_orb, d_hist=dat['d_hist'],
               crosscheck_exact=not mism,
               sweep30=rows,
               sweep30_total=dict(measured=sm, corrected=se,
                                  z_corrected=z_tot_c,
                                  generic16=se16, z_generic16=z_tot_g,
                                  chi2_corrected=chi2, dof=30),
               full_range_bins=brows),
          open('/tmp/laneA2/a2_ratelaw_result.json', 'w'), indent=1)
print("\nsaved /tmp/laneA2/a2_ratelaw_result.json")
