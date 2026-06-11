#!/usr/bin/env python3
"""LANE A2 step 3b: class-wise rate test — does each stabilizer class d
follow its OWN d/q law over the 30-prime sweep?  (Separates H-A2a
stabilizer weighting from H-A2b smoothness distortion.)"""
import json
from math import sqrt
dat = json.load(open('/tmp/laneA2/a2_orbit_data.json'))
orbs = [(o['d'], int(o['norm'])) for o in dat['per_orbit']]
def sieve(lim):
    s = bytearray([1]) * lim
    s[0:2] = b'\x00\x00'
    for i in range(2, int(lim**.5)+1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(lim) if s[i]]
sweep = [q for q in sieve(3400) if q % 32 == 1][:30]
hist = {}
for d, n in orbs:
    hist[d] = hist.get(d, 0) + 1
out = {}
for dcl in sorted(hist):
    m = sum(1 for q in sweep for d, n in orbs if d == dcl and n % q == 0)
    e = v = 0.0
    for q in sweep:
        p = 1 - (1 - 1/q)**dcl
        e += hist[dcl]*p
        v += hist[dcl]*p*(1-p)
    out[dcl] = dict(n_orb=hist[dcl], measured=m, expected=round(e, 1),
                    z=round((m-e)/sqrt(v), 2))
    print(dcl, out[dcl])
json.dump(out, open('/tmp/laneA2/a2_classwise_result.json', 'w'), indent=1)
