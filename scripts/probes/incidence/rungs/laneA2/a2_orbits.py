#!/usr/bin/env python3
"""LANE A2 step 1+2: regenerate the 13,219 delta orbit reps WITH norms,
and compute each orbit's Galois structure under G = Gal(Q(z32)/Q) x {+-1}
(|G| = 32).

For each orbit rep v:
  stab s   = #{(j,e) : sigma_j(v) = (-1)^e v}   (Stab_G, injects into Gal)
  orbit |O|= 32/s  (verified by direct enumeration)
  d        = 16/s = |O|/2 = number of Galois conjugates UP TO SIGN
           = number of independent prime ideals above a split p that can
             contain v  =>  per-orbit bad chance ~ 1-(1-1/p)^d ~ d/p.

H-A2a: measured bad rate c/p has c = mean(d) (not 16) because orbits with
nontrivial stabilizer offer fewer chances.  Output: per-orbit d + norms.
"""
import json, sys, time
sys.path.insert(0, '/home/nubs/Git/ArkLib/scripts/probes/incidence/exactness')
from char0 import N, ZERO, ONE, sub, neg, mul
from norms import galois, norm
from itertools import combinations
from char0 import witness_list, dense_list

t0 = time.time()
wits = witness_list()
dens, _ = dense_list(verbose=False)
dlist = list(dens.values())
deltas = set()
for w in wits:
    ew, Tw = w['ew'], w['Tw']
    for d in dlist:
        et, Tt = d['ev'], d['Tt']
        for k in range(32):
            if k in Tw or k in Tt:
                continue
            deltas.add(sub(ew[k], et[k]))
n_raw = len(deltas)
print(f"distinct raw deltas: {n_raw}  [{time.time()-t0:.1f}s]")
assert ZERO not in deltas

# canonical orbit reps + per-orbit structure
orbits = {}   # canon rep -> dict(stab, orbsize, d)
for v in deltas:
    imgs = set()
    stab = 0
    stab_elts = []
    for j in range(1, 32, 2):
        gv = galois(v, j)
        imgs.add(gv)
        imgs.add(neg(gv))
        if gv == v:
            stab += 1; stab_elts.append((j, +1))
        elif gv == neg(v):
            stab += 1; stab_elts.append((j, -1))
    rep = min(imgs)
    osz = len(imgs)
    assert osz * stab == 32, (osz, stab)   # orbit-stabilizer in G
    if rep in orbits:
        # same orbit reached from another raw delta: structure must agree
        assert orbits[rep]['s'] == stab
    else:
        orbits[rep] = dict(s=stab, osz=osz, d=16 // stab,
                           stab_elts=stab_elts)
print(f"orbit representatives: {len(orbits)}  [{time.time()-t0:.1f}s]")

# how much of each orbit is actually present in the raw delta set?
present = {}
for v in deltas:
    imgs = set()
    for j in range(1, 32, 2):
        gv = galois(v, j)
        imgs.add(gv); imgs.add(neg(gv))
    rep = min(imgs)
    present[rep] = present.get(rep, 0) + 1
frac_full = sum(1 for r, c in present.items() if c == orbits[r]['osz'])
print(f"orbits fully saturated in raw delta set: {frac_full}/{len(orbits)}")

# norms
norms_out = {}
for i, (rep, info) in enumerate(sorted(orbits.items())):
    n = norm(rep)
    norms_out[i] = n
    info['norm'] = n
    if i % 2000 == 0:
        print(f"  norm {i}/{len(orbits)} [{time.time()-t0:.1f}s]")
print(f"norms done [{time.time()-t0:.1f}s]")

# d histogram and stabilizer-element census
dhist, stabcensus = {}, {}
for info in orbits.values():
    dhist[info['d']] = dhist.get(info['d'], 0) + 1
    for j, e in info['stab_elts']:
        if j != 1:
            key = f"sigma_{j}{'+' if e > 0 else '-'}"
            stabcensus[key] = stabcensus.get(key, 0) + 1
print("d histogram (d = independent chances per split prime):", dict(sorted(dhist.items())))
print("nontrivial stabilizer elements (j: zeta->zeta^j, sign):", dict(sorted(stabcensus.items())))
D = sum(info['d'] for info in orbits.values())
print(f"Sum d = {D}; mean d = {D/len(orbits):.4f}  <-- predicted c (vs generic 16)")

# verify rerun against the committed certificate at a few primes
chk = {}
for q in (97, 193, 257, 1409):
    chk[q] = sum(1 for info in orbits.values() if info['norm'] % q == 0)
print("recheck small_bad (expect 1575/786/502/95):", chk)

json.dump(dict(
    n_raw_deltas=n_raw,
    n_orbits=len(orbits),
    d_hist={str(k): v for k, v in sorted(dhist.items())},
    stab_census=stabcensus,
    sum_d=D, mean_d=D / len(orbits),
    recheck=chk,
    per_orbit=[dict(d=info['d'], s=info['s'],
                    stab=[[j, e] for j, e in info['stab_elts'] if j != 1],
                    norm=str(info['norm']))
               for rep, info in sorted(orbits.items())],
), open('/tmp/laneA2/a2_orbit_data.json', 'w'))
print(f"saved /tmp/laneA2/a2_orbit_data.json [{time.time()-t0:.1f}s]")
