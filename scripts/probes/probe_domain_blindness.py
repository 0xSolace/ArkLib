#!/usr/bin/env python3
"""Domain-blindness, OPTIMIZED: precompute ext(syndrome,S) table once per domain.
Tests whether the worst-line bad count differs between the smooth subgroup and random domains."""
import itertools, random, time
exec(open('/tmp/probe_n1_energy_vs_badcount.py').read().split('# ---- run')[0])

def bad_count_fast(p, D, k, delta):
    n=len(D); H=parity_check(p,D,k); m=len(H)
    if (p**m)**2 > 200000: return None
    Smin=int((1-delta)*n + 0.999999)
    allS=[frozenset(c) for r in range(Smin,n+1) for c in itertools.combinations(range(n),r)]
    syns=list(itertools.product(range(p),repeat=m))
    # precompute ext[syndrome][S] = bool, once
    ext={}
    for s in syns:
        es={}
        for S in allS:
            es[S]=ext_from_S(p,D,k,s,H,S)
        ext[s]=es
    best=0
    for s0 in syns:
        e0=ext[s0]
        for s1 in syns:
            e1=ext[s1]; cnt=0
            for gamma in range(p):
                sg=tuple((s0[i]+gamma*s1[i])%p for i in range(m))
                eg=ext[sg]
                if any(eg[S] and not (e0[S] and e1[S]) for S in allS):
                    cnt+=1
            best=max(best,cnt)
    return best

random.seed(11)
print("DOMAIN-BLINDNESS (optimized): smooth vs 8 random domains, (11,5,3)", flush=True)
p,n,k=11,5,3
H=tuple(mult_subgroup(p,n))
allsub=list(itertools.combinations([x for x in range(1,p)],n))
sample=[H]+random.sample([s for s in allsub if s!=H], 8)
for delta in [0.25,0.35]:
    print(f"-- delta={delta} --", flush=True)
    for D in sample:
        t=time.time(); bc=bad_count_fast(p,list(D),k,delta)
        tag="SMOOTH" if D==H else ""
        print(f"   {D} bad={bc} {tag} ({time.time()-t:.0f}s)", flush=True)
