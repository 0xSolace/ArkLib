import cmath, math
def prime_factors(n):
    f=set(); d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def find_primes(n, count, minratio=4):
    out=[]; k=minratio
    while len(out)<count and k<minratio+50000:
        p=n*k+1
        if p>3 and all(p%d for d in range(2,int(p**0.5)+1)): out.append(p)
        k+=1
    return out
def munit(p,n):
    m=(p-1)//n
    for a in range(2,p):
        h=pow(a,m,p)
        if pow(h,n,p)==1 and all(pow(h,n//q,p)!=1 for q in prime_factors(n)):
            G=[]; v=1
            for _ in range(n): G.append(v); v=v*h%p
            return G
    return None
def ep(p): return lambda t: cmath.exp(2j*math.pi*(t%p)/p)
def eta(G,c,p,w): return sum(w((c*x)%p) for x in G)

# FULL coset-invariance: eta_{c*u} = eta_c for ALL u in G, all c (incl c=0). Thinness-essential.
# Also test it FAILS for a non-subgroup thin set S (random same-size subset of F_p^*).
import random
cases=[]
for n in [8,16,32,64]:
    for p in find_primes(n,2,4): cases.append((n,p))
cases += [(16,65537),(32,65537),(64,65537)]

allok=True
for n,p in cases:
    G=munit(p,n)
    if G is None: continue
    w=ep(p)
    maxerr=0
    for c in [0,1,3,(p-1)//2,p-2,7]:
        c%=p
        base=eta(G,c,p,w)
        for u in G:
            maxerr=max(maxerr,abs(eta(G,(c*u)%p,p,w)-base))
    # non-subgroup control
    random.seed(p)
    S=random.sample([x for x in range(1,p)], n)
    ctrl=0
    for c in [1,3]:
        base=eta(S,c,p,w)
        for u in S[:4]:
            ctrl=max(ctrl,abs(eta(S,(c*u)%p,p,w)-base))
    ok = maxerr<1e-9
    allok = allok and ok
    print(f"n={n:3d} p={p:7d}  subgroup_inv_err={maxerr:.2e} {'OK' if ok else 'FAIL'}  | nonsubgroup_ctrl_err={ctrl:.2e} (should be >>0)")
print("ALL SUBGROUP COSET-INVARIANCE:", "PASS" if allok else "FAIL")
