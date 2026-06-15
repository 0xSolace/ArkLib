#!/usr/bin/env python3
"""
probe_a2_mann_crossing_pin.py   (#444 TASK A2 -- Mann/antipodal pin of char-0 incidence AT THE CROSSING)

Question (A2): the worst-case char-0 incidence I_0(delta) crosses budget=n at band w_cross
(=> delta* = (n - w_cross)/n).  Is I_0 AT (and around) the crossing derivable EXACTLY from
antipodal-pairing (Mann/Conway-Jones) combinatorics?  If yes => delta* closes via Mann (PROVEN).

Setup (in-tree governing law, exact; prize direction p >> n^3 => char-0-faithful):
  RS[mu_n, k], n=2^mu.  Monomial pencil (a,b), a<b, a,b in [k, n-1].
  Inner: I_0(a,b; w) = #{ gamma!=0 : x^a + gamma x^b agrees with some deg<k poly on >= w pts of mu_n }.
  Worst over directions.  Crossing band w_cross = smallest w with worst I_0 <= budget=n; delta*=(n-w)/n.

IMPORTANT (reconciliation, this probe).  The established ground-truth delta* (gt={(8,2):0.375,
(8,4):0.25,(16,4):0.5625,(16,8):0.3125}) is realized by the WORST direction, which at the boundary
is the a=n/2 antipodal-coset generator (e.g. (n/2, n/2+1)).  So we DO include a=n/2 directions
(the task's "!= n/2" exclusion gives a STRICTLY larger delta* / smaller w_cross and disagrees with
gt -- reported in the FAR_NO_HALF row for contrast).  Both conventions reported.

(k+1)-subset solve (prime-size-independent): for each (k+1)-subset solve for (g, gamma); record
gamma -> max full-domain agreement and one max witness set R.  De-dup gamma.

A2 CLASSIFICATION at/around the crossing: for each gamma reaching agreement >= w we test the BEST
witness set R for
  antipodal_closed(R): all j in R have (j+n/2) in R  (Mann: only primitive 2-power vanishing rel. is z-z=0)
  coset_full(R): R is a union of full cyclotomic cosets of sub-2-groups.
Mann_anti(w)=#gamma with antipodal-closed best R.  Ask: Mann_anti(w_cross)==I_0(w_cross)?
Compare w_cross-k to log2(n).
"""
import itertools, math, sys

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True
def find_prime(n, lo):
    p = lo + (n - (lo % n)) + 1
    while True:
        if (p - 1) % n == 0 and is_prime(p): return p
        p += n
def prim_root(p):
    fac = []; m = p - 1; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac): return g
def rou(p, n):
    g = prim_root(p); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]
def solve(M, bvec, p):
    m = len(M); A = [row[:] + [bvec[i]] for i, row in enumerate(M)]; r = 0
    for c in range(m):
        piv = None
        for i in range(r, m):
            if A[i][c] % p != 0: piv = i; break
        if piv is None: return None
        A[r], A[piv] = A[piv], A[r]; inv = pow(A[r][c], p-2, p); A[r] = [(v*inv)%p for v in A[r]]
        for i in range(m):
            if i != r and A[i][c] % p != 0:
                f = A[i][c]; A[i] = [(A[i][j]-f*A[r][j])%p for j in range(m+1)]
        r += 1
    return [A[i][m] % p for i in range(m)]
def antipodal_closed(R, n):
    Rs = set(R); h = n // 2
    return all(((j + h) % n) in Rs for j in R)
def coset_full(R, n):
    """R is a union of full cyclotomic cosets of some sub-2-groups (covers every elt of R)."""
    Rs = set(R); covered = set()
    for d in range(2, n+1):
        if n % d: continue
        step = n // d
        for start in range(step):
            cs = set((start + step*t) % n for t in range(d))
            if cs <= Rs: covered |= cs
    return covered == Rs and len(Rs) > 0

def gamma_map(mu, a, b, k, p, n):
    powr = [[pow(mu[i], j, p) for j in range(k)] for i in range(n)]
    za = [pow(mu[i], a, p) for i in range(n)]
    zb = [pow(mu[i], b, p) for i in range(n)]
    seen = {}
    for A in itertools.combinations(range(n), k+1):
        M = [powr[i] + [(-zb[i]) % p] for i in A]; rhs = [za[i] for i in A]
        sol = solve(M, rhs, p)
        if sol is None: continue
        gamma = sol[k]
        if gamma == 0 or gamma in seen: continue
        g = sol[:k]
        R = []
        for i in range(n):
            gi = 0; xi = mu[i]
            for j in range(k-1, -1, -1): gi = (gi*xi + g[j]) % p
            if gi == (za[i] + gamma*zb[i]) % p: R.append(i)
        seen[gamma] = (len(R), tuple(R))
    return seen

def crossing(mu, a_set, k, p, n, budget):
    band_I = {w: 0 for w in range(k+1, n+1)}
    band_anti = {w: 0 for w in range(k+1, n+1)}
    band_dir = {w: None for w in range(k+1, n+1)}
    for a in a_set:
        for b in range(k, n):
            if a >= b: continue
            gm = gamma_map(mu, a, b, k, p, n)
            for w in range(k+1, n+1):
                cnt = 0; canti = 0
                for gamma, (ag, R) in gm.items():
                    if ag >= w:
                        cnt += 1
                        if antipodal_closed(R, n): canti += 1
                if cnt > band_I[w]:
                    band_I[w] = cnt; band_anti[w] = canti; band_dir[w] = (a, b)
    w_cross = next((w for w in range(k+1, n+1) if band_I[w] <= budget), None)
    return band_I, band_anti, band_dir, w_cross

def analyze(n, k, gt=None):
    rho = k/n
    p = find_prime(n, n**3 * 8)
    mu = rou(p, n)
    budget = n; half = n//2
    full_a = list(range(k, n))                       # includes n/2 (the gt-realizing convention)
    nohalf_a = [x for x in range(k, n) if x != half] # task's "!= n/2" convention
    bI, bA, bD, wc = crossing(mu, full_a, k, p, n, budget)
    _, _, _, wc_nh = crossing(mu, nohalf_a, k, p, n, budget)
    dstar = (n - wc)/n if wc else None
    cap = 1 - rho
    print(f"\n=== n={n} k={k} rho={rho:.4f} p={p} budget={budget}  (a,b in [k,n), worst dir; INCLUDES a=n/2) ===")
    print(f"{'w':>3} {'delta':>7} | {'I_0':>6} {'Mann_anti':>9} | {'Mann==I0?':>9}  dir")
    for w in range(k+1, n+1):
        if bI[w] == 0: continue
        mk = "  <== CROSSING" if w == wc else ""
        match = "EXACT" if bA[w] == bI[w] else f"anti<I0 ({bA[w]}/{bI[w]})"
        print(f"{w:>3} {(n-w)/n:>7.4f} | {bI[w]:>6} {bA[w]:>9} | {match:>9}  {bD[w]}{mk}")
    if wc:
        gmatch = (abs(dstar - gt) < 1e-9) if gt else "?"
        print(f"  delta* = {dstar:.4f}   gt={gt}  MATCH_gt={gmatch}")
        print(f"  w_cross-k = {wc-k}   log2(n) = {math.log2(n):.1f}   log2(n)-match = {(wc-k)==round(math.log2(n))}")
        print(f"  CROSSING Mann-pin: I_0={bI[wc]} Mann_anti={bA[wc]} -> "
              f"{'MANN CLOSES (antipodal)' if bA[wc]==bI[wc] else 'MANN UNDERCOUNTS'}")
        print(f"  [no-half convention crossing band = {wc_nh} (delta*={(n-wc_nh)/n:.4f}); "
              f"{'agrees with gt' if wc_nh==wc else 'DISAGREES with gt -> a=n/2 is load-bearing'}]")
    return dict(n=n, k=k, rho=rho, wc=wc, dstar=dstar, cap=cap,
                I0=bI[wc] if wc else None, anti=bA[wc] if wc else None,
                wk=wc-k if wc else None, log2n=math.log2(n), gt=gt,
                mann=(bA[wc]==bI[wc]) if wc else None)

def main():
    GT = {(8,2):0.375,(8,4):0.25,(16,4):0.5625,(16,8):0.3125}
    cases = [(8,2),(8,4),(16,2),(16,4),(16,8)]
    if len(sys.argv) > 1:
        cases = [tuple(int(x) for x in sys.argv[1].split(','))]
    rows = [analyze(n,k,GT.get((n,k))) for (n,k) in cases]
    print("\n===== A2 SUMMARY =====")
    print(" n  k  rho     wc  delta*   gt      I0_cr anti_cr  Mann?  wc-k  log2n  log2-match")
    for r in rows:
        if r['wc'] is None: continue
        print(f"{r['n']:3d}{r['k']:3d} {r['rho']:5.3f} {r['wc']:3d}  {r['dstar']:.4f}  {str(r['gt']):>6}  "
              f"{r['I0']:4d}  {r['anti']:5d}   {'YES' if r['mann'] else 'NO ':>3}  {r['wk']:3d}  {r['log2n']:5.1f}  "
              f"{'YES' if r['wk']==round(r['log2n']) else 'NO'}")

if __name__ == "__main__":
    main()
