import itertools, random
from collections import Counter
def find_prime_root(n):
    p=n*n
    while True:
        p+=1
        if all(p%d for d in range(2,int(p**0.5)+1)) and (p-1)%n==0:
            for g in range(2,p):
                if pow(g,n,p)==1 and pow(g,n//2,p)!=1: return p,g
def add_energy(P,p):
    # E = #{(a,b,c,d) in P^4 : a+b=c+d} = sum_s r(s)^2, r(s)=#{(a,b): a+b=s}
    cnt=Counter()
    for a in P:
        for b in P: cnt[(a+b)%p]+=1
    return sum(v*v for v in cnt.values())
def list_at(pts,k,a,w,p):
    n=len(pts); cset=set()
    for Tk in itertools.combinations(range(n),k):
        full=[]
        for jx in range(n):
            tot=0
            for idx,i in enumerate(Tk):
                num=1;den=1
                for i2 in Tk:
                    if i2!=i: num=(num*(pts[jx]-pts[i2]))%p; den=(den*(pts[i]-pts[i2]))%p
                tot=(tot+w[i]*num*pow(den,p-2,p))%p
            full.append(tot)
        if sum(1 for jx in range(n) if full[jx]==w[jx])>=a: cset.add(tuple(full))
    return len(cset)
def lowdeg(pts,d,co,p): return [sum(co[t]*pow(pts[i],t,p) for t in range(d+1))%p for i in range(len(pts))]
def worst(pts,k,a,p,trials,seed=11):
    n=len(pts); rnd=random.Random(seed); best=0
    for _ in range(trials):
        if rnd.random()<0.5:
            cs=[lowdeg(pts,k-1,[rnd.randrange(p) for _ in range(k)],p) for _ in range(rnd.randint(2,5))]
            w=[cs[rnd.randrange(len(cs))][i] for i in range(n)]
        else:
            w=lowdeg(pts,a,[rnd.randrange(p) for _ in range(a+1)],p)
        best=max(best,list_at(pts,k,a,w,p))
    return best
print("Energy-list conjecture L <= E(eval)/n  test:")
print(f"{'n':>3}{'k':>3}{'a':>3} {'domain':>10}{'E':>10}{'E/n':>8}{'L_worst':>9}{'L<=E/n?':>9}")
for n in [8,16]:
    p,g=find_prime_root(n)
    muN=[pow(g,j,p) for j in range(n)]; add=[i%p for i in range(n)]
    rndset=random.Random(2).sample(range(1,p),n)
    for k in [2,3]:
        if k>=n: continue
        a=k+1
        for name,P in [("mu_n",muN),("additive",add),("random",rndset)]:
            E=add_energy(P,p); L=worst(P,k,a,p,2000 if n<=8 else 1500)
            print(f"{n:>3}{k:>3}{a:>3} {name:>10}{E:>10}{E//n:>8}{L:>9}{str(L<=E/n):>9}")
