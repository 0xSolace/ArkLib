#!/usr/bin/env python3
"""
probe(#389): the 2-adic FFT-butterfly recursion for the dyadic subgroup character sum, and the
transfer-cocycle / Lyapunov reframing of the open sup-norm core.

Let S_k(t) = sum_{j=0}^{2^k-1} e_p(t * zeta^j),  zeta = primitive 2^k-th root of unity in F_p.
This is the character sum whose SUP over t is the prize's open core (the L^infty Shaw error; the
average is sqrt(n) by Parseval, the sup is conjecturally <= C sqrt(n log n) but unproven for
n = p^{1/5}, far below Weil's sqrt(q) and only n^{1-nu} from BGK).

VERIFIED IDENTITY (this probe, errors ~1e-15):
    S_k(t) = S_{k-1}(t) + S_{k-1}(t * zeta_k)          [the FFT butterfly on mu_{2^k}]
because mu_{2^k} = mu_{2^{k-1}}  (union)  zeta_k * mu_{2^{k-1}}  (even/odd cosets, DISJOINT), so the
L^2 cross-term Sum_t S_{k-1}(t) conj(S_{k-1}(t zeta_k)) = 0 exactly => Parseval avg|S| = sqrt(n).

REFRAMING (the attack route): iterate the butterfly. Writing the pair V_{k}(t)=(S_k(t), S_k(t w))
for a suitable rotation w, the recursion is a product of 2x2 TRANSFER MATRICES driven by the
2-adic digits of the frequency. Hence
    sup_t |S_k(t)|  ~  2^{ k * (Lyapunov exponent of the transfer cocycle) }.
Square-root cancellation  <=>  Lyapunov exponent = (1/2) log 2  (the L^2 / Parseval value), i.e. the
cocycle is "non-resonant" (no frequency aligns all k butterfly levels constructively). This is
EXACTLY the renormalization framework for the VALUE DISTRIBUTION of incomplete theta/Gauss sums
(Marklof; Demirci Akarsu-Marklof 2012, reading-list O4 arXiv:1207.1607; Cellarosi-Marklof). Their
limit laws give the *distribution* of S_k(t)/sqrt(n); the prize needs the *sup* (a large-deviation /
maximal-Lyapunov statement), which is the precise open gap.

NOT a closure: the maximal Lyapunov exponent being (1/2)log2 (rather than larger on a sparse
resonant set of t) is the square-root-cancellation conjecture restated, still open. This probe
records the exact identity + the renormalization attack surface, connecting the open core to a
developed analytic-number-theory machinery.
"""
import sympy, math
import numpy as np

def S(t, p, zeta, n):
    powers = [pow(int(zeta), j, p) for j in range(n)]
    ang = 2*math.pi*np.array([float((t*pw) % p) for pw in powers])/p
    return complex(np.sum(np.exp(1j*ang)))

def main():
    p = 1073741953
    print("Verifying  S_k(t) = S_{k-1}(t) + S_{k-1}(t*zeta_k)  (exact FFT butterfly):")
    for k in (4, 6, 8):
        n = 1 << k
        g = int(sympy.primitive_root(p)); zk = pow(g, (p-1)//n, p); zkm1 = pow(zk, 2, p)
        err = 0.0
        for t in (1, 7, 12345, 999999, p-3):
            lhs = S(t, p, zk, n)
            rhs = S(t, p, zkm1, n>>1) + S(t*zk % p, p, zkm1, n>>1)
            err = max(err, abs(lhs - rhs))
        even = {pow(zkm1, j, p) for j in range(n>>1)}
        odd = {(zk*pow(zkm1, j, p)) % p for j in range(n>>1)}
        print(f"  k={k} n={n}: max|err|={err:.1e}  even/odd-coset disjoint={len(even & odd)==0}")
    print("=> exact identity; open core = transfer-cocycle Lyapunov exponent = (1/2)log2 (square-root cancellation).")

if __name__ == "__main__":
    main()
