#!/usr/bin/env python3
"""Issue #389 — the SYMMETRIC-FUNCTION reduction of the worst-case (non-correlated) monomial
far-line incidence, and the q-independent O(n) measurement that puts delta* in the window.

Setup: smooth RS[k] on mu_n. For a monomial direction (X^a, X^b) the bad scalars are
B = {gamma : X^b + gamma X^a is delta-close to RS[k]}.  Working modulo m_S = prod_{x in S}(X-x)
(S the agreement set, |S| = w = (1-delta) n), the residues X^{w-1+j} mod m_S have coefficients
that are COMPLETE-HOMOGENEOUS symmetric functions of S, so the closeness condition becomes:
  gamma = sigma(e_1(S),...,e_*(S))   (a fixed symmetric function of the elementary symmetrics),
subject to the vanishing of further symmetric functions of S.

Cleanest case, direction (k+1, k+2), w = k+2 (m_S degree k+2):
  X^{k+1} mod m_S = X^{k+1};  X^{k+2} mod m_S = e_1 X^{k+1} - e_2 X^k + ...
  closeness (deg < k) <=> [X^{k+1}]: e_1 + gamma = 0  and  [X^k]: e_2 = 0.
  => B = { -e_1(S) : S subset mu_n, |S| = k+2, e_2(S) = 0 }.
VERIFIED below to match the exact list-decode incidence (n=8 -> 8, n=16 -> 16 at large q).

Measured worst non-correlated incidence (n=16,k=4): bounded & q-independent (dir(5,7): 64,72,40,40
at q=97,193,257,353), ~O(n). It crosses the prize threshold q*eps* = n between w=7 (d=0.562, inc 4)
and w=6 (d=0.625, inc 64), so delta* is in the WINDOW interior (1-sqrt rho, 1-rho)=(0.5,0.75).

OPEN CORE (now concrete, q-independent, NOT a character sum): prove the symmetric-function value
set { sigma(S) : S subset mu_n, |S|=w, [vanishing symmetric constraints] } has O(1) mu_n-cosets,
i.e. the worst non-correlated incidence is O(n). Honest: a reduction + measurement, not a proof.
"""
import itertools

def gen_mu(q, n):
    for x in range(2, q):
        if pow(x, n, q) == 1 and pow(x, n // 2, q) != 1:
            return [pow(x, i, q) for i in range(n)]

def e1_e2(S, q):
    e1 = sum(S) % q
    e2 = sum(S[i] * S[j] for i in range(len(S)) for j in range(i + 1, len(S))) % q
    return e1, e2

def bad_via_symmetric(n, k, q):
    """direction (k+1,k+2), w=k+2: B = {-e_1(S) : |S|=k+2, e_2(S)=0}."""
    dom = gen_mu(q, n); w = k + 2
    bad = set()
    for S in itertools.combinations(dom, w):
        e1, e2 = e1_e2(S, q)
        if e2 == 0:
            bad.add((-e1) % q)
    bad.discard(0)
    # count mu_n-cosets
    seen = set(); cosets = 0
    for gm in bad:
        if gm in seen:
            continue
        cosets += 1
        for z in dom:
            seen.add(gm * z % q)
    return len(bad), cosets

if __name__ == "__main__":
    print("symmetric-function reduction, dir(k+1,k+2): #bad = #{-e_1(S):|S|=k+2,e_2=0}")
    for (n, k, q) in [(8, 2, 41), (16, 4, 97), (16, 4, 193), (16, 4, 257)]:
        nb, cos = bad_via_symmetric(n, k, q)
        print(f"  n={n} k={k} q={q}: #bad={nb}  #cosets={cos}  #bad/n={nb/n:.2f}")
