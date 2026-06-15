# Recursive μ_{n/2} attack — FINAL verdict (Phase 6 + recursion workflow, judges taken over)

## The clean char-0 result (genuine, recordable brick)
The 2-power additive-energy telescopes EXACTLY in char-0 (verified to n=64, out-of-sample):
  E_r(μ_{2^a}) = 2^r·E_r(μ_{2^{a-1}}) + CROSS_r(n),  base E_r(μ_2)=C(2r,r),
giving the closed forms (Δ_top = the char-0 cross-energy, CONTROLLED/clean per level):
  E_2 = 3n²−3n ; E_3 = 15n³−45n²+40n ; E_4 = 105n⁴−630n³+1435n²−1155n ; E_5 = 945n⁵−…
  leading coeff = (2r−1)!! = the Gaussian/Wick value, EXACTLY, for all r.
This extends the in-tree Lam–Leung r=2 value (3n²−3n) to ALL r via the explicit 2-power recursion,
with the cross-term Δ_top vanishing/clean at every level (e.g. F-strikes: the cross(ee,oo) bucket = n²/2).
So in CHAR 0 the recursion telescopes to the Wick value ⟹ IF it held in char-p at r≈log q it would give
B ≤ √(2n log q) = the prize. It is the cleanest the structure comes.

## Why it does NOT close the prize (3 decisive obstructions, all proven this round)
1. **char-0 ≠ char-p.** The strikes computed E_r^char0 (ℤ[ζ] antipodal vanishing). The prize needs E_r(mod p)
   at r≈log q; the char-p EXCESS appears past the Mahler clean range r<(1/2)p^{2/n} (vacuous at prize scale),
   and it BREAKS the telescoping. The clean char-0 Δ_top=0 is NOT the char-p Δ_top (the open core).
2. **Realizability telescopes to EXPONENTIAL.** The core-realizability subset-sum Σpᵢ²=e_2(C) in μ_{n/2}
   telescopes (clean, q-indep) to the fixed point 3^{n/4} — EXPONENTIAL, because Lam–Leung makes the n/4
   antipodal-pair contributions additively INDEPENDENT. Does NOT bound #orbits/I_∞ polynomially.
3. **Fold √2-loss IRRECOVERABLE.** (F9, exact mod-p rank) the singleton does NOT halve: each singleton adds
   exactly one independent constraint, k singletons pin a deg-<k poly ⟹ singleton stays full-degree on the
   half-length transversal. The transversal is an ARC, not a subgroup (n/2 even ⟹ μ_{n/2} = union of whole
   fibers, never a transversal) ⟹ there is provably NO second coprime fold to capture it. Ratio = √2 exactly
   at a=3,4,5, every ρ. To cross Johnson one must beat factor 2 via μ_{n/2} multiplicative structure on the
   singleton arc, but the arc is provably NON-multiplicative.

## #orbits at the window edge (orbits workflow, 7 refute / 1 polylog)
#orbits = Θ(n) at the window edge (char-0) — TAUTOLOGICAL at the crossing (I_∞=n ⟹ #orbits=n/orbit_size),
consistent with the crossing being at the window edge, but the growth LAW that pins the crossing location
reduces to the same recursive cross-term = the open char-p excess.

## Net
The 2-power recursion is self-similar and bottoms out trivially IN CHAR 0, where it telescopes to the exact
Wick energy (clean, recordable). But the prize lives in char-p at r≈log q, and every route — char-p excess,
the exponential realizability subset-sum, the irrecoverable √2 singleton arc — hits the SAME irreducible wall.
No closure. The campaign's deepest, most self-similar attack confirms the open core with maximal precision.
