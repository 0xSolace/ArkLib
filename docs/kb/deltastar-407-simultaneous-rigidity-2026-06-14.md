# NOVEL-A advanced: simultaneous odd-system rigidity — mechanism + strong empirics (2026-06-14, wakesync)

Built on the Q1-inequality sharpening (deg H=k-1 char-0; char-p crux = antipodal-free S with the odd
system vanishing mod p). The char-p bad config ⟺ a sign vector ε∈{±1}^{2k} (transversal of antipodal
pairs) with f(x)=Σεᵢxⁱ (deg<2k, ±1 coeffs) satisfying f(ζ^j)≡0 mod p for the r=k/2 odd j=1,3,…,k−1.

## The single-vs-simultaneous DICHOTOMY (verified, probe_simultaneous_rigidity.py)
- SINGLE relation e_1=0 (f(ζ)≡0): char-p FLOPPY. Spurious at p=17 (k=4); at 332/501 primes (k=6).
  [Matches NOVEL-C: a single sum gets dirty; bad primes up to N(f(ζ)) ≤ (2k)^{2k}.]
- SIMULTANEOUS e_1=e_3=0 (2 conds): char-p RIGID. ZERO spurious across 2229 primes (k=4), 501 primes
  (k=6, even non-dyadic), all scanned p. FULL r=k/2 system: ZERO spurious for k=4,6,8,10.

## The MECHANISM (why simultaneous is rigid — clean, not heuristic-only)
char-0: f(ζ)=0 ⟹ Φ_{4k}|f ⟹ f=0 (deg f=2k−1 < φ(4k)=2k). So NO char-0 solution (any char-0 bad
config). char-p spurious needs p | f(ζ^j) for ALL r values simultaneously ⟹ p | gcd-ideal
(f(ζ),f(ζ³),…,f(ζ^{k−1})). For ONE value: bad primes p ≤ N(f(ζ)) ≤ (2k)^{2k} (huge → floppy). For r
values' GCD: heuristic count of solutions ~ 2^{2k}/p^r, so bad-prime threshold p ≲ 2^{2k/r}. At r=k/2
this is **2^4 = 16 = O(1)**, BELOW the dimension floor p > 4k (μ_{4k}⊆F_p ⟹ p≥4k+1). So for k≥4 no
spurious prime can exist at all ⟹ char-uniform rigidity ⟹ Q1 char-p crux CLOSED (no Paley/BGK needed
for THIS face). The single-relation floppiness (NOVEL-C) is IRRELEVANT: the bad config needs the FULL
r=k/2 system, whose bad primes are O(1) ≪ prize q.

## HONEST gaps (why this is strong evidence, NOT a proven closure)
1. The bad-prime threshold 2^{2k/r} is the RANDOM-MODEL heuristic; the real content = the r conditions
   f(ζ^j)=0 are "independent enough" (gcd-ideal trivial / norm O(1)) for ±1 vectors at scale. This
   coprimality-of-f(ζ^j) is concrete number theory — plausibly EASIER than BGK (different object: ±1
   polynomials at roots of unity, not character-sum cancellation) but NOT proven. It could conceivably
   BE the wall in disguise (the "grand unification"); the empirics (0 spurious) say otherwise so far.
2. Empirical k≤10, limited prime ranges (the danger zone p~2^{2k/r}=16 is < 4k so excluded for r=k/2;
   the sharp tests are the r=2 scans at k=6 up to 40000, danger zone ~64 IN range, which passed: 0 spurious).
3. Q1 (the antipodal/char-p-transfer crux) is ONE face; pinning δ* also needs the char-0 incidence count
   + the window. Closing Q1 char-uniformly removes the field-dependence (the headline wall) but is not by
   itself the full δ* pin.

## Net
Advanced the swarm's "single best forward bet" (NOVEL-A): gave the rigidity a clean MECHANISM (simultaneous
⟹ gcd-ideal of f(ζ^j) ⟹ bad primes ≲ 2^{2k/r}=O(1) < dimension floor 4k) and STRONG empirics (0 spurious,
k=4–10; single-relation floppiness confirmed as the contrast). If the coprimality holds at scale, the Q1
char-p crux closes char-uniformly WITHOUT BGK/Paley — the most promising bypass found. The remaining open
content = prove gcd(f(ζ),…,f(ζ^{k−1})) has no prime factor > 4k for ±1 vectors f. NOT a closure; the best
lever, now mechanized + corroborated. probe_simultaneous_rigidity.py.
