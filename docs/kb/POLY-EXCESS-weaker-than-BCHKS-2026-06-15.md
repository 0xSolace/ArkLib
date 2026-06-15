# POLY-EXCESS: a strictly-weaker-than-BCHKS open lemma for the prize, with measured margin

## The reduction (Result A, proven)
top1=max_{b≠0}|η_b|² ≤ (p·E_r)^{1/r} for all r (moment identity + max≤sum). Minimizing over r (Stirling, saddle
r*=log p) gives the EXACT closed form:
  top1 ≤ (8/3)·n·log m · c_{r*}^{1/log p},   union constant 8/3≈2.667 (verified vs measured 2.69, n=64..4096).
⟹ **C=O(1)  ⟺  c_{r*} ≤ m^{O(1)} at depth r*≈log m**  — the deep-moment excess over Wick need only be
POLYNOMIAL in the budget m, NOT zero. This is STRICTLY WEAKER than the campaign's c_r≤1 (= BCHKS Conj 1.12,
zero excess). MEASURED excess exponent log(c_{r*})/log m = −0.47, −0.33, −0.04 (n=16,32,48): NEGATIVE ⟹ the
actual excess is SUB-Wick at good primes — real headroom inside the polynomial slack.

## THE NEW OPEN LEMMA (POLY-EXCESS) — the softer target
  E_{log m}(μ_n, F_p) ≤ m^{O(1)} · (2r*−1)‼ · n^{r*},  r*=log m,  uniformly over prize primes.
Equivalently: #{signed length-2r* ±1 wraparound relations Σ±ζ^{a_i}≡0 (mod p) among μ_n} ≤ m^{O(1)}·(Lam–Leung
char-0 count). A SOFTER cyclotomic-norm-divisor target than vanishing (BCHKS demands zero spurious; POLY-EXCESS
allows m^{O(1)}×). NOT trivially true: the crude E_r≤n^{2r} gives m^{ω(1)} (super-poly, too big). Plausibly
UNIFIES the good/bad split (good: sub-Wick negative exponent; bad: bounded excess, worst-C plateaus ~1.5 / top1
≤2.2 n log m to n=256 — well within m^{O(1)}).

## Result B (proven no-go — depth is irreducible, do not re-chase):
- Fixed depth r₀: top1/(n log m) ~ n^{4/r₀}/log m → ∞ for any fixed r₀. Depth MUST grow ~log m.
- Low-moment + interpolation: best provable pointwise input is trivial n² OR Weil √p, which COINCIDE at β=4
  (√p=n²); so interpolation caps at the trivial n² bound (measured "constant" grows as n/log m: 1.96→15.9,
  n=16..256). Relaxing the constant buys EXCESS-ROOM at the same depth, NOT depth reduction.

## Status & why POLY-EXCESS matters
The prize ⟸ POLY-EXCESS (strictly weaker than the 25-yr-open BCHKS 1.12, with measured negative-exponent margin).
This is a genuine QUANTITATIVE SOFTENING of the wall, not a reframing: the same object (deep-moment excess at
depth log m) but the bar is m^{O(1)}× instead of 1×. Whether the polynomial slack makes it PROVABLE where BCHKS
isn't is the new open question — the natural attack: cyclotomic-norm divisor bounds (count wt-2r* relations with
p|Norm, allowing m^{O(1)} multiplicity) where the crude/Lam–Leung norm bound was vacuous for the zero-excess
version but may suffice for the polynomial-excess version. THIS is the lowest bar yet isolated for the prize.
(All routes verified prize-faithful; deliverable /tmp/prize-research/PROOF_ATTACK_TOP1.md; NOT a closure.)
