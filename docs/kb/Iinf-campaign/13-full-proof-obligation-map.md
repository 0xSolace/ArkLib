# Full proof-obligation map for the "char-0 offset" closure — and why it's already blocked (2026-06-16)

You asked: assuming the n=32 test is positive (char-0 offset stays O(1)≈3), what ELSE must be proven all
around it to make it a real closure? Answer: the chain has **one fatal, already-refuted link** plus two
hard gaps. A positive n=32 would NOT close the prize — it would be a red flag that my object differs from
the true δ* object. Here is the complete obligation list, with status.

## Target theorem
`δ*_prize ≥ δ_we` (the prize FLOOR), via:
`δ*_prize ≥ δ*_char0 = (1−ρ) − offset₀(n)/n`, and `offset₀(n) = o(n/log n)` ⇒ `δ*_char0 ≥ δ_we`.

## The obligations, one by one

### P1 — Monotonicity `δ*_prize ≥ δ*_char0`  ❌ REFUTED (fatal)
- Needed: `#bad_q(line,δ) ≤ #bad_0(line,δ)` (char-p has no more bad scalars than char-0).
- **Status: REFUTED by saturation [issue UPDATE line 11; c.4703145366/50/64].** The bad scalar is a ratio
  `γ = N(S)/D(S) ∈ ℚ(ζ_n)`. When `D(S) ≡ 0 (mod 𝔭)` but `D(S) ≠ 0` in char-0, the reduction does NOT delete
  γ — it SATURATES: the whole far line lies in `C²` mod 𝔭, contributing **excess `I=q`** bad scalars that
  char-0 never had. So `#bad_q` can be `≫ #bad_0`. The monotonicity is false in exactly the regime
  (vanishing denominators / saturation) that the prize prime hits. **This kills the reduction outright** —
  `δ*_prize ≥ δ*_char0` does not hold; the prize can be WORSE than char-0, not better.
- This is the fractional-bad-scalar gap. My CRT engine computes the char-0 count of γ-VALUES and never sees
  the char-p saturation excess (a char-p-only phenomenon). So `δ*_char0` is not even a lower bound on
  `δ*_prize`.

### P2 — `offset₀(n) = o(n/log n)`  ❌ PRECLUDED by the proven ceiling
- Needed: char-0 far-line incidence ≤ budget `n` at agreement `k + o(n/log n)`.
- **Status: contradicts the proven ceiling.** `DeltaStarBracket.lean` proves `δ* ≤ cap − H(ρ)/(β log n)`
  = the window edge. Even granting P1 (which fails), `δ*_char0 ≤ δ*_prize ≤ δ_we` forces
  `offset₀ ≥ offset_we = Θ(n/log n)`. So `offset₀` CANNOT be O(1); the n=8,16 values (3) are the small-n
  manifestation of a `Θ(n/log n)` quantity (n=16: `n/log n = 4 ≈ 3`). **A positive n=32 (offset 3) would
  CONTRADICT the proven ceiling** — meaning my measured object is not the true worst-case δ* object
  (almost certainly because of P3).

### P3 — Worst direction captured  ❌ GAP (monomial ≠ extremal)
- Needed: the max over ALL lines, not just monomial pencils.
- **Status: monomial-extremality REFUTED [c.146].** A general cofactor line `f=X^{10}+cX^9, g=X^8` doubles
  the bad count vs the monomial `X^{10}+γX^8` (8→16 at n=16). So my monomial-only incidence is a strict
  LOWER bound on the true worst; the true `offset₀` is ≥ my measured one. (This is consistent with P2:
  the true offset must be larger — `Θ(n/log n)` — and my monomial undercount makes it look like O(1).)

### P4 — Budget `q·ε* = n`  ✅ definitional (prize regime).

### P5 — The squeeze (what a REAL closure would need)
Even with P1 fixed, P2+ceiling force `offset₀ = Θ(n/log n)` EXACTLY. Combined with the proven ceiling and a
(fixed) monotonicity, you'd get `δ*_char0 = δ*_prize = δ_we` — the prize PINNED. But proving
`offset₀ = (H(ρ)/β)·n/log n` (the char-0 incidence crosses budget exactly at the window edge, worst-case
over all lines including cofactor) **IS the char-0 incidence asymptotic** — and the campaign's fixed-point
theorem says that equals the additive energy = the char-p Gauss-sum = BGK. So P5 is not easier than BGK.

## Net: a positive n=32 does NOT close the prize
- **P1 (monotonicity) is refuted** — the reduction's foundation is gone (saturation excess `I=q`).
- **P2 is precluded** by the proven ceiling — O(1) offset is impossible; offset is `Θ(n/log n)`.
- **P3** — my monomial measurement undercounts the true worst, which is exactly why it *looks* O(1).
- A positive n=32 (offset 3) would therefore signal P3 (object mismatch), not a closure. The honest reading
  is that `offset₀ = Θ(n/log n)` (n=8,16 = 3 ≈ small-n value), the floor is the open BGK quantity, and the
  monotonicity-to-char-0 route is a dead end — I had MISSED that the issue already refuted P1 (the §5.1
  monotonicity) in its 2026-06-14 update.

## What WOULD be needed for a genuine closure (the real obligation list)
1. **Repair or replace the monotonicity** — handle the saturation/vanishing-denominator excess. The
   excess `I=q` happens when the line lies in `C²` mod 𝔭; bounding HOW OFTEN (over the worst line, at the
   window edge) is itself a char-p incidence question. (This is the count/census lane the issue flags as
   "equivalence to §5.0 asserted but never proven.")
2. **Use the true extremal family** (cofactor lines, the WB-pencil ladder / PGL₂ orbit), not monomials.
3. **Prove the char-0 incidence asymptotic** `offset₀ = Θ(n/log n)` with the exact constant — which is the
   additive-energy/BGK object.
All three are the open core. The reduction does not shrink the problem; it relocates it onto the refuted
monotonicity. Honest conclusion: no closure via this route; the prize remains the open BGK wall.

Tools/validation: /tmp/flexb.c (fixed, validated vs Python brute + issue pins). Related: docs 11, 12
(12 contains the retraction of the earlier sentinel-bug claim), issue §4 (ceiling), §5.1 + UPDATE (P1 refutation).
