# δ\* → Johnson: ramifications, arguments, and conjectures (essay, 2026-06-15)

## 0. The datum that reframes everything

GPU brute force (validated `cuda-pg` engine, exact char-0, p-independent) pinned the
over-determined worst-direction far-line incidence threshold for smooth-domain RS at ρ=¼:

> **`s*(n) = n/2 + 1 − 2·(⌊log₂n⌋ − 3)`**  (perfect fit, n = 8,12,16,20,24,28,32),
> ⟹ `m* = s*−k = n/4 + 1 − 2(⌊log₂n⌋−3) ~ n/4`,
> ⟹ **`δ*(n) = ½ − 1/n + 2(⌊log₂n⌋−3)/n → ½ = 1−√ρ = Johnson`.**

The single most important rewrite: at ρ=¼, the Johnson agreement is `√ρ·n = n/2`. So

> **`s* = √ρ·n + 1 − 2·(dyadic-tower depth)`**, where dyadic-tower depth = `⌊log₂n⌋−3` = #levels
> in the chain `μ_n ⊃ μ_{n/2} ⊃ … ⊃ μ_8`.

The over-determined combinatorial incidence **re-derives the Johnson radius as its leading term**,
and the *entire* smooth-domain (2-power) enhancement above Johnson is a `+2(log₂n)/n` correction
that **vanishes as n→∞**. The worst direction (for n=2^μ) is **`dir(n/4, 5n/8)`** (verified
n=16→(4,10), n=32→(8,20)), the complete-homogeneous readout, with dilation-orbit size exactly 8.

## 1. Ramifications

**R1 — The combinatorial face saturates at Johnson.** The over-determined / p-independent /
"decoupled-from-BGK" face of the proximity gap (the one we proved characteristic-faithful) does
**not** sustain a window-interior gap; it collapses to the Johnson radius `1−√ρ` with a vanishing
`Θ(log n/n)` bump. Everything strictly beyond Johnson must come from the *under-determined* (BGK
char-sum) band — which sits at *deeper* radii than δ* and therefore (at the validated prime
scale) does **not bind** δ\*.

**R2 — δ\* is pinnable WITHOUT BGK, if the over-det band binds.** Because the binding band is
over-determined (p-independent, validated) and its incidence is a Johnson-main-term + dyadic
correction, **δ\* admits an exact closed form proved from (a) the Johnson/Guruswami–Sudan bound
(known, char-free) and (b) a dyadic-tower/Lam–Leung antipodal count (combinatorial)** — no
square-root cancellation, no Paley/BGK. This *reframes the prize as combinatorial, not analytic*,
contingent on R3.

**R3 — The one remaining gap (honest).** The under-determined band (s=k+1) is p-dependent;
validated p-independence is for s−k≥2 (the binding band). We must confirm that at the *prize*
prime (p≈2¹⁶⁰) the under-det band stays at deeper radii than s* (doesn't overtake the crossing).
At p≈n⁴ it provably doesn't (the engine's δ\* is the over-det value). The leap is p≈n⁴ → p≈2¹⁶⁰.

**R4 — Reconciliation with "the prize is BGK-hard."** Both are true and non-contradictory: the
*beyond-Johnson* content is BGK-hard, but it lives in a band that **does not bind the worst-case
δ\***. The worst-case δ\* is set by the Johnson-saturating over-det band. The months of "it's BGK"
were about the wrong (non-binding) band.

## 2. The structure to prove (the heart)

The exact law decomposes as **Johnson main term `√ρ·n` − dyadic correction `2(⌊log₂n⌋−3)` + O(1)`**.
Proving it = proving two clean statements about the worst direction `dir(n/4, 5n/8)` on μ_{2^μ}:

- **(J)** *Johnson saturation:* the worst-direction over-det incidence `I(s)` crosses the budget
  `n` at agreement `s ≈ √ρ·n` — i.e. the smooth-domain far-line count obeys a Johnson-type law
  with the **same** leading constant as the field-agnostic Johnson bound.
- **(D)** *Dyadic correction:* the deviation from `√ρ·n` is exactly `−2·#levels` of the
  `μ_n ⊃ μ_{n/2} ⊃ …` tower, traceable to the Lam–Leung antipodal/even-parity structure of
  vanishing sums of 2-power roots of unity (each tower level contributes one antipodal halving).

Both are **combinatorial, char-0, and (we conjecture) provable** with existing tools
(Guruswami–Sudan + Lam–Leung + the in-tree coset-saturation lemmas).

## 3. What has never been explored (but could be)

1. **The Johnson bound as an EQUALITY (not just an upper bound) for smooth domains.** GS gives
   `δ_J ≤ 1−√ρ` as a *sufficient* radius. Nobody has computed the *exact* far-line incidence
   crossing for a *structured* domain and found it equals Johnson + an explicit lower-order term.
   The GPU law is exactly this. The smooth domain makes the Johnson bound *tight with a computable
   defect*.
2. **2-adic valuation as the carrier of the beyond-Johnson gap.** The correction is `2·v`-flavored
   (powers-of-2 stalls). No prior work ties the proximity-gap defect-above-Johnson to the 2-adic
   tower depth. This is a genuinely new structural handle (and explains why the prize regime —
   pure 2-power μ_n — is special).
3. **The worst direction is the complete-homogeneous readout `(n/4, 5n/8)`, not the tower
   `(k,k+t)`.** A2's analytic model failed precisely by guessing the tower. The actual extremal
   direction is a specific symmetric-function readout — its incidence is a single, writable
   dyadic-sumset count.
4. **δ\* as a function approaching Johnson from ABOVE with a log-bump peak.** The non-monotone
   peak (≈0.594 at n=32) then descent is unexplored; it may encode the optimal n for a *finite*
   construction (where the beyond-Johnson margin is maximal) — directly useful for real FRI/STARK
   parameter choice.
5. **Cross-domain: this is a "Johnson + arithmetic defect" phenomenon** that may recur for other
   structured evaluation sets (multiplicative subgroups of other smooth orders, additive
   subgroups/subspaces). The 2-adic case is the cleanest; a general "tower-depth defect" law could
   exist.

## 4. Why this is the right target now

The prize asks to *pin δ\* in the window, worst-case, with a closed proof reducing to known math*.
The GPU law DOES pin it (exact closed form) and DOES suggest a reduction to known math (GS +
Lam–Leung), with one honest gap (R3, the p-scale leap for the non-binding band). This is the first
route in the whole campaign that is **combinatorial end-to-end** for the *binding* band. The 100
arguments and conjectures below attack: (J), (D), the worst-direction characterization, and R3.
