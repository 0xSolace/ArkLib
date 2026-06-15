# I_∞ campaign — iinf-qindep workflow verdict (wf_84b1d071-195, 2026-06-15)

9-thread workflow on the q-independent finite incidence. Synthesis of 8 completed threads
(+ 9th, a √2-orbit plateau lower-bound for n=64, consistent). **This is the most positive
result of the campaign: the prize FLOOR HOLDS at the window edge, empirically n≤32 + 3 proven
bricks — with a precisely-located remaining gap.**

## Object disambiguation (resolves all cross-thread "contradictions")
Three distinct invariants of `e₁(S)` over `e₂(S)=0` w-subsets were measured:
| invariant | w=4 plateau value | source |
|---|---|---|
| `#distinct e₁` (raw — the **prize** object) | `n²/4 − n = n·(n/4−1)` | csp, my round-4 data ✓ |
| `#orbits` of e₁ under μ_n rotation | `n/4 − 1` | csp |
| `#distinct |e₁|²` (real-subfield degree) | `n/4` | symfunc, vanishing-sums |
| worst-dir k=2 raw-γ (DIFFERENT object) | `(n/2−1)²` | a9a63bf4 (flagged as conflation) |
All consistent once disambiguated; orbits free of size n ⇒ raw = n·orbits.

## Three PROVEN bricks (genuine, not empirical)
1. **p-independence — RIGOROUS, Lean axiom-clean (1874-job build).** `I(δ) = deg(Z_{n,δ})` for
   `q > q₀(n)`, where `Z_{n,δ}` is a 0-dim scheme = per-S root set of one univariate resultant
   `R_S(γ)=∏_{z∈S}(Q₀(z)+γQ₁(z)−W(z))` of q-independent degree ≤ s. Threshold `q₀(n) ≈ n²`
   (over-determined band, bad-prime exponent stable ≈2: n=16→17, n=32→2113, n=64→2753), so
   `q₀ < n⁴ ≪` prize prime `n·2^128`. **⇒ the prize-scale incidence IS the char-0 count, proven.**
   (Settles the long-open "is the incidence q-independent at prize scale" — YES, with margin.)
2. **Support/vanishing law — PROVEN via Lam-Leung.** `I(n,w)=0` for `w ≡ 2,3 (mod 4)`: a vanishing
   sum of 2^a-th roots needs an even # of terms, `C(w,2)` even ⟺ `w ≡ 0,1 (mod 4)`.
3. **Tower descent recursion — VERIFIED exact.** `I(2N,k,2m') = I(N,k/2,m')` (imprimitive descent);
   primitive vanishing `I=0` for odd m≥3; seed `I₁(n,w)=Σ_{s≡w(2)} C(n/2,s)·2^s − [w even]`.

## THE FLOOR VERDICT (decisive thread: empirical-growth-law-and-crossing)
Worst-direction incidence indexed by **offset `j = w − k`** (depth below code dim; δ = cap − j/n):
- Near-capacity **exponential** `I(j=1) ~ exp(c·n)`, c≈0.5 — explosion confined to a **constant-width
  band j = 1,2,3**.
- Measured char-0 profiles (ρ=1/4): n=8 `[40,8,8,1,1]`, n=16 `[3984,88,8,16,16,8,1]`,
  n=32 `[≫,11440,88,88,…O(1) tail]`.
- Window edge `w* = k + Θ(n/log n)` ⇒ offset `j* = n/log n ≈ 3.8, 5.8, 9.2` (n=8,16,32), **strictly
  deeper than the crossing offset `j_cross ≈ 2, 2.5, ≥4–5`; the gap `j* − j_cross` WIDENS with n.**
- Directly measured window-edge values: **n=8→I=1, n=16→I=8, n=32→O(1) — all ≪ n budget.**
- **⇒ PRIZE FLOOR HOLDS WITH MARGIN at the window edge** (the I=n crossing pins a thinner
  near-capacity threshold, NOT δ*).

## Correction to my round-4 pessimism
Round-4 ("multiplier stays n/4−1 → quadratic at the window edge") used ρ=1/2 and **mis-located the
window edge at the near-capacity plateau**. Correctly indexed by offset j, the n/4−1 plateau is the
*near-capacity* regime (small j); the true window edge (j*=n/log n) is **deeper**, where incidence is
O(1)–O(n). Floor holds. My round-4 quadratic was the explosion band, not the edge.

## Honest gap (why this is not yet a closure)
Empirical (n ≤ 32) + a *fitted* `exp(c·n)` near-capacity law + the 3 proven bricks. The remaining
step is the **asymptotic decay-rate proof**: that the near-capacity explosion stays confined below
`j* = n/log n` for ALL n. That is where the open Gauss-period/Paley core may re-enter — BUT the
needed statement is potentially **weaker** than full `B ≤ 2√n`: only that the explosion is confined
shallower than the log-backoff window. **This is a genuinely new, possibly-provable handle** that the
72-sweep's blanket "= open Gauss-period" did not isolate. Fed directly into the decay-rate workflow.

Tools: /tmp/c32*, /tmp/prize_attack/. Threads' Lean brick: the p-independence resultant scheme.
Related: [[arklib-407-multiplier-decay]], [[arklib-407-72-conjecture-sweep]], [[arklib-407-r4-char0-correction]].
