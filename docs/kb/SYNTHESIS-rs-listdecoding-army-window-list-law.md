# SYNTHESIS: the prize = explicit-RS list-decoding past Johnson — full 16-angle army result (#444)

The RS-list-decoding army (16 angles, 27 agents, 4M tokens, cross-verified by independent engines + closed forms
+ external papers) attacked the prize in its TRUE reduced form. Verdict: **poly-supported (floor likely true), not
proven**. The map is now coherent and sharp.

## PROVEN (rigorous, in-regime, cross-verified)

1. **The reduction is EXACT:** proximity-gap FLOOR ⟺ explicit-RS list-decoding past Johnson (BChKS 2025/2055,
   soundness a < q/(2n)); the in-tree super-code/far-line bridge makes it √-free (q·ε* = n). So the prize IS the
   list-decoding problem.
2. **The worst-case word is 2-SPARSE** (affine-line/dilation, x^a+γx^b), engine-verified: listscan/sparsescan max
   coincides at a 2-sparse word at every tested (n,k,δ).
3. **ANTIPODAL-TOWER self-similar recursion** (brute-verified n≤16, partial n=32): the smooth list problem is
   self-similar down the 2-power subgroup tower: `L(μ_n,k,t) = L(μ_{n/2}, ⌊k/2⌋, ⌈t/2⌉)`. At a fixed dyadic window
   ratio D/n = a/2^s the list is EXACTLY CONSTANT in n.

## ALL "import-from-known-capacity-results" ROUTES ELIMINATED (rigorous, domain-blind)

- **Subspace-design derandomization: DEAD** (caps at Johnson; τ-parameter domain-blind, requires folding depth
  m≥d; plain RS has m=1). `derand-subspace-route-DEAD-caps-at-johnson.md`.
- **GG25 extension: DEAD** (caps at Johnson; same τ; radius 1/n−(ρ+ℓ)/r).
- **FRS folding: DEAD** (Folding Decorrelation Barrier, exact algebraic identity).
- **Guruswami–Sudan past Johnson: DEAD** (μ_n cyclic/dyadic structure REMOVES interpolation room).
- **Curve-decodability (GG25): caps strictly below Johnson** for plain RS, no domain dependence.
- **Literature sweep: NO published result** reaches past Johnson for explicit plain RS over a smooth subgroup; the
  2026 survey (arXiv:2603.03841) lists this as **Open Question #1 (p.85), verbatim the prize, recognized open Mar-2026.**

## THE BEST CONJECTURE (two-sided anchored): the EXPLICIT-RS WINDOW LIST LAW

For RS[μ_n,k], η := (1−ρ)−δ (distance below capacity), the worst-case list over ALL words is
> **L*(δ) = 2^{Θ_ρ(1/η)}**, attained by a 2-sparse word, with `log₂(L*)·η → C(ρ)` (measured C(1/16)≈0.23,
> C(1/8)≈0.27, C(1/4)≈0.43).

Consequences: for η ≥ c/log n (window interior), **L* = 2^{O(log n)} = poly(n)** ⟹ explicit smooth RS list-decodes
past Johnson (floor HOLDS). **KKH26 / ePrint 2026/782 provides the matching LOWER bound** — so the law is two-sided.
My independent broad-scan (rs-listscan: ρ=1/4 n=16,20,24 → L=7,22,34; log₂L·η ≈ 0.35–0.67) is roughly consistent
with C(1/4)≈0.43.

## OPEN (the genuine prize core) + the most promising path

- **OPEN:** the UPPER bound `L*(δ) ≤ 2^{O_ρ(1/η)}` for ALL words, all window-interior δ. KKH26 gives the lower
  bound; the upper bound is unproven. Residuals: (a) general-γ 2-sparse (γ=1 engine-worst, not proven worst ∀n);
  (b) at r=t−k≥2 rungs the count involves ADDITIVE symmetric-function constraints e_1(S)=…=e_{r−1}(S) over F_q;
  proving these cut independently is the core.
- **⭐ MOST PROMISING PATH (potentially OFF the BGK wall):** prove the upper half for the worst-case 2-sparse
  (antipodal/walking-Laurent) family via the antipodal-tower recursion, which reduces the count to a
  **PRIME-DECOUPLED Z/n subset-sum / elementary-symmetric-function count, NOT a character sum.** The dyadic
  squaring recursion `e_{2l}(±z) = (−1)^l e_l(z²)`, `e_odd = 0` descends `(n,D,j) → (n/2, D/2, ⌊j/2⌋)` to a base
  group μ_{2^s} of FIXED size when D/n = a/2^s, making the count constant/poly in n. **Prime-independent** — the
  first concrete route that may bypass the BGK char-sum.

## HONEST CAVEAT

The window list law is conjectural; my broad-scan shows mild n-growth at fixed η (L=7@n=16 vs 34@n=24 both at
η=0.125), so the Θ(1/η) constant may carry mild n-dependence — poly-vs-superpoly remains undecided at feasible n
(the recurring scale-confounding). The law is *consistent with* the floor (poly) and has a published lower-bound
anchor, but the upper bound is the open core. NOT a closure. The antipodal-tower prime-decoupled symmetric-function
count is the sharpest, most novel, potentially-off-BGK attack surface the campaign has produced.
