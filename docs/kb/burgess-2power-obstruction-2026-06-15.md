# Why the 2-power/shifted structure does NOT cross Burgess — precise obstructions (2026-06-15)

The shifted-subgroup Paley sum S(χ)=Σ_{ζ∈μ_n}χ(1+ζ) (= multiplicative dual of M(n), SAME wall) attacked
from 6 angles + literature. NO crossing of the Burgess barrier (n=p^{1/4}). Precise obstructions found:

## Two new exact 2-power identities (genuine, but yield no bound)
1. **1+μ_n is MULTIPLICATIVELY SIDON:** E_×(1+μ_n)=2N²−N (N=n−1) — the order-2 multiplicative energy is at
   its MINIMUM. But this minimality does NOT propagate to depth k~log p: the k-fold energy J_k EXPLODES
   (measured 28× by k=8 at μ=5) because of the exact norm relation **∏_{ζ≠−1}(1+ζ)=±n**. THE precise
   obstruction: the depth-log energy (what the moment method needs) is forced large by the norm relation.
2. **Σ_{ζ∈μ_n}χ(1−ζ)χ(1+ζ)=2·S_{n/2}(χ)** (from (1−ζ²)=(1−ζ)(1+ζ), re-verified ≤6e-8): clean self-similar
   descent, but the WRONG way (level n/2 → bilinear in level n); Cauchy-Schwarz gives only the trivial ≤n.

## Why each 2-power-specific lead dies (precise)
- **Squaring/dyadic recursion → triangle inequality only.** The worst χ phase-ALIGNS the two cosets
  (cos≈+1.0); the cancellation/orthogonality holds only in the L²-AVERAGE (Parseval), not for the worst χ.
- **Shifted Stepanov is WORSE than additive.** (X−1)^n−1 is squarefree, its exact mod-p condition-rank is
  FULL (degeneracy 0 for M=2,3,4) — NO high-order vanishing to exploit (vs the additive set's 2 relations).
- **Weil/curve is DIMENSIONALLY VACUOUS — and this IS why Burgess is a barrier.** μ_n is 0-dimensional (n
  points); the Weil bound √p = n² is exactly p^{1/4} = n-TOO-BIG. The "n<√q ⟹ Weil vacuous" obstruction is
  the structural origin of the Burgess barrier at p^{1/4}.

## Literature SOTA (confirmed precise)
Shifted-subgroup sums = Fourier dual of additive, IDENTICAL BGK/sum-product machinery, NO better exponent.
di Benedetto-Garaev (arXiv:2003.06165) H^{1−31/2880}=H^{0.98924} valid ONLY H>p^{1/4} STRICTLY (vacuous at
barrier by hypothesis); at exactly p^{1/4} only Bourgain-Garaev H^{0.99998} (saving ~1.85e-5). Paley Graph
Conjecture OPEN for density ≤1/2 (Hanson-Petridis clique bound is β=2, nothing at β=4). Target √(n log m) is
a full HALF-power below all unconditional bounds at β=4. Exact re-verify (all χ): max_χ|S|=3,6.99,14.5,25.4,
43.5 (n=4..64), ratio to √(n log m)=0.74→1.54 (climbs past √2, finite-size/2-adic artifact, M/S within ~10%).

## Net
The 2-power/shifted/Paley framing opens NO unconditional crack — same Burgess-barrier wall. The precise
obstructions (norm-relation forces depth-log energy large; squaring phase-aligns; Stepanov full-rank;
Weil 0-dimensional-vacuous) explain WHY at the structural level, sharpening the dead ledger. The two exact
identities (mult-Sidon, (1−ζ²) descent) are reusable facts. Probe: this session.
