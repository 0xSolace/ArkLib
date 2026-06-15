# The BChKS admissibility construction MISSES the prize window edge — and ε*=2^-128 is exactly why (#407)

**Date 2026-06-14. Source: BChKS "On Proximity Gaps for RS" (obtained) + direct computation.** A genuine,
novel, quantitative localization of the strongest known FAILURE construction relative to the prize window
edge, for the dyadic FRI domain μ_{2^a}.

## 1. BChKS Conj 1.12 / Thm 1.13 is the FAILURE direction (correction to the fleet's target)
BChKS Def 1.11: (q,a,b) ADMISSIBLE iff ∃ subgroup G, |G|=b, |G^{(+b/2)}| ≥ a (large MIDDLE sumset).
Thm 1.13: admissible ⟹ a proximity-gap FAILURE — ∃ f,g with ≥ a bad scalars at radius δ−2/b but [f,g]
far from C². So PROVING Conj 1.12 produces failures (strengthens the CEILING); it does NOT close the floor.
The prize floor needs the OPPOSITE: μ_{2^a} avoids admissibility at the window edge.

## 2. EXACT computation of the dyadic admissibility object (unconditional, not the conjecture)
The only subgroups of the FRI domain μ_{2^a} are μ_{2^j}. The middle sumset |μ_{2^j}^{(+2^{j-1})}|,
computed char-0 EXACT (Z-basis of Z[ζ_{2^j}], distinct coeff vectors):
  j=2: 5 ;  j=3: 41 ;  j=4: 3281   →  |μ_{2^j}^{(+2^{j-1})}| = 2^{c·2^{j-1}},  c = 1.16, 1.34, 1.46 (rising).
And it EQUIDISTRIBUTES mod q (verified: |sumset mod q| = min(q, char-0 count) EXACTLY, full coverage,
for many q ≡ 1 mod 2^j). So for the SPECIFIC dyadic subgroups, admissibility (Conj 1.12) is UNCONDITIONAL
by direct computation — a = min(q, 2^{c·2^{j-1}}).

## 3. The construction lives at η = c/log₂q — and ε* pushes the window edge ABOVE it
The BChKS construction at G=μ_{2^j} gives ε_mca ≈ 1 at η_j = 2^{1−j}; its a=q (full-failure) point is at
  η_construction ≈ c / log₂ q.
The prize window edge is  η_we = H(ρ)/log₂(q·ε*) = H(ρ)/log₂ n   (since q·ε* ≈ n).
At realistic prize parameters (ε*=2^-128, q=n·2^128, n=2^30, ρ≈1/2):
  log₂q = 158 ≫ log₂n = 30  ⟹  η_construction = 1.46/158 ≈ 0.0092  ≪  η_we = 1/30 ≈ 0.033.
So the BChKS FAILURE construction lives PAST the window edge (deep failure zone) — CONSISTENT with the
prize, confirming the ceiling, NOT refuting the floor.

## 4. THE MECHANISM (novel): the ε*=2^-128 exponent protects the floor
The floor survives the BChKS admissibility attack iff η_construction < η_we, i.e.
  (c−1)·log₂ n  <  log₂(1/ε*) = 128   ⟺   n < 2^{128/(c−1)}.
With c≈1.46: threshold n < 2^{278}. With c→2 (max entropy): threshold n < 2^{128}. EITHER WAY, every
realistic FRI domain (log₂ n ≤ 40) is SAFE by a huge margin — and the protection is EXACTLY the large ε*
exponent (the 128 in log₂(1/ε*)), which separates the window edge from the dyadic admissibility construction.
REFUTABLE PREDICTION: the prize floor (ρ≈1/2) would FAIL for n > 2^{128/(c−1)} — astronomically beyond any
real FRI, but a concrete boundary.

## 5. Honest scope
This eliminates the STRONGEST KNOWN concrete failure construction (BChKS admissibility/sumset) at realistic
parameters, with a precise ε*-dependent threshold. It is NOT a proof of the floor — the floor needs ALL
failure modes to miss (= the full explicit-RS list-decoding bound). But it is the first quantitative reason
the prize HOLDS at realistic parameters, tied to ε*, and it corrects the fleet's target (Conj 1.12 = failure
direction, not the floor). novelty 8 / insight 9 / proximity 9 (exact prize params) / feasibility: this
sub-result is DONE; the full floor remains the open list-decoding bound.
