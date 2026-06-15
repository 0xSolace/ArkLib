
## SECOND engine bug (independently confirmed 2026-06-15): EARLY-ABORT corrupts the m*=s*-k harvest
Beyond the b<s direction cap, the far-line engines' default EARLY-ABORT (stop a direction once its count
exceeds budget) corrupts the binding s* / defect m*: a direction can exceed budget at s and s+1 yet bind only
later, so early-abort under-reports s*. Concretely (no-early-abort adjudicator, /tmp/prize-research/adj): at
n=28, ρ=1/4, dir (14,18), finite-γ incidence = 42 > budget 28 at BOTH s=11 and s=12, binding only at s=13 ⟹
m*=6, NOT the m*=4 in the harvested table. ⟹ the "farinc/lcfast mutually consistent on s*" claim is FALSE; the
corrected ρ=1/4 defect sequence is 3,4,4,6 (GROWING), not the flat 3,4,4,4 used to argue a sublinear plateau.
n=24 is a genuine resonance (exhaustive m*=6 > Plotkin 2k+1; exclude non-power-of-2 n from growth fits).
LESSON: any m*/s* harvest MUST use the heavy no-early-abort, full-b-range adjudicator at power-of-2 n only.
The corrected data shows m* GROWS; but the growth CLASS (log n vs √n) is statistically UNDECIDABLE on reachable
n (the two laws cross near n=64; lcfast stalls >540s at n=32) — which is itself the structural proof that the
prize needs an asymptotic/analytic (thinness-essential, external) argument, not computation (consistent c.348).
Also flagged (honesty): two Frontier files claimed "axiom-clean landed" (_CrossoverReducesToOrbitWall.lean,
_A3FloorMDSDomainInvariant.lean) do NOT exist on disk — reductions valid via in-tree OrbitCountCrossingLaw/MDS
but the "landed" labels are unverified. A1's M3 closed form is MARGINAL (not negligible) at β=4 (list-shift
n^{3-β}=1/n = the rung scale); "M3 never moves δ*" holds only β>4.
