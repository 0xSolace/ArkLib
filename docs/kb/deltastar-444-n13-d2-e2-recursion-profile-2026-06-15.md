# #444 N13/D2 e2-recursion profile -- 2026-06-15

Status: bounded exact probe, not a prize proof.

Probe:
`scripts/probes/probe_444_n13_d2_e2_recursion_profile.py`

Purpose: separate three objects that the N13/D2 route can otherwise conflate.

- `e2(S)=0, e1(S)!=0`: the monomial-pencil bad-scalar lane.
- `e1(S)=e2(S)=0`: the stronger vanishing-subset / coset-union lane.
- `2` singleton antipodal-pair profile: the family reduced by
  `ArkLib/Data/CodingTheory/ProximityGap/_E2SquaringRecursion.lean` to subset sums on squared roots.

The probe uses exact arithmetic in `Z[zeta_n]` with basis
`1,zeta,...,zeta^(n/2-1)` and `zeta^(n/2)=-1`, so the counts are structural
cyclotomic counts rather than finite-field coincidences.

## Output snapshot

Enumeration cap: `C(n,w) <= 1200000`.

| n | w | C(n,w) | e2=0 | e1=e2=0 | e2=0,e1!=0 | distinct e1 | e1 orbits | 2-singleton/e1!=0 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 4 | 70 | 10 | 2 | 8 | 8 | 1 | 8 |
| 8 | 5 | 56 | 8 | 0 | 8 | 8 | 1 | 0 |
| 16 | 4 | 1820 | 52 | 4 | 48 | 48 | 3 | 48 |
| 16 | 5 | 4368 | 48 | 0 | 48 | 16 | 1 | 0 |
| 16 | 8 | 12870 | 70 | 6 | 64 | 48 | 3 | 64 |
| 16 | 12 | 1820 | 20 | 4 | 16 | 16 | 1 | 16 |
| 32 | 4 | 35960 | 232 | 8 | 224 | 224 | 7 | 224 |
| 32 | 5 | 201376 | 224 | 0 | 224 | 32 | 1 | 0 |
| 32 | 6 | 906192 | 0 | 0 | 0 | 0 | 0 | 0 |

Pair-profile detail:

- `(1,2)` rows: width 4 counts are exactly `n*(n/4-1)` bad scalars after
  removing the `e1=0` antipodal-closed rows: `8,48,224` for `n=8,16,32`.
- `(3,2)` and `(5,2)` rows: the half-width / complement-side rows are also
  covered by the same two-singleton profile.
- `(2,1)` rows: width 5 has `e2=0,e1!=0` counts `8,48,224` for `n=8,16,32`,
  but zero two-singleton coverage.

## Consequence for N13/D2

The coset-union / generating-function lane cannot simply count
`e1=e2=0` vanishing subsets and call that the bad-scalar count: in every
nonempty row above, `e1=e2=0` is strictly smaller than `e2=0,e1!=0`.

The Lean file `_E2SquaringRecursion.lean` is still useful. It gives a clean
algebraic reduction for the two-singleton plus antipodal-doubles family, and
that family explains the width-4 counts and the half-width rows in this bounded
census. But it is not a global closure: the width-5 `(2,1)` family is
structural, has the same `8,48,224` scale in the tested dyadic cases, and is
outside the current two-singleton recursion hypothesis.

Action item for the route: either count `e2=0,e1!=0` directly with a generating
function that includes the odd-singleton families, or prove a separate injection
from the full bad-scalar lane into a stronger vanishing-subset/coset-union
object. Without that bridge, N13/D2 is a scoped reduction, not a proof of the
delta-star floor.
