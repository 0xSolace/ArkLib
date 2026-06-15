# CAVEAT: the antipodal-tower "off-BGK path" misses the NON-symmetric worst case at ρ<1/4 (#444)

Honest scrutiny of the army's "most promising off-BGK path" (antipodal-tower → prime-decoupled symmetric-function
count). It has a real GAP: it bounds only the z→−z SYMMETRIC sub-family, which is a LOWER bound on the worst case,
NOT the upper bound needed.

## The finding (exact, listsize-style enumeration of agreement-set symmetry)

For a 2-sparse word u=x^a+γx^b, the antipodal-tower squaring identity `e_{2ℓ}(±z)=(−1)^ℓ e_ℓ(z²)` only simplifies
for SYMMETRIC agreement sets S=−S. So the tower count = the symmetric part of the list. Measured (n=16):

| word | rate | parity | list | symmetric agreement sets |
|---|---|---|---|---|
| x^15+x^5 | ρ=1/4 | both ODD (u odd) | 7 | **7/7 symmetric** ✓ tower applies |
| x^13+x^12 | ρ=1/8 | mixed | 4 | **1/4 symmetric** ✗ 3 escape the tower |

- An **odd** word (both exponents odd) has `u(−x)=−u(x)`, forcing its list agreement sets to be antipodal-closed
  (symmetric) — the tower captures it fully. The ρ=1/4 worst word is odd, so the tower applies there.
- But the ρ=1/8 worst word is the **consecutive-exponent `x^a+x^{a−1}`** (mixed parity, NOT odd), and 3 of its 4
  list codewords have **non-symmetric** agreement sets. These escape the squaring recursion.

## Consequence (corrects the "most promising path" optimism)

The antipodal-tower / prime-decoupled symmetric-function count bounds only the **symmetric sub-family** of the
list = a **LOWER bound** on the worst case. The **upper bound** (which the floor needs) requires the
**non-symmetric** agreement sets too, and those do NOT descend via the dyadic squaring (which is the z→−z
symmetry engine). So the army's claim that "the upper bound reduces to a prime-decoupled symmetric-function count
via the antipodal tower" is INCOMPLETE — it omits the non-symmetric worst case at ρ<1/4.

## What stays (honest)

- The reduction (floor ⟺ list past Johnson), the dead import routes, and the window list law `L*=2^{Θ(1/η)}`
  (KKH26 lower bound) all stand.
- The antipodal-tower is still a genuine structural tool — it exactly bounds the odd-word (symmetric) family, and
  at ρ=1/4 the worst word IS odd, so it applies there. But it is NOT a complete upper-bound route, because the
  non-symmetric worst case (ρ<1/4 consecutive words) escapes it.
- So the off-BGK hope is partial: it may close ρ=1/4 (odd worst word) but not the lower rates. The general upper
  bound still requires handling non-symmetric agreement sets — which is back to the general char-sum/incidence
  structure (the BGK wall), unless a non-symmetry-based recursion is found.

## Net

A real, honest gap in the proposed off-BGK path: the antipodal-tower bounds the symmetric (odd-word) sub-family
only (lower bound), missing the non-symmetric worst case at ρ<1/4. NOT a refutation of the floor (the window list
law and KKH26 lower bound stand), but a correction to the "most promising path" — it is incomplete as an upper
bound. The open core is unchanged: the upper bound for the GENERAL (incl. non-symmetric) worst case = the BGK wall.
Next: either find a recursion for non-symmetric subsets, or confirm the worst word is always odd (engine: is the
ρ<1/4 worst always beatable by an odd word? measured NO at n=16 — consecutive beats odd).
