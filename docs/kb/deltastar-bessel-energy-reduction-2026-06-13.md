# The Bessel reduction: exact additive energy of μ_{2^μ} is provably sub-Gaussian (2026-06-13)

A genuinely new, clean reduction of the clean-moments core (#389, commit
674243318), with a PROVEN unconditional bound on the exact (p=∞) energy and
the residual sharpened to the mod-p excess.

## The reduction (novel, exact)
For `n = 2^μ`, `μ_n` elements map to ± unit vectors in `ℤ^{n/2}` (since
`ζ^{n/2} = −1`). Hence the exact additive energy
`E_r^∞(μ_n) = #{(x,y) ∈ μ_n^{2r} : Σx_i = Σy_j}` is the return count of a
`2r`-step ±unit-vector walk in `ℤ^d` (`d = n/2`):

  **`E_r^∞(μ_{2^μ}) = (2r)! · [x^{2r}] I₀(2x)^{n/2}`,   I₀(2x) = Σ_m x^{2m}/(m!)².**

VERIFIED exactly: `n=8,r=2 → 4!·[x⁴]I₀(2x)⁴ = 24·7 = 168` ✓ (and r=3,4, n=16,32
— `probe_prize_bessel.py`, all match the direct energy `probe_prize_energy_exact.py`).

## The proven sub-Gaussian bound (UNCONDITIONAL, clean)
`[x^{2r}]I₀(2x)^d = Σ_{m₁+…+m_d=r} ∏ 1/(mᵢ!)²`, while the clean/Gaussian value
`(2r−1)!!·n^r = (2r)!·d^r/r! = (2r)!·Σ_{Σmᵢ=r} ∏ 1/mᵢ!`. Since
`∏ 1/(mᵢ!)² ≤ ∏ 1/mᵢ!` (each `1/mᵢ! ≤ 1`), TERM BY TERM:

  **`E_r^∞(μ_{2^μ}) ≤ (2r−1)!! · n^r`   for ALL r — i.e. `I₀(2x) ≤ e^{x²}`
   coefficientwise.**

Empirically the ratio →1 from below as `n→∞` at every `r`, and stays `≤1` and
bounded even at `r = log₂ n` (the threshold): `2^14`: r=2..16 ratios
0.9999…0.993; r=log₂n always `≤1` (`probe_prize_bessel`). So the exact energy
is sub-Gaussian to all orders — the clean-moments hypothesis holds for the
EXACT (p=∞) energy, proven.

## What this closes and what remains (HONEST)
- **Closed:** the exact-energy main term is sub-Gaussian, `E_r^∞ ≤ (2r−1)!!n^r`,
  unconditionally and cleanly (coefficientwise `I₀ ≤ e^{x²}`). This is the
  Gaussian baseline the clean-moments bridge assumes — now a theorem, not an
  assumption, for `n=2^μ`.
- **Residual (sharpened):** the prize needs the FINITE-p energy
  `E_r^{(p)} = Σ_b|η_b|^{2r}/p = E_r^∞ + (mod-p excess)` clean up to `r~log p`.
  My bound handles `E_r^∞`; the open part is now precisely the **mod-p
  coincidence excess** `#{(x,y) : Σ(x_i−y_j) ≡ 0 (mod p), ≠ 0 exactly}` —
  the non-trivial mod-p additive relations among roots of unity. This is a
  cleaner, more concrete residual than "is `E_r^{(p)}` clean": bound the
  mod-p excess by `o((2r−1)!!n^r)` up to `r~log p` and δ* closes (dyadic).

The mod-p excess is governed by Mann/Conway–Jones (non-trivial vanishing
relations = coset structures) reduced mod p — connecting back to the
sparse-divisor/coset bricks. The reduction turns the analytic core into:
Bessel main term (PROVEN sub-Gaussian) + mod-p coset-coincidence excess
(the remaining open input, now isolated and structured).

## The mod-p excess is governed by the prime P — PROVEN clean threshold p > (2r)^{n/2}

Measured (`probe_prize_excess.py`, n=8): `E_r^{(p)} − E_r^∞` vanishes once `p`
exceeds an `r`-dependent threshold (r=2: clean p≥73; r=3: by p≥193; r=4: still
+ at 241), and when positive it pushes `E_r^{(p)}` ABOVE Gaussian (breaks
cleanliness). Mechanism + PROOF:

Via the reduction `φ: ℤ[ζ_n] → F_p` (`ζ_n ↦ g`, `g` a primitive n-th root,
`n|p−1`), `Σg^{aᵢ} = Σg^{bⱼ}` in `F_p` iff `e := Σ(ζ^{aᵢ}−ζ^{bⱼ}) ∈ ker φ = P`
(the prime above `p`, norm `p^f ≥ p`). So
`E_r^{(p)} = E_r^∞ + #{e ∈ P∖{0}}`. Each `e` is a sum of `2r` roots of unity:
`|σ(e)| ≤ 2r` for all embeddings `σ`, so `1 ≤ |Norm(e)| ≤ (2r)^{φ(n)} =
(2r)^{n/2}`; and `e ∈ P ⟹ p | Norm(e)`. Therefore:

  **`p > (2r)^{n/2}  ⟹  no excess  ⟹  E_r^{(p)}(μ_n) = E_r^∞(μ_n) ≤ (2r−1)!!·n^r`.**

(Sufficient, not tight — n=8,r=2 is clean already at p=73 < 4⁴=256, the
specific sums avoiding P-points below the Minkowski bound.)

## Consequence: a PROVEN conditional δ* closure + the exact wall
Combining with the swarm's Markov bridge (clean to `r_max ⟹ B ≤
√(p^{1/r_max}(2r_max/e)n)`), the closure needs clean up to `r_max ~ log p`,
i.e. `p > (2 log p)^{n/2}`, i.e.

  **`n = O(log p / log log p)  ⟹  E_r(μ_n) clean to r~log p  ⟹  δ* closes`**
  (PROVEN: Bessel sub-Gaussian `E_r^∞ ≤ Gaussian` + norm-bound no-excess).

This is a genuine proven δ*-closure for the **logarithmically-short** regime
(an infinite family), via Bessel + geometry of numbers — NO conjectural input.
It also pinpoints EXACTLY why the prize (constant rate, `n ~ p^{1/β}`) is open:
there the norm bound `(2r)^{n/2} ≫ p` already at `r=2`, so the prime `P`
acquires small points (`e ∈ P∖{0}` with `≤ 2r` terms) and the excess is
genuinely present. The wall is precisely **small points of `P` in the
`2r`-root-of-unity box** — a concrete lattice/ideal question (the geometry of
the prime above `p` in `ℤ[ζ_n]`), now cleanly isolated from the
(proven-sub-Gaussian) main term. Bounding small-`P`-points at constant rate is
the remaining open input; it is a sharp, classical-flavored target (Minkowski
is too lossy; the true count needs the arithmetic of `P`).
