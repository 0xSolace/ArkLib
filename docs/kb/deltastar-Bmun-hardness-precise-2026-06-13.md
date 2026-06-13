# Precise characterization: why `B(μ_n)` is hard (the unique open core) (2026-06-13)

The single remaining open piece of the prize — proven irreducible (no elementary/Fisher method
reaches it, since the construction has maximal coincidence at every order) — is the worst-case
Gaussian period `B(μ_n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(bx)`. Here is the exact reason it
resists, derived from the moment structure.

## The moments are exactly computable and Gaussian-like at order ≤ 4
`η_b` is constant on the `f=(p−1)/n` cosets `bμ_n`. Exact moment identities:
- `Σ_b |η_b|² = p·n`  ⟹  over cosets `Σ|η|² ≈ p`, `avg|η|² = n`.
- `Σ_b |η_b|⁴ = p·E(μ_n) = p(3n²−3n)`  ⟹  `avg|η|⁴ ≈ 3n²`, so
  > **`avg|η|⁴ / (avg|η|²)² = 3`** — *exactly the Gaussian 4th/2nd ratio.*

So the periods are **Gaussian-like in their 2nd and 4th moments** (variance `n`), predicting the
conjectured `B(μ_n) = Θ(√(n·log(p/n)))` (max of `f` Gaussians of variance `n`).

## Why the 4th moment cannot prove the max (the precise gap)
- **4th moment alone** gives only `max|η|⁴ ≤ Σ|η|⁴ ≈ 3pn`, i.e. `B ≤ (3pn)^{1/4}` — carries a
  `p^{1/4}` factor (`≈2^{55}` at `p=2^{192},n=2^{30}` vs the true `≈2^{19}`). **Far too weak.**
- The **max over `f` near-Gaussian variables** needs sub-Gaussian tails = control of the `2j`-th
  moments `Σ_b|η_b|^{2j} = p·E_j(μ_n)` (the additive `2j`-energy) up to `j ≈ log f = log(p/n)`.
- **But** (proven earlier, `moment-hierarchy-correction`): `E_j(μ_n)` is **clean** (minimal)
  **iff `p > n^j`**. So clean only for `j < ⌈log_n p⌉ ≈ 6` (prize), while the max needs `j` up to
  `≈ log(p/n) ≈ 162`.

> **The gap: clean moments reach order `≈ log_n p ≈ 6`; the worst-case max needs order
> `≈ log(p/n) ≈ 162`.** The intervening high additive energies `E_j(μ_n)` (`6 ≤ j ≤ 162`) are
> **not** controlled by the clean low-order structure — this is exactly the Bourgain-regime
> incomplete-character-sum difficulty, and it is genuinely open for `n ≪ √p`.

## Consequence (the honest final localization)
The prize `δ*` reduces — provably and irreducibly — to bounding `B(μ_n) ≤ C√(n·log(p/n))`, which is
equivalent to controlling the high additive energies `E_j(μ_n)` for `⌈log_n p⌉ ≤ j ≤ log(p/n)` in
the deployed regime. This is the **single, precisely-located, recognized-hard open input**; every
other component of the proof of `δ* = 1−ρ−2/s*` is established (upper bracket + monomial extremality
+ the direction-Fisher second-moment bound + the proof that no elementary method suffices).

**No closure is claimed.** This page records the exact mathematical reason the prize's analytic core
is open, so that a future analytic bound on `B(μ_n)` (or on the high energies `E_j`) slots directly
into the otherwise-complete scaffold.
