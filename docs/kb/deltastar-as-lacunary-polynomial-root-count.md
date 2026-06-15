# The prize δ* as a lacunary-polynomial root count over roots of unity — a clean classical reduction (#407)

A clean analytic reformulation of the far-line list-decoding radius (the object the numerics cannot resolve,
per `CRITICAL-numerics-cannot-distinguish-johnson-from-floor.md`). It connects the prize to classical
sparse-polynomial / vanishing-sums-of-roots-of-unity theory — the right *analytic* attack surface.

## The reduction (exact, by construction)

The far-line monomial list-decoding radius is
> **s*(n,k) = max number of roots in μ_n of a polynomial `P(x) = x^a + γ·x^b − c(x)`** (`deg c < k`, any
> `γ ∈ F_q`, `a,b ∈ [k,n)`) — i.e. the max μ_n-root-count of a polynomial with **support `{a,b} ∪ {0,…,k−1}`**
> (a **(k+2)-term lacunary polynomial**).

This is exact: agreement of the far line `x^a+γx^b` with a degree-<k codeword on a set `S ⊆ μ_n` is precisely
`P` vanishing on `S`. δ* = 1 − s*/n.

## Verified data (engine)

| n | k | s* | terms (k+2) | √(kn) |
|---|---|---|---|---|
| 16 | 4 | 7 | 6 | 8.0 |
| 16 | 2 | 5 | 4 | 5.7 |
| 24 | 6 | 11 | 8 | 12.0 |
| 24 | 12 | 16 | 14 | 17.0 |

Note `s* > k+2` (more roots than terms) — possible because **factors of `x^n−1` are themselves sparse**
(cyclotomic polynomials), so a lacunary `P` can be divisible by a high-degree sparse factor of `x^n−1`.

## The connection to classical theory (the analytic handoff)

The open question — does `s* = √(kn)` (Johnson) or `s* = k + Θ(n/log n)` (floor) asymptotically — is now a
**lacunary-polynomial root-count** problem:
- **Vanishing-sums-of-roots-of-unity:** `P(ζ)=0` for `ζ ∈ μ_n` ⟺ a weighted vanishing sum of n-th roots of unity.
  Controlled by **Mann's theorem** and **Conway–Jones** (minimal vanishing sums) — already in the campaign's
  toolkit for the char-p side.
- **Sparse polynomial root bounds:** the number of roots of unity of a `t`-sparse polynomial — **Bombieri–Zannier**,
  **Filaseta–Lenstra** (sparse factors of `x^n−1`), **Lenstra** (cyclotomic factors). These bound exactly the
  object `s*`.
- This is the **GG25 curve-decodability / list-size object** (the in-tree prize engine) re-expressed as a lacunary
  root count — a cleaner, more classical statement of the same open core.

## Why this is the right form

- It is **finite and exact** (no char-p, no probability) — a pure question about roots of a structured polynomial.
- It connects to **citable classical theory** (Mann/Conway–Jones/Bombieri–Zannier/Filaseta–Lenstra) — the
  literature the prize "reduces to."
- The Johnson-vs-floor distinction = whether a `(k+2)`-sparse polynomial can have `k + Θ(n/log n)` roots in μ_n
  (floor) or is capped at `√(kn)` (Johnson). This is a sharp, classical lacunary-root question.

## Reading list (added to PAPERS_NEEDED)

- Bombieri–Zannier, "Algebraic points on subvarieties of G_m^n" (sparse polynomial / torsion points).
- Filaseta–Lenstra / Lenstra, sparse factors of x^n−1, cyclotomic factors of lacunary polynomials.
- Conway–Jones, "Trigonometric Diophantine equations" (minimal vanishing sums of roots of unity).
- Mann, "On linear relations between roots of unity" (1965).
- (Connect to GG25 curve-decodability: the list-size of RS for 2-sparse-spectrum words.)

## Status

A clean, exact, novel-framing reduction of the prize δ* to a classical lacunary-polynomial root-count over roots
of unity — the correct *analytic* form (the numerics provably cannot resolve it). NOT a closure: bounding the
max μ_n-root-count of a `(k+2)`-sparse polynomial as `√(kn)` (Johnson) vs `k+Θ(n/log n)` (floor) is the open
core, now stated in the most classical/citable form found. This is the analytic handoff.
