# The c_r closed form `(1/2)log I₀(2t)`: the char-0 ladder closes rigorously for ALL r, and the char-p wall is sharply reframed (#444, 2026-06-17)

## The result (exact, verified r=1..8; `scripts/probes/probe_cr_bessel_cgf_closed_form.py`)
The DC-Wick cumulants are `κ_{2r}=c_r·n` (linear, established exactly to r=8). The coefficient sequence
`c_r = 1, −3, 40, −1155, 57456, −4370520, 471556800, −68492499075` has the **closed-form generating
function**
```
        g(t) := Σ_r c_r t^{2r}/(2r)!  =  (1/2)·log I₀(2t)        (I₀ = modified Bessel, ENTIRE)
```
so the char-0 additive-energy cumulant generating function is `K(t) = n·g(t) = (n/2)·log I₀(2t)`.

## Why (rigorous structural derivation)
By Lam–Leung the period pairs antipodally: `η_b = Σ_{a<n/2} (e_p(bζ^a)+e_p(−bζ^a)) = Σ_{a<n/2} 2cos(2π bζ^a/p)`
— a sum of **n/2 real cosine terms**. A single `2cos(uniform angle)` has CGF `E[e^{t·2cosθ}] = I₀(2t)`
(the Bessel integral). In the **char-0 idealization** the n/2 angles `{2π bζ^a/p}` are jointly
equidistributed/independent, so the period CGF is the n/2-fold sum `(n/2)·log I₀(2t)`. Hence
`κ_{2r} = (n/2)·κ_{2r}(2cos) = c_r·n` — **linear in n for ALL r**, with the explicit Bessel `c_r`.

## Consequence: the char-0 ladder closes rigorously (all r, not just computational to r=8)
`I₀` is entire and the per-pair variable `2cosθ` is **bounded**, so `K(t)` is entire and sub-exponential.
The max-over-m saddle `t* ~ √(2 log m / n) → 0` sits at the origin where `g(t) ≈ t²/2` (the `c_1=1` term),
giving `K(t*) ≈ n·t*²/2` ⟹ sub-Gaussian with proxy `n` ⟹ **`M_char0 ≤ √(2n·log m)(1+o(1))`**. This upgrades
the char-0 closure from "linear to r=8 (computational)" to "**exact closed-form for all r**", consumed by
the in-tree SG-MGF bridge.

## The char-p wall, sharply reframed
The char-0 result used the **idealization that the n/2 angles `2π bζ^a/p` are jointly equidistributed**.
The char-p reality: those angles are the dilates of the multiplicative subgroup `μ_{n/2}` in `F_p`, and are
**correlated** — their deviation from joint equidistribution is *exactly* the BGK/Paley short-character-sum
question. So the `$1M` gap is now precisely: **how far the n/2 subgroup angles deviate from independence**
(= the period's departure from the Bessel/arcsine law `(n/2)log I₀(2t)`). The char-0 Bessel law is the
*independent-angle baseline*; the prize is the *correlated-angle correction*, the genuine open core.

## Net
Char-0: **CLOSED in closed form** (`κ_{2r}` = Bessel/arcsine cumulants, `g=(1/2)log I₀(2t)` entire, saddle ⟹
floor — rigorous for all r). Prize: the char-p deviation of the n/2 dilated-subgroup angles from joint
equidistribution (BGK), now framed as the exact gap between the period CGF and `(n/2)log I₀(2t)`.
Formalizable next: the Bessel-CGF identity + the bounded-variable sub-Gaussian saddle as Lean lemmas.
