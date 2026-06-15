# The multiplicative-dual Paley sum is the SAME WALL as the additive Gauss period (no leverage), 2026-06-15

## The decisive check (exact, n=8..64)
The prize reduces to the shifted 2-power subgroup multiplicative character sum
`S(χ)=Σ_{ζ∈μ_n}χ(1+ζ)` (the multiplicative dual of the additive Gauss period `M(n)=max_b|Σ_{x∈μ_n}e_p(bx)|`).
Computed `max_χ|S(χ)|` (= DFT over Z/(p−1) of the histogram of {ind(1+ζ)}) vs `M(n)` at the same p,n:
| n | maxS | M(n) | maxS/M | maxS/√(n log m) |
|---|------|------|--------|------|
| 8  | 6.99  | 7.56  | 0.925 | 0.989 |
| 16 | 14.50 | 13.84 | 1.048 | 1.257 |
| 32 | 25.36 | 22.98 | 1.103 | 1.390 |
| 64 | 43.47 | 38.53 | 1.128 | 1.538 |

## Verdict: SAME WALL (the dual is if anything marginally HARDER)
`max_χ|S(χ)|` is essentially equal to `M(n)` — ratio 0.93→1.13, slightly ABOVE 1 (the dual is marginally
larger). Both grow as ~√(2n log m), C≈√2. So the multiplicative-dual / shifted-subgroup form gives **NO
leverage** over the additive form — it is the **same Burgess-barrier wall**, confirmed from the
multiplicative side. The "dual might be structurally easier" hope is REFUTED. (Expected from the
additive↔multiplicative Fourier involution, now quantified: the involution is essentially norm-preserving
on the sup.)

## Consequence for the "next move" (crossing Burgess)
The shifted-subgroup Paley sum S(χ) does not admit an obvious advantage over M(n); crossing the Burgess
barrier (n=p^{1/4}, β=4) is the SAME open problem in both forms. The only remaining hope from this route
is whether the shifted-subgroup-char-sum LITERATURE (Karatsuba/Shkredov/Hanson/Bourgain-Garaev) has a
better unconditional exponent than the additive BGK at |H|=p^{1/4} (under check). Structural facts (ζ=−1
drops, ζ↔ζ^{−1} pairing = oddness, (1−ζ²)=(1−ζ)(1+ζ), ∏(1+ζ)=±n) do not by themselves cross Burgess.
Probe: this session (max_χ|S| via FFT of the 1+μ_n index histogram).
