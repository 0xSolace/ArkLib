STATUS: PARTIAL — truncation propagation lemma proven; order-t linearization not yet landed.

# pc-w6-newton — Newton truncation propagation for power-series powers

File: `ArkLib/Data/Polynomial/NewtonLinearization.lean`

Compile check:

```bash
lake env lean ArkLib/Data/Polynomial/NewtonLinearization.lean
```

Current checked content:

- `coeff_pow_sub_below`: if `γ₁ γ₂ : R⟦X⟧` agree on all coefficients `j < t`, then
  `γ₁ ^ i` and `γ₂ ^ i` also agree on all coefficients `j < t`, for every `i`.

The proof is by induction on `i`. In the successor case, `coeff_mul` rewrites the coefficient
of the product as an antidiagonal sum. Every pair `(a,b)` in the antidiagonal for `j` satisfies
`a + b = j`; since `j < t`, both `a < t` and `b < t`, so the original truncation hypothesis and
the induction hypothesis rewrite the two product factors.

This is the reusable base needed for the BCIKS20 Appendix A.4 Newton-linearization path, but it
does not yet prove the order-`t` linear response formula or the composed-polynomial
`P'(c)` corollary. Those downstream statements still require the antidiagonal endpoint/interior
split and derivative/evaluation bookkeeping.

No `sorry`/`admit` was introduced in this file.
