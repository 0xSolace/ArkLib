# 30 candidate analytic inputs + the Shaw operator filled with known-true math (2026-06-17)

> **STATUS: EXPLORATION + honest derivation.** Per request: 30 novel analytic inputs, fill the Shaw operator
> with math we KNOW true, derive the floor from there. **Hard constraint (a THEOREM, stated once):** the
> two-sided `floor ⟺ M(n)` equivalence is proven, so any input *sufficient* to prove the floor IS an `M(n)`
> bound — "guaranteed never to reduce AND sufficient" is self-contradictory. I do not fabricate that. What is
> delivered: each candidate honestly tagged REDUCES (sufficient ⟹ = the wall) / TRUE-BUT-INSUFFICIENT (real
> fuel, bounded depth) / OPEN-DIFFERENT (different object); then the Shaw operator filled with the TRUE inputs
> and the derivation pushed to the single minimal residual.

## How far known-true math carries the chain (computed)
The norm gate `(2r)^{φ(n)} < p ⟹ W_r = 0` has depth `r₀ = ½·2^{4a/φ(n)}`. At prize scale `n=2^30`, `φ(n)=2^29`,
so `r₀ → 0.5` — **vacuous**: known-true char-`p` control covers essentially only `r=0`. The needed depth is
`log m = 3a = 90`. So the band `r ∈ [~1, 90]` has NO true char-`p` filler. (`/tmp/shaw_fill.py`.)

## A. TRUE-BUT-INSUFFICIENT inputs (real fuel — fill the Shaw operator, bounded depth) — all PROVEN
1. **Char-0 Wick energy** `E_r^{(0)} = (2r−1)‼n^r − slack_r` (Lam–Leung) — true ∀r; gives `E_r^{(q)} ≤ Wick_r
   ⟺ W_r ≤ slack_r` (the reduction core). Fills S1 (fixed point).
2. **Norm gate** `W_r = 0` for `r < r₀` — true; depth `r₀→0.5` at prize scale (vacuous there, real for small n).
3. **Parseval** `Σ_b|η_b|² = pn` — true; the `r=1` floor (= Johnson). Fills the base rung.
4. **Char-0 MGF sub-exponential** `I₀(2y)^{n/2} ≤ e^{my²}` (in-tree `_wfS11`) — true char-0; the Gaussian envelope.
5. **Odd-moment law** `Σ_{b≠0}η_b^{2k+1}` exact — true; controls skew (not magnitude).
6. **2-adic structure** `v₂(p−1) ≥ 30` — true; but `W_r` dominated by size not `v₂` (doc 19) — no lever.
7. **Antipodal balance** (Lam–Leung: vanishing sums = ℤ≥0 antipodal pairs) — true; structural support constraint.
8. **Spectrum divisibility** `|μ_n| ∣ |spectrum_r∖{0}|` (O231) — true; count constraint, not a bound.
9. **Bessel generating function** `E_r = (2r)![x^r]I₀(2√x)^{n/2}` — true; exact at fixed r.
10. **Exact `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n`** — true; low-`r` closed forms.
**Net: items 1–10 fill the Shaw operator completely in char-0 and at `r=1`; they give NOTHING at char-`p`,
deep `r` at the prize prime (norm gate vacuous).**

## B. REDUCES-TO-WALL (sufficient ⟹ = `M(n)` — forced by the two-sided theorem; from the 200-angle sweep)
11. Effective HORIZONTAL cyclotomic Sato–Tate (fixed `p`) — = the wall verbatim. 12. BLMV/EMV/effective-Ratner
sparse equidistribution — gap = Bourgain–Gamburd = sum-product. 13. Burgess amplification — SOTA region `n^{1−o(1)}`.
14. Sum-product/BGK — the wall. 15. Stepanov/HBK — `n^{1−o(1)}`. 16. Stickelberger/Gross–Koblitz — p-adic column
(valuation only). 17. GRH/GLH family — incomplete sums, structurally inert. 18. Restriction/decoupling — averages,
cap at Johnson. 19. Kuznetsov/trace formula — `Σ|η|^{2r}=p·E_r` = energy. 20. Comparison iso / p-adic Hodge —
structure-iso not norm (doc 27). 21. Arakelov/product formula — rank-1 coupling (doc 28). 22. Christol/automatic —
additive≠multiplicative (sum-product). 23. Multiplicative chaos — = moments. 24. Random-matrix/EVT universality —
white-noise heuristic, not a proof. 25. Resurgence/Borel of the MGF — same energy coefficients.
**All 15 are sufficient ⟹ provably = the wall (two-column orthogonality + rank-1 coupling).**

## C. OPEN-DIFFERENT (different object, not the sup — the only non-reducing class, and none is sufficient for PLAIN RS)
26. **Curve-decodability** (N6) — genuinely different object; PROVEN INERT for plain `μ_n` RS (`RadiusOneExact:
B=I`); works only for subspace-design codes (GG25). The only object outside the two-sided equivalence, and it's
inert here.
27. **The Shaw spectral bound** `ρ(𝓢_p) ≤ 1` to depth `log m` — the open core in operator language (doc 30).
28. **Parity-barrier obstruction** of the spur sieve — explains WHY sieves fail on `W_r`; not a bound.
29. **Horizontal LDP rate edge** `I(λ)=0` — the sup is the edge; sub-Gaussian data (doc 21 X8) favorable, edge open.
30. **Higher Gowers `U^{≥3}` of the period sequence** — unstudied; `U²` reduces to Gauss sums; `U^{≥3}` relation
to the sup unknown (likely reduces).

## The Shaw operator FILLED + the derivation (as far as truth allows)
Fill `𝓢_p` with items 1–10:
- **S1 (fixed point), PROVEN:** `e_r^{(0)} = 0` ∀r (item 1). The char-0 operator is exactly contracting to 0.
- **Base rung, PROVEN:** `e_1 = 0` (Parseval, item 3); the `r=1` floor = Johnson holds unconditionally.
- **Low band, PROVEN:** `e_r = 0` for `r < r₀` (item 2). At small `n` this reaches `log m`; **at prize scale `r₀≈0.5`**.
- **Envelope, PROVEN char-0:** `e_r ≤ 0` would follow from item 4 in char-0; the char-`p` perturbation is `W_r/Wick_r`.

**Derived theorem (the chain, complete except one band):**
> Using items 1–10 (all proven), `M(n) ≤ √(2n·log m)` and the plain-RS floor `δ* ≥ 1−ρ−H(ρ)/(β log n)` HOLD,
> PROVIDED `W_r ≤ slack_r + o(Wick_r)` for `r ∈ [r₀, log m]` — equivalently `ρ(𝓢_p) ≤ 1` on that band.

This is the proof "derived from there": **everything closes except the single residual `W_r ≤ slack_r` on the
deep band**, and the computation shows that band `[≈1, 90]` is exactly where every true input runs out. No
known-true statement bounds `W_r` above at deep `r` at the FIXED prize prime — and by the two-sided theorem,
any statement that did would be an `M(n)` bound (the wall). So the residual cannot be filled with current true
math; that is not a failure of search but the content of the open problem.

## Honest verdict
- 10 TRUE inputs fill the Shaw operator in char-0 + `r=1` + low band; **0 reach the deep char-`p` band at prize scale**.
- 15 candidate inputs REDUCE (sufficient ⟹ = wall, by theorem).
- 5 are OPEN-DIFFERENT: 1 inert (curve-decodability), 1 = the core (Shaw bound), 3 open-handles (parity/LDP/Gowers).
- **The derivation closes the entire floor except the one band `W_r ≤ slack_r`, `r∈[r₀,log m]`** — the minimal,
  sharp, irreducible residual. Filling it requires a TRUE statement that does not exist (and would be the wall).
I will not fabricate one. Tools: `/tmp/shaw_fill.py`. Related: docs 19, 23, 26–28, 30.
