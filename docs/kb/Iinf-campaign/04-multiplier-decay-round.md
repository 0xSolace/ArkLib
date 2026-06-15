# I_∞ campaign — round 4: the multiplier-decay reframing (2026-06-15)

Direct char-0 (`q ≫ n⁴`) computation of the **pure / monomial-direction** incidence
`I(w) = #{ distinct e₁(S) : S ⊆ μ_n, |S| = w, e₂(S) = 0, e₁(S) ≠ 0 }`.
This is the easy (single-direction) sub-object of the prize incidence, but it is exactly
computable and pins the shape of the q-independent count.

## Exact facts established this round

1. **Support law (free-rank / P7 confirmed).** `I(w) > 0` only at `w ≡ 0, 1 (mod 4)`.
   All other bands have no `e₂=0, e₁≠0` w-subset. (Mann/Lam-Leung antipodal parity.)

2. **Closed form on the low-w / capacity plateau — VERIFIED EXACT n=8,16,32,64:**
   ```
   I(w=4) = (n/4 − 1)·n  =  n²/4 − n
   ```
   multiplier `m = I/n = n/4 − 1` for `n = 8,16,32,64 → m = 1,3,7,15`. Quantized to integer
   multiples of n; multiplier set by the core-size spectrum (all `core=2` at w=4).
   The multiplier is **flat at `n/4−1` across the whole low band `w ∈ [4, ρn]`**
   (n=16: w=4→3, w=8(=ρn)→3 — same multiplier).

3. **⇒ The q-independent incidence is QUADRATIC (`~ n²/4`) at and below the window edge,
   NOT `≤ n`.** This **definitively refutes** the "prize floor = is the q-independent
   incidence ≤ n (a constant-factor question)" reframing carried from round 3. The constant
   is not a constant; the count grows like n²/4 on the plateau.

## The corrected, sharpened localization

- Window = `(1−√ρ, 1−ρ−Θ(1/log n))`. The window **edge** is `δ* = 1−ρ−Θ(1/log n)`, i.e.
  *just below capacity* `1−ρ`, so `w* = (1−δ*)n = ρn + Θ(n/log n)` — **just above** the
  capacity-agreement `ρn`.
- On the plateau `[4, ρn]` (capacity and below) the multiplier is `n/4−1` → quadratic.
- Past capacity it **decays**: n=16 shows `w=8,9 → 3n`, then `w=12,13 → n` (multiplier 3→1)
  over `Δw ≈ n/4`. The `Θ(1/log n)` backoff buys a w-window of `≈ n/log n` past capacity.
- **The prize floor is therefore a DECAY-RATE question, not a bound:**
  does the multiplier decay from `n/4−1` (at `w=ρn`) down to `O(1)` (≤ the `q·ε*=n` budget)
  within the backoff window `w ∈ [ρn, ρn + Θ(n/log n)]`?
  This is the correct statement of what the `Θ(1/log n)` in `δ*` is doing.

## Honest status vs the 72-sweep verdict

This does **not** escape the open core ([[arklib-407-72-conjecture-sweep]]):
- The above is the **pure monomial direction**. The prize needs the **worst** direction,
  whose plateau count is far larger (72-sweep: 3504 at n=16 on a far band, ≫ the pure 48).
- The **decay rate of the worst-direction multiplier** across the capacity→edge transition
  *is* the Gauss-period / Paley-graph bound in disguise — the same open core, in 6 equivalent
  forms. No new closure.

What is genuinely new and correct: (a) the exact closed form `n²/4−n` for the pure plateau,
(b) the `w≡0,1 mod 4` support law, (c) the reframing of the prize floor from a false
"constant bound" to a **decay-rate within the log-backoff window** — a correct localization
of *where* the open content sits and *why* `δ*` carries `Θ(1/log n)`.

## Decisive next measurement (not yet run)

Worst-direction multiplier at the window-edge bands `w = ρn + {1,…,n/log n}` for `n = 32, 64`.
Brute force is infeasible (`C(64,32)`); needs the `Z[ζ]` exact + core-stratification method the
orbits-workflow used. Outcome distinguishes: decay-to-O(1) by `w*` ⇒ floor holds (and would be
a real conjecture); multiplier stays super-constant at `w*` ⇒ floor reduces to the open
Gauss-period bound (consistent with the overdetermined 72-sweep conclusion).
