# Fifty Estimates Against the Burgess Barrier — Honest Synthesis

**Object.** `M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|`, `μ_n` = 2^μ-th roots of unity in
`F_p`, `n=2^μ`, `p~n^4` (Burgess barrier `n~p^{1/4}`), `m=2^128`.
**Target.** `M(n) ≤ C·√(n log m)` with a *p-independent* `C` — i.e. cross Burgess
(whose exponent is *exactly 1* at `p^{1/4}`, giving only the trivial `M ≤ n^{1-o(1)}`).

48 estimates across 6 lanes (sp-shifted, sp-twopower, eq-sheaf, eq-curve, eq-hybrid,
wildcard) were invented, each required to be (a) a precise inequality/identity, (b) Burgess-crossing,
(c) **closed** = reducible only to proven math (Weil on an actual curve / exact algebraic identity /
finite decidable check), not to BGK / Johnson / another open conjecture.

---

## 0. Verified ground (numeric, this session)

Self-contained check at `p~n^4` (smallest prime with `n|p-1`), exact integer energy + brute `M`:

| n | p | p^{1/4} | E_+(μ_n) | 3n²−3n | M | √n | √(2n) | √(n·ln p) |
|---|---|---------|----------|--------|---|----|------|-----------|
| 8 | 4129 | 8.0 | 168 | 168 | 7.56 | 2.83 | 4.00 | 8.16 |
| 16 | 65537 | 16.0 | 720 | 720 | 13.84 | 4.00 | 5.66 | 13.32 |
| 32 | 1048609 | 32.0 | 2976 | 2976 | 22.98 | 5.66 | 8.00 | 21.06 |

Two premises **confirmed**, not assumed:
1. `E_+(μ_n)=3n²−3n` exactly (the multiplicative-/additive-Sidon floor). It is **minimal**,
   yet `M ≈ √(n log p) ≫ √n`. So extra energy cancellation is *not* the lever — the floor
   is already achieved and does not cross.
2. `M(n)` sits at the `√(n log p)` (= BGK/Burgess) scale, *far above* the energy-floor `√n`.
   The whole prize is the `√(log p)` gap between these two scales, exactly where Burgess
   gives nothing and Weil is vacuous (`√p = n² = p^{1/4}`, too big — `μ_n` is 0-dimensional).

---

## 1. Survivors (CLOSED ∧ crosses ∧ true): **NONE**

After adversarial attack, **zero** of the 48 estimates is simultaneously closed, Burgess-crossing,
and true. Every estimate that *crosses* either (i) reduces to BGK/sum-product/another open
conjecture, (ii) is circular (assumes the bound it wants to prove), or (iii) is false. Every
estimate that is *genuinely closed* (reduces to proven Weil / an exact identity / a finite check)
**does not cross** — it reproduces `√(n log p)`, `√p`-vacuity, or the Johnson/energy `√n` scale.

Tally of the 48 self/adversarial verdicts:
- `reduces-to-wall` (BGK / open-conjecture / Johnson / Weil-but-vacuous / circular): **40**
- `false` (refuted by counterexample or sign/structure check): **6**
  (2POW-F, 2POW-H, E2, E6, EQ1, EQ7, W1 — note W1 also false → 7 if counted; see §2)
- `open` (honest residual, reduces to open conjecture): **2** (E8, EQ8)

No `survivor`. The two `open` items are *honest residuals*, not survivors: both explicitly
reduce to open math (effective-conductor constant; coding-theory curve-decodability).

---

## 2. Why the closest candidates fail — the dominant failure mode

**Dominant failure mode (40/48): reduces-to-wall.** The estimate is a correct, often
*exact* algebraic re-encoding of `M`, but the quantitative input it needs is precisely the
open BGK / sum-product / deep-moment bound. Re-naming the wall is not crossing it.

The four sharpest near-misses, and the exact failure:

- **EQ3 / H6 (moment–fiber-product).** EXACT (verified): `Σ_{b∈F_p}|η_b|^{2r} = p·E_r(μ_n)`,
  `E_r` = #F_p-points of the diagonal subgroup variety `W_r`. To beat `√n` you need
  `E_r/(r!·n^r) = 1+o(1)` at depth `r≈log m`. **Fails:** `W_r` is the *deep r-fold subset-sum*
  object = exactly BCHKS Conj 1.12 / di-Benedetto–Garaev at `β=4`; it is the open conjecture,
  not proven Weil (Weil is vacuous on this 0-dim'l fiber product). *reduces-to-open-conjecture.*

- **H1 / W5 (Gauss-sum phase separation).** EXACT (verified): `n·η_b = Σ_{j=0}^{n-1}
  χ̄^j(b)·g(χ^j,ψ)`, `|g(χ^j,ψ)|=√p` for `j≠0`. The amplitudes are *pinned by Weil* (proven!),
  but the **phases** of the `n` Gauss sums are the unknown. Bounding the phase sum below `√(n·√p)`
  = `n^{5/4}` is exactly the open period-equidistribution wall. *reduces-to-BGK.*

- **2POW-A/B/C (coset-tower / quadratic-lift recursion).** EXACT (verified to 1e-16, requires
  `2n|p-1`): `η_b(μ_{2n}) = η_b(μ_n) + η_{gb}(μ_n)` and `S_n(b)=½Σ_{μ_{2n}}e_p(bw²)`. A *true*
  doubling identity. **Fails to recurse:** the recursion is exact on even τ but the odd-part /
  cross term amplifies (the 2-power tower does not contract); the per-level descent would need
  `M(2n) ≤ √2·M(n)` which is exactly the open per-level sub-Gaussian claim. *reduces-to-BGK.*

- **W1 (dyadic orthogonal doubling).** Looks like a clean tensor recursion `η_b(μ_{2n})=…`
  with claimed orthogonality of the two halves. **FALSE:** the two summands `η_b(μ_n)` and
  `η_{gb}(μ_n)` are *not* orthogonal (the cross term `Cov(η_a,η_b)=−Var/(m−1)` is nonzero,
  exchangeable not independent — see prior MEMORY: periods are exchangeable white-noise with
  one linear constraint, NOT log-correlated/independent). Assuming orthogonality is circular and
  the numeric cross-term refutes it. *circular/false.*

**The single most common failure: "exact identity → reduces to BGK/open."** ~30 of 48 are
*provably correct exact identities or inequalities* (this is the genuine value below) whose
quantitative consequence is the open wall. The barrier is not a lack of identities; it is that
*every* identity relocates the same `√(log p)` gap between the energy floor `√n` and `√(n log p)`.

**False (6–7):** 2POW-F (Klein-4 inverse cancellation — sign structure refuted), 2POW-H (2-power
extremality — μ_n is NOT uniformly best-equidistributed among order-n subgroups; refuted at thick
β), E2 (isotypic line-bundle split — circular, the split doesn't bound the phase), E6 (depth-aspect
dyadic tower — reduces to open *and* the iterate conductor explodes), EQ1 (complete-power-sum-Weil —
the completion `Σ_{z}e_p(bz^m)` is a *full* exponential sum, Weil gives `√p=n²`, no-go, and the
claimed crossing bound is false), EQ7 (dimension-lift to positive-dim W_r — Weil applies but gives
`√p`-scale error = vacuous, claimed crossing false), W1 (above).

**Circular (E2, E4, E5, 2POW-D, 2POW-E, W4, W8):** assume the equidistribution / norm-floor /
flatness they are trying to prove, or use `|η_b|≥1` (algebraic-integer norm floor) which bounds
*below* not above and is `cross=no`.

---

## 3. Most promising candidate (still fails) + what closing it needs

**Best: EQ3/H6 — the moment–fiber-product route, `Σ_b|η_b|^{2r}=p·E_r(μ_n)`.**

Why it is the best: it is the *only* route that is (i) an exact, machine-verified identity,
(ii) genuinely Burgess-crossing **if** the input holds (a sub-Gaussian deep moment immediately
gives `M ≤ √(n log m)` by the standard moment→sup bound at `r≈log m`), and (iii) connects to a
*named, current* object — BCHKS Conjecture 1.12 (the framework authors' own Nov-2025 paper,
ePrint 2025/2055) and di-Benedetto–Garaev at `β=4`.

**The gap (precise):** one needs `E_r(μ_n) ≤ (1+o(1))·r!·n^r` for `r` up to `≈ log m ≈ 128`,
at `p~n^4`. Equivalently: the number of distinct r-fold subset relations in `μ_n` does not
exceed the random/Wick count at logarithmic depth. **What it would take to close:**
- Prove the deep-moment (r≈log) sub-Gaussianity of `μ_n` *directly* — currently OPEN. Note the
  known refutation: at 2-power-*structured* primes (Fermat p=65537, n=64) the raw r-th moment
  *explodes* past `r~log_n p` (ratio →815, MEMORY: cumulant-dichotomy), so any proof MUST be a
  **non-moment** argument at structured primes, or restrict to the prize's *thin* regime
  (`n≤p^{1/4}`, β≥4) where the structured blow-up may be tamed. No proven Weil/curve realizes
  `W_r` with bounded genus (the fiber product is 0-dimensional and high-conductor), so the curve
  door (EQ2/EQ6 no-gos) is closed. The honest path is the BCHKS conjecture itself — i.e. it is
  **open math**, confirming the prize is not currently closeable.

---

## 4. Genuinely NEW closed sub-results (true + proven bricks — valuable, non-crossing)

These are real bricks (true, reduce to proven math / finite check), even though none crosses:

1. **`E_+(μ_n)=3n²−3n` exactly** (additive/multiplicative Sidon floor for `n=2^μ`, `p>2^n`).
   Verified here n=8,16,32; matches prior `rootsOfUnity_additiveEnergy_eq_sidon` Lean brick.
   *Proven, finite/algebraic.* Establishes the floor is *minimal yet non-crossing*.
2. **Exact doubling identity** `η_b(μ_{2n}) = η_b(μ_n) + η_{gb}(μ_n)` and quadratic lift
   `S_n(b)=½Σ_{w∈μ_{2n}}e_p(bw²)` (2POW-A/B). *Exact, verified 1e-16.* A correct, reusable
   recursion — the obstruction is its non-contraction, which is itself a clean negative brick.
3. **Gauss-sum separation** `n·η_b = Σ_{j}χ̄^j(b)g(χ^j,ψ)`, `|g(χ^j,ψ)|=√p` (H1/W5).
   *Exact + Weil-pinned amplitudes.* Cleanly isolates "all the difficulty is in the `n` Gauss
   phases," matching the constant-index `norm_gaussSum_eq_sqrt` Lean brick already landed.
4. **Moment master identity** `Σ_{b∈F_p}|η_b|^{2r}=p·E_r(μ_n)` (EQ3). *Exact, verified.*
   The canonical bridge; `E_2=3n²−3n→` recovers (1); `E_3=15n³−45n²+40n` (prior char-0 brick).
5. **Two structural NO-GOs (proven):** EQ2/EQ6 — *any* geometrically-irreducible positive-dim'l
   variety, even optimal bounded-genus `O(1)`/`O(log n)`, gives a Weil error floor `≥` the
   `√p`-scale = vacuous for `μ_n`. This **proves the curve/Weil door is shut**, redirecting all
   effort to the arithmetic (BCHKS) door. A genuinely useful elimination.
6. **2-power non-extremality (refutation, proven):** μ_n is NOT the best-equidistributed order-n
   subgroup uniformly (2POW-H false). Kills the "exploit 2-power structure for free" hope.

These are the publishable bricks: floor identity, doubling identity, Gauss separation, moment
bridge, the two-line Weil no-go, and the non-extremality refutation.

---

## 5. Honest bottom line

**There is NO closed estimate that crosses Burgess.** All 48 confirm — from six independent
lanes — that crossing `p^{1/4}` requires **genuinely open math**. The structure is now sharp and
not larp:

- The energy floor (√n) is *achieved* and provably does *not* cross (E_+ minimal yet M≈√(n log p)).
- Every exact identity (~30 of them, several verified to 1e-16) relocates the *same* `√(log p)`
  gap; none collapses it.
- The proven-Weil/curve door is **shut** by a two-line no-go (0-dimensionality → `√p` error
  floor = `n²` = vacuous; EQ2/EQ6).
- The only crossing-capable route (EQ3/H6 moment–fiber-product) reduces *exactly* to BCHKS
  Conj 1.12 / di-Benedetto–Garaev `β=4` — an **open** deep-moment / sum-product conjecture, with a
  known *non-moment* obstruction at 2-power-structured primes.

So: the prize is **not** closeable with present proven tools; crossing Burgess at the
`p^{1/4}` barrier is equivalent to a currently-open sum-product/equidistribution conjecture. The
deliverables of this round are the **closed bricks of §4** and the **sharpened localization**
(the open core is precisely the deep-moment `E_r(μ_n) ≤ (1+o(1))r!n^r` at `r≈log m`, off the
curve door, on the arithmetic door, non-moment-essential at structured primes).
