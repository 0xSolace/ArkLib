# The char-p transfer of the Wick energy bound: why modern machinery resists it, and the archimedean-size mechanism

*#444, 2026-06-22. The Paley wall = the char-0→char-p transfer of the proven Wick energy bound. This round
attacked the transfer with the modern char-p transfer machinery (prismatic, q-de Rham, perfectoid tilting,
Witt/de Rham–Witt, ultraproduct/Lefschetz, o-minimal, specialization, Igusa/motivic, Serre–Tate, crystalline) —
**10 tools, 0 uniform handles** — and pinned the unifying reason + a sharp new mechanism. Honest: not closure.*

---

## The setup

The wall reduces to `E_r(μ_n) ≤ (2r−1)‼·n^r` to depth `r ≈ log p`. The **char-0 version is proven**:
`E_r^∞` (energy of the `2^a`-th roots of unity on the unit circle in `ℂ`) `≤ (2r−1)‼·n^r` for all `r`
(Lam–Leung antipodal / Bessel; in-tree `_AvW0`, `_CharZeroWickEnergy`, `DyadicEnergyK1`). The open core is the
**transfer**: `E_r^{F_p} = E_r^∞ + W_r`, where the **wraparound** `W_r = #{2r-tuples in μ_n summing to 0 mod p
but NOT over ℂ}` is the count of extra mod-`p` coincidences. The wall is `W_r ≤ SLACK_r` to `r ≈ log p`, uniform.

## Result: no modern transfer tool gives a uniform handle (0/10), and the reason is structural

Every one of the 10 tools relocates onto one of two in-tree-certified walls:
- the **valuation/height wall** — the tool's output is a function of `v_p(N(relation))` / Newton polygon /
  Hodge–Tate weight, provably `⊥` the **complex modulus** where `W_r` lives (`_wfJ3`, `_CP_PADIC_FILTRATION`,
  `_AvSD`, `_GrossKoblitzPhaseNoGo`);
- the **onset/`r`-vs-`p` diagonal** — where the tool *does* speak (the no-wrap window `2r < p^{1/d}`, or the
  `√q`-Weil *average* `E_r/p`), it is silent on the worst-case modulus at depth `r ≈ β log p`.

> **The single sharpest reason (the answer to "char-p transfer / new ground"):** every p-adic / cohomological /
> model-theoretic transfer tool is a **functor into p-adic or finite-field-definable data — whose target
> category has no archimedean place.** `W_r` is an archimedean modulus (the `√n` phase cancellation). The
> transfer asks to control an archimedean quantity from a p-adic/finite reduction, which these functors
> structurally cannot do. This is not a coverage gap; it is a category obstruction.

**Closest tool:** ultraproduct / Ax–Kochen / Lefschetz — the *only* one that controls `W_r` **exactly** in a
genuine regime (the no-wrap window `2r < p^{1/d}`, where Łoś transfers the char-0 bound verbatim). It fails by
**one quantifier**: the diagonal `r = ⌊β log p⌋` is not a single first-order sentence (the `ℓ¹`-budget `2r`
grows with the modulus `p` of the lattice it constrains), so the ultraproduct deletes the finite-`p` onset by
construction — re-deriving, *ineffectively*, the in-tree effective `_NoExcessOnsetThreshold`
(`(2r)^{[K:ℚ]} < p ⟹ NoWraparound`).

## The genuinely-new ground

1. **The Witt ghost-collapse (class-level unifying no-go).** Over the perfect base `F_p`, Frobenius `= id` on
   Teichmüller lifts (`[a]^p = [a]` for `a ∈ F_p`), so the ghost components `w_j(S) = S` for all `j`: the **entire
   graded Witt / de Rham–Witt / syntomic tower degenerates to the single datum `v_p(S)`**. This is the strongest
   negative for the whole p-adic-lift family — it explains *why* `_wfJ3` (prismatic), `_AvSD` (Stickelberger),
   `_GrossKoblitzPhaseNoGo` all reduce under **one** mechanism (perfect-base ghost degeneracy), not three
   coincidences. Landable as `_AvWitt_GhostCollapseVacuous` (with the explicit witness `1+g^{n/2}=p`, `v_p=1`,
   which is char-0-*zero* yet has the same valuation as a genuine wrap — so `v_p` cannot separate `W_r=0` from
   `W_r>0`).
2. **The count-side avatar.** `W_r = #Z_r(F_p) − #Z_r(ℂ)`, the mod-`p` collision count of the relation scheme
   `Z_r` (distinct from the magnitude side `|η_b|`) — a genuinely-new lens; the substance (`v_p` does not
   determine `W_r`) is the count-side analogue of the proven magnitude-side `corr(|η_b|, v_p) ≈ 0`.

## The archimedean-size mechanism (verified, the sharp new fact)

`W_r` is driven by the **archimedean size of `p` relative to the cyclotomic relation heights** — *not* the
2-adic residue class. Exact `F_p` computation, `n=8`, `r=3` (`E_3^∞ = 5120`):

| `p` | 17 | 41 | 73 | 89 | 97 | 113 | 137 | 193 | 233 | 281 |
|---|---|---|---|---|---|---|---|---|---|---|
| `W_3 = E_3^{F_p}−E_3^∞` | 10440 | 3120 | 480 | 480 | 480 | 0 | 240 | 0 | 0 | 0 |

`W_3 → 0` as `p` grows, vanishing once `p` exceeds the relation heights (`p ≳ 113`), with sporadic bumps at
slightly larger heights (`240` at `p=137`). It is **not** 2-adically locally constant (within `p≡17 mod 64`,
`W_3` jumps `10440 → 0`), killing every continuity-based (`(q−1)`-adic / 2-adic) transfer. The mechanism:

> **The char-p transfer holds whenever `p > height(relations at depth r)` and fails only when `p ≲ height`.**
> The relation heights grow `b(r)^{n/2}` (exponentially), `b(r)² ∈ {4,5,8,9,12}`. At the prize saddle
> `r ≈ log p`, the heights catch up to `p`, so `W_r > 0` exactly there. The transfer is an **archimedean
> `p`-vs-height comparison** — which is precisely why the p-adic/cohomological tools (seeing valuation, not
> size) cannot capture it, and why the exponential height (no poly-height escape) is the wall.

## Verdict

The char-p transfer of an archimedean-modulus bound resists all 10 modern transfer machineries by a **category
obstruction** (functors into archimedean-place-free targets), unified by the **Witt ghost-collapse**. The
transfer mechanism is made precise: an archimedean `p`-vs-relation-height comparison that holds for `p` above the
(exponentially-growing) heights and fails at the saddle `r ≈ log p`. New ground opened (ghost-collapse no-go,
count-side avatar, the archimedean-size law), but no uniform handle on `W_r` — that remains the wall. NOT closure.
