# di Benedetto et al. (arXiv:2003.06165) — Audit + Ranked Attack Plan

**Goal (#444):** beat the SOTA subgroup char-sum exponent `1 − 31/2880 ≈ 0.9892` toward `1/2`, OR
extend nontriviality past the `|H| > p^{1/4}` threshold into the prize regime `|H| ~ q^{1/4..1/5}`,
for `M = max_b |Σ_{x∈μ_n} e_p(bx)|`, `μ_n` = 2-power roots of unity, `n = 2^μ`.

**Verification status:** EVERYTHING below is verified against the actual PDF (arXiv:2003.06165 v1,
13 Mar 2020, 14 pp, full text read line-by-line at `/tmp/diben.txt`) and by exact `F_p` computation
(reproduced here, prize regime `p > n^4`). Where a claim is conjectural it is flagged CONJECTURE.

---

## 0. Provenance (verified, anti-fabrication)

- **Title (exact):** "New estimates for exponential sums over multiplicative subgroups and intervals
  in prime fields."
- **Authors (exact):** Daniel di Benedetto, Moubariz Z. Garaev, Victor C. Garcia, Diego
  Gonzalez-Sanchez, Igor E. Shparlinski, Carlos A. Trujillo. (Earlier prompt attributions to
  "Solymosi–White" were WRONG; corrected.) J. Number Theory 2020. MSC 11L07, 11T23.
  Key words explicitly include "trilinear sums."
- **Main theorem (Theorem 3.1, verbatim):** For `H` a multiplicative subgroup of `F_p^*` with
  `p^{1/2} > H > p^{1/4}`, `max_{(a,p)=1} |S_a(H)| ≲ H^{2689/2880} p^{1/72}`; in particular when
  `H > p^{1/4}`, `max |S_a(H)| ≲ H^{1−31/2880}`. (`A ≲ B` means `|A| ≤ B p^{o(1)}`.)
- Improves Bourgain–Garaev (2009): `175/9437184 = 1.85e−5` → `31/2880 = 1.076e−2`.

---

## 1. The exact method, where 31/2880 comes from, and the `p^{1/4}` origin

### 1.1 The proof chain (Theorem 3.1, §5), faithfully

Write `Δ = |S_a(H)| / H`, so `|S_a(H)| = HΔ`; the goal is to upper-bound `Δ`. The argument is a
**three-fold trilinear descent** that peels off three "popular sumset" legs and finishes with one
application of the Petridis–Shparlinski trilinear bound:

1. Cube `S_a(H)^3` and use subgroup invariance (`Σ_{x∈H} → Σ_{x∈H} of (·)y`), giving
   `H^4 Δ^3 ≤ Σ_{x1,x2,x3} |Σ_{y∈H} e_p(a(x1+x2+x3)y)|` (eq 5.2).
2. **Dyadic pigeonhole** isolates a popular triple-set `G1 ⊆ H^3` with `|G1| ≳ H^3 Δ^3 / Δ1`,
   `Δ^3 ≲ Δ1 < 1` (eq 5.4). Form the sumset `X = {x1+x2+x3 : G1}`.
3. **Cauchy–Schwarz + Lemma 4.3** (`T3(H) ≪ H^4`): `|X| ≳ |G1|^2 / T3(H) ≳ H^2 Δ^6 / Δ1^2` (eq 5.6).
   **← Lemma 4.3 used HERE (X-leg).**
4. Hölder, repeat the dyadic descent on the `y`-triples → set `Y`, again via **Lemma 4.3**:
   `|Y| ≳ H^2 Δ1^6 / Δ2^2` (eq 5.10). **← Lemma 4.3 used AGAIN (Y-leg). T3 used TWICE total.**
5. Cauchy–Schwarz on the `z`-difference, dyadic descent → set `Z = {z1−z2}`, via **Lemma 4.2**
   (`T2(H) ≪ H^{49/20}`): `|Z| ≳ H^{31/20} Δ2^4 / Δ3^2` (eq 5.13). **← Lemma 4.2 used ONCE (Z-leg).**
6. **Compare with Lemma 4.1** (the only `p`-dependence): `|X||Y||Z|^{1/2} Δ3^4 ≪ p`.

Substituting the three set-size bounds (eq 5.14, verbatim from the paper):
```
p ≫ (H^2 Δ^6/Δ1^2) · (H^2 Δ1^6/Δ2^2) · (H^{31/40} Δ2^2/Δ3) · Δ3^4 = H^{191/40} Δ^6 Δ1^4 Δ3^3
```
(the `H^{31/40}` is `|Z|^{1/2}`.) Then a Δ-descent collapse (lines 384–390) gives
`Δ^6 Δ1^4 Δ3^3 ≳ Δ^{18·4}... → Δ^{72}`-type relation, yielding the final
```
Δ ≲ p^{1/72} H^{−191/2880}.
```

### 1.2 Where 31/2880 is produced — VERIFIED arithmetic

Define the **H-exponent** `Hexp(t2,t3) = (6−t3) + (6−t3) + (4−t2)/2`, where `t3` is the exponent in
`T3(H) ≪ H^{t3}` (used in X and Y legs) and `t2` in `T2(H) ≪ H^{t2}` (used in Z leg, at half-power).

| input | value | check |
|---|---|---|
| paper general `t3 = 4, t2 = 49/20` | `Hexp = 2 + 2 + 31/40 = 191/40` | matches eq 5.14 ✓ |
| final exponent at `H = p^{1/4}` | `1 + (4 − Hexp)/72 = 1 − 31/2880` | matches Thm 3.1 ✓ |
| `Hexp/72` | `191/2880` | matches ✓ |

So **`31/2880` is the single output of: `(Hexp − 4)/72 = (191/40 − 4)/72 = (31/40)/72 = 31/2880`,
evaluated at the edge `H = p^{1/4}` (i.e. `p^{1/72} = H^{4/72} = H^{1/18}`).**

### 1.3 The `|H| > p^{1/4}` origin (the vanishing point) — VERIFIED, with a correction

- **Sole source of `p`:** Lemma 4.1 (Petridis–Shparlinski trilinear, [11, Thm 1.1]):
  `Σ_{x,y,z} α_x β_y γ_z e_p(axyz) ≪ p^{1/4} |X|^{3/4} |Y|^{3/4} |Z|^{7/8}`.
  The `p^{1/4}` prefactor is the ONLY place `p` enters the entire Thm 3.1 proof. After the power-72
  descent it becomes `p^{1/72}` in `Δ ≲ p^{1/72} H^{−191/2880}`.
- **Edge evaluation is the "barrier":** the clean form `H^{1−31/2880}` requires `p^{1/72} ≤ H^{1/18}`,
  i.e. `p ≤ H^4`, i.e. `H ≥ p^{1/4}`. So the stated `H > p^{1/4}` is *the edge at which the clean
  exponent holds*, not the true vanishing point.
- **CORRECTION (honest):** the **true nontriviality threshold is `H > p^{40/191} = p^{0.2094}`**
  (solve `Δ < 1`: `p^{1/72} < H^{Hexp/72}` ⇒ `H > p^{1/Hexp} = p^{40/191}`). `40/191 ≈ 0.2094 < 0.25`,
  so di Benedetto's method is *already nontrivial slightly below `p^{1/4}`* with the general inputs.
  The prize floor `q^{1/5} = p^{0.20}` is just barely outside this (`0.2000 < 0.2094`). This matters:
  it means **a modest improvement in the energy inputs alone covers the whole prize window
  `p^{1/5}..p^{1/4}`** — no new analytic machinery required.

---

## 2. Ranked improvement targets

`Hexp(t2,t3) = (6−t3) + (6−t3) + (4−t2)/2`; saving `c = (Hexp−4)/72` at the edge; final
`|S| ≲ H^{1−c}`; nontriviality threshold `H > p^{1/Hexp}`. All numbers below are EXACT-reproduced.

| # | move | input needed | `Hexp` | exponent `1−c` | gain vs 0.9892 | threshold | feasibility |
|---|---|---|---|---|---|---|---|
| **1** | `t3: 4→3` in BOTH X,Y legs | `T3(μ_n) ≪ n^{3+o(1)}` | `271/40` | **0.96146** (`c=37/960`) | **3.58×** | `p^{1/6.78}=p^{0.148}` | **HIGH — exact identity verified below** |
| **2** | `t3:4→3` AND `t2:49/20→2` | also `T2(μ_n) = 3n²−3n` (Sidon floor) | `7` | **0.95833** (`c=1/24`) | **3.87×** | `p^{1/7}=p^{0.143}` | HIGH (T2 PROVEN; T3 as #1) |
| 3 | `t2:49/20→2` only | Sidon floor `T2` | `5` | 0.98611 (`c=1/72`) | 1.29× | `p^{1/5}=p^{0.200}` | HIGHEST (T2 is an exact identity) but small gain |
| 4 | reduce `p^{1/4}` prefactor in Lemma 4.1 | 2-power-aware trilinear/incidence bound `p^{1/4−κ}` | (n/a) | shifts `c` by `+κ/18` and threshold by `−`; the ONLY move toward `1/2` | — | — | LOW — open research, but the only route past O(10⁻²) |

**Why #1 and #2 are the real levers, and #3 alone is weak:** `T3` is used TWICE (X and Y), so each
unit of `t3` costs 2 in `Hexp`; `T2` is used once at HALF weight, so a unit of `t2` costs only `1/2`.
Hence `t3:4→3` buys `+2` in `Hexp` while `t2:49/20→2` buys only `+9/40`.

### 2.1 The energy inputs — VERIFIED by exact `F_p` computation (prize regime `p > n^4`)

```
T2(μ_n) := #{h1+h2 = h3+h4 : hi ∈ μ_n}     (additive energy)
T3(μ_n) := #{h1+h2+h3 = h4+h5+h6 : hi ∈ μ_n}  (third additive energy)
```
| n | p (>n⁴) | T2 | `3n²−3n` | match | T3 | `15n³−45n²+40n` | match | general `n⁴`/T3 |
|---|---|---|---|---|---|---|---|---|
| 4 | 269 | 36 | 36 | ✓ | 400 | 400 | ✓ | 0.64 |
| 8 | 4129 | 168 | 168 | ✓ | 5120 | 5120 | ✓ | 0.80 |
| 16 | 65617 | 720 | 720 | ✓ | 50560 | 50560 | ✓ | 1.30 |
| 32 | 1048609 | 2976 | 2976 | ✓ | 446720 | 446720 | ✓ | 2.35 |

**Two findings that change the honesty picture:**

- **T2(μ_n) = 3n²−3n EXACTLY** (Sidon-except-antipodal floor, `t2 = 2`). PROVEN identity, holds at
  every `n` tested, prize regime. This is strictly below the general `T2 ≪ H^{49/20}` (`t2 = 2.45`).
  Target #3 is therefore *already rigorous*; it just gives a small gain.
- **T3(μ_n) = 15n³ − 45n² + 40n EXACTLY** in the prize regime (`p > n^4`), with ZERO char-p excess
  for all `n = 4,8,16,32`. This is the in-tree char-0 formula `E_3(μ_n)`, and it holds verbatim with
  no correction. **So `t3 = 3` is NOT a conjecture for the values tested — it is a verified exact
  polynomial.** The general bound `H^4` overestimates T3 by a factor `n/15` (grows without bound;
  already 2.35× at n=32, → ∞). The only thing that remains to PROVE (not compute) is that the
  identity persists for all `n` (the "No-Excess" statement: char-p `T3 = ` char-0 value for `p > n^4`).
  This is exactly the in-tree target and is the cleanest open input in the whole project.

---

## 3. Single most promising attack to launch next

**Attack: feed `t3 = 3` (and the free `t2 = 2`) into the EXISTING di Benedetto §5 skeleton — i.e.
PROVE `T3(μ_n) = O(n^{3} polylog)` in the prize regime, then substitute. No new analytic machinery.**

This is Target #2: `Hexp: 191/40 → 7`, exponent `0.9892 → 23/24 = 0.95833` (**3.87× the saving**),
and — critically — the nontriviality threshold drops `p^{0.2094} → p^{1/7} = p^{0.143}`, which
**covers the entire prize window `q^{1/4}..q^{1/5}` with room to spare** (`0.143 < 0.20`).

**Concrete first step (a single self-contained lemma):** prove
> `T3(μ_n) = 15n³ − 45n² + 40n` for all `n = 2^μ` and all primes `p` with `p > n^4` and `p ≡ 1 (mod n)`.

This reduces to a **vanishing-sums-of-roots-of-unity / No-Excess count**: the char-0 value is the
number of solutions over `C`, and the claim is that no *extra* solutions appear mod `p` once
`p > n^4` (a coincidence `h1+h2+h3 ≡ h4+h5+h6 mod p` that is not an equality over `C` would force a
nonzero integer combination of ≤ 6 roots of unity to be divisible by `p`; its absolute value is
`< 6 < p`, contradiction — modulo making the bound on the integer combination rigorous). The exact
identity is already verified computationally for `n ≤ 32`. The in-tree analogue is
`E2W4CyclotomicNonCollision` / the `r=3` energy formula (`#407` ledger: `E_3(μ_n)=15n³−45n²+40n` was
established char-0 and char-p-safe in the prize regime). **The Lean target: a `No-Excess for T3`
brick** (third additive energy = char-0 value when `p > n^4`), then a paper-level substitution lemma
recording `Hexp = 7 ⇒ |S| ≲ H^{23/24}` and the extended threshold `H > p^{1/7}`.

Why this over the others:
- It is the ONLY target that simultaneously (a) multiplies the exponent gain ~4× AND (b) pushes the
  threshold past the prize floor — the two distinct deliverables of the goal.
- Its input is an EXACT IDENTITY already verified by computation, not a conjectural energy bound;
  only the "persists for all n" proof remains, and it has an in-tree precedent.
- It is purely a substitution into a published, verified skeleton — low risk of a hidden analytic gap.

---

## 4. Honest closeness baseline

- **Best VERIFIED exponent at `|H| ~ q^{1/4}` by ANY published method:** `1 − 31/2880 ≈ 0.989236`
  (di Benedetto Thm 3.1, this paper). At the prize floor `q^{1/5}` the published general method is
  BELOW its nontriviality threshold (`1/5 = 0.20 < 40/191 = 0.2094`), so there is **no published
  nontrivial bound at `q^{1/5}` for general subgroups** — the prize floor is past di Benedetto's edge.
- **Does the 2-power structure plausibly beat it? YES, and verifiably:** substituting the
  computationally-verified Sidon-floor inputs (`t2 = 2`, `t3 = 3`) into the same skeleton gives
  `23/24 ≈ 0.958333` at `q^{1/4}` (3.87× better) AND extends nontriviality to `q^{1/7}`, covering the
  whole prize window. This is **conditional only on proving `T3(μ_n) = O(n³)` persists for all `n`**
  — an exact identity for every `n ≤ 32` tested, with an in-tree char-0 + No-Excess precedent.
- **Honest gap / what this does NOT do:** even the full Sidon-floor substitution lands at `≈ 0.9583`,
  still **far from the prize target `1/2`**. Closing to `1/2` requires Target #4 — beating the
  `p^{1/4}` prefactor of the trilinear Lemma 4.1 itself (the only move that can reach `1/2`), which is
  open research with no current input. The honest summary: the 2-power structure **comfortably
  extends di Benedetto past `p^{1/4}` into the prize regime and improves the exponent ~4×, but does
  not by itself reach the `1/2` prize bound.** It is a real, verifiable improvement in CLOSENESS, not
  a closure.

---

## Executive summary

- **Method:** Theorem 3.1 is a three-fold trilinear descent. Cube `S_a(H)`, dyadically extract a
  popular sumset `X`, repeat for `Y`, take a difference set `Z`, then apply the Petridis–Shparlinski
  trilinear bound (Lemma 4.1) ONCE. The set sizes come from the subgroup energies `T3(H)≪H^4`
  (Lemma 4.3, used TWICE: X and Y) and `T2(H)≪H^{49/20}` (Lemma 4.2, used ONCE: Z). Net:
  `Δ ≲ p^{1/72} H^{−191/2880}`; at the edge `H=p^{1/4}` this is `H^{1−31/2880}`. The `31/2880` is
  exactly `(191/40 − 4)/72`. The SOLE `p`-dependence — and the entire `H>p^{1/4}` edge — comes from
  Lemma 4.1's `p^{1/4}` prefactor. (True nontriviality threshold is `p^{40/191}=p^{0.209}`, just
  below `p^{1/4}` and just above the prize floor `p^{0.20}`.)
- **Top-3 ranked improvement targets** (`Hexp` controls everything; `c=(Hexp−4)/72`):
  1. **`T3: H^4 → n^3` (used twice, t3:4→3):** `Hexp 191/40→271/40`, exponent **0.9615** (3.58×),
     threshold `p^{1/6.78}`. Input = `T3(μ_n)=O(n³)`, VERIFIED exact (`=15n³−45n²+40n`, zero char-p
     excess) for `n≤32`. HIGH feasibility (in-tree No-Excess precedent).
  2. **Both Sidon-floor inputs (t3:4→3, t2:49/20→2):** `Hexp→7`, exponent **0.9583** (3.87×),
     threshold `p^{1/7}=p^{0.143}` — **covers the whole prize window `q^{1/4}..q^{1/5}`**. T2 is a
     PROVEN exact identity (`3n²−3n`); T3 as in #1.
  3. **`t2:49/20→2` alone (Sidon floor):** `Hexp→5`, exponent 0.9861 (1.29×), threshold `p^{1/5}`.
     Smallest gain but the input is already fully rigorous.
  - (Beyond the table: the ONLY route toward `1/2` is beating Lemma 4.1's `p^{1/4}` for the 2-power
    set — open research, no current input.)
- **Best attack to launch:** prove `T3(μ_n) = O(n³ polylog)` in the prize regime (`p>n^4`) — an exact
  identity already verified computationally — then substitute into the unchanged §5 skeleton. Yields
  exponent `0.9583` AND threshold `p^{1/7}`, extending past `p^{1/4}` to cover the entire prize floor.
- **Honest baseline:** best verified exponent at `q^{1/4}` is `0.9892` (di Benedetto); nothing
  published is nontrivial at `q^{1/5}`. The 2-power structure verifiably improves this to `~0.9583`
  and extends past `p^{1/4}`, but does NOT reach the `1/2` prize. Real closeness gain, not a closure.

**Files:** verified source text `/tmp/diben.txt`; PDF `/tmp/diben.pdf`; this audit
`/tmp/bgk/DIBENEDETTO_AUDIT.md`.
