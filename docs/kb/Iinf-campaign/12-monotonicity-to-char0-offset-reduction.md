# The monotonicity → char-0 offset reduction (2026-06-16)

A genuinely different reduction of the prize floor — to a **char-0 (q-independent) cyclotomic offset
bound**, NOT the open char-p BGK character sum. Promising; the decisive `n=32` exact test is running.
Honest: not yet a closure (the char-0 offset asymptotic is unconfirmed and may grow).

## The chain
1. **Proven (ring-hom monotonicity, §5.1, axiom-clean Lean):** the char-p bad-scalar set is the IMAGE of
   the char-0 set under `ℤ[ζ_n] → F_q`, so `#bad_q(line,δ) ≤ #bad_0(line,δ)` for every line, δ. Max over
   lines ⇒ `I_q(δ) ≤ I_0(δ)` ⇒ **`δ*_q ≥ δ*_0`** (the prize δ* is at least the char-0 δ*).
   (Moreover, since the prize prime `q≈n·2^128` exceeds the collision threshold `(2w)^{φ(n)}` for `n ≲ 50`,
   `I_q = I_0` exactly there; for larger n, `I_q ≤ I_0` with the gap = char-p deletions, which only help.)
2. **Far-line δ* as an offset:** `I_0(δ)` crosses the budget `n` at agreement `w* = k + offset₀(n)`
   (`k=ρn`), so `δ*_0 = (1−ρ) − offset₀(n)/n`. The window edge is `δ_we = (1−ρ) − Θ(1/log n)`, i.e.
   offset `n/log₂n`.
3. **Therefore:** `δ*_q ≥ δ*_0 ≥ δ_we  ⟺  offset₀(n) ≤ n/log₂n`. **The prize FLOOR holds iff the char-0
   far-line offset grows no faster than `n/log n`.** That is a statement about `I_0`, the char-0 incidence
   — a finite, q-independent, cyclotomic count (Lam–Leung / antipodal rigidity), with **no character sum
   over `F_q` and no BGK**.

## Why this is different from "reduces to BGK"
The campaign's fixed-point theorem (every face = one object = the char-p Gauss-sum phase / BGK) was about
the char-p incidence at the prize prime. The monotonicity says we never needed the char-p value — only
that the **char-0** value is small enough at the window edge. The char-0 incidence is the q-independent
cyclotomic object; bounding its offset is proven-math-adjacent (the antipodal/free-rank machinery we have),
not the open analytic thin-subgroup character sum. **If `offset₀(n) = o(n/log n)`, the prize closes via
proven monotonicity + a char-0 cyclotomic bound.**

## Data (validated against the issue's exact pins)
The far-line engine reproduces the issue's exact `δ*(8)=3/8`, `δ*(16)=9/16` — both **offset 3**.
Compare to the window-edge offset `n/log₂n`:
| n | offset₀ | `n/log₂n` (window-edge offset) | floor (offset₀ ≤ n/log n)? |
|---|---|---|---|
| 8  | 3 | 2.67 | marginally NO (small-n boundary) |
| 16 | 3 | 4.00 | YES |
| 32 | ? | 6.40 | **decisive test running (exact, 2-prime CRT)** |

If `offset₀(32) ≈ 3` (≪ 6.4), the char-0 offset grows far slower than `n/log n` ⇒ floor holds for all
large n ⇒ **potential closure**. If `offset₀(32) ≈ 6` (≈ 6.4), the offset tracks the window edge ⇒ tight ⇒
open (the issue's conclusion). The issue only had `n ≤ 16` and assumed the `1/log n` (tracking) form; the
`n=32` exact char-0 offset is new and distinguishes the two.

## Honest caveats (why this is a lead, not yet a closure)
- **Faithfulness:** the char-0 collision threshold is `(2w)^{φ(n)} ≈ 2^{30}` (n=16), `2^{71}` (n=32). A
  single prime below this is char-p (a lower bound). The `n=32` result uses **two primes `~2^36`, product
  `>2^71`**, deduping bad scalars by `(γ mod 𝔭₁, γ mod 𝔭₂)` — exact char-0. (n=8,16 should be re-checked
  the same way; the issue's "exact" pins suggest offset 3 is the true char-0 value there.)
- **3 points ≠ proof.** Even `offset₀=3` at n=8,16,32 is evidence for `O(1)`/slow growth, not a proof.
  Closing requires PROVING `offset₀(n) = o(n/log n)` — a char-0 cyclotomic theorem (the actual target).
- **The risk:** the issue concluded the char-0 incidence reduces to BGK; if `offset₀` does grow like
  `Θ(n/log n)`, this reduction gives `δ*_q ≥ δ_we` with equality — still the floor, but tight and matching
  the open conjecture. The `n=32` test resolves which.

## If the test supports O(1) offset: the provable target
Prove: the char-0 worst far-line incidence at agreement `k + c·n/log n` is `≤ n` for some `c>0` and all
dyadic n. Equivalently (cyclotomic): the number of distinct `e_t(S)` over `μ_{2^a}`-configs with
`e_1=…=e_{t−1}=0` at the window-edge band is `O(n)`. This is Lam–Leung/antipodal-rigidity territory — a
finite, q-independent, character-sum-free statement. THAT is the prize, in a form that does not invoke BGK.

Tools: /tmp/n32ex.c (2-prime CRT exact engine), /tmp/dstar.c (validated far-line engine, reproduces
issue pins). Related: [[arklib-407-multiplier-decay]], 11-deltastar-offset-law-and-monotonicity-localization.md.

## UPDATE (2026-06-16) — EXACT char-0 (2-prime CRT) REFUTES the lead, and CORRECTS the issue's pin
Built a faithfulness-aware exact engine: the single-prime values were char-p (the collision threshold is
`(2w)^{φ(n)} ≈ 2^{30}` at n=16, far above small primes). Deduping bad scalars by `(γ mod 𝔭₁, γ mod 𝔭₂)`
with `𝔭₁𝔭₂ ~ 2^{72} > threshold` gives the TRUE char-0 count. Result (n=16, **validated across two
independent prime pairs `~2^18` and `~2^20`, identical**):

| w | offset | char-0 (CRT, exact) | char-p p=65537 (Fermat) |
|---|---|---|---|
| 6 | 2 | 200 | 89 |
| 7 | 3 | **120** | **16 ← polluted** |
| 8 | 4 (=window-edge offset) | **120** | 16 |
| 9 | 5 | 16 = budget | — |

**So the true char-0 offset at n=16 is 5, not 3.** The issue's "exact `δ*(16)=9/16`" (offset 3) used the
Fermat prime `65537`, which collapsed 120 distinct char-0 bad scalars to 16 — a `7.5×` pollution. The true
char-0 `δ*(16) = 7/16` (offset 5). (This is consistent — `δ*` may sit below Johnson; the unconditional
lower bound is *half*-Johnson `(1−√ρ)/2 = 0.25`, and `7/16 = 0.4375 > 0.25`. The Fermat value `9/16` was an
over-estimate from under-counting.)

**This REFUTES the closure lead.** The char-0 far-line incidence at the window-edge offset (`n/log₂n = 4`
for n=16, w=8) is **120 ≫ budget 16**. So `δ*_char0 < window edge`, the offset is `5 > 4`, and the
monotonicity bound `δ*_prize ≥ δ*_char0` lands *below* the window edge — it does NOT give the floor. The
prize genuinely needs the char-p deletions (= BGK) to climb from `δ*_char0` to the window edge. **This
independently re-derives the issue's "reduces to BGK" verdict** — now with the precise correction that the
char-0 incidence at the window edge is super-budget (`120` vs `16` at n=16), and a validated fix to the
δ*(16) pin. (n=8 char-0 offset is 2 but degenerate — `I` jumps 56→0, a small-n "ran out of configs"
effect. n=32 exact CRT still running; expected to confirm offset `> 6.4`.) Honest: lead refuted; the
Fermat-pollution correction to δ*(16) and the validated CRT methodology are the genuine residue.
