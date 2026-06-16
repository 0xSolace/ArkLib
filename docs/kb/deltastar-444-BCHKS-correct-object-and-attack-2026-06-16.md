# BCHKS-1.12 — the CORRECT object, why the in-tree Prop is mis-stated, and the proof attack (#444)

**Goal:** fully PROVE the floor that pins the exact δ* lower bound. This file corrects what that
floor actually IS (the in-tree `BCHKS1_12` Prop is a mis-statement) and lays out the attack on the
correct object. Source of truth: ABF26 §4 (`docs/kb/prize-407-faithful-problem-map-from-abf26.md`)
+ my exact computation.

## A. The in-tree `BCHKS1_12` Prop is FALSE / vacuous as stated [VERIFIED]

`_BridgeB31.BCHKS1_12` (and `_CoreReductionComplete`, `_CoreA7`) state it as
> `∃ c, ∀ n, ∃ m ≤ c·log₂ n, |Σ_r(μ_s)| ≤ budget`, with `Σ s r = |Σ_r(μ_s)|` the **distinct
> r-fold subset-sum count** and `budget = q·ε* ≈ s`.

**This is FALSE.** Exact computation (large/char-0 prime, `probe`): `|Σ_r(μ_s)|` GROWS monotonically
in r and is ALWAYS `≫ s`:
- n=s=8:  `|Σ_r|` = 33, 96, 225, 456, 833, 1408, 2241  (r=2..8) — never ≤ 8.
- n=s=16: `|Σ_r|` = 129, 704, 2945, 10128, 29953, 78592, 185617 — never ≤ 16.

There is **no depth r ≤ c·log s with `|Σ_r| ≤ s`**. So the `∃ m, BCHKSBudget` hypothesis is
**unsatisfiable** with this `Σ`. The "prize ⟸ BCHKS-1.12" reduction (`prize_reduces_to_BCHKS`) is
therefore **VACUOUSLY true on a false hypothesis** — it proves nothing about the prize. (Consistent
with B33 `objectIdentity_false`: the cascade `D` decreases while `Σ_r` increases — they are different
objects, and the dedup `D ≤ Σ_r` has *enormous* growing slack, so bounding `D` via `Σ_r` is useless.)

**Why the swarm reached this:** it identified the prize object with the raw subset-sum count `|Σ_r|`.
But `|Σ_r|` is the SUMSET SIZE `|H^{(+r)}|`, which is *supposed to be the budget multiplier*, not the
bad-scalar count itself. The mis-statement put the sumset on the wrong side of the inequality.

## B. The CORRECT floor — Sumset-Extremality (ABF26 §4) [the real target]

`|F|` is taken **LARGE** (not fixed at `n·2^128`); the soundness error is `(stuff)/|F|`, and **δ* is
the radius where `(stuff)` (the bad-scalar count) goes from `poly(n)` to super-poly** (crosses
`ε*·|F|`). The open FLOOR is:
> **Sumset-Extremality.** For every affine line `(f,g)` and every `δ` below the threshold,
> `#{λ : Δ(f + λg, C) ≤ δ} ≤ poly(n) · |H^{(+r)}|`,
> where `H^{(+r)}` is the `r`-fold sumset of the subgroup `μ_s` (so `|H^{(+r)}| = |Σ_r|`) and
> `r = ⌊δn⌋`-related depth. The bad-scalar count is bounded by `poly · (sumset size)`.

Key facts from ABF26 §4 + this session:
- **The subset-sum ceiling `e_j = C(s,r)` is NOT tight** (REFUTED, faithful map line 131): the
  worst CHAR-FREE direction is the **complete-homogeneous** one, `h_j = C(s+r−1, r)`, with
  `log(h_j/e_j)/s → 0.26` (constant) ⟹ `h_j ≈ e_j·n^{0.26·K·ln2}`, a strictly larger leading
  exponent. So the bad-scalar count is pinned by `h_j`, not `e_j`.
- **The leading-order δ* is char-FREE-pinned** by the complete-homogeneous value; the **char-p
  anomaly** (non-monomial conspiracies realizable only at bad primes = the additive-energy anomaly)
  is **exponent-0** (does not change the leading order) but is the IRREDUCIBLE residual = BGK.
- **Good-prime existence (quantitative Linnik):** a prime where the r-sums are DISTINCT mod p exists,
  giving polynomially-many distinct λ; bad primes divide `Res(Φ_s, ΣXⁱ−ΣXʲ)` (≤ log₄ s per pair).
- **`GaussianEnergyBound` is validated empirically at the actual prize parameters** (faithful map
  line 160) — the energy route (the E_r ladder, now E_2..E_7 exact in-tree) IS the leading-order
  pin. The di Benedetto exponent beat (0.9583) lives on the char-p anomaly (exponent-0).

## C. THE PROOF ATTACK — what to actually prove (and the in-tree pieces)

The exact δ* lower bound (the FLOOR) decomposes:
1. **CHAR-FREE leading order [the bulk — most attackable]:** prove the complete-homogeneous count
   `h_j = C(s+r−1, r)` is the worst-direction bad-scalar count, and that `poly(n)·h_j` crosses
   `ε*·|F|` at the conjectured δ*. The complete-homogeneous = `dividedDifferencePow_eq_schurH`
   (in-tree `SchurLagrangeBridge`); the count is `C(s+r−1,r)`. PROVABLE: the worst direction is
   monomial (in-tree `_CoreA5.monomial_dir_maximizes_overdet`), the forced-γ count per (k+1)-subset
   is `h_{a−k}(R)`, and the distinct count is `≤ C(s+r−1,r)` (multiset count). The poly/super-poly
   crossing of `C(s+r−1,r)` vs `ε*·|F|` gives the leading δ*. **This is the main landable target.**
2. **GOOD-PRIME existence [Linnik]:** prove a good prime exists where r-sums are distinct mod p,
   bounding the bad-prime set by `Res(Φ_s,·)` divisor count `≤ log₄ s` per pair (in-tree
   `E2W4CyclotomicNonCollision`, `KKH26CharZeroCollisionLaw`). REDUCES to quantitative Linnik /
   effective Chebotarev (the `Spur_r(p)` count — see `_AvW2`).
3. **CHAR-p ANOMALY [exponent-0, the irreducible BGK residual]:** the additive-energy bound
   `E_r(μ_n) ≤ (2r−1)‼·n^r` transferred to char-p at `r≈log q`. char-0 PROVEN (Lam–Leung; the E_r
   ladder E_2..E_7 exact in-tree); char-p excess `W_r=0` for `p > onset-threshold(r)` (VERIFIED for
   r≤4 at prize scale; the deep-r onset is the wall). This is exponent-0 so does NOT move the leading
   δ*, but is needed for the EXACT constant.

**So the exact δ* lower bound = char-free complete-homogeneous crossing (provable bulk) + Linnik
good-prime (reduces to effective PNT) + char-p anomaly exponent-0 (the deep-r energy transfer,
the genuine open residual).** The leading order is char-free and ATTACKABLE; the wall is only the
sub-leading exact-constant correction.

## D2. PROGRESS — explicit δ* LOWER BOUND LANDED (modulo 3 named residuals) [2026-06-16]

Floor proof on the CORRECT object, axiom-clean on fork/main:
- **F3 `prize_reduces_to_SumsetExtremality`** — corrected master reduction (window interior from ONE
  open hyp `SumsetExtremality`, not the false `|Σ_r|≤budget`); fires at verified δ*(μ_16)=9/16.
- **F6 `explicit_deltaStar_lower_bound`** — `δ* ≥ 1 − ρ − M_cross/n` (M_cross = complete-homogeneous
  crossing fold), from THREE named residuals; char-free pieces discharged; non-vacuity at 9/16.
- **F4 `badPrimeSet_card_le`** — Linnik good-prime residual (combinatorial half).

REMAINING residuals (the genuine open content): **F1 char-free Sumset-Extremality
`#bad ≤ poly·C(s+r−1,r)`** (the BULK = the prize's char-free core), good-prime Linnik (analytic
half), and **F5 char-p anomaly exponent-0** (deep-r W_r=0; onset grows faster than n⁴). The explicit
lower bound is PROVEN modulo these; pinning the EXACT bound = discharging F1 + the two analytic
residuals.

## D3. F1 LANDED — single open core isolated [2026-06-16, the honest frontier]

The floor proof is now FULLY SCAFFOLDED, axiom-clean, on the CORRECT object:
- **F1 `_BchksF1`** — the char-free floor QUANTITATIVELY encoded: multiplier `chooseCH s r =
  C(s+r−1,r)` (the SPECIFIC complete-homogeneous count, fixing the placeholder), `subsetSum_le_chooseCH`
  (`C(s,r) ≤ chooseCH` = Kambiré-not-tight), `bad_le_chooseCH_of_spectrum` (floor `bad ≤ chooseCH`
  REDUCED to the spectrum bound).
- **F3** reduction skeleton · **F4** Linnik (combinatorial half) · **F5** anomaly exp-0 (Wick-sandwich)
  · **F6** explicit lower bound `δ* ≥ 1−ρ−M_cross/n`.

**THE SINGLE GENUINE OPEN INPUT (the prize's char-free core):**
> `CompleteHomogeneousSpectrumBound`: `#{distinct h_r(R) : R ∈ binom(μ_s, k+1)} ≤ C(s+r−1, r)`
> — the distinct complete-homogeneous spectrum count of the subgroup is bounded by the
> complete-homogeneous dimension, at the binding fold `r = M_cross`.

Everything else in the floor proof is discharged (char-free arithmetic) or reduced to a precisely
named analytic residual (Linnik good-prime, deep-r Wick sandwich `E_r(F_p)≤Wick_r`). **Pinning the
EXACT δ* lower bound = proving this ONE combinatorial spectrum bound + the two analytic residuals.**
The spectrum bound is the genuine open prize core (the char-free worst-direction count); it is NOT
the in-tree BGK analytic wall but the p-independent complete-homogeneous distinct-value count — a
concrete, attackable combinatorial conjecture.

## D. ACTIONS
1. Mark the in-tree `BCHKS1_12` Prop as MIS-STATED (subset-sum on the wrong side); the real floor is
   Sumset-Extremality `#bad ≤ poly·|H^{(+r)}|`. The `prize_reduces_to_BCHKS` reduction is vacuous on
   the false `|Σ_r|≤budget` hypothesis — re-target it to the sumset-extremality / complete-homogeneous
   floor.
2. Attack (1) — the char-free complete-homogeneous leading-order floor — as the main landable target.
3. Attack (2) good-prime Linnik and (3) the char-p exponent-0 anomaly as the residuals.
