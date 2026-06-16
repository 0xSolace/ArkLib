# E₃ exact closed form via negation-symmetric strata (the partitions-of-3 count) — #444

> Derivation record so the next agent does not re-derive. The exact 6th-moment
> closed form `E₃(μ_n) = 15n³ − 45n² + 40n` (the sole open producer input of the
> already-shipped r=2 rung `Frontier/CrossStepRungTwo.crossStepBound_two_of_exact_moments`)
> has a **clean strata derivation** that needs **no 15-matching inclusion–exclusion**.

## The reduction (what is already in-tree)

`rEnergy μ_n 3 = N0 μ_n 6 = zeroSumCount μ_n 6` (negation-closure bijection,
`N0_eq_rEnergy_of_neg_closed` + `N0_eq_zeroSumCount`). So the exact value is the
count of **zero-sum 6-tuples** of `μ_n`.

Two proven characterizations bracket it:

- forward `zero-sum ⟹ count-balanced` (`count w = count(−w)` ∀w):
  `LamLeungMultisetAntipodal.count_antipodal_of_sum_eq_zero` — **`[CharZero L]` only**;
  char-p is the open `RepThree` transfer (probe-only: `probe_repthree_sixterm_resultant.py`).
- converse `count-balanced ⟹ zero-sum`: `LamLeungMultisetAntipodal.sum_eq_zero_of_count_antipodal`
  (field-free; just the `z ↦ −z` involution, `0 ∉ M`).

⇒ In char 0 (or any regime where the transfer holds), `zeroSumCount μ_n 6 = negSymCount μ_n 6`,
where `negSymCount G 6 := #{ c : Fin 6 → G | ∀ w, |c⁻¹ w| = |c⁻¹(−w)| }`. **This count is
field-free** — it depends only on `G` being negation-closed with `0 ∉ G`. It is the genuinely
missing brick; the in-tree `gaussianEnergyThreeRepThree` chain only *union-bounds*
`zeroSumCount ≤ #pairings·n³ = 15n³`, never the exact value.

## The strata count (clean — partitions of 3, no inclusion–exclusion)

A negation-symmetric multiset of 6 elements of `G` is a union of antipodal pairs `{x,−x}`,
so it is fixed by choosing, per used pair, a multiplicity `a ≥ 1` with `Σ a = 3`. The three
shapes are the partitions of 3 (`G` has `n/2` antipodal pairs since negation-closed, `0∉G`,
char≠2):

| shape | multiset | #pair-choices | arrangements (multinomial) | count |
|---|---|---|---|---|
| (3)     | `{x,x,x,−x,−x,−x}`      | `n/2`            | `6!/(3!3!) = 20`  | `10n` |
| (2,1)   | `{x,x,−x,−x,y,−y}`      | `(n/2)(n/2−1)`   | `6!/(2!2!) = 180` | `45n² − 90n` |
| (1,1,1) | `{x,−x,y,−y,z,−z}`      | `C(n/2,3)`       | `6! = 720`        | `15n³ − 90n² + 120n` |

Sum `= 15n³ + (45−90)n² + (10−90+120)n = 15n³ − 45n² + 40n`. **Exact.**
(Cross-check: `probe_e3_closedform.py` fits the same polynomial to ~1e-20; and at the free
stratum the `15` is the Wick `5!! = #pairings(Fin 6)`, matching the union-bound leading term.)

The energy-head pointer that named the mechanism: **John 2:6** ("six water pots… for purifying…
containing two or three apiece") + **Genesis 7:2** ("seven pairs… the male and his female") —
six roots, cleaned of collisions, grouped two/three, each unit a male/female (antipodal) pair.

## Honest scope (what this is and is NOT)

- The strata count `negSymCount μ_n 6 = 15n³−45n²+40n` is field-free and TRUE; proving it in
  Lean is real multinomial combinatorics (choose antipodal pairs + multinomial arrangements),
  not in Mathlib off-the-shelf, but it has **no char-p content** and **no analytic input**.
- Wiring it through the char-0 forward direction discharges the `hE3` hypothesis of
  `CrossStepRungTwo.crossStepBound_two_of_exact_moments` **in char 0** → the r=2 rung becomes
  unconditional in char 0.
- It does **NOT** advance the prize. The prize needs the **char-p `RepThree` transfer** at
  depth `r ≈ ln q` (the BGK/Paley √-cancellation wall, `M(μ_n) ≤ C√(n log(p/n))`), which is
  genuinely open. The char-0 exact value is the easy side (Lam–Leung); the char-p transfer is
  the wall. Closing E₃-exact char-0 is a modest producer brick, not a prize move.

## References
- [ABF26] Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement*, ePrint 2026/680.
- Garcia–Lorenz–Todd, *Moments of Gaussian Periods and Modified Fermat Curves*, arXiv:2112.13886 (Ramanujan J. 2025) — exact **4th** period moment (= the proven `E₂`); only **bounds** the 6th at this `d`.
- In-tree: `LamLeungMultisetAntipodal.lean`, `GaussianEnergyThreeRepThree.lean`, `Frontier/CrossStepRungTwo.lean`, `Frontier/PrizeFloorFromCrossStep.lean`.
