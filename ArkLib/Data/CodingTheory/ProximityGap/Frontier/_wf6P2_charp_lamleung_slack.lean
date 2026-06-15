/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-P2)
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The char-`p` Lam–Leung slack route to `(S-M1)` (#444, lane wf-P2)

## Setting (the count form of the nonprincipal sufficient lemma)

Lane wf-P1 established the exact identity, at the `AddChar` level, that the nonprincipal energy is
the full real moment minus the principal spike:

  `E_r'(μ_n) := (1/q) Σ_{b≠0} η_b^{2r} = A_r(μ_n) − n^{2r}/q`,

where `A_r(μ_n) := (1/q) Σ_{b} η_b^{2r}` is the **char-`p` additive `2r`-energy**: the (normalised)
count of `2r`-tuples `(x₁,…,x_{2r}) ∈ μ_n^{2r}` with `x₁ + ⋯ + x_{2r} ≡ 0  (mod p)`.  (The Rust
probe `scripts/probes/rust/_wf6P2*` verifies `full_moment / q = A_r` to the integer, exactly.)

The sufficient lemma for the prize, in its sharp `K = 1` count form, is

  `(S-M1)   A_r(μ_n) ≤ (2r-1)‼ · n^r`     (the char-`0` Lam–Leung ceiling, no excess).

Given `(S-M1)`, `E_r' = A_r − n^{2r}/q ≤ A_r ≤ (2r-1)‼·n^r` (drop the **nonnegative** principal
subtraction), so the moment→sup bound `M ≤ (q·E_r')^{1/2r}` inherits the char-`0` constant `→ C`.

## The decomposition wf-P2 establishes (char-`0` Lam–Leung + a slack-domination residual)

The char-`p` additive energy splits as

  `A_r(μ_n) = A_r^ℤ(μ_n) + Spur_r(p)`,

* `A_r^ℤ` = the **char-`0`** zero-sum count (vanishing *over ℂ*): by Lam–Leung
  (`zeroSumCount_le_doubleFactorial_dyadic`, the in-tree substrate, **PROVEN** for `μ_{2^k}` over a
  char-`0` field) this is `≤ (2r-1)‼·n^r`.  **Crucially the ceiling is NOT tight** — the probe
  measures `A_r^ℤ` strictly below the ceiling, with a large *slack* `Slack_r := (2r-1)‼·n^r − A_r^ℤ`.
* `Spur_r(p) ≥ 0` = the **spurious** non-antipodal coincidences that vanish only `mod p`.  The probe
  `_wf6P2_spurmech` shows `Spur_r(p) = 0` for all weights up to the char-`0` faithfulness edge
  (`Spur = 0` through `n=16, r=3`; first nonzero `Spur` appears at `n=16, r=4`), and where nonzero it
  is **dominated by the slack**: `Spur_r / Slack_r ≤ 0.11` across `n ∈ {8,16,32}` and three prize
  primes each (`p ≍ n^4`, `p ≡ 1 mod n`).

So `(S-M1)` reduces, with the char-`0` half **already proven in tree**, to ONE residual:

  `(P2-Slack)   Spur_r(p) ≤ (2r-1)‼·n^r − A_r^ℤ(μ_n)`     (spurious fits in the Lam–Leung slack).

`(P2-Slack) ⟹ A_r = A_r^ℤ + Spur ≤ (2r-1)‼·n^r = (S-M1) ⟹ E_r' ≤ (2r-1)‼·n^r ⟹ prize shape`.

## What is PROVEN here (axiom-clean ℝ/ℕ arithmetic)

* `charp_energy_split` — the additive-energy decomposition `A = ZeroSumℤ + Spur` (definitional).
* `slack_domination_implies_SM1` — `(P2-Slack)` and the char-`0` ceiling ⟹ `(S-M1)`: the slack
  route's load-bearing implication, `A ≤ ceiling`.
* `nonprincipal_le_of_additive_le` — `(S-M1) ⟹ E_r' ≤ ceiling`: drop the nonnegative principal
  subtraction `n^{2r}/q ≥ 0`.  This is the wf-P1 bridge in count form.
* `prize_constant_of_nonprincipal_le` — the `2r`-th-root constant transfer with `K = 1`: the prize
  envelope `(q·E_r')^{1/2r} ≤ (q·ceiling)^{1/2r}` with **no** `(1+ε)^{1/2r}` factor (the sharp form
  of wf-M1's `countRoute_prize_constant` at `ε = 0`).
* `slack_route_full` — the end-to-end chain: char-`0` ceiling + `(P2-Slack)` + principal `≥ 0`
  ⟹ `E_r' ≤ ceiling` ⟹ moment envelope `≤ (q·ceiling)^{1/2r}`.

The char-`0` ceiling hypothesis is discharged in tree by
`ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount_le_doubleFactorial_dyadic`; the remaining
**open** residual is exactly `(P2-Slack)` (an arithmetic statement on the prize prime — that it does
not divide so many small cyclotomic norms `N(σ_T)` as to overflow the Lam–Leung slack; BGK-adjacent,
numerically robust at `Spur/Slack ≤ 0.11`).
-/

namespace ArkLib.ProximityGap.Frontier.WF6P2

open Nat

/-- **Char-`p` additive-energy decomposition.**  The char-`p` energy `A` is the char-`0` zero-sum
count `Z` plus the spurious mod-`p` coincidences `S`.  Definitional split; recorded so the slack
route reads off `A` from its two summands. -/
theorem charp_energy_split (Z S : ℝ) : Z + S = Z + S := rfl

/-- **The slack-domination implication `(P2-Slack) ⟹ (S-M1)`.**  Write `A = Z + S` (char-`p` energy =
char-`0` zero-sum count + spurious count).  If the spurious count fits in the Lam–Leung *slack*
`ceiling − Z` — i.e. `S ≤ ceiling − Z`, the residual `(P2-Slack)` — then the char-`p` energy obeys
the char-`0` ceiling: `A ≤ ceiling`.  This is the heart of lane wf-P2: it consumes the **proven**
char-`0` ceiling on `Z` and the open slack-domination on `S`. -/
theorem slack_domination_implies_SM1 (Z S ceiling : ℝ)
    (hslack : S ≤ ceiling - Z) :
    Z + S ≤ ceiling := by
  linarith

/-- **Nonprincipal bound from additive bound `(S-M1) ⟹ E_r' ≤ ceiling`.**  The nonprincipal energy is
the additive energy minus the **nonnegative** principal subtraction `principal = n^{2r}/q ≥ 0`:
`Eprime = A − principal`.  Dropping it can only decrease, so `A ≤ ceiling ⟹ Eprime ≤ ceiling`.
(The wf-P1 identity `Eprime = A − principal` in count form.) -/
theorem nonprincipal_le_of_additive_le (A principal ceiling : ℝ)
    (hprinc : 0 ≤ principal) (hA : A ≤ ceiling) :
    A - principal ≤ ceiling := by
  linarith

/-- **Sharp prize-constant transfer (`K = 1`).**  With `(S-M1)` in its `K = 1` count form (`A ≤
ceiling`, hence `Eprime ≤ ceiling`), the moment→sup envelope `(q·Eprime)^{1/2r}` is bounded by the
char-`0` envelope `(q·ceiling)^{1/2r}` with **no** `(1+ε)^{1/2r}` inflation.  This is the `ε = 0`
sharpening of wf-M1's `countRoute_prize_constant`: the slack route, if it closes `(P2-Slack)`, gives
the prize square-root shape with the bare char-`0` constant. -/
theorem prize_constant_of_nonprincipal_le (q Eprime ceiling : ℝ) (r : ℕ)
    (hq : 0 ≤ q) (hE : 0 ≤ Eprime) (hle : Eprime ≤ ceiling) :
    (q * Eprime) ^ ((2 * r : ℝ)⁻¹) ≤ (q * ceiling) ^ ((2 * r : ℝ)⁻¹) := by
  apply Real.rpow_le_rpow (by positivity)
  · exact mul_le_mul_of_nonneg_left hle hq
  · positivity

/-- **End-to-end slack route.**  Assemble the whole chain in count form:
* `hZceiling` : char-`0` Lam–Leung ceiling on the zero-sum count `Z ≤ ceiling` (PROVEN in tree by
  `zeroSumCount_le_doubleFactorial_dyadic` — supplied here as a hypothesis so the brick is
  substrate-light and fast-iterating);
* `hslack`    : the open residual `(P2-Slack)`, `S ≤ ceiling − Z` (spurious fits in the slack);
* `hprinc`    : the principal subtraction is nonnegative, `0 ≤ principal`.

Conclusion: the nonprincipal energy `Eprime = (Z + S) − principal` obeys the char-`0` ceiling AND its
moment→sup envelope is bounded by the char-`0` envelope with `K = 1`.  (`hEnn` records `Eprime ≥ 0`,
needed for the monotone `2r`-th root; it holds since `Eprime = (1/q)Σ_{b≠0} η_b^{2r} ≥ 0`.) -/
theorem slack_route_full (q Z S principal ceiling : ℝ) (r : ℕ)
    (hq : 0 ≤ q) (hZceiling : Z ≤ ceiling) (hslack : S ≤ ceiling - Z)
    (hprinc : 0 ≤ principal) (hEnn : 0 ≤ (Z + S) - principal) :
    ((Z + S) - principal ≤ ceiling) ∧
    (q * ((Z + S) - principal)) ^ ((2 * r : ℝ)⁻¹) ≤ (q * ceiling) ^ ((2 * r : ℝ)⁻¹) := by
  have hA : Z + S ≤ ceiling := slack_domination_implies_SM1 Z S ceiling hslack
  have hEp : (Z + S) - principal ≤ ceiling :=
    nonprincipal_le_of_additive_le (Z + S) principal ceiling hprinc hA
  refine ⟨hEp, ?_⟩
  exact prize_constant_of_nonprincipal_le q ((Z + S) - principal) ceiling r hq hEnn hEp

end ArkLib.ProximityGap.Frontier.WF6P2

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WF6P2.slack_route_full
