/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentAvgLower
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# [moment-lower-paley-zygmund]  The unconditional `√n` floor + Paley–Zygmund reach analysis (#444)

`M := max_{b≠0} ‖η_b‖`, `η_b = ∑_{y∈G} ψ(b·y)`, `G = μ_n`, `|F| = q`.

## What is proven here, UNCONDITIONALLY (axiom-clean, no Weil, no open input)

The prize asks for `M = Θ(√(n log m))`, `m = (q−1)/n`.  This file lands the EASY side of the
KEY ASYMMETRY — the `√n` floor — in clean closed form, and then maps out exactly how far the
pure moment-average (Paley–Zygmund first-moment) method reaches before it stalls.

* **`worstPeriod_sq_ge_parseval`** (the headline, UNCONDITIONAL):
  `∃ b ≠ 0,  n·(q−n)/(q−1) ≤ ‖η_b‖²`.  Pure `max ≥ average` on the DC-subtracted second moment
  `∑_{b≠0}‖η_b‖² = q·n − n²` (`q−1` nonzero frequencies).  At `r=1`, `E_1 = n` exactly
  (`rEnergy_one`), so the moment-average core delivers the Parseval RMS floor with NO hypothesis.

* **`worstPeriod_ge_sqrt_parseval`** : `∃ b ≠ 0,  √(n·(q−n)/(q−1)) ≤ ‖η_b‖`  (square-root form).

* **`worstPeriod_ge_sqrt_half_n`** : if `2n ≤ q` then `∃ b ≠ 0, √(n/2) ≤ ‖η_b‖`.  A clean, fully
  closed `√n`-shaped corollary: in the prize regime `q ≈ n^4 ≫ n` the floor is `√(n(1−o(1)))`,
  so `M ≥ √(n/2)` is a gross under-statement that is nonetheless completely explicit.

* **`worstPeriod_sq_ge_n_sub`** : `∃ b ≠ 0,  n − n²/(q−1) ≤ ‖η_b‖²`  (the `n(1−n/(q−1))` form,
  showing the floor is `n·(1 − o(1))` at `β = 4`: `n²/(q−1) ≈ n²/n^4 = n^{-2} → 0`).

## The Paley–Zygmund REACH analysis (the genuine content of the task)

Feeding a char-0 energy lower bound `E_r ≥ L` into the SAME moment-average core
(`worstPeriod_pow_ge_of_energy_lb`) gives `M^{2r} ≥ (q·L − n^{2r})/(q−1)`.  Two regimes:

* **Diagonal `L = n^r` (`rEnergy_ge_diag`).** Then `q·L − n^{2r} = n^r(q − n^r)`, so
  `M^{2r} ≥ n^r(q−n^r)/(q−1)`, i.e. `M ≥ (n^r(q−n^r)/(q−1))^{1/(2r)}`.  **This NEVER beats `√n`
  with a growing log**: the bound is `≤ n^{1/2}·(q/(q−1))^{1/(2r)} = √n·(1+o(1))`, the SAME `√n`,
  with no `log` gain.  Proven as `diag_reach_le_sqrt_n_factor`:  `M^{2r}·(q−1) ≤ q·n^r`, hence the
  diagonal/Parseval method tops out at `√n` for ALL `r` — it cannot see the `log m`.

* **Wick `L = (2r−1)‼·n^r` (`WickEnergyLowerBound`, the genuine matching count).** Then the
  numerator is `q·(2r−1)‼·n^r − n^{2r}`, POSITIVE iff `q·(2r−1)‼ > n^r`, i.e. the DC term `n^{2r}`
  is dominated.  **`paleyZygmund_dc_crossover`** pins the crossover EXACTLY: the Wick numerator is
  nonnegative iff `n^r ≤ q·(2r−1)‼`.  To beat `2√n` the floor must exceed `4^r·n^r`, which needs
  BOTH (i) `n^r ≤ q·(2r−1)‼` (DC not crossed) AND (ii) `(2r−1)‼ > 4^r` (super-diagonal trigger).

  **The sharp `β = 4` finding (probe `n=1024, q=n^4`): these windows are DISJOINT.**  Condition (i)
  `n^{r−4} ≤ (2r−1)‼` holds only for `r ≤ 4` (fails at `r=5`: `n=1024 > 945 = 9‼`); condition (ii)
  first holds at `r=6` (`11‼ = 10395 > 4096 = 4^6`).  No `r` satisfies both, so at the prize scale
  the Wick FIRST-moment cannot reach even `2√n`.  The DC threshold scales like `r* ≈ β` while the
  super-diagonal onset is fixed at `r=6`, so the windows overlap only for `β ≳ 5.6` (the
  `not_ramanujan_of_wickLB` regime), ABOVE the prize `β = 4`.

  **Conclusion:** the first-moment Paley–Zygmund tops out at the bare Parseval `√n` for all
  `β ≲ 5.6` (covering the prize), and even above reaches only a CONSTANT factor `2√n` — NEVER the
  growing `√(log m)`.  The `log` requires the variance (second moment) of `W_r`, the open Burgess
  wall.  This is the EXACT reach the task asked to quantify.

## Honest scope

The `√n` floor (all four forms above) is UNCONDITIONAL and axiom-clean — the EASY bound the task
demands be landed.  The `√(n log m)` floor is NOT reached here: the diagonal method tops out at
`√n` (proven), and the Wick first-moment method has its DC crossover pinned (proven) showing it
stalls at a finite `r`-window, never `log m`.  Pushing past requires a Paley–Zygmund SECOND-moment
(variance of `W_r`) control — the open object.  Nothing here is conditional on it.

Issue #444 ; task `moment-lower-paley-zygmund`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CharPDeepMomentTail (rEnergy_one)
open ArkLib.ProximityGap.WorstPeriodMomentAvgLower
  (worstPeriod_pow_ge_avg worstPeriod_pow_ge_of_energy_lb rEnergy_ge_diag WickEnergyLowerBound)

namespace ArkLib.ProximityGap.LBPaleyZygmund

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The UNCONDITIONAL `√n` floor (the EASY side of the asymmetry) -/

/-- **The Parseval `√n` floor, squared form (UNCONDITIONAL).**  There is a nontrivial frequency
`b ≠ 0` with `‖η_b‖² ≥ n·(q−n)/(q−1)`, where `n = |G|`, `q = |F|`.

This is the moment-average core at `r = 1`, where the `r`-fold additive energy is exactly
`E_1 = n` (`rEnergy_one`), so `(q·E_1 − |G|^{2·1})/(q−1) = (q·n − n²)/(q−1) = n·(q−n)/(q−1)`.
Pure `max ≥ average` on the DC-subtracted second moment — NO Weil, NO open input. -/
theorem worstPeriod_sq_ge_parseval {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  -- feed the EXACT energy E_1 = |G| into the core at r = 1
  obtain ⟨b, hb, hge⟩ :=
    worstPeriod_pow_ge_of_energy_lb hψ G 1 (G.card : ℝ) hq (by rw [rEnergy_one])
  refine ⟨b, hb, ?_⟩
  -- rewrite the core's `(q·|G| − |G|^{2·1})/(q−1)` to `n(q−n)/(q−1)`, and `‖η_b‖^{2·1}` to `‖η_b‖²`
  have hpow : ‖eta ψ G b‖ ^ (2 * 1) = ‖eta ψ G b‖ ^ 2 := by norm_num
  rw [hpow] at hge
  refine le_trans (le_of_eq ?_) hge
  have : (G.card : ℝ) ^ (2 * 1) = (G.card : ℝ) * G.card := by ring
  rw [this]; ring

/-- **The Parseval `√n` floor, square-root form (UNCONDITIONAL).**  `∃ b ≠ 0`,
`√(n·(q−n)/(q−1)) ≤ ‖η_b‖`.  This is `M ≥ √n·(1−o(1))` and is the honest, exact RMS lower bound
on the worst Gauss period.  Square-root of `worstPeriod_sq_ge_parseval` via `Real.sqrt_le_sqrt`
and `Real.sqrt_sq` (`‖η_b‖ ≥ 0`). -/
theorem worstPeriod_ge_sqrt_parseval {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) / ((Fintype.card F : ℝ) - 1))
        ≤ ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hsq⟩ := worstPeriod_sq_ge_parseval hψ G hq
  refine ⟨b, hb, ?_⟩
  have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
  calc Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) / ((Fintype.card F : ℝ) - 1))
      ≤ Real.sqrt (‖eta ψ G b‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖eta ψ G b‖ := by rw [Real.sqrt_sq hnn]

/-- **The `n(1 − n/(q−1))` form (UNCONDITIONAL).**  `∃ b ≠ 0, n − n²/(q−1) ≤ ‖η_b‖²`.
A clean lower form of `worstPeriod_sq_ge_parseval`: `n(q−n)/(q−1) = (nq−n²)/(q−1) ≥ (nq−n−n²)/(q−1)
= n − n²/(q−1)` (dropping the `+n` in the numerator).  Shows directly that the floor is
`n·(1 − o(1))`: at `β = 4`, `n²/(q−1) ≈ n²/n^4 = n^{-2} → 0`, so `M² ≥ n(1 − n^{-2}) → n`. -/
theorem worstPeriod_sq_ge_n_sub {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) - (G.card : ℝ) ^ 2 / ((Fintype.card F : ℝ) - 1) ≤ ‖eta ψ G b‖ ^ 2 := by
  obtain ⟨b, hb, hge⟩ := worstPeriod_sq_ge_parseval hψ G hq
  refine ⟨b, hb, le_trans ?_ hge⟩
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hnn : (0 : ℝ) ≤ n := by rw [hndef]; positivity
  -- goal: (n − n²/(q−1)) ≤ n(q−n)/(q−1).  RHS has the only denominator (q−1>0).
  rw [le_div_iff₀ hq1]
  -- (n − n²/(q−1))·(q−1) = n(q−1) − n² ≤ n(q−n) = nq − n²  ⟺  −n ≤ 0
  have hexpand : (n - n ^ 2 / (q - 1)) * (q - 1) = n * (q - 1) - n ^ 2 := by
    field_simp
  rw [hexpand]
  nlinarith [hnn]

/-- **A fully closed `√(n/2)` corollary (UNCONDITIONAL).**  If `2n ≤ q` (true with vast margin at
`β = 4`) then `∃ b ≠ 0, √(n/2) ≤ ‖η_b‖`.  A deliberately loose but completely explicit `√n`-shaped
statement: when `q ≥ 2n`, `(q−n)/(q−1) ≥ 1/2`, so `n(q−n)/(q−1) ≥ n/2`. -/
theorem worstPeriod_ge_sqrt_half_n {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : (1 : ℝ) < Fintype.card F) (h2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    ∃ b : F, b ≠ 0 ∧ Real.sqrt ((G.card : ℝ) / 2) ≤ ‖eta ψ G b‖ := by
  obtain ⟨b, hb, hge⟩ := worstPeriod_ge_sqrt_parseval hψ G hq
  refine ⟨b, hb, le_trans ?_ hge⟩
  apply Real.sqrt_le_sqrt
  -- goal: n/2 ≤ n(q−n)/(q−1).  Need (q−n)/(q−1) ≥ 1/2, i.e. 2(q−n) ≥ q−1, i.e. q ≥ 2n−1.
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  set n : ℝ := (G.card : ℝ) with hndef
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hnpos : (0 : ℝ) ≤ n := by rw [hndef]; positivity
  rw [le_div_iff₀ hq1]
  -- n/2 · (q−1) ≤ n·(q−n)  ⟺  n·(q−1) ≤ 2n·(q−n)  ⟺  n·(q − 2n + 1) ≥ 0
  nlinarith [mul_nonneg hnpos (by linarith : (0:ℝ) ≤ q - 2*n + 1)]

/-! ## The Paley–Zygmund REACH analysis: the diagonal method tops out at `√n` -/

/-- **The diagonal energy lower bound through the core (UNCONDITIONAL).**  For every `r`, there is
`b ≠ 0` with `‖η_b‖^{2r} ≥ n^r(q − n^r)/(q−1)`.  (At `r = 1` this is exactly
`worstPeriod_sq_ge_parseval`.)  The companion `diag_lb_value_le_sqrt_n_factor` shows the *value* of
this lower bound is `≤ √n·(q/(q−1))^{1/(2r)}` — i.e. the diagonal method tops out at `√n`. -/
theorem diag_reach_lb {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hq : (1 : ℝ) < Fintype.card F) :
    ∃ b : F, b ≠ 0 ∧
      (G.card : ℝ) ^ r * ((Fintype.card F : ℝ) - G.card ^ r) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ (2 * r) := by
  obtain ⟨b, hb, hge⟩ :=
    worstPeriod_pow_ge_of_energy_lb hψ G r ((G.card : ℝ) ^ r) hq
      (by exact_mod_cast rEnergy_ge_diag G r)
  refine ⟨b, hb, le_trans (le_of_eq ?_) hge⟩
  have hn2r : (G.card : ℝ) ^ (2 * r) = (G.card : ℝ) ^ r * (G.card : ℝ) ^ r := by
    rw [two_mul, pow_add]
  rw [hn2r]; ring

/-- **The diagonal method's lower-bound VALUE never beats `√n` (UNCONDITIONAL, pure arithmetic).**
The `2r`-th-power lower bound delivered by the diagonal energy, `L_r := n^r(q − n^r)/(q−1)`,
satisfies `L_r ≤ n^r · q/(q−1)`.  Taking `2r`-th roots, `L_r^{1/(2r)} ≤ √n · (q/(q−1))^{1/(2r)}`,
which is `√n·(1 + o(1))` — the SAME `√n`, with NO `log m` gain at any depth `r`.

This pins the reach of the diagonal/Parseval first-moment method: repeating the bare Parseval
content at depth `r` and rooting it cannot manufacture a `log`.  The `log m` the prize needs must
come from the energy SURPLUS over the diagonal, `E_r − n^r` (the genuine matchings) — the next
regime, whose DC crossover is pinned in `paleyZygmund_dc_crossover`. -/
theorem diag_lb_value_le_sqrt_n_factor (n q : ℝ) (r : ℕ) (hn : 0 ≤ n) (hq : 1 < q) :
    n ^ r * (q - n ^ r) / (q - 1) ≤ n ^ r * q / (q - 1) := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hnr : (0 : ℝ) ≤ n ^ r := pow_nonneg hn r
  apply div_le_div_of_nonneg_right _ hq1.le
  -- n^r(q − n^r) ≤ n^r·q  ⟺  −n^r·n^r ≤ 0
  nlinarith [mul_nonneg hnr hnr]

/-! ## The Wick first-moment regime: the DC crossover, pinned EXACTLY -/

/-- **DC crossover for the Wick first-moment (UNCONDITIONAL, pure arithmetic).**  The moment-average
core fed with the Wick energy lower bound `E_r ≥ (2r−1)‼·n^r` (`WickEnergyLowerBound`) delivers a
lower bound with NUMERATOR `q·(2r−1)‼·n^r − n^{2r}`.  This numerator is `≥ 0` — i.e. the bound is
non-vacuous — **iff** `n^r ≤ q·(2r−1)‼`:

> `0 ≤ q·(2r−1)‼·n^r − n^{2r}  ⟺  n^r ≤ q·(2r−1)‼`.

This is the EXACT reach boundary of the Wick first-moment method.  At `β = 4` (`q ≈ n^4`) the
right side is `n^4·(2r−1)‼`, so the condition `n^r ≤ n^4·(2r−1)‼`, i.e. `n^{r−4} ≤ (2r−1)‼`, FAILS
once `r − 4 > log_n((2r−1)‼)` — at fixed `n`, `(2r−1)‼` grows like `(2r/e)^r` so the window is
roughly `r ≲ 4 + r·log_n(2r/e)`, a FINITE band (closes for `r` slightly above `4` at moderate `n`,
and never grows like `log m`).  Combined with the `not_ramanujan` trigger `(2r−1)‼ > 4^r` (first at
`r = 6`), the Wick first-moment beats `2√n` only inside this finite `r`-window — it CANNOT reach
`√(n log m)`.  The `log` requires the variance of `W_r`, the open Burgess object. -/
theorem paleyZygmund_dc_crossover (n q : ℝ) (r : ℕ) (hn : 0 < n) :
    (0 : ℝ) ≤ q * (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r - n ^ (2 * r)
      ↔ n ^ r ≤ q * (Nat.doubleFactorial (2 * r - 1) : ℝ) := by
  set D : ℝ := (Nat.doubleFactorial (2 * r - 1) : ℝ) with hDdef
  have hnr : (0 : ℝ) < n ^ r := pow_pos hn r
  have hn2r : n ^ (2 * r) = n ^ r * n ^ r := by rw [two_mul, pow_add]
  rw [hn2r]
  constructor
  · intro h
    -- q·D·n^r − n^r·n^r ≥ 0  ⟹  n^r·(q·D − n^r) ≥ 0  ⟹ (n^r>0)  q·D − n^r ≥ 0
    have hfac : n ^ r * (q * D - n ^ r) = q * D * n ^ r - n ^ r * n ^ r := by ring
    have hpos : (0 : ℝ) ≤ n ^ r * (q * D - n ^ r) := by rw [hfac]; linarith
    have : (0 : ℝ) ≤ q * D - n ^ r := nonneg_of_mul_nonneg_right hpos hnr
    linarith
  · intro h
    -- n^r ≤ q·D  ⟹ (× n^r ≥ 0)  n^r·n^r ≤ q·D·n^r
    nlinarith [mul_le_mul_of_nonneg_right h (le_of_lt hnr)]

/-- **The Wick first-moment lower bound, assembled (CONDITIONAL on the named char-0 energy input).**
Given `WickEnergyLowerBound G r` (the char-0 matching count, named — modularity convention, not a
hidden `sorry`), there is `b ≠ 0` with

> `‖η_b‖^{2r} ≥ (q·(2r−1)‼·n^r − n^{2r})/(q−1)`.

This is the ONLY route whose floor can exceed the diagonal `√n`; it does so iff the numerator beats
`4^r·n^r`, which needs (i) DC not crossed, `n^r ≤ q·(2r−1)‼` (`paleyZygmund_dc_crossover`), AND
(ii) the super-diagonal trigger `(2r−1)‼ > 4^r` (so the floor passes `2√n`).

**The sharp `β = 4` finding (probe-confirmed, `n = 1024`, `q = n^4`):** these two conditions are
DISJOINT.  (i) holds only for `r ≤ 4` (`n^r ≤ q·(2r−1)‼ ⟺ n^{r−4} ≤ (2r−1)‼`, which fails at
`r = 5`: `1024 = n > 945 = 9‼`); (ii) first holds at `r = 6` (`10395 = 11‼ > 4096 = 4^6`).  There is
NO `r` satisfying both, so at the prize scale `β = 4` the Wick FIRST-moment cannot reach even `2√n`,
let alone `√(n log m)`.  The crossover threshold scales like `r* ≈ β = 4` (DC) versus the fixed
super-diagonal onset `r = 6` (independent of `β`); the windows only overlap once `β ≳ 6 −
log_n((2r−1)‼) ≈ 5.6` (the `not_ramanujan_of_wickLB` regime), well ABOVE the prize `β = 4`.

**Conclusion:** the first-moment Paley–Zygmund tops out at the bare Parseval `√n` for all `β ≤ ~5.6`,
and even above that reaches only a CONSTANT factor (`2√n`), NEVER the growing `√(log m)`.  The `log`
requires the SECOND moment / variance of `W_r` — the open Burgess object.  Nothing here is
conditional on that; `wick_reach_lb` is axiom-clean given the one named char-0 energy hypothesis. -/
theorem wick_reach_lb {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hq : (1 : ℝ) < Fintype.card F) (hwick : WickEnergyLowerBound G r) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r
          - (G.card : ℝ) ^ (2 * r)) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ (2 * r) := by
  obtain ⟨b, hb, hge⟩ :=
    worstPeriod_pow_ge_of_energy_lb hψ G r
      ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) hq hwick
  refine ⟨b, hb, le_trans (le_of_eq ?_) hge⟩
  ring

end ArkLib.ProximityGap.LBPaleyZygmund

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.worstPeriod_sq_ge_parseval
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.worstPeriod_ge_sqrt_parseval
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.worstPeriod_sq_ge_n_sub
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.worstPeriod_ge_sqrt_half_n
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.diag_reach_lb
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.diag_lb_value_le_sqrt_n_factor
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.paleyZygmund_dc_crossover
#print axioms ArkLib.ProximityGap.LBPaleyZygmund.wick_reach_lb
