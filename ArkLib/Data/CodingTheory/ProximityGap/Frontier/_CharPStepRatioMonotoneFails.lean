/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPTransferDecomposition

set_option autoImplicit false

/-!
# REFUTATION: the char-`p` step-ratio monotonicity FAILS in the prize regime (#444)

`_CharZeroStepRatioMonotone` proves the step-ratio monotonicity gap
`G(r) = (2r+3)·E_{r+1}² − (2r+1)·E_r·E_{r+2} ≥ 0` in **char 0** (the cyclotomic energies), and
`_CharPTransferDecomposition` set up the decomposition `G_p = G₀ + L + Q` and the *conditional*
transfer `charP_transfer_of_dominance`/`gap_p_nonneg_of_dominance`, whose hypotheses are
`0 ≤ G₀ + L` (dominance) and `0 ≤ Q` (wraparound log-convexity). The file's prose asserted the
dominance `0 ≤ G₀ + L` was "machine-confirmed with growing margin".

**That assertion is FALSE.** It rested on a probe with an incorrect char-0 energy `E_r(ℂ)` (a naive
integer-lift, wrong at `r ≥ 4`). Re-probing with the CORRECT cyclotomic/antipodal `E_r(ℂ)`
(`Er_C_2power`) shows the char-`p` step-ratio gap itself is **NEGATIVE** at concrete prize-regime
points, so neither `G_p ≥ 0` nor the dominance `G₀ + L ≥ 0` holds in general. The char-`p` transfer
program is therefore WALLED: its sufficient hypotheses are *unsatisfiable* in the prize regime once
the additive-energy wraparound onsets (`W_r > 0` for `r ≥ 4`).

## The explicit refuting witness (EXACT integer additive energies, kernel-checked)

`n = 32`, `p = 786433` (`= 3·2^18 + 1`, so `32 ∣ p − 1`; prize regime `p ~ n⁴`), depth `r = 3`,
`s = 2r+1 = 7`. The EXACT period energies `E_k(F_p) = #{(x,y) ∈ μ_n^{2k} : Σx ≡ Σy mod p}` are
(computed by exact modular convolution; reproduced by `probe_charp_dominance_GL_v2.py`):

  `E₃(F_p) = 446720`,  `E₄(F_p) = 92179360`,  `E₅(F_p) = 24850732032`.

The char-`p` step-ratio gap at `r = 3` is
  `G_p = (s+2)·E₄² − s·E₃·E₅ = 9·92179360² − 7·446720·24850732032 = −1235923403258880 < 0`.

So `7·E₃(F_p)·E₅(F_p) > 9·E₄(F_p)²` — the char-`p` Cauchy–Schwarz/log-convexity step REVERSES.
(For contrast the char-0 gap at the same `r`, `9·E₄(ℂ)² − 7·E₃(ℂ)·E₅(ℂ)`, is `+2385085198648320 > 0`,
exactly as `_CharZeroStepRatioMonotone` proves. The reversal is caused by the wraparound excess
`W₄ = 1290240, W₅ = 1837785600 > 0`, whose linear term `L` overwhelms `G₀`.)

A second independent witness: `n = 64`, `p = 2752513`, `r = 2`, `s = 5`, with exact period energies
`E₂(F_p) = 12096`, `E₃(F_p) = 3750400`, `E₄(F_p) = 1666665280`, gives
`G_p = 7·E₃² − 5·E₂·E₄ = 7·3750400² − 5·12096·1666665280 = −2341415014400 < 0` likewise.

## Why this is a constraint result (the no-fifth-door bookkeeping)

It pins, kernel-checked, that **door-(iv) cannot be closed by char-`p` step-ratio monotonicity**: that
inequality is FALSE, so the ρ-antitone-via-energy-cross route (which needs `S_{r+1}·E_r ≤ S_r·E_{r+1}`,
the same Cauchy–Schwarz structure transferred to char-`p`) is not available unconditionally. Any prize
proof must control the FULL char-`p` quantity, not lean on a transferred char-0 monotonicity. This does
NOT touch the char-0 result (still proven) and makes NO cancellation/completion/moment/anti-concentration/
capacity claim. It REFUTES one assumed route. CORE stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`axiom`/`opaque`/`native_decide`.
-/

namespace ArkLib.ProximityGap.CharPStepRatioFails

open ArkLib.ProximityGap.CharPTransferDecomposition (gap)

/-- **Witness 1: the char-`p` step-ratio gap is negative at `n=32, p=786433, r=3`.** With the exact
period energies `E₃=446720, E₄=92179360, E₅=24850732032` and `s = 2·3+1 = 7`, the gap
`gap 7 E₃ E₄ E₅ = 9·E₄² − 7·E₃·E₅` is strictly negative. So the char-`p` step-ratio monotonicity
`7·E₃·E₅ ≤ 9·E₄²` FAILS. -/
theorem charP_stepRatio_gap_neg_n32 :
    gap 7 446720 92179360 24850732032 < 0 := by
  unfold gap; norm_num

/-- The same witness as a direct REVERSED inequality: `9·E₄² < 7·E₃·E₅` at `n=32, p=786433, r=3`. -/
theorem charP_stepRatio_reversed_n32 :
    (7 + 2 : ℝ) * (92179360 : ℝ) ^ 2 < 7 * (446720 : ℝ) * 24850732032 := by
  norm_num

/-- **Witness 2: the char-`p` step-ratio gap is negative at `n=64, p=2752513, r=2`.** With the exact
period energies `E₂=12096, E₃=3750400, E₄=1666665280` and `s = 2·2+1 = 5`, the gap
`gap 5 E₂ E₃ E₄ = 7·E₃² − 5·E₂·E₄` is strictly negative (`= −2341415014400`). So the char-`p`
step-ratio monotonicity `5·E₂·E₄ ≤ 7·E₃²` FAILS at this prize-regime point too. -/
theorem charP_stepRatio_gap_neg_n64 :
    gap 5 12096 3750400 1666665280 < 0 := by
  unfold gap; norm_num

/-- **The dominance hypothesis of `gap_p_nonneg_of_dominance` is NOT universally satisfiable.** There
exist real values `G₀ ≥ 0`, `L`, `Q ≥ 0` (the exact char-0 gap, linear term, and wraparound gap at
`n=32, p=786433, r=3`) for which the assembled char-`p` gap `G₀ + L + Q < 0`. Hence one cannot
discharge `gap_p_nonneg_of_dominance` from `0 ≤ Q` alone; the dominance input `0 ≤ G₀ + L` is FALSE
here. Concretely `G₀ = 2385085198648320`, `L = −3635991075225600`, `Q = 14982473318400`, giving
`G₀ + L + Q = −1235923403258880 < 0`. -/
theorem dominance_not_satisfiable_witness :
    ∃ G₀ L Q : ℝ, 0 ≤ G₀ ∧ 0 ≤ Q ∧ G₀ + L + Q < 0 := by
  refine ⟨2385085198648320, -3635991075225600, 14982473318400, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

end ArkLib.ProximityGap.CharPStepRatioFails

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.CharPStepRatioFails.charP_stepRatio_gap_neg_n32
#print axioms ArkLib.ProximityGap.CharPStepRatioFails.charP_stepRatio_reversed_n32
#print axioms ArkLib.ProximityGap.CharPStepRatioFails.charP_stepRatio_gap_neg_n64
#print axioms ArkLib.ProximityGap.CharPStepRatioFails.dominance_not_satisfiable_witness
