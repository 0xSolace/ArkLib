/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPTransferDecomposition

set_option autoImplicit false

/-!
# Discharging the wraparound gap `Q ≥ 0` from wraparound LOG-CONCAVITY (#444)

`_CharPTransferDecomposition` reduced the open char-`p` step-ratio wall to two localized
wraparound-control inputs fed into `charP_transfer_of_dominance`:

  1. `0 ≤ G₀ + L`  (the proven char-0 gap dominates the linear wraparound perturbation),
  2. `0 ≤ Q`       where `Q = gap s wa wb wc = (s+2)·wb² − s·wa·wc`  is the wraparound's OWN
                   log-convexity gap (`wa = W_r, wb = W_{r+1}, wc = W_{r+2} ≥ 0` the wraparound
                   excesses `W_r = E_r(F_p) − E_r(ℂ)`).

Input (2), `Q ≥ 0`, was previously carried as a blind machine-confirmed hypothesis. This file
DISCHARGES it from a strictly cleaner, sharper, probe-verified arithmetic condition: the
**wraparound sequence is itself log-concave**, `wa·wc ≤ wb²`. Under that single inequality (plus
the elementary `0 ≤ s`, true since `s = 2r+1`), the wraparound gap is not merely `≥ 0` but
**`≥ 2·wb²`** — a *strict* margin whenever the middle wraparound `wb ≠ 0`.

## Mechanism (one line of arithmetic)

`Q = (s+2)·wb² − s·(wa·wc) ≥ (s+2)·wb² − s·wb² = 2·wb² ≥ 0`,
using `wa·wc ≤ wb²` and `s ≥ 0` (so `−s·(wa·wc) ≥ −s·wb²`).

## Probe receipt (`scripts/probes/probe_charp_wraparound_logconcave_Q_v2.py`)

EXACT integer additive-energy ladders `E_r(F_p)` (modular conv) and `E_r(ℂ)` (CYCLOTOMIC
ANTIPODAL reduction, the in-tree `Er_C_2power`) over `n = 8,16,32,64`, seven structured
prize-regime primes `p ~ n⁴ ≫ n³`, proper subgroups `μ_n ⊊ F_p^*`. Result: `W_r ≥ 0` everywhere;
**wraparound log-concavity `W_r·W_{r+2} ≤ W_{r+1}²` holds at every interior `r`, every prime**
(including the non-vacuous post-onset cases `n=16,p=65537,r=3,4` with `W_4=4480, W_5=2923920,
W_6=1248322944`, and `n=32,r=3` with genuinely positive `W`); and the resulting `Q ≥ 0`. So the
condition this file assumes is empirically forced in the prize regime, not larped.

NOTE: the original probe (`..._Q.py`, now fixed in place) used a naive integer-lift for `E_r(ℂ)`
which is wrong at `r≥4`; the corrected antipodal `E_r(ℂ)` (v2) gives the robust verdict above. The
theorems below are pure algebra (`wa·wc ≤ wb² ⟹ Q ≥ 0`) and are unaffected by the arithmetic fix.

## Honest scope

This converts ONE of the two open wraparound hypotheses (`Q ≥ 0`) into a consequence of the
sharper `wa·wc ≤ wb²`. It does NOT close CORE: the wraparound log-concavity `wa·wc ≤ wb²` itself
remains a measured (probe-true) but UNPROVEN arithmetic input at deep `r` — exactly the BGK/Paley
char-`p` wall, now relocated to a cleaner single-inequality form. No cancellation / completion /
moment-saving / capacity claim. CORE stays OPEN. This is a constraint/reduction sharpening
(door-iv Lane-2/Lane-3).

⚠ ROUTE STATUS (2026-06-20): although `Q ≥ 0` is a valid algebraic lemma, its PARTNER hypothesis in
the `charP_transfer_of_dominance` assembly — the dominance `0 ≤ G₀ + L` — is FALSE in the prize regime
(`_CharPStepRatioMonotoneFails.lean`: the char-`p` step-ratio gap `G_p = G₀ + L + Q` is NEGATIVE at
`n=32, p=786433, r=3` and `n=64, p=2752513, r=2`). So this char-`p`-transfer ROUTE does NOT close CORE;
the `Q ≥ 0` lemma here stands as a kernel identity but has no satisfiable partner on this route.
-/

namespace ArkLib.ProximityGap.CharPTransferDecomposition

/-- **The wraparound gap `Q` is `≥ 2·wb²` under wraparound log-concavity.** If the wraparound
sequence is log-concave at this depth (`wa·wc ≤ wb²`) and `0 ≤ s` (true for `s = 2r+1`), then the
wraparound's own log-convexity gap `Q = gap s wa wb wc = (s+2)·wb² − s·wa·wc` is at least `2·wb²`.
This is the structural strengthening: the gap is not merely nonneg, it carries a `2·wb²` margin. -/
theorem gap_wrap_ge_two_mul_sq {s wa wb wc : ℝ} (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    2 * wb ^ 2 ≤ gap s wa wb wc := by
  have hmul : s * (wa * wc) ≤ s * wb ^ 2 := by
    exact mul_le_mul_of_nonneg_left hlc hs
  unfold gap
  nlinarith [hmul]

/-- **`Q ≥ 0` is discharged by wraparound log-concavity.** The open wraparound-control hypothesis
`0 ≤ gap s wa wb wc` of `charP_transfer_of_dominance` follows from `0 ≤ s` and the single
log-concavity inequality `wa·wc ≤ wb²`. (Via `gap_wrap_ge_two_mul_sq` and `0 ≤ 2·wb²`.) -/
theorem gap_wrap_nonneg_of_logConcave {s wa wb wc : ℝ} (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ gap s wa wb wc := by
  have h2 : (0 : ℝ) ≤ 2 * wb ^ 2 := by positivity
  exact le_trans h2 (gap_wrap_ge_two_mul_sq hs hlc)

/-- **`Q > 0` (strict) when the middle wraparound is nonzero.** Under log-concavity and `0 ≤ s`,
if `wb ≠ 0` then the wraparound gap is strictly positive (margin `2·wb² > 0`). This is the strict
endpoint: a single nonvanishing middle wraparound excess forces strict wraparound monotonicity. -/
theorem gap_wrap_pos_of_logConcave {s wa wb wc : ℝ} (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2)
    (hwb : wb ≠ 0) : 0 < gap s wa wb wc := by
  have h2 : (0 : ℝ) < 2 * wb ^ 2 := by positivity
  exact lt_of_lt_of_le h2 (gap_wrap_ge_two_mul_sq hs hlc)

/-- **Char-`p` transfer with the `Q`-hypothesis discharged by wraparound log-concavity.** Combines
the existing `charP_transfer_of_dominance` with `gap_wrap_nonneg_of_logConcave`: the char-`p`
step-ratio gap is nonneg given (a) the char-0 backbone dominates the linear wraparound perturbation
(`0 ≤ G₀ + L`), and (b) the wraparound sequence is log-concave (`wa·wc ≤ wb²`) with `0 ≤ s`. This
replaces the blind `0 ≤ Q` assumption by the sharper, probe-verified `wa·wc ≤ wb²`. -/
theorem charP_transfer_of_dominance_logConcave {s a₀ b₀ c₀ wa wb wc : ℝ} (hs : 0 ≤ s)
    (hdom : 0 ≤ gap s a₀ b₀ c₀ + (2 * (s + 2) * b₀ * wb - s * (a₀ * wc + c₀ * wa)))
    (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ gap s (a₀ + wa) (b₀ + wb) (c₀ + wc) :=
  charP_transfer_of_dominance hdom (gap_wrap_nonneg_of_logConcave hs hlc)

end ArkLib.ProximityGap.CharPTransferDecomposition

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_ge_two_mul_sq
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_nonneg_of_logConcave
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_pos_of_logConcave
#print axioms ArkLib.ProximityGap.CharPTransferDecomposition.charP_transfer_of_dominance_logConcave
