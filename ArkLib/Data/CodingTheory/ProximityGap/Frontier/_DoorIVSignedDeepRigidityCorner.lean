/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444, #464)
-/
import ArkLib.Data.CodingTheory.ProximityGap.SignedPeriodZeroSumBridge

set_option linter.style.longLine false

/-!
# Door-(iv) Lane 2/3 — the signed deep sum's RIGIDITY CORNER + sign↔count bridge, kernel-checked (#444, #464)

The thinness-discriminator search located the prize's surviving positive structural object in the
**ODD signed deep sum** `A_r := ∑_{ψ≠0} η_ψ^r` (`SignedPeriodZeroSumBridge`), with the exact identity

>   `A_r = q · zeroSumCount S r − |S|^r`.

The `DISPROOF_LOG` entry *"The odd signed deep sum A_r is SIGN-RIGID (negative) in the thin regime"*
(2026-06-21) measured, but stated only **in prose**, two facts that this file turns into kernel theorems:

1. **The rigidity corner.** Below the odd onset depth `d_odd` the zero-sum count vanishes
   (`zeroSumCount S r = 0`), and there `A_r = −|S|^r` *exactly* — the "sign-rigid `A_r = −n^r`
   floor" the entry reports. This is a one-step consequence of the formalized identity, but it was
   never an exported declaration; it grounds the empirical "sign-rigid below `d_odd`" claim.

2. **The sign ↔ count bridge.** The empirical fact "`A_r ≤ 0` throughout the thin regime" is, via the
   identity, *exactly* the count inequality `q · zeroSumCount S r ≤ |S|^r`. This file states the
   bridge at the level of the **integer count** (`q·Z` vs `n^r`), where it is field-universal and
   `|·|`-free — so the sign side of the wall is re-expressed as an honest orbit-count-style upper
   bound on the signed zero-sum count, the object the `OrbitCountWall` reduction is about.

## Honest scope

Lane-2/3 reduction/constraint backbone. These are EXACT structural facts on the located signed prize
object, sitting directly on the formalized `nonzeroSignedPeriodPow_eq_zeroSumCount` identity. They make
the `DISPROOF_LOG` sign-rigidity entry kernel-checked. They are **NOT** a CORE bound: bounding `A_r`
quantitatively at `r ≈ log q` (the deep signed cancellation `q·Z − n^r` being *small*, equivalently
the RATE at which `q·Z → n^r`) is the open BGK wall. No cancellation, completion, moment-saving,
anti-concentration, or capacity claim. `CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Issues #444, #464.
-/

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner

open Finset
open ArkLib.ProximityGap.SignedPeriodPowerCount
open ArkLib.ProximityGap.NegationClosedWalk (zeroSumCount)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The rigidity corner (kernel form).** Where the `r`-fold zero-sum count vanishes
(`zeroSumCount S r = 0` — below the odd onset depth `d_odd`), the signed deep sum is pinned to its
floor: `∑_{ψ≠0} η_ψ^r = −|S|^r`. This is the kernel grounding of the `DISPROOF_LOG` "sign-rigid
`A_r = −n^r` below `d_odd`" measurement. -/
theorem signedPeriodPow_eq_neg_card_pow_of_zeroSumCount_zero
    (S : Finset F) (r : ℕ) (hZ : zeroSumCount S r = 0) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      = - (S.card : ℂ) ^ r := by
  rw [nonzeroSignedPeriodPow_eq_zeroSumCount S r, hZ]
  simp

/-- **The rigidity corner is strictly negative** for a NONEMPTY domain. At the floor (`Z = 0`),
`A_r = −|S|^r` has strictly negative real part `−|S|^r < 0`, the literal "sign-rigid negative" floor.
(For `r = 0` the count is `1 ≠ 0`, so the hypothesis already forces `r` into the nontrivial range.) -/
theorem signedPeriodPow_re_neg_of_zeroSumCount_zero
    (S : Finset F) (r : ℕ) (hne : S.Nonempty) (hZ : zeroSumCount S r = 0) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r).re < 0 := by
  rw [signedPeriodPow_eq_neg_card_pow_of_zeroSumCount_zero S r hZ]
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hpos : (0 : ℝ) < (S.card : ℝ) ^ r := pow_pos hcard r
  have hre : (- (S.card : ℂ) ^ r).re = - (S.card : ℝ) ^ r := by
    have h1 : (- (S.card : ℂ) ^ r) = (((- (S.card : ℝ) ^ r : ℝ)) : ℂ) := by
      push_cast; ring
    rw [h1, Complex.ofReal_re]
  rw [hre]
  linarith

/-- **Sign ↔ count bridge (count side, field-universal, `|·|`-free).** The empirical
"`A_r ≤ 0` in the thin regime" is, via the identity `A_r = q·Z − |S|^r`, EXACTLY the count inequality
`q · zeroSumCount S r ≤ |S|^r`. We state the bridge over `ℝ` on the count: the signed sum's
real value is `≤ 0` iff `q·Z ≤ n^r`. This re-expresses the SIGN side of the wall as an honest
orbit-count-style upper bound on the signed zero-sum count (the `OrbitCountWall` object), with no
`|·|` anywhere. -/
theorem signedPeriodPow_re_nonpos_iff
    (S : Finset F) (r : ℕ) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r).re ≤ 0
      ↔ (Fintype.card F : ℝ) * (zeroSumCount S r : ℝ) ≤ (S.card : ℝ) ^ r := by
  have hid := nonzeroSignedPeriodPow_eq_zeroSumCount (F := F) S r
  rw [hid]
  -- `(q·Z − n^r).re = q·Z − n^r` since both summands are real-cast; then `≤ 0 ↔ q·Z ≤ n^r`.
  have hre : ((Fintype.card F : ℂ) * (zeroSumCount S r : ℂ) - (S.card : ℂ) ^ r).re
      = (Fintype.card F : ℝ) * (zeroSumCount S r : ℝ) - (S.card : ℝ) ^ r := by
    have h1 : ((Fintype.card F : ℂ) * (zeroSumCount S r : ℂ) - (S.card : ℂ) ^ r)
        = (((Fintype.card F : ℝ) * (zeroSumCount S r : ℝ) - (S.card : ℝ) ^ r : ℝ) : ℂ) := by
      push_cast; ring
    rw [h1, Complex.ofReal_re]
  rw [hre]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Sign ↔ count bridge, strict floor form.** `A_r = −|S|^r` (the strict rigidity floor) holds iff
the count is exactly zero. The signed sum sits at its negative floor *precisely* below the onset
depth where `zeroSumCount S r = 0`; any deviation up from `−|S|^r` is exactly `q·Z` worth of genuine
zero-sum relations switching on. -/
theorem signedPeriodPow_eq_neg_card_pow_iff_zeroSumCount_zero
    (S : Finset F) (r : ℕ) (hq : (Fintype.card F : ℂ) ≠ 0) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r) = - (S.card : ℂ) ^ r
      ↔ zeroSumCount S r = 0 := by
  rw [nonzeroSignedPeriodPow_eq_zeroSumCount S r]
  constructor
  · intro h
    have : (Fintype.card F : ℂ) * (zeroSumCount S r : ℂ) = 0 := by
      have := h
      ring_nf at this ⊢
      linear_combination this
    have hZc : (zeroSumCount S r : ℂ) = 0 := by
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hq
      · exact h0
    exact_mod_cast hZc
  · intro hZ
    rw [hZ]; simp

end ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner.signedPeriodPow_eq_neg_card_pow_of_zeroSumCount_zero
#print axioms ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner.signedPeriodPow_re_neg_of_zeroSumCount_zero
#print axioms ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner.signedPeriodPow_re_nonpos_iff
#print axioms ArkLib.ProximityGap.Frontier.SignedDeepRigidityCorner.signedPeriodPow_eq_neg_card_pow_iff_zeroSumCount_zero
