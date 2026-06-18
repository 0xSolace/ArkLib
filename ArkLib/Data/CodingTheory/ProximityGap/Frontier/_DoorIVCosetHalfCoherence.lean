/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV coset-half coherence: the index-2 split has a sign-degeneracy

This file records the tiny axiom-clean arithmetic brick behind the probe
`scripts/probes/probe_dooriv_cosethalf_coherence.py`.

For the standard two-piece split of a 2-power subgroup `H = H₀ ⊔ hH₀`, each half is closed under
negation once `4 ∣ n`, so the two half-period sums are real.  Consequently the two-piece coherence

`ρ(A,B) = |A+B| / (|A|+|B|)`

has no intrinsic slack: whenever the two real half-sums have the same sign it is exactly `1`.
The probe finds such same-sign adversarial cosets throughout the thin prize regime.  This does not
prove CORE and does not use moments/completion; it is a constraint lemma saying that the **raw
index-2 coset-half coherence** is too degenerate to be the missing anti-concentration input unless
one refines the decomposition beyond two negation-stable halves.
-/

namespace ProximityGap.Frontier.DoorIVCosetHalfCoherence

/-- Two-piece coherence of real half-period sums. -/
noncomputable def twoPieceCoherence (A B : ℝ) : ℝ := |A + B| / (|A| + |B|)

/-- If both real half-period sums are nonnegative and not both zero, their two-piece coherence is
exactly one.  This is the positive-sign half of the door-(iv) index-2 degeneracy. -/
theorem twoPieceCoherence_eq_one_of_nonneg {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hpos : 0 < A + B) :
    twoPieceCoherence A B = 1 := by
  unfold twoPieceCoherence
  rw [abs_of_nonneg hA, abs_of_nonneg hB, abs_of_nonneg (add_nonneg hA hB)]
  field_simp [ne_of_gt hpos]

/-- If both real half-period sums are nonpositive and not both zero, their two-piece coherence is
exactly one.  This is the negative-sign half of the door-(iv) index-2 degeneracy. -/
theorem twoPieceCoherence_eq_one_of_nonpos {A B : ℝ}
    (hA : A ≤ 0) (hB : B ≤ 0) (hneg : A + B < 0) :
    twoPieceCoherence A B = 1 := by
  unfold twoPieceCoherence
  have hA' : 0 ≤ -A := neg_nonneg.mpr hA
  have hB' : 0 ≤ -B := neg_nonneg.mpr hB
  have hsum' : 0 ≤ -(A + B) := le_of_lt (neg_pos.mpr hneg)
  rw [abs_of_nonpos hA, abs_of_nonpos hB, abs_of_nonpos (le_of_lt hneg)]
  have hden : -A + -B = -(A + B) := by ring
  rw [hden]
  exact div_self (ne_of_gt (neg_pos.mpr hneg))

/-- A compact same-sign formulation: if the two real half-sums are both nonnegative or both
nonpositive, and their total is nonzero, then their two-piece coherence is exactly one.  This is the
formal constraint used by the probe: once the two half-sums are forced onto the real line, same-sign
adversarial cosets saturate `ρ`. -/
theorem twoPieceCoherence_eq_one_of_sameSign {A B : ℝ}
    (hsign : (0 ≤ A ∧ 0 ≤ B) ∨ (A ≤ 0 ∧ B ≤ 0)) (hsum : A + B ≠ 0) :
    twoPieceCoherence A B = 1 := by
  rcases hsign with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact twoPieceCoherence_eq_one_of_nonneg hA hB
      (lt_of_le_of_ne (add_nonneg hA hB) hsum.symm)
  · exact twoPieceCoherence_eq_one_of_nonpos hA hB
      (lt_of_le_of_ne (add_nonpos hA hB) hsum)

/-- Opposite nonzero signs give strict slack in the real two-piece coherence.  Thus the only
possible saving in the raw index-2 split is a sign-cancellation event; magnitude imbalance alone
cannot produce a nontrivial door-(iv) theorem. -/
theorem twoPieceCoherence_lt_one_of_pos_neg {A B : ℝ}
    (hA : 0 < A) (hB : B < 0) :
    twoPieceCoherence A B < 1 := by
  unfold twoPieceCoherence
  rw [abs_of_pos hA, abs_of_neg hB]
  have hden : 0 < A + -B := by linarith
  have hnum_lt : |A + B| < A + -B := by
    rw [abs_lt]
    constructor <;> linarith
  calc
    |A + B| / (A + -B) < (A + -B) / (A + -B) :=
      div_lt_div_of_pos_right hnum_lt hden
    _ = 1 := div_self (ne_of_gt hden)

/-- Symmetric opposite-sign slack. -/
theorem twoPieceCoherence_lt_one_of_neg_pos {A B : ℝ}
    (hA : A < 0) (hB : 0 < B) :
    twoPieceCoherence A B < 1 := by
  unfold twoPieceCoherence
  rw [abs_of_neg hA, abs_of_pos hB]
  have hden : 0 < -A + B := by linarith
  have hnum_lt : |A + B| < -A + B := by
    rw [abs_lt]
    constructor <;> linarith
  calc
    |A + B| / (-A + B) < (-A + B) / (-A + B) :=
      div_lt_div_of_pos_right hnum_lt hden
    _ = 1 := div_self (ne_of_gt hden)

end ProximityGap.Frontier.DoorIVCosetHalfCoherence

#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_nonneg
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_nonpos
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_eq_one_of_sameSign
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_lt_one_of_pos_neg
#print axioms ProximityGap.Frontier.DoorIVCosetHalfCoherence.twoPieceCoherence_lt_one_of_neg_pos
