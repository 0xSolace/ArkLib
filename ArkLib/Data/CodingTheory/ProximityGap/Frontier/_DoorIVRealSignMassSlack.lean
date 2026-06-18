/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Door IV real sign-mass slack

This is a second small constraint brick for Shaw's door-(iv) coherence object.  Once a coset
refinement is negation-stable, every piece-period is real.  The only way the normalized coherence
can drop below `1` is then literal cancellation between the positive and negative real mass.

If `P` is the total positive mass and `N` is the total negative mass (recorded as a nonnegative
number), the real coherence is

`|P - N| / (P + N)`.

The exact formulas below say that the slack from `1` is precisely twice the minority sign mass
divided by the total mass.  Thus any door-(iv) theorem based on a real, negation-stable
refinement must prove a lower bound on the minority sign mass.  Merely naming a finer
decomposition does not supply phase
anti-concentration; it has to force a balanced sign split.

This is not CORE and not a moment/completion bound.  It is a constraint lemma for the
surviving door-(iv) lane.
-/

namespace ProximityGap.Frontier.DoorIVRealSignMassSlack

/-- Coherence after compressing real pieces to positive mass `P` and negative mass `N`. -/
noncomputable def signMassCoherence (P N : ℝ) : ℝ := |P - N| / (P + N)

/-- If negative mass is the minority, coherence is `1 - 2N/(P+N)`. -/
theorem signMassCoherence_eq_one_sub_twice_neg {P N : ℝ}
    (hle : N ≤ P) (hden : 0 < P + N) :
    signMassCoherence P N = 1 - 2 * N / (P + N) := by
  unfold signMassCoherence
  have hsub : 0 ≤ P - N := sub_nonneg.mpr hle
  rw [abs_of_nonneg hsub]
  field_simp [ne_of_gt hden]
  ring

/-- If positive mass is the minority, coherence is `1 - 2P/(P+N)`. -/
theorem signMassCoherence_eq_one_sub_twice_pos {P N : ℝ}
    (hle : P ≤ N) (hden : 0 < P + N) :
    signMassCoherence P N = 1 - 2 * P / (P + N) := by
  unfold signMassCoherence
  have hsub : P - N ≤ 0 := sub_nonpos.mpr hle
  rw [abs_of_nonpos hsub]
  field_simp [ne_of_gt hden]
  ring

/-- Real sign-mass coherence is always at most `1` for nonnegative sign masses. -/
theorem signMassCoherence_le_one {P N : ℝ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) (hden : 0 < P + N) :
    signMassCoherence P N ≤ 1 := by
  unfold signMassCoherence
  have h_abs : |P - N| ≤ P + N := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  exact (div_le_one hden).mpr h_abs

end ProximityGap.Frontier.DoorIVRealSignMassSlack

open ProximityGap.Frontier.DoorIVRealSignMassSlack

#print axioms signMassCoherence_eq_one_sub_twice_neg
#print axioms signMassCoherence_eq_one_sub_twice_pos
#print axioms signMassCoherence_le_one
