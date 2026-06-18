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

/-- Threshold form of the sign-mass constraint.  To force real-piece coherence below
`1 - eps`, the minority sign mass must be at least an `eps/2` fraction of the total
mass.  Thus a real, negation-stable door-(iv) refinement only helps after proving a
quantitative lower bound on minority sign mass. -/
theorem minority_mass_ge_of_coherence_le_one_sub {P N eps : ℝ}
    (hden : 0 < P + N) (hcoh : signMassCoherence P N ≤ 1 - eps) :
    eps * (P + N) / 2 ≤ min P N := by
  rcases le_total N P with hNP | hPN
  · have hform := signMassCoherence_eq_one_sub_twice_neg hNP hden
    have hineq : 1 - 2 * N / (P + N) ≤ 1 - eps := by
      simpa [hform] using hcoh
    have heps_le : eps ≤ 2 * N / (P + N) := by linarith
    have hmul : eps * (P + N) ≤ 2 * N := by
      exact (le_div_iff₀ hden).mp heps_le
    have hhalf : eps * (P + N) / 2 ≤ N := by linarith
    simpa [min_eq_right hNP] using hhalf
  · have hform := signMassCoherence_eq_one_sub_twice_pos hPN hden
    have hineq : 1 - 2 * P / (P + N) ≤ 1 - eps := by
      simpa [hform] using hcoh
    have heps_le : eps ≤ 2 * P / (P + N) := by linarith
    have hmul : eps * (P + N) ≤ 2 * P := by
      exact (le_div_iff₀ hden).mp heps_le
    have hhalf : eps * (P + N) / 2 ≤ P := by linarith
    simpa [min_eq_left hPN] using hhalf

/-- Exact one-line sign-mass formula: real-piece coherence is one minus twice the
minority sign mass divided by total mass. -/
theorem signMassCoherence_eq_one_sub_twice_min {P N : ℝ} (hden : 0 < P + N) :
    signMassCoherence P N = 1 - 2 * min P N / (P + N) := by
  rcases le_total N P with hNP | hPN
  · simpa [min_eq_right hNP] using signMassCoherence_eq_one_sub_twice_neg hNP hden
  · simpa [min_eq_left hPN] using signMassCoherence_eq_one_sub_twice_pos hPN hden

/-- Exact threshold equivalence for real-piece coherence.  Achieving a target `theta`
is equivalent to proving that the minority sign mass is at least `(1-theta)/2` of the
total mass. -/
theorem signMassCoherence_le_iff_minority_mass_ge {P N theta : ℝ}
    (hden : 0 < P + N) :
    signMassCoherence P N ≤ theta ↔ (1 - theta) * (P + N) / 2 ≤ min P N := by
  rw [signMassCoherence_eq_one_sub_twice_min hden]
  constructor
  · intro hcoh
    have hle : 1 - theta ≤ 2 * min P N / (P + N) := by linarith
    have hmul : (1 - theta) * (P + N) ≤ 2 * min P N := by
      exact (le_div_iff₀ hden).mp hle
    linarith
  · intro hminor
    have hmul : (1 - theta) * (P + N) ≤ 2 * min P N := by linarith
    have hle : 1 - theta ≤ 2 * min P N / (P + N) := by
      exact (le_div_iff₀ hden).mpr hmul
    linarith

/-- Equivalent operational corollary: if the minority sign mass is below an `eps/2`
fraction of total mass, then a real-piece coherence drop of size `eps` is impossible. -/
theorem not_coherence_le_one_sub_of_minority_mass_lt {P N eps : ℝ}
    (hden : 0 < P + N) (hminor : min P N < eps * (P + N) / 2) :
    ¬ signMassCoherence P N ≤ 1 - eps := by
  intro hcoh
  have hge := minority_mass_ge_of_coherence_le_one_sub hden hcoh
  linarith

end ProximityGap.Frontier.DoorIVRealSignMassSlack

open ProximityGap.Frontier.DoorIVRealSignMassSlack

#print axioms signMassCoherence_eq_one_sub_twice_neg
#print axioms signMassCoherence_eq_one_sub_twice_pos
#print axioms signMassCoherence_le_one
#print axioms minority_mass_ge_of_coherence_le_one_sub
#print axioms signMassCoherence_eq_one_sub_twice_min
#print axioms signMassCoherence_le_iff_minority_mass_ge
#print axioms not_coherence_le_one_sub_of_minority_mass_lt
