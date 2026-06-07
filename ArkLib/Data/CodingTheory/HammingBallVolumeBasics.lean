/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# Basic facts about the q-ary Hamming-ball volume

Elementary monotonicity and positivity of `CodingTheory.hammingBallVolume` (ABF26 Def 2.4),
complementing the entropy-volume *bounds* in `EntropyVolumeBound.lean`.

* `hammingBallVolume_mono` / `hammingBallVolume_real_mono` — monotonicity in the relative radius.
* `one_le_hammingBallVolume` — the centre is always counted, so the volume is `≥ 1`.
-/

namespace CodingTheory

/-- **Monotonicity of the Hamming-ball volume in the relative radius.** A larger radius gives a
larger ball: the summation range `range (⌊δ·n⌋₊+1)` only grows, and every layer is `≥ 0`. -/
theorem hammingBallVolume_mono (q n : ℕ) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    hammingBallVolume q δ₁ n ≤ hammingBallVolume q δ₂ n := by
  unfold hammingBallVolume
  apply Finset.sum_le_sum_of_subset
  apply Finset.range_mono
  exact Nat.succ_le_succ
    (Nat.floor_le_floor (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n)))

/-- Real-valued form of `hammingBallVolume_mono`. -/
theorem hammingBallVolume_real_mono (q n : ℕ) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    (hammingBallVolume q δ₁ n : ℝ) ≤ (hammingBallVolume q δ₂ n : ℝ) := by
  exact_mod_cast hammingBallVolume_mono q n hδ

/-- **The Hamming-ball volume is at least one** — the centre itself (the `i = 0` layer
`C(n,0)·(q-1)^0 = 1`) is always counted. -/
theorem one_le_hammingBallVolume (q : ℕ) (δ : ℝ) (n : ℕ) :
    1 ≤ hammingBallVolume q δ n := by
  unfold hammingBallVolume
  calc 1 = Nat.choose n 0 * (q - 1) ^ 0 := by simp
    _ ≤ ∑ i ∈ Finset.range (⌊δ * n⌋₊ + 1), Nat.choose n i * (q - 1) ^ i :=
        Finset.single_le_sum (f := fun i => Nat.choose n i * (q - 1) ^ i)
          (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos _))

end CodingTheory

-- Axiom audit (kernel-clean): [propext, Classical.choice, Quot.sound]
#print axioms CodingTheory.hammingBallVolume_mono
#print axioms CodingTheory.one_le_hammingBallVolume
