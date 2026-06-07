/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentReduction

/-!
# CS25 second moment — pair-count reformulation (#82)

The remaining second-moment input `∑_w (closeCount w)²` reorganizes, by double counting, into a
sum over ordered codeword pairs of the **two-ball intersection volume**:

  `∑_w (closeCount 𝒞 r w)² = ∑_{c, c' ∈ 𝒞} #{w : Δ₀(w,c) ≤ r ∧ Δ₀(w,c') ≤ r}`.

Each `w` counted in `(closeCount w)²` corresponds to an ordered pair `(c, c')` of close codewords;
swapping the order of summation collects the count of `w` simultaneously close to both `c` and `c'`,
i.e. `|B(c,r) ∩ B(c',r)|`.  By translation invariance this depends only on `Δ₀(c,c')`, so the next
step expresses it via the RS/MDS weight enumerator `A_d` (`RSWeightEnumerator.card_evalWeight_le`)
and the ball-intersection volume `I(d)` — `E[N²] = |𝒞|·∑_d A_d·I(d)`.
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Second moment as a pair sum (double counting).**  `∑_w (closeCount w)²` equals the sum over
ordered codeword pairs `(c, c')` of the two-ball intersection count `#{w : close to both}`. -/
omit [AddCommGroup F] in
theorem sum_closeCount_sq_eq (𝒞 : Finset (ι → F)) (r : ℕ) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      = ∑ c ∈ 𝒞, ∑ c' ∈ 𝒞,
          (Finset.univ.filter (fun w : ι → F =>
            hammingDist w c ≤ r ∧ hammingDist w c' ≤ r)).card := by
  classical
  have hcc : ∀ w : ι → F, (closeCount 𝒞 r w) ^ 2
      = ∑ c ∈ 𝒞, ∑ c' ∈ 𝒞,
          (if hammingDist w c ≤ r ∧ hammingDist w c' ≤ r then (1 : ℕ) else 0) := by
    intro w
    simp only [pow_two, closeCount, Finset.card_filter]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
    by_cases h1 : hammingDist w c ≤ r <;> by_cases h2 : hammingDist w c' ≤ r <;> simp [h1, h2]
  simp_rw [hcc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [Finset.card_filter]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_closeCount_sq_eq
