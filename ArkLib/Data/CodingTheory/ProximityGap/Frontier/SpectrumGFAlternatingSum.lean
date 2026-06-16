/-
# The char-0 subset-sum spectrum generating function at `x = -1`: the alternating sum (#444)

`Sweep_A50_SpectrumGeneratingFunction` proved the closed-form generating-function identity

  `(x² − 1) · G(x) = x^{m+2}·(x+2)^m − (2x+1)^m`,   `G(x) = spectrumGF x m = ∑_r N_r x^r`,

and its header asserts three evaluations subsume the prior census bricks:
* `x = 1`   → the total mass `T(m) = 3^{m-1}(m+3)` (proven separately in
  `_SubsetSumSpectrumTotalMass`);
* `x = −1`  → the **alternating sum** `∑_r (−1)^r N_r = (−1)^{m+1}(m−1)`, marked "**(new here)**";
* the RHS functional equation ⟺ the complement-symmetry palindrome `N_r = N_{2m−r}`.

The `x = −1` evaluation is **not** a corollary of `spectrumGF_mul_eq`: at `x = −1` the factor
`(x² − 1) = 0`, so the value is a *removable singularity* — it cannot be obtained by dividing the
closed form. It requires a **direct** evaluation of the manifest net-vector double sum. This file
discharges A50's asserted-but-unproven `x = −1` consequence into a theorem.

**Mechanism (elementary, char-0).** At `x = −1` the inner geometric block collapses
(`∑_{i<m−k+1} (−1)^{k+2i} = (−1)^k (m−k+1)`), so

  `spectrumGF (−1) m = ∑_k C(m,k) (−2)^k (m−k+1)`
                     `= (m+1)·∑_k C(m,k)(−2)^k − ∑_k k·C(m,k)(−2)^k`
                     `= (m+1)·(−1)^m − 2m·(−1)^m`              [binomial `(1−2)^m` + its `k`-weight]
                     `= (−1)^m (1−m) = (−1)^{m+1}(m−1)`.

The `k`-weighted sum `∑_k k C(m,k)(−2)^k = 2m(−1)^m` is the `succ_mul_choose_eq` index-shift
companion of the total-mass file's `Σ k C(m,k)2^k = 2m·3^{m−1}`, here over a `CommRing` with the
signed base `−2` (so `(1−2)^{m−1} = (−1)^{m−1}` and the `−2` factor flips it to `2m(−1)^m`).

**Honest scope (the wall is untouched).** This is the char-0 / cross-polytope alternating count.
It equals the `F_p` object only in the dilute regime `N_r ≪ p`; the prize-binding depth `r = ρn`
is collision-saturated and the `Ψ_p − Ψ₀ > 0` defect (= BGK / BCHKS-1.12) is the open core and is
**not** addressed here. No capacity / beyond-Johnson / sub-linear / growth-law claim. The `x = −1`
here is a generating-function evaluation point, NOT the asymptotic-guard incidence cliff-at-n/2.
CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A50_SpectrumGeneratingFunction
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

variable {R : Type*} [CommRing R]

/-- **The inner geometric block at `x = −1` collapses.** `∑_{i<m−k+1} (−1)^{k+2i} = (−1)^k(m−k+1)`,
since each `(−1)^{2i} = 1`. -/
private theorem inner_neg_one (m k : ℕ) :
    ∑ i ∈ range (m - k + 1), (-1 : R) ^ (k + 2 * i)
      = (-1) ^ k * ((m - k + 1 : ℕ) : R) := by
  have : ∀ i ∈ range (m - k + 1), (-1 : R) ^ (k + 2 * i) = (-1) ^ k := by
    intro i _
    rw [pow_add, pow_mul]
    simp
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, nsmul_eq_mul]
  ring

/-- **Binomial GF at `−2`**: `∑_{k≤m} C(m,k)(−2)^k = (−1)^m` (binomial theorem at `−2 + 1`). -/
theorem sum_choose_neg_two_pow (m : ℕ) :
    ∑ k ∈ range (m + 1), (m.choose k : R) * (-2) ^ k = (-1) ^ m := by
  have h := (add_pow (-2 : R) 1 m).symm
  simp only [one_pow, mul_one] at h
  rw [show ((-1 : R)) = (-2) + 1 by ring, ← h]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **`k`-weighted binomial GF at `−2`**: `∑_{k≤m} k·C(m,k)(−2)^k = 2m·(−1)^m`, via the index
shift `k·C(m,k) = m·C(m−1,k−1)` (`succ_mul_choose_eq`) + `sum_choose_neg_two_pow`. The signed
companion of the total-mass file's `Σ k C(m,k)2^k = 2m·3^{m−1}`. -/
theorem sum_k_choose_neg_two_pow (m : ℕ) :
    ∑ k ∈ range (m + 1), (k : R) * ((m.choose k : R) * (-2) ^ k) = 2 * m * (-1) ^ m := by
  rcases m with _ | m
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hkey : ∀ j ∈ range (m + 1),
        ((j + 1 : ℕ) : R) * (((m + 1).choose (j + 1) : R) * (-2) ^ (j + 1))
          = (-2) * (m + 1) * (((m.choose j : R) * (-2) ^ j)) := by
      intro j _
      have hc : (m + 1) * m.choose j = (m + 1).choose (j + 1) * (j + 1) := by
        have := Nat.add_one_mul_choose_eq m j
        simpa using this
      have hcR : ((m + 1 : ℕ) : R) * (m.choose j : R)
          = ((m + 1).choose (j + 1) : R) * ((j + 1 : ℕ) : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) hc
      push_cast
      push_cast at hcR
      have hstep : (((j : R) + 1)) * (((m + 1).choose (j + 1) : R))
          = ((m : R) + 1) * (m.choose j : R) := by
        rw [hcR]; ring
      calc ((j : R) + 1) * (((m + 1).choose (j + 1) : R) * (-2) ^ (j + 1))
          = (((j : R) + 1) * ((m + 1).choose (j + 1) : R)) * (-2) ^ (j + 1) := by ring
        _ = (((m : R) + 1) * (m.choose j : R)) * (-2) ^ (j + 1) := by rw [hstep]
        _ = (-2) * ((m : R) + 1) * ((m.choose j : R) * (-2) ^ j) := by rw [pow_succ]; ring
    rw [Finset.sum_congr rfl hkey]
    rw [← Finset.mul_sum, sum_choose_neg_two_pow m]
    push_cast
    ring

/-- **`spectrumGF` at `x = −1`, in the manifest `k`-form.**
`spectrumGF (−1) m = ∑_{k≤m} C(m,k)(−2)^k (m−k+1)`. -/
theorem spectrumGF_neg_one_kform (m : ℕ) :
    spectrumGF (-1 : R) m
      = ∑ k ∈ range (m + 1), ((m.choose k : R) * (-2) ^ k) * ((m - k + 1 : ℕ) : R) := by
  unfold spectrumGF
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [inner_neg_one]
  have : ((-2 : R)) ^ k = (2 : R) ^ k * (-1) ^ k := by
    rw [show ((-2 : R)) = (-1) * 2 by ring, mul_pow]; ring
  rw [this]
  push_cast
  ring

/-- **The alternating sum (A50's "(new here)" consequence, discharged).**
`spectrumGF (−1) m = (−1)^{m+1}(m−1)`, i.e. `∑_r (−1)^r N_r = (−1)^{m+1}(m−1)`, for every `m`
(the `m = 0` edge holds too: both sides equal `1`). The removable-singularity value of A50's
`spectrumGF_mul_eq` at `x = −1`, evaluated DIRECTLY (it is NOT obtainable by division since
`(x²−1)=0` there). -/
theorem spectrumGF_neg_one (m : ℕ) :
    spectrumGF (-1 : R) m = (-1) ^ (m + 1) * ((m : R) - 1) := by
  rw [spectrumGF_neg_one_kform]
  -- split (m-k+1) = (m+1) - k  [valid for k ≤ m], distribute over the two binomial GF sums
  have hsplit : ∀ k ∈ range (m + 1),
      ((m.choose k : R) * (-2) ^ k) * ((m - k + 1 : ℕ) : R)
        = ((m : R) + 1) * ((m.choose k : R) * (-2) ^ k)
          - (k : R) * ((m.choose k : R) * (-2) ^ k) := by
    intro k hk
    have hkm : k ≤ m := by simpa [Nat.lt_succ_iff] using mem_range.mp hk
    have hcast : ((m - k + 1 : ℕ) : R) = (m : R) - (k : R) + 1 := by
      push_cast [Nat.cast_sub hkm]; ring
    rw [hcast]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_choose_neg_two_pow, sum_k_choose_neg_two_pow]
  -- ((m+1)·(-1)^m - 2m·(-1)^m) = (-1)^m·(1-m) = (-1)^(m+1)(m-1)
  have hpow : (-1 : R) ^ (m + 1) = (-1) * (-1) ^ m := by rw [pow_succ]; ring
  rw [hpow]; ring

end ArkLib.ProximityGap.EvenOddDescent
