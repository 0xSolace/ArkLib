/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftDevacuated
import ArkLib.Data.CodingTheory.ProximityGap.RepCountSidonBound
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction

/-!
# THE GARCIA–VOLOCH SUPPLY WALL CLOSES UNCONDITIONALLY FOR SMALL SUBGROUPS (#389)

`RepCountSidonBound.gvRepBound_of_sidonModNeg` proves: *if* `μ_n ⊂ F_p` is Sidon-modulo-negation,
then the Garcia–Voloch representation bound `GVRepBound (μ_n) M` holds at the optimal `M = O(√n)`
scale — and with it the entire supply chain of `GVHBKEnergyReduction` (`E(μ_n) ≲ |G|^{8/3}`).  That
file flags the conditional honestly: `μ_n` over `F_p` is **not** Sidon at prize scale (large `n`).

`SidonLiftDevacuated.sidonModNeg_rootsOfUnity` now **discharges that conditional unconditionally in
the small-subgroup regime** `p > 4^{φ(n)} = 2^n`: there `μ_n` *is* Sidon-modulo-negation, by the
de-vacuated no-parallelogram lifting.  Composing the two:

> **`gvRepBound_rootsOfUnity`** — for `p > 4^{φ(n)}` and any `M` with `3n ≤ M²` and `M³ ≤ 64n²`,
> `GVRepBound (μ_n) M` holds; i.e. every nonzero shift has `≤ M = O(√n)` representations.

**Honest scope.** This closes the *supply* side (the GV/HBK rep-bound and hence
`E(μ_n) ≲ |G|^{8/3}`) for `n < log₂ p` — exactly the regime where Sidon holds.  It does **not** pin
`δ*` past Johnson: the supply→line-incidence bridge carries a `√`-loss (the recognized open wall),
and the prize regime `n ~ √p` (where Sidon fails) is untouched.  Issue #389.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- The explicit `n`-th roots `{ω^t : t < n}` are exactly `nthRootsFinset n 1`. -/
theorem image_eq_nthRootsFinset {n : ℕ} (hn0 : n ≠ 0) {p : ℕ} [Fact p.Prime]
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    (Finset.range n).image (ω ^ ·) = Polynomial.nthRootsFinset n (1 : ZMod p) := by
  have hcardImg : ((Finset.range n).image (ω ^ ·)).card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h := (primitiveRoot_pow_eq_iff hn0 hω a b).mp hab
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
  · simp only [Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t, _, rfl⟩ := hz
    rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0)]
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  · rw [hω.card_nthRootsFinset]; exact hcardImg.ge

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg in
/-- **The GV supply wall closes UNCONDITIONALLY in the small-subgroup regime.**  For `p > 4^{φ(n)}`
(`= 2^n` when `n = 2^m`) and any `M` with `3n ≤ M²` and `M³ ≤ 64n²`, the Garcia–Voloch rep bound
`GVRepBound (μ_n) M` holds — discharging, via the de-vacuated Sidon lifting, the conditional of
`gvRepBound_of_sidonModNeg`. -/
theorem gvRepBound_rootsOfUnity {n : ℕ} (hn2 : 2 ∣ n) (hn0 : n ≠ 0)
    {p : ℕ} [Fact p.Prime] [NeZero (n : ZMod p)] (hp : 4 ^ n.totient < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {M : ℕ}
    (hM : 3 * n ≤ M ^ 2) (hM3 : M ^ 3 ≤ 64 * n ^ 2) :
    GVRepBound ((Finset.range n).image (ω ^ ·)) M := by
  set G := (Finset.range n).image (ω ^ ·) with hG
  have hp2 : 2 < p := by
    have : (4 : ℕ) ≤ 4 ^ n.totient :=
      Nat.le_self_pow (by have : 1 ≤ n.totient := Nat.totient_pos.mpr (by omega); omega) 4
    omega
  haveI : NeZero p := ⟨by omega⟩
  have hroots := image_eq_nthRootsFinset hn0 hω
  have hGmem : ∀ z, z ∈ G ↔ z ^ n = 1 := by
    intro z; rw [hG, hroots, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn0)]
  have hcard : G.card = n := by rw [hG, hroots, hω.card_nthRootsFinset]
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have h0 : (0 : ZMod p) ∉ G := by
    intro hmem; rw [hGmem, zero_pow hn0] at hmem; exact zero_ne_one hmem
  have hev : Even n := even_iff_two_dvd.mpr hn2
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    rw [hGmem] at hx
    rw [hGmem, neg_pow, hx, mul_one]; exact hev.neg_one_pow
  have hS : SidonModNeg G := sidonModNeg_rootsOfUnity hn2 hn0 hp hω
  exact gvRepBound_of_sidonModNeg (by omega : 1 ≤ n) hGmem hcard h2 h0 hneg hS hM
    (by rw [hcard]; exact hM3)

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.gvRepBound_rootsOfUnity
