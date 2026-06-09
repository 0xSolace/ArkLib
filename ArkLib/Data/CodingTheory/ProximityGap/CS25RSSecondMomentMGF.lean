/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BallIntersectionMGF
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSNearBound
import ArkLib.Data.CodingTheory.ProximityGap.CS25RSMinDistance

set_option linter.style.longLine false

/-!
# CS25 #82: the unconditional second-moment Chernoff bound for Reed–Solomon codes

This file discharges the MDS weight-distribution hypothesis of `sum_jointCoverCount_mgf_mds_le`
for actual Reed–Solomon codes, giving an **unconditional** tight second-moment bound:

  `θ^{2r} · ∑_{e∈RS} I(e) ≤ A_0·(1+(q−1)θ²)^n + (q·(2θ+(q−2)θ²)+(1+(q−1)θ²))^n / q^{n−k}`,

for every `θ ∈ [0,1]`, where `RS = rsCodeFinset domain k`, `r = ⌊δ·n⌋`, `q = |F|`, `n = |ι|`, and
`A_0 = #{e∈RS : e=0}` (`= 1`).

The off-diagonal weight bound `A_d ≤ C(n,d)q^d/q^{n−k}` (`d ≥ 1`) is proven from two in-tree facts:
* `card_evalWeight_le` (the MDS weight enumerator, via `rsCodeFinset_eq_image` and
  `hammingNorm_evalOnPoints_eq_evalSupport_card`) — covers `d > n−k`;
* `rsCodeFinset_hammingDist_ge` (RS minimum distance `n−k+1`) — gives `A_d = 0` for `1 ≤ d ≤ n−k`.

Combined with `sum_jointCoverCount_mgf_mds_le` (the MGF/Chernoff ball-intersection bound), this is the
complete, machine-checked CS25 second moment for Reed–Solomon codes, reduced to a single-variable
optimization over `θ ∈ [0,1]`.

## Main results

* `rs_codeword_weight_count_le` — exact-weight RS codeword count `A_d ≤ C(n,d)q^{deg−(n−d)}`.
* `rs_offdiag_weight_bound` — the off-diagonal MDS bound `A_d ≤ C(n,d)q^d/q^{n−deg}` for `d ≥ 1`.
* `rs_sum_jointCoverCount_mgf_le` — the unconditional RS second-moment Chernoff bound.
-/

open scoped BigOperators NNReal

namespace ArkLib.CS25

open Code Finset Polynomial

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Exact-weight RS codeword count.** The number of Reed–Solomon codewords of Hamming weight exactly
`d` is at most `C(n,d)·q^{deg−(n−d)}` — the codewords are evaluations of degree-`<deg` polynomials
(`rsCodeFinset_eq_image`) with eval-support of size `d` (`hammingNorm_evalOnPoints…`), counted by the
MDS weight enumerator `card_evalWeight_le`. -/
theorem rs_codeword_weight_count_le (domain : ι ↪ F) (deg d : ℕ)
    [Fintype (Polynomial.degreeLT F deg)] :
    ((rsCodeFinset domain deg).filter (fun v => hammingNorm v = d)).card
      ≤ (Fintype.card ι).choose d * (Fintype.card F) ^ (deg - (Fintype.card ι - d)) := by
  have hsub : (rsCodeFinset domain deg).filter (fun v => hammingNorm v = d)
      ⊆ (Finset.univ.filter (fun p : Polynomial.degreeLT F deg =>
          (evalSupport domain p).card = d)).image
          (fun p : Polynomial.degreeLT F deg => ReedSolomon.evalOnPoints domain (p : F[X])) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvcode, hvwt⟩ := hv
    rw [rsCodeFinset_eq_image, Finset.mem_image] at hvcode
    obtain ⟨p, _, hpv⟩ := hvcode
    rw [Finset.mem_image]
    refine ⟨p, ?_, hpv⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      by rw [← hammingNorm_evalOnPoints_eq_evalSupport_card, hpv]; exact hvwt⟩
  exact le_trans (Finset.card_le_card hsub)
    (le_trans Finset.card_image_le (card_evalWeight_le domain deg d))

/-- **Off-diagonal MDS weight bound for Reed–Solomon codes.** For `1 ≤ d`, `A_d ≤ C(n,d)q^d/q^{n−deg}`.
For `1 ≤ d ≤ n−deg` the count is `0` (minimum distance `n−deg+1`, `rsCodeFinset_hammingDist_ge`); for
`d > n−deg` it follows from `rs_codeword_weight_count_le` with the exponent identity
`deg−(n−d) = d−(n−deg)`. -/
theorem rs_offdiag_weight_bound (domain : ι ↪ F) (deg : ℕ) [NeZero deg]
    [Fintype (Polynomial.degreeLT F deg)] (hdeg_le : deg ≤ Fintype.card ι) (d : ℕ) (hd : 1 ≤ d) :
    (((rsCodeFinset domain deg).filter (fun v => hammingNorm v = d)).card : ℝ)
      ≤ (Nat.choose (Fintype.card ι) d : ℝ) * (Fintype.card F : ℝ) ^ d
          / (Fintype.card F : ℝ) ^ (Fintype.card ι - deg) := by
  haveI : Nonempty F := ⟨0⟩
  have hdeg1 : 1 ≤ deg := Nat.one_le_iff_ne_zero.mpr (NeZero.ne deg)
  set n := Fintype.card ι with hn
  have hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hcase : d ≤ n - deg ∨ n < d
  · have hempty : (rsCodeFinset domain deg).filter (fun v => hammingNorm v = d) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv hwt
      rcases hcase with hle | hgt
      · have hv0 : v ≠ 0 := fun h => by rw [h, hammingNorm_zero] at hwt; omega
        have h0 : (0 : ι → F) ∈ rsCodeFinset domain deg :=
          (mem_rsCodeFinset _ _ _).mpr (Submodule.zero_mem _)
        have hdist := rsCodeFinset_hammingDist_ge domain deg v (0 : ι → F) hv h0 hv0
        rw [hammingDist_zero_right, hwt] at hdist
        omega
      · have hle := hammingNorm_le_card_fintype (x := v)
        omega
    rw [hempty, Finset.card_empty, Nat.cast_zero]; positivity
  · simp only [not_or, not_le, not_lt] at hcase
    obtain ⟨hbig, hdn⟩ := hcase
    have hcnt : (((rsCodeFinset domain deg).filter (fun v => hammingNorm v = d)).card : ℝ)
        ≤ (Nat.choose n d : ℝ) * (Fintype.card F : ℝ) ^ (deg - (n - d)) := by
      calc (((rsCodeFinset domain deg).filter (fun v => hammingNorm v = d)).card : ℝ)
          ≤ ((Nat.choose n d * (Fintype.card F) ^ (deg - (n - d)) : ℕ) : ℝ) := by
            exact_mod_cast rs_codeword_weight_count_le domain deg d
        _ = (Nat.choose n d : ℝ) * (Fintype.card F : ℝ) ^ (deg - (n - d)) := by push_cast; ring
    refine le_trans hcnt (le_of_eq ?_)
    rw [eq_div_iff (by positivity), mul_assoc, ← pow_add]
    congr 2
    omega

/-- **Unconditional second-moment Chernoff bound for Reed–Solomon codes.** For every `θ ∈ [0,1]`,

  `θ^{2r} · ∑_{e∈RS} I(e) ≤ A_0·(1+(q−1)θ²)^n + (q·(2θ+(q−2)θ²)+(1+(q−1)θ²))^n / q^{n−deg}`,

`r = ⌊δ·n⌋`, `A_0 = #{e∈RS : e=0}`.  The MDS hypothesis of `sum_jointCoverCount_mgf_mds_le` is
discharged by `rs_offdiag_weight_bound`.  The diagonal `A_0`-term is the `e=0` ball volume `V`; the
off-diagonal is fully explicit in `(θ,q,n,deg)`.  Minimizing over `θ ∈ [0,1]` yields the CS25
second-moment exponent — the final input to the `ε_ca` capacity breakdown. -/
theorem rs_sum_jointCoverCount_mgf_le [Nonempty ι] (domain : ι ↪ F) (deg : ℕ) [NeZero deg]
    [Fintype (Polynomial.degreeLT F deg)] (hdeg_le : deg ≤ Fintype.card ι)
    (δ : ℝ≥0) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ ^ (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊)
        * (∑ e ∈ rsCodeFinset domain deg, (jointCoverCount δ 0 e : ℝ))
      ≤ (((rsCodeFinset domain deg).filter (fun e => hammingNorm e = 0)).card : ℝ)
          * (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2) ^ (Fintype.card ι)
        + ((Fintype.card F : ℝ) * (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2)
            + (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2)) ^ (Fintype.card ι)
          / (Fintype.card F : ℝ) ^ (Fintype.card ι - deg) :=
  sum_jointCoverCount_mgf_mds_le (rsCodeFinset domain deg) δ θ hθ0 hθ1 deg
    (fun d hd => rs_offdiag_weight_bound domain deg hdeg_le d hd)

/-- The unique weight-`0` Reed–Solomon codeword is `0`, so `A_0 = 1`. -/
theorem rs_weight_zero_card (domain : ι ↪ F) (deg : ℕ) :
    ((rsCodeFinset domain deg).filter (fun e => hammingNorm e = 0)).card = 1 := by
  have h0 : (0 : ι → F) ∈ rsCodeFinset domain deg :=
    (mem_rsCodeFinset _ _ _).mpr (Submodule.zero_mem _)
  have hset : (rsCodeFinset domain deg).filter (fun e => hammingNorm e = 0) = {0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_singleton, hammingNorm_eq_zero]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ h0, h⟩⟩
  rw [hset, Finset.card_singleton]

/-- **Clean unconditional RS second-moment Chernoff bound** (`A_0 = 1` substituted): for every
`θ ∈ [0,1]`,

  `θ^{2r} · ∑_{e∈RS} I(e) ≤ (1+(q−1)θ²)^n + (q·(2θ+(q−2)θ²)+(1+(q−1)θ²))^n / q^{n−deg}`.

The first term is the diagonal `e=0` ball volume `V`; the second is the off-diagonal. -/
theorem rs_sum_jointCoverCount_mgf_le_one [Nonempty ι] (domain : ι ↪ F) (deg : ℕ) [NeZero deg]
    [Fintype (Polynomial.degreeLT F deg)] (hdeg_le : deg ≤ Fintype.card ι)
    (δ : ℝ≥0) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ ^ (2 * ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊)
        * (∑ e ∈ rsCodeFinset domain deg, (jointCoverCount δ 0 e : ℝ))
      ≤ (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2) ^ (Fintype.card ι)
        + ((Fintype.card F : ℝ) * (2 * θ + ((Fintype.card F : ℝ) - 2) * θ ^ 2)
            + (1 + ((Fintype.card F : ℝ) - 1) * θ ^ 2)) ^ (Fintype.card ι)
          / (Fintype.card F : ℝ) ^ (Fintype.card ι - deg) := by
  have h := rs_sum_jointCoverCount_mgf_le domain deg hdeg_le δ θ hθ0 hθ1
  rwa [rs_weight_zero_card, Nat.cast_one, one_mul] at h

end ArkLib.CS25
