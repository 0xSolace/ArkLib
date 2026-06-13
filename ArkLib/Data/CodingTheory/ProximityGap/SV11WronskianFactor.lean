/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SV11GeneratorFamily
import ArkLib.Data.CodingTheory.ProximityGap.WronskianGeneral

/-!
# The SV11 Wronskian's common `(X−c)`-power factor (#389) — the degree-reduction first step

`sv11_combination_natDegree_le` shows the imposed-combination auxiliary keeps degree `≈ tB`, which
makes the Stepanov bound trivial. The sharp `O(t^{2/3})` route instead uses the **Wronskian** of the
generators as the auxiliary and *divides out* the `t`-power common factors, dropping the effective
degree. This file proves the first, common-factor, step of that reduction.

For SV11 generators `g_j = X^{a_j}(X−c)^{t·b_j}` all with `b_j ≥ 1`, every `g_j` is divisible by
`(X−c)^t`, so by the in-tree `pow_dvd_wronskianDet` (with `l ≤ t+1`) the Wronskian is divisible by
`(X−c)^{l·t − C(l,2)}` — a factor of degree `≈ lt` that divides out, beginning the cancellation of the
`t`-power degree. The remaining (refined, per-`b_j`) cancellation down to effective degree `~lD` is the
research-level step that completes the sharp bound; this is its proven foundation.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Finset
open ArkLib.ProximityGap.Wronskian

namespace ProximityGap.BinomialDet

variable {F : Type*} [Field F]

/-- **The SV11 Wronskian's `(X−c)`-power factor.** For SV11 generators `g_j = X^{a_j}(X−c)^{t·b_j}` all
with `b_j ≥ 1` and `l ≤ t+1`, the Wronskian is divisible by `(X−c)^{l·t − C(l,2)}`. -/
theorem sv11_wronskian_pow_dvd {l : ℕ} (c : F) (t : ℕ) (idx : Fin l → ℕ × ℕ)
    (hl : l ≤ t + 1) (hb : ∀ j, 1 ≤ (idx j).2) :
    (X - C c) ^ (l * t - l.choose 2) ∣
      ArkLib.ProximityGap.Wronskian.wronskianDet (fun j => sv11Gen c t (idx j)) := by
  apply ArkLib.ProximityGap.Wronskian.pow_dvd_wronskianDet hl
  intro j
  unfold sv11Gen
  refine dvd_trans (pow_dvd_pow (X - C c) ?_) (dvd_mul_left _ _)
  calc t = t * 1 := (mul_one t).symm
    _ ≤ t * (idx j).2 := Nat.mul_le_mul_left t (hb j)

/-- **Non-uniform Wronskian divisibility.** If each `f_j` is divisible by `(X−α)^{kf j}` with every
`kf j ≥ l−1` (so the derivative orders `< l` never exhaust the vanishing), the Wronskian is divisible
by `(X−α)^{(∑ kf j) − C(l,2)}`. Non-uniform generalization of `pow_dvd_wronskianDet`. -/
theorem pow_dvd_wronskianDet_nonuniform {l : ℕ} {α : F} {kf : Fin l → ℕ} {f : Fin l → F[X]}
    (hk : ∀ j, l - 1 ≤ kf j) (hdvd : ∀ j, (X - C α) ^ (kf j) ∣ f j) :
    (X - C α) ^ ((∑ j, kf j) - l.choose 2) ∣ wronskianDet f := by
  rw [wronskianDet, Matrix.det_apply]
  refine Finset.dvd_sum (fun σ _ => ?_)
  have hle : ∀ i, (σ i : ℕ) ≤ kf i := fun i =>
    le_trans (by have := (σ i).isLt; omega) (hk i)
  have hexp : (∑ j, kf j) - l.choose 2 = ∑ i : Fin l, (kf i - (σ i : ℕ)) := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun i _ => hle i), sum_perm_eq_choose_two σ]
  have hprod : (X - C α) ^ ((∑ j, kf j) - l.choose 2) ∣ ∏ i, wronskianMatrix f (σ i) i := by
    rw [hexp]
    calc (X - C α) ^ (∑ i : Fin l, (kf i - (σ i : ℕ)))
        = ∏ i : Fin l, (X - C α) ^ (kf i - (σ i : ℕ)) :=
          (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => kf i - (σ i : ℕ)) (X - C α)).symm
      _ ∣ ∏ i : Fin l, wronskianMatrix f (σ i) i :=
          Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => by
            rw [wronskianMatrix_apply]; exact pow_sub_dvd_iterate_derivative (hdvd i) (σ i))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with sg | sg
  · rw [sg, one_smul]; exact hprod
  · rw [sg, Units.neg_smul, one_smul]; exact dvd_neg.mpr hprod

/-- **The full `t`-power cancellation for the SV11 Wronskian.** For generators `g_j = X^{a_j}(X−c)^{t·b_j}`
with every `b_j ≥ 1` and `l−1 ≤ t`, the Wronskian is divisible by `(X−c)^{t·(∑ b_j) − C(l,2)}` — the
*entire* `t`-power. Dividing it out leaves effective degree `≤ ∑ a_j ≈ lD` (no `t`): the degree-reduction
that turns the trivial imposed bound into the sharp `O(t^{2/3})` Wronskian-as-auxiliary bound. -/
theorem sv11_wronskian_full_pow_dvd {l : ℕ} (c : F) (t : ℕ) (idx : Fin l → ℕ × ℕ)
    (hlt : l - 1 ≤ t) (hb : ∀ j, 1 ≤ (idx j).2) :
    (X - C c) ^ (t * (∑ j, (idx j).2) - l.choose 2) ∣
      wronskianDet (fun j => sv11Gen c t (idx j)) := by
  have heq : t * (∑ j, (idx j).2) = ∑ j, t * (idx j).2 := by rw [Finset.mul_sum]
  rw [heq]
  refine pow_dvd_wronskianDet_nonuniform (kf := fun j => t * (idx j).2) (fun j => ?_) (fun j => ?_)
  · calc l - 1 ≤ t := hlt
      _ = t * 1 := (mul_one t).symm
      _ ≤ t * (idx j).2 := Nat.mul_le_mul_left t (hb j)
  · unfold sv11Gen
    exact dvd_mul_left _ _

end ProximityGap.BinomialDet

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.BinomialDet.sv11_wronskian_pow_dvd
#print axioms ProximityGap.BinomialDet.pow_dvd_wronskianDet_nonuniform
#print axioms ProximityGap.BinomialDet.sv11_wronskian_full_pow_dvd
