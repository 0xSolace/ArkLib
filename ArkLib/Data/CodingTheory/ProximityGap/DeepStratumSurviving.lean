/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepStratumRankUnconditional
import ArkLib.Data.CodingTheory.ProximityGap.DeepStratumMovingDirection

/-!
# Deep-stratum rank `≥ m+1`, fully unconditional (#389, route 2)

`DeepStratumRankUnconditional.lean` reduced the deep-pair rank-`(m+1)` bound to a
single per-pair residual `SurvivingTPrimeCoord` (one surviving `T'`-band
coordinate making the `(m+1)`-element family «`m` `T`-band ∧ that coordinate»
jointly surjective).  `DeepStratumMovingDirection.lean` proved the *geometric*
crux `exists_surviving_band_coord`: the moving direction
`Z_T = ∏_{i∈T}(X − dom i)` has a `T'`-band coordinate `d` with
`coeff(k+1+d)(coreInterp_{T'} Z_T) ≠ 0` while its entire `T`-band is zero.

This file closes the loop: it upgrades that *existence of a nonzero coordinate*
to the full **surjectivity** of the `(m+1)`-family (the actual content of
`SurvivingTPrimeCoord`) by the moving-direction scaling argument — add the right
multiple `λ·Z_T` to a bare `T`-band realizer; `Z_T` vanishes on `T` so the
`T`-band is untouched, and the surviving `T'`-coordinate slides linearly through
all of `F`.  Hence:

* `survivingTPrimeCoord_of_deep` — **`SurvivingTPrimeCoord` holds for every
  distinct deep pair, unconditionally** (`M ≥ k+m+2`).
* `deep_pair_rank_ge_m_succ_uncond` — therefore the pair-coherence kernel of
  every distinct deep pair obeys `#kernel · q^(m+1) ≤ q^M`, i.e. **rank `≥ m+1`
  on the whole deep stratum with no hypothesis whatsoever**.  The deep stratum
  carries no diagonal-level (rank-`m`) locus: the value-collision fiber is
  strictly thinner than the per-core fiber at every distinct deep pair.

This removes the last residual from the route-2 rank bound.  (It does *not*
close the sub-Johnson supply wall — the supply is an upper bound on bad scalars;
this is a lower bound on the second-moment rank.)

Issue #389.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.DeepStratumUncond

open ProximityGap ProximityGap.Ownership ProximityGap.PairRank ProximityGap.FarPairRank
  ProximityGap.DegeneracyRank ProximityGap.DeepStratumMoving

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## Additivity / scaling of `coreInterp` (interpolate is a `LinearMap`) -/

theorem coreInterp_add (dom : Fin n ↪ F) (T : Finset (Fin n)) (P R : F[X]) :
    coreInterp dom T (P + R) = coreInterp dom T P + coreInterp dom T R := by
  rw [coreInterp, coreInterp, coreInterp]
  have hvals : (fun i => (P + R).eval (dom i))
      = (fun i => P.eval (dom i)) + (fun i => R.eval (dom i)) := by
    funext i; simp [eval_add]
  rw [hvals, map_add]

theorem coreInterp_smul (dom : Fin n ↪ F) (T : Finset (Fin n)) (lam : F) (P : F[X]) :
    coreInterp dom T (lam • P) = lam • coreInterp dom T P := by
  rw [coreInterp, coreInterp]
  have hvals : (fun i => (lam • P).eval (dom i))
      = lam • (fun i => P.eval (dom i)) := by
    funext i; simp [eval_smul]
  rw [hvals, map_smul]

/-! ## The surviving coordinate gives full surjectivity (UNCONDITIONAL) -/

open Classical in
/-- **`SurvivingTPrimeCoord` holds for every distinct deep pair, unconditionally.**
Upgrades `exists_surviving_band_coord` (existence of a nonzero `T'`-band
coordinate of the moving direction) to the joint surjectivity of the
`(m+1)`-family. -/
theorem survivingTPrimeCoord_of_deep (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hne : T ≠ T') (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ} (hM : k + m + 2 ≤ M) :
    SurvivingTPrimeCoord dom k m T T' M := by
  classical
  -- a point of T' ∖ T
  obtain ⟨y, hyT', hyT⟩ : ∃ y, y ∈ T' ∧ y ∉ T := by
    by_contra h; push_neg at h
    exact hne (Finset.eq_of_subset_of_card_le (fun z hz => h z hz) (by rw [hT, hT'])).symm
  -- the moving direction and its surviving coordinate
  set δ : F[X] := vanishPoly dom T with hδ
  set r : F[X] := coreInterp dom T' δ with hr
  have hrmov : r = movingInterp dom T T' := rfl
  obtain ⟨d, hd⟩ := exists_surviving_band_coord dom T T' hT' hdeep hyT' hyT
  have hrc : r.coeff (k + 1 + (d : ℕ)) ≠ 0 := by rw [hrmov]; exact hd
  -- coreInterp of the moving direction through T is zero (all T-band coeffs)
  have hcoreTδ : coreInterp dom T δ = 0 := by
    rw [hδ, coreInterp]; exact interp_T_vanishPoly_eq_zero dom T
  -- δ degree < M
  have hδMdeg : δ.degree < (M : WithBot ℕ) := by
    have hδ0 : δ ≠ 0 := by
      intro h
      exact vanishPoly_eval_ne_zero dom T hyT (by rw [← hδ, h]; simp)
    rw [Polynomial.degree_eq_natDegree hδ0, hδ, vanishPoly_natDegree, hT]
    exact_mod_cast (by omega : k + m + 1 < M)
  -- build the realizer for each target
  refine ⟨d, fun t => ?_⟩
  obtain ⟨c₀, hc₀⟩ := tband_surjective dom hT (by omega : k + m + 1 ≤ M)
    (fun j => t (Sum.inl j))
  set Q₀ : F[X] := genPoly c₀ with hQ₀
  set s₀ : F := (coreInterp dom T' Q₀).coeff (k + 1 + (d : ℕ)) with hs₀
  set lam : F := (t (Sum.inr ()) - s₀) / r.coeff (k + 1 + (d : ℕ)) with hlam
  have hlamδdeg : (lam • δ).degree < (M : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_smul_le _ _) hδMdeg
  have hsumdeg : (Q₀ + lam • δ).degree < (M : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (genPoly_degree_lt c₀) hlamδdeg)
  set c : Fin M → F := fun i => (Q₀ + lam • δ).coeff (i : ℕ) with hc
  have hgenc : genPoly c = Q₀ + lam • δ := genPoly_coeff_eq hsumdeg
  refine ⟨c, fun j => ?_, ?_⟩
  · rw [hgenc, coreInterp_add, coreInterp_smul, hcoreTδ, smul_zero, add_zero]
    exact hc₀ j
  · rw [hgenc, coreInterp_add, coreInterp_smul, Polynomial.coeff_add,
      Polynomial.coeff_smul, ← hr, ← hs₀, smul_eq_mul, hlam,
      div_mul_cancel₀ _ hrc, add_sub_cancel]

/-! ## Unconditional rank `≥ m+1` for every deep pair -/

open Classical in
/-- **UNCONDITIONAL rank `≥ m+1` on the whole deep stratum.**  Every distinct
deep pair's pair-coherence (= two-band) kernel obeys `#kernel · q^(m+1) ≤ q^M`.
No degeneracy hypothesis: the value-collision fiber is strictly thinner than the
per-core fiber everywhere on the deep stratum. -/
theorem deep_pair_rank_ge_m_succ_uncond (dom : Fin n ↪ F) {k m : ℕ}
    {T T' : Finset (Fin n)} (hT : T.card = k + m + 1) (hT' : T'.card = k + m + 1)
    (hne : T ≠ T') (hdeep : k + 1 ≤ (T ∩ T').card) {M : ℕ} (hM : k + m + 2 ≤ M) :
    (Finset.univ.filter (fun c : Fin M → F =>
        IsCoherent dom k m T (genPoly c) ∧ IsCoherent dom k m T' (genPoly c)
          ∧ (coreInterp dom T (genPoly c)).coeff k
              = (coreInterp dom T' (genPoly c)).coeff k)).card
      * (Fintype.card F) ^ (m + 1) ≤ (Fintype.card F) ^ M :=
  deep_pair_rank_ge_m_succ dom hT hT' hdeep
    (survivingTPrimeCoord_of_deep dom hT hT' hne hdeep hM)

end ProximityGap.DeepStratumUncond

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.DeepStratumUncond.survivingTPrimeCoord_of_deep
#print axioms ProximityGap.DeepStratumUncond.deep_pair_rank_ge_m_succ_uncond
