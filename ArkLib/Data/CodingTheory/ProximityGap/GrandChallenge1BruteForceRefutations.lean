import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge1BruteForce
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal

namespace GrandChallenge1BruteForce

/-! # Formal Refutations of Naive Hypotheses

Per the brute-force sweep, we are shooting down the naive `Hyp` candidates 
proposed for bounding the Guruswami-Sudan list sizes. These candidates
are structurally flawed and easily refuted by trivial edge cases.
-/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- Hypothesis 7 asserts L.card ≤ k^2. We shoot this down by picking k=0 and L.card=1.
theorem not_Hyp7_MatrixRankBound (L : Finset (ι → F)) (hL : 0 < L.card) :
    ¬ Hyp7_MatrixRankBound L 0 := by
  intro h
  unfold Hyp7_MatrixRankBound at h
  have h0 : 0 ^ 2 = 0 := rfl
  linarith

-- Hypothesis 8 asserts L.card ≤ |F|. We shoot this down by taking a large list.
theorem not_Hyp8_AlgebraicIndependence (L : Finset (ι → F)) (hL : Fintype.card F < L.card) :
    ¬ Hyp8_AlgebraicIndependence L := by
  intro h
  unfold Hyp8_AlgebraicIndependence at h
  linarith

-- Hypothesis 9 asserts L.card ≤ natDegreeX H. Shot down by H = Y (degX = 0) and L.card > 0.
theorem not_Hyp9_MultiplicityIntersection (L : Finset (ι → F)) (H : F[X][Y]) 
    (hL : 0 < L.card) (hX : Bivariate.natDegreeX H = 0) :
    ¬ Hyp9_MultiplicityIntersection H L := by
  intro h
  unfold Hyp9_MultiplicityIntersection at h
  linarith

-- Hypothesis 10 asserts L.card ≤ natDegreeY H. Shot down by H = X (degY = 0) and L.card > 0.
theorem not_Hyp10_AffineVarietyDimension (L : Finset (ι → F)) (H : F[X][Y]) 
    (hL : 0 < L.card) (hY : Bivariate.natDegreeY H = 0) :
    ¬ Hyp10_AffineVarietyDimension H L := by
  intro h
  unfold Hyp10_AffineVarietyDimension at h
  linarith

end GrandChallenge1BruteForce
