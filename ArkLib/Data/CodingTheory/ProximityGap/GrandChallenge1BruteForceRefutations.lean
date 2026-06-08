import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenge1BruteForce

open Polynomial Polynomial.Bivariate ProximityGap MCAGS Code NNReal
open GrandChallenge1BruteForce

namespace GrandChallenge1BruteForceRefutations

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-!
# Refutation targets for naive Grand Challenge 1 hypotheses

The brute-force hypotheses are useful red-team targets, but several attempted counterexample
proofs were left as `sorry` stubs and the file also carried conflict markers. This file keeps the
refutation goals as named `Prop`s until each counterexample is formalized in a separate proof file.
-/

def refute_Hyp1 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp1_ResultantRankBound H L

def refute_Hyp2 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp2_SmoothCurveIntersection H L

def refute_Hyp3 (domain : ι ↪ F) : Prop :=
  ¬ ∀ L : Finset (ι → F), Hyp3_PuncturedSupportSparsity domain L

def refute_Hyp4 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ u : ι → F, Hyp4_DerivativeMultiplicityCollapse H u

def refute_Hyp5 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp5_SchwartzZippelDensity H L

def refute_Hyp6 : Prop :=
  ¬ ∀ L : Finset (ι → F), Hyp6_SubSpaceEvasion L

def refute_Hyp7 : Prop :=
  ¬ ∀ L : Finset (ι → F), ∀ k : ℕ, Hyp7_MatrixRankBound L k

def refute_Hyp8 : Prop :=
  ¬ ∀ L : Finset (ι → F), Hyp8_AlgebraicIndependence L

def refute_Hyp9 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp9_MultiplicityIntersection H L

def refute_Hyp10 : Prop :=
  ¬ ∀ H : F[X][Y], ∀ L : Finset (ι → F), Hyp10_AffineVarietyDimension H L

end GrandChallenge1BruteForceRefutations
