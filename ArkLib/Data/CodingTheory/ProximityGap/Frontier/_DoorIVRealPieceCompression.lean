/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealPieceCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVRealSignMassSlack

/-!
# Door IV real-piece compression: finer real refinements add only sign mass

The multiplicative-coset refinement probes for the localized door-(iv) object found that, at the
adversarial frequency, many finer piece decompositions remain collinear on the real axis.  This file
records the exact bookkeeping consequence: once a real refinement is compressed to total positive
mass `P` and total negative mass `N`, its normalized list coherence is literally the two-mass
coherence `|P-N|/(P+N)` from `_DoorIVRealSignMassSlack`.

Therefore a finer real/collinear refinement contributes no new angular degree of freedom.  Any
claimed `rho <= theta` theorem for such pieces is exactly equivalent to proving a lower bound on the
minority sign mass.  This is a Door-IV constraint lemma only: no Gauss-period cancellation, no CORE
bound, no moment/completion route.
-/

namespace ProximityGap.Frontier.DoorIVRealPieceCompression

open ProximityGap.Frontier.DoorIVRealPieceCoherence
open ProximityGap.Frontier.DoorIVRealSignMassSlack

/-- If a real piece list compresses to positive mass `P` and negative mass `N`, then its list
coherence is exactly the sign-mass coherence.  The hypotheses are intentionally just the two
compression identities, so future probes/formalizations can plug in any concrete positive/negative
partition without reopening triangle-inequality arguments. -/
theorem realPieceCoherence_eq_signMassCoherence_of_compression {xs : List ℝ} {P N : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) :
    realPieceCoherence xs = signMassCoherence P N := by
  unfold realPieceCoherence signMassCoherence
  rw [hsum, habssum]

/-- Threshold form of the compression lemma.  For any real/collinear refinement that has been
compressed to sign masses `P,N`, a target `theta` is equivalent to the minority-sign-mass lower
bound `(1-theta)(P+N)/2 <= min P N`.  Thus the only possible saving in a real refinement is a
balanced sign split, not extra angular anti-concentration. -/
theorem realPieceCoherence_le_iff_minority_mass_ge_of_compression {xs : List ℝ} {P N theta : ℝ}
    (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N) (hden : 0 < P + N) :
    realPieceCoherence xs ≤ theta ↔ (1 - theta) * (P + N) / 2 ≤ min P N := by
  rw [realPieceCoherence_eq_signMassCoherence_of_compression (xs := xs) (P := P) (N := N)
      hsum habssum]
  exact signMassCoherence_le_iff_minority_mass_ge (P := P) (N := N) (theta := theta) hden

/-- Operational obstruction: if the minority sign mass is below an `eps/2` fraction of the total
compressed mass, then the compressed real refinement cannot prove a `1-eps` coherence drop. -/
theorem not_realPieceCoherence_le_one_sub_of_minority_mass_lt_of_compression {xs : List ℝ}
    {P N eps : ℝ} (hsum : xs.sum = P - N) (habssum : (xs.map abs).sum = P + N)
    (hden : 0 < P + N) (hminor : min P N < eps * (P + N) / 2) :
    ¬ realPieceCoherence xs ≤ 1 - eps := by
  rw [realPieceCoherence_eq_signMassCoherence_of_compression (xs := xs) (P := P) (N := N)
      hsum habssum]
  exact not_coherence_le_one_sub_of_minority_mass_lt (P := P) (N := N) (eps := eps) hden hminor

end ProximityGap.Frontier.DoorIVRealPieceCompression

open ProximityGap.Frontier.DoorIVRealPieceCompression

#print axioms realPieceCoherence_eq_signMassCoherence_of_compression
#print axioms realPieceCoherence_le_iff_minority_mass_ge_of_compression
#print axioms not_realPieceCoherence_le_one_sub_of_minority_mass_lt_of_compression
