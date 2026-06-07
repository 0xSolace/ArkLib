/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengesLattice
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdJohnsonSq

/-!
# Johnson-capacity route for `OrdinaryRSCapacityAtPrizeRates` (scratch)

The lower-side hypothesis `OrdinaryRSCapacityAtPrizeRates domain τ ℓ` (defined in
`GrandChallengesLattice.lean`) asks, for each ABF26 prize rate `r ∈ {1/2,1/4,1/8,1/16}`,
for an *upper* bound on the maximised list size of the ordinary Reed-Solomon code at the
proposed predecessor lattice radius:

  `Λ(RS_{k_r}, (τ r).val / n) ≤ ℓ r`.

The proven Elias volume bound `linear_lambda_ge_elias_volume_eli57` is a *lower* bound on
`Λ`; it lives on the **obstruction** side of this frontier (see
`not_ordinaryRSCapacityAtPrizeRates_of_elias_volume_gt`) and cannot establish the cap.

The cap is supplied instead by the **Johnson** capacity machinery: the proven
`ProximityGap.Lambda_le_of_johnson_sq` (ABF26 Theorem 3.2, optimal-`β` squared form) gives
exactly `Λ(C, j/n) ≤ ℓ` from a concrete, `norm_num`-checkable polynomial inequality in
`(n, q, ℓ, j, minDist C)`.  This file packages that reduction at the four prize rates.

The remaining payload after this reduction is the per-rate squared Johnson inequality plus the
two standard RS facts `minDist = n - k + 1` and `finrank = k`.  The squared Johnson inequality
holding at a given `(τ r, ℓ r)` is the genuine capacity content; whenever the proposed radius
sits inside the Johnson list-decoding region of the rate-`r` RS code, the inequality is a finite
numeric check.  This is the provable lower side of the Lambda-Elias frontier; the genuinely open
research boundary is only the strip between the Johnson radius and the full list-decoding
capacity radius (the Johnson→capacity gap), which is not needed for the cap when `(τ r, ℓ r)`
lands in the Johnson region.
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable
open ProximityGap.GrandChallengesLattice

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **Per-rate Johnson cap for the ordinary-RS prize capacity, abstract `minDist` form.**

For each prize rate, the proven optimal-`β` squared Johnson bound
(`Lambda_le_of_johnson_sq`) gives the maximised list-size cap
`Λ(RS_{k_r}, (τ r).val / n) ≤ ℓ r` directly from the squared Johnson polynomial inequality
`hsq`.  This is exactly `OrdinaryRSCapacityAtPrizeRates`. -/
theorem ordinaryRSCapacityAtPrizeRates_of_johnson_sq
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    Code.minDist
                      (ReedSolomon.code domain
                        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ :
                          Set (ι → F)) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  intro r
  have hbase :
      Lambda
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        ((((((τ r).val : ℕ) : ℝ≥0)) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) ≤
          (ℓ r : ℕ∞) :=
    Lambda_le_of_johnson_sq
      (C := (ReedSolomon.code domain
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)))
      (j := (τ r).val) (ℓ := ℓ r) hq1 (hP r) (hsq r)
  -- `OrdinaryRSCapacityAtPrizeRates` uses the same radius up to the trivial `((τ r).val : ℕ)`
  -- coercion identity, so the goal matches `hbase` definitionally.
  exact hbase

/-- **Per-rate Johnson cap with the RS distance specialised.**

Same as `ordinaryRSCapacityAtPrizeRates_of_johnson_sq`, but the squared Johnson inequality is
phrased with the closed-form Reed-Solomon minimum distance `n - k + 1` already substituted,
supplied via the standard RS facts behind `hminDist`. -/
theorem ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDistance
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hminDist : ∀ r : Fin 4,
      Code.minDist
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) =
        Fintype.card ι - ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1)
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  refine ordinaryRSCapacityAtPrizeRates_of_johnson_sq domain τ ℓ hq1 hP ?_
  intro r
  simpa [hminDist r] using hsq r

/-- **Per-rate Johnson cap from RS degree side conditions.**

The numerics-facing form: from `0 < k_r` and `k_r ≤ n`, the standard RS fact
`minDist = n - k + 1` (`ReedSolomon.minDist_eq'`) is discharged automatically, leaving only the
squared Johnson arithmetic certificate at the closed-form distance.  This mirrors
`listPrizeLatticeResolved_of_johnson_sq_rsDegreeLe_and_elias_next`, but lands directly on the
capacity predicate `OrdinaryRSCapacityAtPrizeRates`. -/
theorem ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDegreeLe
    (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hq1 : 1 < Fintype.card F)
    (hdeg_pos : ∀ r : Fin 4,
      0 < ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (hdeg_le : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hsq : ∀ r : Fin 4,
      ((ℓ r : ℝ) + 1)
          * ((((Fintype.card ι - (τ r).val : ℕ) : ℝ)) -
              (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)) ^ 2
        > ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)))
          * ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))
              + (ℓ r : ℝ)
                * (((Fintype.card ι -
                    (Fintype.card ι -
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ℕ) : ℝ) -
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))) :
    OrdinaryRSCapacityAtPrizeRates domain τ ℓ := by
  refine ordinaryRSCapacityAtPrizeRates_of_johnson_sq_rsDistance
    domain τ ℓ hq1 hP ?_ hsq
  intro r
  haveI : NeZero ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ := ⟨(hdeg_pos r).ne'⟩
  exact ReedSolomon.minDist_eq' (α := domain) (hdeg_le r)

end ProximityGap
