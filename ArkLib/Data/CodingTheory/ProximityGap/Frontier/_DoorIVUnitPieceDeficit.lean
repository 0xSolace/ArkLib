/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTwoPieceAngularDeficit

/-!
# Door IV unit-piece angular-deficit specialization

`_DoorIVTwoPieceAngularDeficit` proves the exact multi-piece identity

`‖Σ zᵢ‖² = (l1Mass zs)² − 2·totalPairDeficit zs`,   `l1Mass zs = Σ ‖zᵢ‖`,

and the prize-facing reduction `‖Σ zᵢ‖² ≤ T ⟺ totalPairDeficit zs ≥ ((l1Mass zs)² − T)/2`, all in
terms of the *abstract* `l1Mass`.  But the actual door-(iv) object is the worst-frequency monomial
sum `η_b = Σ_{x∈μ_n} e_p(b·x)`, whose pieces are the **unit-modulus** phases `z_x = e_p(b·x)`
(`‖z_x‖ = 1`).  For such pieces the `L¹` mass is *exactly the number of pieces* (`l1Mass = length`),
so the abstract identity collapses to the concrete count form the prize uses.

This file records that specialization, axiom-clean:

* `l1Mass_eq_length_of_forall_norm_one` — unit pieces ⟹ `l1Mass zs = zs.length`.
* `norm_sum_sq_eq_length_sq_sub_two_totalPairDeficit_of_unit` — the exact identity
  `‖Σ zᵢ‖² = (#pieces)² − 2·totalPairDeficit` for unit pieces (so with `#pieces = n`, `‖η_b‖² =
  n² − 2·D(b)`, hence the deficit `D(b) = (n² − ‖η_b‖²)/2`).
* `norm_sum_sq_le_iff_totalPairDeficit_ge_of_unit` — the prize ceiling `‖Σ‖² ≤ T` is exactly the
  total-pairwise-angular-deficit lower bound `≥ ((#pieces)² − T)/2` for unit pieces.  With `#pieces=n`
  and the prize ceiling `T = C²·n·log(p/n)`, this is `D(b) ≥ n²/2·(1 − C²·log(p/n)/n) = n²/2·(1−o(1))`:
  the prize ⟺ the worst-b coset's pairwise angular deficit reaches `(1−o(1))·n²/2`.
* `totalPairDeficit_le_length_sq_div_two_of_unit` — the matching trivial ceiling (`D ≤ (#pieces)²/2`).
* `norm_sum_sq_lt_length_sq_iff_totalPairDeficit_pos_of_unit` — any strict coherence slack `‖Σ‖²<n²`
  for unit pieces is exactly a strictly positive total pairwise angular deficit.

These are EXACT specializations of already-kernel-checked identities; they introduce no estimate.
Constraint/identity lemmas only: no CORE / cancellation / completion / capacity / moment claim.
The open prize burden (forcing `D(b) ≥ (1−o(1))n²/2` at the worst `b` over the THIN monomial phase set
without a moment or completion route) is untouched.
-/

namespace ProximityGap.Frontier.DoorIVUnitPieceDeficit

open ProximityGap.Frontier.DoorIVTwoPieceAngularDeficit

/-- For a list of unit-modulus complex pieces, the `L¹` mass equals the number of pieces. -/
theorem l1Mass_eq_length_of_forall_norm_one {zs : List ℂ} (h : ∀ z ∈ zs, ‖z‖ = 1) :
    l1Mass zs = zs.length := by
  unfold l1Mass
  induction zs with
  | nil => simp
  | cons z zs ih =>
      have hz : ‖z‖ = 1 := h z (by simp)
      have htail : ∀ w ∈ zs, ‖w‖ = 1 := fun w hw => h w (by simp [hw])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hz, ih htail]
      push_cast
      ring

/-- Exact unit-piece angular-deficit identity: `‖Σ zᵢ‖² = (#pieces)² − 2·totalPairDeficit`.
With `#pieces = n` this is `‖η_b‖² = n² − 2·D(b)`, i.e. the worst-frequency coset deficit is exactly
`D(b) = (n² − ‖η_b‖²)/2`. -/
theorem norm_sum_sq_eq_length_sq_sub_two_totalPairDeficit_of_unit {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ^ 2 = (zs.length : ℝ) ^ 2 - 2 * totalPairDeficit zs := by
  have hid := norm_sum_sq_eq_l1Mass_sq_sub_two_totalPairDeficit zs
  rw [l1Mass_eq_length_of_forall_norm_one h] at hid
  exact hid

/-- The prize-facing reduction for unit pieces: the squared-coherence ceiling `‖Σ zᵢ‖² ≤ T` is
exactly the total-pairwise-angular-deficit lower bound `totalPairDeficit ≥ ((#pieces)² − T)/2`.
For the worst monomial frequency this says: the prize `‖η_b‖² ≤ C²·n·log(p/n)` ⟺ the worst-b coset's
accumulated pairwise angular deficit reaches `(n² − C²·n·log(p/n))/2 = (n²/2)(1 − o(1))`. -/
theorem norm_sum_sq_le_iff_totalPairDeficit_ge_of_unit {zs : List ℂ} (T : ℝ)
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ^ 2 ≤ T ↔ ((zs.length : ℝ) ^ 2 - T) / 2 ≤ totalPairDeficit zs := by
  have hiff := norm_sum_sq_le_iff_totalPairDeficit_ge zs T
  rw [l1Mass_eq_length_of_forall_norm_one h] at hiff
  exact hiff

/-- Matching trivial ceiling for unit pieces: `totalPairDeficit ≤ (#pieces)²/2`.  With `#pieces=n`
this caps the deficit at `n²/2`, so the prize target `(n²/2)(1−o(1))` sits just below the ceiling. -/
theorem totalPairDeficit_le_length_sq_div_two_of_unit {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    totalPairDeficit zs ≤ (zs.length : ℝ) ^ 2 / 2 := by
  have hle := totalPairDeficit_le_l1Mass_sq_div_two zs
  rw [l1Mass_eq_length_of_forall_norm_one h] at hle
  exact hle

/-- Strict coherence slack for unit pieces is exactly positive total pairwise angular deficit:
`‖Σ zᵢ‖² < (#pieces)² ⟺ 0 < totalPairDeficit`.  So a strict drop below the fully-coherent value `n²`
on the worst monomial sum is exactly genuine accumulated phase misalignment. -/
theorem norm_sum_sq_lt_length_sq_iff_totalPairDeficit_pos_of_unit {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ^ 2 < (zs.length : ℝ) ^ 2 ↔ 0 < totalPairDeficit zs := by
  have hiff := norm_sum_sq_lt_l1Mass_sq_iff_totalPairDeficit_pos zs
  rw [l1Mass_eq_length_of_forall_norm_one h] at hiff
  exact hiff

/-- Saturation for unit pieces: full coherence `‖Σ zᵢ‖² = (#pieces)²` ⟺ zero total deficit.
The worst monomial sum attains the trivial top `‖η_b‖ = n` exactly when no pairwise misalignment is
present (all phases aligned). -/
theorem norm_sum_sq_eq_length_sq_iff_totalPairDeficit_eq_zero_of_unit {zs : List ℂ}
    (h : ∀ z ∈ zs, ‖z‖ = 1) :
    ‖zs.sum‖ ^ 2 = (zs.length : ℝ) ^ 2 ↔ totalPairDeficit zs = 0 := by
  have hiff := norm_sum_sq_eq_l1Mass_sq_iff_totalPairDeficit_eq_zero zs
  rw [l1Mass_eq_length_of_forall_norm_one h] at hiff
  exact hiff

end ProximityGap.Frontier.DoorIVUnitPieceDeficit

#print axioms
  ProximityGap.Frontier.DoorIVUnitPieceDeficit.l1Mass_eq_length_of_forall_norm_one
#print axioms
  ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_eq_length_sq_sub_two_totalPairDeficit_of_unit
#print axioms
  ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_le_iff_totalPairDeficit_ge_of_unit
#print axioms
  ProximityGap.Frontier.DoorIVUnitPieceDeficit.totalPairDeficit_le_length_sq_div_two_of_unit
#print axioms
  ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_lt_length_sq_iff_totalPairDeficit_pos_of_unit
#print axioms
  ProximityGap.Frontier.DoorIVUnitPieceDeficit.norm_sum_sq_eq_length_sq_iff_totalPairDeficit_eq_zero_of_unit
