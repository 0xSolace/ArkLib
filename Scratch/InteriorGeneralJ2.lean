import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeInteriorGeneral

namespace ProximityGap

namespace GrandChallengesLattice

open Polynomial Matrix
open scoped NNReal ENNReal BigOperators
open ReedSolomon Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Scratch version of the J2 lower bound with the actual spike hypothesis `k + 3 <= n`. -/
theorem epsMCA_interiorJ2_ge_sharp
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 3 ≤ Fintype.card F) :
    (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F))
        (mcaLatticePoint (Fintype.card ι)
          (⟨2, by
            have hn : 0 < Fintype.card ι := Fintype.card_pos
            omega⟩ : Fin (Fintype.card ι + 1))) := by
  classical
  set n := Fintype.card ι with hndef
  have hn3 : 3 ≤ n := by omega
  have ht_n : 3 + k ≤ n := by omega
  have hδ : ((1 - mcaLatticePoint n (⟨2, by omega⟩ : Fin (n + 1))) * n : ℝ≥0)
      ≤ ((n - 3 + 1 : ℕ) : ℝ≥0) :=
    spike_three_size_at_interiorJ2 (n := n) hn3
  have hspike := epsMCA_ge_spike domain k 3
    (mcaLatticePoint n (⟨2, by omega⟩ : Fin (n + 1))) ht_n hq hδ
  simpa using hspike

set_option maxHeartbeats 800000 in
/-- Scratch version of the strict-below-J2 threshold consequence under `k + 3 <= n`. -/
theorem mcaThreshold_lt_two_of_interiorJ2_gt_sharp
    (domain : ι ↪ F) {k : ℕ} (hk : k + 3 ≤ Fintype.card ι) (hq : 3 ≤ Fintype.card F)
    {ε_star : ℝ≥0}
    (hbad : (ε_star : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
      have hn : 0 < Fintype.card ι := Fintype.card_pos
      omega⟩
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne < j2 := by
  let C : Set (ι → F) := ReedSolomon.code domain k
  let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    omega⟩
  show mcaThreshold C ε_star hne < j2
  by_contra hnot
  have hj2_le : j2 ≤ mcaThreshold C ε_star hne := not_lt.mp hnot
  have hsat_threshold : mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
    mcaThreshold_spec C ε_star hne
  have hsat_j2 : mcaSatisfies C ε_star j2 :=
    mcaSatisfies_downward_closed C ε_star hj2_le hsat_threshold
  have hge : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j2) :=
    epsMCA_interiorJ2_ge_sharp domain hk hq
  have hchain : (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ (ε_star : ℝ≥0∞) :=
    le_trans hge hsat_j2
  exact (not_le_of_gt hbad) hchain

/-- Scratch four-rate wrapper for the strict-below-J2 consequence. -/
theorem mcaPrizeLattice_lt_two_of_interiorJ2_gt_scratch
    (domain : ι ↪ F)
    (hk : ∀ r : Fin 4,
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 3 ≤ Fintype.card ι)
    (hq : 3 ≤ Fintype.card F)
    (hbad : (epsStar : ℝ≥0∞) < (3 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞))
    (hne : ∀ r : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
        have hn : 0 < Fintype.card ι := Fintype.card_pos
        have hkr := hk r
        omega⟩
      mcaThreshold C epsStar (hne r) < j2 := by
  intro r
  simpa using
    (mcaThreshold_lt_two_of_interiorJ2_gt_sharp
      (F := F) domain (hk r) hq hbad (hne r))

/-- Scratch formal-prize field-size wrapper for the strict-below-J2 consequence. -/
theorem mcaPrizeLattice_lt_two_of_card_ge_six_and_card_lt_three_mul_two_pow_scratch
    (domain : ι ↪ F)
    (hn : 6 ≤ Fintype.card ι)
    (hq : 3 ≤ Fintype.card F)
    (hcard_hi : Fintype.card F < (3 : ℕ) * 2 ^ (128 : ℕ))
    (hne : ∀ r : Fin 4,
      mcaThresholdExists
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∀ r : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
      let j2 : Fin (Fintype.card ι + 1) := ⟨2, by
        omega⟩
      mcaThreshold C epsStar (hne r) < j2 :=
  mcaPrizeLattice_lt_two_of_interiorJ2_gt_scratch domain
    (fun r => prizeRate_floor_add_three_le_of_card_ge_six r hn)
    hq
    (epsStar_lt_three_div_card_of_card_lt_three_mul_two_pow (F := F) hcard_hi)
    hne

end GrandChallengesLattice

end ProximityGap
