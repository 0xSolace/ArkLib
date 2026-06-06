/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDThresholdElias
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLattice
import ArkLib.Data.CodingTheory.ProximityGap.MCAEndpointLower
import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumErdosHeilbronn

/-!
# Faithful lattice encodings of the §1 Grand Challenges (after Finding F6)

`GrandChallengeCollapse.lean` proves that the real-valued, strict-failure encodings
`grandMCAChallenge` / `grandListDecodingChallenge` of `GrandChallenges.lean` **collapse**:
because `ε_mca C δ` and `Λ(C^⋈m, δ)` are step functions of `δ` through `⌊δ·n⌋`
(`epsMCA_eq_of_floor_eq`, `Lambda_eq_of_floor_eq`), no maximal *real* threshold `δ* < 1` can
satisfy a strict-failure-above clause, so the encodings degenerate to radius-one statements
and `listDecodingPrize` is provably false as encoded.

The paper [ABF26] §1 actually asks to **determine the largest *lattice* threshold**
`δ* ∈ {0, 1/n, …, 1}`: relative Hamming distances live on the `1/n`-lattice, so the only
meaningful thresholds are the lattice points `j/n` for `j : Fin (n+1)`, where
`n := |ι|`. On this lattice the maximal threshold is a *well-defined finite quantity*
whenever it exists at all — a finite, nonempty, (by monotonicity) downward-closed subset of
`Fin (n+1)` has a maximum — and **determining its value is the open $1M problem**; the
one-sided witnesses of `GrandChallenges.lean` *bound* it.

This file builds that faithful encoding:

* `mcaLatticePoint n j := j/n : ℝ≥0` — the lattice radii.
* `mcaSatisfies C ε* j` (a `DecidablePred`) — `ε_mca(C, j/n) ≤ ε*`; downward closed in `j`
  by `epsMCA_mono` (`mcaSatisfies_downward_closed`).
* `mcaThreshold C ε* hne : Fin (n+1)` — the lattice threshold, `Finset.max'` of the
  satisfying set under a nonemptiness hypothesis `hne`
  (the paper's "`|F|` sufficiently large so that `δ*` exists").
* `mcaThreshold_spec` / `mcaThreshold_unique` — existence and uniqueness: the threshold
  satisfies the bound and is the **unique greatest** lattice point that does.
* `mcaThresholdLattice_bracketed` — a lattice lower witness and a lattice upper witness
  bracket `mcaThreshold`, mirroring `mca_threshold_bracketed`.
* the list-decoding analogues `listThreshold`, `listThreshold_spec`, … ,
  `listThresholdLattice_bracketed`.

Nothing here resolves the prize: it makes the prize *quantity* `mcaThreshold` / `listThreshold`
a real Lean object that the witnesses can be proved to bracket, replacing the collapse-broken
existence predicate.

## Relationship to `GrandChallengeLattice.lean` (singular)

There are two lattice encodings in this directory, and they are **complementary, not
duplicate** — both are kept and both are fully proven (axiom-clean):

* This file (`GrandChallengesLattice`, plural, namespace `ProximityGap.GrandChallengesLattice`)
  indexes the lattice by `Finset (Fin (n+1))` (`Finset.univ.filter …`) and supplies the
  step-function bridge to the real-valued witness framework
  (`MCALowerWitness`/`MCAUpperWitness`, `ListLowerWitness`/`ListUpperWitness`):
  `latticeIndexOf`, the `*_bracketed` lemmas, the `*_unique` lemmas, and the
  per-rate prize-resolution predicates. `Hab25Core.lean` consumes these objects.
* `GrandChallengeLattice.lean` (singular, namespace `ProximityGap.GrandChallenges`)
  indexes the lattice by `Finset ℕ` (`Finset.range (n+1) |>.filter …`). Its
  `listLatticeSet` / `listLatticeThreshold` are the canonical objects the downstream
  Grand-Challenge LD-threshold bracket files consume
  (`GrandChallengeLDThreshold{,Elias,JohnsonSq,HalfDist}.lean`), which rewrite by
  `GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range` and therefore
  depend on that `Finset ℕ` representation.

The two representations are structurally incompatible (`Finset ℕ` vs `Finset (Fin (n+1))`),
so neither file can be replaced by a re-export of the other without rewriting the downstream
proofs; both are retained intentionally. See the singular file's header for the full
disposition note.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.style.longFile 1700

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ProbabilityTheory

namespace GrandChallengesLattice

/-! ## Lattice radii -/

/-- The lattice radius `j/n : ℝ≥0` for `j : Fin (n+1)`. Relative Hamming distances take
values in `{0, 1/n, …, n/n = 1}`, so these are the only meaningful proximity radii. -/
noncomputable def mcaLatticePoint (n : ℕ) (j : Fin (n + 1)) : ℝ≥0 :=
  (j.val : ℝ≥0) / (n : ℝ≥0)

/-- Each lattice radius lies in `[0, 1]`. -/
theorem mcaLatticePoint_le_one (n : ℕ) (j : Fin (n + 1)) :
    mcaLatticePoint n j ≤ 1 := by
  unfold mcaLatticePoint
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast Nat.lt_succ_iff.mp j.isLt

@[simp] theorem mcaLatticePoint_top (ι : Type) [Fintype ι] [Nonempty ι] :
    mcaLatticePoint (Fintype.card ι)
      ⟨Fintype.card ι, Nat.lt_succ_self _⟩ = 1 := by
  unfold mcaLatticePoint
  have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact div_self hn

/-- Lattice radii are monotone in the index. -/
theorem mcaLatticePoint_mono (n : ℕ) {i j : Fin (n + 1)} (h : i ≤ j) :
    mcaLatticePoint n i ≤ mcaLatticePoint n j := by
  unfold mcaLatticePoint
  gcongr
  exact_mod_cast h

/-- The floor index of a lattice radius is the index itself: `⌊(j/n)·n⌋ = j` (for `0 < n`). -/
theorem floor_mcaLatticePoint (n : ℕ) (hn : 0 < n) (j : Fin (n + 1)) :
    Nat.floor (mcaLatticePoint n j * (n : ℝ≥0)) = j.val := by
  unfold mcaLatticePoint
  have hnne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hnne]
  exact Nat.floor_natCast _

/-! ## The MCA lattice threshold

`mcaSatisfies C ε* j` says the lattice radius `j/n` keeps `ε_mca` within `ε*`. By
`epsMCA_mono` this predicate is *downward closed* in `j`, so the set of satisfying `j` is
an initial segment of `Fin (n+1)`; its maximum (when the set is nonempty) is the faithful
lattice threshold the paper asks to determine. -/

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `ε_mca(C, j/n) ≤ ε*` at the lattice radius `j/n`. Decidable so the satisfying set is a
`Finset`. -/
def mcaSatisfies (C : Set (ι → F)) (ε_star : ℝ≥0) (j : Fin (Fintype.card ι + 1)) : Prop :=
  epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j) ≤ (ε_star : ENNReal)

noncomputable instance (C : Set (ι → F)) (ε_star : ℝ≥0) :
    DecidablePred (mcaSatisfies C ε_star) := fun _ => Classical.propDecidable _

/-- **Downward closure.** If `j/n` keeps `ε_mca ≤ ε*` and `i ≤ j`, then so does `i/n`.
Direct consequence of `epsMCA_mono`. -/
theorem mcaSatisfies_downward_closed (C : Set (ι → F)) (ε_star : ℝ≥0)
    {i j : Fin (Fintype.card ι + 1)} (hij : i ≤ j) (hj : mcaSatisfies C ε_star j) :
    mcaSatisfies C ε_star i :=
  le_trans (epsMCA_mono (F := F) C (mcaLatticePoint_mono _ hij)) hj

/-- The satisfying lattice points, as a `Finset (Fin (n+1))`. -/
noncomputable def mcaSatSet (C : Set (ι → F)) (ε_star : ℝ≥0) :
    Finset (Fin (Fintype.card ι + 1)) :=
  Finset.univ.filter (mcaSatisfies C ε_star)

@[simp] theorem mem_mcaSatSet (C : Set (ι → F)) (ε_star : ℝ≥0)
    {j : Fin (Fintype.card ι + 1)} :
    j ∈ mcaSatSet C ε_star ↔ mcaSatisfies C ε_star j := by
  simp [mcaSatSet]

/-- **Existence (nonemptiness) hypothesis.** The paper's "assuming `|F|` sufficiently large
so that such a `δ*_C` exists": some lattice radius keeps `ε_mca` within `ε*`. Equivalently,
the satisfying set is nonempty. This is the *only* hypothesis the lattice encoding needs;
once it holds, the threshold is a well-defined finite quantity. -/
def mcaThresholdExists (C : Set (ι → F)) (ε_star : ℝ≥0) : Prop :=
  ∃ j : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star j

theorem mcaSatSet_nonempty_iff (C : Set (ι → F)) (ε_star : ℝ≥0) :
    (mcaSatSet C ε_star).Nonempty ↔ mcaThresholdExists C ε_star := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_mcaSatSet C ε_star).mp hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_mcaSatSet C ε_star).mpr hj⟩

/-- **The faithful MCA lattice threshold** `δ*_C = mcaThreshold / n`. Defined as the greatest
lattice index whose radius keeps `ε_mca` within `ε*`, under the existence hypothesis `hne`.
**Determining its value is the open ABF26 §1 Grand MCA Challenge** (the $1M problem); the
witnesses below merely bracket it. -/
noncomputable def mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) : Fin (Fintype.card ι + 1) :=
  (mcaSatSet C ε_star).max' ((mcaSatSet_nonempty_iff C ε_star).mpr hne)

/-- **Existence half.** The lattice threshold itself satisfies the MCA bound:
`ε_mca(C, mcaThreshold/n) ≤ ε*`. -/
theorem mcaThreshold_spec (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) :
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) := by
  have h := (mcaSatSet C ε_star).max'_mem ((mcaSatSet_nonempty_iff C ε_star).mpr hne)
  exact (mem_mcaSatSet C ε_star).mp h

/-- **Maximality.** Every satisfying lattice point is `≤ mcaThreshold`. -/
theorem le_mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : mcaSatisfies C ε_star j) :
    j ≤ mcaThreshold C ε_star hne :=
  (mcaSatSet C ε_star).le_max' j ((mem_mcaSatSet C ε_star).mpr hj)

/-- **Strict failure above the threshold.** Any lattice point strictly above `mcaThreshold`
fails the bound: `ε_mca(C, j/n) > ε*`. This is the lattice analogue of the (collapse-broken)
real strict-failure clause, and it holds here precisely because we are on the lattice. -/
theorem gt_mcaThreshold_exceeds (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : mcaThreshold C ε_star hne < j) :
    epsMCA (F := F) (A := F) C (mcaLatticePoint (Fintype.card ι) j) > (ε_star : ENNReal) := by
  by_contra h
  exact absurd (le_mcaThreshold C ε_star hne (not_lt.mp h)) (not_le.mpr hj)

/-- **Uniqueness.** `mcaThreshold` is the *unique* lattice index that both satisfies the
bound and is maximal among satisfying indices. Hence the lattice threshold is well-defined:
existence + uniqueness of the maximal `j`. -/
theorem mcaThreshold_unique (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (j : Fin (Fintype.card ι + 1))
    (hsat : mcaSatisfies C ε_star j)
    (hmax : ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star i → i ≤ j) :
    j = mcaThreshold C ε_star hne :=
  le_antisymm (le_mcaThreshold C ε_star hne hsat)
    (hmax _ (mcaThreshold_spec C ε_star hne))

/-! ## Bridging the witness framework to the MCA lattice threshold

A `MCALowerWitness` (a real radius `δ ≤ 1` with `ε_mca(C, δ) ≤ ε*`) lands, via the step
structure `epsMCA_eq_of_floor_eq`, on the lattice point `⌊δ·n⌋`, certifying a *lower* bound
on `mcaThreshold`. A `MCAUpperWitness` lands on `⌊δ·n⌋` and certifies an *upper* bound. These
mirror `MCALowerWitness.le_δStar` / `MCAUpperWitness.δStar_le` on the lattice. -/

open GrandChallenges

/-- The lattice index `⌊δ·n⌋` carried by a real radius `δ ≤ 1`, as a `Fin (n+1)`. -/
noncomputable def latticeIndexOf (δ : ℝ≥0) (hδ : δ ≤ 1) : Fin (Fintype.card ι + 1) :=
  ⟨Nat.floor (δ * (Fintype.card ι : ℝ≥0)),
    Nat.lt_succ_of_le (by
      have hle : δ * (Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
        calc δ * (Fintype.card ι : ℝ≥0)
            ≤ 1 * (Fintype.card ι : ℝ≥0) := by gcongr
          _ = (Fintype.card ι : ℝ≥0) := one_mul _
      calc Nat.floor (δ * (Fintype.card ι : ℝ≥0))
          ≤ Nat.floor ((Fintype.card ι : ℝ≥0)) := Nat.floor_le_floor hle
        _ = Fintype.card ι := Nat.floor_natCast _)⟩

@[simp] theorem latticeIndexOf_val (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (latticeIndexOf (ι := ι) δ hδ).val = Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := rfl

/-- `ε_mca` at a real radius equals `ε_mca` at its lattice point `⌊δ·n⌋/n` (step structure):
the radius enters only through `⌊δ·n⌋`. -/
theorem epsMCA_eq_at_latticeIndex (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    epsMCA (F := F) (A := F) C δ =
      epsMCA (F := F) (A := F) C
        (mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) δ hδ)) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  refine epsMCA_eq_of_floor_eq (F := F) C ?_
  rw [floor_mcaLatticePoint _ hn, latticeIndexOf_val]

/-- **Lower bracket.** An `MCALowerWitness` forces its lattice index `⌊δ·n⌋ ≤ mcaThreshold`:
the certified real radius rounds down to a satisfying lattice point. -/
theorem MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (w : MCALowerWitness C ε_star) :
    latticeIndexOf (ι := ι) w.δ w.le_one ≤ mcaThreshold C ε_star hne := by
  refine le_mcaThreshold C ε_star hne ?_
  unfold mcaSatisfies
  rw [← epsMCA_eq_at_latticeIndex C w.δ w.le_one]
  exact w.bound

/-- A lower MCA witness is already enough to make the faithful lattice threshold exist:
round the certified real radius down to its Hamming lattice point. -/
theorem mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (w : MCALowerWitness C ε_star) :
    mcaThresholdExists C ε_star :=
  ⟨latticeIndexOf (ι := ι) w.δ w.le_one, by
    unfold mcaSatisfies
    rw [← epsMCA_eq_at_latticeIndex C w.δ w.le_one]
    exact w.bound⟩

/-- The faithful MCA threshold obtained from a lower witness satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (w : MCALowerWitness C ε_star) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star w
    mcaSatisfies C ε_star (mcaThreshold C ε_star hne) :=
  mcaThreshold_spec C ε_star (mcaThresholdExists_of_MCALowerWitness C ε_star w)

/-- A repaired line-decoding target that yields an MCA lower witness also makes the faithful
MCA lattice threshold exist. -/
theorem mcaThresholdExists_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    mcaThresholdExists (C : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star
    (MCALowerWitness.ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

/-- The faithful MCA threshold created from a repaired line-decoding target satisfies the MCA
bound. -/
theorem mcaThreshold_spec_ofLineDecodingTarget
    (C : ModuleCode ι F F) (δ a ε_star : ℝ≥0)
    (hδ_le_one : δ ≤ 1)
    (hLD : CodingTheory.LineDecodable (F := F) (A := F) (C : Set (ι → F)) δ a
      ((Fintype.card ι : ℝ≥0) + 1))
    (hTarget : CodingTheory.lineDecodable_imp_epsMCA_le_target (F := F) (A := F)
      C δ a hLD)
    (hle : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle
    mcaSatisfies (C : Set (ι → F)) ε_star
      (mcaThreshold (C : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (C : Set (ι → F)) ε_star
    (mcaThresholdExists_ofLineDecodingTarget C δ a ε_star hδ_le_one hLD hTarget hle)

/-- The BCHKS25 Johnson-range MCA lower bound makes the faithful MCA lattice threshold exist
whenever its explicit right-hand side is below the target `ε_star`. -/
theorem mcaThresholdExists_ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal)) :
    mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  mcaThresholdExists_of_MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star
    (MCALowerWitness.ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
      hBCHKS25 hle)

/-- The faithful MCA threshold obtained from the BCHKS25 Johnson-range lower bound satisfies
the MCA target. -/
theorem mcaThreshold_spec_ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal)) :
    let hne :=
      mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
        hBCHKS25 hle
    mcaSatisfies (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne) :=
  mcaThreshold_spec (ReedSolomon.code domain k : Set (ι → F)) ε_star
    (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one
      hBCHKS25 hle)

/-- Under the §4.5 MCA conjecture, the conjectural lower-witness link also makes the faithful
MCA lattice threshold exist. -/
theorem mcaThresholdExists_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star := by
  obtain ⟨c₁, c₂, c₃, hw⟩ := nonempty_mcaLowerWitness_of_mcaConjecture h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  rcases hw domain k ε_star δ hk hδ hδ1 hle with ⟨w⟩
  exact mcaThresholdExists_of_MCALowerWitness
    (ReedSolomon.code domain k : Set (ιC → FC)) ε_star w

/-- Under the §4.5 MCA conjecture, the faithful lattice threshold obtained from the conjectural
lower-witness link satisfies the MCA bound. -/
theorem mcaThreshold_spec_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        ∃ hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ιC → FC)) ε_star,
          mcaSatisfies (ReedSolomon.code domain k : Set (ιC → FC)) ε_star
            (mcaThreshold (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne) := by
  classical
  rcases mcaThresholdExists_of_mcaConjecture h with ⟨c₁, c₂, c₃, hExists⟩
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  let hne := hExists domain k ε_star δ hk hδ hδ1 hle
  exact ⟨hne, mcaThreshold_spec (ReedSolomon.code domain k : Set (ιC → FC)) ε_star hne⟩

/-- **Upper bracket.** An `MCAUpperWitness` at a radius `δ ≤ 1` forces
`mcaThreshold < ⌊δ·n⌋`: its lattice point already exceeds `ε*`, so the threshold is strictly
below it. -/
theorem mcaThreshold_lt_MCAUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star) (w : MCAUpperWitness C ε_star) (hδ : w.δ ≤ 1) :
    mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) w.δ hδ := by
  by_contra h
  push Not at h
  have hsat : mcaSatisfies C ε_star (latticeIndexOf (ι := ι) w.δ hδ) := by
    refine mcaSatisfies_downward_closed C ε_star h ?_
    exact mcaThreshold_spec C ε_star hne
  have : epsMCA (F := F) (A := F) C
      (mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) w.δ hδ)) ≤
      (ε_star : ENNReal) := hsat
  rw [← epsMCA_eq_at_latticeIndex C w.δ hδ] at this
  exact absurd this (not_le.mpr w.exceeds)

/-- A capacity-side `ε_ca` lower bound for a linear code gives a lattice upper bracket on the
faithful MCA threshold. -/
theorem mcaThreshold_lt_ofEpsCAGt {MC : Submodule F (ι → F)} {ε_star δ : ℝ≥0}
    (hne : mcaThresholdExists (MC : Set (ι → F)) ε_star)
    (h : epsCA (F := F) (A := F) (MC : Set (ι → F)) δ δ > (ε_star : ENNReal))
    (hδ : δ ≤ 1) :
    mcaThreshold (MC : Set (ι → F)) ε_star hne < latticeIndexOf (ι := ι) δ hδ :=
  mcaThreshold_lt_MCAUpperWitness (MC : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofEpsCAGt h) hδ

/-- The CS25 complete-CA-breakdown lower bound gives a direct upper bracket on the faithful
MCA lattice threshold. -/
theorem mcaThreshold_lt_ofRSBreakdownCS25
    (domain : ι ↪ F) (k : ℕ) (δ ε_star : ℝ≥0)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi)
    (hε : (ε_star : ENNReal) < 1) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofRSBreakdownCS25 domain k δ ε_star hq_ge hδ_lo hδ_hi hCS25 hε)
    hδle

/-- The DG25 sampling lower bound gives a direct upper bracket on the faithful MCA lattice
threshold once the sampling lower bound is numerically above `ε*`. -/
theorem mcaThreshold_lt_ofSamplingDG25
    (C : LinearCode ι F) (δ δ' ε_star : ℝ≥0)
    (hne : mcaThresholdExists (C : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (hδ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_pos : 0 < δ) (hδ_lt : δ < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25 C δ δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (C : Set (ι → F))) ≤ δ] >
        (ε_star : ENNReal)) :
    mcaThreshold (C : Set (ι → F)) ε_star hne < latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness (C : Set (ι → F)) ε_star hne
    (MCAUpperWitness.ofSamplingDG25 C δ δ' ε_star hδ' hδ_pos hδ_lt hDG25 hgt)
    hδle

/-- The arbitrary-radius spike lower bound gives a direct upper bracket on the faithful MCA
lattice threshold.  Unlike the endpoint floor, this excludes every lattice point at or above
the chosen radius `δ` whenever the spike value `t / |F|` already exceeds the MCA budget. -/
theorem mcaThreshold_lt_ofSpike
    (domain : ι ↪ F) (k t : ℕ) (δ ε_star : ℝ≥0)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδle : δ ≤ 1)
    (ht_n : t + k ≤ Fintype.card ι) (ht_q : t ≤ Fintype.card F)
    (hδ :
      ((1 - δ) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ))
    (hgt :
      (ε_star : ENNReal) < (t : ENNReal) / (Fintype.card F : ENNReal)) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
      latticeIndexOf (ι := ι) δ hδle :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) ε_star hne
    ⟨δ, lt_of_lt_of_le hgt (epsMCA_ge_spike domain k t δ ht_n ht_q hδ)⟩ hδle

/-- A lower MCA witness and the CS25 complete-CA-breakdown lower bound bracket the faithful
MCA lattice threshold directly. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_RSBreakdownCS25
    (domain : ι ↪ F) (k : ℕ) (δ_hi ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδhi : δ_hi ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) - (δ_hi : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ_hi : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ_hi hq_ge hδ_lo hδ_hi)
    (hε : (ε_star : ENNReal) < 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness
      (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofRSBreakdownCS25 domain k δ_hi ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo)
      hδhi hq_ge hδ_lo hδ_hi hCS25 hε⟩

/-- The BCHKS25 Johnson-range MCA lower bound and the CS25 complete-CA-breakdown lower bound
bracket the faithful MCA lattice threshold directly.  This is the end-to-end lattice form of
the common Johnson-lower/capacity-upper workflow for Reed-Solomon codes. -/
theorem mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_RSBreakdownCS25
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_cs_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) - (δ_hi : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_cs_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ_hi : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ_hi hq_ge hδ_cs_lo hδ_cs_hi)
    (hε : (ε_star : ENNReal) < 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    latticeIndexOf (ι := ι) δ_lo hδlo_le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) wlo,
    mcaThreshold_lt_ofRSBreakdownCS25 domain k δ_hi ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle)
      hδhi hq_ge hδ_cs_lo hδ_cs_hi hCS25 hε⟩

/-- A lower MCA witness and the DG25 sampling lower bound bracket the faithful MCA lattice
threshold directly once the sampling lower bound is numerically above `ε*`. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_SamplingDG25
    (C : LinearCode ι F) (δ_hi δ' ε_star : ℝ≥0)
    (wlo : MCALowerWitness (C : Set (ι → F)) ε_star)
    (hδhi : δ_hi ≤ 1)
    (hδ' : (δ' : ENNReal) = ⨆ u : ι → F, δᵣ(u, (C : Set (ι → F))))
    (hδ_pos : 0 < δ_hi) (hδ_lt : δ_hi < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25 C δ_hi δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (C : Set (ι → F))) ≤ δ_hi] >
        (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (C : Set (ι → F)) ε_star hne ∧
      mcaThreshold (C : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (C : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofSamplingDG25 C δ_hi δ' ε_star
      (mcaThresholdExists_of_MCALowerWitness (C : Set (ι → F)) ε_star wlo)
      hδhi hδ' hδ_pos hδ_lt hDG25 hgt⟩

/-- The BCHKS25 Johnson-range MCA lower bound and the DG25 sampling lower bound bracket the
faithful MCA lattice threshold directly for Reed-Solomon codes. -/
theorem mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_SamplingDG25
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi δ' ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hδ' : (δ' : ENNReal) =
      ⨆ u : ι → F, δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))))
    (hδ_pos : 0 < δ_hi) (hδ_lt : δ_hi < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25
      (ReedSolomon.code domain k) δ_hi δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ_hi] >
        (ε_star : ENNReal)) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    latticeIndexOf (ι := ι) δ_lo hδlo_le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) wlo,
    mcaThreshold_lt_ofSamplingDG25 (ReedSolomon.code domain k) δ_hi δ' ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle)
      hδhi hδ' hδ_pos hδ_lt hDG25 hgt⟩

/-- A lower MCA witness and an arbitrary-radius spike certificate bracket the faithful MCA
lattice threshold directly.  This is a middle-radius finite-search certificate: one side can
come from Johnson/GS-style existence, while the other comes from the explicit spike family at
the candidate next lattice radius. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_Spike
    (domain : ι ↪ F) (k t : ℕ) (δ_hi ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (hδhi : δ_hi ≤ 1)
    (ht_n : t + k ≤ Fintype.card ι) (ht_q : t ≤ Fintype.card F)
    (hδ :
      ((1 - δ_hi) * Fintype.card ι : ℝ≥0) ≤ (Fintype.card ι - t + 1 : ℕ))
    (hgt :
      (ε_star : ENNReal) < (t : ENNReal) / (Fintype.card F : ENNReal)) :
    let hne := mcaThresholdExists_of_MCALowerWitness
      (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofSpike domain k t δ_hi ε_star
      (mcaThresholdExists_of_MCALowerWitness
        (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo)
      hδhi ht_n ht_q hδ hgt⟩

/-- Adjacent per-rate MCA lower witnesses and middle-radius spike certificates resolve the
faithful MCA lattice prize with the lower witness indices as the exact thresholds.

This is a non-endpoint finite-search closing rule: a Johnson/GS-style lower witness can certify
the candidate lattice point, while the explicit spike family rules out the next one. -/
theorem mcaPrizeLatticeResolved_of_lowerWitnesses_and_spike_adjacent
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (t : Fin 4 → ℕ) (δ_hi : Fin 4 → ℝ≥0)
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (ht_n : ∀ j : Fin 4,
      t j + ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (ht_q : ∀ j : Fin 4, t j ≤ Fintype.card F)
    (hδ : ∀ j : Fin 4,
      ((1 - δ_hi j) * Fintype.card ι : ℝ≥0) ≤
        (Fintype.card ι - t j + 1 : ℕ))
    (hgt : ∀ j : Fin 4,
      (epsStar : ENNReal) < (t j : ENNReal) / (Fintype.card F : ENNReal))
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one) := by
  refine mcaPrizeLatticeResolved_of_adjacent_witnesses domain wlo ?_ ?_ ?_
  · intro j
    exact MCAUpperWitness.ofGt
      (lt_of_lt_of_le (hgt j)
        (epsMCA_ge_spike domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (t j) (δ_hi j)
          (ht_n j) (ht_q j) (hδ j)))
  · intro j
    simpa using hδhi j
  · intro j
    simpa using hadj j

/-- Per-rate canonical-window lower bounds and adjacent middle-radius spike certificates resolve
the faithful MCA lattice prize directly.

This is the arithmetic-facing form of
`mcaPrizeLatticeResolved_of_lowerWitnesses_and_spike_adjacent`: the lower witnesses are
instantiated from the unconditional canonical-witness window bound, so an ABF26 certificate file
only has to provide, at each of the four prize rates, the lower binomial/count inequality, the
spike admissibility inequalities, and the one-step lattice adjacency check. -/
theorem mcaPrizeLatticeResolved_of_chooseBounds_and_spike_adjacent
    (domain : ι ↪ F)
    (δ_lo δ_hi : Fin 4 → ℝ≥0) (t : Fin 4 → ℕ)
    (hδlo : ∀ j : Fin 4, δ_lo j ≤ 1)
    (hlo : ∀ j : Fin 4,
      ((Fintype.card ι).choose
          (max
            (⌈((1 : ℝ≥0) - δ_lo j) * (Fintype.card ι : ℝ≥0)⌉₊)
            (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1)) : ENNReal) /
        (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal))
    (hδhi : ∀ j : Fin 4, δ_hi j ≤ 1)
    (ht_n : ∀ j : Fin 4,
      t j + ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ ≤ Fintype.card ι)
    (ht_q : ∀ j : Fin 4, t j ≤ Fintype.card F)
    (hspike_radius : ∀ j : Fin 4,
      ((1 - δ_hi j) * Fintype.card ι : ℝ≥0) ≤
        (Fintype.card ι - t j + 1 : ℕ))
    (hspike_gt : ∀ j : Fin 4,
      (epsStar : ENNReal) < (t j : ENNReal) / (Fintype.card F : ENNReal))
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (δ_lo j) (hδlo j)).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (δ_lo j) (hδlo j)) := by
  let wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar := fun j =>
    MCALowerWitness.ofChooseLe domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (hδlo j) (hlo j)
  have hadj' : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (δ_hi j) (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1 := by
    intro j
    simpa [wlo] using hadj j
  simpa [wlo] using
    (mcaPrizeLatticeResolved_of_lowerWitnesses_and_spike_adjacent
      domain wlo t δ_hi hδhi ht_n ht_q hspike_radius hspike_gt hadj')

/-- A lower MCA witness and a capacity-side `ε_ca` upper witness bracket the faithful lattice
threshold directly. This is the lattice version of the common Johnson-lower/capacity-upper
workflow for linear codes. -/
theorem mcaThresholdLattice_bracketed_of_lowerWitness_and_epsCAGt
    {MC : Submodule F (ι → F)} {ε_star δ_hi : ℝ≥0}
    (wlo : MCALowerWitness (MC : Set (ι → F)) ε_star)
    (hhi : epsCA (F := F) (A := F) (MC : Set (ι → F)) δ_hi δ_hi >
      (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness (MC : Set (ι → F)) ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤
        mcaThreshold (MC : Set (ι → F)) ε_star hne ∧
      mcaThreshold (MC : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold (MC : Set (ι → F)) ε_star
      (mcaThresholdExists_of_MCALowerWitness (MC : Set (ι → F)) ε_star wlo) wlo,
    mcaThreshold_lt_ofEpsCAGt
      (mcaThresholdExists_of_MCALowerWitness (MC : Set (ι → F)) ε_star wlo) hhi hδhi⟩

/-- The BCHKS25 Johnson-range MCA lower bound and any capacity-side `ε_ca` upper witness
bracket the faithful MCA lattice threshold directly for Reed-Solomon codes. -/
theorem mcaThresholdLattice_bracketed_ofJohnsonBCHKS25_and_epsCAGt
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hhi :
      epsCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_hi δ_hi >
        (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    latticeIndexOf (ι := ι) δ_lo hδlo_le_one ≤
        mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne ∧
      mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne <
        latticeIndexOf (ι := ι) δ_hi hδhi :=
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  ⟨MCALowerWitness_le_mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) wlo,
    mcaThreshold_lt_ofEpsCAGt
      (MC := ReedSolomon.code domain k)
      (mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
        hδlo_le_one hBCHKS25 hle) hhi hδhi⟩

/-- The second-moment radius-one lower bound gives a direct upper bracket on the faithful
MCA lattice threshold: in the explicit numeric regime where `epsStar < (M' - M'^2/q)/q`,
the top radius `1` already exceeds `epsStar`, so the threshold lies strictly below the
top lattice point. -/
theorem mcaThreshold_lt_one_of_secondMoment
    (domain : ι ↪ F) (k M' : ℕ)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) epsStar)
    (hk : k + 1 ≤ Fintype.card ι)
    (hM' : M' ≤ Nat.choose (Fintype.card ι) (k + 1))
    (hle : M' * M' ≤ M' * Fintype.card F)
    (hnum :
      Fintype.card F * Fintype.card F <
        2 ^ (128 : ℕ) * (M' * Fintype.card F - M' * M')) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl := by
  have hsecond :
      (epsStar : ENNReal) <
        epsMCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) 1 := by
    exact lt_of_lt_of_le
      (epsStar_lt_second_moment_value
        (M' := M') (q := Fintype.card F) Fintype.card_pos hle hnum)
      (epsMCA_one_ge_second_moment domain hk hM')
  exact mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) epsStar hne
    ⟨1, hsecond⟩ le_rfl

/-- The spike endpoint floor gives a direct upper bracket on the faithful MCA lattice
threshold in the small-field regime where `q < 2^128 · (n-k)`. -/
theorem mcaThreshold_lt_one_of_fieldSmall
    (domain : ι ↪ F) (k : ℕ)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) epsStar)
    (hk : 1 ≤ k) (hn : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (Fintype.card ι - k)) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) epsStar hne
    ⟨1, epsStar_lt_epsMCA_one_of_field_small domain k hk hn hsmall⟩ le_rfl

/-- The unconditional subset-sum endpoint floor gives a direct upper bracket on the faithful
MCA lattice threshold when the subset-sum set is numerically large enough. -/
theorem mcaThreshold_lt_one_of_subsetSums
    (domain : ι ↪ F) (k : ℕ)
    (hne : mcaThresholdExists (ReedSolomon.code domain k : Set (ι → F)) epsStar)
    (hk : k + 1 ≤ Fintype.card ι)
    (hsmall : Fintype.card F < 2 ^ (128 : ℕ) * (subsetSumsKplus1 domain k).card) :
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain k : Set (ι → F)) epsStar hne
    ⟨1, epsStar_lt_epsMCA_one_of_subsetSums domain hk hsmall⟩ le_rfl

/-- The Erdős-Heilbronn endpoint floor for `k = 1` gives a direct upper bracket on the
faithful MCA lattice threshold in the prime-characteristic numeric regime. -/
theorem mcaThreshold_lt_one_of_erdosHeilbronn
    (domain : ι ↪ F) {p : ℕ} (hp : p.Prime)
    (hne : mcaThresholdExists (ReedSolomon.code domain 1 : Set (ι → F)) epsStar)
    (hchar : ringChar F = p) (hn : 2 ≤ Fintype.card ι)
    (hsmall : 2 * (Fintype.card ι - 2) < p)
    (hq : Fintype.card F < 2 ^ (128 : ℕ) * (2 * (Fintype.card ι - 2) + 1)) :
    mcaThreshold (ReedSolomon.code domain 1 : Set (ι → F)) epsStar hne <
      latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl :=
  mcaThreshold_lt_MCAUpperWitness
    (ReedSolomon.code domain 1 : Set (ι → F)) epsStar hne
    ⟨1, epsStar_lt_epsMCA_one_of_erdos_heilbronn domain hp hchar hn hsmall hq⟩ le_rfl

/-- **Lattice bracketing of the MCA threshold (faithful `mca_threshold_bracketed`).** A
lower witness and an upper witness (at a radius `≤ 1`) bracket the lattice threshold:
`⌊δ_lo·n⌋ ≤ mcaThreshold < ⌊δ_hi·n⌋`. This is the lattice replacement for
`GrandChallenges.mca_threshold_bracketed`, which bracketed the collapse-broken real
threshold of a `GrandMCAResolution`. -/
theorem mcaThresholdLattice_bracketed (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hne : mcaThresholdExists C ε_star)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1) :
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ mcaThreshold C ε_star hne ∧
      mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  ⟨MCALowerWitness_le_mcaThreshold C ε_star hne wlo,
    mcaThreshold_lt_MCAUpperWitness C ε_star hne whi hδhi⟩

/-- **Lattice bracketing without a separate existence hypothesis.** The lower witness
both constructs the threshold's nonemptiness proof and supplies the lower bracket. -/
theorem mcaThresholdLattice_bracketed_of_witnesses (C : Set (ι → F)) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ mcaThreshold C ε_star hne ∧
      mcaThreshold C ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  mcaThresholdLattice_bracketed C ε_star
    (mcaThresholdExists_of_MCALowerWitness C ε_star wlo) wlo whi hδhi

/-- If a lower MCA witness and an upper MCA witness land on adjacent lattice indices, the
faithful MCA threshold is exactly the lower witness index.  This is the finite-search closing
step: `lo ≤ threshold < lo + 1` pins the threshold. -/
theorem mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (C : Set (ι → F)) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness C ε_star)
    (whi : MCAUpperWitness C ε_star) (hδhi : whi.δ ≤ 1)
    (hadj :
      (latticeIndexOf (ι := ι) whi.δ hδhi).val =
        (latticeIndexOf (ι := ι) wlo.δ wlo.le_one).val + 1) :
    let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
    mcaThreshold C ε_star hne = latticeIndexOf (ι := ι) wlo.δ wlo.le_one := by
  classical
  let hne := mcaThresholdExists_of_MCALowerWitness C ε_star wlo
  let lo := latticeIndexOf (ι := ι) wlo.δ wlo.le_one
  let hi := latticeIndexOf (ι := ι) whi.δ hδhi
  have hbracket :
      lo ≤ mcaThreshold C ε_star hne ∧ mcaThreshold C ε_star hne < hi := by
    simpa [hne, lo, hi] using
      mcaThresholdLattice_bracketed_of_witnesses C ε_star wlo whi hδhi
  have hle : lo.val ≤ (mcaThreshold C ε_star hne).val := by
    exact Fin.le_iff_val_le_val.mp hbracket.1
  have hlt : (mcaThreshold C ε_star hne).val < hi.val := by
    exact Fin.lt_def.mp hbracket.2
  have hval : (mcaThreshold C ε_star hne).val = lo.val := by
    have hadj' : hi.val = lo.val + 1 := by simpa [lo, hi] using hadj
    omega
  ext
  exact hval

/-- Adjacent BCHKS25 lower and CS25 upper witnesses determine the faithful MCA lattice
threshold exactly. -/
theorem mcaThreshold_eq_ofJohnsonBCHKS25_and_RSBreakdownCS25_adjacent
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_cs_lo :
        1 - CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((CodingTheory.qEntropy (Fintype.card F) (δ_hi : ℝ) - (δ_hi : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_cs_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ_hi : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hCS25 : CodingTheory.rs_epsCA_breakdown_cs25 domain k δ_hi hq_ge hδ_cs_lo hδ_cs_hi)
    (hε : (ε_star : ENNReal) < 1)
    (hadj :
      (latticeIndexOf (ι := ι) δ_hi hδhi).val =
        (latticeIndexOf (ι := ι) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne =
      latticeIndexOf (ι := ι) δ_lo hδlo_le_one := by
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  let whi := MCAUpperWitness.ofRSBreakdownCS25 domain k δ_hi ε_star hq_ge
    hδ_cs_lo hδ_cs_hi hCS25 hε
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo whi hδhi hadj

/-- Adjacent BCHKS25 lower and DG25 sampling upper witnesses determine the faithful MCA
lattice threshold exactly. -/
theorem mcaThreshold_eq_ofJohnsonBCHKS25_and_SamplingDG25_adjacent
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi δ' ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hδ' : (δ' : ENNReal) =
      ⨆ u : ι → F, δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))))
    (hδ_pos : 0 < δ_hi) (hδ_lt : δ_hi < δ')
    (hDG25 : CodingTheory.linear_epsCA_ge_sampling_dg25
      (ReedSolomon.code domain k) δ_hi δ' hδ' hδ_pos hδ_lt)
    (hgt :
      ((Fintype.card F - 1 : ℝ≥0) / Fintype.card F : ENNReal)
          * Pr_{
              let u ← $ᵖ (ι → F)
              }[δᵣ(u, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ_hi] >
        (ε_star : ENNReal))
    (hadj :
      (latticeIndexOf (ι := ι) δ_hi hδhi).val =
        (latticeIndexOf (ι := ι) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne =
      latticeIndexOf (ι := ι) δ_lo hδlo_le_one := by
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  let whi := MCAUpperWitness.ofSamplingDG25 (ReedSolomon.code domain k) δ_hi δ' ε_star
    hδ' hδ_pos hδ_lt hDG25 hgt
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo whi hδhi hadj

/-- Adjacent BCHKS25 lower and generic capacity-side `ε_ca` upper witnesses determine the
faithful MCA lattice threshold exactly. -/
theorem mcaThreshold_eq_ofJohnsonBCHKS25_and_epsCAGt_adjacent
    (domain : ι ↪ F) (k : ℕ) (η δ_lo δ_hi ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ_lo : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) -
            (η : ℝ))
    (hδlo_le_one : δ_lo ≤ 1)
    (hBCHKS25 : CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ_lo
      hη hδ_johnson)
    (hle :
        ENNReal.ofReal
            (let n : ℝ := Fintype.card ι
             let ρ_plus : ℝ := k / n + 1 / n
             let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
             ((2 * (m + 1 / 2) ^ 5 + 3 * (m + 1 / 2) * δ_lo * ρ_plus) /
                    (3 * ρ_plus ^ ((3 : ℝ) / 2)) *
                  n +
                (m + 1 / 2) / ρ_plus ^ ((1 : ℝ) / 2)) /
               (Fintype.card F : ℝ)) ≤
          (ε_star : ENNReal))
    (hhi :
      epsCA (F := F) (A := F) (ReedSolomon.code domain k : Set (ι → F)) δ_hi δ_hi >
        (ε_star : ENNReal))
    (hδhi : δ_hi ≤ 1)
    (hadj :
      (latticeIndexOf (ι := ι) δ_hi hδhi).val =
        (latticeIndexOf (ι := ι) δ_lo hδlo_le_one).val + 1) :
    let hne := mcaThresholdExists_ofJohnsonBCHKS25 domain k η δ_lo ε_star hη
      hδ_johnson hδlo_le_one hBCHKS25 hle
    mcaThreshold (ReedSolomon.code domain k : Set (ι → F)) ε_star hne =
      latticeIndexOf (ι := ι) δ_lo hδlo_le_one := by
  let wlo := MCALowerWitness.ofJohnsonBCHKS25 domain k η δ_lo ε_star hη hδ_johnson
    hδlo_le_one hBCHKS25 hle
  let whi := MCAUpperWitness.ofEpsCAGt
    (MC := ReedSolomon.code domain k) (ε_star := ε_star) (δ := δ_hi) hhi
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (ReedSolomon.code domain k : Set (ι → F)) ε_star wlo whi hδhi hadj


/-! ## The list-decoding lattice threshold

The exact mirror of the MCA development, with the maximised list size `Λ(C^⋈m, δ)` (ABF26
D2.8) in place of `ε_mca`, the threshold `ε*·|F|` in place of `ε*`, and `lambda_coe_mono`
in place of `epsMCA_mono`. -/

open ListDecodable

/-- `Λ(C^⋈m, j/n) ≤ ε*·|F|` at the lattice radius `j/n`. -/
def listSatisfies (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (j : Fin (Fintype.card ι + 1)) : Prop :=
  (Lambda (C^⋈ (Fin m)) ((mcaLatticePoint (Fintype.card ι) j : ℝ≥0) : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

noncomputable instance (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    DecidablePred (listSatisfies C m ε_star) := fun _ => Classical.propDecidable _

/-- **Downward closure** for list decoding, from `lambda_coe_mono`. -/
theorem listSatisfies_downward_closed (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    {i j : Fin (Fintype.card ι + 1)} (hij : i ≤ j) (hj : listSatisfies C m ε_star j) :
    listSatisfies C m ε_star i :=
  le_trans (GrandChallenges.lambda_coe_mono (mcaLatticePoint_mono _ hij)) hj

/-- The satisfying lattice points for the list-decoding bound. -/
noncomputable def listSatSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    Finset (Fin (Fintype.card ι + 1)) :=
  Finset.univ.filter (listSatisfies C m ε_star)

@[simp] theorem mem_listSatSet (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    {j : Fin (Fintype.card ι + 1)} :
    j ∈ listSatSet C m ε_star ↔ listSatisfies C m ε_star j := by
  simp [listSatSet]

/-- **Existence (nonemptiness) hypothesis** for the list-decoding lattice threshold. -/
def listThresholdExists (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  ∃ j : Fin (Fintype.card ι + 1), listSatisfies C m ε_star j

theorem listSatSet_nonempty_iff (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) :
    (listSatSet C m ε_star).Nonempty ↔ listThresholdExists C m ε_star := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_listSatSet C m ε_star).mp hj⟩
  · rintro ⟨j, hj⟩; exact ⟨j, (mem_listSatSet C m ε_star).mpr hj⟩

/-- **The faithful list-decoding lattice threshold.** The greatest lattice index whose
radius keeps `Λ(C^⋈m, ·) ≤ ε*·|F|`, under the existence hypothesis. **Determining its value
is the open ABF26 §1 Grand List Decoding Challenge**; the witnesses bracket it. -/
noncomputable def listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) : Fin (Fintype.card ι + 1) :=
  (listSatSet C m ε_star).max' ((listSatSet_nonempty_iff C m ε_star).mpr hne)

/-- **Existence half.** The list threshold satisfies the bound. -/
theorem listThreshold_spec (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) :
    listSatisfies C m ε_star (listThreshold C m ε_star hne) := by
  have h := (listSatSet C m ε_star).max'_mem ((listSatSet_nonempty_iff C m ε_star).mpr hne)
  exact (mem_listSatSet C m ε_star).mp h

/-- **Maximality.** Every satisfying lattice point is `≤ listThreshold`. -/
theorem le_listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : listSatisfies C m ε_star j) :
    j ≤ listThreshold C m ε_star hne :=
  (listSatSet C m ε_star).le_max' j ((mem_listSatSet C m ε_star).mpr hj)

/-- **Strict failure above the threshold.** -/
theorem gt_listThreshold_exceeds (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) {j : Fin (Fintype.card ι + 1)}
    (hj : listThreshold C m ε_star hne < j) :
    (Lambda (C^⋈ (Fin m)) ((mcaLatticePoint (Fintype.card ι) j : ℝ≥0) : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := by
  by_contra h
  exact absurd (le_listThreshold C m ε_star hne (not_lt.mp h)) (not_le.mpr hj)

/-- **Uniqueness.** `listThreshold` is the unique maximal satisfying lattice index. -/
theorem listThreshold_unique (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star) (j : Fin (Fintype.card ι + 1))
    (hsat : listSatisfies C m ε_star j)
    (hmax : ∀ i : Fin (Fintype.card ι + 1), listSatisfies C m ε_star i → i ≤ j) :
    j = listThreshold C m ε_star hne :=
  le_antisymm (le_listThreshold C m ε_star hne hsat)
    (hmax _ (listThreshold_spec C m ε_star hne))

/-- `Λ` at a real radius equals `Λ` at its lattice point `⌊δ·n⌋/n` (step structure). -/
theorem Lambda_eq_at_latticeIndex (C : Set (ι → F)) (m : ℕ) (δ : ℝ≥0) (hδ : δ ≤ 1) :
    (Lambda (C^⋈ (Fin m)) ((δ : ℝ≥0) : ℝ) : ENNReal) =
      (Lambda (C^⋈ (Fin m))
        ((mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) δ hδ) : ℝ≥0) : ℝ)
        : ENNReal) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  congr 1
  refine Lambda_eq_of_floor_eq (C^⋈ (Fin m)) ?_
  rw [floor_mcaLatticePoint _ hn, latticeIndexOf_val]

/-- **Lower bracket.** A `ListLowerWitness` forces `⌊δ·n⌋ ≤ listThreshold`. -/
theorem ListLowerWitness_le_listThreshold (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (w : GrandChallenges.ListLowerWitness C m ε_star) :
    latticeIndexOf (ι := ι) w.δ w.le_one ≤ listThreshold C m ε_star hne := by
  refine le_listThreshold C m ε_star hne ?_
  unfold listSatisfies
  rw [← Lambda_eq_at_latticeIndex C m w.δ w.le_one]
  exact w.bound

/-- A lower list-decoding witness is enough to make the faithful list threshold exist. -/
theorem listThresholdExists_of_ListLowerWitness (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0) (w : GrandChallenges.ListLowerWitness C m ε_star) :
    listThresholdExists C m ε_star :=
  ⟨latticeIndexOf (ι := ι) w.δ w.le_one, by
    unfold listSatisfies
    rw [← Lambda_eq_at_latticeIndex C m w.δ w.le_one]
    exact w.bound⟩

/-- The faithful list-decoding threshold obtained from a lower witness satisfies the list
bound. -/
theorem listThreshold_spec_of_ListLowerWitness (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0) (w : GrandChallenges.ListLowerWitness C m ε_star) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star w
    listSatisfies C m ε_star (listThreshold C m ε_star hne) :=
  listThreshold_spec C m ε_star (listThresholdExists_of_ListLowerWitness C m ε_star w)

/-- **Upper bracket.** A `ListUpperWitness` at a radius `δ ≤ 1` forces
`listThreshold < ⌊δ·n⌋`. -/
theorem listThreshold_lt_ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (w : GrandChallenges.ListUpperWitness C m ε_star) (hδ : w.δ ≤ 1) :
    listThreshold C m ε_star hne < latticeIndexOf (ι := ι) w.δ hδ := by
  by_contra h
  push Not at h
  have hsat : listSatisfies C m ε_star (latticeIndexOf (ι := ι) w.δ hδ) :=
    listSatisfies_downward_closed C m ε_star h (listThreshold_spec C m ε_star hne)
  have hb : (Lambda (C^⋈ (Fin m))
      ((mcaLatticePoint (Fintype.card ι) (latticeIndexOf (ι := ι) w.δ hδ) : ℝ≥0) : ℝ)
      : ENNReal) ≤ ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) := hsat
  rw [← Lambda_eq_at_latticeIndex C m w.δ hδ] at hb
  exact absurd hb (not_le.mpr w.exceeds)

/-- A strict `Λ` lower bound gives a lattice upper bracket on the faithful list threshold. -/
theorem listThreshold_lt_ofLambdaGt (C : Set (ι → F)) (m : ℕ) {ε_star δ : ℝ≥0}
    (hne : listThresholdExists C m ε_star)
    (h : (Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)))
    (hδ : δ ≤ 1) :
    listThreshold C m ε_star hne < latticeIndexOf (ι := ι) δ hδ :=
  listThreshold_lt_ListUpperWitness C m ε_star hne
    (GrandChallenges.ListUpperWitness.ofGt h) hδ

/-- A lower list witness and a strict `Λ` upper-side bound bracket the faithful list lattice
threshold directly. -/
theorem listThresholdLattice_bracketed_of_lowerWitness_and_LambdaGt
    (C : Set (ι → F)) (m : ℕ) {ε_star δ_hi : ℝ≥0}
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (hhi : (Lambda (C^⋈ (Fin m)) (δ_hi : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)))
    (hδhi : δ_hi ≤ 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) δ_hi hδhi :=
  ⟨ListLowerWitness_le_listThreshold C m ε_star
      (listThresholdExists_of_ListLowerWitness C m ε_star wlo) wlo,
    listThreshold_lt_ofLambdaGt C m
      (listThresholdExists_of_ListLowerWitness C m ε_star wlo) hhi hδhi⟩

/-- **Lattice bracketing of the list-decoding threshold (faithful prize-progress edge).**
A lower witness and an upper witness (at a radius `≤ 1`) bracket the lattice threshold:
`⌊δ_lo·n⌋ ≤ listThreshold < ⌊δ_hi·n⌋`. The list-decoding mirror of
`mcaThresholdLattice_bracketed`. -/
theorem listThresholdLattice_bracketed (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (hne : listThresholdExists C m ε_star)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1) :
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  ⟨ListLowerWitness_le_listThreshold C m ε_star hne wlo,
    listThreshold_lt_ListUpperWitness C m ε_star hne whi hδhi⟩

/-- **List-threshold bracketing without a separate existence hypothesis.** The lower witness
constructs the threshold's nonemptiness proof and supplies the lower bracket. -/
theorem listThresholdLattice_bracketed_of_witnesses (C : Set (ι → F)) (m : ℕ)
    (ε_star : ℝ≥0)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    latticeIndexOf (ι := ι) wlo.δ wlo.le_one ≤ listThreshold C m ε_star hne ∧
      listThreshold C m ε_star hne < latticeIndexOf (ι := ι) whi.δ hδhi :=
  listThresholdLattice_bracketed C m ε_star
    (listThresholdExists_of_ListLowerWitness C m ε_star wlo) wlo whi hδhi

/-- If a lower list witness and an upper list witness land on adjacent lattice indices, the
faithful list-decoding threshold is exactly the lower witness index. -/
theorem listThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0)
    (wlo : GrandChallenges.ListLowerWitness C m ε_star)
    (whi : GrandChallenges.ListUpperWitness C m ε_star) (hδhi : whi.δ ≤ 1)
    (hadj :
      (latticeIndexOf (ι := ι) whi.δ hδhi).val =
        (latticeIndexOf (ι := ι) wlo.δ wlo.le_one).val + 1) :
    let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
    listThreshold C m ε_star hne = latticeIndexOf (ι := ι) wlo.δ wlo.le_one := by
  classical
  let hne := listThresholdExists_of_ListLowerWitness C m ε_star wlo
  let lo := latticeIndexOf (ι := ι) wlo.δ wlo.le_one
  let hi := latticeIndexOf (ι := ι) whi.δ hδhi
  have hbracket :
      lo ≤ listThreshold C m ε_star hne ∧ listThreshold C m ε_star hne < hi := by
    simpa [hne, lo, hi] using
      listThresholdLattice_bracketed_of_witnesses C m ε_star wlo whi hδhi
  have hle : lo.val ≤ (listThreshold C m ε_star hne).val := by
    exact Fin.le_iff_val_le_val.mp hbracket.1
  have hlt : (listThreshold C m ε_star hne).val < hi.val := by
    exact Fin.lt_def.mp hbracket.2
  have hval : (listThreshold C m ε_star hne).val = lo.val := by
    have hadj' : hi.val = lo.val + 1 := by simpa [lo, hi] using hadj
    omega
  ext
  exact hval

/-! ## Faithful prize-resolution targets

The collapse-broken `GrandChallenges.mcaPrize` / `GrandChallenges.listDecodingPrize` predicates
ask only for existence of real thresholds.  The lattice formulation exposes the actual finite
quantities the paper asks to determine: one lattice index for each prize rate.  The predicates
below let a downstream proof state "these are the four thresholds" and immediately unfold that
claim to the verified satisfy/maximality characterization. -/

/-- A proposed solution of the MCA prize lattice problem: for every prize rate, the faithful
MCA lattice threshold is the supplied index `τ j`. -/
def mcaPrizeLatticeResolved (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) : Prop :=
  ∀ j : Fin 4,
    ∃ hne : mcaThresholdExists
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar,
      mcaThreshold
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          epsStar hne = τ j

/-- The faithful MCA prize-resolution predicate is exactly the per-rate statement that the
proposed lattice index satisfies the MCA bound and is maximal among satisfying lattice points. -/
theorem mcaPrizeLatticeResolved_iff (domain : ι ↪ F)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) :
    mcaPrizeLatticeResolved domain τ ↔
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : mcaThresholdExists C epsStar,
          mcaSatisfies C epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C epsStar i → i ≤ τ j := by
  constructor
  · intro h j
    rcases h j with ⟨hne, heq⟩
    refine ⟨hne, ?_, ?_⟩
    · simpa [heq] using mcaThreshold_spec
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar hne
    · intro i hi
      simpa [heq] using le_mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar hne hi
  · intro h j
    rcases h j with ⟨hne, hsat, hmax⟩
    refine ⟨hne, ?_⟩
    exact (mcaThreshold_unique
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar hne (τ j) hsat hmax).symm

/-- If radius one already satisfies the MCA budget, then the faithful MCA lattice threshold is
the top lattice point.  This is the positive endpoint counterpart to the radius-one
obstruction lemmas: when the top point is good, maximality forces it to be the threshold. -/
theorem mcaThreshold_eq_top_of_epsMCA_one_le
    (C : Set (ι → F)) (ε_star : ℝ≥0)
    (hone : epsMCA (F := F) (A := F) C 1 ≤ (ε_star : ENNReal)) :
    let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
    let hne : mcaThresholdExists C ε_star := ⟨top, by
      unfold mcaSatisfies
      have h1 : mcaLatticePoint (Fintype.card ι) top = 1 := by
        unfold mcaLatticePoint
        exact div_self (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
      rw [h1]
      exact hone⟩
    mcaThreshold C ε_star hne = top := by
  classical
  let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  have h1 : mcaLatticePoint (Fintype.card ι) top = 1 := by
    unfold mcaLatticePoint
    exact div_self (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')
  let hne : mcaThresholdExists C ε_star := ⟨top, by
    unfold mcaSatisfies
    rw [h1]
    exact hone⟩
  have hsat : mcaSatisfies C ε_star top := by
    unfold mcaSatisfies
    rw [h1]
    exact hone
  have hmax : ∀ i : Fin (Fintype.card ι + 1), mcaSatisfies C ε_star i → i ≤ top := by
    intro i _hi
    rw [Fin.le_iff_val_le_val]
    exact Nat.lt_succ_iff.mp i.isLt
  exact (mcaThreshold_unique C ε_star hne top hsat hmax).symm

/-- Endpoint upper bounds resolve the faithful MCA lattice prize with threshold `1` at every
prize rate. -/
theorem mcaPrizeLatticeResolved_top_of_radiusOne_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      epsMCA (F := F) (A := F)
        (ReedSolomon.code domain
          ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) 1
        ≤ (epsStar : ENNReal)) :
    mcaPrizeLatticeResolved domain
      (fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩) := by
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let top : Fin (Fintype.card ι + 1) := ⟨Fintype.card ι, Nat.lt_succ_self _⟩
  let hne : mcaThresholdExists C epsStar := ⟨top, by
    unfold mcaSatisfies
    simpa [C, top] using hbound j⟩
  refine ⟨hne, ?_⟩
  simpa [C, top, hne] using
    mcaThreshold_eq_top_of_epsMCA_one_le (C := C) (ε_star := epsStar) (hbound j)

/-- The radius-one counting upper bound gives exact top faithful MCA thresholds whenever
`C(n,k_j+1)/q ≤ epsStar` at every prize rate. -/
theorem mcaPrizeLatticeResolved_top_of_choose_bounds
    (domain : ι ↪ F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι)
          (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    mcaPrizeLatticeResolved domain
      (fun _ => ⟨Fintype.card ι, Nat.lt_succ_self _⟩) := by
  apply mcaPrizeLatticeResolved_top_of_radiusOne_bounds
  intro j
  exact le_trans
    (epsMCA_one_le_choose_div domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊)
    (hbound j)

/-- Existentially resolving the faithful MCA lattice prize is equivalent to threshold
nonemptiness at all four prize rates.  Once every rate has at least one satisfying lattice point,
the finite threshold function itself supplies the four proposed indices. -/
theorem exists_mcaPrizeLatticeResolved_iff (domain : ι ↪ F) :
    (∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ) ↔
      ∀ j : Fin 4,
        mcaThresholdExists
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          epsStar := by
  constructor
  · rintro ⟨τ, hτ⟩ j
    exact (hτ j).choose
  · intro h
    refine ⟨fun j =>
      mcaThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F))
        epsStar (h j), ?_⟩
    intro j
    exact ⟨h j, rfl⟩

/-- Per-rate lower MCA witnesses resolve the faithful MCA lattice prize existentially.  This is
the four-rate aggregation form used by downstream Johnson/GS/CA upper-bound pipelines. -/
theorem exists_mcaPrizeLatticeResolved_of_lowerWitnesses
    (domain : ι ↪ F)
    (w : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), mcaPrizeLatticeResolved domain τ :=
  (exists_mcaPrizeLatticeResolved_iff domain).mpr fun j =>
    mcaThresholdExists_of_MCALowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      epsStar (w j)

/-- Per-rate lower and upper MCA witnesses bracket all four faithful MCA prize thresholds. -/
theorem mcaPrizeLattice_bracketed_of_witnesses
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
      latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one ≤
          mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne <
          latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := fun j =>
  mcaThresholdLattice_bracketed_of_witnesses
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    epsStar (wlo j) (whi j) (hδhi j)

/-- Per-rate lower MCA witnesses and per-rate second-moment endpoint certificates bracket all
four faithful MCA prize thresholds below the top lattice point.

This is the four-rate faithful-lattice counterpart of
`not_mcaPrize_of_second_moment`: instead of merely refuting the collapsed formal predicate,
it records that radius `1` is already above the MCA budget, so any existing faithful
threshold lies strictly below the top lattice point. -/
theorem mcaPrizeLattice_lt_one_of_lowerWitnesses_and_secondMoment
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hk : ∀ j : Fin 4,
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι)
    (M' : Fin 4 → ℕ)
    (hM : ∀ j : Fin 4,
      M' j ≤ Nat.choose (Fintype.card ι)
        (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1))
    (hle : ∀ j : Fin 4, M' j * M' j ≤ M' j * Fintype.card F)
    (hnum : ∀ j : Fin 4,
      Fintype.card F * Fintype.card F <
        2 ^ (128 : ℕ) *
          (M' j * Fintype.card F - M' j * M' j)) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
      latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one ≤
          mcaThreshold C epsStar hne ∧
        mcaThreshold C epsStar hne <
          latticeIndexOf (ι := ι) (1 : ℝ≥0) le_rfl := fun j =>
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  let hne := mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j)
  ⟨MCALowerWitness_le_mcaThreshold C epsStar hne (wlo j),
    mcaThreshold_lt_one_of_secondMoment domain
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ (M' j) hne
      (hk j) (hM j) (hle j) (hnum j)⟩

/-- Adjacent per-rate MCA witnesses resolve the faithful MCA lattice prize with the lower
witness indices as the four exact thresholds. -/
theorem mcaPrizeLatticeResolved_of_adjacent_witnesses
    (domain : ι ↪ F)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.MCALowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.MCAUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1) :
    mcaPrizeLatticeResolved domain
      (fun j => latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one) := by
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  refine ⟨mcaThresholdExists_of_MCALowerWitness C epsStar (wlo j), ?_⟩
  exact mcaThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    C epsStar (wlo j) (whi j) (hδhi j) (hadj j)

/-- A proposed solution of the list-decoding prize lattice problem at interleaving `m`: for
every prize rate, the faithful list-decoding lattice threshold is the supplied index `τ j`. -/
def listPrizeLatticeResolved (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) : Prop :=
  ∀ j : Fin 4,
    ∃ hne : listThresholdExists
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar,
      listThreshold
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          m epsStar hne = τ j

/-- The faithful list-prize resolution predicate is exactly the per-rate statement that the
proposed lattice index satisfies the list-size bound and is maximal among satisfying lattice
points. -/
theorem listPrizeLatticeResolved_iff (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1)) :
    listPrizeLatticeResolved domain m τ ↔
      ∀ j : Fin 4,
        let C : Set (ι → F) :=
          ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
        ∃ _ : listThresholdExists C m epsStar,
          listSatisfies C m epsStar (τ j) ∧
            ∀ i : Fin (Fintype.card ι + 1), listSatisfies C m epsStar i → i ≤ τ j := by
  constructor
  · intro h j
    rcases h j with ⟨hne, heq⟩
    refine ⟨hne, ?_, ?_⟩
    · simpa [heq] using listThreshold_spec
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar hne
    · intro i hi
      simpa [heq] using le_listThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar hne hi
  · intro h j
    rcases h j with ⟨hne, hsat, hmax⟩
    refine ⟨hne, ?_⟩
    exact (listThreshold_unique
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar hne (τ j) hsat hmax).symm

/-- Existentially resolving the faithful list-decoding lattice prize is equivalent to threshold
nonemptiness at all four prize rates for the chosen interleaving `m`. -/
theorem exists_listPrizeLatticeResolved_iff (domain : ι ↪ F) (m : ℕ) :
    (∃ τ : Fin 4 → Fin (Fintype.card ι + 1), listPrizeLatticeResolved domain m τ) ↔
      ∀ j : Fin 4,
        listThresholdExists
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
            Set (ι → F))
          m epsStar := by
  constructor
  · rintro ⟨τ, hτ⟩ j
    exact (hτ j).choose
  · intro h
    refine ⟨fun j =>
      listThreshold
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ :
          Set (ι → F))
        m epsStar (h j), ?_⟩
    intro j
    exact ⟨h j, rfl⟩

/-- Per-rate lower list-decoding witnesses resolve the faithful list lattice prize
existentially for the chosen interleaving `m`. -/
theorem exists_listPrizeLatticeResolved_of_lowerWitnesses
    (domain : ι ↪ F) (m : ℕ)
    (w : ∀ j : Fin 4,
      GrandChallenges.ListLowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar) :
    ∃ τ : Fin 4 → Fin (Fintype.card ι + 1), listPrizeLatticeResolved domain m τ :=
  (exists_listPrizeLatticeResolved_iff domain m).mpr fun j =>
    listThresholdExists_of_ListLowerWitness
      (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar (w j)

/-- Per-rate lower and upper list-decoding witnesses bracket all four faithful list prize
thresholds for the chosen interleaving `m`. -/
theorem listPrizeLattice_bracketed_of_witnesses
    (domain : ι ↪ F) (m : ℕ)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.ListLowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.ListUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1) :
    ∀ j : Fin 4,
      let C : Set (ι → F) :=
        ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
      let hne := listThresholdExists_of_ListLowerWitness C m epsStar (wlo j)
      latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one ≤
          listThreshold C m epsStar hne ∧
        listThreshold C m epsStar hne <
          latticeIndexOf (ι := ι) (whi j).δ (hδhi j) := fun j =>
  listThresholdLattice_bracketed_of_witnesses
    (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
    m epsStar (wlo j) (whi j) (hδhi j)

/-- Adjacent per-rate list-decoding witnesses resolve the faithful list lattice prize with the
lower witness indices as the four exact thresholds. -/
theorem listPrizeLatticeResolved_of_adjacent_witnesses
    (domain : ι ↪ F) (m : ℕ)
    (wlo : ∀ j : Fin 4,
      GrandChallenges.ListLowerWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (whi : ∀ j : Fin 4,
      GrandChallenges.ListUpperWitness
        (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar)
    (hδhi : ∀ j : Fin 4, (whi j).δ ≤ 1)
    (hadj : ∀ j : Fin 4,
      (latticeIndexOf (ι := ι) (whi j).δ (hδhi j)).val =
        (latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one).val + 1) :
    listPrizeLatticeResolved domain m
      (fun j => latticeIndexOf (ι := ι) (wlo j).δ (wlo j).le_one) := by
  intro j
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊
  refine ⟨listThresholdExists_of_ListLowerWitness C m epsStar (wlo j), ?_⟩
  exact listThreshold_eq_latticeIndexOf_lowerWitness_of_adjacent
    C m epsStar (wlo j) (whi j) (hδhi j) (hadj j)

/-- Exact values for the canonical `Finset ℕ` list threshold resolve the four-rate faithful
list-decoding prize predicate in the `Fin (n+1)` lattice representation.

This is pure representation glue: downstream files such as
`GrandChallengeLDThresholdElias.lean` prove exact values for
`GrandChallenges.listLatticeThreshold`, while the prize-facing predicate here is stated using
`listThreshold`. -/
theorem listPrizeLatticeResolved_of_canonical_listLatticeThreshold_eq
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty)
    (heq : ∀ r : Fin 4,
      GrandChallenges.listLatticeThreshold
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar (hne r) = (τ r).val) :
    listPrizeLatticeResolved domain m τ := by
  classical
  intro r
  let C : Set (ι → F) :=
    ReedSolomon.code domain ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊
  let t : ℕ := GrandChallenges.listLatticeThreshold C m epsStar (hne r)
  have ht_mem : t ∈ GrandChallenges.listLatticeSet C m epsStar := by
    simpa [t] using
      (GrandChallenges.listLatticeSet C m epsStar).max'_mem (hne r)
  have ht_range : t < Fintype.card ι + 1 := by
    rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at ht_mem
    exact ht_mem.1
  have ht_bound :
      (Lambda (C^⋈ (Fin m)) (((t : ℝ≥0) / (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ) :
          ENNReal) ≤ (epsStar : ENNReal) * (Fintype.card F : ENNReal) := by
    rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range] at ht_mem
    exact ht_mem.2
  have hτval : t = (τ r).val := by
    simpa [C, t] using heq r
  have hsatτ : listSatisfies C m epsStar (τ r) := by
    unfold listSatisfies mcaLatticePoint
    simpa [hτval] using ht_bound
  let hne' : listThresholdExists C m epsStar := ⟨τ r, hsatτ⟩
  refine ⟨hne', ?_⟩
  have hmax : ∀ i : Fin (Fintype.card ι + 1), listSatisfies C m epsStar i → i ≤ τ r := by
    intro i hi
    have hi_mem : i.val ∈ GrandChallenges.listLatticeSet C m epsStar := by
      rw [GrandChallenges.listLatticeSet, Finset.mem_filter, Finset.mem_range]
      refine ⟨i.isLt, ?_⟩
      unfold listSatisfies mcaLatticePoint at hi
      simpa using hi
    have hi_le_t : i.val ≤ t :=
      Finset.le_max' (GrandChallenges.listLatticeSet C m epsStar) i.val hi_mem
    rw [Fin.le_iff_val_le_val]
    exact le_trans hi_le_t (le_of_eq hτval)
  exact (listThreshold_unique C m epsStar hne' (τ r) hsatτ hmax).symm

/-- Per-rate adjacent Johnson-square/Elias certificates resolve the faithful four-rate
list-decoding lattice prize directly.

This packages the canonical `Finset ℕ` exact-threshold theorem from
`GrandChallengeLDThresholdElias.lean` through the prize-facing `Fin (n+1)` representation:
for each prize rate, a squared Johnson certificate at `τ r` and an Elias-volume failure
certificate at `(τ r).val + 1` determine the exact threshold. -/
theorem listPrizeLatticeResolved_of_johnson_sq_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
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
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  Module.finrank F
                    (ReedSolomon.code domain
                      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊))))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_canonical_listLatticeThreshold_eq
    domain m τ hne ?_
  intro r
  exact ProximityGap.listLatticeThreshold_eq_of_johnson_sq_and_elias_next
    (C := ReedSolomon.code domain
      ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
    (m := m) (j := (τ r).val) (ℓ := ℓ r)
    hm (hnext r) hq1 (hP r) (hsq r) (hpow r) (hvol_next r) (hne r)

/-- Per-rate adjacent Johnson-square/Elias certificates with the Reed-Solomon distance and
rank already specialized to the prize degree.

This is the numerics-facing ABF26 LD closing criterion: after supplying the standard
Reed-Solomon facts `minDist = n - k + 1` and `finrank = k`, the two remaining analytic
certificates are exactly the squared Johnson inequality and the Elias-volume inequality in
terms of the concrete prize degree `k = ⌊rate·n⌋`. -/
theorem listPrizeLatticeResolved_of_johnson_sq_rsDistance_and_elias_next
    (domain : ι ↪ F) (m : ℕ)
    (τ : Fin 4 → Fin (Fintype.card ι + 1))
    (ℓ : Fin 4 → ℕ)
    (hm : m ≠ 0)
    (hnext : ∀ r : Fin 4, (τ r).val + 1 < Fintype.card ι)
    (hq1 : 1 < Fintype.card F)
    (hP : ∀ r : Fin 4,
      (Fintype.card ι : ℝ) / (Fintype.card F : ℝ) ≤
        ((Fintype.card ι - (τ r).val : ℕ) : ℝ))
    (hminDist : ∀ r : Fin 4,
      Code.minDist
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F)) =
        Fintype.card ι - ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ + 1)
    (hrank : ∀ r : Fin 4,
      Module.finrank F
          (ReedSolomon.code domain
            ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊) =
        ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)
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
                    (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))))
    (hpow : ∀ r : Fin 4,
      ((ℓ r : ENNReal)) ^ m ≤
        (epsStar : ENNReal) * (Fintype.card F : ENNReal))
    (hvol_next : ∀ r : Fin 4,
      (epsStar : ENNReal) * (Fintype.card F : ENNReal) <
        ENNReal.ofReal
          ((CodingTheory.hammingBallVolume (Fintype.card F)
              (((((τ r).val + 1 : ℕ) : ℝ≥0) /
                    (Fintype.card ι : ℝ≥0) : ℝ≥0) : ℝ)
              (Fintype.card ι) : ℝ)
            / (Fintype.card F : ℝ) ^
                ((Fintype.card ι : ℝ) -
                  ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊)))
    (hne : ∀ r : Fin 4,
      (GrandChallenges.listLatticeSet
        (ReedSolomon.code domain
          ⌊prizeRates r * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar).Nonempty) :
    listPrizeLatticeResolved domain m τ := by
  refine listPrizeLatticeResolved_of_johnson_sq_and_elias_next
    domain m τ ℓ hm hnext hq1 hP ?_ hpow ?_ hne
  · intro r
    simpa [hminDist r] using hsq r
  · intro r
    simpa [hrank r] using hvol_next r

end GrandChallengesLattice

end ProximityGap
