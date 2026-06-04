/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Mirco Richter, Poulami Das (Least Authority), Aristotle (Harmonic)
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination'

import ArkLib.Data.Fin.Sigma
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.UniqueDecoding
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound
import ArkLib.ProofSystem.Stir.ProximityGap

/-! Section 4.5 from STIR [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open BigOperators Finset NNReal Code

namespace Combine
variable {m : ℕ}
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- Fact 4.10
  Geometric series formula in a field, for a unit `r : F`. -/
lemma geometric_sum_units {F : Type*} [Field F] [DecidableEq F] {r : Fˣ} {a : ℕ} :
  ∑ j ∈ range (a + 1), (r ^ j : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by
  by_cases h : r = 1
  · rw [h]
    simp
  · simp only [h, ↓reduceIte]
    rw [geom_sum_eq]
    · have {a b : F} : a / b = -a / -b := by
        field_simp
      rw [@this _ (1 - ↑r)]
      simp
    · simp only [ne_eq, Units.val_eq_one]
      exact h

def ri (dstar : ℕ) (degs : Fin m → ℕ) (r : F) (i : Fin m) : F :=
            let exp := i + ∑ j < i, (dstar - degs j)
            r ^ exp

/-- Definition 4.11.1
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x)
      := sum_{i < m} r_i * f_i(x) * ( sum_{l < (d* - d_i + 1)} (r * φ(x))^l ) -/
def combine
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) (x : ι) : F :=
    ∑ i, (ri dstar degs r i) * (fs i x) * (∑ l ∈ range (dstar - degs i + 1), ((φ x) * r)^l)

@[simp]
lemma combine_dstar_zero
  {φ : ι ↪ F} {r : F} {fs : Fin m → ι → F} {degs : Fin m → ℕ} {x : ι} 
  :
  combine φ 0 r fs degs = 
    ∑ i, (r ^ i.val) • fs i
  := by
  unfold combine ri
  simp only [zero_tsub, sum_const_zero, add_zero, zero_add, range_one, sum_singleton, pow_zero,
    mul_one]
  ext y
  simp
/-- Definition 4.11.2
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      if (r * φ(x)) = 1 then sum_{i < m} r_i * f_i(x) * (dstar - degree + 1)
      else sum_{i < m} r_i * f_i(x) * (1 - r * φ(x)^(dstar - degree + 1)) / (1 - r * φ(x))
-/
lemma combine_eq_cases {F ι : Type*} [Field F] [DecidableEq F]
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ)
    (hdegs : ∀ i, degs i ≤ dstar) :
  combine φ dstar r fs degs =
    fun x =>
      let q := φ x * r
      if q ≠ 1
      then ∑ i, (ri dstar degs r i) * (fs i x) * (1 - q^(dstar - degs i + 1)) / (1 - q)
      else ∑ i, (ri dstar degs r i) * (fs i x) *  (dstar - degs i + 1) := by
  ext x
  unfold combine
  simp only
  by_cases h : r = 0
  · aesop
  · by_cases h' : φ x * r = 1
    · aesop
    · simp only [ne_eq, h', not_false_eq_true, ↓reduceIte]
      congr
      ext i
      have :
        ri dstar degs r i * fs i x * (1 - (φ x * r) ^ (dstar - degs i + 1)) / (1 - φ x * r) =
          (ri dstar degs r i * fs i x) * ((1 - (φ x * r) ^ (dstar - degs i + 1)) / (1 - φ x * r))
        := by
          field_simp
      rw [this]
      congr
      by_cases hq0 : φ x * r = 0
      · -- q = 0: the geometric series collapses to 1, and the closed form is also 1
        simp [hq0]
      · have := GroupWithZero.eq_zero_or_unit (φ x * r)
        rcases this with h0 | ⟨r', hr'⟩
        · exact (hq0 h0).elim
        · rw [hr', geometric_sum_units]
          have : r' ≠ 1 := by
            -- `q ≠ 1` in this branch and `q = r'`
            intro hEq
            apply h'
            simpa [hEq] using hr'
          simp [this]

open Finset
open BigOperators

def block_size (dstar : ℕ) (degs : Fin m → ℕ) (i : Fin m) := dstar - degs i + 1
def block_start (dstar : ℕ) (degs : Fin m → ℕ) (i : Fin m) := ∑ j ∈ univ.filter (· < i), block_size dstar degs j
def total_terms (dstar : ℕ) (degs : Fin m → ℕ) := ∑ i, block_size dstar degs i

private lemma block_start_monotone 
  {dstar : ℕ} {degs : Fin m → ℕ} {i j : Fin m} (h : i ≤ j) :
  block_start dstar degs i ≤ block_start dstar degs j 
  := by
  have h_subset : Finset.filter (· < i) Finset.univ ⊆ Finset.filter (· < j) Finset.univ := by
      grind;
  apply Finset.sum_le_sum_of_subset; assumption


private lemma block_start_zero 
  {dstar : ℕ} {degs : Fin m.succ → ℕ} :
  block_start dstar degs 0 = 0 := by 
  simp [block_start]

private lemma block_start_filter_nonempty
  {dstar : ℕ} {degs : Fin m.succ → ℕ} {l : ℕ}
  :
  (univ.filter (fun j => block_start dstar degs j ≤ l)).Nonempty
  := by 
  simp only [Finset.Nonempty, Nat.succ_eq_add_one, mem_filter, mem_univ, true_and]
  exists 0
  simp [block_start]

private lemma block_idx_eq_max 
  {dstar : ℕ} {degs : Fin m → ℕ} 
  {i : Fin m} {j : Fin (block_size dstar degs i)}
  :
  Finset.max 
    {x | block_start dstar degs x ≤ block_start dstar degs i + j}
  = i
  := by
    refine' le_antisymm _ _ <;> norm_num [ Finset.le_max ];
    intro a ha;
    contrapose! ha;
    refine' lt_of_lt_of_le ( Nat.add_lt_add_left ( Fin.is_lt j ) _ ) _;
    unfold block_start block_size;
    rw [ show ( Finset.univ.filter fun j => j < a ) = Finset.univ.filter ( fun j => j < i ) ∪ { i } ∪ Finset.univ.filter ( fun j => i < j ∧ j < a ) from ?_, Finset.sum_union, Finset.sum_union ] <;> norm_num [ ha.ne, ha.ne.symm ];
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => lt_asymm ( Finset.mem_filter.mp hx₁ |>.2 ) ( Finset.mem_filter.mp hx₂ |>.2.1 );
    · grind

set_option maxHeartbeats 0 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
private lemma combine_eq_flat 
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) :
  combine φ dstar r fs degs = fun x =>
    ∑ L ∈ range (total_terms dstar degs),
      let i_opt := Finset.max (univ.filter (fun j => block_start dstar degs j ≤ L))
      match i_opt with
      | none => 0
      | some i =>
        let k := L - block_start dstar degs i
        ri dstar degs r i * fs i x * (φ x * r) ^ k
:= by
  -- The sum over the Finset.range (total_terms dstar degs) can be reorganized to match the structure of the blocks in combine.
  have h_sum_reorganized : ∀ x : ι, ∑ L ∈ Finset.range (total_terms dstar degs), (let i_opt := Finset.max (Finset.univ.filter (fun j => block_start dstar degs j ≤ L)); match i_opt with | Option.none => 0 | Option.some i => let k := L - block_start dstar degs i; ri dstar degs r i * fs i x * ((φ x) * r) ^ k) = ∑ i : Fin m, ∑ L ∈ Finset.range (block_size dstar degs i), ri dstar degs r i * fs i x * ((φ x) * r) ^ L := by
    intro x
    have h_partition : Finset.range (total_terms dstar degs) = Finset.biUnion (Finset.univ : Finset (Fin m)) (fun i => Finset.Ico (block_start dstar degs i) (block_start dstar degs i + block_size dstar degs i)) := by
      ext L
      simp [total_terms, block_start, block_size];
      constructor;
      · induction' m with m ih;
        · aesop;
        · intro hL
          by_cases h : L < ∑ x : Fin m, (dstar - degs (Fin.castSucc x) + 1);
          · obtain ⟨ a, ha₁, ha₂ ⟩ := ih ( fun i x => fs i.castSucc x ) ( fun i => degs i.castSucc ) h;
            refine' ⟨ Fin.castSucc a, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_castSucc ];
            · convert ha₁ using 1;
              simp +decide [ Fin.sum_univ_castSucc, Finset.sum_filter ];
              exact Fin.le_last _;
            · simp_all +decide [ Fin.sum_univ_castSucc, Finset.sum_filter ];
              grind;
          · refine' ⟨ Fin.last m, _, _ ⟩ <;> simp_all +decide [ Fin.sum_univ_castSucc ];
            · rw [ Finset.sum_filter ];
              rw [ Fin.sum_univ_castSucc ] ; aesop;
            · simp_all +decide [ Fin.sum_univ_castSucc, Finset.sum_filter ];
      · rintro ⟨ i, hi ⟩;
        refine' lt_of_lt_of_le hi.2 _;
        rw [ ← Finset.sum_sdiff ( Finset.subset_univ ( Finset.filter ( fun x => x < i ) Finset.univ ) ) ];
        rw [ add_comm ];
        simp
        apply Nat.lt_of_succ_le
        rw [Nat.succ_eq_add_one]
        apply Finset.single_le_sum
          ( fun x _ => Nat.zero_le ( dstar - degs x + 1 ) )
        simp
    rw [ h_partition, Finset.sum_biUnion ];
    · refine' Finset.sum_congr rfl fun i hi => _;
      refine' Finset.sum_bij ( fun L hL => L - block_start dstar degs i ) _ _ _ _ <;> simp +decide;
      · exact fun a ha₁ ha₂ => by rw [ tsub_lt_iff_left ha₁ ] ; exact ha₂;
      · intros; omega;
      · exact fun b hb => ⟨ block_start dstar degs i + b, ⟨ by linarith, by linarith ⟩, by simp +decide ⟩;
      · intro a ha₁ ha₂;
        rw [ show Finset.max ( Finset.filter ( fun j => block_start dstar degs j ≤ a ) Finset.univ ) = ↑i from ?_ ];
        refine' le_antisymm _ _ <;> simp +decide [ Finset.max ];
        · intro j hj₁;
          contrapose! hj₁;
          refine' lt_of_lt_of_le ha₂ _;
          unfold block_start block_size;
          rw [ show ( Finset.univ.filter fun k => k < j ) = Finset.univ.filter ( fun k => k < i ) ∪ { i } ∪ Finset.univ.filter ( fun k => i < k ∧ k < j ) from ?_, Finset.sum_union, Finset.sum_union ] <;> norm_num;
          · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => lt_asymm ( Finset.mem_filter.mp hx₁ |>.2 ) ( Finset.mem_filter.mp hx₂ |>.2.1 );
          · grind;
        · exact ⟨ i, ha₁, le_rfl ⟩;
    · intro i _ j _ hij
      have h_disjoint : block_start dstar degs j ≥ block_start dstar degs i + block_size dstar degs i ∨ block_start dstar degs i ≥ block_start dstar degs j + block_size dstar degs j := by
        cases lt_or_gt_of_ne hij <;> simp_all +decide [ block_start, block_size ];
        · refine' Or.inl ( le_trans _ ( Finset.sum_le_sum_of_subset ( show Finset.filter ( fun x => x < i ) Finset.univ ∪ { i } ⊆ Finset.filter ( fun x => x < j ) Finset.univ from _ ) ) );
          · rw [ Finset.sum_union ] <;> simp +decide [ *, Finset.sum_singleton ];
          · simp +decide [ Finset.subset_iff, * ];
            exact fun a ha => lt_trans ha ‹_›;
        · rw [ show ( Finset.univ.filter fun x => x < i ) = Finset.univ.filter ( fun x => x < j ) ∪ { j } ∪ ( Finset.univ.filter ( fun x => x < i ) \ ( Finset.univ.filter ( fun x => x < j ) ∪ { j } ) ) from ?_, Finset.sum_union, Finset.sum_union ] <;> simp +decide [ *, Finset.sum_singleton, Finset.sum_union ];
          · simp +contextual [ Finset.disjoint_left ];
          · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_univ _, lt_trans ( Finset.mem_filter.mp hx |>.2 ) ‹_› ⟩;
      cases h_disjoint <;> [ exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂ ] ; ; exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂ ] ];
  ext x; exact (by
  convert h_sum_reorganized x |> Eq.symm using 2 ; simp +decide [ combine, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring!;);

private lemma combine_eq_flat'
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m.succ → ι → F) (degs : Fin m.succ → ℕ) :
  combine φ dstar r fs degs = fun x =>
    ∑ l : Fin (total_terms dstar degs),
      let i := Finset.max' 
          (univ.filter (fun j => block_start dstar degs j ≤ l)) 
          block_start_filter_nonempty
      let k := l - block_start dstar degs i
      ri dstar degs r i * fs i x * (φ x * r) ^ k
  := by
  rw [combine_eq_flat]
  ext x
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_equiv (Equiv.refl _) (by simp)
  intro i hi 
  simp at hi
  simp only [Nat.succ_eq_add_one, Equiv.refl_apply, hi, ↓reduceDIte]
  have h : Finset.max {j | block_start dstar degs j ≤ i}
    = Finset.max' {j | block_start dstar degs j ≤ i} block_start_filter_nonempty
  := by
    simp [Finset.max, Finset.max']
    rfl
  rw [h]
  simp
  rfl

private lemma combine_eq_flat''
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m.succ → ι → F) (degs : Fin m.succ → ℕ) :
  combine φ dstar r fs degs = fun x =>
    ∑ l : Fin (total_terms dstar degs),
      let i := Finset.max' 
          (univ.filter (fun j => block_start dstar degs j ≤ l)) 
          block_start_filter_nonempty
      let k := l - block_start dstar degs i
      r ^ (i + ∑ j < i, (dstar - degs j)) 
        * fs i x * (φ x * r) ^ k
  := by
  rw [combine_eq_flat']
  ext x 
  simp
  congr
     
private lemma combine_eq_flat'''
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m.succ → ι → F) (degs : Fin m.succ → ℕ) :
  combine φ dstar r fs degs = fun x =>
    ∑ l : Fin (total_terms dstar degs),
      (r ^ l.val) *      
      (let i := Finset.max' 
          (univ.filter (fun j => block_start dstar degs j ≤ l)) 
          block_start_filter_nonempty
      let k := l - block_start dstar degs i
      fs i x * (φ x) ^ k)
  := by 
  have h_block : ∀ l : Fin (Combine.total_terms dstar degs), ∃ i : Fin m.succ, Combine.block_start dstar degs i ≤ l ∧ ∀ j : Fin m.succ, Combine.block_start dstar degs j ≤ l → j ≤ i := by
        intro l
        obtain ⟨i, hi⟩ : ∃ i : Fin m.succ, Combine.block_start dstar degs i ≤ l := by
          use 0
          simp [Combine.block_start_zero]
        generalize_proofs at *; (
        exact ⟨ Finset.max' ( Finset.univ.filter fun j => Combine.block_start dstar degs j ≤ l ) ⟨ i, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hi ⟩ ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.univ.filter fun j => Combine.block_start dstar degs j ≤ l ) ⟨ i, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hi ⟩ ⟩ ) |>.2, fun j hj => Finset.le_max' _ _ ( by simpa using hj ) ⟩)
  convert Combine.combine_eq_flat'' φ dstar r fs degs using 1;
  refine' funext fun x => Finset.sum_congr rfl fun l hl => _;
  obtain ⟨ i, hi, hi' ⟩ := h_block l;
  rw [ show ( Finset.max' ( Finset.filter ( fun j => Combine.block_start dstar degs j ≤ ( l : ℕ ) ) Finset.univ ) Combine.block_start_filter_nonempty ) = i from ?_ ];
  · rw [ show ( l : ℕ ) = Combine.block_start dstar degs i + ( l - Combine.block_start dstar degs i ) by rw [ Nat.add_sub_of_le hi ] ] ; ring;
    simp +decide [ Combine.block_start, Finset.sum_Ico_eq_sum_range ];
    simp +decide [ Combine.block_size, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
    rw [ show ( Finset.filter ( fun x => x < i ) Finset.univ : Finset ( Fin ( m + 1 ) ) ) = Finset.Iio i by ext; simp +decide ] ; simp +decide [ ← pow_add ] ;
    exact Or.inl <| Or.inl <| by ring;
  · refine' le_antisymm _ _ <;> simp_all +decide [ Finset.max' ];
    exact ⟨ i, hi, le_rfl ⟩;

set_option synthInstance.maxHeartbeats 20000 in
private lemma combine_eq_flat_final
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) :
  combine φ dstar r fs degs = 
    ∑ l : Fin (total_terms dstar degs),
      r ^ (l : ℕ) • fun (x : ι) ↦ (
        let i : WithBot (Fin m) := Finset.max (univ.filter (fun j ↦ block_start dstar degs j ≤ l))
        i.elim (0 : F) fun i ↦
          let k := l - block_start dstar degs i
          fs i x * (φ x) ^ k                     
      )
  := by 
  rcases m with _ | m
  · unfold combine
    ext x
    simp [Option.elim]
  · rw [combine_eq_flat''']
    ext x
    simp
    congr
    ext l
    simp
    have h :
      Finset.max {j | block_start dstar degs j ≤ ↑l}
      = Finset.max' {j | block_start dstar degs j ≤ ↑l}
          block_start_filter_nonempty
    := by
      simp [Finset.max, Finset.max']
      rfl
    rw [h]
    simp [Option.elim]

-- def DegCor

/-- Definition 4.12.1
    DegCor(d*, r, f, degree)(x) := f(x) * ( sum_{ l < d* - d + 1 } (r * φ(x))^l ) -/
def degCor
  (φ : ι ↪ F) (dstar degree : ℕ) (r : F) (f : ι → F) (x : ι) : F :=
    f x * ∑ l ∈ range (dstar - degree + 1), ((φ x) * r) ^ l

/-- Definition 4.12.2
    DegCor(d*, r, f, d)(x) := f(x) * conditionalExp(x) -/
lemma degreeCor_eq {F : Type u_1} [Field F] [DecidableEq F] {ι : Type u_2} (φ : ι ↪ F)
  (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) (x : ι) :
  let q := φ x * r
  degCor φ dstar degree r f x =
    if q ≠ 1
    then f x * (1 - q^(dstar - degree + 1)) / (1 - q)
    else f x * (dstar - degree + 1) := by
  intros q
  unfold degCor
  by_cases h : q = 1
  · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
    congr
    rcases GroupWithZero.eq_zero_or_unit (φ x * r) with h' | h'
    · aesop
    · dsimp [q] at h
      rcases h' with ⟨r', h'⟩
      rw [h', geometric_sum_units]
      aesop
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
    have :
      f x * (1 - q ^ (dstar - degree + 1)) / (1 - q) =
        f x * ((1 - q ^ (dstar - degree + 1)) / (1 - q)) := by
      field_simp
    rw [this]
    congr
    rcases GroupWithZero.eq_zero_or_unit (φ x * r) with h' | h'
    · aesop
    · rcases h' with ⟨r', h'⟩
      rw [h', geometric_sum_units]
      aesop


variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] 

open scoped NNReal NNRat in
private lemma glorious_lemma
  {n m : ℕ}
  {δ : ℝ≥0} {rho : ℚ≥0}
  (hδLt : δ < (min (1 - NNReal.sqrt rho)
    (1 - rho - 1 / (↑m))))
  (hrho : rho = n / (↑m : ℚ≥0))
  :
  ↑rho + 1 / ↑(m) < 1 - δ := by 
    all_goals first | infer_instance | simp_all +decide [ lt_tsub_iff_left ] ; ring_nf at * ;
    exact hδLt.2.trans_le' ( by norm_cast ) ;

private lemma even_more_glorious_lemma
  {n m : ℕ}
  {δ : ℝ≥0}
  (hm : 0 < m)
  (h : ↑n / ↑(m) + (↑(m))⁻¹ < 1 - δ)
  :
  ↑(n + 1) < (1 - δ) * m 
 := by 
 rw [← div_lt_iff₀ (by positivity)]; convert h using 1; push_cast; ring   

open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
lemma master_lemma
  [Nonempty ι]
  {φ : ι ↪ F} {dstar m : ℕ}
  {fs : Fin m → ι → F} {degs : Fin m → ℕ} (hdegs : ∀ i, degs i ≤ dstar)
  {δ : ℝ≥0} 
  (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
    (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
  {S : Finset ι}
  (hS_card : (1 - δ) * (Fintype.card ι) ≤ S.card)
  {v : (i : Fin m) → Fin (block_size dstar degs i) → Polynomial F}
  (hv_deg : ∀ i j, (v i j).degree < dstar)
  (hv_eval : ∀ i j, ∀ x ∈ S, (v i j).eval (φ x) = (φ x) ^ j.val * (fs i x))
  (i : Fin m)
  (j : Fin (block_size dstar degs i))
  :
  (v i j).degree < degs i + j := by 
  have hlt : 
    dstar < Fintype.card ι := by
    by_contra contra
    simp at contra
    rw [ReedSolomon.rateOfLinearCode_eq_min_div] at hδLt
    rw [min_eq_right contra] at hδLt
    simp at hδLt
  rcases j with ⟨j, hj⟩   
  simp only [block_size] at hj
  simp
  generalize hj': (dstar - degs i) - j = j'
  revert j
  induction j' with
  | zero => 
    intro j hj hj'
    have hj' : j = (dstar - degs i) := by omega
    conv =>
      rhs
      rw [hj']
    rw [←WithBot.coe_natCast]
    have h : 
      WithBot.some (dstar - degs i) = Nat.cast (dstar - degs i) := by
        rfl
    rw [h]
    rw [←WithBot.coe_natCast]
    rw [←WithBot.coe_add, ←Nat.cast_add]
    have h : 
      degs i + (dstar - degs i) = dstar := Nat.add_sub_of_le (hdegs i)
    rw [h]
    exact hv_deg i ⟨j, hj⟩
  | succ j' ih => 
    intro j hj hj' 
    have hj' : j = dstar - degs i - j' - 1 := by omega
    have h_fin : j + 1 < dstar - degs i + 1 := by omega
    specialize ih (j + 1) h_fin (by omega)
    let q : Polynomial F := Polynomial.X * v i ⟨j, hj⟩ 
    have hq_deg : q.degree < dstar + 1 := by
      simp [q]
      rw [WithBot.lt_def]
      simp
      by_cases hv: v i ⟨j, hj⟩ = 0
      · left
        simp [hv]
        exists dstar + 1
      · right 
        rw [Polynomial.degree_eq_natDegree hv]
        exists (1 + (v i ⟨j ,hj⟩).natDegree)
        exists (dstar + 1)
        apply And.intro
        · rw [add_comm] 
          apply Nat.add_lt_add_right
          rw [Polynomial.natDegree_lt_iff_degree_lt hv]
          exact hv_deg _ _
        · apply And.intro rfl rfl
    have hq_coincide :
      ∀ x ∈ S, q.eval (φ x) = (v i ⟨j + 1, h_fin⟩).eval (φ x) := by
      intro x hx 
      simp [q]
      rw [hv_eval _ _ _ hx]
      rw [hv_eval _ _ _ hx]
      ring_nf
    have hq_coincide := 
      Polynomial.eq_of_eval_eq_degree
        (q := v i ⟨j + 1, h_fin⟩)
        hq_deg (by {
          simp
          apply lt_trans (hv_deg _ _)
          rw [WithBot.lt_def]
          simp
          exists dstar 
          exists (dstar + 1)
          simp
          rfl
        }) (Finset.image φ S) (by {
          simp
          rw [Finset.card_image_of_injective _ (by {
            intro x y hxy
            aesop
          })]
          have h : ↑(rate (code φ dstar)) + 1 / ↑(Fintype.card ι) < 1 - δ := by
            simp only [ReedSolomon.sqrtRate] at hδLt 
            apply glorious_lemma 
              hδLt (by {
                simp [rate]
                rfl
              })
          rw [ReedSolomon.rateOfLinearCode_eq_min_div] at h
          rw [min_eq_left (by omega)] at h
          simp at h
          have h := even_more_glorious_lemma (m := Fintype.card ι) 
            (by simp) h
          have h := le_trans (le_of_lt h) hS_card 
          rw [Nat.cast_le] at h
          omega
        })
        (by {
          intro x hx
          simp at hx
          rcases hx with ⟨a, ⟨ha, hx⟩⟩
          rw [←hx]
          exact hq_coincide a ha
        })
    simp [q] at hq_coincide
    rw [←hq_coincide] at ih
    simp at ih
    rw [←add_assoc] at ih
    rw [add_comm 1] at ih
    rw [WithBot.add_lt_add_iff_right (by simp)] at ih
    exact ih
        
open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- Lemma 4.13
  Let `dstar` be the target degree, `f₁,...,f_{m-1} : ι → F`,
  `0 < degs₁,...,degs_{m-1} < dstar` be degrees and
  `δ ∈ (0, min{(1-BStar(ρ)), (1-ρ-1/|ι|)})` be a distance parameter, then
      Pr_{r ← F} [δᵣ(Combine(dstar,r,(f₁,degs₁),...,(fₘ,degsₘ)))]
                   > err' (dstar, ρ, δ, m * (dstar + 1) - ∑ i degsᵢ) -/
theorem combine_theorem
  {φ : ι ↪ F} {dstar m : ℕ}
  -- Finding 17 cascade: the keystone is false at dstar = 0, so this consumer
  -- inherits the nondegeneracy hypothesis (see upstream-issues.md).
  [NeZero dstar]
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
  (δ : ℝ≥0) (hδPos : δ > 0)
  (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                   (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
  (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
    proximityError F dstar (rate (code φ dstar)) δ (m * (dstar + 1) - ∑ i, degs i)) :
    jointAgreement (F := F) (κ := Fin m) (ι := ι) (C := code φ dstar)
      (W := fs) (δ := δ)
    := by
  classical
  let nterms : Fin m → ℕ := fun i => dstar - degs i + 1
  let K := (i : Fin m) × Fin (nterms i)
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let fexp : Fin (Fintype.card K) → ι → F :=
    fun k x => fs (e k).1 x * (φ x) ^ ((e k).2 : ℕ)
  let gen : F → Fin (Fintype.card K) → F :=
    fun r k => ri dstar degs r (e k).1 * r ^ ((e k).2 : ℕ)
  have hδLt' : δ < 1 - Bstar (rate (code φ dstar)) := by
    exact lt_of_lt_of_le hδLt (min_le_left _ _)
  have hcardK :
      Fintype.card K = m * (dstar + 1) - ∑ i : Fin m, degs i := by
    have hsum :
        (∑ i : Fin m, nterms i) = m * (dstar + 1) - ∑ i : Fin m, degs i := by
      calc
        (∑ i : Fin m, nterms i) = ∑ i : Fin m, ((dstar + 1) - degs i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [nterms]
          have hi := hdegs i
          omega
        _ = (∑ _ : Fin m, (dstar + 1)) - ∑ i : Fin m, degs i := by
          simpa using Finset.sum_tsub_distrib (s := Finset.univ)
            (f := fun _ : Fin m => dstar + 1) (g := degs) (by
              intro i _
              exact Nat.le_trans (hdegs i) (Nat.le_succ dstar))
        _ = m * (dstar + 1) - ∑ i : Fin m, degs i := by
          simp [Finset.sum_const]
    calc
      Fintype.card K = ∑ i : Fin m, nterms i := by
        simp [K]
      _ = m * (dstar + 1) - ∑ i : Fin m, degs i := hsum
  have hcombine :
      (fun r : F => (fun x : ι => ∑ j : Fin (Fintype.card K), gen r j * fexp j x)) =
        (fun r : F => combine φ dstar r fs degs) := by
    funext r x
    simp only [combine, gen, fexp]
    rw [(Equiv.sum_comp e (fun k : K =>
      ri dstar degs r k.1 * r ^ (k.2 : ℕ) * (fs k.1 x * φ x ^ (k.2 : ℕ))))]
    change (∑ k : K, ri dstar degs r k.1 * r ^ (k.2 : ℕ) *
        (fs k.1 x * φ x ^ (k.2 : ℕ))) =
      ∑ i, ri dstar degs r i * fs i x *
        ∑ l ∈ range (dstar - degs i + 1), (φ x * r) ^ l
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_fin_eq_sum_range]
    simp only [nterms]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [dif_pos (by
      have hl' := Finset.mem_range.mp hl
      omega)]
    ring_nf
  have hProb' :
      Pr_{ let r ← $ᵖ F}[
        δᵣ((fun x => ∑ j : Fin (Fintype.card K), gen r j * fexp j x), code φ dstar) ≤ δ] >
      ENNReal.ofReal
        (proximityError F dstar (rate (code φ dstar)) δ (Fintype.card K)) := by
    have hProb₁ :
        Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), code φ dstar) ≤ δ] >
        ENNReal.ofReal
          (proximityError F dstar (rate (code φ dstar)) δ (Fintype.card K)) := by
      rw [hcardK]
      simpa using hProb
    have hcombine_app :
        ∀ r : F, (fun x : ι => ∑ j : Fin (Fintype.card K), gen r j * fexp j x) =
          combine φ dstar r fs degs := by
      intro r
      exact congrFun hcombine r
    simpa [hcombine_app] using hProb₁
  rcases STIR.proximity_gap (φ := φ) (degree := dstar) (m := Fintype.card K)
      (δ := δ) (f := fexp) (GenFun := gen) hδPos hδLt' hProb' with
    ⟨S, hS, hclose⟩
  refine ⟨S, hS, ?_⟩
  choose v hv_mem hv_agree using
    (fun i : Fin m => hclose (e.symm ⟨i, ⟨0, by simp [nterms]⟩⟩))
  refine ⟨v, fun i => ?_⟩
  constructor
  · exact hv_mem i
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    let pair : K := ⟨i, ⟨0, by simp [nterms]⟩⟩
    have h : fexp (e.symm pair) x = v i x := by
      simpa [pair] using hv_agree i x hx
    have hfs : fexp (e.symm pair) x = fs i x := by
      have heq : e (e.symm pair) = pair := Equiv.apply_symm_apply e pair
      change fs (e (e.symm pair)).1 x * φ x ^ ((e (e.symm pair)).2 : ℕ) = fs i x
      rw [heq]
      simp [pair]
    exact h.symm.trans hfs

end Combine
