/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.UDRBadCount
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.JointAgreement

/-!
# Connected unique-decoding-regime MCA bound for Reed–Solomon, from scratch (#232)

Wires the from-scratch UDR bad-scalar bound to the actual `ε_mca` of a Reed–Solomon code, yielding
ABF26 Table-1 row 2 (`ε_mca ≤ O(δn)/|F|` below the unique-decoding radius) with **no admit**:

  `epsMCA_rs_udr_le` — for `RS[F, α, k]` with `k ≤ n` and the regime `3(n − t) < n − k + 1`
  (`t = ⌈(1-δ)n⌉`, the witness-size floor), `ε_mca(RS, δ) ≤ 2(n − t)/|F|`.

Since `n − t ≈ δn`, this is `ε_mca ≤ 2δn/|F|`, a genuine positive-side lower-witness on `δ*`
(`δ* ≥ δ` whenever the regime holds). The minimum-distance input is `ReedSolomon.code_eq_of_agree`
(degree-`<k` codewords agreeing on `≥ k` points are equal).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ProximityGap.UDRwire

open Finset ProximityGap
open scoped NNReal ENNReal

/-- The standalone UDR engine's local pair predicate is definitionally the global
`pairJointAgreesOn` predicate once the submodule code is viewed as a set. -/
theorem pairJoint_iff_pairJointAgreesOn {ι F : Type} [Field F]
    (C : Submodule F (ι → F)) (S : Finset ι)
    (u₀ u₁ : ι → F) :
    UDR.pairJoint C S u₀ u₁ ↔ pairJointAgreesOn (C : Set (ι → F)) S u₀ u₁ :=
  Iff.rfl

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq ι] in
theorem badGamma_le (e₀ e₁ : ι → F) :
    (univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card
      ≤ (univ.filter (fun i => e₁ i ≠ 0)).card :=
  UDR.badGamma_le e₀ e₁

omit [DecidableEq ι] [Fintype F] in
theorem badCount_udr_le (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) (d t : ℕ)
    (htn : t < Fintype.card ι)
    (hmd : ∀ a ∈ C, ∀ b ∈ C, (univ.filter (fun i => a i ≠ b i)).card < d → a = b)
    (hreg : 3 * (Fintype.card ι - t) < d)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = u₀ i + γ • u₁ i)
    (hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (C : Set (ι → F)) (S γ) u₀ u₁) :
    G.card ≤ 2 * (Fintype.card ι - t) := by
  exact UDR.badCount_udr_le C u₀ u₁ d t htn hmd hreg G S w hSt hwC hwS
    (fun γ hγ hpair => hno γ hγ ((pairJoint_iff_pairJointAgreesOn C (S γ) u₀ u₁).mp hpair))

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- RS minimum-distance, agreement form: degree-`<k` codewords disagreeing on `< n − k + 1`
coordinates are equal (via `ReedSolomon.code_eq_of_agree`). -/
theorem rs_min_dist (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι) :
    ∀ a ∈ (ReedSolomon.code α k : Set (ι → F)), ∀ b ∈ (ReedSolomon.code α k : Set (ι → F)),
      (univ.filter (fun i => a i ≠ b i)).card < Fintype.card ι - k + 1 → a = b := by
  classical
  intro a ha b hb hdis
  refine ReedSolomon.code_eq_of_agree hk ha hb (S := univ.filter (fun i => a i = b i))
    (fun i hi => (mem_filter.mp hi).2) ?_
  have hpart := Finset.card_filter_add_card_filter_not (s := (univ : Finset ι))
    (p := fun i => a i = b i)
  rw [Finset.card_univ] at hpart
  have hpart' : (univ.filter (fun i => a i = b i)).card
      + (univ.filter (fun i => a i ≠ b i)).card = Fintype.card ι := hpart
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  omega

omit [DecidableEq ι] [DecidableEq F] in
open Classical in
/-- **Connected UDR MCA bound for Reed–Solomon (from scratch, no admit).** For `RS[F,α,k]` with
`k ≤ n` and the unique-decoding regime `3(n − ⌈(1-δ)n⌉) < n − k + 1`,
`ε_mca(RS, δ) ≤ 2(n − ⌈(1-δ)n⌉)/|F|`. -/
theorem epsMCA_rs_udr_le (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι) (δ : ℝ≥0)
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ < Fintype.card ι)
    (hreg : 3 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1) :
    epsMCA (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
      ≤ ((2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) : ℕ)
          : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  set t : ℕ := ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with htdef
  have hmd := rs_min_dist α k hk
  apply epsMCA_le_of_badCount_le (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
    (2 * (Fintype.card ι - t))
  intro u
  set G : Finset F :=
    univ.filter (fun γ : F =>
      mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ) with hGdef
  set S : F → Finset ι := fun γ =>
    if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ then
      h.choose
    else
      ∅ with hSdef
  set w : F → ι → F := fun γ =>
    if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ
      then (h.choose_spec.2.1).choose else 0 with hwdef
  refine badCount_udr_le (ReedSolomon.code α k) (u 0) (u 1) (Fintype.card ι - k + 1) t htn hmd hreg
    G S w ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    have hcardR : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((h.choose.card : ℕ) : ℝ≥0) := h.choose_spec.1
    rw [htdef]; exact Nat.ceil_le.mpr hcardR
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    exact (h.choose_spec.2.1).choose_spec.1
  · intro γ hγ i hi
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    simp only [hSdef, dif_pos h] at hi
    exact (h.choose_spec.2.1).choose_spec.2 i hi
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    exact h.choose_spec.2.2

open Classical in
/-- **A non-trivial `MCALowerWitness` from the UDR bound.** For a large enough field
(`2(n−t)·2^128 ≤ |F|`, `t = ⌈(1-δ)n⌉`) in the unique-decoding regime, radius `δ` certifies
`ε_mca(RS, δ) ≤ ε*` (`ε* = 2^{-128}`), so the Grand MCA threshold satisfies `δ* ≥ δ`. This upgrades
the lower witness from `δ = 0` to the unique-decoding radius `δ ≲ (1−ρ)/3`. -/
noncomputable def rs_mcaLowerWitness_udr (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (hδ1 : δ ≤ 1)
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ < Fintype.card ι)
    (hreg : 3 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1)
    (hF : 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) * 2 ^ 128 ≤ Fintype.card F) :
    GrandChallenges.MCALowerWitness (ReedSolomon.code α k : Set (ι → F)) epsStar where
  δ := δ
  le_one := hδ1
  bound := by
    refine le_trans (epsMCA_rs_udr_le α k hk δ htn hreg) ?_
    set m : ℕ := 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) with hm
    have hmpos : 0 < m := by rw [hm]; omega
    have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hmpos.ne'
    have hmt : (m : ℝ≥0∞) ≠ ⊤ := by exact_mod_cast (ENNReal.natCast_ne_top m)
    have hcoe : (epsStar : ENNReal) = 1 / 2 ^ 128 := by
      rw [epsStar, ENNReal.coe_div (by positivity), ENNReal.coe_one, ENNReal.coe_pow,
        ENNReal.coe_ofNat]
    rw [hcoe]
    have hFge : ((m * 2 ^ 128 : ℕ) : ℝ≥0∞) ≤ (Fintype.card F : ℝ≥0∞) := by exact_mod_cast hF
    have hcast : ((m * 2 ^ 128 : ℕ) : ℝ≥0∞) = (m : ℝ≥0∞) * 2 ^ 128 := by push_cast; ring
    calc (m : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
        ≤ (m : ℝ≥0∞) / ((m * 2 ^ 128 : ℕ) : ℝ≥0∞) := ENNReal.div_le_div_left hFge (m : ℝ≥0∞)
      _ = (m : ℝ≥0∞) / ((m : ℝ≥0∞) * 2 ^ 128) := by rw [hcast]
      _ = (m : ℝ≥0∞) * 1 / ((m : ℝ≥0∞) * 2 ^ 128) := by rw [mul_one]
      _ = 1 / 2 ^ 128 := ENNReal.mul_div_mul_left 1 (2 ^ 128) hm0 hmt

/-! ## Extension to the *full* unique-decoding radius via the proximity-gap dichotomy

The bound `badCount_udr_le` needs `3(n − t) < d` because it bootstraps the global codeword pair
from *two* bad scalars (so the agreement set is an intersection of two witness sets, size `2t − n`,
and a third witness intersection costs another `(n − t)`). The Polishchuk–Spielman-backed
`RS_jointAgreement_of_goodCoeffs_card_gt` instead hands the global pair directly on a *single*
size-`t` set, removing one factor: the regime relaxes to `2(n − t) < d`, i.e. the *full*
unique-decoding radius `δ ≤ (d−1)/(2n)`. -/

omit [DecidableEq ι] [Fintype F] in
/-- **Bad-scalar bound with a handed-in global pair (e.g. from `jointAgreement`).** Needs only
`2(n − t) < d`. The pair `(c₀, c₁)` agreeing with `(u₀, u₁)` on a single size-`t` set `S₀` lets the
min-distance step pin `w γ = c₀ + γ • c₁` (agreement on `S₀ ∩ S γ`, size `≥ 2t − n`), after which
`¬ pairJointAgreesOn` forces an `i ∈ E := supp(e₁)` with `e₀ i + γ · e₁ i = 0`; that map
`γ ↦ i` is injective (`badGamma_le`), so the bad count is `≤ |E| ≤ n − t`. -/
theorem badCount_udr_le_jointAgreement (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) (d t : ℕ)
    (hmd : ∀ a ∈ C, ∀ b ∈ C, (univ.filter (fun i => a i ≠ b i)).card < d → a = b)
    (hreg : 2 * (Fintype.card ι - t) < d)
    (c₀ c₁ : ι → F) (hc₀C : c₀ ∈ C) (hc₁C : c₁ ∈ C)
    (S₀ : Finset ι) (hS₀t : t ≤ S₀.card)
    (hc₀S : ∀ i ∈ S₀, c₀ i = u₀ i) (hc₁S : ∀ i ∈ S₀, c₁ i = u₁ i)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = u₀ i + γ • u₁ i)
    (hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (C : Set (ι → F)) (S γ) u₀ u₁) :
    G.card ≤ Fintype.card ι - t := by
  classical
  set e₀ : ι → F := u₀ - c₀ with he₀def
  set e₁ : ι → F := u₁ - c₁ with he₁def
  have he₁S₀ : ∀ i ∈ S₀, e₁ i = 0 := fun i hi => by
    simp only [he₁def, Pi.sub_apply, hc₁S i hi, sub_self]
  have hsupp : (univ.filter (fun i => e₁ i ≠ 0)).card ≤ Fintype.card ι - t := by
    have hsub : (univ.filter (fun i => e₁ i ≠ 0)) ⊆ S₀ᶜ := by
      intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
      simp only [mem_compl]; intro hiS₀; exact hi (he₁S₀ i hiS₀)
    calc (univ.filter (fun i => e₁ i ≠ 0)).card ≤ S₀ᶜ.card := card_le_card hsub
      _ = Fintype.card ι - S₀.card := card_compl S₀
      _ ≤ Fintype.card ι - t := by omega
  have hGsub : G ⊆ G.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0) := by
    intro γ hγ
    simp only [mem_filter, hγ, true_and]
    have hcollapse : w γ = c₀ + γ • c₁ := by
      apply hmd _ (hwC γ hγ) _ (C.add_mem hc₀C (C.smul_mem _ hc₁C))
      have hsub2 : (univ.filter (fun i => w γ i ≠ (c₀ + γ • c₁) i)) ⊆ (S₀ ∩ S γ)ᶜ := by
        intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_compl, mem_inter, not_and]; intro hiS₀ hiS
        apply hi
        have e1 := hc₀S i hiS₀; have e2 := hc₁S i hiS₀; have e3 := hwS γ hγ i hiS
        simp only [Pi.add_apply, Pi.smul_apply, e1, e2, e3, smul_eq_mul]
      have hcardle : (univ.filter (fun i => w γ i ≠ (c₀ + γ • c₁) i)).card < d := by
        have hle := card_le_card hsub2
        rw [card_compl] at hle
        have hun : (S₀ ∪ S γ).card ≤ Fintype.card ι := by simpa using card_le_univ (S₀ ∪ S γ)
        have hui : (S₀ ∪ S γ).card + (S₀ ∩ S γ).card = S₀.card + (S γ).card :=
          card_union_add_card_inter S₀ (S γ)
        have hsg := hSt γ hγ
        omega
      exact hcardle
    have hnpj := hno γ hγ
    have hexi : ∃ i ∈ S γ, ¬ (c₀ i = u₀ i ∧ c₁ i = u₁ i) := by
      by_contra hcon; push Not at hcon
      exact hnpj ⟨c₀, hc₀C, c₁, hc₁C, fun i hi => hcon i hi⟩
    obtain ⟨i, hiS, hidis⟩ := hexi
    have hci := congrFun hcollapse i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hci
    have hsi := hwS γ hγ i hiS
    rw [smul_eq_mul] at hsi
    have hc : u₀ i + γ * u₁ i = c₀ i + γ * c₁ i := by rw [← hsi, hci]
    have haff : e₀ i + γ * e₁ i = 0 := by
      simp only [he₀def, he₁def, Pi.sub_apply]; linear_combination hc
    have he₁i : e₁ i ≠ 0 := by
      intro h0
      rw [h0, mul_zero, add_zero] at haff
      apply hidis
      refine ⟨?_, ?_⟩
      · have hz : u₀ i - c₀ i = 0 := by simpa only [he₀def, Pi.sub_apply] using haff
        exact (sub_eq_zero.mp hz).symm
      · have hz : u₁ i - c₁ i = 0 := by simpa only [he₁def, Pi.sub_apply] using h0
        exact (sub_eq_zero.mp hz).symm
    exact ⟨i, he₁i, haff⟩
  calc G.card
      ≤ (G.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card :=
        card_le_card hGsub
    _ ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := UDR.badGammaOn_le G e₀ e₁
    _ ≤ Fintype.card ι - t := hsupp

omit [DecidableEq ι] in
open Code Classical in
/-- **Full-UDR MCA bound for Reed–Solomon.** For `RS[F, α, k]` with `k ≤ n`, *below the unique-
decoding radius* (`δ ≤ relUDR`) and in the regime `2(n − ⌈(1−δ)n⌉) < n − k + 1`,
`ε_mca(RS, δ) ≤ |ι|/|F|`. The proof splits each pencil via `RS_goodCoeffs_card_dichotomy`: if the
δ-close count is `≤ |ι|` the bad count is too (`badCount_le_lineCloseCount`); otherwise
`jointAgreement` holds and `badCount_udr_le_jointAgreement` bounds the bad count by `n − t ≤ |ι|`.
This extends `epsMCA_rs_udr_le` (regime `3(n − t) < d`) to the full unique-decoding radius. -/
theorem epsMCA_rs_udr_le_full (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ : δ ≤ relativeUniqueDecodingRadius (ι := ι) (F := F)
      (C := ReedSolomon.code α k))
    (hreg : 2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1) :
    epsMCA (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
      ≤ (Fintype.card ι : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  set t : ℕ := ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with htdef
  have hmd := rs_min_dist α k hk
  apply epsMCA_le_of_badCount_le (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
    (Fintype.card ι)
  intro u
  by_cases hgt : (RS_goodCoeffs (deg := k) (domain := α) u δ).card > Fintype.card ι
  · have hja := RS_jointAgreement_of_goodCoeffs_card_gt (deg := k) (domain := α) hδ u hgt
    obtain ⟨S₀, hS₀card, v, hv⟩ := hja
    have hS₀t : t ≤ S₀.card := by
      rw [htdef]; exact Nat.ceil_le.mpr (by exact_mod_cast hS₀card)
    have hc₀C : v 0 ∈ ReedSolomon.code α k := (hv 0).1
    have hc₁C : v 1 ∈ ReedSolomon.code α k := (hv 1).1
    have hc₀S : ∀ i ∈ S₀, v 0 i = u 0 i := fun i hi => by
      have := (hv 0).2 hi; rw [Finset.mem_filter] at this; exact this.2
    have hc₁S : ∀ i ∈ S₀, v 1 i = u 1 i := fun i hi => by
      have := (hv 1).2 hi; rw [Finset.mem_filter] at this; exact this.2
    set G : Finset F :=
      univ.filter (fun γ : F =>
        mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ) with hGdef
    set Sf : F → Finset ι := fun γ =>
      if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ
        then h.choose else ∅ with hSdef
    set wf : F → ι → F := fun γ =>
      if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ
        then (h.choose_spec.2.1).choose else 0 with hwdef
    have hbound := badCount_udr_le_jointAgreement (ReedSolomon.code α k) (u 0) (u 1)
      (Fintype.card ι - k + 1) t hmd hreg (v 0) (v 1) hc₀C hc₁C S₀ hS₀t hc₀S hc₁S
      G Sf wf ?_ ?_ ?_ ?_
    · exact le_trans (by simpa [hGdef] using hbound) (Nat.sub_le _ _)
    · intro γ hγ
      rw [hGdef, mem_filter] at hγ; have h := hγ.2
      simp only [hSdef, dif_pos h]
      rw [htdef]; exact Nat.ceil_le.mpr (by exact_mod_cast h.choose_spec.1)
    · intro γ hγ
      rw [hGdef, mem_filter] at hγ; have h := hγ.2
      simp only [hwdef, dif_pos h]; exact (h.choose_spec.2.1).choose_spec.1
    · intro γ hγ i hi
      rw [hGdef, mem_filter] at hγ; have h := hγ.2
      simp only [hwdef, dif_pos h]; simp only [hSdef, dif_pos h] at hi
      exact (h.choose_spec.2.1).choose_spec.2 i hi
    · intro γ hγ
      rw [hGdef, mem_filter] at hγ; have h := hγ.2
      simp only [hSdef, dif_pos h]; exact h.choose_spec.2.2
  · push Not at hgt
    refine le_trans (badCount_le_lineCloseCount (ReedSolomon.code α k : Set (ι → F)) δ u) ?_
    have heq : (univ.filter (fun γ : F => δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code α k : Set (ι → F))) ≤ δ))
        = RS_goodCoeffs (deg := k) (domain := α) u δ := by
      rw [RS_goodCoeffs]
    rw [heq]; exact hgt

#print axioms badCount_udr_le
#print axioms epsMCA_rs_udr_le
#print axioms rs_mcaLowerWitness_udr
#print axioms badCount_udr_le_jointAgreement
#print axioms epsMCA_rs_udr_le_full

end ProximityGap.UDRwire
