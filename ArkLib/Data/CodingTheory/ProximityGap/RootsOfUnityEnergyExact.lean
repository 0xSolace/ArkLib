/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic

/-!
# The EXACT additive energy of the roots of unity (#389, the sharp value)

The sibling energy probes (`probe_split_energy.py`, `probe_energy_doubling.py`) found that the
split-case additive energy of `μ_n` (`n = 2^m`) is **exactly** `3n² − 3n = 3·n·(n−1)` — the
"char-0 level" value, strictly below the `n^{8/3}` that a loose Garcia–Voloch / HBK Stepanov
bound would give, and below even the `≤ 3n²` that the in-tree `unitCircle_additiveEnergy_le` /
`additiveEnergy_le_of_dvd_succ` bounds establish.  This file proves that sharp value **exactly**,
reduced to a single clean combinatorial hypothesis.

`rootsOfUnity_additiveEnergy_eq`: if `S` (the role of `μ_n`) is closed under negation, avoids `0`,
sits in characteristic `≠ 2`, and has **no nontrivial additive coincidence** — every
representation `y + ((a+b)−y)` of a *nonzero* value `a+b` has `y ∈ {a,b}` (`hnc`) — then

  `∑_{a,b ∈ S} |{y ∈ S : (a+b) − y ∈ S}|  =  3·n·(n−1)`,   `n = |S|`.

This is the exact additive energy.  The point: it converts the *analytic* sharp-energy target
`E ≤ Cn²` (the redirected open core of the proximity-prize split case) into the *exact* identity
`E = 3n(n−1)`, conditional on the clean Diophantine statement `hnc` — which is precisely the
"`r(s) ≤ 2` with reps `{a,b}`" structure.  Any proof of `hnc` (the char-0 / inert Frobenius
`x ↦ x^{-1}` route discharges it; the split case is the genuine Weil-strength residual) yields the
exact energy verbatim.  Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap

variable {F : Type*} [Field F] [DecidableEq F]
/-- **The exact additive energy of a negation-closed Sidon-to-zero set** (the roots-of-unity
energy `E(μ_n) = 3n(n−1)`). Under the hypotheses that `S` is closed under negation, avoids `0`,
char ≠ 2, and has *no nontrivial additive coincidence* (`hnc`: a representation `y + ((a+b)−y)`
of a nonzero `a+b` forces `y ∈ {a,b}`), the additive energy is exactly `3·n·(n−1)`. -/
theorem rootsOfUnity_additiveEnergy_eq (S : Finset F) (n : ℕ) (hn : S.card = n)
    (hneg : ∀ x ∈ S, -x ∈ S) (h0 : (0 : F) ∉ S) (hchar : (2 : F) ≠ 0)
    (hnc : ∀ a ∈ S, ∀ b ∈ S, a + b ≠ 0 → ∀ y ∈ S, (a + b) - y ∈ S → y = a ∨ y = b) :
    ∑ a ∈ S, ∑ b ∈ S, (S.filter (fun y => (a + b) - y ∈ S)).card = 3 * n * (n - 1) := by
  classical
  have inner : ∀ a ∈ S, ∑ b ∈ S, (S.filter (fun y => (a + b) - y ∈ S)).card = 3 * (n - 1) := by
    intro a ha
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
    have hna : -a ∈ S := hneg a ha
    have haa : a + a ≠ 0 := by
      intro h; rw [← two_mul] at h
      rcases mul_eq_zero.mp h with h2 | ha'
      · exact hchar h2
      · exact ha0 ha'
    have hane : -a ≠ a := by
      intro h
      apply haa
      have e1 : a + a = -a + a := by rw [h]
      rw [e1, neg_add_cancel]
    -- c(a, -a) = n  (filter is all of S)
    have cneg : (S.filter (fun y => (a + -a) - y ∈ S)).card = n := by
      rw [Finset.filter_true_of_mem (fun y hy => by rw [add_neg_cancel, zero_sub]; exact hneg y hy), hn]
    -- c(a, a) = 1  (filter is {a})
    have csame : (S.filter (fun y => (a + a) - y ∈ S)).card = 1 := by
      have : S.filter (fun y => (a + a) - y ∈ S) = {a} := by
        apply Finset.ext; intro y
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hyS, hyr⟩
          rcases hnc a ha a ha haa y hyS hyr with h | h <;> exact h
        · rintro rfl; exact ⟨ha, by rw [add_sub_cancel_right]; exact ha⟩
      rw [this, Finset.card_singleton]
    -- c(a, b) = 2 for b ∉ {-a, a}
    have cgen : ∀ b ∈ (S.erase (-a)).erase a,
        (S.filter (fun y => (a + b) - y ∈ S)).card = 2 := by
      intro b hb
      rw [Finset.mem_erase, Finset.mem_erase] at hb
      obtain ⟨hba, hbna, hbS⟩ := hb
      have hab : a + b ≠ 0 := by
        intro h; exact hbna (by rw [eq_neg_of_add_eq_zero_right h])
      have : S.filter (fun y => (a + b) - y ∈ S) = {a, b} := by
        apply Finset.ext; intro y
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hyS, hyr⟩; exact hnc a ha b hbS hab y hyS hyr
        · rintro (rfl | rfl)
          · exact ⟨ha, by rw [add_sub_cancel_left]; exact hbS⟩
          · exact ⟨hbS, by rw [add_sub_cancel_right]; exact ha⟩
      rw [this, Finset.card_insert_of_notMem (by simp [Ne.symm hba]), Finset.card_singleton]
    -- assemble the inner sum by peeling -a then a
    rw [← Finset.add_sum_erase S (fun b => (S.filter (fun y => (a + b) - y ∈ S)).card) hna]
    rw [← Finset.add_sum_erase (S.erase (-a))
          (fun b => (S.filter (fun y => (a + b) - y ∈ S)).card)
          (Finset.mem_erase.mpr ⟨Ne.symm hane, ha⟩)]
    rw [cneg, csame, Finset.sum_congr rfl cgen, Finset.sum_const, smul_eq_mul]
    have hcard : ((S.erase (-a)).erase a).card = n - 2 := by
      have h1 := Finset.card_erase_of_mem hna
      have h2 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hane, ha⟩)
      rw [hn] at h1
      omega
    rw [hcard]
    have hn2 : 2 ≤ n := by
      rw [← hn]
      have : ({-a, a} : Finset F) ⊆ S := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl; exacts [hna, ha]
      calc 2 = ({-a, a} : Finset F).card := by rw [Finset.card_insert_of_notMem (by simp [hane]), Finset.card_singleton]
        _ ≤ S.card := Finset.card_le_card this
    omega
  rw [Finset.sum_congr rfl inner, Finset.sum_const, hn, smul_eq_mul]
  ring

end ArkLib.ProximityGap
