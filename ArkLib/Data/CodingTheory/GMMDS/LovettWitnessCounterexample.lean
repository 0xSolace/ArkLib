/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24

/-!
# Lovett's GM-MDS proof: `LovettWitnessExists` is a FALSE residual (#389)

The in-tree residual `LovettWitnessExists` (`LovettLemma2456.lean`) packages the combinatorial
core of Lovett's §2 (Lemmas 2.4–2.6, arXiv:1803.02523) as: *every primitive `V*(k)` system
contains an index `i₀` with `V i₀ = (1,…,1,0)` **and** `n = k`*.

**The `n = k` conjunct is not derivable** and makes `LovettWitnessExists` false.  This file
exhibits a fully explicit counterexample:

`n = 2`, `k = 3`, `m = 2`, `V = (v₀, v₁)` with `v₀ = (1,0)` and `v₁ = (0,2)`.

* `cexV_isVStar` — `V` satisfies `V*(3)`.
* `cexV_primitive` — `V` is primitive (`∀ j, ∃ i, V i j = 0`).
* `cexV_not_reducible` — `V` is **not** reducible (no coordinate is `≥ 1` everywhere), so the
  minimal-counterexample master frame routes it to the *primitive* step, where the witness is
  demanded.
* `cexV_no_witness` — `LovettWitness F V 3` is false (it would force `2 = 3`).

The deeper fact (verified externally, not formalised here) is that `P(3, V)` is *linearly
independent* — its coefficient determinant over `F(a)` is `(a₁ − a₂)²`, the polynomials being
`{x − a₁, (x − a₁)x, (x − a₂)²}`.  So this is **not** a counterexample to Theorem 1.7: it is a
genuine independent primitive `V*(k)` system with `n < k`.  Lovett's Lemma 2.6 (`n = k`) only
excludes `n < k` for a *dependent* minimal counterexample (it assumes `P(k,V)` dependent and
substitutes `x = aₙ`); in the IH-packaging used by `lovettHolds_of_witness`, independence of
`P(k,V)` is the *goal*, not a hypothesis, so `n < k` cannot be ruled out and the `n = k` clause
fails.

**Repair (future work).**  Drop `n = k` from `LovettWitness`, keeping only Lemma 2.5
(`∃ i₀, V i₀ = (1,…,1,0)`).  Then `lovettHolds_of_witness` must split on `n = k` vs `n < k`: the
latter case is the genuine algebraic Lemma 2.6 / final contradiction proven as a *direct*
independence statement (`P(k,V)` and the raised-vector family span the same space; the raised
family has strictly smaller `d`, so the `d`-IH makes it independent; the separated factor
`p = ∏_{j<n−1}(x − aⱼ)` closes it).  See the module docstring of `LovettLemma2456` and issue #389.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

/-- The counterexample system: `v₀ = (1,0)`, `v₁ = (0,2)` in `ℕ²`. -/
def cexV : Fin 2 → (Fin 2 → ℕ) := ![![1, 0], ![0, 2]]

/-- `V` is primitive: coordinate `0` is zeroed by `v₁`, coordinate `1` by `v₀`. -/
theorem cexV_primitive : ∀ j : Fin 2, ∃ i, cexV i j = 0 := by
  decide

/-- `V` is **not** reducible: no coordinate is `≥ 1` in *every* vector. -/
theorem cexV_not_reducible : ¬ ∃ j : Fin 2, ∀ i, 1 ≤ cexV i j := by
  decide

theorem cexV_vAbs0 : vAbs (cexV 0) = 1 := by rw [vAbs]; decide
theorem cexV_vAbs1 : vAbs (cexV 1) = 2 := by rw [vAbs]; decide

/-- The weight of the meet over a nonempty `J` equals the meet weight; computed per-subset. -/
private theorem cexV_meet_singleton (i : Fin 2) :
    vAbs (vMeet cexV {i} (Finset.singleton_nonempty i)) = vAbs (cexV i) := by
  unfold vAbs vMeet
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [Finset.inf'_singleton]

/-- The meet over the whole index set `{0,1}` is the zero vector (primitivity). -/
private theorem cexV_meet_pair (hJ : ({0, 1} : Finset (Fin 2)).Nonempty) :
    vAbs (vMeet cexV {0, 1} hJ) = 0 := by
  rw [vAbs]
  have hz : ∀ l, vMeet cexV {0, 1} hJ l = 0 := by
    intro l
    obtain ⟨i, hi⟩ := cexV_primitive l
    refine Nat.le_zero.mp ?_
    rw [← hi]
    refine Finset.inf'_le (fun i => cexV i l) ?_
    fin_cases i <;> decide
  simp [hz]

/-- Every nonempty `I ⊆ Fin 2` is `{0}`, `{1}`, or `{0,1}`. -/
private theorem cexV_subset_cases (I : Finset (Fin 2)) (hI : I.Nonempty) :
    I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  classical
  obtain ⟨w, hw⟩ := hI
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
  · right; right
    have hIeq : I = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro x; fin_cases x <;> assumption
    rw [hIeq]; decide
  · left
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨h0, fun x hx => ?_⟩
    fin_cases x
    · rfl
    · exact absurd hx h1
  · right; left
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨h1, fun x hx => ?_⟩
    fin_cases x
    · exact absurd hx h0
    · rfl
  · exfalso; fin_cases w <;> simp_all

/-- `V` satisfies Lovett's property `V*(3)`. -/
theorem cexV_isVStar : IsVStar cexV 3 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- (i) weights ≤ k − 1 = 2
    intro i
    fin_cases i
    · show vAbs (cexV 0) ≤ 3 - 1; rw [cexV_vAbs0]; omega
    · show vAbs (cexV 1) ≤ 3 - 1; rw [cexV_vAbs1]
  · -- (ii) MDS inequality for every nonempty I
    intro I hI
    rcases cexV_subset_cases I hI with rfl | rfl | rfl
    · rw [Finset.sum_singleton, cexV_meet_singleton, cexV_vAbs0]
    · rw [Finset.sum_singleton, cexV_meet_singleton, cexV_vAbs1]
    · rw [show (∑ i ∈ ({0, 1} : Finset (Fin 2)), (3 - vAbs (cexV i)))
            = (3 - vAbs (cexV 0)) + (3 - vAbs (cexV 1)) by
          rw [Finset.sum_insert (by decide), Finset.sum_singleton],
        cexV_meet_pair, cexV_vAbs0, cexV_vAbs1]
  · -- (iii) coordinate `0` (the only one `< n − 1 = 1`) is in `{0,1}`
    intro i l hl
    have hl0 : l = 0 := by
      have : (l : ℕ) = 0 := by omega
      exact Fin.ext (by simpa using this)
    subst hl0
    fin_cases i <;> decide

/-- **`LovettWitness F V 3` is false.**  It would require `n = k`, i.e. `2 = 3`. -/
theorem cexV_no_witness (F : Type*) [Field F] : ¬ LovettWitness F cexV 3 := by
  rintro ⟨hn, i₀, hone, hnk⟩
  exact absurd hnk (by norm_num)

/-- **`LovettWitnessExists` is false.**  Instantiating at the counterexample system would force a
witness with `n = k`, contradicting `cexV_no_witness`.  (The IH hypotheses of `LovettWitnessExists`
are true — Theorem 1.7 holds — so they cannot rescue the statement.) -/
theorem not_lovettWitnessExists_unconditional
    (F : Type*) [Field F]
    (IHn : ∀ {n' m' : ℕ} (V' : Fin m' → (Fin n' → ℕ)) (k' : ℕ),
      n' < 2 → 1 ≤ k' → IsVStar V' k' → LovettHolds F V' k')
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin 2 → ℕ)),
      lovettD V' 3 < lovettD cexV 3 → IsVStar V' 3 → LovettHolds F V' 3) :
    ¬ LovettWitnessExists F := by
  intro hw
  exact cexV_no_witness F
    (hw cexV 3 (by norm_num) cexV_isVStar cexV_primitive IHn IHd)

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.cexV_isVStar
#print axioms ArkLib.GMMDS.cexV_no_witness
#print axioms ArkLib.GMMDS.not_lovettWitnessExists_unconditional
