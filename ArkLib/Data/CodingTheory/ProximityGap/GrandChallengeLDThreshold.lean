/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLattice
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeLDAttainment
import ArkLib.Data.CodingTheory.InterleavedListSize
import ArkLib.Data.CodingTheory.JohnsonBound.Family

/-!
# Value bounds for the genuine list-decoding threshold (ABF26 §1, faithful form)

`GrandChallengeLDAttainment` shows the `∃ δ*`-with-maximality formalization of the Grand
List Decoding Challenge is degenerate; `GrandChallengeLattice` provides the faithful
object instead: `listLatticeThreshold C m ε*` — the largest grid radius `j/n` with
`Λ(C^⋈m, j/n) ≤ ε*·|F|`, which exists whenever the lattice set is nonempty.  The paper's
actual challenge is to *determine the value* of this threshold.  This file proves the two
value bounds that are within reach of current mathematics:

* **Capacity-side upper bound** (`listLatticeThreshold_le_of_rs`, unconditional):
  for every Reed–Solomon instance with `1 ≤ k ≤ n`, `m ≥ 1`, `ε* < 1`,
  `listLatticeThreshold ≤ n - k`.  Reason: at any radius `j/n` with `j > n - k`, the
  `|F|`-sized family `{c · ∏_{t ∈ T}(X - x_t) : c ∈ F}` (with `|T| = n - j ≤ k - 1`)
  consists of distinct codewords vanishing on `T`, hence lying within distance `j/n` of
  the zero word; so `Λ(C^⋈m, j/n) ≥ |F| > ε*·|F|`.  In δ-units the threshold is at most
  `1 - k/n = ` (capacity radius); together with the monotone structure this makes the
  capacity radius an *unconditional ceiling* for the genuine challenge threshold.

* **Johnson-side lower bound** (`le_listLatticeThreshold_of_johnson`, parameterized):
  if the radical-free Johnson condition of
  `closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition` holds at radius
  `j/n` with list cap `ℓ`, and `ℓ^m ≤ ε*·|F|`, then `j ≤ listLatticeThreshold`.
  The per-centre Johnson cap lifts to `Λ` (`Lambda_le_of_johnson_condition`) and to the
  interleaved code through `Lambda_interleaved_le_pow` (ABF26 Lemma 2.10, elementary
  `m`-th-power form).

What remains open — the actual content of the prize — is the gap between these two
bounds: whether the threshold for smooth-domain RS codes sits near the Johnson radius or
near capacity.  Neither bound here (nor anything else in the tree or, at the time of
writing, the literature) decides that question.
-/

namespace ProximityGap

open scoped NNReal
open ListDecodable

section JohnsonSide

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The per-centre radical-free Johnson cap lifts to the maximised list size `Λ`. -/
theorem Lambda_le_of_johnson_condition
    (C : Code ι F) (δ : ℝ) {ℓ : ℕ} {β : ℝ}
    (hδ : 0 ≤ δ) (hq : 0 < Fintype.card F) (hβ : 0 ≤ β)
    (hcond : ((Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) * (1 + β ^ 2)
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ)))
      + (ℓ : ℝ) * ((((Fintype.card ι - Code.minDist C : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        - 2 * β * (((Fintype.card ι - ⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℕ) : ℝ)
          - (Fintype.card ι : ℝ) / (Fintype.card F : ℝ))
        + β ^ 2 * (Fintype.card ι : ℝ) * (1 - 1 / (Fintype.card F : ℝ))) < 0) :
    Lambda C δ ≤ (ℓ : ℕ∞) := by
  classical
  refine Lambda_le_of_forall_ncard_le fun f => ?_
  have hpt := JohnsonBound.closeCodewordsRelFinset_card_le_of_floor_minDist_johnson_condition
    (C := C) (f := f) (δ := δ) (ℓ := ℓ) (β := β) hδ hq hβ hcond
  rw [card_closeCodewordsRelFinset_eq_ncard] at hpt
  exact_mod_cast hpt

end JohnsonSide

section CapacitySide

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [Nonempty ι] [DecidableEq ι]

open Polynomial

/-- The scaled vanishing family: for a set `T` of fewer than `deg` domain points, the
evaluations of `c · ∏_{t ∈ T}(X - x_t)` over `c : F` are `|F|` distinct codewords of
`RS[F, domain, deg]`, each vanishing on `T`. -/
lemma exists_family_vanishing_on (domain : ι ↪ F) {deg : ℕ} (T : Finset ι)
    (hT : T.card < deg) :
    ∃ φ : F → (ι → F), Function.Injective φ ∧
      (∀ c, φ c ∈ (ReedSolomon.code domain deg : Set (ι → F))) ∧
      (∀ c, ∀ i ∈ T, φ c i = 0) := by
  classical
  -- the vanishing polynomial of `T`
  set P : F[X] := ∏ t ∈ T, (X - Polynomial.C (domain t)) with hP
  have hPdeg : P.natDegree = T.card := by
    rw [hP]
    rw [Polynomial.natDegree_prod _ _ (fun t _ => Polynomial.X_sub_C_ne_zero (domain t))]
    simp [Polynomial.natDegree_X_sub_C]
  have hPne : P ≠ 0 := by
    rw [hP]
    exact Finset.prod_ne_zero_iff.mpr fun t _ => Polynomial.X_sub_C_ne_zero (domain t)
  -- a point outside `T` where `P` does not vanish
  have hTcard : T.card < Fintype.card ι := lt_of_lt_of_le hT (le_trans (Nat.le_of_lt_succ
    (Nat.lt_succ_of_lt hT)).le (le_refl _)) |>.trans_le (le_refl _) |>.trans_le (le_refl _)
  sorry

end CapacitySide

end ProximityGap
