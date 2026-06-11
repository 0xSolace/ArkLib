/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA

/-!
# Exact preservation of curve decodability under interleaving (issue #334, K5, brick 5)

[Jo26] (ePrint 2026/891) **Theorem 5.7**: if `C` is marked `(ℓ, δ, a, b)`-curve-decodable and
`C(a, b) ≤ q`, then `C^{≡s}` is marked `(ℓ, δ, a, b)`-curve-decodable for every width `s` —
**exact** preservation, no field-size factor. (The paper derives the marked hypothesis from
the [GG25] one via Theorem 5.5; the formal statement here takes the marked hypothesis
directly — what the proof consumes — and gives back the marked conclusion, whose [GG25] form
follows by the proven `curveDecodable_of_marked`.)

Mechanism (formalized clause-for-clause):
* `rowCombine` and **Lemma 5.6** (`relHammingDist_rowCombine_le`): row-combinations do not
  increase relative Hamming distance (the combination is a pointwise map —
  `hammingDist_comp_le_hammingDist`).
* `curveExplainSubmodule` (the paper's `V_B`): the row-combinations `λ` whose projected `f` is
  explained by some base-codeword curve on all of `B` — a subspace (witnesses add and scale).
* **Coverage**: the marked base property applied to each projected instance puts every `λ` in
  `V_B` for some `b`-subset `B` of `A₀`.
* **Properness under failure**: if no interleaved marked witness exists, every `V_B` is proper
  (a full `V_B` reassembles an interleaved witness row-by-row from the standard vectors).
* **The covering contradiction**: at most `C(a, b) ≤ q` proper subspaces cannot cover `F^s`
  ([Jo26] Lemma 3.2, in tree as `exists_nonzero_notMem_of_proper_family`, junk-completed
  along an embedding of the `b`-subsets into `F`).
-/

open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The row-combination of an interleaved word: `(λ · w) i = ∑ k, λ k • w i k`. -/
def rowCombine {s : ℕ} (lam : Fin s → F) (w : ι → Fin s → A) : ι → A :=
  fun i => ∑ k, lam k • w i k

/-- **[Jo26] Lemma 5.6 (projection does not increase distance).** The row-combination is a
pointwise map of the symbol alphabet, so disagreement positions only disappear. -/
theorem relHammingDist_rowCombine_le {s : ℕ} (lam : Fin s → F)
    (x y : ι → Fin s → A) :
    (δᵣ(rowCombine (A := A) lam x, rowCombine (A := A) lam y) : ℚ≥0) ≤ δᵣ(x, y) := by
  unfold Code.relHammingDist
  apply div_le_div_of_nonneg_right ?_ (by positivity) |>.trans_eq rfl
  · exact_mod_cast hammingDist_comp_le_hammingDist
      (fun (_ : ι) (row : Fin s → A) => ∑ k, lam k • row k)

/-- **The explanation subspace `V_B`** ([Jo26] Theorem 5.7's construction): the
row-combinations `λ` for which the projected `f` is explained by some base-codeword curve on
all of `B`. A subspace: witnesses add, scale, and `0` is witnessed by the zero codewords. -/
def curveExplainSubmodule (C : Submodule F (ι → A)) {ℓ s : ℕ}
    (f : F → ι → Fin s → A) (B : Finset F) :
    Submodule F (Fin s → F) where
  carrier := {lam | ∃ h : Fin (ℓ + 1) → ι → A, (∀ j, h j ∈ C) ∧
    ∀ α ∈ B, rowCombine (A := A) lam (f α)
      = fun i => ∑ j : Fin (ℓ + 1), α ^ (j : ℕ) • h j i}
  zero_mem' := by
    refine ⟨0, fun j => C.zero_mem, fun α _ => ?_⟩
    funext i
    simp [rowCombine]
  add_mem' := by
    rintro lam mu ⟨h, hh, hag⟩ ⟨g, hg, hag'⟩
    refine ⟨h + g, fun j => C.add_mem (hh j) (hg j), fun α hα => ?_⟩
    funext i
    have h1 := congrFun (hag α hα) i
    have h2 := congrFun (hag' α hα) i
    simp only [rowCombine, Pi.add_apply] at h1 h2 ⊢
    rw [show (∑ k, (lam k + mu k) • f α i k)
        = (∑ k, lam k • f α i k) + (∑ k, mu k • f α i k) from by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => add_smul _ _ _]
    rw [h1, h2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (smul_add _ _ _).symm
  smul_mem' := by
    rintro c lam ⟨h, hh, hag⟩
    refine ⟨c • h, fun j => C.smul_mem c (hh j), fun α hα => ?_⟩
    funext i
    have h1 := congrFun (hag α hα) i
    simp only [rowCombine] at h1 ⊢
    rw [show (∑ k, (c • lam) k • f α i k) = c • (∑ k, lam k • f α i k) from by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply]
      exact smul_assoc _ _ _]
    rw [h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
    rfl

/-! ### The assembly (Theorem 5.7 proper) — next brick

The remaining assembly — coverage of `F^s` by the `V_B` (via the marked base property on each
`rowCombine`-projected instance and Lemma 5.6), properness of every `V_B` under failure (the
standard vectors reassemble an interleaved witness), and the `C(a,b) ≤ q` covering
contradiction (`exists_nonzero_notMem_of_proper_family`, junk-completed along an embedding of
`A₀.powersetCard b` into `F`) — is fully drafted but currently blocked on a `whnf` divergence
when consuming `MarkedCurveDecodable`'s clauses at the interleaved code `(C : Set _)^⋈ (Fin s)`
(the `CodeInterleavable` projection grinds during unification of the hypothesis instances; the
same membership defeq is fine in `Jo26InterleavingBound.lean`'s direct constructions). The fix
candidates: an `@[reducible]` local alias for the interleaved set, or converting the marked
clauses through `mem_interleavedCode_iff` once at entry. Recorded on issue #334. -/

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.relHammingDist_rowCombine_le
#print axioms ProximityGap.curveExplainSubmodule
