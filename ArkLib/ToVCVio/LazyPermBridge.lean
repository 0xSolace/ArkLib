/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.LazyPermMarginal
import VCVio

/-!
# The lazy permutation oracle — implementations and step distributions

Brick 4 (increment A) of the eager–lazy permutation bridge behind CO25 Lemma 5.8
(`Lemma5_8EagerPaperResidual`): the two implementations of a bidirectional permutation
oracle `(X ⊕ X) →ₒ X` (forward queries on `.inl`, inverse queries on `.inr`), and the
distribution facts for a single lazy step.

* `eagerPermImpl π` — answer through a fixed permutation (the once-sampled carrier);
* `lazyPermImpl` — memoize a growing cache of pairs; answer cache hits deterministically
  and fresh queries by a uniform draw from the unused side (`sampleUnused`, with a junk
  default for the unreachable empty case);
* `evalDist_sampleUnused` — over a duplicate-free nonempty list, `sampleUnused` is the
  uniform distribution on the list's finset, connecting the implementation to the
  chain-rule lemmas of `LazyPermMarginal`.

The master `simulateQ` induction (lazy from a realizable cache ≡ draw a uniform extension
once, then answer eagerly) is increment B.
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace LazyPermBridge

open LazyPermMarginal

variable {X : Type} [DecidableEq X] [Inhabited X]

/-- Answer both directions of the permutation oracle through a fixed permutation. -/
noncomputable def eagerPermImpl (π : Equiv.Perm X) :
    QueryImpl ((X ⊕ X) →ₒ X) ProbComp :=
  fun t => pure (match t with
    | .inl a => π a
    | .inr b => π.symm b)

/-- Uniformly sample an element of a list (junk default on the empty list, which is
unreachable from realizable caches). -/
noncomputable def sampleUnused (xs : List X) : ProbComp X :=
  match xs with
  | [] => pure default
  | y :: ys => ((y :: ys)[·]) <$> $[0..ys.length]

variable [Fintype X]

/-- The unused outputs of a cache, as a list (for sampling). -/
noncomputable def unusedValuesList (c : List (X × X)) : List X := by
  classical
  exact (Finset.univ.filter (fun b : X => b ∉ c.map Prod.snd)).toList

/-- The unused inputs of a cache, as a list (for sampling on inverse queries). -/
noncomputable def unusedKeysList (c : List (X × X)) : List X := by
  classical
  exact (Finset.univ.filter (fun a : X => a ∉ c.map Prod.fst)).toList

/-- The lazy bidirectional permutation oracle: cache hits answer deterministically; fresh
queries draw uniformly from the unused side and record the new pair. -/
noncomputable def lazyPermImpl :
    QueryImpl ((X ⊕ X) →ₒ X) (StateT (List (X × X)) ProbComp) :=
  fun t c =>
    match t with
    | .inl a =>
        match c.find? (fun p => p.1 = a) with
        | some p => pure (p.2, c)
        | none => (fun b => (b, c.concat (a, b))) <$> sampleUnused (unusedValuesList c)
    | .inr b =>
        match c.find? (fun p => p.2 = b) with
        | some p => pure (p.1, c)
        | none => (fun a => (a, c.concat (a, b))) <$> sampleUnused (unusedKeysList c)

section Facts

@[simp] lemma mem_unusedValuesList {c : List (X × X)} {b : X} :
    b ∈ unusedValuesList c ↔ b ∉ c.map Prod.snd := by
  classical
  simp [unusedValuesList]

@[simp] lemma mem_unusedKeysList {c : List (X × X)} {a : X} :
    a ∈ unusedKeysList c ↔ a ∉ c.map Prod.fst := by
  classical
  simp [unusedKeysList]

lemma unusedValuesList_nodup (c : List (X × X)) : (unusedValuesList c).Nodup := by
  classical
  exact Finset.nodup_toList _

lemma unusedKeysList_nodup (c : List (X × X)) : (unusedKeysList c).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- **The lazy step distribution**: over a duplicate-free nonempty list, `sampleUnused` is
the uniform distribution on the list's finset (lifted to the success branch). This connects
the implementation's fresh-query step to the chain rules of `LazyPermMarginal`. -/
theorem evalDist_sampleUnused_run (xs : List X) (hnd : xs.Nodup) (hxs : xs ≠ []) :
    (evalDist (sampleUnused xs)).run
      = (PMF.uniformOfFinset xs.toFinset (by
          simpa [Finset.nonempty_iff_ne_empty, List.toFinset_eq_empty_iff] using hxs)).map
            some := by
  classical
  rcases xs with _ | ⟨y, ys⟩
  · exact absurd rfl hxs
  · ext o
    rcases o with _ | x
    · -- failure mass is zero on both sides
      have hfail : Pr[⊥ | sampleUnused (y :: ys)] = 0 := by
        simp [sampleUnused]
      rw [show ((evalDist (sampleUnused (y :: ys))).run none)
          = Pr[⊥ | sampleUnused (y :: ys)] from rfl, hfail]
      rw [PMF.map_apply]
      refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
      simp
    · -- success mass: `count/length = 1/card` for a duplicate-free list
      have hout : ((evalDist (sampleUnused (y :: ys))).run (some x))
          = Pr[= x | sampleUnused (y :: ys)] := rfl
      rw [hout]
      have hcount : Pr[= x | sampleUnused (y :: ys)]
          = ((y :: ys).count x : ℝ≥0∞) / (y :: ys).length := by
        show Pr[= x | ((y :: ys)[·]) <$> $[0..ys.length]] = _
        rw [List.count, ← List.countP_eq_sum_fin_ite]
        simp [probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]
      rw [hcount, PMF.map_apply]
      refine Eq.trans ?_ (tsum_eq_single x
        (fun b hb => if_neg (fun h => hb (Option.some_inj.mp h).symm))).symm
      rw [if_pos rfl]
      by_cases hx : x ∈ (y :: ys)
      · rw [PMF.uniformOfFinset_apply_of_mem (hs := ⟨y, by simp⟩)
            (List.mem_toFinset.mpr hx),
          List.count_eq_one_of_mem hnd hx, List.toFinset_card_of_nodup hnd]
        simp [ENNReal.div_eq_inv_mul]
      · rw [PMF.uniformOfFinset_apply_of_notMem (hs := ⟨y, by simp⟩)
            (fun h => hx (List.mem_toFinset.mp h)),
          List.count_eq_zero_of_not_mem hx]
        simp

end Facts

end LazyPermBridge

/-! ## Axiom audit — kernel-clean. -/
#print axioms LazyPermBridge.evalDist_sampleUnused_run
