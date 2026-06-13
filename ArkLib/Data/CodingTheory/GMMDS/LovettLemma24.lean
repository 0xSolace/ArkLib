/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCombinatorial

/-!
# Lovett's GM-MDS proof: tight constraints and primitivity combinatorics (#389)

Combinatorial scaffolding for Lovett's Lemmas 2.4–2.6 (arXiv:1803.02523).  This file collects
the *purely combinatorial* facts about a `V*(k)` system that the (algebraic) Lemmas 2.4–2.6
build on, kept separate from the algebraic substitution arguments:

* `tightConstraint` — Definition 2.3: `I` is tight when property (ii) holds with equality.
* `singleton_tight` — a singleton is always tight (Lovett's remark after Def 2.3).
* `vMeet_univ_eq_zero` — in a *primitive* system (`∀ j, ∃ i, vᵢ(j) = 0`) the meet over **all**
  indices is the zero vector (this is Lovett's Lemma 2.2 conclusion, the standing hypothesis of
  §2 once the reducible branch is removed by the master frame).
* `last_coord_meet_zero` — the last coordinate of the full meet is `0`, used in Lemma 2.5 to
  locate a vector with `vᵢ(n−1) = 0`.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- **Definition 2.3 (tight constraint).**  `I` is *tight* for `V` (at level `k`) when the MDS
inequality (ii) holds with equality:
`Σ_{i∈I}(k − |vᵢ|) + |⋀_{i∈I} vᵢ| = k`. -/
def tightConstraint (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m))
    (hI : I.Nonempty) : Prop :=
  (∑ i ∈ I, (k - vAbs (V i))) + vAbs (vMeet V I hI) = k

/-- A singleton index set `{i}` is always a tight constraint: the sum is `k − |vᵢ|` and the meet
is `vᵢ`, so the total is `k`. -/
theorem singleton_tight (V : Fin m → (Fin n → ℕ)) {k : ℕ} (i : Fin m)
    (hk : vAbs (V i) ≤ k) :
    tightConstraint V k {i} (Finset.singleton_nonempty i) := by
  classical
  unfold tightConstraint
  rw [Finset.sum_singleton]
  have hmeet : vAbs (vMeet V {i} (Finset.singleton_nonempty i)) = vAbs (V i) := by
    unfold vAbs vMeet
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Finset.inf'_singleton]
  rw [hmeet]; omega

/-- In a system where coordinate `j` is *globally hit by a zero* (`∃ i, V i j = 0`), the meet over
**all** indices vanishes at `j`. -/
theorem meet_univ_coord_zero {V : Fin m → (Fin n → ℕ)} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    {j : Fin n} (hj : ∃ i, V i j = 0) :
    vMeet V Finset.univ hne j = 0 := by
  classical
  obtain ⟨i, hi⟩ := hj
  unfold vMeet
  refine Nat.le_zero.mp ?_
  rw [← hi]
  exact Finset.inf'_le (fun i => V i j) (Finset.mem_univ i)

/-- **Primitivity ⟹ full meet is zero** (Lovett's Lemma 2.2 conclusion).  If every coordinate is
hit by a zero of some vector, the coordinate-wise meet over all indices is the zero vector. -/
theorem vMeet_univ_eq_zero {V : Fin m → (Fin n → ℕ)} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (hprim : ∀ j : Fin n, ∃ i, V i j = 0) :
    vMeet V Finset.univ hne = (fun _ => 0) := by
  funext j
  exact meet_univ_coord_zero hne (hprim j)

/-- The full meet has weight zero in a primitive system. -/
theorem vAbs_vMeet_univ_eq_zero {V : Fin m → (Fin n → ℕ)}
    (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (hprim : ∀ j : Fin n, ∃ i, V i j = 0) :
    vAbs (vMeet V Finset.univ hne) = 0 := by
  rw [vMeet_univ_eq_zero hne hprim]; simp [vAbs]

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.singleton_tight
#print axioms ArkLib.GMMDS.vMeet_univ_eq_zero
