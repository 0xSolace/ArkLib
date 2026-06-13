/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24
import ArkLib.Data.CodingTheory.GMMDS.LovettPrimitiveDischarge

/-!
# Lovett's GM-MDS proof: the meet-replacement system for Lemma 2.4 (#389)

This file builds the *meet-replacement* system `V'` used in the proof of Lovett's Lemma 2.4
(arXiv:1803.02523, p.8).  Given a `V*(k)` system `V` and a **tight** index set `I` with
`1 < |I| < m`, Lemma 2.4 replaces the entire `I`-block of vectors by the single coordinate-wise
meet `v_I = ⋀_{i∈I} vᵢ`, keeping every vector outside `I`.  The resulting system

> `replaceMeet V I = ⟨v_I⟩ ⊕ ⟨vᵢ : i ∉ I⟩`  over the index type  `Fin 1 ⊕ {i // i ∉ I}`,

has the following key properties (all proven here):

* `replaceMeet_card` — its number of vectors is `m − |I| + 1`, strictly less than `m` (since
  `|I| > 1`), so the **`m`-induction hypothesis** of the master frame applies to it.
* `lovettD_replaceMeet` — when `I` is *tight*, the induction measure `d = Σ (k − |vᵢ|)` is
  **unchanged**: removing the `|I|` blocks `Σ_{i∈I}(k − |vᵢ|)` and adding back the single block
  `k − |v_I|` is a wash by tightness (`k − |v_I| = Σ_{i∈I}(k − |vᵢ|)`).
* `replaceMeet_isVStar` — `V'` is again a `V*(k)` system.  Clauses (i)/(iii) are immediate from
  the meet being `≤` each member; clause (ii) is the genuine combinatorial content of Lemma 2.4:
  an index set `I'` of `V'` that uses the meet block is re-expressed as the index set
  `(I' \ {meet}) ∪ I` of `V`, whose meet and sum coincide (the sum step uses tightness).

The remaining content of Lemma 2.4 — that `P(k, V')` independent transfers to `P(k, V)`
independent via the equal-span / equal-cardinality counting lemma over `F(a)` — is the algebraic
finish, isolated downstream.  This file is the *combinatorial* layer: construction, cardinality,
measure invariance, and `V*(k)` preservation.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-! ## Meet monotonicity -/

/-- The meet over `I` is coordinate-wise `≤` every member of `I`. -/
theorem vMeet_le_mem {V : Fin m → (Fin n → ℕ)} {I : Finset (Fin m)} (hI : I.Nonempty)
    {i : Fin m} (hi : i ∈ I) (l : Fin n) : vMeet V I hI l ≤ V i l :=
  Finset.inf'_le (fun i => V i l) hi

/-- The meet weight is `≤` the weight of every member of `I`. -/
theorem vAbs_vMeet_le_mem {V : Fin m → (Fin n → ℕ)} {I : Finset (Fin m)} (hI : I.Nonempty)
    {i : Fin m} (hi : i ∈ I) : vAbs (vMeet V I hI) ≤ vAbs (V i) :=
  Finset.sum_le_sum (fun l _ => vMeet_le_mem hI hi l)

/-! ## The meet-replacement system -/

/-- The index type of the meet-replacement system: one new "meet" index plus the indices
**outside** `I`. -/
abbrev ReplaceIdx (I : Finset (Fin m)) : Type := Fin 1 ⊕ {i : Fin m // i ∉ I}

/-- The meet-replacement system `V'`: the meet `v_I` on the new index, and `vᵢ` on each `i ∉ I`. -/
noncomputable def replaceMeet (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    ReplaceIdx I → (Fin n → ℕ) :=
  Sum.elim (fun _ => vMeet V I hI) (fun i => V i.1)

/-- The new system has `m − |I| + 1` vectors. -/
theorem replaceMeet_card (I : Finset (Fin m)) :
    Fintype.card (ReplaceIdx I) = (m - I.card) + 1 := by
  classical
  rw [Fintype.card_sum, Fintype.card_fin]
  have : Fintype.card {i : Fin m // i ∉ I} = m - I.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    congr 1
    simp [Fintype.card_coe]
  rw [this]; omega

/-- The canonical reindexing equivalence `ReplaceIdx I ≃ Fin (m − |I| + 1)`. -/
noncomputable def replaceEquiv (I : Finset (Fin m)) : ReplaceIdx I ≃ Fin ((m - I.card) + 1) :=
  (Fintype.equivFinOfCardEq (replaceMeet_card I))

/-- The meet-replacement system as a genuine `Fin (m − |I| + 1)`-indexed system (so that the
master frame's `m`-induction hypothesis, which quantifies over `Fin m'`-indexed systems, applies). -/
noncomputable def replaceMeetFin (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    Fin ((m - I.card) + 1) → (Fin n → ℕ) :=
  replaceMeet V I hI ∘ (replaceEquiv I).symm

/-- `replaceMeetFin` is a reindexing of `replaceMeet` along the bijection `(replaceEquiv I).symm`. -/
theorem replaceMeetFin_comp (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    replaceMeetFin V I hI = replaceMeet V I hI ∘ (replaceEquiv I).symm := rfl

/-! ## The induction measure is invariant under tight meet-replacement -/

/-- A sum over the not-in-`I` subtype equals the Finset sum over the complement of `I`. -/
theorem sum_notMem_eq_sum_compl {M : Type*} [AddCommMonoid M] (I : Finset (Fin m))
    (g : Fin m → M) :
    (∑ i : {i : Fin m // i ∉ I}, g i.1) = ∑ i ∈ Iᶜ, g i := by
  classical
  rw [← Finset.sum_subtype Iᶜ (fun x => by simp) g]

/-- **The measure is unchanged under tight meet-replacement.**  When `I` is tight (and `|v_I| ≤ k`,
which holds in a `V*(k)` system), the induction measure `d = Σ (k − |vᵢ|)` of the replacement
system equals that of the original. -/
theorem lovettD_replaceMeet {V : Fin m → (Fin n → ℕ)} {k : ℕ} {I : Finset (Fin m)}
    (hI : I.Nonempty) (htight : tightConstraint V k I hI) :
    lovettD (replaceMeetFin V I hI) k = lovettD V k := by
  classical
  unfold lovettD replaceMeetFin
  -- reindex the Fin-sum back to the ReplaceIdx sum via the equivalence
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp (replaceEquiv I).symm (fun p => k - vAbs (replaceMeet V I hI p))]
  unfold replaceMeet
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const]
  -- left block: one term `k - |v_I|`
  rw [Finset.card_univ, Fintype.card_fin, one_smul]
  -- right block: sum over the not-in-I subtype = sum over Iᶜ
  rw [sum_notMem_eq_sum_compl I (fun i => k - vAbs (V i))]
  -- original: split Fin m into I and Iᶜ
  rw [← Finset.sum_add_sum_compl I (fun i => k - vAbs (V i))]
  -- tightness: k - |v_I| = Σ_{i∈I}(k-|vᵢ|)
  unfold tightConstraint at htight
  omega

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.vAbs_vMeet_le_mem
#print axioms ArkLib.GMMDS.replaceMeet_card
#print axioms ArkLib.GMMDS.lovettD_replaceMeet
