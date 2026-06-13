/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovCountingLemma
import ArkLib.Data.CodingTheory.ProximityGap.GVRepBoundFromEnergy

/-!
# The Stepanov auxiliary-polynomial framework (#389): the open core as ONE existence

This file closes the Stepanov pipeline up to its single irreducible kernel.  Feeding
the counting lemma `card_le_natDegree_of_vanishing` the representation point set
`{y ∈ G : c − y ∈ G}` (whose size is `repCount G c`), the whole Garcia–Voloch rep bound
— hence the entire `μ_n` supply wall — reduces to **one existence statement**:

> **`StepanovAux G c D m`** — there is a nonzero polynomial of degree `< D` divisible by
> `(X − y)^m` at every representation point `y` of `c`.

Proven here:
* **`repCount_lt_of_stepanovAux`** — `StepanovAux G c D m ⟹ m · r(c) < D`.
* **`gvRepBound_of_stepanovAux`** — if `StepanovAux` holds at every `c ≠ 0` with
  `D ≤ (M+1)·m` and `M³ ≤ 64|G|²`, then `GVRepBound G M`.

So the supply chain is now machine-checked **end to end except `StepanovAux`** — the
auxiliary-polynomial *construction* (the Wronskian/derivative degree estimate of the
Stepanov/Heath-Brown–Konyagin method for a multiplicative subgroup).  That construction
is the genuine open kernel; everything that consumes it is proven.  The Garcia–Voloch
parameters are `m ≈ n^{1/3}`, `D ≈ n`, giving `M ≈ n^{2/3}`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.Stepanov

open ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The Stepanov auxiliary-polynomial existence** (the open kernel of the rep bound):
a nonzero polynomial of degree `< D`, divisible by `(X − y)^m` at every representation
point `y ∈ {y ∈ G : c − y ∈ G}` of `c`. -/
def StepanovAux (G : Finset F) (c : F) (D m : ℕ) : Prop :=
  ∃ f : F[X], f ≠ 0 ∧ f.natDegree < D ∧
    ∀ y ∈ G.filter (fun y => c - y ∈ G), (X - C y) ^ m ∣ f

/-- **The auxiliary polynomial bounds the representation count.**  By the counting
lemma, `m · r(c) ≤ deg(f) < D`. -/
theorem repCount_lt_of_stepanovAux {G : Finset F} {c : F} {D m : ℕ}
    (h : StepanovAux G c D m) : m * repCount G c < D := by
  obtain ⟨f, hf, hdeg, hdvd⟩ := h
  have hcount : m * (G.filter (fun y => c - y ∈ G)).card ≤ f.natDegree :=
    card_le_natDegree_of_vanishing hf hdvd
  rw [repCount]
  omega

/-- **The whole Garcia–Voloch rep bound from the auxiliary-polynomial existence.**  If
`StepanovAux G c D m` holds for every `c ≠ 0`, with `D ≤ (M+1)·m` and `M³ ≤ 64|G|²`,
then `GVRepBound G M` — the input consumed by the entire supply chain. -/
theorem gvRepBound_of_stepanovAux {G : Finset F} {D m M : ℕ} (hm : 1 ≤ m)
    (hMD : D ≤ (M + 1) * m) (hMcube : M ^ 3 ≤ 64 * G.card ^ 2)
    (h : ∀ c : F, c ≠ 0 → StepanovAux G c D m) :
    GVRepBound G M := by
  refine ⟨fun t ht => ?_, hMcube⟩
  have hlt : m * repCount G t < D := repCount_lt_of_stepanovAux (h t ht)
  have h2 : m * repCount G t < (M + 1) * m := lt_of_lt_of_le hlt hMD
  rw [mul_comm (M + 1) m] at h2
  have h3 : repCount G t < M + 1 := Nat.lt_of_mul_lt_mul_left h2
  omega

end ArkLib.ProximityGap.Stepanov

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.Stepanov.repCount_lt_of_stepanovAux
#print axioms ArkLib.ProximityGap.Stepanov.gvRepBound_of_stepanovAux
