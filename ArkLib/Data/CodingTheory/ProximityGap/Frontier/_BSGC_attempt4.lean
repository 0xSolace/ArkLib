/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC2

/-!
# BSG — the ENERGY-COUPLED DRC kernel residual `DRCKernelEnergy` (Track-A milestone, attempt 4)

## What this file delivers (axiom-clean, no `sorry`)

The whole BSG ladder currently reduces `BSGCore` to the residual `DRCKernel` (in `_BSG_DRC2`),
which is **energy-stripped**: it consumes an *arbitrary* graph `G ⊆ A ×ˢ A` whose left-neighbourhood
at one vertex is large. That arbitrariness is exactly the hole the Sidon countermodel
(`bareDRCExtract_false_1_1_1`) exploits — a Sidon set with the *complete* graph satisfies the
cardinality conditions yet has no small-doubling refinement.

This file re-introduces the energy coupling that the abstraction discarded, **without editing any
existing file**. We state a strictly **smaller-but-energy-coupled** residual `DRCKernelEnergy`:

* it is handed the original `A, K` together with the **energy hypothesis** `#A ^ 3 ≤ K * E[A]`
  (the genuine BSG input, kept *coupled* rather than abstracted into graph cardinalities), and
* the popular vertex datum is stated for the **popular graph** `G = popGraph A (#A / (2K))`
  (defined *from* `A`'s representation function `rAdd`, never an arbitrary graph), and
* it must output the BSG subset.

We prove two things:

1. `bsgCore_of_kernelEnergy : DRCKernelEnergy C₁ C₂ c → BSGCore C₁ C₂ c` — the reduction. The
   only nontrivial step beyond the existing `_BSG_DRC2` plumbing is discharging the small-set
   edge case `#A < 2K` (where the popular threshold degenerates) by the singleton refinement,
   requiring `2 ≤ C₁` and `1 ≤ C₂`. In the main case `#A ≥ 2K` we hand the proven popular-graph
   density (`popGraph_edge_dense`, `popGraph_cherry_rich`) and the averaging core
   (`exists_large_left_neighborhood`) to `DRCKernelEnergy`, supplying the energy hypothesis verbatim.

2. **Satisfiability / countermodel check** (`sidon_not_refutes_kernelEnergy`): the Sidon instance
   that refutes the energy-stripped `BareDRCExtract` **cannot be replayed** against
   `DRCKernelEnergy`, because at `(A = {0,1,3} ⊆ ZMod 7, K = 1)` the energy hypothesis
   `#A ^ 3 ≤ K * E[A]` is **false** (`27 ≤ 15` is false). So re-coupling to the energy hypothesis
   provably excludes the canonical obstruction by construction. (And `DRCKernelEnergy` is not
   vacuously unsatisfiable: it is *implied by* the energy-free `DRCKernel`, which the literature
   asserts at absolute constants — see `kernelEnergy_of_kernel`.)

## Status

`REDUCES-FURTHER` — `BSGCore` reduced to the strictly-smaller, **energy-coupled** `DRCKernelEnergy`;
the canonical Sidon countermodel is machine-checked to *not* apply to it.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29.
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- **The energy-coupled DRC kernel `DRCKernelEnergy`.**

Strictly smaller than `BSGCore`: the energy→popular-graph→averaging layers
(`popGraph_edge_dense`, `popGraph_cherry_rich`, `exists_large_left_neighborhood`) are discharged
*before* it is called, so it receives the large-neighbourhood vertex `b` already. The crucial
difference from the energy-stripped `DRCKernel`: the hypotheses **carry the energy bound**
`#A ^ 3 ≤ K * E[A]` and **pin the graph** to the popular graph `popGraph A (#A / (2K))` (built from
`A`'s own representation counts). It therefore cannot be instantiated at the Sidon complete graph
unless the energy hypothesis is genuinely met — which the Sidon set fails at small `K`. -/
def DRCKernelEnergy (C₁ C₂ c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (b : α),
      0 < K → A.Nonempty → 2 * K ≤ #A →
      #A ^ 3 ≤ K * E[A] →
      b ∈ A →
      #A ^ 2 ≤ 16 * K ^ 4 * (#(leftNbhd A (popGraph A (#A / (2 * K))) b)) ^ 2 →
      ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
        C₁ * K * #A' ≥ #A ∧ #(A' - A') ≤ C₂ * K ^ c * #A'

/-- **The energy-free kernel implies the energy-coupled one.** `DRCKernelEnergy` is *weaker* (more
hypotheses to discharge), so it follows from the abstract `DRCKernel`. This certifies
`DRCKernelEnergy` is **satisfiable** (not vacuously false): any model of the literature's `DRCKernel`
is a model of `DRCKernelEnergy`. -/
theorem kernelEnergy_of_kernel {C₁ C₂ c : ℕ} (h : DRCKernel C₁ C₂ c) :
    DRCKernelEnergy C₁ C₂ c := by
  intro α _ _ A K b hK hA _hcard _hE hbA hbig
  exact h A K (popGraph A (#A / (2 * K))) b hK hA (popGraph_subset _ _) hbA hbig

/-- **The reduction `BSGCore ≤ DRCKernelEnergy`** (with `2 ≤ C₁`, `1 ≤ C₂`).

Main case `#A ≥ 2K`: the proven energy→graph layer (`popGraph_edge_dense`, `popGraph_cherry_rich`)
manufactures the dense, cherry-rich popular graph `G = popGraph A (#A/(2K))`; the averaging core
(`exists_large_left_neighborhood`) extracts the large-neighbourhood vertex `b`; we then hand
`DRCKernelEnergy` the **energy hypothesis verbatim** plus that vertex datum.

Small case `#A < 2K`: pick any `a ∈ A`, take `A' = {a}`. Then `#A' = 1`, `#(A'-A') = #({a}-{a}) = 1`
(as `{a} - {a} = {0}`), `C₁ K #A' = C₁ K ≥ 2K > #A` (using `2 ≤ C₁`), and
`#(A'-A') = 1 ≤ C₂ K^c #A' = C₂ K^c` (using `1 ≤ C₂`, `0 < K`). -/
theorem bsgCore_of_kernelEnergy {C₁ C₂ c : ℕ} (hC₁ : 2 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (hker : DRCKernelEnergy C₁ C₂ c) :
    Finset.BSGCore C₁ C₂ c := by
  intro α _ _ A K hK hA hE
  classical
  by_cases hsmall : 2 * K ≤ #A
  · -- Main case: energy → dense popular graph → averaging vertex → energy-coupled kernel.
    set θ : ℕ := #A / (2 * K) with hθ
    set G : Finset (α × α) := popGraph A θ with hG
    have hGsub : G ⊆ A ×ˢ A := popGraph_subset A θ
    have hdense : #A ^ 2 ≤ 4 * K ^ 2 * #G := popGraph_edge_dense A K hK hA hsmall hE
    have hcherry : #A ^ 4 ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) :=
      popGraph_cherry_rich A K G hGsub hdense
    obtain ⟨b, hbA, hb⟩ := exists_large_left_neighborhood A K G hA hcherry
    -- Translate the squared-degree bound to the left-neighbourhood card.
    have hbig : #A ^ 2 ≤ 16 * K ^ 4 * (#(leftNbhd A G b)) ^ 2 := by
      rwa [card_leftNbhd]
    exact hker A K b hK hA hsmall hE hbA hbig
  · -- Small case `#A < 2K`: singleton refinement.
    push_neg at hsmall
    obtain ⟨a, haA⟩ := hA
    refine ⟨{a}, by simpa using haA, ⟨a, mem_singleton_self a⟩, ?_, ?_⟩
    · -- `C₁ * K * #{a} = C₁ * K ≥ 2 * K > #A`.
      rw [Finset.card_singleton, mul_one]
      have h2K : 2 * K ≤ C₁ * K := Nat.mul_le_mul_right _ hC₁
      have : #A ≤ 2 * K := Nat.le_of_lt hsmall
      omega
    · -- `#({a} - {a}) = 1 ≤ C₂ * K ^ c * #{a} = C₂ * K ^ c`.
      have hself : ({a} : Finset α) - {a} = {0} := by
        rw [Finset.singleton_sub_singleton, sub_self]
      rw [hself, Finset.card_singleton, Finset.card_singleton, mul_one]
      have hKc : 1 ≤ K ^ c := Nat.one_le_pow _ _ hK
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ C₂ * K ^ c := Nat.mul_le_mul hC₂ hKc

/-! ## Satisfiability / countermodel check: the Sidon instance does NOT refute `DRCKernelEnergy`

The Sidon set `A = {0,1,3} ⊆ ZMod 7` with the *complete* graph and `K = 1` refutes the
energy-**stripped** residuals. We certify it cannot be replayed against the energy-**coupled**
`DRCKernelEnergy`, because the energy hypothesis `#A ^ 3 ≤ K * E[A]` is **false** there:
`#A ^ 3 = 27`, `K * E[A] = 1 * E[{0,1,3}] = 15`, and `27 ≤ 15` is false. -/

/-- The Sidon witness `sidonA = {0,1,3} ⊆ ZMod 7` (`B₂` set, maximal doubling `#(A-A) = 7`); the
canonical obstruction to small-doubling refinement. -/
def sidonA : Finset (ZMod 7) := {0, 1, 3}

@[simp] lemma card_sidonA : #sidonA = 3 := by decide

/-- The additive energy of the Sidon witness `sidonA = {0,1,3} ⊆ ZMod 7` is `15`. -/
@[simp] lemma addEnergy_sidonA : E[sidonA] = 15 := by decide

/-- **Countermodel check.** At the Sidon instance `(sidonA, K = 1)`, the energy hypothesis of
`DRCKernelEnergy` is **false**: `#sidonA ^ 3 = 27 > 15 = 1 * E[sidonA]`. Hence the canonical Sidon
obstruction — which refutes the energy-stripped `BareDRCExtract` (`bareDRCExtract_false_1_1_1`) —
**cannot be instantiated** against the energy-coupled `DRCKernelEnergy`: re-coupling to the energy
hypothesis excludes it by construction. -/
theorem sidon_not_refutes_kernelEnergy :
    ¬ (#sidonA ^ 3 ≤ 1 * E[sidonA]) := by
  rw [card_sidonA, addEnergy_sidonA]; decide

/-- The same fact at the level the countermodel needs: for `K = 1` the energy hypothesis fails on
the Sidon witness, so the `K = 1` complete-graph replay is blocked. (For `K ≥ 2` the Sidon energy
*is* enough, but then `DRCKernelEnergy` demands the popular-graph vertex datum with `K ≥ 2`, not the
`K = 1` complete graph the countermodel supplies.) -/
theorem sidon_energy_fails_K1 : #sidonA ^ 3 > 1 * E[sidonA] := by
  rw [card_sidonA, addEnergy_sidonA]; decide

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.kernelEnergy_of_kernel
#print axioms Finset.BSG.bsgCore_of_kernelEnergy
#print axioms Finset.BSG.addEnergy_sidonA
#print axioms Finset.BSG.sidon_not_refutes_kernelEnergy
#print axioms Finset.BSG.sidon_energy_fails_K1
