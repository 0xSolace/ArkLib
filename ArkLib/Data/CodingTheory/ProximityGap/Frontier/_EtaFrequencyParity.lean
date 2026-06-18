/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SymmetricEtaRealBridge

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# `η_{−b} = conj(η_b)` always, and `η_{−b} = η_b` on symmetric `G` (frequency parity) (#444)

Two structural facts about the dependence of the Cayley eigenvalue `η_b = Σ_{x∈G} ψ(b·x)` on the
FREQUENCY `b` (companion to `_SymmetricEtaRealBridge`, which fixed the dependence on the SIGN of `η_b`):

> **`eta_neg_eq_conj`** : `η_{−b} = conj(η_b)`  (always — `ψ(−b·x) = conj(ψ(b·x))`).

This is the Hermitian-frequency reflection, true for ANY connection set (no symmetry needed). Combined
with the realness on symmetric `G` (`_SymmetricEtaRealBridge.conj_eta_eq_of_symm`, `conj(η_b) = η_b` when
`−G = G`) it yields the eigenvalue degeneracy:

> **`eta_neg_eq_of_symm`** : `η_{−b} = η_b`  (when `−G = G`).

So on the prize-regime symmetric subgroup `μ_n` (`n = 2^a`, `−1 ∈ μ_n`) the non-principal spectrum is
`b ↔ −b` **2-fold degenerate**: the `m = q−1` non-principal frequencies pair into `(q−1)/2` distinct
eigenvalues, each of multiplicity `2`. This is the exact structural basis of the antipodal/dihedral
descent (the `b`-pairing the in-tree `Bridge05`/antipodal files exploit on the value side), recorded
here on the FREQUENCY side as a clean reusable lemma.

## The clean consequence: `‖η_{−b}‖ = ‖η_b‖` (the maximiser pairs up)

> **`norm_eta_neg_eq`** : `‖η_{−b}‖ = ‖η_b‖`  (always — modulus is reflection-invariant).

So the prize sup `M = max_{b≠0}‖η_b‖` is attained on a `b ↔ −b` PAIR (for `b ≠ −b`), never an isolated
frequency: any extremal frequency has an antipodal twin of equal magnitude. (Holds unconditionally; it is
the modulus shadow of `eta_neg_eq_conj`.)

## Honesty (project §6)

POSITIVE structural bricks, NOT a closure and NOT a refutation. Exact and axiom-clean (character
algebra; `eta_neg_eq_conj` is unconditional, `eta_neg_eq_of_symm` chains it through the symmetric-realness
lemma). They bound NOTHING from above: the prize `M ≤ C√(n·log p)` (char-`p` energy/BGK wall) stays
OPEN. Frequency-side `b ↔ −b` degeneracy halves the count of DISTINCT non-principal eigenvalues but does
not bound any single one. Issue #444.

## References
- `Frontier/_SymmetricEtaRealBridge.conj_eta_eq_of_symm` (`conj(η_b) = η_b` on symmetric `G`).
- `SubgroupGaussSumFourthMoment` (internal `conj(η_b) = Σ ψ(−(b·y))` pattern, here exposed standalone).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ProximityGap.Frontier.SymmetricEtaRealBridge

namespace ProximityGap.Frontier.EtaFrequencyParity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **★ `η_{−b} = conj(η_b)` (unconditional Hermitian-frequency reflection).**
`η_{−b} = Σ_{x∈G} ψ((−b)·x) = Σ_{x∈G} ψ(−(b·x)) = Σ_{x∈G} conj(ψ(b·x)) = conj(η_b)`. Pure character
algebra, no symmetry, no Weil. -/
theorem eta_neg_eq_conj {ψ : AddChar F ℂ} (G : Finset F) (b : F) :
    eta ψ G (-b) = (starRingEnd ℂ) (eta ψ G b) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  unfold eta
  rw [map_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [hconj, neg_mul]

/-- **★ `η_{−b} = η_b` on symmetric `G` (frequency `b ↔ −b` degeneracy).** Chaining the unconditional
reflection `η_{−b} = conj(η_b)` with the symmetric realness `conj(η_b) = η_b` (`−G = G`): the
non-principal spectrum is `2`-fold degenerate under `b ↦ −b`. -/
theorem eta_neg_eq_of_symm {ψ : AddChar F ℂ} (G : Finset F) (hsymm : ∀ x ∈ G, -x ∈ G) (b : F) :
    eta ψ G (-b) = eta ψ G b := by
  rw [eta_neg_eq_conj, conj_eta_eq_of_symm G hsymm b]

/-- **`‖η_{−b}‖ = ‖η_b‖` (unconditional).** The modulus shadow of `eta_neg_eq_conj`: any extremal
frequency has an antipodal twin of equal magnitude, so the prize sup `M = max_{b≠0}‖η_b‖` is attained on
a `b ↔ −b` pair. -/
theorem norm_eta_neg_eq {ψ : AddChar F ℂ} (G : Finset F) (b : F) :
    ‖eta ψ G (-b)‖ = ‖eta ψ G b‖ := by
  rw [eta_neg_eq_conj, RCLike.norm_conj]

end ProximityGap.Frontier.EtaFrequencyParity

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.EtaFrequencyParity.eta_neg_eq_conj
#print axioms ProximityGap.Frontier.EtaFrequencyParity.eta_neg_eq_of_symm
#print axioms ProximityGap.Frontier.EtaFrequencyParity.norm_eta_neg_eq
