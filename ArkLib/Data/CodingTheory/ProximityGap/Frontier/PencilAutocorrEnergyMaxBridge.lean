/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrSumDoubleCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrSubgroupExact

/-!
# The multiplicative-ENERGY lower bound on the worst autocorrelation (#407/#444)

`PencilAutocorrSumDoubleCount.autocorr_max_pigeonhole` gives the FIRST-moment lower bound on the
worst multiplicative autocorrelation `M = max_{ρ≠1} |S ∩ ρ·S|`:

  `|S|·(|S|−1) ≤ (|G|−1)·M`,   i.e.   `M ≥ |S|(|S|−1)/(|G|−1)`.

This file lands the SECOND-moment (energy) companion, which is the SHARPER and exact lever for the
thin subgroup. With the two double-counts

  `∑_{ρ∈G} |S ∩ ρ·S| = |S|²`         (`autocorr_sum_eq_sq`),
  `∑_{ρ∈G} |S ∩ ρ·S|² = E_×(S)`      (the multiplicative energy),

the elementary bound `∑ a_ρ² ≤ (max_ρ a_ρ)·(∑ a_ρ)` (a number is `≤` the max times its weight) gives

> **`E_×(S) ≤ M₀ · |S|²`** where `M₀ = max_{ρ∈G} |S ∩ ρ·S|`   (`mulEnergy_le_maxAutocorr_mul_sq`),

equivalently the energy lower bound on the worst autocorrelation `M₀ ≥ E_×(S)/|S|²`
(`maxAutocorr_ge_mulEnergy_div_sq`).

**Why this is the SHARP face (not boundary-mapping).**  For the prize object `S = H = μ_n` the
multiplicative energy is EXACTLY `E_×(H) = |H|³` (`subgroup_multiplicativeEnergy_eq_card_cube`), so the
energy bound forces `M₀ ≥ |H|³/|H|² = |H|` — the EXACT all-or-nothing maximum
(`subgroup_autocorr_le_card` + `exists_nontrivial_shift_autocorr_eq_card` pin `M₀ = |H|`).  The
first-moment pigeonhole only delivers `M ≥ |H|(|H|−1)/(|G|−1) = Θ(|H|²/|G|)`, which for the prize
regime `|G| = q ≈ |H|^β` is `≈ |H|^{2−β} → 0` — vacuous.  The energy lever is the one that recovers the
true `Θ(|H|)` rigidity, confirming the unsigned multiplicative autocorrelation of the subgroup carries
its full mass on the diagonal-of-shifts with NO spreading: any √(log) cancellation must live in the
SIGNED phase, never the unsigned overlap (consistent with the in-tree honest-scope notes).

**Honest scope.**  This is a sign-free additive/multiplicative-combinatorics structural brick: the
exact second-moment relation between the worst autocorrelation and the multiplicative energy.  It is
NOT a CORE closure, NOT thinness-essential (it holds for any finite group), and makes NO capacity /
beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched).  It SHARPENS the pigeonhole lever and
re-derives the subgroup's exact `M₀ = |H|` from energy, but the prize `M(n) ≤ C√(n log(p/n))` lives in
the SIGNED character sum, which this does not touch.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issues #407, #444.
-/

open Finset

namespace ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **The elementary second-moment bound.**  For any nonnegative integer family `a : G → ℕ` over a
finite type, `∑ a ρ ^ 2 ≤ (sup over ρ of a ρ) · ∑ a ρ`: each term `a ρ ^ 2 = a ρ · a ρ ≤ M₀ · a ρ`.
This is the kernel of the energy↔max bridge, isolated so the autocorrelation specialization is a
one-line application. -/
theorem sum_sq_le_max_mul_sum (a : G → ℕ) {M₀ : ℕ} (hM₀ : ∀ ρ : G, a ρ ≤ M₀) :
    ∑ ρ : G, a ρ ^ 2 ≤ M₀ * ∑ ρ : G, a ρ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ρ _ => ?_)
  rw [pow_two]
  exact Nat.mul_le_mul_right _ (hM₀ ρ)

/-- **The multiplicative-energy upper bound by the worst autocorrelation.**  With the autocorrelation
double-count `∑_ρ |S ∩ ρS| = |S|²`, the energy `E_×(S) = ∑_ρ |S ∩ ρS|²` is at most `M₀·|S|²` where
`M₀` is the worst (over ALL `ρ`, including the trivial shift) autocorrelation:

  `E_×(S) ≤ M₀ · |S|²`. -/
theorem mulEnergy_le_maxAutocorr_mul_sq (S : Finset G) {M₀ : ℕ}
    (hM₀ : ∀ ρ : G, (S ∩ dilate ρ S).card ≤ M₀) :
    ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2 ≤ M₀ * S.card ^ 2 := by
  have hsum := PencilAutocorrSumDoubleCount.autocorr_sum_eq_sq S
  calc
    ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2
        ≤ M₀ * ∑ ρ : G, (S ∩ dilate ρ S).card :=
          sum_sq_le_max_mul_sum (fun ρ => (S ∩ dilate ρ S).card) hM₀
    _ = M₀ * S.card ^ 2 := by rw [hsum]

/-- **Subgroup exactness via energy.**  For the prize object `S = H` (a multiplicative subgroup, the
thin `μ_n`), the energy bound `E_×(H) ≤ M₀·|H|²` combined with the EXACT energy `E_×(H) = |H|³`
forces the worst autocorrelation `M₀ ≥ |H|` whenever `H` is nonempty.  Together with
`subgroup_autocorr_le_card` (`M₀ ≤ |H|`), this RE-DERIVES `M₀ = |H|` from the energy lever alone —
the unsigned multiplicative autocorrelation of the subgroup is maximally concentrated, no spreading
to exploit. -/
theorem subgroup_maxAutocorr_ge_card {H : Finset G} {M₀ : ℕ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hne : H.Nonempty)
    (hM₀ : ∀ ρ : G, (H ∩ dilate ρ H).card ≤ M₀) :
    H.card ≤ M₀ := by
  have hEnergy : ∑ ρ : G, (H ∩ dilate ρ H).card ^ 2 = H.card ^ 3 :=
    subgroup_multiplicativeEnergy_eq_card_cube hmul hinv
  have hbound : ∑ ρ : G, (H ∩ dilate ρ H).card ^ 2 ≤ M₀ * H.card ^ 2 :=
    mulEnergy_le_maxAutocorr_mul_sq H hM₀
  rw [hEnergy] at hbound
  -- |H|^3 ≤ M₀·|H|^2 ⟹ |H| ≤ M₀ (cancel the positive |H|^2)
  have hpos : 0 < H.card ^ 2 := by
    have : 0 < H.card := Finset.card_pos.mpr hne
    positivity
  -- |H|^3 = |H|^2 · |H| and M₀·|H|^2 = |H|^2 · M₀ ; cancel |H|^2 on the left
  have hcube : H.card ^ 3 = H.card ^ 2 * H.card := by ring
  have hrhs : M₀ * H.card ^ 2 = H.card ^ 2 * M₀ := Nat.mul_comm _ _
  rw [hcube, hrhs] at hbound
  exact Nat.le_of_mul_le_mul_left hbound hpos

end ProximityGap.Frontier.PencilAutocorrelation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms sum_sq_le_max_mul_sum
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms mulEnergy_le_maxAutocorr_mul_sq
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms subgroup_maxAutocorr_ge_card
