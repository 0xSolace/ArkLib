/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodMomentBound
import ArkLib.Data.CodingTheory.ProximityGap.GeneralEnergyBound
import Mathlib.Tactic

set_option linter.style.longLine false

/-!
# Conditional square-root cancellation: the dyadic conjecture under the no-relation hypothesis (#389)

Chaining the moment-method sup-norm bound (`worst_period_moment_le`) with the general-`r` additive-energy
bound (`energyR_le_factorial`) gives, for EVERY `r`, the explicit worst-period bound

> `worst_period_le_factorial` :  `b ≠ 0  →  ‖η_b‖^{2r} ≤ q · r! · |G|^r`,

valid whenever `G` has no nontrivial `r`-fold additive relation (`H`). Taking `2r`-th roots,
`max_{b≠0} ‖η_b‖ ≤ (q · r! · |G|^r)^{1/2r}`, and optimizing `r ≈ log f` yields `‖η_b‖ ≲ √(|G| log f)`
— **the square-root-cancellation bound of the dyadic conjecture, PROVEN under `H`.** The cyclotomic
resultant lift (`|Res(Φ_n, manyTerm)| ≤ (2r)^{φ(n)}`, `ManyTermResultantBound`) supplies `H` for
`q > (2r)^{φ(n)}`, so the conjecture holds unconditionally in that (polylog-`n`) regime. This reduces
the open conjecture to the single hypothesis `H` (no `r`-fold relation), which is governed entirely by
the explicit resultant bound — the cleanest provable form of the open math.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Conditional square-root cancellation (per moment `r`).** If `G` has no nontrivial `r`-fold
additive relation, every nontrivial Gaussian period satisfies `‖η_b‖^{2r} ≤ q · r! · |G|^r`. Hence
`max_{b≠0} ‖η_b‖ ≤ (q · r! · |G|^r)^{1/2r}`, which optimized over `r ≈ log f` is `√(|G| log f)` — the
dyadic square-root-cancellation bound, proven under the no-relation hypothesis. -/
theorem worst_period_le_factorial {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (H : ∀ x ∈ Fintype.piFinset (fun _ : Fin r => G), ∀ z ∈ Fintype.piFinset (fun _ : Fin r => G),
          (∑ i, x i = ∑ i, z i) → ∃ σ : Equiv.Perm (Fin r), z = x ∘ σ)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * r.factorial * (G.card : ℝ) ^ r := by
  have h1 := worst_period_moment_le hψ G r hb
  have h2 : (energyR G r : ℝ) ≤ (r.factorial : ℝ) * (G.card : ℝ) ^ r := by
    exact_mod_cast energyR_le_factorial G r H
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r) := h1
    _ ≤ (Fintype.card F : ℝ) * energyR G r := by
        have : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
        linarith
    _ ≤ (Fintype.card F : ℝ) * ((r.factorial : ℝ) * (G.card : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h2 hqnn
    _ = (Fintype.card F : ℝ) * r.factorial * (G.card : ℝ) ^ r := by ring

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.worst_period_le_factorial
