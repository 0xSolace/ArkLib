/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The universal ABF26 T4.21 double-cover hypothesis is FALSE (issue #141)

`MCAForallDoubleCover C δ` is equivalent to "no MCA bad event ever"
(`MCAForallDoubleCover_iff_forall_not_mcaEvent`). This file proves it is **not** universally true,
replacing the previously-present unsound `axiom mcaForallDoubleCover_residual`. A concrete `ZMod 2`
counterexample on one coordinate witnesses a real `mcaEvent`; hence the per-instance double cover is
a genuine hypothesis (supplied per instance by the Guruswami–Sudan interpolation route), never a
universal theorem.
-/

open scoped NNReal
open ProximityGap

namespace ProximityGap

instance mcaForallDoubleCover_fact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **The global ABF26 T4.21 double-cover hypothesis is NOT universally true (issue #141).**
Over `ZMod 2` with one coordinate, code `C = {fun _ => 1}`, radius `δ = 0`, stack `u = ![0, 1]`,
scalar `γ = 1`: the line `u₀ + 1·u₁` equals the codeword `1` on `S = {0}`, yet no codeword equals
`u₀ = 0` on `S`, so `mcaEvent` holds. Since `MCAForallDoubleCover ↔ ∀ u γ, ¬ mcaEvent`, the global
hypothesis fails — no axiom may assert it universally. -/
theorem mcaForallDoubleCover_not_universal :
    ¬ (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
         (C : Set (ι → A)) (δ : ℝ≥0),
         MCAForallDoubleCover (F := F) (A := A) C δ) := by
  intro H
  classical
  have hcov := H (ι := Fin 1) (F := ZMod 2) (A := ZMod 2)
    ({(fun _ => 1)} : Set (Fin 1 → ZMod 2)) 0
  rw [MCAForallDoubleCover_iff_forall_not_mcaEvent] at hcov
  refine hcov ![(fun _ => 0), (fun _ => 1)] 1 ?_
  refine ⟨{0}, ?_, ⟨(fun _ => 1), rfl, ?_⟩, ?_⟩
  · simp
  · intro i hi
    fin_cases i
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    decide
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    have hv₀eq : v₀ = (fun _ => 1) := hv₀
    have hcontra := (hag 0 (by simp)).1
    rw [hv₀eq] at hcontra
    simp only [Matrix.cons_val_zero] at hcontra
    revert hcontra
    decide

#print axioms mcaForallDoubleCover_not_universal

end ProximityGap
