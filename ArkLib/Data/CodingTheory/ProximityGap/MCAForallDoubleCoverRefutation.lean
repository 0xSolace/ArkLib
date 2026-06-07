/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Refutation of the universal `MCAForallDoubleCover` claim (Issues #140 / #169 / #171)

`MCAForallDoubleCover C δ` is the "repaired T4.21" hypothesis from
`LineDecodingCoverage.lean`. Crucially, `MCAForallDoubleCover.not_mcaEvent` proves

  `MCAForallDoubleCover C δ → ∀ u γ, ¬ mcaEvent C δ (u 0) (u 1) γ`,

i.e. it is *equivalent* to "the MCA bad event never occurs for this code at this radius"
(`MCAForallDoubleCover_iff_forall_not_mcaEvent`). It is therefore a **strong, code-specific
hypothesis**, true only for codes/radii at which no bad event exists — emphatically **not**
universally true.

`ArkLib/ResidualAxioms.lean` nonetheless carries

  `axiom mcaForallDoubleCover_residual … : MCAForallDoubleCover C δ`

quantified over *all* `ι, F, A, C, δ`. Composed with
`CodingTheory.lineDecodable_imp_epsMCA_le_target`
(`MCAForallDoubleCover C δ → epsMCA C δ ≤ a/q`, proved via `epsMCA = 0`), that axiom forces
`epsMCA C δ = 0` for **every** code at **every** radius — a plainly false statement. Hence the
axiom is **unsound** (it makes the library inconsistent), not an honest open-problem placeholder.

This file proves that, sorry-free and axiom-clean, by exhibiting a concrete realizable
`mcaEvent`, which refutes `MCAForallDoubleCover` for a concrete code:

* `concrete_mcaEvent` — a realizable MCA bad event over `F = A = ZMod 2`, `ι = Fin 1`,
  `C = {0}`, `δ = 0`, with `u₀ = 0`, `u₁ = 1`, `γ = 0`: the line `u₀ + γ•u₁ = 0` matches the
  codeword `0 ∈ C` on the full domain, yet no joint pair of codewords agrees with `(u₀, u₁)`
  there because `u₁ 0 = 1` cannot be matched inside `{0}`.

* `not_mcaForallDoubleCover_concrete` — therefore `¬ MCAForallDoubleCover (ZMod 2) {0} 0`.

* `exists_not_mcaForallDoubleCover` — hence `∃ C δ, ¬ MCAForallDoubleCover C δ`: the universal
  `mcaForallDoubleCover_residual` asserts a false proposition and must be **removed**, not
  "proved" (it is open/false research-grade content, exactly the larp pattern catalogued in
  #169 / #171). The genuine repair of ABF26 T4.21 needs the Guruswami–Sudan interpolation-degree
  data exposed in the statement (see `LineDecoding.lean` / `MCAGS.lean`), not a blanket axiom.

This is a refutation artifact (cf. `LineDecodingCounting.double_coverage_counterexample`), not a
closure of any open problem. Tracking: Issues #140, #169, #171.
-/

namespace ProximityGap

open Code
open scoped NNReal

/-- `Fact (Nat.Prime 2)`, needed for the concrete field `ZMod 2` used as the refutation witness. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **A concrete realizable MCA bad event.** Over `F = A = ZMod 2`, `ι = Fin 1`, the line
`u₀ + γ•u₁` with `u₀ = 0`, `u₁ = 1`, `γ = 0` equals the codeword `0 ∈ {0}` on the whole domain,
but no joint codeword pair agrees with `(u₀, u₁)` there (since `u₁ 0 = 1 ∉ {0}`). So the MCA bad
event of ABF26 Def. 4.3 genuinely occurs. -/
theorem concrete_mcaEvent :
    mcaEvent (F := ZMod 2) (A := ZMod 2) ({0} : Set (Fin 1 → ZMod 2)) 0
      (0 : Fin 1 → ZMod 2) (fun _ => (1 : ZMod 2)) (0 : ZMod 2) := by
  refine ⟨Finset.univ, ?_, ⟨0, ?_, ?_⟩, ?_⟩
  · simp
  · simp
  · intro i _
    simp
  · rintro ⟨v₀, hv₀, v₁, hv₁, h⟩
    rw [Set.mem_singleton_iff] at hv₁
    have := (h 0 (Finset.mem_univ 0)).2
    rw [hv₁] at this
    simp at this

/-- **`MCAForallDoubleCover` is not universally true.** It fails for the concrete code `{0}` over
`ZMod 2` at radius `0`, because `concrete_mcaEvent` exhibits a bad event there and
`MCAForallDoubleCover.not_mcaEvent` would rule all bad events out. -/
theorem not_mcaForallDoubleCover_concrete :
    ¬ MCAForallDoubleCover (F := ZMod 2) (A := ZMod 2) ({0} : Set (Fin 1 → ZMod 2)) 0 := by
  intro hcov
  exact MCAForallDoubleCover.not_mcaEvent (F := ZMod 2) (A := ZMod 2)
    ({0} : Set (Fin 1 → ZMod 2)) 0 hcov
    (![(0 : Fin 1 → ZMod 2), (fun _ => (1 : ZMod 2))]) (0 : ZMod 2) concrete_mcaEvent

/-- **The universal `mcaForallDoubleCover_residual` axiom asserts a false proposition.** There
exist a code and radius for which `MCAForallDoubleCover` fails; an `axiom` claiming it for all
codes is therefore unsound and must be removed (it is not honest open-problem scaffolding).
Tracking: Issues #140, #169, #171. -/
theorem exists_not_mcaForallDoubleCover :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : DecidableEq ι)
      (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F)
      (A : Type) (_ : Fintype A) (_ : DecidableEq A) (_ : AddCommGroup A) (_ : Module F A)
      (C : Set (ι → A)) (δ : ℝ≥0), ¬ MCAForallDoubleCover (F := F) (A := A) C δ :=
  ⟨Fin 1, inferInstance, inferInstance, inferInstance,
    ZMod 2, inferInstance, inferInstance, inferInstance,
    ZMod 2, inferInstance, inferInstance, inferInstance, inferInstance,
    ({0} : Set (Fin 1 → ZMod 2)), 0, not_mcaForallDoubleCover_concrete⟩

end ProximityGap

#print axioms ProximityGap.concrete_mcaEvent
#print axioms ProximityGap.not_mcaForallDoubleCover_concrete
#print axioms ProximityGap.exists_not_mcaForallDoubleCover
