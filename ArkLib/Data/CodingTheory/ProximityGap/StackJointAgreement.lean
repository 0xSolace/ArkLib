/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Stack joint agreement

This file collects the row-index-general form of joint agreement for word stacks.  It is the
common core behind the curve MCA event (`MCACurveEvent.lean`) and the generator MCA event
(`GeneratorMCA.lean`):

* `stackJointAgreesOn` says every row of a stack agrees on `S` with some codeword of `C`.
* `stackJointAgreesOn_iff_forall_row` splits stack agreement into independent row witnesses.
* `stackJointAgreesOn_two_iff` / `stackJointAgreesOn_pair_iff` recover the pair API used by
  the affine-line MCA event.

The rowwise split is the useful mathematical seam: stack agreement is a product condition over
rows, while MCA badness is exactly the failure of this product condition on a large witness set.
-/

namespace ProximityGap

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ### Rowwise stack agreement -/

/-- The stack `u` **jointly agrees** with a tuple of codewords of `C` on every position in
`S`: there is one codeword witness for each row, and each witness agrees with its row on
all coordinates of `S`.

For `κ = Fin ℓ` this is the `ℓ`-ary generalization of `pairJointAgreesOn`; for arbitrary
`κ` it is the product form consumed by the joint-agreement escape lemmas. -/
def stackJointAgreesOn {κ : Type} (C : Set (ι → A)) (S : Finset ι)
    (u : κ → ι → A) : Prop :=
  ∃ v : κ → ι → A, (∀ j, v j ∈ C) ∧ ∀ i ∈ S, ∀ j, v j i = u j i

open Classical in
/-- Stack joint agreement splits row-by-row: choosing a jointly agreeing codeword stack is
equivalent to independently choosing, for every row, a codeword agreeing with that row on
`S`.  This exposes the product structure hidden in the existential stack witness. -/
theorem stackJointAgreesOn_iff_forall_row {κ : Type} (C : Set (ι → A)) (S : Finset ι)
    (u : κ → ι → A) :
    stackJointAgreesOn C S u ↔ ∀ j : κ, ∃ v ∈ C, ∀ i ∈ S, v i = u j i := by
  constructor
  · rintro ⟨v, hv_mem, hv_agree⟩ j
    exact ⟨v j, hv_mem j, fun i hi => hv_agree i hi j⟩
  · intro hrow
    choose v hv_mem hv_agree using hrow
    exact ⟨v, hv_mem, fun i hi j => hv_agree j i hi⟩

/-- If one row has no codeword agreeing with it on `S`, then the whole stack cannot jointly
agree on `S`. -/
theorem not_stackJointAgreesOn_of_not_row {κ : Type} (C : Set (ι → A)) (S : Finset ι)
    (u : κ → ι → A) (j : κ)
    (hrow : ¬ ∃ v ∈ C, ∀ i ∈ S, v i = u j i) :
    ¬ stackJointAgreesOn C S u := by
  intro hstack
  exact hrow ((stackJointAgreesOn_iff_forall_row C S u).mp hstack j)

/-! ### Pair compatibility -/

/-- At `κ = Fin 2`, stack joint agreement is exactly `pairJointAgreesOn` on the two rows. -/
theorem stackJointAgreesOn_two_iff (C : Set (ι → A)) (S : Finset ι)
    (u : Fin 2 → ι → A) :
    stackJointAgreesOn C S u ↔ pairJointAgreesOn C S (u 0) (u 1) := by
  constructor
  · rintro ⟨cs, hcs, hag⟩
    exact ⟨cs 0, hcs 0, cs 1, hcs 1, fun i hi => ⟨hag i hi 0, hag i hi 1⟩⟩
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    refine ⟨![v₀, v₁], ?_, ?_⟩
    · intro j
      fin_cases j
      · simpa using hv₀
      · simpa using hv₁
    · intro i hi j
      fin_cases j
      · simpa using (hag i hi).1
      · simpa using (hag i hi).2

/-- Alias for the curve-MCA API: at `κ = Fin 2`, `stackJointAgreesOn` is
`pairJointAgreesOn`. -/
theorem stackJointAgreesOn_pair_iff (C : Set (ι → A)) (S : Finset ι)
    (u : Fin 2 → ι → A) :
    stackJointAgreesOn C S u ↔ pairJointAgreesOn C S (u 0) (u 1) :=
  stackJointAgreesOn_two_iff C S u

end ProximityGap

/-! ## Axiom audit -/
#print axioms ProximityGap.stackJointAgreesOn
#print axioms ProximityGap.stackJointAgreesOn_iff_forall_row
#print axioms ProximityGap.not_stackJointAgreesOn_of_not_row
#print axioms ProximityGap.stackJointAgreesOn_two_iff
#print axioms ProximityGap.stackJointAgreesOn_pair_iff
