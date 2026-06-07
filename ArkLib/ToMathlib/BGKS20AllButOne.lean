/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.Bridge2BGKS20

/-!
# BGKS20 separation bridge — the "all but one scalar" `NearCertainBadLine` producer

This file adds a small, self-contained supporting lemma for the BGKS20 characteristic-2
separation bridge (`ArkLib.ToMathlib.Bridge2BGKS20`, issue #22). The BGKS20 construction is
described — both in [BGKS20] Lemma 3.3 and in the bridge file's own docstrings — as exhibiting a
stack `u = (u₀, u₁)` that is **not** jointly close to the code, yet whose affine line
`u₀ + γ·u₁` is `δ_fld`-close to `C` for **all but one** scalar `γ ∈ F`.

The bridge file, however, only exposes the *already-counted* form of the witness: a good-combiner
set `Γ` together with the bare cardinality bound `|F| - 1 ≤ |Γ|`
(`Bridge.NearCertainBadLine`, `Bridge.epsCA_ge_one_sub_inv_of_nearCertainWitness`). This file
closes that small gap by providing the literal *all-but-one-scalar* entry point:

* `real_card_sub_one_le_card_erase` — the Finset-cardinality glue: over a fintype, the complement
  of a single point `Finset.univ.erase γ_bad` has cardinality `|F| - 1`, hence satisfies the
  real bound `(|F| : ℝ) - 1 ≤ |Finset.univ.erase γ_bad|` that `NearCertainBadLine` requires.
* `nearCertainBadLine_of_allButOne` — **the producer**: from a stack not jointly `δ_int`-close
  together with a single bad scalar `γ_bad` such that *every other* scalar makes the line
  `δ_fld`-close to `C`, assemble a `Bridge.NearCertainBadLine` (good set `Finset.univ.erase
  γ_bad`). This matches BGKS20's natural witness shape — "exactly one bad combiner" — with the
  cardinality bookkeeping discharged in-tree.
* `epsCA_ge_one_sub_inv_of_allButOne` — composes the producer with the proven separation bridge
  `Bridge.epsCA_separation_bridge_of_residual` to land the BGKS20 lower bound
  `ε_ca(C, δ_fld, δ_int) ≥ 1 - 1/|F|` directly from the all-but-one-scalar data.

## What this file does *not* close

It does **not** manufacture the BGKS20 stack — the genuinely-external content is still the
characteristic-2 full-domain Reed–Solomon construction that produces a non-jointly-close stack
with exactly one bad combiner ([BGKS20] Lemma 3.3, tracked as the
`Bridge.NearCertainBadLine` residual). This file only reduces the *count* obligation to its
sharpest in-paper phrasing ("all but one scalar is good") and discharges the surrounding
cardinality arithmetic.

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, 2026,
  Theorem 5.4.
* [BGKS20] Ben-Sasson, Goldreich, Kopparty, Saraf. *Bounds on the List Decodability of
  Reed-Solomon Codes*, 2020, Lemma 3.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CodingTheory.Bridge

open scoped NNReal BigOperators
open ProximityGap Code

section AllButOne

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Cardinality glue for the all-but-one good set.** Over a fintype `F`, removing a single
scalar `γ_bad` leaves `|F| - 1` scalars, so `Finset.univ.erase γ_bad` meets the real cardinality
bound `(|F| : ℝ) - 1 ≤ |Finset.univ.erase γ_bad|` that `NearCertainBadLine` demands. -/
theorem real_card_sub_one_le_card_erase (γ_bad : F) :
    (Fintype.card F : ℝ) - 1 ≤ ((Finset.univ.erase γ_bad).card : ℝ) := by
  classical
  have hmem : γ_bad ∈ (Finset.univ : Finset F) := Finset.mem_univ _
  have hcard : (Finset.univ.erase γ_bad).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem hmem, Finset.card_univ]
  rw [hcard]
  have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
  have hcast : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]; norm_num
  rw [hcast]

/-- **BGKS20 "all but one scalar" producer.** Given a stack `u` that is *not* jointly
`δ_int`-close to `C`, and a single bad scalar `γ_bad` such that for *every other* scalar
`γ ≠ γ_bad` the line `u 0 + γ • u 1` is `δ_fld`-close to `C`, the code `C` admits a
`Bridge.NearCertainBadLine`.

This is the literal [BGKS20] Lemma 3.3 phrasing — the line is close to `C` for all but one
scalar — with the good set taken to be `Finset.univ.erase γ_bad` (cardinality `|F| - 1`). The
single remaining obligation is the genuinely-external BGKS20 char-2 construction of such a
stack. -/
theorem nearCertainBadLine_of_allButOne
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (γ_bad : F)
    (hgood : ∀ γ : F, γ ≠ γ_bad → δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) :
    NearCertainBadLine (F := F) C δ_fld δ_int := by
  classical
  refine ⟨u, hjp, Finset.univ.erase γ_bad, ?_, real_card_sub_one_le_card_erase γ_bad⟩
  intro γ hγ
  rw [Finset.mem_erase] at hγ
  exact hgood γ hγ.1

/-- **`ε_ca` lower bound directly from the all-but-one-scalar data.** Composes the producer with
the proven separation bridge `epsCA_separation_bridge_of_residual`: a stack not jointly
`δ_int`-close whose line is `δ_fld`-close to `C` for all but one scalar certifies the BGKS20
separation lower bound `ε_ca(C, δ_fld, δ_int) ≥ 1 - 1/|F|`. -/
theorem epsCA_ge_one_sub_inv_of_allButOne
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (hjp : ¬ jointProximity (C := C) (u := u) δ_int)
    (γ_bad : F)
    (hgood : ∀ γ : F, γ ≠ γ_bad → δᵣ(u 0 + γ • u 1, C) ≤ δ_fld) :
    ENNReal.ofReal (1 - 1 / Fintype.card F) ≤ epsCA (F := F) C δ_fld δ_int :=
  epsCA_separation_bridge_of_residual (F := F) C δ_fld δ_int
    (nearCertainBadLine_of_allButOne C δ_fld δ_int u hjp γ_bad hgood)

end AllButOne

end CodingTheory.Bridge

/-! ### Axiom audit (issue #22 BGKS20 all-but-one surface) -/

#print axioms CodingTheory.Bridge.real_card_sub_one_le_card_erase
#print axioms CodingTheory.Bridge.nearCertainBadLine_of_allButOne
#print axioms CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_allButOne
