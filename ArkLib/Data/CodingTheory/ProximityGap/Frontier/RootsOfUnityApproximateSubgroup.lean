/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountCurve
import Mathlib.Combinatorics.Additive.ApproximateSubgroup
import Mathlib.RingTheory.RootsOfUnity.Basic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
# The BGK multiplicative input, Mathlib-interoperable: `μ_n` is an `IsApproximateSubgroup 1` of `Fˣ` (#444)

`BGKMultiplicativeInput.lean` lands the multiplicative half of the BGK 2006 sum–product chain for the
in-tree carrier `μ_n = RepCountCurve.muN F n`, but it states the doubling constant `σₘ[μ_n] = 1`
**by hand** (`muN_doubling_eq_one`) because its docstring observes that "the `Combinatorics.Additive`
`Finset.mulConst` requires the ambient type to be a `Group`, which a field `F` is not under `*`; the
in-tree carrier lives in `F`, so we state the constant directly." That hand-statement is correct but
it leaves `μ_n` **outside** Mathlib's `IsApproximateSubgroup` API — exactly the API the BGK route
needs to compose with a (future) sum–product estimate.

This file closes that interoperability gap by lifting to the group of units `Fˣ`, where the canonical
Mathlib object `rootsOfUnity n F : Subgroup Fˣ` lives. The bridge is `Mathlib`'s own
`IsApproximateSubgroup.subgroup : IsApproximateSubgroup 1 (H : Set G)` for a `SubgroupClass`, which we
specialise to the roots of unity and then weld back to the in-tree `μ_n` via the units-coercion image.

## What is welded (NON-MOMENT, sign-free, EXTEND-proven on Mathlib's approximate-subgroup API)

* `rootsOfUnity_isApproximateSubgroup` — `IsApproximateSubgroup (1 : ℝ) (↑(rootsOfUnity n F))`: the
  `n`-th roots of unity, as a subgroup of `Fˣ`, are an approximate subgroup with the **optimal**
  constant `K = 1` (a genuine subgroup, not merely approximate). This is the BGK multiplicative input
  living in Mathlib's actual `IsApproximateSubgroup` type, so it now composes with `card_pow_le`,
  `card_mul_self_le`, `IsApproximateSubgroup.image`, etc.
* `rootsOfUnity_card_pow_le` — `#((rootsOfUnity n F : Finset Fˣ) ^ k) ≤ #(rootsOfUnity n F)`: the
  `K = 1` specialisation of `IsApproximateSubgroup.card_pow_le`, i.e. **every** power set has cardinality
  at most the subgroup's — the exact `σₘ = 1` doubling at all orders, now machine-derived from the
  Mathlib API rather than restated.
* `rootsOfUnity_card_mul_self_le` — `#(R * R) ≤ #R`: the second-order doubling consequence.
* `coe_rootsOfUnity_image_eq_muN` — the WELD to the in-tree carrier: for `n ≥ 1`,
  `(Units.val '' (rootsOfUnity n F : Set Fˣ)) = (muN F n : Set F)`. The Mathlib subgroup object and
  the in-tree `μ_n` Finset are the same set under the units coercion, so the approximate-subgroup
  structure proven above transports to `BGKMultiplicativeInput`'s carrier.

## Why this matters (honest scope)

This is still the **easy** (multiplicative) half of the BGK dichotomy — trivial because `μ_n` is
literally a subgroup, so `K = 1`. The value added over `BGKMultiplicativeInput` is purely structural
plumbing: the in-tree `μ_n` is now connected to Mathlib's `IsApproximateSubgroup` type with the
optimal constant, which is the precondition for ever composing it with a formalised sum–product /
Plünnecke–Ruzsa estimate. The genuinely hard, multi-month half — deriving a contradiction from
`σₘ = 1` together with large additive energy `E^+(μ_n) ≫ n^{5/2}` — is **untouched**: Mathlib still has
no sum–product theorem over `𝔽_p`. No char-`p` transfer, no capacity, no beyond-Johnson `√(log)`
saving, no growth-law, nothing about the cliff-at-`n/2`. The multiplicative doubling is field- and
thickness-BLIND (a subgroup is a subgroup in any field, thin or thick) — so by the §3 meta-thm and
rule 3 it is **not** thinness-essential and CANNOT prove CORE; it is the sign-free shadow whose
contrast with additive Sidon-ness is the *configuration* of the wall, not a route around it.

`CORE M(μ_n) ≤ C·√(n·log(q/n))` with absolute `C` remains **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`/`axiom`/`native_decide`. Issue #444.
-/

open Finset
open scoped Pointwise

namespace ArkLib.ProximityGap.RootsOfUnityApproximateSubgroup

open ArkLib.ProximityGap (muN)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The `n`-th roots of unity are an `IsApproximateSubgroup 1` of `Fˣ`.** They form a genuine
subgroup of the group of units, so Mathlib's `IsApproximateSubgroup.subgroup` gives the optimal
approximate-subgroup constant `K = 1`. This is the BGK multiplicative input expressed in Mathlib's
`IsApproximateSubgroup` type (rather than the by-hand `muN_doubling_eq_one`), so it composes with the
`Combinatorics.Additive` API. -/
theorem rootsOfUnity_isApproximateSubgroup (n : ℕ) :
    IsApproximateSubgroup (1 : ℝ) ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ) :=
  IsApproximateSubgroup.subgroup

/-- The roots of unity as a `Finset Fˣ` (via the ambient `Fintype Fˣ`), used to state the cardinality
doubling consequences against Mathlib's `Finset`-level `card_pow_le`. -/
noncomputable def rouFinset (n : ℕ) : Finset Fˣ :=
  haveI : Fintype ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ) := Fintype.ofFinite _
  ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ).toFinset

@[simp] theorem coe_rouFinset (n : ℕ) :
    ((rouFinset n : Finset Fˣ) : Set Fˣ) = ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ) := by
  haveI : Fintype ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ) := Fintype.ofFinite _
  simp [rouFinset]

/-- **The exact `σₘ = 1` doubling at all orders, derived from the Mathlib API.** For the roots of
unity `R = rouFinset n` (as a `Finset Fˣ`), `#(R ^ k) ≤ #R` for every `k`: the `K = 1`
specialisation of `IsApproximateSubgroup.card_pow_le` (`#(A^k) ≤ K^(k-1) · #A` with `K = 1`). -/
theorem rootsOfUnity_card_pow_le (n : ℕ) (k : ℕ) :
    ((rouFinset (F := F) n) ^ k).card ≤ (rouFinset (F := F) n).card := by
  have h := (rootsOfUnity_isApproximateSubgroup (F := F) n)
  rw [← coe_rouFinset (F := F) n] at h
  have hle := h.card_pow_le (n := k)
  -- `#(A^k) ≤ K^(k-1) * #A` with `K = 1` collapses to `#(A^k) ≤ #A`.
  simp only [one_pow, one_mul] at hle
  exact_mod_cast hle

/-- **Second-order doubling: `#(R * R) ≤ #R`.** The `μ_n · μ_n = μ_n` / `σₘ = 1` fact in the units
group, derived (not restated) from the Mathlib approximate-subgroup API. -/
theorem rootsOfUnity_card_mul_self_le (n : ℕ) :
    ((rouFinset (F := F) n) * (rouFinset (F := F) n)).card ≤ (rouFinset (F := F) n).card := by
  have h := rootsOfUnity_card_pow_le (F := F) n 2
  simpa [pow_two] using h

/-- **The weld to the in-tree carrier.** For `n ≥ 1`, the units-coercion image of the Mathlib subgroup
`rootsOfUnity n F` is exactly the in-tree Finset `μ_n` (as a set in `F`). So the approximate-subgroup
structure proven above transports to `BGKMultiplicativeInput`'s carrier `muN F n`.

`⊆`: a root of unity `ζ : Fˣ` with `ζ^n = 1` has `(↑ζ)^n = 1` and `↑ζ ∈ μ_n`.
`⊇`: an element `x ∈ μ_n` has `x^n = 1` with `n ≥ 1`, so `x ≠ 0`, hence `x = ↑(Units.mk0 x _)` and
that unit is an `n`-th root of unity. -/
theorem coe_rootsOfUnity_image_eq_muN {n : ℕ} (hn : 1 ≤ n) :
    (Units.val '' ((rootsOfUnity n F : Subgroup Fˣ) : Set Fˣ)) = (muN F n : Set F) := by
  ext x
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    simp only [SetLike.mem_coe, mem_rootsOfUnity] at hζ
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and, muN]
    have : ((ζ : Fˣ) : F) ^ n = ((1 : Fˣ) : F) := by
      rw [← Units.val_pow_eq_pow_val, hζ]
    simpa using this
  · intro hx
    simp only [muN, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx
    -- `x^n = 1` with `n ≥ 1` ⟹ `x ≠ 0`.
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hx
      exact one_ne_zero hx.symm
    refine ⟨Units.mk0 x hx0, ?_, by simp⟩
    simp only [SetLike.mem_coe, mem_rootsOfUnity]
    ext
    push_cast
    simpa using hx

end ArkLib.ProximityGap.RootsOfUnityApproximateSubgroup

/-! ## Axiom audit — expected `propext`, `Classical.choice`, `Quot.sound` only. -/
open ArkLib.ProximityGap.RootsOfUnityApproximateSubgroup in
#print axioms rootsOfUnity_isApproximateSubgroup
open ArkLib.ProximityGap.RootsOfUnityApproximateSubgroup in
#print axioms rootsOfUnity_card_pow_le
open ArkLib.ProximityGap.RootsOfUnityApproximateSubgroup in
#print axioms rootsOfUnity_card_mul_self_le
open ArkLib.ProximityGap.RootsOfUnityApproximateSubgroup in
#print axioms coe_rootsOfUnity_image_eq_muN
