/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidualRefutation

/-!
# Counterexample to the bare closed-boundary residual at the affine-line index `k = 1`

`BoundaryCardResidualRefutation` exhibits a `ZMod 5` witness that refutes the bare
`BoundaryCardResidual` at curve dimension `k = 2`.  The BCIKS20 **affine-line** correlated
agreement keystone `RS_correlatedAgreement_affineLines`
(`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean`), however, consumes the
boundary obligation at the affine-line index `k = 1`:

```
theorem RS_correlatedAgreement_affineLines ...
    (hStrictCoeff : StrictCoeffPolysResidual (k := 1) ...)
    (hBoundaryCard : BoundaryCardResidual (k := 1) ...)
    (hδ : δ ≤ 1 - ReedSolomon.sqrtRate deg domain) : ...
```

This file closes that gap.  Reusing the *same* small-field witness as the `k = 2` refutation —
field `ZMod 5`, domain `Fin 4`, Reed–Solomon degree `1` (constant codewords), the exact Johnson
square-root endpoint `δ = 1 - sqrt(1/4) = 1/2` — but with the **two**-word affine stack
`uBad₁ 0 = 0`, `uBad₁ 1 = domain`, we prove

* `not_jointAgreement_affineLine`   — `jointAgreement` fails for `uBad₁` at the boundary, and
* `not_boundaryCardResidual_affineLine` — `¬ BoundaryCardResidual (k := 1) ...`.

The obstruction is identical to the `k = 2` case and does not depend on the stack width: word `1`
of the stack is the injective `domain`, which can agree with a constant (degree-`1`) codeword on at
most one coordinate, whereas the boundary floor `⌊(1 - √ρ)·4⌋ = 2` forces any joint-agreement set
to have cardinality at least two.  The good-coefficient set is nonempty (the parameter `z = 0`
yields the zero codeword), so the bare residual's hypothesis is met yet its conclusion is false.

**Consequence.**  The boundary hypothesis of `RS_correlatedAgreement_affineLines` is *unsatisfiable*
at the exact square-root endpoint for these parameters.  Since the strict-radius companion
`RS_correlatedAgreement_affineLines_strict` (`δ < 1 - √ρ`) needs no boundary residual at all, the
only content the non-strict keystone adds over its strict form is the single endpoint
`δ = 1 - √ρ` — and that endpoint is gated behind a residual that is provably false.  Boundary work
at `k = 1` must therefore keep a genuinely stronger threshold/cardinality hypothesis (the
large-field-guarded `BoundaryCardLatticeData` route), exactly as at `k = 2`.
-/

namespace ArkLib

namespace BoundaryCardResidualAffineLineRefutation

open ArkLib ArkLib.BoundaryCardResidual ArkLib.BoundaryCardResidualRefutation
  ProximityGap Code
open scoped BigOperators NNReal ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Affine-line bad stack: `u 0` is the zero codeword, `u 1` separates all four coordinates.
This is the two-word (`k = 1`) analogue of `BoundaryCardResidualRefutation.uBad`. -/
def uBad₁ : WordStack F (Fin 2) I :=
  fun t i => if t = 1 then domain i else 0

/-- The good-coefficient set is nonempty at the boundary: the affine parameter `z = 0` collapses
the curve word `∑ t, z^t • uBad₁ t` to `uBad₁ 0 = 0`, the zero codeword, which is `δ`-close. -/
theorem good_nonempty_affineLine :
    0 < (RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) uBad₁
      (1 - ReedSolomon.sqrtRate 1 domain)).card := by
  classical
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  have hzero_mem :
      (0 : I → F) ∈ (ReedSolomon.code domain 1 : Set (I → F)) :=
    (ReedSolomon.code domain 1).zero_mem
  have hrel :
      δᵣ((0 : I → F), (ReedSolomon.code domain 1 : Set (I → F))) ≤
        (1 - ReedSolomon.sqrtRate 1 domain : ℝ≥0) := by
    rw [Code.relDistFromCode_eq_distFromCode_div,
      Code.distFromCode_of_mem (ReedSolomon.code domain 1 : Set (I → F)) hzero_mem]
    simp
  have hsum :
      (∑ t : Fin 2, (0 : F) ^ (t : ℕ) • uBad₁ t) = (0 : I → F) := by
    funext i
    fin_cases i <;> simp [uBad₁]
  simpa [RS_goodCoeffsCurve, hsum] using hrel

/-- `jointAgreement` fails for the affine-line bad stack at the exact square-root boundary.
Word `1` of the stack is the injective `domain`; it can agree with a constant degree-`1` codeword
on at most one coordinate, but the boundary floor forces any joint-agreement set to have
cardinality at least two. -/
theorem not_jointAgreement_affineLine :
    ¬ jointAgreement (C := ReedSolomon.code domain 1)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) (W := uBad₁) := by
  classical
  rintro ⟨S, hS, v, hv⟩
  have hS_two : 2 ≤ S.card := by
    rw [ge_iff_le,
      ← Code.relDist_floor_bound_iff_complement_bound
        (Fintype.card I) S.card (1 - ReedSolomon.sqrtRate 1 domain)] at hS
    rw [boundary_floor_eq_two] at hS
    norm_num [I] at hS
    exact hS
  have hS_one : S.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have hvconst := code_deg_one_constant (hv 1).1 a b
    have ha_eq := (Finset.mem_filter.mp ((hv 1).2 ha)).2
    have hb_eq := (Finset.mem_filter.mp ((hv 1).2 hb)).2
    have ha_dom : v 1 a = domain a := by simpa [uBad₁] using ha_eq
    have hb_dom : v 1 b = domain b := by simpa [uBad₁] using hb_eq
    have hdom : domain a = domain b := by
      rw [← ha_dom, hvconst, hb_dom]
    exact domain.injective hdom
  omega

/-- **The bare closed-boundary residual is false at the affine-line index `k = 1`.**
This is the boundary obligation consumed by `RS_correlatedAgreement_affineLines`; the small-field
`ZMod 5` witness shows its hypothesis is met (nonempty good set) yet its conclusion
(`jointAgreement`) fails, so the residual cannot be discharged as stated. -/
theorem not_boundaryCardResidual_affineLine :
    ¬ BoundaryCardResidual (k := 1) (deg := 1) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain) := by
  intro h
  exact not_jointAgreement_affineLine (h (by norm_num) uBad₁ rfl good_nonempty_affineLine)

/-! ## The affine-line *conclusion* fails at the boundary

The result above shows the boundary *hypothesis* `BoundaryCardResidual (k := 1)` is unsatisfiable
at the endpoint.  We now show the stronger fact that the affine-line correlated-agreement
*conclusion* `δ_ε_correlatedAgreementAffineLines` itself is **false** at the exact square-root
endpoint with `ε = errorBound`.  Hence `RS_correlatedAgreement_affineLines` adds no genuine content
over its strict companion: at the endpoint its conclusion does not even hold. -/

/-- For `k = 1` the affine line `u 0 + z • u 1` is exactly the curve `∑ t, z^t • u t`. -/
theorem uBad₁_affine_eq_curve (z : F) :
    uBad₁ 0 + z • uBad₁ 1 = ∑ t : Fin 2, (z ^ (t : ℕ)) • uBad₁ t := by
  rw [Fin.sum_univ_two]
  simp

/-- The probability that the affine line through `uBad₁` is `δ`-close to the code is positive at
the boundary: the parameter `z = 0` collapses the line to `uBad₁ 0 = 0`, the zero codeword.  Uses
the proven `good_nonempty_affineLine` through the curve-probability cardinality identity. -/
theorem affineLine_probability_pos :
    Pr_{let z ← $ᵖ F}[δᵣ(uBad₁ 0 + z • uBad₁ 1, ReedSolomon.code domain 1)
        ≤ 1 - ReedSolomon.sqrtRate 1 domain] > (0 : ENNReal) := by
  classical
  simp only [uBad₁_affine_eq_curve]
  change
    Pr_{let z ← $ᵖ F}[δᵣ(∑ t : Fin (1 + 1), (z ^ (t : ℕ)) • uBad₁ t,
        ReedSolomon.code domain 1) ≤
          ((1 - ReedSolomon.sqrtRate 1 domain : ℝ≥0) : ENNReal)] > (0 : ENNReal)
  have hPr := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := 1) (deg := 1) (domain := domain)
    (δ := 1 - ReedSolomon.sqrtRate 1 domain) uBad₁
  rw [hPr]
  have hcard : (0 : ℝ≥0) <
      ((RS_goodCoeffsCurve (k := 1) (deg := 1) (domain := domain) uBad₁
        (1 - ReedSolomon.sqrtRate 1 domain)).card : ℝ≥0) := by
    exact_mod_cast good_nonempty_affineLine
  exact_mod_cast
    (div_pos hcard (by norm_num [F] : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0)))

/-- **The affine-line correlated-agreement conclusion is false at the boundary.**
At the exact square-root endpoint `δ = 1 - √ρ` with `ε = errorBound = 0`, the bad stack `uBad₁`
meets the probability premise (`Pr > 0 = ε`) yet fails `jointAgreement`.  So the non-strict
affine-line keystone `RS_correlatedAgreement_affineLines` is vacuous at the endpoint: its
conclusion does not hold there, only its (unsatisfiable) boundary hypothesis would supply it. -/
theorem not_delta_epsilon_correlatedAgreementAffineLines_boundary :
    ¬ δ_ε_correlatedAgreementAffineLines (F := F) (A := F) (ι := I)
      (C := ReedSolomon.code domain 1)
      (δ := 1 - ReedSolomon.sqrtRate 1 domain)
      (ε := errorBound (1 - ReedSolomon.sqrtRate 1 domain) 1 domain) := by
  intro h
  refine not_jointAgreement_affineLine (h uBad₁ ?_)
  rw [boundary_errorBound_eq_zero]
  simpa using affineLine_probability_pos

end BoundaryCardResidualAffineLineRefutation

end ArkLib

/-! ## Axiom audit -/
#print axioms ArkLib.BoundaryCardResidualAffineLineRefutation.good_nonempty_affineLine
#print axioms ArkLib.BoundaryCardResidualAffineLineRefutation.not_jointAgreement_affineLine
#print axioms ArkLib.BoundaryCardResidualAffineLineRefutation.not_boundaryCardResidual_affineLine
#print axioms ArkLib.BoundaryCardResidualAffineLineRefutation.affineLine_probability_pos
#print axioms ArkLib.BoundaryCardResidualAffineLineRefutation.not_delta_epsilon_correlatedAgreementAffineLines_boundary
