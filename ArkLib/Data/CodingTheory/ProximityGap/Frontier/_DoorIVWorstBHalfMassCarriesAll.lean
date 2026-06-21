/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVComplexRayCoherence

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) constraint: at the worst frequency the coset-half COHERENCE is exactly 1, so the
period magnitude equals the HALF-MASS and the cross-half coherence contributes NOTHING (#444)

## Probe-grounded motivation (rule-2: probe before formalize)

The prize is localized to `M(n) = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(b·x)`.  Door-(iv)'s
"Shaw-value" localized object (brief / Shaw essay 2026-06-18, Lane 1) is the **index-2 coset-half
coherence**
`ρ(b) = twoPieceNormCoherence A_b B_b = ‖A_b + B_b‖ / (‖A_b‖ + ‖B_b‖)`,
where `A_b, B_b` are the two index-2 (squares-coset) half-sums, `η_b = A_b + B_b`.  The live hope was
a coherence/anti-alignment bound: if the two halves DESTRUCTIVELY interfere at the worst `b`
(`ρ(b*) < 1` with growing deficit), that interference could carry √-cancellation WITHOUT a moment or
a √q-completion.

PROBE (`scripts/probes/probe_dooriv_worstb_coherence_deficit_law.py`, proper `μ_n < F_p*`, `p ≫ n³`,
structured primes, `n = 16..256`, never `n = q−1`).  At the worst frequency `b*`, on the **canonical
index-2 squares-coset split**, in EVERY prize-regime row:

  `ρ(b*) = 1.000000`   exactly   (deficit `1 − ρ(b*) ≡ 0`; measured `angle(A_{b*}, B_{b*}) = 0.000°`).

(Cross-check: an arbitrary contiguous halving gives `ρ ≈ 0.99 < 1`, so `ρ ≡ 1` is SPECIFIC to the
canonical squares-coset split — the halves are perfectly co-linear there.)  Mechanism: `μ_n` is cyclic
of even order; negation symmetry forces the worst-`b` period real up to a global phase, and the two
squares-coset halves of that real period point along a COMMON ray, so they are `SameRay`.

## The load-bearing fact (this file, axiom-clean)

By `twoPieceNormCoherence_eq_one_iff_sameRay`, `ρ = 1 ↔ SameRay`.  We add the consequence the probe
demands: **when the two halves are `SameRay`, the norm of the combined period EQUALS the half-mass**
`‖A + B‖ = ‖A‖ + ‖B‖`, i.e. the coherence factor is exactly `1` and contributes NO saving.  Hence
`M = ρ(b*)·H(b*) = 1·H(b*) = H(b*)` with `H(b*) = ‖A_{b*}‖ + ‖B_{b*}‖`: the ENTIRE magnitude (and
therefore the entire √-cancellation) is carried by the **half-mass**, each half being itself a thinner
period sum (order `n/2`).  This LOCALIZES any door-(iv) saving OFF the index-2 coherence object and
ONTO the self-similar half-mass recursion `μ_n ⊃ (μ_n)² ⊃ …`.

This is a **refutation with mechanism** (it removes the index-2 coherence lever and pins the burden on
the descent), NOT a CORE/cancellation/completion/moment/capacity claim: it does not bound `M(n)`.  It
sharpens `_DoorIVComplexRayCoherence` (the `ρ = 1 ↔ SameRay` characterization) into the worst-`b`
saturating instance the probe exhibits.
-/

namespace ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll

open ProximityGap.Frontier.DoorIVComplexRayCoherence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- **SameRay halves saturate the triangle inequality**: when `x` and `y` lie on a common nonnegative
ray, the norm of their sum equals the sum of their norms.  (Library fact, packaged at the door-(iv)
interface.) -/
theorem norm_add_eq_of_sameRay {x y : E} (h : SameRay ℝ x y) :
    ‖x + y‖ = ‖x‖ + ‖y‖ :=
  h.norm_add

/-- **The combined magnitude equals the half-mass at coherence one.**  If the two coset-halves achieve
the maximal two-piece coherence `ρ = 1` (positive denominator), then the norm of the period
`‖x + y‖` equals the half-mass `‖x‖ + ‖y‖` exactly — the coherence factor contributes nothing. -/
theorem norm_add_eq_halfMass_of_coherence_one {x y : E} (hden : 0 < ‖x‖ + ‖y‖)
    (hρ : twoPieceNormCoherence x y = 1) :
    ‖x + y‖ = ‖x‖ + ‖y‖ :=
  norm_add_eq_of_sameRay ((twoPieceNormCoherence_eq_one_iff_sameRay hden).1 hρ)

/-- **Worst-`b` localization, stated on the coherence object.**  At the worst frequency the probe shows
the canonical index-2 halves are `SameRay`; therefore the period magnitude `M = ‖A + B‖` equals the
half-mass `H = ‖A‖ + ‖B‖`.  Any further √-cancellation must come from `H` (the half-masses), since the
cross-half coherence factor is pinned at exactly `1`. -/
theorem worstB_magnitude_eq_halfMass_of_sameRay {A B : E} (h : SameRay ℝ A B) :
    ‖A + B‖ = ‖A‖ + ‖B‖ :=
  norm_add_eq_of_sameRay h

/-- **No coherence saving at the worst `b` (contrapositive form).**  A strict magnitude saving below the
half-mass, `‖A + B‖ < ‖A‖ + ‖B‖`, REQUIRES the halves to be non-`SameRay`.  The probe shows the worst-`b`
canonical halves ARE `SameRay` (`ρ ≡ 1`), so no such cross-half saving is available there: any door-(iv)
saving must be internal to the half-masses (the recursion), not between the two coset-halves. -/
theorem not_sameRay_of_magnitude_lt_halfMass {A B : E}
    (hlt : ‖A + B‖ < ‖A‖ + ‖B‖) :
    ¬ SameRay ℝ A B := by
  intro hsame
  exact absurd (worstB_magnitude_eq_halfMass_of_sameRay hsame) (ne_of_lt hlt)

/-- **The coherence factor is exactly one at the worst `b`.**  Restating saturation as `ρ = 1`: when the
halves are `SameRay` (probe: worst-`b` canonical split) with positive half-mass, the two-piece coherence
equals one, so `M = ρ · H = H`. -/
theorem coherence_eq_one_of_sameRay {A B : E} (hden : 0 < ‖A‖ + ‖B‖)
    (h : SameRay ℝ A B) :
    twoPieceNormCoherence A B = 1 :=
  (twoPieceNormCoherence_eq_one_iff_sameRay hden).2 h

/-- **Capstone constraint (this file).**  At positive half-mass, the following are EQUIVALENT
characterizations of the saturated worst-`b` configuration the probe exhibits:
`ρ = 1`  ↔  `SameRay`  ↔  `M = H` (the period magnitude equals the half-mass).  Hence the cross-half
coherence is a dead lever exactly when the magnitude already equals the half-mass — which the probe
shows holds at the worst `b` for all prize-regime `n`. -/
theorem coherence_one_iff_magnitude_eq_halfMass {A B : E} (hden : 0 < ‖A‖ + ‖B‖) :
    twoPieceNormCoherence A B = 1 ↔ ‖A + B‖ = ‖A‖ + ‖B‖ := by
  constructor
  · intro hρ; exact norm_add_eq_halfMass_of_coherence_one hden hρ
  · intro hM
    unfold twoPieceNormCoherence
    rw [hM, div_self (ne_of_gt hden)]

#print axioms ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.norm_add_eq_halfMass_of_coherence_one
#print axioms ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.worstB_magnitude_eq_halfMass_of_sameRay
#print axioms ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.not_sameRay_of_magnitude_lt_halfMass
#print axioms ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.coherence_one_iff_magnitude_eq_halfMass

end ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll
