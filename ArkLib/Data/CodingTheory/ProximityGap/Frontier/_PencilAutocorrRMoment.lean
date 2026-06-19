/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrSubgroupExact

set_option linter.style.longLine false

/-!
# The UNIFORM r-th unsigned subgroup autocorrelation moment: `∑_ρ |H ∩ ρ·H|^r = |H|^{r+1}` (#444)

`PencilAutocorrSubgroupExact.subgroup_multiplicativeEnergy_eq_card_cube` proves the `r = 2`
(multiplicative-energy) case, `∑_ρ |H ∩ ρ·H|² = |H|³`, and `PencilAutocorrSumDoubleCount` the `r = 1`
(double-count) case `∑_ρ |H ∩ ρ·H| = |H|²`. Both are the same all-or-nothing structure read at a
fixed exponent. This file proves the **single uniform theorem** that subsumes every exponent `r ≥ 1`:

> **`∑_{ρ∈G} (H ∩ dilate ρ H).card ^ r = H.card ^ (r + 1)`** for every `r ≥ 1`.

Mechanism is a direct corollary of the EXACT all-or-nothing autocorrelation
(`subgroup_autocorr_exact`): each summand is `(if ρ∈H then |H| else 0)^r = if ρ∈H then |H|^r else 0`
(using `r ≥ 1` so the `ρ∉H` branch is `0^r = 0`), so the sum is
`(#{ρ : ρ∈H}) · |H|^r = |H| · |H|^r = |H|^{r+1}`. No `r`-specific argument — the same all-or-nothing
profile delivers every positive moment.

The `r ≥ 1` hypothesis is ESSENTIAL, not cosmetic: at `r = 0` the formula is FALSE (the LHS counts
`0^0 = 1` on the outside shifts too, giving `∑_ρ 1 = |G| ≠ |H| = |H|^{0+1}`). This is recorded in
`subgroup_autocorr_zeroth_moment_eq_card_univ` (the honest `r = 0` value) so no one mis-instantiates
the uniform law below its valid range.

This is the unsigned analogue of the signed `ResonanceConjecture` uniform-ceiling chain
(`_ResonanceMomentGeneralCeiling`): there the per-`r` *upper* bound `T(r) ≤ m(m-1)^{2(r-1)}` was the
content; here the UNSIGNED subgroup autocorrelation collapses to an EXACT closed form at every `r ≥ 1`
(no `√(log)` cancellation in the unsigned count), which is precisely WHY the prize cancellation must
live in the SIGNED phase. The unsigned autocorrelation moments are maximally rigid at all orders.

## Honest scope
NOT a CORE closure, NOT a refutation. It EXTENDS the proven `r = 2` energy theorem to a uniform
all-`r` closed form (frontier-MOVEMENT: a general theorem, not a point bound). NON-MOMENT in the
prize sense (this is the *unsigned* multiplicative autocorrelation, sign-free additive combinatorics),
field- and thickness-universal, EXTEND-proven (consumes `subgroup_autocorr_exact`). Specialises to
`r = 1` (`|H|²`, double-count) and `r = 2` (`|H|³`, energy). No capacity / beyond-Johnson /
cliff-at-n/2 claim. `CORE M(μ_n) ≤ C·√(n·log(q/n))` OPEN — the signed phase carries the wall.
-/

open Finset

namespace ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- **THE UNIFORM r-th UNSIGNED SUBGROUP AUTOCORRELATION MOMENT.** For a multiplicative subgroup
`H` (closed under `*`, `⁻¹`, containing `1`) and every exponent `r ≥ 1`:

  `∑_{ρ∈G} (H ∩ dilate ρ H).card ^ r = H.card ^ (r + 1)`.

The all-or-nothing autocorrelation makes every unsigned moment exact: full `|H|^r` on the `|H|`
inside-shifts, zero outside, summing to `|H| · |H|^r = |H|^{r+1}`. The `1 ≤ r` hypothesis is
essential (`0^r = 0` on the outside shifts); see `subgroup_autocorr_zeroth_moment_eq_card_univ`. -/
theorem subgroup_autocorr_rmoment [Fintype G] {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    {r : ℕ} (hr : 1 ≤ r) :
    ∑ ρ : G, ((H ∩ dilate ρ H).card) ^ r = H.card ^ (r + 1) := by
  -- each summand is (if ρ∈H then |H| else 0)^r = if ρ∈H then |H|^r else 0  (uses 0^r = 0 via 1≤r)
  have hpt : ∀ ρ : G, ((H ∩ dilate ρ H).card) ^ r
      = if ρ ∈ H then H.card ^ r else 0 := by
    intro ρ
    rw [subgroup_autocorr_exact hmul hinv ρ]
    by_cases hρ : ρ ∈ H
    · simp [hρ]
    · rw [if_neg hρ, if_neg hρ, zero_pow (by omega : r ≠ 0)]
  rw [Finset.sum_congr rfl (fun ρ _ => hpt ρ)]
  -- ∑_ρ (if ρ∈H then |H|^r else 0) = (#{ρ : ρ∈H}) • |H|^r = |H| • |H|^r = |H|^{r+1}
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const]
  rw [smul_eq_mul, pow_succ']

/-- **The `r = 1` double-count specialisation:** `∑_ρ |H ∩ ρ·H| = |H|²`. -/
theorem subgroup_autocorr_first_moment [Fintype G] {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    ∑ ρ : G, (H ∩ dilate ρ H).card = H.card ^ 2 := by
  have h := subgroup_autocorr_rmoment hmul hinv (r := 1) (le_refl 1)
  simpa using h

/-- **The `r = 2` energy specialisation:** `∑_ρ |H ∩ ρ·H|² = |H|³` (re-derived uniformly, matching
`subgroup_multiplicativeEnergy_eq_card_cube`). -/
theorem subgroup_autocorr_second_moment [Fintype G] {H : Finset G}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    ∑ ρ : G, ((H ∩ dilate ρ H).card) ^ 2 = H.card ^ 3 :=
  subgroup_autocorr_rmoment hmul hinv (r := 2) (by omega)

/-- **The HONEST `r = 0` value (NOT `|H|`):** `∑_ρ |H ∩ ρ·H|^0 = ∑_ρ 1 = |G|`. This records that
the uniform law `= |H|^{r+1}` is FALSE at `r = 0` (it would force `|G| = |H|`), so the `1 ≤ r`
hypothesis in `subgroup_autocorr_rmoment` is essential, not cosmetic. -/
theorem subgroup_autocorr_zeroth_moment_eq_card_univ [Fintype G] (H : Finset G) :
    ∑ _ρ : G, ((H ∩ dilate _ρ H).card) ^ 0 = Fintype.card G := by
  simp only [pow_zero, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

end ProximityGap.Frontier.PencilAutocorrelation
