/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Shaw-value capstone for #444

Door (iv) has localized the prize to the single Gauss-period sup norm

`M(q,n) = max_{b ≠ 0} |∑_{x∈μ_n} e_q(bx)|`.

Shaw's useful normalization is the dimensionless value

`Sh(q,n) = M(q,n) / sqrt (n * log (q / n))`.

This file is deliberately elementary and axiom-clean: it proves that the normalized statement
`Sh(q,n) ≤ C` is *definitionally equivalent* to the prize-scale core inequality
`M(q,n) ≤ C * sqrt (n * log (q / n))`, pointwise and uniformly over any index type.

Nothing here proves the open Gauss-period bound. It packages the reduction target so later formal
work can cite one exact capstone instead of repeatedly re-normalizing the same inequality.

The final `O(1)` theorem records the precise Shaw-value essay slogan: on any positive-scale prize
family, `Sh(n)=O(1)` is equivalent to the square-root `CORE` bound with one absolute constant.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open scoped Real

namespace ProximityGap.Frontier.ShawValueCapstone

/-- The prize normalization scale `sqrt (n * log (q / n))`. -/
noncomputable def shawScale (q n : ℝ) : ℝ :=
  Real.sqrt (n * Real.log (q / n))

/-- The Shaw value: the Gauss-period sup norm divided by the prize scale. -/
noncomputable def shawValue (q n M : ℝ) : ℝ :=
  M / shawScale q n

/-- In the genuine prize regime `q > n > 0`, the Shaw normalization scale is positive.
This discharges the only analytic side condition in the capstone from the usual thin-subgroup
size assumptions. -/
theorem shawScale_pos_of_pos_lt {q n : ℝ} (hn : 0 < n) (hnq : n < q) :
    0 < shawScale q n := by
  unfold shawScale
  apply Real.sqrt_pos.2
  apply mul_pos hn
  apply Real.log_pos
  have hdiv : n / n < q / n := div_lt_div_of_pos_right hnq hn
  simpa [div_self (ne_of_gt hn)] using hdiv

/-- Pointwise Shaw-value capstone: after the positive-scale guard, `Sh(q,n) ≤ C` is exactly the
prize core bound `M(q,n) ≤ C * sqrt (n * log(q/n))`. -/
theorem shawValue_le_iff_core_bound {q n M C : ℝ} (hscale : 0 < shawScale q n) :
    shawValue q n M ≤ C ↔ M ≤ C * shawScale q n := by
  unfold shawValue
  exact div_le_iff₀ hscale

/-- The same equivalence in the direction most often cited in prose: a prize-scale core bound is
identical to a dimensionless `O(1)` Shaw value with the same constant. -/
theorem core_bound_iff_shawValue_le {q n M C : ℝ} (hscale : 0 < shawScale q n) :
    M ≤ C * shawScale q n ↔ shawValue q n M ≤ C := by
  exact (shawValue_le_iff_core_bound (q := q) (n := n) (M := M) (C := C) hscale).symm

/-- Uniform Shaw boundedness over an arbitrary family of prize instances.  This is the formal
`Sh(n)=O(1)` object, with the quantifier left abstract so callers can instantiate it with the
thin dyadic tower, the all-primes family, or a finite verified slate. -/
def UniformShawBound {ι : Type*} (q n M : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i : ι, shawValue (q i) (n i) (M i) ≤ C

/-- Uniform prize-core bound over the same family and with the same absolute constant. -/
def UniformCoreBound {ι : Type*} (q n M : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i : ι, M i ≤ C * shawScale (q i) (n i)

/-- **Prize `↔` bounded Shaw value.**  Under the pointwise positive-scale guard, a uniform
prize-core inequality is equivalent to a uniform bound on Shaw's dimensionless value.

This is the citable capstone for the reduction target: proving the proximity prize's Gauss-period
core with an absolute constant `C` is the same thing as proving `Sh(q,n) ≤ C` uniformly. -/
theorem uniformCoreBound_iff_uniformShawBound {ι : Type*} {q n M : ι → ℝ} {C : ℝ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i)) :
    UniformCoreBound q n M C ↔ UniformShawBound q n M C := by
  constructor
  · intro h i
    exact (core_bound_iff_shawValue_le (q := q i) (n := n i) (M := M i) (C := C)
      (hscale i)).mp (h i)
  · intro h i
    exact (shawValue_le_iff_core_bound (q := q i) (n := n i) (M := M i) (C := C)
      (hscale i)).mp (h i)

/-- Prize-regime specialization of the uniform capstone.  If every family member lies in the thin
subgroup size regime `q_i > n_i > 0`, then the uniform prize core bound is equivalent to a uniform
bound on Shaw's value, with no separate scale hypothesis. -/
theorem uniformCoreBound_iff_uniformShawBound_of_pos_lt {ι : Type*} {q n M : ι → ℝ} {C : ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    UniformCoreBound q n M C ↔ UniformShawBound q n M C := by
  exact uniformCoreBound_iff_uniformShawBound (q := q) (n := n) (M := M) (C := C)
    (fun i => shawScale_pos_of_pos_lt (hn i) (hnq i))

/-- `Sh(n)=O(1)` on an indexed family: one nonnegative absolute constant bounds Shaw value. -/
def ShawOOneOn {ι : Type*} (q n M : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ UniformShawBound q n M C

/-- Prize-style square-root cancellation with one nonnegative absolute constant. -/
def CorePrizeBoundOn {ι : Type*} (q n M : ι → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ UniformCoreBound q n M C

/-- **Shaw-value essay slogan, formalized.**  On a positive-scale family, `Sh(n)=O(1)` is exactly
the prize-scale square-root `CORE` bound, with the same absolute constant and no hidden loss. -/
theorem shawOOneOn_iff_corePrizeBoundOn {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i)) :
    ShawOOneOn q n M ↔ CorePrizeBoundOn q n M := by
  constructor
  · rintro ⟨C, hC, hSh⟩
    exact ⟨C, hC, (uniformCoreBound_iff_uniformShawBound
      (q := q) (n := n) (M := M) (C := C) hscale).2 hSh⟩
  · rintro ⟨C, hC, hCore⟩
    exact ⟨C, hC, (uniformCoreBound_iff_uniformShawBound
      (q := q) (n := n) (M := M) (C := C) hscale).1 hCore⟩

/-- Prize-regime version of the `O(1)` capstone, using only `q_i > n_i > 0` for scale positivity. -/
theorem shawOOneOn_iff_corePrizeBoundOn_of_pos_lt {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    ShawOOneOn q n M ↔ CorePrizeBoundOn q n M :=
  shawOOneOn_iff_corePrizeBoundOn (q := q) (n := n) (M := M)
    (fun i => shawScale_pos_of_pos_lt (hn i) (hnq i))


/-- Plancherel/Johnson-floor normalization: if `sqrt n ≤ M`, then Shaw's value is at least
`sqrt n / sqrt(n log(q/n))`.  This records the floor in normalized units without claiming any
upper bound. -/
theorem shawValue_floor_of_sqrt_le {q n M : ℝ} (hscale : 0 < shawScale q n)
    (hfloor : Real.sqrt n ≤ M) :
    Real.sqrt n / shawScale q n ≤ shawValue q n M := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hfloor (le_of_lt hscale)

/-- Trivial-ceiling normalization: if `M ≤ n`, then `Sh(q,n) ≤ n / sqrt(n log(q/n))`.  This is the
formal bookkeeping counterpart of the elementary `M ≤ n` ceiling, not a prize-strength estimate. -/
theorem shawValue_trivial_ceiling_of_le {q n M : ℝ} (hscale : 0 < shawScale q n)
    (hceil : M ≤ n) :
    shawValue q n M ≤ n / shawScale q n := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hceil (le_of_lt hscale)

/-- Two-sided Shaw-value corridor.  If a raw Gauss-period norm is trapped between a lower certificate
`L` and an upper certificate `U`, then the normalized Shaw value is trapped between the same
certificates divided by the prize scale.  This is pure normalization bookkeeping: it packages the
Plancherel/Johnson floor and any available ceiling in the dimensionless units used by Shaw's
`prize ↔ Sh(n)=O(1)` capstone, without asserting any new analytic bound. -/
theorem shawValue_mem_corridor_of_mem_raw_corridor {q n M L U : ℝ} (hscale : 0 < shawScale q n)
    (hlo : L ≤ M) (hhi : M ≤ U) :
    L / shawScale q n ≤ shawValue q n M ∧ shawValue q n M ≤ U / shawScale q n := by
  constructor
  · unfold shawValue
    exact div_le_div_of_nonneg_right hlo (le_of_lt hscale)
  · unfold shawValue
    exact div_le_div_of_nonneg_right hhi (le_of_lt hscale)

/-- Prize-regime corridor specialization.  The usual thin-regime guard `q > n > 0` supplies the
positive scale, so any raw interval `L ≤ M ≤ U` transfers directly to Shaw-normalized units. -/
theorem shawValue_mem_corridor_of_mem_raw_corridor_of_pos_lt {q n M L U : ℝ}
    (hn : 0 < n) (hnq : n < q) (hlo : L ≤ M) (hhi : M ≤ U) :
    L / shawScale q n ≤ shawValue q n M ∧ shawValue q n M ≤ U / shawScale q n := by
  exact shawValue_mem_corridor_of_mem_raw_corridor (q := q) (n := n) (M := M) (L := L) (U := U)
    (shawScale_pos_of_pos_lt hn hnq) hlo hhi


/-- Exact two-sided interval capstone for Shaw normalization.  A normalized interval
`L ≤ Sh(q,n) ≤ U` is equivalent, under the positive-scale guard, to the raw interval obtained by
multiplying both endpoints by the prize scale.  This is the bidirectional consumer-facing form of the
reduction: every Shaw corridor is exactly the corresponding raw Gauss-period corridor, with no hidden
loss and no analytic input. -/
theorem shawValue_mem_interval_iff_raw_mem_scaled_interval {q n M L U : ℝ}
    (hscale : 0 < shawScale q n) :
    (L ≤ shawValue q n M ∧ shawValue q n M ≤ U) ↔
      L * shawScale q n ≤ M ∧ M ≤ U * shawScale q n := by
  unfold shawValue
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨(le_div_iff₀ hscale).mp hlo, (div_le_iff₀ hscale).mp hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨(le_div_iff₀ hscale).mpr hlo, (div_le_iff₀ hscale).mpr hhi⟩

/-- Prize-regime specialization of the exact two-sided Shaw interval equivalence. -/
theorem shawValue_mem_interval_iff_raw_mem_scaled_interval_of_pos_lt {q n M L U : ℝ}
    (hn : 0 < n) (hnq : n < q) :
    (L ≤ shawValue q n M ∧ shawValue q n M ≤ U) ↔
      L * shawScale q n ≤ M ∧ M ≤ U * shawScale q n := by
  exact shawValue_mem_interval_iff_raw_mem_scaled_interval (q := q) (n := n) (M := M)
    (L := L) (U := U) (shawScale_pos_of_pos_lt hn hnq)


/-- Uniform-family version of the exact Shaw interval capstone.  A family lies pointwise in the
normalized corridor `L ≤ Sh_i ≤ U` iff the raw Gauss-period norms lie pointwise in the scaled corridor
`L*scale_i ≤ M_i ≤ U*scale_i`.  This is the family-level corridor analogue of
`prize ↔ bounded Shaw value`, with no hidden loss and no analytic input. -/
theorem uniformShawInterval_iff_uniformRawScaledInterval {ι : Type*} {q n M : ι → ℝ} {L U : ℝ}
    (hscale : ∀ i : ι, 0 < shawScale (q i) (n i)) :
    (∀ i : ι, L ≤ shawValue (q i) (n i) (M i) ∧ shawValue (q i) (n i) (M i) ≤ U) ↔
      (∀ i : ι, L * shawScale (q i) (n i) ≤ M i ∧
        M i ≤ U * shawScale (q i) (n i)) := by
  constructor
  · intro h i
    exact (shawValue_mem_interval_iff_raw_mem_scaled_interval
      (q := q i) (n := n i) (M := M i) (L := L) (U := U) (hscale i)).mp (h i)
  · intro h i
    exact (shawValue_mem_interval_iff_raw_mem_scaled_interval
      (q := q i) (n := n i) (M := M i) (L := L) (U := U) (hscale i)).mpr (h i)

/-- Prize-regime specialization of the uniform-family exact Shaw interval capstone. -/
theorem uniformShawInterval_iff_uniformRawScaledInterval_of_pos_lt {ι : Type*}
    {q n M : ι → ℝ} {L U : ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    (∀ i : ι, L ≤ shawValue (q i) (n i) (M i) ∧ shawValue (q i) (n i) (M i) ≤ U) ↔
      (∀ i : ι, L * shawScale (q i) (n i) ≤ M i ∧
        M i ≤ U * shawScale (q i) (n i)) := by
  exact uniformShawInterval_iff_uniformRawScaledInterval (q := q) (n := n) (M := M)
    (L := L) (U := U) (fun i => shawScale_pos_of_pos_lt (hn i) (hnq i))

/-- The explicit Johnson-floor/trivial-ceiling corridor in Shaw units: from
`sqrt n ≤ M ≤ n` one gets
`sqrt n / sqrt(n log(q/n)) ≤ Sh(q,n) ≤ n / sqrt(n log(q/n))`.  This records exactly where the
kernel-checked floor and elementary ceiling sit after Shaw normalization; it is not a cancellation
estimate and makes no claim toward closing CORE. -/
theorem shawValue_floor_ceiling_corridor {q n M : ℝ} (hscale : 0 < shawScale q n)
    (hfloor : Real.sqrt n ≤ M) (hceil : M ≤ n) :
    Real.sqrt n / shawScale q n ≤ shawValue q n M ∧
      shawValue q n M ≤ n / shawScale q n := by
  exact shawValue_mem_corridor_of_mem_raw_corridor (q := q) (n := n) (M := M)
    (L := Real.sqrt n) (U := n) hscale hfloor hceil

/-- Prize-regime form of the Johnson-floor/trivial-ceiling corridor, discharging scale positivity
from `q > n > 0`. -/
theorem shawValue_floor_ceiling_corridor_of_pos_lt {q n M : ℝ}
    (hn : 0 < n) (hnq : n < q) (hfloor : Real.sqrt n ≤ M) (hceil : M ≤ n) :
    Real.sqrt n / shawScale q n ≤ shawValue q n M ∧
      shawValue q n M ≤ n / shawScale q n := by
  exact shawValue_floor_ceiling_corridor (q := q) (n := n) (M := M)
    (shawScale_pos_of_pos_lt hn hnq) hfloor hceil

end ProximityGap.Frontier.ShawValueCapstone

#print axioms ProximityGap.Frontier.ShawValueCapstone.shawScale_pos_of_pos_lt
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_le_iff_core_bound
#print axioms ProximityGap.Frontier.ShawValueCapstone.core_bound_iff_shawValue_le
#print axioms ProximityGap.Frontier.ShawValueCapstone.uniformCoreBound_iff_uniformShawBound
#print axioms ProximityGap.Frontier.ShawValueCapstone.uniformCoreBound_iff_uniformShawBound_of_pos_lt
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_iff_corePrizeBoundOn
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_iff_corePrizeBoundOn_of_pos_lt
#print axioms ProximityGap.Frontier.ShawValueCapstone.uniformShawInterval_iff_uniformRawScaledInterval
#print axioms ProximityGap.Frontier.ShawValueCapstone.uniformShawInterval_iff_uniformRawScaledInterval_of_pos_lt
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_floor_of_sqrt_le
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_trivial_ceiling_of_le
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_mem_corridor_of_mem_raw_corridor
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_mem_corridor_of_mem_raw_corridor_of_pos_lt
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_mem_interval_iff_raw_mem_scaled_interval
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_mem_interval_iff_raw_mem_scaled_interval_of_pos_lt
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_floor_ceiling_corridor
#print axioms ProximityGap.Frontier.ShawValueCapstone.shawValue_floor_ceiling_corridor_of_pos_lt
