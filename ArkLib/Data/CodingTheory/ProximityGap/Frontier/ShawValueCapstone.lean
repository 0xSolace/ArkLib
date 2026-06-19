/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Shaw-value capstone rungs for the proximity-prize normalization (#444)

Door (iv) has localized the remaining analytic object to the worst-frequency monomial-sum
coherence.  This file packages the harmless, citable normalization around that object:

* `prizeScale n L = sqrt (n * L)` is the native square-root target scale.
* `shawValue M n L = M / prizeScale n L` is the normalized Shaw value.
* `prizeBound_iff_shawValue_le` states the exact arithmetic equivalence, under a positive scale:
  bounding the raw worst-frequency value `M` by `C * sqrt(n L)` is the same as bounding the
  normalized Shaw value by `C`.
* `shawValue_floor_of_plancherel_floor` and `shawValue_le_of_trivial_ceiling` record the two easy
  ends of the chain: a Plancherel/RMS floor passes to the normalized value, and the trivial ceiling
  passes to the normalized value.

Scope: this is Lane-2 infrastructure only.  It does **not** prove the prize inequality or any new
anti-concentration for the monomial phase set; it makes the “prize ⇔ bounded Shaw value” arithmetic
rung explicit and axiom-clean so future door-(iv) work can cite the normalized target without
re-proving division-by-scale bookkeeping.
-/

namespace ArkLib.ProximityGap.Frontier.ShawValueCapstone

/-- The square-root target scale in the prize normalization.  In applications `n` is the subgroup
size and `L` is the logarithmic thinness parameter such as `log (p / n)`. -/
noncomputable def prizeScale (n L : ℝ) : ℝ :=
  Real.sqrt (n * L)

/-- The normalized Shaw value: raw worst-frequency size divided by the prize scale. -/
noncomputable def shawValue (M n L : ℝ) : ℝ :=
  M / prizeScale n L

/-- Positivity of the prize scale from positive subgroup size and positive logarithmic thinness. -/
theorem prizeScale_pos {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    0 < prizeScale n L := by
  unfold prizeScale
  exact Real.sqrt_pos.2 (mul_pos hn hL)

/-- **Capstone normalization equivalence.**  Once the target scale is positive, the raw prize-shaped
bound `M ≤ C * sqrt(n L)` is exactly the statement that the Shaw value is at most `C`.

This is the formal Lane-2 rung behind the prose “prize ⇔ bounded Shaw value”: all hard content is in
proving a uniform bound for the normalized object; this theorem only removes the arithmetic wrapper. -/
theorem prizeBound_iff_shawValue_le {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C := by
  constructor
  · intro h
    unfold shawValue
    have hdiv : M / prizeScale n L ≤ (C * prizeScale n L) / prizeScale n L :=
      div_le_div_of_nonneg_right h (le_of_lt hs)
    simpa [mul_comm, mul_left_comm, mul_assoc, ne_of_gt hs] using hdiv
  · intro h
    unfold shawValue at h
    calc
      M = (M / prizeScale n L) * prizeScale n L := by
        field_simp [ne_of_gt hs]
      _ ≤ C * prizeScale n L := mul_le_mul_of_nonneg_right h (le_of_lt hs)

/-- The equivalence in expanded parameters: for `0 < n` and `0 < L`, raw prize boundedness by `C`
is exactly boundedness of the normalized Shaw value by `C`. -/
theorem prizeBound_iff_shawValue_le_of_pos {M C n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C :=
  prizeBound_iff_shawValue_le (prizeScale_pos hn hL)



/-! ## Uniform-family capstone: the arithmetic form of `prize ⇔ Sh(n)=O(1)` -/

/-- A raw prize-family bound by the same constant `C` across a parameter family.  The parameters may
encode fields, subgroup sizes, or admissible thin instances; this definition is intentionally only the
arithmetic wrapper. -/
def rawPrizeFamilyBound {ι : Type*} (M n L : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, M i ≤ C * prizeScale (n i) (L i)

/-- A uniform Shaw-value bound by the same constant `C` across a parameter family. -/
def shawValueFamilyBound {ι : Type*} (M n L : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, shawValue (M i) (n i) (L i) ≤ C

/-- **Uniform-family Lane-2 capstone.**  Under pointwise positivity of the prize scale, a uniform raw
prize-family bound by `C` is exactly a uniform Shaw-value bound by `C`.

This is the machine-checked arithmetic core of the prose reduction `prize ⇔ Sh(n)=O(1)`: after
normalization, proving the prize with an absolute constant is the same as proving that the normalized
Shaw values are bounded by that absolute constant.  No cancellation estimate is hidden here. -/
theorem rawPrizeFamilyBound_iff_shawValueFamilyBound {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    rawPrizeFamilyBound M n L C ↔ shawValueFamilyBound M n L C := by
  constructor
  · intro h i
    exact (prizeBound_iff_shawValue_le (hs i)).1 (h i)
  · intro h i
    exact (prizeBound_iff_shawValue_le (hs i)).2 (h i)

/-- Existential constant form of the uniform-family capstone: there is an absolute raw prize constant
iff there is an absolute normalized Shaw-value constant, with the same witness. -/
theorem exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < prizeScale (n i) (L i)) :
    (∃ C, rawPrizeFamilyBound M n L C) ↔ (∃ C, shawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, (rawPrizeFamilyBound_iff_shawValueFamilyBound hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, (rawPrizeFamilyBound_iff_shawValueFamilyBound hs).2 hC⟩

/-- A Plancherel/RMS floor `sqrt n ≤ M` becomes the corresponding normalized lower bound for the
Shaw value.  This records the easy Johnson-side floor in Shaw-value units. -/
theorem shawValue_floor_of_plancherel_floor {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hfloor : Real.sqrt n ≤ M) :
    Real.sqrt n / prizeScale n L ≤ shawValue M n L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hfloor (le_of_lt hs)

/-- The trivial ceiling `M ≤ n` becomes the corresponding normalized upper bound for the Shaw value.
This is the harmless top bracket `M ≤ n`, in Shaw-value units. -/
theorem shawValue_le_of_trivial_ceiling {M n L : ℝ} (hs : 0 < prizeScale n L) (hceil : M ≤ n) :
    shawValue M n L ≤ n / prizeScale n L := by
  unfold shawValue
  exact div_le_div_of_nonneg_right hceil (le_of_lt hs)

/-! ## The two-sided Shaw-value bracket: the citable framing of the open prize

The prize asks to collapse the *width* of the bracket below to an absolute constant.  The two
easy rungs above are combined here into a single two-sided statement, and the bracket endpoints
are identified in closed form, so the entire open problem reads as "tighten a `sqrt n`-wide
bracket to `O(1)`".  All content here is harmless normalization arithmetic — no anti-concentration
or cancellation estimate is hidden. -/

/-- **Two-sided Shaw-value bracket.**  Whenever the Plancherel/RMS floor `sqrt n ≤ M` and the
trivial ceiling `M ≤ n` both hold, the normalized Shaw value is sandwiched between the two
normalized brackets.  This bundles `shawValue_floor_of_plancherel_floor` and
`shawValue_le_of_trivial_ceiling` into the single citable bracket the prize must collapse. -/
theorem shawValue_bracket {M n L : ℝ} (hs : 0 < prizeScale n L)
    (hfloor : Real.sqrt n ≤ M) (hceil : M ≤ n) :
    Real.sqrt n / prizeScale n L ≤ shawValue M n L ∧
      shawValue M n L ≤ n / prizeScale n L :=
  ⟨shawValue_floor_of_plancherel_floor hs hfloor,
   shawValue_le_of_trivial_ceiling hs hceil⟩

/-- Closed form of the **lower** bracket endpoint: `sqrt n / prizeScale n L = 1 / sqrt L`.
The Plancherel floor lands the normalized Shaw value at `1/sqrt(log(p/n))`, independent of `n`. -/
theorem floor_bracket_eq {n L : ℝ} (hn : 0 < n) :
    Real.sqrt n / prizeScale n L = 1 / Real.sqrt L := by
  unfold prizeScale
  rw [Real.sqrt_mul (le_of_lt hn), div_mul_eq_div_div,
    div_self (ne_of_gt (Real.sqrt_pos.2 hn))]

/-- Closed form of the **upper** bracket endpoint: `n / prizeScale n L = sqrt (n / L)`.
The trivial ceiling lands the normalized Shaw value at `sqrt(n / log(p/n))`, the SOTA-shaped scale. -/
theorem ceiling_bracket_eq {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    n / prizeScale n L = Real.sqrt (n / L) := by
  have hnL : (0 : ℝ) < n * L := mul_pos hn hL
  have hsnL : Real.sqrt (n * L) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnL)
  unfold prizeScale
  rw [div_eq_iff hsnL, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n / L)]
  have h2 : (n / L) * (n * L) = n ^ 2 := by field_simp
  rw [h2, Real.sqrt_sq (le_of_lt hn)]

/-- **Bracket width is `sqrt n`.**  The ratio of the upper to the lower bracket endpoint equals
`sqrt n`: the open prize is exactly the demand to collapse this `sqrt n`-wide normalized bracket
to an absolute constant.  (Probe `probe_shaw_bracket_arith.py`: ratio = 4,5.66,8,11.3,16 at
n=16..256 = `sqrt n`, non-vacuous.) -/
theorem bracket_width_eq_sqrt {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    (n / prizeScale n L) / (Real.sqrt n / prizeScale n L) = Real.sqrt n := by
  have hps : prizeScale n L ≠ 0 := ne_of_gt (prizeScale_pos hn hL)
  have hsn : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  rw [div_div_div_cancel_right₀]
  · rw [div_eq_iff hsn, Real.mul_self_sqrt (le_of_lt hn)]
  all_goals try exact hps

end ArkLib.ProximityGap.Frontier.ShawValueCapstone

#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeBound_iff_shawValue_le
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeBound_iff_shawValue_le_of_pos
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound_iff_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_rawPrizeFamilyBound_iff_exists_shawValueFamilyBound
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_floor_of_plancherel_floor
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_le_of_trivial_ceiling
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue_bracket
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.floor_bracket_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.ceiling_bracket_eq
#print axioms ArkLib.ProximityGap.Frontier.ShawValueCapstone.bracket_width_eq_sqrt
