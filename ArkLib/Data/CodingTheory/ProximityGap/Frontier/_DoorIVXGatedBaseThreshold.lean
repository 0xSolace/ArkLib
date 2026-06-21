/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDilationDescentTelescope

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Door-(iv) Lane-3: the `XGatedRatio` GATE-THRESHOLD obstruction — the √2-saving cannot reach the thin base (#444)

`_DoorIVXGatedPrizeReduction` (`6e47fbd34`) proved the end-to-end reduction
`XGatedRatio ψ G ζ μ x₀ lnm  ∧  (gate: x₀·lnm ≤ |level k| ∀ k ≤ μ)  ⟹  M_μ ≤ (√2)^μ · M_0 = √n · M_0`.
The `√2` per-level ratio it telescopes is the *corrected, cancellation-regime* object
(`_BetaGatedRatioGate.XGatedRatio`): it is gated by `x = n/ln m ≥ x₀`, i.e. it only holds once the level
is large enough to be in the cancellation regime.

This file locks the structural cost of that gate.  By `_BetaGatedRatioGate.levelTower_card` the level
cardinality is `|level k| = 2^k · |G|`, so the gate `x₀·lnm ≤ |level k|` **cannot hold at the thin base
levels**: it first holds at `k ≥ k* := ⌈log₂(x₀·lnm/|G|)⌉`.  Below `k*` the per-level ratio is the
*trivial doubling factor 2* (`_BetaGatedRatioGate.levelRatio_at_zero_eq_two`, the aligned `b = 0`
frequency), NOT `√2`.  The honest telescope therefore SPLITS:

> **`k*` trivial-doubling base levels (factor `2`)  +  `(a − k*)` cancelling levels (factor `c ≤ 2`)
>   ⟹  `M_a ≤ 2^{k*} · c^{a − k*} · M_0`.**

At `c = √2` this is `2^{k*}·(√2)^{a−k*}·M_0 = √(2^{k*}) · (√2)^a · M_0 = √(2^{k*}) · √n · M_0` (at `2^a = n`):
the descent saving is `(√2)^{a−k*}`, **not** `(√2)^a`.  The `√2`-saving cannot reach the thin base; the
`k*` base levels are non-cancelling and cost an extra factor `√(2^{k*})` over the clean prize floor.

This is a Lane-3 constraint companion to the XGate reduction.  It is *harmless asymptotically* —
`k* = O(log(lnm/|G|)) = O(log log p)` is `μ`-independent, so the polylog loss does not destroy the
prize-scale saving — but it is a genuine structural fact: the dyadic descent's clean `(√2)^μ` floor
is only available *modulo* a `√(2^{k*})` base correction, because the gate the reduction assumes is
unsatisfiable at the thin base.  Pure abstract telescoping (no subgroup machinery for the arithmetic),
parametric over a level-indexed worst-period sequence `M : ℕ → ℝ`, building on
`_DoorIVDilationDescentTelescope.telescope_per_level_factor`.

NO CORE / cancellation / completion / moment / anti-concentration / capacity claim.  CORE stays OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold

open ArkLib.ProximityGap.Frontier.DoorIVDilationDescentTelescope

/-- **Split dyadic-descent telescoping (factor `2` base, factor `c` cancellation regime).**
If a nonnegative level-indexed sequence `M` doubles on the thin base levels `k < k*`
(`M (k+1) ≤ 2 · M k`) and satisfies the cancellation-regime per-level bound `M (k+1) ≤ c · M k` with
`1 ≤ c` for the levels `k* ≤ k` (here from `k*` up to `a = k* + r`), then
`M (k* + r) ≤ 2^{k*} · c^r · M 0`.

This is the honest telescope for the `XGatedRatio` reduction: the gate `x₀·lnm ≤ |level k|` fails for
`k < k*` (the base is too thin to be in the cancellation regime), so those `k*` levels pay the trivial
doubling factor `2` (`levelRatio_at_zero_eq_two`), and only the `r` levels above `k*` enjoy the
cancellation factor `c` (`= √2` for the prize). -/
theorem split_telescope_two_then_c (M : ℕ → ℝ) (_hpos : ∀ k, 0 ≤ M k)
    {c : ℝ} (hc1 : 1 ≤ c) (kstar r : ℕ)
    (hbase : ∀ k, k < kstar → M (k + 1) ≤ 2 * M k)
    (hcanc : ∀ j, j < r → M (kstar + j + 1) ≤ c * M (kstar + j)) :
    M (kstar + r) ≤ 2 ^ kstar * c ^ r * M 0 := by
  -- Step 1: telescope the `k*` base levels with factor `2` ⟹ `M k* ≤ 2^{k*} · M 0`.
  -- Reuse the proven factor-2 telescope on the truncated sequence `fun k => M k` for `k ≤ k*`.
  have hbase' : M kstar ≤ 2 ^ kstar * M 0 := by
    -- prove `M k ≤ 2^k · M 0` for all `k ≤ k*` by induction on `k`.
    have key : ∀ k, k ≤ kstar → M k ≤ 2 ^ k * M 0 := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ n ih =>
        intro hsucc
        have hn : n < kstar := hsucc
        have hnle : n ≤ kstar := le_of_lt hn
        calc M (n + 1) ≤ 2 * M n := hbase n hn
          _ ≤ 2 * (2 ^ n * M 0) := by
              have h2 : (0 : ℝ) ≤ 2 := by norm_num
              exact mul_le_mul_of_nonneg_left (ih hnle) h2
          _ = 2 ^ (n + 1) * M 0 := by ring
    exact key kstar le_rfl
  -- Step 2: telescope the `r` cancellation levels above `k*` with factor `c`
  -- ⟹ `M (k* + r) ≤ c^r · M k*`.
  have hcanc' : M (kstar + r) ≤ c ^ r * M kstar := by
    have key : ∀ j, j ≤ r → M (kstar + j) ≤ c ^ j * M kstar := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ n ih =>
        intro hsucc
        have hn : n < r := hsucc
        have hnle : n ≤ r := le_of_lt hn
        have hc0 : (0 : ℝ) ≤ c := le_trans (by norm_num) hc1
        calc M (kstar + (n + 1)) = M (kstar + n + 1) := by ring_nf
          _ ≤ c * M (kstar + n) := hcanc n hn
          _ ≤ c * (c ^ n * M kstar) := mul_le_mul_of_nonneg_left (ih hnle) hc0
          _ = c ^ (n + 1) * M kstar := by ring
    exact key r le_rfl
  -- Step 3: chain.  `M (k*+r) ≤ c^r · M k* ≤ c^r · (2^{k*} · M 0) = 2^{k*} · c^r · M 0`.
  have hcr0 : (0 : ℝ) ≤ c ^ r := pow_nonneg (le_trans (by norm_num) hc1) r
  calc M (kstar + r) ≤ c ^ r * M kstar := hcanc'
    _ ≤ c ^ r * (2 ^ kstar * M 0) := mul_le_mul_of_nonneg_left hbase' hcr0
    _ = 2 ^ kstar * c ^ r * M 0 := by ring

/-- **Prize specialization: the descent saving is `(√2)^r`, gated above the `k*` thin base.**
With the cancellation-regime factor `c = √2`, the split telescope gives
`M (k* + r) ≤ 2^{k*} · (√2)^r · M 0`.  The `√2`-saving applies only to the `r = a − k*` levels above the
gate threshold; the `k*` thin base levels pay the trivial doubling factor `2`. -/
theorem split_telescope_sqrt2 (M : ℕ → ℝ) (_hpos : ∀ k, 0 ≤ M k) (kstar r : ℕ)
    (hbase : ∀ k, k < kstar → M (k + 1) ≤ 2 * M k)
    (hcanc : ∀ j, j < r → M (kstar + j + 1) ≤ Real.sqrt 2 * M (kstar + j)) :
    M (kstar + r) ≤ 2 ^ kstar * (Real.sqrt 2) ^ r * M 0 := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact split_telescope_two_then_c M _hpos h1 kstar r hbase hcanc

/-- **The gate-threshold cost is exactly `√(2^{k*})` over the clean prize floor.**
Writing the total height `a = k* + r`, the split-telescope factor `2^{k*} · (√2)^r` equals
`√(2^{k*}) · (√2)^a`: the clean prize floor `(√2)^a` (`= √n` at `2^a = n`) times an excess factor
`√(2^{k*})`.  This isolates exactly what the unreachable thin base costs:  `√(2^{k*})`. -/
theorem split_cost_eq_sqrt_two_pow (kstar r : ℕ) :
    (2 : ℝ) ^ kstar * (Real.sqrt 2) ^ r
      = Real.sqrt (2 ^ kstar) * (Real.sqrt 2) ^ (kstar + r) := by
  -- `(√2)^{k*+r} = (√2)^{k*} · (√2)^r`, and `2^{k*} = √(2^{k*}) · (√2)^{k*}` since
  -- `√(2^{k*}) = (√2)^{k*}` (multiplicativity of √), so `2^{k*} = (√2)^{k*} · (√2)^{k*}`.
  have hs2 : Real.sqrt (2 ^ kstar) = (Real.sqrt 2) ^ kstar := by
    induction kstar with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]
  have hsq : (Real.sqrt 2) * (Real.sqrt 2) = 2 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  rw [hs2, pow_add]
  -- goal: 2^k* * (√2)^r = (√2)^k* * ((√2)^k* * (√2)^r)
  have h2k : (2 : ℝ) ^ kstar = (Real.sqrt 2) ^ kstar * (Real.sqrt 2) ^ kstar := by
    rw [← mul_pow, hsq]
  rw [h2k]; ring

/-- **The thin base genuinely costs: for `k* ≥ 1` the split bound strictly exceeds the clean floor.**
The split-telescope factor `2^{k*} · (√2)^r` is `STRICTLY` larger than the clean `(√2)^{k*+r}` floor
whenever there is at least one unreachable base level (`k* ≥ 1`).  Equivalently `√(2^{k*}) > 1`: the
gate the XGate reduction assumes is unsatisfiable at the thin base, so the descent cannot deliver the
clean `(√2)^a` floor — it pays a real `√(2^{k*}) > 1` excess. -/
theorem gate_threshold_strictly_above_clean {kstar : ℕ} (hk : 1 ≤ kstar) (r : ℕ) :
    (Real.sqrt 2) ^ (kstar + r) < (2 : ℝ) ^ kstar * (Real.sqrt 2) ^ r := by
  rw [split_cost_eq_sqrt_two_pow kstar r]
  -- goal: (√2)^{k*+r} < √(2^{k*}) · (√2)^{k*+r}, i.e. 1 < √(2^{k*}).
  have hpow_pos : (0 : ℝ) < (Real.sqrt 2) ^ (kstar + r) := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt (2 ^ kstar) := by
    have h2k : (1 : ℝ) < (2 : ℝ) ^ kstar := by
      have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ kstar :=
        pow_le_pow_right₀ (by norm_num) hk
      have h21 : (2 : ℝ) ^ 1 = 2 := by norm_num
      linarith [this]
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) h2k
  calc (Real.sqrt 2) ^ (kstar + r)
      = 1 * (Real.sqrt 2) ^ (kstar + r) := by ring
    _ < Real.sqrt (2 ^ kstar) * (Real.sqrt 2) ^ (kstar + r) :=
        mul_lt_mul_of_pos_right hsqrt_gt_one hpow_pos

end ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.split_telescope_two_then_c
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.split_telescope_sqrt2
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.split_cost_eq_sqrt_two_pow
#print axioms ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.gate_threshold_strictly_above_clean
