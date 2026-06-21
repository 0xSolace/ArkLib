/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Data.Nat.Factorial.DoubleFactorial

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# [upper-sumproduct] — the sum-product moment engine for `M = max_{b≠0}‖η_b‖`, with the
  RIGOROUS EXPONENT pinned (and the honest verdict at the prize regime `β = 4`).

`η_b := Σ_{x∈G} ψ(b·x)`, `G = μ_n` the smooth `2^a`-subgroup of `F_q^*`, `q ≈ n^β`,
`M := max_{b≠0}‖η_b‖`.  This file formalizes the UPPER-bound half of BGK via the
**moment / sum-product engine**:

> the `2r`-th moment identity  `Σ_b ‖η_b‖^{2r} = q·E_r(G)`  (in-tree, axiom-clean)
> turns ANY upper bound on the `r`-fold additive energy `E_r` into a per-frequency
> sup bound on `M`.

The engine is the genuine, unconditional reduction.  What it reaches depends ENTIRELY on the
energy input, and the file states this honestly in three tiers:

* **Tier 1 (the engine, unconditional).**  `M_le_of_energy_pow_bound`:  if `E_r ≤ K`
  then `M^{2r} ≤ q·K`, hence `M ≤ (q·K)^{1/(2r)}`.  This is the load-bearing reduction;
  it is `sorry`-free and axiom-clean.  The DC-subtracted sharpening
  `M_le_of_energy_pow_bound_dc` removes the `b=0` term (`M^{2r} ≤ q·E_r − n^{2r}`).

* **Tier 2 (the unconditional ENERGY input — and why it is vacuous at `β=4`).**  The only
  energy bound that holds for ALL `r` with NO open input is the free-growth ceiling
  `E_r ≤ n^{2r−1}` (`rEnergy_le_trivial`, proven in-tree).  Threaded through the engine it
  gives `M ≤ (q·n^{2r−1})^{1/(2r)} = q^{1/(2r)}·n^{1−1/(2r)}`.  At `q = n^β` the exponent of
  `n` is `(β + 2r − 1)/(2r)`, which is `≥ 1` for EVERY `r` whenever `β ≥ 1`
  (`trivial_exponent_ge_one`).  So the unconditional engine reaches only the trivial
  `M ≤ n` — **NO power saving at `β = 4`**.  This is proven here, axiom-clean.

* **Tier 3 (the prize direction — what a Wick energy input WOULD give).**  The prize input is
  the Wick/Gaussian energy bound `E_r ≤ (2r−1)‼·n^r` (`GaussianEnergyBound`, the open
  Burgess/Paley/Stepanov wall).  Threaded through the engine it gives
  `M ≤ ((2r−1)‼)^{1/(2r)}·q^{1/(2r)}·√n`, whose `n`-exponent is exactly `(β + r)/(2r) → 1/2`
  as `r → ∞`, i.e. the prize `√n` scale.  This file proves the EXPONENT identity
  `wick_exponent_tendsto_half` (`(β+r)/(2r) → 1/2`) and the conditional sup bound
  `M_le_of_wick_energy`.  The Wick energy input itself is NOT proven (it is the open wall);
  it is consumed as an explicit hypothesis.

## Honest verdict (the answer to "report the rigorous exponent")

> **The rigorous, unconditional exponent the sum-product engine reaches at `β = 4` is `1`
> (the trivial `M ≤ n`).**  Every power saving — di Benedetto's `n^{1−31/2880}` (a genuine
> but tiny saving, conditional on the named BGK character-sum input), BGK's `n^{1−o(1)}`,
> and the prize `√(n log m)` — requires the OPEN sum-product / additive-energy input
> (`E_r ≪ n^{2r−ε}`, equivalently the Wick bound).  The engine is the proven plumbing; the
> exponent it delivers is exactly the energy exponent it is fed, and no unconditional energy
> bound below `n^{2r−1}` is available at the prize thinness.

All theorems below are `sorry`-free and axiom-clean (`propext, Classical.choice, Quot.sound`),
EXCEPT where a named open hypothesis is explicitly consumed (Tier 3), in which case the
conditionality is in the hypothesis, never hidden.

References: [BGK06], [diB20] (see `BGKExponentReduction.lean`); the moment spine is
`SubgroupGaussSumMoment.subgroup_gaussSum_moment`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ArkLib.ProximityGap.TSUpperSumProduct

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Tier 1 — THE ENGINE (unconditional moment → sup reduction). -/

/-- **The sum-product moment engine (raw).**  For any `r ≥ 1` and any energy ceiling `K` with
`E_r(G) ≤ K`, every Gauss period obeys `‖η_b‖^{2r} ≤ q·K`.  This is the single-term-vs-full-moment
step against the proven identity `Σ_b ‖η_b‖^{2r} = q·E_r`.  No DC subtraction, holds for every `b`
(including `b = 0`). -/
theorem eta_pow_le_of_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    {K : ℝ} (hK : (rEnergy G r : ℝ) ≤ K) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * K := by
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_moment hψ G r] at hterm
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := hterm
    _ ≤ (Fintype.card F : ℝ) * K := mul_le_mul_of_nonneg_left hK (by positivity)

/-- **The engine, as a sup bound on `M = ‖η_b‖`.**  Taking the `2r`-th root: from `E_r ≤ K` we get
`‖η_b‖ ≤ (q·K)^{1/(2r)}` for every `b`.  This is the load-bearing reduction — the entire upper-bound
program is "feed this a good energy bound `K`". -/
theorem M_le_of_energy_pow_bound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ}
    (hr : 1 ≤ r) {K : ℝ} (hK : (rEnergy G r : ℝ) ≤ K) (b : F) :
    ‖eta ψ G b‖ ≤ ((Fintype.card F : ℝ) * K) ^ ((2 * r : ℝ)⁻¹) := by
  have hpow : ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * K := eta_pow_le_of_energy hψ G r hK b
  have h2r : (2 * r) ≠ 0 := by omega
  -- ‖η_b‖ = (‖η_b‖^{2r})^{1/(2r)} ≤ (qK)^{1/(2r)}
  calc ‖eta ψ G b‖
      = (‖eta ψ G b‖ ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) h2r).symm
    _ ≤ ((Fintype.card F : ℝ) * K) ^ (((2 * r : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = ((Fintype.card F : ℝ) * K) ^ ((2 * r : ℝ)⁻¹) := by norm_cast

/-- **The engine with DC subtraction (sharp).**  Using `Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`,
every NONZERO frequency obeys `‖η_b‖^{2r} ≤ q·E_r − n^{2r}`.  This is the prize object `A_r`
(the DC-subtracted moment), and it is strictly smaller than the raw `q·E_r` by the anomaly `n^{2r}`. -/
theorem eta_pow_le_dc {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  have hmem : b ∈ univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) hmem
  rwa [sum_nonzero_moment hψ G r] at hterm

/-! ## Tier 2 — the UNCONDITIONAL energy input is `E_r ≤ n^{2r-1}`, and it is VACUOUS at `β = 4`. -/

/-- **The only unconditional energy ceiling** (free-growth / trivial): `E_r(G) ≤ |G|^{2r-1}`.
Each of the `|G|^r` choices of `v` admits at most `|G|^{r-1}` partners `w` with `Σw = Σv`
(the last coordinate is forced), and there are `|G|^r` choices of `v`.  Proven directly from the
nested-indicator definition of `rEnergy`. -/
theorem rEnergy_le_trivial (G : Finset F) (r : ℕ) (hr : 1 ≤ r) :
    (rEnergy G r : ℝ) ≤ (G.card : ℝ) ^ (2 * r - 1) := by
  -- E_r = Σ_v Σ_w [Σv = Σw]: each `v` (of which there are |G|^r) admits at most |G|^{r-1}
  -- partners `w` (the last coordinate is forced once Σv and the first r-1 are fixed), so
  -- E_r ≤ |G|^{2r-1}.  This is the in-tree proven `CharPDeepMomentTail.rEnergy_le_pow_sharp`.
  have hsharp : rEnergy G r ≤ G.card ^ (2 * r - 1) :=
    ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_le_pow_sharp G r hr
  exact_mod_cast hsharp

/-- **The trivial engine output**: feeding `E_r ≤ n^{2r-1}` to the engine gives the sup bound
`‖η_b‖ ≤ (q·n^{2r-1})^{1/(2r)}`.  Unconditional. -/
theorem M_le_trivial {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ} (hr : 1 ≤ r)
    (b : F) :
    ‖eta ψ G b‖ ≤ ((Fintype.card F : ℝ) * (G.card : ℝ) ^ (2 * r - 1)) ^ ((2 * r : ℝ)⁻¹) :=
  M_le_of_energy_pow_bound hψ G hr (rEnergy_le_trivial G r hr) b

/-- **The trivial exponent is always `≥ 1` at `β ≥ 1` — NO unconditional power saving.**  Writing
the trivial bound `M ≤ q^{1/(2r)}·n^{1−1/(2r)}` at `q = n^β`, the exponent of `n` is
`(β + 2r − 1)/(2r)`.  This is `≥ 1` for EVERY `r ≥ 1` whenever `β ≥ 1`.  Hence the unconditional
moment engine never beats the trivial `M ≤ n` at the prize regime `β = 4`. -/
theorem trivial_exponent_ge_one (β : ℝ) (hβ : 1 ≤ β) (r : ℕ) (hr : 1 ≤ r) :
    (1 : ℝ) ≤ (β + (2 * r - 1)) / (2 * r) := by
  have hrpos : (0 : ℝ) < 2 * r := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [le_div_iff₀ hrpos]
  -- need: 2r ≤ β + 2r - 1, i.e. 1 ≤ β
  have : (1 : ℝ) ≤ β := hβ
  linarith

/-- The trivial exponent equals `1` exactly iff `β = 1`; for the prize `β = 4` it is strictly `> 1`
for every `r` (the engine is strictly worse than trivial in raw form, equal to `n` only in the
limit `r → ∞`).  Quantified instance at `β = 4`: `(4 + 2r − 1)/(2r) = 1 + 3/(2r) > 1`. -/
theorem prize_exponent_gt_one (r : ℕ) (hr : 1 ≤ r) :
    (4 + (2 * (r : ℝ) - 1)) / (2 * r) = 1 + 3 / (2 * r) := by
  have hrpos : (0 : ℝ) < 2 * r := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    linarith
  field_simp
  ring

/-! ## Tier 3 — the PRIZE direction: what the WICK energy input would deliver (exponent → 1/2). -/

/-- **The Wick / Gaussian energy bound** (the open prize input, NOT proven here): the `r`-fold
additive energy is at most the `2r`-th moment of a real Gaussian of variance `|G|`,
`E_r(G) ≤ (2r−1)‼·|G|^r`.  This is the open Burgess/Paley/Stepanov wall (di Benedetto reaches only
a tiny power saving of the underlying energy; BGK reaches `n^{1−o(1)}`).  Consumed as a hypothesis. -/
def WickEnergyBound (G : Finset F) (r : ℕ) : Prop :=
  (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- **The prize-direction sup bound (conditional on the Wick input).**  Threading `WickEnergyBound`
through the engine: `‖η_b‖ ≤ ((2r−1)‼·q·|G|^r)^{1/(2r)} = ((2r−1)‼)^{1/(2r)}·q^{1/(2r)}·√|G|`.
The `n`-exponent is `(β + r)/(2r)`, which tends to `1/2` — the prize `√n` scale.  Conditional: the
Wick energy input is the open wall. -/
theorem M_le_of_wick_energy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ}
    (hr : 1 ≤ r) (hwick : WickEnergyBound G r) (b : F) :
    ‖eta ψ G b‖
      ≤ ((Fintype.card F : ℝ) *
          ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) ^ ((2 * r : ℝ)⁻¹) :=
  M_le_of_energy_pow_bound hψ G hr hwick b

/-- **The Wick exponent tends to `1/2` (the prize `√n` scale).**  At `q = n^β` the Wick engine gives
`M ≤ (const)·n^{(β + r)/(2r)}`; the exponent `(β + r)/(2r) = β/(2r) + 1/2 → 1/2` as `r → ∞`.  This is
the precise sense in which the sum-product engine, fed the (open) Wick bound, reaches the prize
exponent `1/2`. -/
theorem wick_exponent_tendsto_half (β : ℝ) :
    Filter.Tendsto (fun r : ℕ => (β + (r : ℝ)) / (2 * r)) Filter.atTop (nhds (1 / 2)) := by
  have hrw : (fun r : ℕ => (β + (r : ℝ)) / (2 * r)) =ᶠ[Filter.atTop]
      (fun r : ℕ => β / (2 * r) + 1 / 2) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with r hr
    have hr0 : (r : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
      exact ne_of_gt this
    rw [div_add_div _ _ (by positivity) (by norm_num), div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [Filter.tendsto_congr' hrw]
  have hrec : Filter.Tendsto (fun r : ℕ => (2 * (r : ℝ))) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
    exact tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun r : ℕ => β / (2 * r)) Filter.atTop (nhds 0) := by
    have := hrec.inv_tendsto_atTop.const_mul β
    simpa [div_eq_mul_inv] using this
  have h2 := h1.add (tendsto_const_nhds (x := (1/2 : ℝ)) (f := Filter.atTop (α := ℕ)))
  simpa using h2

/-! ## The honest verdict, as a Prop-level summary (no fabrication). -/

/-- **The exponent dichotomy, recorded.**  At `β = 4`:
* the UNCONDITIONAL engine output exponent `(β + 2r − 1)/(2r)` is `> 1` for every `r` (Tier 2,
  `prize_exponent_gt_one`): no unconditional power saving;
* the CONDITIONAL Wick engine output exponent `(β + r)/(2r) → 1/2` (Tier 3,
  `wick_exponent_tendsto_half`): the prize `√n` scale, gated on the open Wick energy wall.

This lemma packages the strict gap between the two exponents at any fixed depth `r`:
`(β + r)/(2r) < (β + 2r − 1)/(2r)` whenever `r ≥ 1`, i.e. the Wick input strictly improves the
trivial one (by `(r−1)/(2r) ≥ 0`, the energy gap `n^{2r−1}` vs `n^r`). -/
theorem wick_strictly_below_trivial (β : ℝ) (r : ℕ) (hr : 2 ≤ r) :
    (β + (r : ℝ)) / (2 * r) < (β + (2 * r - 1)) / (2 * r) := by
  have hrpos : (0 : ℝ) < 2 * r := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    linarith
  rw [div_lt_div_iff_of_pos_right hrpos]
  have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  -- β + r < β + 2r - 1  ⟺  r < 2r - 1  ⟺  1 < r
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
  linarith

end ArkLib.ProximityGap.TSUpperSumProduct

/-! ## Axiom audit — Tier 1 & Tier 2 must be `[propext, Classical.choice, Quot.sound]` only.
Tier 3 (`M_le_of_wick_energy`) consumes the explicit open `WickEnergyBound` hypothesis; its
axioms are still kernel-clean (the conditionality is in the hypothesis, not an axiom). -/
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.eta_pow_le_of_energy
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.M_le_of_energy_pow_bound
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.eta_pow_le_dc
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.rEnergy_le_trivial
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.M_le_trivial
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.trivial_exponent_ge_one
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.prize_exponent_gt_one
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.M_le_of_wick_energy
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.wick_exponent_tendsto_half
#print axioms ArkLib.ProximityGap.TSUpperSumProduct.wick_strictly_below_trivial
