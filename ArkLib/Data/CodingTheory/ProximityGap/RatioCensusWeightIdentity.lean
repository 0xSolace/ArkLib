/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination

/-!
# The ratio-census weight identity (#407, attack thread D3)

The far-line incidence at radius `w` for two syndromes `s₀, s₁ : ι → F` is governed by the
*multiplicity profile of the ratio sequence* `{−s₀ᵢ/s₁ᵢ}ᵢ` (the inverse-Littlewood–Offord /
ratio-census view).  The exact, elementary, character-sum-free identity behind it is:

> **`hammingNorm_line_eq`** — for any field `F`, any finite index set `ι`, any offset/direction
> `s₀, s₁ : ι → F` and any scalar `γ`,
> `hammingNorm (s₀ + γ • s₁) = n − #{i : s₀ᵢ + γ·s₁ᵢ = 0}`,  where `n = |ι|`.

The zero-count `#{i : s₀ᵢ + γ·s₁ᵢ = 0}` splits — by whether the direction vanishes at `i` — into
the **always-zero** coordinates (`s₁ᵢ = 0 ∧ s₀ᵢ = 0`, independent of `γ`) and the **ratio-hit**
coordinates (`s₁ᵢ ≠ 0 ∧ γ = −s₀ᵢ/s₁ᵢ`):

> **`zeroCount_split`** —
> `#{i : s₀ᵢ + γ·s₁ᵢ = 0} = #{i : s₁ᵢ = 0 ∧ s₀ᵢ = 0} + #{i : s₁ᵢ ≠ 0 ∧ γ = −s₀ᵢ/s₁ᵢ}`.

so the weight at `γ` is `n` minus the fixed always-zero count minus the **multiplicity of `γ` in
the ratio sequence** `r : i ↦ −s₀ᵢ/s₁ᵢ` (over the support `s₁ᵢ ≠ 0`):

> **`hammingNorm_line_eq_sub_ratio_mult`** —
> `hammingNorm (s₀ + γ • s₁) = n − z₀ − ratioMult s₀ s₁ γ`,  `z₀ = #{i : s₁ᵢ=0 ∧ s₀ᵢ=0}`.

This is the **exact reusable machinery** of the D3 thread: far-line incidence at radius `w` is
literally `#{γ : ratioMult ≥ n − w − z₀}`, the level-set profile of the rational function
`r(x) = −s₀(x)/s₁(x)` on the evaluation domain.  Two consequences are recorded:

* `ratioMult` summed over all `γ` is **exactly** `#{i : s₁ᵢ ≠ 0}` (the support size) — the
  **first-moment identity** `∑_γ ratioMult = wt(s₁)` (every support coordinate pins one `γ`).  In
  the smooth-domain prize regime where `s₁` is a far direction (support `= n`), this is the exact
  source of `μ = E[far-line incidence] = n` recorded in the #407 ledger.
* the **level-set / degree bound** consumer `hammingNorm_line_ge_of_card_eq`: at most
  `deg`-many coordinates can share one ratio value when `r` has bounded degree — phrased here as a
  clean monotone lower bound on the weight from any cap on `ratioMult`.

Pure finite combinatorics over `F`; **axiom-clean** (`propext, Classical.choice, Quot.sound`),
no field-size, smoothness, or character-sum hypotheses.  The algebraic STEP 2 (level-set degree
bound) and the honesty STEP 3 (partial BGK-independence: the *generic* rational direction is
Weil-controlled, the *monomial/coset* direction collapses onto the Gauss period) are documented in
the #407 thread; this file lands the exact STEP 1 identity they both build on.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- attack thread D3 (inverse-Littlewood–Offord ratio-census), issue #407.
-/

namespace ArkLib.ProximityGap.RatioCensus

open Finset

variable {ι F : Type*} [Fintype ι] [Field F] [DecidableEq F]

/-- The **ratio sequence** of the direction `s₁` over the offset `s₀`: `r i = −s₀ᵢ/s₁ᵢ`.
On the support `s₁ᵢ ≠ 0` this is the unique scalar `γ` killing coordinate `i` of the line. -/
def ratioSeq (s₀ s₁ : ι → F) (i : ι) : F := (- s₀ i) * (s₁ i)⁻¹

/-- The **ratio multiplicity** of a scalar `γ`: how many support coordinates (`s₁ᵢ ≠ 0`) have
ratio exactly `γ`, i.e. are killed by the line point `s₀ + γ·s₁`.  This is the multiplicity
profile that governs the far-line incidence. -/
def ratioMult (s₀ s₁ : ι → F) (γ : F) : ℕ :=
  (univ.filter (fun i => s₁ i ≠ 0 ∧ ratioSeq s₀ s₁ i = γ)).card

omit [Fintype ι] [DecidableEq F] in
/-- On a support coordinate (`s₁ᵢ ≠ 0`), the line point vanishes iff `γ` equals the ratio. -/
theorem line_zero_iff_ratio {s₀ s₁ : ι → F} {γ : F} {i : ι} (hi : s₁ i ≠ 0) :
    s₀ i + γ * s₁ i = 0 ↔ ratioSeq s₀ s₁ i = γ := by
  unfold ratioSeq
  rw [mul_comm ((-s₀ i)) (s₁ i)⁻¹, inv_mul_eq_div, div_eq_iff hi]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **The zero-count split (the ratio-census decomposition).** The number of coordinates killed
by the line point `s₀ + γ·s₁` splits as the always-zero count plus the ratio multiplicity at `γ`:
`#{i : s₀ᵢ + γ·s₁ᵢ = 0} = #{i : s₁ᵢ = 0 ∧ s₀ᵢ = 0} + ratioMult s₀ s₁ γ`. -/
theorem zeroCount_split (s₀ s₁ : ι → F) (γ : F) :
    (univ.filter (fun i => s₀ i + γ * s₁ i = 0)).card
      = (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card + ratioMult s₀ s₁ γ := by
  classical
  unfold ratioMult
  rw [← Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun i => s₀ i + γ * s₁ i = 0)) (p := fun i => s₁ i = 0)]
  have hA : (univ.filter (fun i => s₀ i + γ * s₁ i = 0)).filter (fun i => s₁ i = 0)
      = univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0) := by
    -- on `s₁ᵢ = 0`: the line point is `s₀ᵢ`, so it vanishes iff `s₀ᵢ = 0`
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, h0⟩; rw [h0, mul_zero, add_zero] at hp; exact ⟨h0, hp⟩
    · rintro ⟨h0, he⟩; refine ⟨?_, h0⟩; rw [h0, mul_zero, add_zero]; exact he
  have hB : (univ.filter (fun i => s₀ i + γ * s₁ i = 0)).filter (fun i => ¬ s₁ i = 0)
      = univ.filter (fun i => s₁ i ≠ 0 ∧ ratioSeq s₀ s₁ i = γ) := by
    -- on `s₁ᵢ ≠ 0`: the line point vanishes iff `γ` is the ratio
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, h0⟩; exact ⟨h0, (line_zero_iff_ratio h0).mp hp⟩
    · rintro ⟨h0, hr⟩; exact ⟨(line_zero_iff_ratio h0).mpr hr, h0⟩
  rw [hA, hB]

/-- **STEP 1: the exact weight identity (pure-complement form).** The Hamming weight of the line
point `s₀ + γ·s₁` is the full index count minus the number of coordinates it kills:
`hammingNorm (s₀ + γ • s₁) = n − #{i : s₀ᵢ + γ·s₁ᵢ = 0}`. -/
theorem hammingNorm_line_eq (s₀ s₁ : ι → F) (γ : F) :
    hammingNorm (s₀ + γ • s₁) + (univ.filter (fun i => s₀ i + γ * s₁ i = 0)).card
      = Fintype.card ι := by
  classical
  have hpt : ∀ i, (s₀ + γ • s₁) i = s₀ i + γ * s₁ i := by
    intro i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hnorm : hammingNorm (s₀ + γ • s₁)
      = (univ.filter (fun i => s₀ i + γ * s₁ i ≠ 0)).card := by
    unfold hammingNorm
    rw [Finset.card_filter, Finset.card_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hpt i]
  rw [hnorm]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset ι)) (p := fun i => s₀ i + γ * s₁ i ≠ 0)
  simp only [not_not] at hsplit
  rw [hsplit, Finset.card_univ]

/-- **STEP 1, ratio-census form.** The weight of the line point equals the full count minus the
always-zero count minus the ratio multiplicity at `γ`:
`hammingNorm (s₀ + γ • s₁) + z₀ + ratioMult s₀ s₁ γ = n`,  `z₀ = #{i : s₁ᵢ=0 ∧ s₀ᵢ=0}`.
This is the precise statement that far-line incidence is the multiplicity profile of the ratio
sequence. -/
theorem hammingNorm_line_eq_sub_ratio_mult (s₀ s₁ : ι → F) (γ : F) :
    hammingNorm (s₀ + γ • s₁)
        + (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card
        + ratioMult s₀ s₁ γ
      = Fintype.card ι := by
  have h1 := hammingNorm_line_eq s₀ s₁ γ
  have h2 := zeroCount_split s₀ s₁ γ
  omega

/-! ### The first-moment identity (μ = E[incidence] = wt(s₁)) -/

/-- **The first-moment identity.** Summing the ratio multiplicity over *all* scalars `γ` counts
each support coordinate exactly once: `∑_γ ratioMult s₀ s₁ γ = #{i : s₁ᵢ ≠ 0} = wt(s₁)`.
For a far direction with full support (`= n`) this is the exact `μ = E[far-line incidence] = n`
recorded in the #407 ledger. -/
theorem sum_ratioMult_eq_support [Fintype F] (s₀ s₁ : ι → F) :
    ∑ γ : F, ratioMult s₀ s₁ γ = (univ.filter (fun i => s₁ i ≠ 0)).card := by
  classical
  unfold ratioMult
  -- `∑_γ #{i ∈ supp : r i = γ}` fibers the support over the ratio map.
  have hfib : ∑ γ : F, (univ.filter (fun i => s₁ i ≠ 0 ∧ ratioSeq s₀ s₁ i = γ)).card
      = ∑ γ : F, ((univ.filter (fun i => s₁ i ≠ 0)).filter
          (fun i => ratioSeq s₀ s₁ i = γ)).card := by
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfib]
  rw [← Finset.card_eq_sum_card_fiberwise
    (f := fun i => ratioSeq s₀ s₁ i) (s := univ.filter (fun i => s₁ i ≠ 0)) (t := (univ : Finset F))
    (fun i _ => Finset.mem_univ _)]

/-! ### The level-set degree consumer -/

/-- **Level-set lower bound on the weight.** Any cap `m` on the ratio multiplicity at `γ`
(`ratioMult s₀ s₁ γ ≤ m`) gives an immediate lower bound on the weight of the line point:
`hammingNorm (s₀ + γ • s₁) ≥ n − z₀ − m`.  In the smooth-domain prize regime the cap is the
level-set degree bound (`m ≤ deg r ≤ k−1`, since `γ` killing `c` coordinates forces
`s₀ + γ·s₁` — an evaluation of a degree-`< k` polynomial — to have `c` roots in the domain);
this is the STEP 2 algebraic input.  The bound is stated cap-agnostic so any source of the cap
(degree, Weil, or BGK) plugs in. -/
theorem hammingNorm_line_ge_of_ratioMult_le (s₀ s₁ : ι → F) (γ : F) {m : ℕ}
    (hm : ratioMult s₀ s₁ γ ≤ m) :
    Fintype.card ι ≤ hammingNorm (s₀ + γ • s₁)
        + (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card + m := by
  have h := hammingNorm_line_eq_sub_ratio_mult s₀ s₁ γ
  omega

/-! ### STEP 2 (D3): the incidence-at-radius level-set count + per-line binding-radius bound

The far-line incidence at radius `w` for the raw line stack `(s₀, s₁)` is, by definition, the
number of scalars whose line point has weight `≤ w`:
`incidence(w) = #{γ : hammingNorm (s₀ + γ • s₁) ≤ w}`.  STEP 1 rewrites the weight via the ratio
multiplicity, so STEP 2 below converts the incidence into the **level-set profile** of the ratio
function: the incidence at radius `w` is *exactly* the number of scalars whose ratio multiplicity
reaches `n − z₀ − w`.  This is the precise object the #407 D3 thread reasons about — far-line
incidence IS the high-multiplicity census of the ratio sequence `r(x) = −s₀(x)/s₁(x)`.

The honest first-moment consequence (`farIncidence_mul_le_support`, a pure Markov bound off
`sum_ratioMult_eq_support`) bounds this **per fixed line `(s₀, s₁)`**:
`incidence(w) · (n − z₀ − w) ≤ wt(s₁)`.  At the Johnson-scale *binding radius* (agreement
`a = n − w ≈ √(k·n)`, i.e. `n − z₀ − w ≈ a`) this reads `incidence ≤ wt(s₁)/a ≤ n/a ≤ √(n/k)` —
which would beat the budget `n`.  **But this is per a single fixed `(s₀, s₁)`.**  The MCA far-line
incidence is a *union over the in-window codeword list*: each bad `γ` subtracts its **own** closest
codeword `w_γ`, so there is no single fixed line stack carrying all the bad scalars (probe
`scripts/probes/probe_407_d3step2_binding_count.py`: at the binding radius every bad `γ` has a
*distinct* closest codeword — `#distinct = #bad` for the monomial adversary on smooth orbits, and
no fixed surrogate line has ratio multiplicity `≥ a` at all bad scalars).  So this per-line Markov
bound does **not** collapse the MCA count to `√(n/k)`; the open content is exactly the size of the
codeword list it is summed against (the sub-Johnson supply core), which this file does not bound.
The lemmas here are the exact, reusable, character-sum-free per-line incidence layer. -/

/-- **STEP 2 (the incidence-at-radius level-set equality).** The far-line incidence at radius `w`
— the scalars whose line point `s₀ + γ • s₁` has weight `≤ w` — is *exactly* the number of scalars
whose ratio multiplicity reaches `n − z₀ − w`:
`#{γ : hammingNorm (s₀ + γ • s₁) ≤ w} = #{γ : ratioMult s₀ s₁ γ ≥ n − z₀ − w}`,
where `z₀ = #{i : s₁ᵢ = 0 ∧ s₀ᵢ = 0}` and `n = |ι|`.  This turns the far-line incidence into the
high-multiplicity census of the ratio sequence — the exact STEP-1-to-STEP-2 bridge of the D3
thread. -/
theorem farIncidence_eq_ratioMult_level [Fintype F] (s₀ s₁ : ι → F) (w : ℕ) :
    (univ.filter (fun γ : F => hammingNorm (s₀ + γ • s₁) ≤ w)).card
      = (univ.filter (fun γ : F =>
          Fintype.card ι - (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card - w
            ≤ ratioMult s₀ s₁ γ)).card := by
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h := hammingNorm_line_eq_sub_ratio_mult s₀ s₁ γ
  omega

/-- **The first-moment (Markov) far-line incidence bound, per fixed line.** Summing the
incidence-at-radius level-set equality against the conservation law `∑_γ ratioMult = wt(s₁)`:
the far-line incidence at radius `w` times the demanded agreement `(n − z₀ − w)` is at most the
support size of the direction: `incidence(w) · (n − z₀ − w) ≤ wt(s₁)`.

This is the honest per-line binding-radius count: at the Johnson-scale agreement `a = n − z₀ − w`
it gives `incidence(w) ≤ wt(s₁)/a`.  It is character-sum-free and BGK-independent, but holds for a
**single fixed** `(s₀, s₁)`; the MCA far-line incidence ranges over a list of distinct nearby
codewords (one per bad `γ`), so it is the codeword-list size — not this per-line bound — that is the
open core (see the section docstring and `probe_407_d3step2_binding_count.py`). -/
theorem farIncidence_mul_le_support [Fintype F] (s₀ s₁ : ι → F) (w : ℕ) :
    (univ.filter (fun γ : F => hammingNorm (s₀ + γ • s₁) ≤ w)).card
        * (Fintype.card ι - (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card - w)
      ≤ (univ.filter (fun i => s₁ i ≠ 0)).card := by
  classical
  set z₀ := (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card with hz₀
  set μ₀ := Fintype.card ι - z₀ - w with hμ₀
  -- rewrite the incidence as the level set, then bound by the conservation sum.
  rw [farIncidence_eq_ratioMult_level s₀ s₁ w, ← hz₀, ← hμ₀,
      ← sum_ratioMult_eq_support s₀ s₁]
  calc (univ.filter (fun γ : F => μ₀ ≤ ratioMult s₀ s₁ γ)).card * μ₀
      = ∑ _γ ∈ univ.filter (fun γ : F => μ₀ ≤ ratioMult s₀ s₁ γ), μ₀ := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ univ.filter (fun γ : F => μ₀ ≤ ratioMult s₀ s₁ γ), ratioMult s₀ s₁ γ :=
        Finset.sum_le_sum (fun γ hγ => (Finset.mem_filter.mp hγ).2)
    _ ≤ ∑ γ : F, ratioMult s₀ s₁ γ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)


/-- **Quotient form of the per-line far-incidence bound.**  When the demanded agreement
`n − z₀ − w` is positive, the product bound `incidence · agreement ≤ wt(s₁)` gives the reusable
ratio form

`incidence(w) ≤ wt(s₁) / (n − z₀ − w)`.

This is often the form needed at the binding radius.  It is still a **single fixed line** bound;
MCA/CORE remains open because the global far-line incidence unions over many closest codewords. -/
theorem farIncidence_le_support_div [Fintype F] (s₀ s₁ : ι → F) (w : ℕ)
    (hpos : 0 < Fintype.card ι - (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card - w) :
    (univ.filter (fun γ : F => hammingNorm (s₀ + γ • s₁) ≤ w)).card
      ≤ (univ.filter (fun i => s₁ i ≠ 0)).card /
          (Fintype.card ι - (univ.filter (fun i => s₁ i = 0 ∧ s₀ i = 0)).card - w) := by
  classical
  exact (Nat.le_div_iff_mul_le hpos).2 (farIncidence_mul_le_support s₀ s₁ w)

end ArkLib.ProximityGap.RatioCensus

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.RatioCensus.zeroCount_split
#print axioms ArkLib.ProximityGap.RatioCensus.hammingNorm_line_eq
#print axioms ArkLib.ProximityGap.RatioCensus.hammingNorm_line_eq_sub_ratio_mult
#print axioms ArkLib.ProximityGap.RatioCensus.sum_ratioMult_eq_support
#print axioms ArkLib.ProximityGap.RatioCensus.hammingNorm_line_ge_of_ratioMult_le
#print axioms ArkLib.ProximityGap.RatioCensus.farIncidence_eq_ratioMult_level
#print axioms ArkLib.ProximityGap.RatioCensus.farIncidence_mul_le_support
#print axioms ArkLib.ProximityGap.RatioCensus.farIncidence_le_support_div
