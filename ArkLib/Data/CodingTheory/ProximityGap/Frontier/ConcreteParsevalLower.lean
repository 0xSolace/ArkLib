/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteMomentAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

set_option linter.style.longLine false

/-!
# The CONCRETE unconditional Parseval lower bound on the worst period (#444)

`_ExpanderMixingBound.M_lower_parseval` proves the unconditional spectral floor
`√(n(p−n)/(p−1)) ≤ M` (`M ≈ √n`, the reverse-EML / Parseval floor), but it carries BOTH the
second-moment Parseval value `Σ_{b≠0}‖η_b‖² = n(p−n)` AND the max≥RMS step `sumSq/(p−1) ≤ M²` as
ABSTRACT real hypotheses — never discharged on the actual periods `η_b = ∑_{y∈G} ψ(by)`.

This file discharges both on the concrete `M(μ_n) = max_{b≠0}‖η_b‖` (= `worstPeriod`, the same
`sup'` object used by `ConcreteMomentAssembly`):

> `worstPeriod_sq_ge_parseval` : `n(q−n)/(q−1) ≤ M(μ_n)²`,
> `worstPeriod_ge_sqrt_parseval` : `√(n(q−n)/(q−1)) ≤ M(μ_n)`.

Mechanism (all in-tree): the nonprincipal second moment `Σ_{b≠0}‖η_b‖² = q·n − n² = n(q−n)` (full
`subgroup_gaussSum_secondMoment` minus the DC term `‖η_0‖²=n²`), and `max≥RMS`:
`Σ_{b≠0}‖η_b‖² ≤ (q−1)·M²` (every nonzero term `≤ M²`, summed over the `q−1` nonzero frequencies). So
`n(q−n) ≤ (q−1)·M²`, i.e. `M² ≥ n(q−n)/(q−1)`; take the root.

This is the CONCRETE LOWER side of the expander-mixing bracket, the unconditional companion to the
concrete UPPER side `ConcreteMomentAssembly.worstPeriod_pow_le_qEnergy_sub_dc`. Together they pin the
worst period two-sided over the real `eta`: `√(n(q−n)/(q−1)) ≤ M(μ_n)` (PROVEN) and (under the
no-wraparound residual) `M(μ_n) ≤ √e·√(2rn)`.

## Honesty (scope)

This is the LOWER bound (`≈ √n`, unconditional, Parseval-only — no Paley/BGK conjecture). It is NOT
the prize: CORE asks for the UPPER bound `M(μ_n) ≤ C·√(n·log(p/n))`, whose gap to this floor
(`√n` vs `√(n·log p)`) is exactly the prize. Pure consolidation: turns the abstract Parseval-floor
hypotheses into in-tree theorems over the real periods. CORE stays OPEN.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ProximityGap.Frontier.ConcreteMomentAssembly

namespace ProximityGap.Frontier.ConcreteParsevalLower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Concrete nonprincipal second moment.** `∑_{b≠0} ‖η_b‖² = q·n − n²`. The full Parseval second
moment `subgroup_gaussSum_secondMoment` minus the DC term `‖η_0‖² = n²`. -/
theorem sum_nonzero_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2 := by
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * (G.card : ℝ) :=
    subgroup_gaussSum_secondMoment hψ G
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hdc : ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by rw [h0, Complex.norm_natCast]
  have hsplit : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [hfull, hdc] at hsplit
  linarith [hsplit]

/-- **Concrete Parseval floor (squared form).** `n(q−n)/(q−1) ≤ M(μ_n)²`, where
`M(μ_n) = max_{b≠0}‖η_b‖ = worstPeriod`. Discharges the abstract `M_sq_lower` on the real periods:
the nonprincipal second moment `n(q−n)` is `≤ (q−1)·M²` (each of the `q−1` nonzero terms `≤ M²`). -/
theorem worstPeriod_sq_ge_parseval {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) :
    (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1)
      ≤ (worstPeriod ψ G hne) ^ 2 := by
  set M := worstPeriod ψ G hne with hM
  -- each nonzero term ‖η_b‖² ≤ M²
  have hterm : ∀ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 ≤ M ^ 2 := by
    intro b hb
    have hbnz : b ∈ nonzeroFreqs F := by
      rw [mem_nonzeroFreqs]; exact (Finset.mem_erase.mp hb).1
    have hle : ‖eta ψ G b‖ ≤ M := by
      rw [hM]; unfold worstPeriod; exact Finset.le_sup' (fun b => ‖eta ψ G b‖) hbnz
    have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
    nlinarith [hnn, hle, norm_nonneg (eta ψ G b)]
  -- sum over q-1 nonzero freqs ≤ (q-1)·M²
  have hcard : (univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hsumle : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ 2 := by
    calc ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
        ≤ ∑ _b ∈ univ.erase (0 : F), M ^ 2 := Finset.sum_le_sum hterm
      _ = ((univ.erase (0 : F)).card : ℝ) * M ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((Fintype.card F : ℝ) - 1) * M ^ 2 := by
            rw [hcard]
            congr 1
            have hqpos : 1 ≤ Fintype.card F := Nat.one_le_iff_ne_zero.mpr (by
              have : 0 < Fintype.card F := Fintype.card_pos; omega)
            push_cast [Nat.cast_sub hqpos]; ring
  -- n(q-n) = Σ_{b≠0} ‖η_b‖² ≤ (q-1)M²
  rw [sum_nonzero_secondMoment hψ G] at hsumle
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  -- q·n − n² = n(q−n); divide
  have hnq : (Fintype.card F : ℝ) * (G.card : ℝ) - (G.card : ℝ) ^ 2
      = (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by ring
  rw [hnq] at hsumle
  rw [div_le_iff₀ hqm1]
  linarith [hsumle]

/-- **★ CONCRETE unconditional Parseval lower bound on the worst period.**
`√(n(q−n)/(q−1)) ≤ M(μ_n)`, the reverse-EML / max≥RMS floor (`≈ √n`), on the real periods
`η_b = ∑_{y∈G} ψ(by)`. Take the root of `worstPeriod_sq_ge_parseval` (`0 ≤ M`). Discharges
`_ExpanderMixingBound.M_lower_parseval` concretely. Unconditional: only Parseval, NO Paley/BGK. -/
theorem worstPeriod_ge_sqrt_parseval {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1))
      ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

/-- **Prize-regime numeric floor (squared).** In the prize regime `q ≥ 2n` (i.e. `2·card G ≤ card F`,
which `q = n^β` with `β ≥ 4` satisfies with huge room), the Parseval ratio floor simplifies to the
clean numeric bound `M(μ_n)² ≥ n/2`. Mechanism: `q ≥ 2n ⇒ (q−n)/(q−1) ≥ 1/2` (since
`2(q−n) ≥ q ≥ q−1`), so `n(q−n)/(q−1) ≥ n/2`, chained with `worstPeriod_sq_ge_parseval`.
(Probe `probe_parseval_half_floor.py`: 0 fails, holds even at the threshold `q = 2n−1`.) -/
theorem worstPeriod_sq_ge_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hreg : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    (G.card : ℝ) / 2 ≤ (worstPeriod ψ G hne) ^ 2 := by
  have hsq := worstPeriod_sq_ge_parseval hψ G hne hq1
  -- n(q−n)/(q−1) ≥ n/2 in the regime q ≥ 2n
  have hqm1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hnn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  have hfloor : (G.card : ℝ) / 2
      ≤ (G.card : ℝ) * ((Fintype.card F : ℝ) - (G.card : ℝ)) / ((Fintype.card F : ℝ) - 1) := by
    rw [le_div_iff₀ hqm1]
    -- (n/2)·(q−1) ≤ n·(q−n)  ⇔  n·(q−1) ≤ 2n·(q−n);  from q ≤ 2(q−n) i.e. 2n ≤ q
    nlinarith [hnn, hreg, hqm1]
  linarith [hfloor, hsq]

/-- **Prize-regime numeric floor (root form).** `√(n/2) ≤ M(μ_n)` whenever `q ≥ 2n`. The clean
usable `≥ √(n/2)` floor on the worst period in the prize regime, rooted from
`worstPeriod_sq_ge_half_card`. Still the EASY/unconditional Parseval direction (no BGK); the prize
gap to `√(n·log(p/n))` is untouched. -/
theorem worstPeriod_ge_sqrt_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hreg : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) / 2) ≤ worstPeriod ψ G hne := by
  have hsq := worstPeriod_sq_ge_half_card hψ G hne hq1 hreg
  have hMnn : 0 ≤ worstPeriod ψ G hne := worstPeriod_nonneg ψ G hne
  rw [show worstPeriod ψ G hne = Real.sqrt ((worstPeriod ψ G hne) ^ 2) from (Real.sqrt_sq hMnn).symm]
  exact Real.sqrt_le_sqrt hsq

end ProximityGap.Frontier.ConcreteParsevalLower

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.sum_nonzero_secondMoment
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_parseval
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_parseval
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_sq_ge_half_card
#print axioms ProximityGap.Frontier.ConcreteParsevalLower.worstPeriod_ge_sqrt_half_card
