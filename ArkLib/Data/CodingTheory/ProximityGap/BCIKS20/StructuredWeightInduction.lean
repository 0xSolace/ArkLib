/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator

/-!
# The structured weight induction (Johnson E2′): the Claim A.2 invariant, assembled

DISPROOF_LOG O154 findings 3–7: the loose per-term wall (`βHenselSuccTermWeightResidual`)
is unprovable through the loose IH (the in-file wave-5 diagnosis), but the paper's
**structured** invariant — `Λ(β_t) ≤ 1 + (t+1)·deg(W) + e_t·Λ_ξ` (Claim A.2, fulltext
3962) — restores the partition cancellation: the per-term ξ-exponents collapse to exactly
`2k` and the W-exponents telescope (the (5.16) display). This file assembles the structured
strong induction, mirroring the in-tree `βHensel_weight_bound` skeleton:

* `structuredBound` — the Claim A.2 invariant value `1 + (t+1)·deg(W) + e_t·Λ_ξ-budget`
  (`e_t = 2t − 1` in ℕ-truncation, so `e_0 = 0`; `Λ_ξ`-budget `(d_R−1)·(D−d_H+1)` from the
  proven `weight_ξ_bound`);
* `βHensel_weight_bound_zero_structured` — the base case, exact at the tight anchor
  `D ≤ d_H + deg(W)` (finding 5: the paper's `Λ(T) = Λ(W) + 1`);
* `StructuredSuccTermBound` — the per-term obligation, now with the **structured** IH (the
  provable form; its arithmetic is findings 3+7, consuming the proven E1′ inventory);
* `βHensel_weight_bound_structured` — the assembled induction.

With a proof of `StructuredSuccTermBound` (the E1′ bricks + the in-tree calculus), the
structured bound composes with the proven `βHensel_weight_bound_of_structured_weight`
collapse into the loose target consumed by the kill-target/Claim-5.10 chain.

## References
* [BCIKS20] §A.4 Claim A.2 (fulltext 3959–3970), the §5 telescoping (1788–1797);
  DISPROOF_LOG O154 findings 3–7; `HasseIndexShift.lean` (the E1′ inventory).
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate BCIKS20AppendixA

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
  [Fact (0 < H.natDegree)]

/-- **The Claim A.2 structured invariant value** at order `t`:
`1 + (t+1)·deg(W) + e_t·(d_R−1)·(D−d_H+1)`, with `e_t = 2t−1` truncated (`e_0 = 0`). -/
noncomputable def structuredBound (H : F[X][Y]) (R : F[X][X][Y]) (D t : ℕ) : ℕ :=
  1 + (t + 1) * (H.leadingCoeff).natDegree
    + (2 * t - 1) * ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))

/-- **The structured base case (finding 5, the paper's `Λ(T) = Λ(W) + 1`):** at the tight
anchor `D ≤ d_H + deg(W)`, the order-0 numerator `β₀ = mk X` satisfies the structured
invariant exactly: `Λ(β₀) = D + 1 − d_H ≤ 1 + deg(W) = structuredBound 0`. -/
theorem βHensel_weight_bound_zero_structured (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D
      ≤ WithBot.some (structuredBound H R D 0) := by
  rw [βHensel_zero]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
  have hweq : weight_Λ (Polynomial.X : F[X][Y]) H D
      = WithBot.some (D + 1 - Bivariate.natDegreeY H) := by
    rw [weight_Λ, Polynomial.support_X (by norm_num)]
    simp
  rw [hweq]
  refine WithBot.coe_le_coe.mpr ?_
  unfold structuredBound
  have hdY : Bivariate.natDegreeY H = H.natDegree := rfl
  omega

/-- **The structured per-term obligation** — the provable form of the per-term wall: the
`(A.1)` recursion term at order `k + 1`, bounded by the structured invariant, **given the
structured IH** for all lower orders. Findings 3+7 verify its arithmetic by hand (the `2k`
ξ-collapse, the W-telescoping, the E1′ B-bound); the proven E1′ inventory
(`HasseIndexShift.lean`) and the in-tree weight calculus are its ingredients. -/
def StructuredSuccTermBound (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) (D : ℕ) (k : ℕ)
    (_hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some (structuredBound H R D l))
    (i1 : ℕ) (_hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (_hlam : (k + 1) ∉ lam.parts) : Prop :=
  weight_Λ_over_𝒪 hH
      ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
        * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
        * B_coeff H x₀ R i1 lam
        * partitionProd lam
            (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
    ≤ WithBot.some (structuredBound H R D (k + 1))

/-- **THE STRUCTURED WEIGHT INDUCTION (E2′, assembled).** Mirrors the in-tree
`βHensel_weight_bound` skeleton with the structured target: given the base anchor and the
structured per-term bound, every Hensel numerator satisfies the Claim A.2 invariant
`Λ(β_t) ≤ 1 + (t+1)·deg(W) + e_t·Λ_ξ`. -/
theorem βHensel_weight_bound_structured (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ H.natDegree + (H.leadingCoeff).natDegree)
    (hterm : ∀ (k : ℕ)
      (hIH : ∀ l, l < k + 1 →
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some (structuredBound H R D l))
      (i1 : ℕ) (hi1 : i1 ∈ Finset.range (k + 2))
      (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts),
        StructuredSuccTermBound x₀ R hHyp hH D k hIH i1 hi1 lam hlam)
    (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some (structuredBound H R D t) := by
  classical
  induction t using Nat.strong_induction_on with
  | _ t hIH =>
    match t with
    | 0 => exact βHensel_weight_bound_zero_structured x₀ R hHyp hH hDH htight
    | (k + 1) =>
        rw [βHensel_succ]
        refine le_trans (weight_Λ_over_𝒪_neg H hH hDH _) ?_
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun i1 hi1 => ?_)
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH hDH _ _) ?_
        refine Finset.sup_le (fun lam hlam => ?_)
        exact hterm k (fun l hl => hIH l (by omega)) i1 hi1 lam
          (Finset.mem_filter.mp hlam).2

/-! ## Source audit -/

#print axioms βHensel_weight_bound_zero_structured
#print axioms βHensel_weight_bound_structured

end BCIKS20.HenselNumerator
