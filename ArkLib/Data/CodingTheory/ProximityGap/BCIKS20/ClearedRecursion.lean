/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StructuredWeightInduction

/-!
# The repaired (A.1) cell coefficient: the paper's W-cleared, δ-adjusted `B_{i1,λ}`

Finding 14 (machine-checked in `Finding14Countermodel.lean`) established that the in-tree
`B_coeff` — the un-cleared `Y ↦ T` lift — diverges from [BCIKS20]'s
`B_{i1,λ} = W^{d−δ−Σλ}·A_{i1,λ}` (A.4, lines 4060–4080). This file defines the FAITHFUL
cell coefficient `B_coeffC`:

* for `i1 ≥ 1` the clearing power is `d_R − Σλ` (every `(T/W)`-denominator cleared);
* for `i1 = 0` the paper's δ-saving applies: the top coefficient of the specialized Hasse
  polynomial is `W`-divisible (the PROVEN `leadingCoeff_dvd_evalX_hasseDerivY_top`), so the
  exact quotient `c_top/W` rides at the top index and the rest clears at `d_R − 1 − Σλ`.

The anchored weight budgets — `(D_R−Σλ−i1) + (d_R−δ−Σλ)·degW`, exactly the paper's — are
proven here from the landed suppliers (`hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored`
+ the exact-division top-term estimate). Under these budgets the anchored per-term ledger
closes at EVERY cell (finding 13's verified cell arithmetic), which is what makes this the
correct recursion to thread through the (P1) weight induction and the Claim-5.10 chain.
-/

namespace BCIKS20.HenselNumerator

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

variable {F : Type} [Field F] {H : F[X][Y]} [Fact (Irreducible H)]
  [Fact (0 < H.natDegree)]

/-- **The paper-faithful cell coefficient** `B_{i1,λ}` (BCIKS20 A.4): the W-cleared,
δ-adjusted lift of the iterated Hasse coefficient, with the partition-multinomial
prefactor. At `i1 = 0` the top coefficient is divided exactly by `W` (the δ-saving);
at `i1 ≥ 1` the full clearing power `d_R − Σλ` is used. -/
noncomputable def B_coeffC (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) : 𝒪 H :=
  if i1 = 0 then
    (prefactor R.natDegree i1 lam) •
      Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam)
            (Bivariate.natDegreeY R - 1 - sigmaLambda lam)
          + Polynomial.C
              ((Polynomial.Bivariate.evalX (Polynomial.C x₀)
                  (hasseDerivX i1 (hasseDerivY (sigmaLambda lam) R))).coeff
                  (Bivariate.natDegreeY R - sigmaLambda lam)
                / H.leadingCoeff)
            * Polynomial.X ^ (Bivariate.natDegreeY R - sigmaLambda lam))
  else
    (prefactor R.natDegree i1 lam) •
      Ideal.Quotient.mk (Ideal.span {H_tilde' H})
        (hasseCoeffRepr𝒪_cleared H x₀ R i1 (sigmaLambda lam)
          (Bivariate.natDegreeY R - sigmaLambda lam))

/-- A single-monomial weight bound: `Λ(C c · X^b) ≤ b·(D+1−d_H) + deg c`. -/
theorem weight_Λ_C_mul_X_pow_le (c : F[X]) (b : ℕ) (D : ℕ) :
    weight_Λ (Polynomial.C c * Polynomial.X ^ b) H D
      ≤ WithBot.some (b * (D + 1 - Bivariate.natDegreeY H) + c.natDegree) := by
  rw [weight_Λ]
  refine Finset.sup_le fun n hn => ?_
  have hcoeff : (Polynomial.C c * Polynomial.X ^ b).coeff n
      = if n = b then c else 0 := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [eq_comm]
  by_cases hnb : n = b
  · subst hnb
    rw [hcoeff, if_pos rfl]
  · exfalso
    have : (Polynomial.C c * Polynomial.X ^ b).coeff n = 0 := by
      rw [hcoeff, if_neg hnb]
    exact (Polynomial.mem_support_iff.mp hn) this

/-- **The anchored budget for `i1 ≥ 1` cells:** `Λ(B_{i1,λ}) ≤ (D_R−Σλ−i1) + (d_R−Σλ)·degW`
— the paper's general cell budget, from the landed cleared-form supplier. -/
theorem B_coeffC_weight_le_anchored_pos
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ Bivariate.natDegreeY H + (H.leadingCoeff).natDegree)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    {i1 : ℕ} (hi1 : i1 ≠ 0) {m : ℕ} (lam : Nat.Partition m) :
    weight_Λ_over_𝒪 hH (B_coeffC (H := H) x₀ R i1 lam) D
      ≤ WithBot.some ((DR - sigmaLambda lam - i1)
          + (Bivariate.natDegreeY R - sigmaLambda lam) * (H.leadingCoeff).natDegree) := by
  rw [B_coeffC, if_neg hi1]
  refine le_trans (weight_Λ_over_𝒪_nsmul_le H hH hDH _ _) ?_
  exact hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored hH hDH htight x₀ R
    htotal hvanish i1 (sigmaLambda lam) _

/-- **The anchored SAVED budget for `i1 = 0` cells:**
`Λ(B_{0,λ}) ≤ (D_R−Σλ) + (d_R−1−Σλ)·degW` — the paper's δ-saved budget. The truncated
part is the landed cleared supplier at power `d_R−1−Σλ`; the top term saves exactly one
`degW` through the exact division `c_top/W` (provided by the W-divisibility of the top
Hasse coefficient). -/
theorem B_coeffC_weight_le_anchored_zero
    (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D)
    (htight : D ≤ Bivariate.natDegreeY H + (H.leadingCoeff).natDegree)
    (hWne : H.leadingCoeff ≠ 0)
    (x₀ : F) (R : F[X][X][Y]) {DR : ℕ}
    (htotal : ∀ n i, ((R.coeff n).coeff i).natDegree ≤ DR - n - i)
    (hvanish : ∀ n i, DR < n + i → ((R.coeff n).coeff i) = 0)
    {m : ℕ} (lam : Nat.Partition m)
    (hdvd : H.leadingCoeff ∣
      (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY (sigmaLambda lam) R))).coeff
        (Bivariate.natDegreeY R - sigmaLambda lam))
    (hdRm : sigmaLambda lam + 1 ≤ Bivariate.natDegreeY R)
    (hdRDR : Bivariate.natDegreeY R ≤ DR) :
    weight_Λ_over_𝒪 hH (B_coeffC (H := H) x₀ R 0 lam) D
      ≤ WithBot.some ((DR - sigmaLambda lam)
          + (Bivariate.natDegreeY R - 1 - sigmaLambda lam)
            * (H.leadingCoeff).natDegree) := by
  rw [B_coeffC, if_pos rfl]
  refine le_trans (weight_Λ_over_𝒪_nsmul_le H hH hDH _ _) ?_
  rw [map_add]
  refine le_trans (weight_Λ_over_𝒪_add_le H hH hDH _ _) ?_
  rw [max_le_iff]
  constructor
  · -- the truncated cleared part, at power d_R − 1 − Σλ
    refine le_trans (hasseCoeffRepr𝒪_cleared_weight_le_of_total_anchored hH hDH htight
      x₀ R htotal hvanish 0 (sigmaLambda lam) _) ?_
    refine WithBot.coe_le_coe.mpr ?_
    omega
  · -- the exact-division top term
    obtain ⟨c', hc'⟩ := hdvd
    have hdivval : (Polynomial.Bivariate.evalX (Polynomial.C x₀)
        (hasseDerivX 0 (hasseDerivY (sigmaLambda lam) R))).coeff
          (Bivariate.natDegreeY R - sigmaLambda lam) / H.leadingCoeff = c' := by
      rw [hc']
      exact mul_div_cancel_left₀ c' hWne
    rw [hdivval]
    rcases eq_or_ne c' 0 with hc0 | hc0
    · -- a vanishing top term contributes nothing
      subst hc0
      rw [map_zero, zero_mul, map_zero, weight_Λ_over_𝒪_zero]
      exact bot_le
    · refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
      refine le_trans (weight_Λ_C_mul_X_pow_le c' _ D) ?_
      refine WithBot.coe_le_coe.mpr ?_
      -- the exact quotient saves one degW: deg c' + degW ≤ shape budget at the top index
      have hdeg : c'.natDegree + (H.leadingCoeff).natDegree
          ≤ DR - sigmaLambda lam - (Bivariate.natDegreeY R - sigmaLambda lam) := by
        have hshape := specializedHasse_coeff_natDegree_le_of_total (x₀ := x₀) htotal 0
          (sigmaLambda lam) (Bivariate.natDegreeY R - sigmaLambda lam)
        have hmul : ((H.leadingCoeff) * c').natDegree
            = (H.leadingCoeff).natDegree + c'.natDegree :=
          Polynomial.natDegree_mul hWne hc0
        rw [hc', hmul] at hshape
        omega
      have hanchor : D + 1 - Bivariate.natDegreeY H
          ≤ (H.leadingCoeff).natDegree + 1 := by
        omega
      have hb := Nat.mul_le_mul_left
        (Bivariate.natDegreeY R - sigmaLambda lam) hanchor
      have hb1 : (Bivariate.natDegreeY R - sigmaLambda lam)
          * ((H.leadingCoeff).natDegree + 1)
          = (Bivariate.natDegreeY R - sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (Bivariate.natDegreeY R - sigmaLambda lam) := by
        rw [Nat.mul_add, Nat.mul_one]
      have hsplit : (Bivariate.natDegreeY R - sigmaLambda lam)
            * (H.leadingCoeff).natDegree
          = (Bivariate.natDegreeY R - 1 - sigmaLambda lam) * (H.leadingCoeff).natDegree
            + (H.leadingCoeff).natDegree := by
        have h1 : Bivariate.natDegreeY R - sigmaLambda lam
            = (Bivariate.natDegreeY R - 1 - sigmaLambda lam) + 1 := by omega
        rw [h1, Nat.add_mul, Nat.one_mul]
      omega

/-! ## Source audit -/

#print axioms weight_Λ_C_mul_X_pow_le
#print axioms B_coeffC_weight_le_anchored_pos
#print axioms B_coeffC_weight_le_anchored_zero

end BCIKS20.HenselNumerator
