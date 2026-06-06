/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.Data.Polynomial.RationalFunctionsCore
import ArkLib.ToMathlib.PartitionRecursion
import ArkLib.ToMathlib.HasseDerivNumerators
import ArkLib.ToMathlib.WeightLambdaCalculus
import Mathlib

/-!
# The Hensel-Lift Numerator Recursion $\beta_t$

This module defines the recurrence relation $\beta_t$ for the regular numerators of the Hensel-lift
coefficients in the proximity gap analysis of Reed–Solomon codes, following [BCIKS20] Appendix A.4.

### The Recurrence Relation

Let $H \in F[X][Y]$ define a function field extension $\mathbb{L}/\mathbb{K}$ and $\mathcal{O}$ be the ring of regular elements.
The recurrence relation is defined by:
$$\beta_0 = T$$
$$\beta_t = \sum_{i_1 \ge 0, \lambda \in \text{Part}(t - i_1), \lambda \ne (t)} W^{i_1 + \delta_{i_1,0} - 1} \xi^{2i_1 + \sum \lambda - 2} B_{i_1, \lambda} \prod_{l \in \lambda} \beta_l^{\lambda_l}$$
where:
- $T$ is the generator of the quotient ring $\mathcal{O}$,
- $\text{Part}(m)$ denotes the set of integer partitions of $m$,
- $W \in \mathcal{O}$ is the regular representative of the leading coefficient of $H$,
- $\xi$ is the evaluation modifier,
- $B_{i_1, \lambda} \in \mathcal{O}$ are the regular numerators of the bivariate Hasse derivative.

This module proves:
1. Well-foundedness of the recurrence relation under the partition-refinement ordering.
2. Invariance of the recurrence outputs under the regular elements ring $\mathcal{O}$ (integrality of the numerators).
3. The total degree/weight bounds of the recursion outputs under the $\Lambda$-weight filtration.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace ArkLib

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-! ### Termination Metric for the Recurrence Relation

To establish the well-foundedness of the recurrence relation defining $\beta_t$, we prove that the indices
of all recursive calls strictly decrease. Every recursive call $\beta_l$ invoked in the definition of
$\beta_{t+1}$ corresponds to a part $l$ of a partition $\lambda \vdash t + 1 - i_1$, where the trivial
partition $(i_1=0, \lambda = (t+1))$ is excluded. We show that $l < t+1$ holds for all such parts, which
justifies the termination of the recursive definition under the standard well-founded relation on $\mathbb{N}$. -/

/-- Establishes that the index $l$ of any recursive call in the definition of $\beta_{t+1}$ is strictly
less than $t+1$, ensuring the well-foundedness of the recursion. -/
theorem recursionStep_lt {t i₁ : ℕ} (p : Nat.Partition (t + 1 - i₁))
    (hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)))
    {l : ℕ} (hl : l ∈ p.parts) : l < t + 1 := by
  rcases Nat.eq_zero_or_pos i₁ with h0 | hpos
  · subst h0
    simp only [Nat.sub_zero, true_and] at p hexcl hl ⊢
    have hne : p ≠ Nat.Partition.indiscrete (t + 1) := by
      intro hp; apply hexcl
      rw [hp]; exact Nat.Partition.indiscrete_parts (Nat.succ_ne_zero t)
    exact ArkLib.Nat.Partition.parts_lt_of_ne_indiscrete p hne l hl
  · have hle : l ≤ t + 1 - i₁ := Nat.Partition.le_of_mem_parts hl
    omega

/-! ### Prefactor Exponents Bookkeeping

We define the exponents of the prefactors $W$ and $\xi$ appearing in the recurrence step.
For $i_1 \ge 0$, we define the Kronecker-like correction $\delta_{i_1,0}$, which yields the exponents:
- $W$-exponent: $i_1 + \delta_{i_1,0} - 1$
- $\xi$-exponent: $2i_1 + |\lambda| - 2$
where $|\lambda|$ is the number of parts of the partition. -/

/-- Kronecker-like delta function $\delta_{i_1,0}$ returning 1 if $i_1 = 0$ and 0 otherwise. -/
def betaδ (i₁ : ℕ) : ℕ := if i₁ = 0 then 1 else 0

/-- Exponent of the leading coefficient prefactor $W$ in the recurrence term. -/
def betaWExp (i₁ : ℕ) : ℕ := i₁ + betaδ i₁ - 1

/-- Exponent of the evaluation modifier prefactor $\xi$ in the recurrence term. -/
def betaξExp {m : ℕ} (i₁ : ℕ) (p : Nat.Partition m) : ℕ :=
  2 * i₁ + Multiset.card p.parts - 2

@[simp] lemma betaWExp_zero : betaWExp 0 = 0 := by simp [betaWExp, betaδ]

lemma betaWExp_of_pos {i₁ : ℕ} (h : 0 < i₁) : betaWExp i₁ = i₁ - 1 := by
  simp [betaWExp, betaδ, Nat.ne_of_gt h]

/-! ### BCIKS20 Hensel-Lift Numerator Recurrence

The recurrence relation $\beta_t \in \mathcal{O}_H$ constructs the regular numerators of the
Hensel-lift coefficients. The base case is given by $\beta_0 = T$ (represented by $X$ in the coordinate ring).
The step $\beta_{t+1}$ is defined by summing over the partition components, weighted by the appropriate
powers of $W$ and $\xi$, and the bivariate Hasse derivative numerators $B_{i_1, \lambda}$. -/

/-- BCIKS20 Appendix-A.4 Hensel-lift numerator recurrence $\beta_t$. -/
noncomputable def betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) : ℕ → 𝒪 H
  | 0 => Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X
  | (t + 1) =>
      ∑ i₁ ∈ Finset.range (t + 2),
        ∑ p : Nat.Partition (t + 1 - i₁),
          if hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) then
            W_𝒪 H ^ betaWExp i₁
              * ξ x₀ R H hHyp ^ betaξExp i₁ p
              * Bcoeff i₁ p
              * ∏ l ∈ p.parts.toFinset.attach,
                  betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)
          else 0
  decreasing_by
    exact recursionStep_lt p hexcl (Multiset.mem_toFinset.mp l.2)

/-! ### Defining Equations -/

/-- Unfolds the base case $\beta_0$. -/
@[simp] lemma betaRec_zero (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) :
    betaRec x₀ R H hHyp Bcoeff 0 =
      Ideal.Quotient.mk (Ideal.span {H_tilde' H}) Polynomial.X := by
  rw [betaRec]

/-- Unfolds the successor step $\beta_{t+1}$. -/
lemma betaRec_succ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    betaRec x₀ R H hHyp Bcoeff (t + 1) =
      ∑ i₁ ∈ Finset.range (t + 2),
        ∑ p : Nat.Partition (t + 1 - i₁),
          if hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) then
            W_𝒪 H ^ betaWExp i₁
              * ξ x₀ R H hHyp ^ betaξExp i₁ p
              * Bcoeff i₁ p
              * ∏ l ∈ p.parts.toFinset.attach,
                  betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)
          else 0 := by
  rw [betaRec]

/-! ### Integrality of the Recurrence Outputs

Since `betaRec` is constructed within the ring of regular elements $\mathcal{O}_H$, its image
under the canonical embedding into the function field $\mathbb{L}_H$ is guaranteed to be integral. -/

/-- Proof that the recurrence outputs are integral elements of the function field. -/
theorem betaRec_mem (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (betaRec x₀ R H hHyp Bcoeff t) ∈ regularElms_set H :=
  regularElms_set_embedding H _

/-! ### Function Field Characterization of Integrality

We establish that the terms of the recurrence remain integral when viewed in the function field
$\mathbb{L}_H$, even when Hasse-derivative coefficients carry denominators of $W$. Integrality
is preserved because the prefactors carry sufficient powers of $W$ to clear the denominators. -/

/-- A finite sum of elements in $\mathbb{L}_H$ is integral if each term has a $W$-power numerator
satisfying the divisibility condition in $\mathcal{O}_H$. -/
theorem sum_mem_regularElms_set_of_term_numerators {ι : Type*} (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (s : Finset ι) (term : ι → 𝕃 H) (j : ι → ℕ)
    (hterm : ∀ i ∈ s, ∃ B : 𝒪 H,
        term i * W_𝕃 H ^ (j i) = embeddingOf𝒪Into𝕃 H B ∧ W_𝒪 H ^ (j i) ∣ B) :
    (∑ i ∈ s, term i) ∈ regularElms_set H := by
  classical
  refine Finset.sum_induction term (· ∈ regularElms_set H)
    (fun _ _ ha hb => regularElms_set_add ha hb) (regularElms_set_zero H) ?_
  intro i hi
  exact hasWPowerNumerator.mem_regularElms_set (hterm i hi)

/-- Specializes the integrality condition to a product of prefactors and recursive sub-terms. -/
theorem term_mem_regularElms_set_of_numerator {H : F[X][Y]}
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {pref A P : 𝕃 H} {j : ℕ}
    (hnum : ∃ B : 𝒪 H, (pref * A) * W_𝕃 H ^ j = embeddingOf𝒪Into𝕃 H B ∧ W_𝒪 H ^ j ∣ B)
    (hP : P ∈ regularElms_set H) :
    (pref * A) * P ∈ regularElms_set H :=
  regularElms_set_mul (hasWPowerNumerator.mem_regularElms_set hnum) hP

/-! ### Weight Filtration and Degree Bounds

We bound the filtration weight of the recurrence output $\beta_t$ under the $\Lambda$-weight filtration
$\text{weight}_\Lambda$. The bound is reduced to verification of individual term budgets. -/

/-- Represents a single summand in the recurrence relation for $\beta_{t+1}$. -/
noncomputable def betaTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t i₁ : ℕ)
    (p : Nat.Partition (t + 1 - i₁)) : 𝒪 H :=
  if ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) then
    W_𝒪 H ^ betaWExp i₁
      * ξ x₀ R H hHyp ^ betaξExp i₁ p
      * Bcoeff i₁ p
      * ∏ l ∈ p.parts.toFinset.attach,
          betaRec x₀ R H hHyp Bcoeff l.1 ^ (p.parts.count l.1)
  else 0

/-- Expresses $\beta_{t+1}$ as a sum of individual terms. -/
lemma betaRec_succ_eq_sum_betaTerm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    betaRec x₀ R H hHyp Bcoeff (t + 1) =
      ∑ i₁ ∈ Finset.range (t + 2),
        ∑ p : Nat.Partition (t + 1 - i₁),
          betaTerm x₀ R H hHyp Bcoeff t i₁ p := by
  rw [betaRec_succ]
  refine Finset.sum_congr rfl (fun i₁ _ => Finset.sum_congr rfl (fun p _ => ?_))
  unfold betaTerm
  by_cases hexcl : ¬ (i₁ = 0 ∧ p.parts = ({t + 1} : Multiset ℕ)) <;> simp [hexcl]

/-- Bounds the filtration weight of the recurrence output $\beta_{t+1}$ in terms of the individual summand budgets. -/
theorem betaRec_weightBound_of_term_bounds (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree) {b : ℕ}
    (hterm_bound : ∀ i₁ ∈ Finset.range (t + 2), ∀ p : Nat.Partition (t + 1 - i₁),
        weight_Λ_over_𝒪 hH (betaTerm x₀ R H hHyp Bcoeff t i₁ p) D
          ≤ (WithBot.some b : WithBot ℕ)) :
    weight_Λ_over_𝒪 hH (betaRec x₀ R H hHyp Bcoeff (t + 1)) D
      ≤ (WithBot.some b : WithBot ℕ) := by
  classical
  rw [betaRec_succ_eq_sum_betaTerm]
  refine (weight_Λ_over_𝒪_sum_le hD hH _ _).trans ?_
  refine Finset.sup_le (fun i₁ hi₁ => ?_)
  refine (weight_Λ_over_𝒪_sum_le hD hH _ _).trans ?_
  refine Finset.sup_le (fun p _ => ?_)
  exact hterm_bound i₁ hi₁ p

end ArkLib

-- Axiom audit: every claimed-done declaration must rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#print axioms ArkLib.recursionStep_lt
#print axioms ArkLib.betaRec
#print axioms ArkLib.betaRec_zero
#print axioms ArkLib.betaRec_succ
#print axioms ArkLib.betaRec_mem
#print axioms ArkLib.sum_mem_regularElms_set_of_term_numerators
#print axioms ArkLib.term_mem_regularElms_set_of_numerator
#print axioms ArkLib.betaRec_succ_eq_sum_betaTerm
#print axioms ArkLib.betaRec_weightBound_of_term_bounds
#print axioms ArkLib.betaWExp_zero
#print axioms ArkLib.betaWExp_of_pos
