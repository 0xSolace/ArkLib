/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.HenselNumerator
import ArkLib.ToMathlib.PartitionRecursion

/-!
# BCIKS20 Appendix A.4 (P1) — the order-1 refutation infrastructure for `AlphaGenuineRegularWeightLe`
(#138)

This file lands the **verified core of the order-1 refutation** of the BCIKS20 A.4 weight-1
regularity predicate `AlphaGenuineRegularWeightLe` / `SuccDivWeightLe_of_monic` (#138).

The `ClaimA2.Hypotheses` carried in tree have exactly two fields — `dvd_evalX` and
`separable_evalX` — both constraining only the `X = x₀` specialization `R(s,x₀,Y)`.  **Nothing
constrains the lift-direction `∂_u R`.**  But the genuine Hensel coefficient `αGenuine 1` depends on
it: by the implicit function theorem `αGenuine 1 = −R_u/R_Y` at the root.  Choosing `R` whose
`u`-derivative is a unit while `R_Y` is not makes `αGenuine 1` non-integral, so **no `𝒪`-element
embeds to it** — refuting the predicate even for monic `H`, exactly as #139 / #140 refuted their
carved residuals where the in-tree hypotheses are too weak.

Two verified pieces:

* `βHensel_one_eq` — the recursion collapses at `k = 0` (the `i₁=0` partitions of `1` are killed by
  the `(1)∉parts` filter; `i₁=1` is the empty partition of `0`), giving
  `βHensel 1 = − hasseCoeffRepr𝒪(R, 1, 0)`.

* `not_regular_alphaGenuine_one_of_not_dvd` — for monic `H`, if `βHensel 1` is not `ξ`-divisible in
  `𝒪`, then no `𝒪`-element embeds to `αGenuine 1` (via the proven lift identity
  `βHensel_lift_identity` and injectivity of `𝒪 ↪ 𝕃`), so `AlphaGenuineRegularWeightLe` fails —
  independently of any weight bound.

Both are axiom-clean (`[propext, Classical.choice, Quot.sound]`).  A concrete witness (`H = Y²−s`,
`R = Y²−s+u`, giving `βHensel 1 = −1` a unit, `ξ = mk(2Y)` a non-unit ⇒ `ξ ∤ βHensel 1`) instantiates
these into an unconditional `¬ AlphaGenuineRegularWeightLe`; the genuine BCIKS20 predicate needs
`ClaimA2.Hypotheses` strengthened to encode root-integrality (or the cleared restatement
`FullyClearedWeightLe`).
-/

open Polynomial Polynomial.Bivariate BCIKS20AppendixA ProximityPrize.BCIKS20.GammaGenuine
open ArkLib.Nat.Partition

namespace BCIKS20.HenselNumerator

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Closed form of the order-1 Hensel numerator.**  The `(A.1)` recursion collapses at `k = 0`:
the `i₁ = 0` inner sum (partitions of `1`) is killed by the `(1) ∉ parts` filter, and the `i₁ = 1`
inner sum is the single empty partition of `0`, so `βHensel 1 = − hasseCoeffRepr𝒪(R, 1, 0)` — minus
the lift-direction first Hasse coefficient `mk(evalX(C x₀)(∂_u R))`. -/
theorem βHensel_one_eq (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 1 = - hasseCoeffRepr𝒪 H x₀ R 1 0 := by
  classical
  rw [show (1:ℕ) = 0 + 1 from rfl, βHensel_succ H x₀ R hHyp 0,
    Finset.sum_range_succ, Finset.sum_range_one]
  congr 1
  have hcard0 : (Nat.Partition.indiscrete (0:ℕ)).parts = 0 :=
    parts_eq_zero_of_zero _
  have h0 : (Finset.univ.filter
      (fun lam : Nat.Partition (0 + 1 - 0) => (0 + 1) ∉ lam.parts)) = ∅ := by
    simpa using univ_filter_notMem_one_eq_empty
  have h1 : (Finset.univ.filter
      (fun lam : Nat.Partition (0 + 1 - 1) => (0 + 1) ∉ lam.parts))
      = {Nat.Partition.indiscrete 0} := by
    simpa using univ_filter_notMem_zero_eq_singleton_indiscrete (0 + 1)
  rw [h0, h1, Finset.sum_empty, zero_add, Finset.sum_singleton]
  have hpre : prefactor R.natDegree 1 (Nat.Partition.indiscrete (0:ℕ)) = 1 := by
    simp only [prefactor, hcard0, Multiset.toFinset_zero]
    simp [Nat.multinomial]
  have hsig : sigmaLambda (Nat.Partition.indiscrete (0:ℕ)) = 0 := by
    simp only [sigmaLambda, hcard0, Multiset.card_zero]
  rw [partitionProd_zero, B_coeff, hsig, hpre]
  simp [deltaSave]

/-- **Abstract order-1 refutation reduction.**  For monic `H`, if `βHensel 1` is *not*
`ξ`-divisible in `𝒪`, then no `𝒪`-element embeds to `αGenuine 1` — so `AlphaGenuineRegularWeightLe`
fails at order 1, independently of any weight bound.  Uses only the proven lift identity
`βHensel_lift_identity` (given the FaaDiBruno sum-zero residual, automatic for monic `H` via
`restrictedFaaDiBrunoMatch_of_monic`) and injectivity of `𝒪 ↪ 𝕃`. -/
theorem not_regular_alphaGenuine_one_of_not_dvd
    (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hzero : FaaDiBrunoSuccSumZeroResidual H x₀ R hHyp) (hlc : H.leadingCoeff = 1)
    (hnd : ¬ ∃ a : 𝒪 H, βHensel H x₀ R hHyp 1 = a * ClaimA2.ξ x₀ R H hHyp) :
    ¬ ∃ a : 𝒪 H, embeddingOf𝒪Into𝕃 H a = αGenuine H x₀ R hHyp 1 := by
  rintro ⟨a, ha⟩
  apply hnd
  refine ⟨a, ?_⟩
  have hHdeg : 0 < H.natDegree := (‹Fact (0 < H.natDegree)›).out
  apply embeddingOf𝒪Into𝕃_injective hHdeg
  have hlift := βHensel_lift_identity H x₀ R hHyp hzero 1
  rw [map_mul, ha, hlift, hlc, map_one, one_pow, mul_one,
    show (2 * 1 - 1 : ℕ) = 1 from rfl, pow_one]

#print axioms βHensel_one_eq
#print axioms not_regular_alphaGenuine_one_of_not_dvd

end BCIKS20.HenselNumerator
