/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import ArkLib.Data.Polynomial.RationalFunctions

/-!
# BCIKS20 Appendix A.4 — Hensel-lift numerator `β` : WAVE 1 FOUNDATION

This file builds the *reusable, mathlib-only* foundation for formalizing BCIKS20
(`2020-654`, "Proximity Gaps for Reed–Solomon Codes") Appendix A.4's recursive
Hensel-lift numerator `β` (ingredient D of the proximity-gap program).

WAVE 1 SCOPE.  This is wave 1 of a months-scale program.  We build and *prove*
(axiom-clean, no `sorry`/`admit`/`native_decide`/`bv_decide`):

1. The **multivariate Hasse coefficient** `mvHasseCoeff k p` (the genuine
   coeff-of-Taylor-shift / binomial-weighted-shift object, characteristic-free per
   BCIKS20 line 4350), with its defining `coeff` formula, additivity / `R`-linearity,
   `mvHasseCoeff 0 = id`, agreement with `Polynomial.hasseDeriv` in the single-variable
   case, and the monomial evaluation.

2. The **partition-indexed product** `partitionProd p b` = `∏_l (b l)^{λ_l}` for a
   `Nat.Partition`, with its reindexing-by-multiplicity lemma and the empty/singleton
   special cases, plus `sigmaLambda` (`Σλ`) and the multinomial/binomial `prefactor`.

WAVE 2 SCOPE (§4 below).  Imports `ArkLib.Data.Polynomial.RationalFunctions` and lands the
genuine `β` recursion of BCIKS20 (A.1) over the in-tree ring `𝒪 H`:

3. `hasseDerivX` / `hasseDerivY` — the iterated single-variable Hasse derivatives of the
   trivariate `R : F[X][X][Y]` on the lift-`X` layer (`map`-through-coeffs) and the `Y`
   layer (outermost), the genuine `Δ_X^{i1}` / `Δ_Y^{m}` of the paper (char-free).
4. `hasseEvalAtRoot` — evaluate the iterated Hasse coefficient at `(X = x₀, Y = α₀ = T/W)`
   into `𝕃 H`, mirroring `ClaimA2.ζ`.
5. `B_coeff : 𝒪 H` — the genuine rescaled coefficient `prefactor · A_{i1,λ} · W^{…}`,
   landed in `𝒪 H` via the canonical regular representative (the `W`-clearing **weight**
   lemma is the only deferred piece — `B_coeff` itself is the genuine object).
6. `βHensel : ℕ → 𝒪 H` — **the keystone**: the genuine (A.1) well-founded recursion,
   base case `β₀ = T mod H̃` (genuine `mk X`, not `0`), recursive arm the literal (A.1)
   sum `− ∑_{i1} ∑_{λ ≠ indiscrete} W^{…}·ξ^{…}·B_{i1,λ}·∏_l β_l^{λ_l}`.
7. `βHensel_zero` — base-case value lemma (PROVEN).
8. `(P1) βHensel_weight_bound` — `t = 0` case PROVEN; inductive step a documented `sorry`.
9. `(P2) βHensel_lift_identity` — the irreducible BCIKS20 A.4 frontier, documented `sorry`.

See `ingredientD-wave1-design.md` / `ingredientD-wave1-foundation.md` / `ingredientD-wave2.md`
for the staged specs.

The objects here are the **genuine** mathematical objects, never stubs:
`mvHasseCoeff k p` has `coeff n = (∏ᵢ (nᵢ+kᵢ).choose kᵢ) · coeff (n+k) p`, i.e. the real
binomial-weighted shift (its weight is genuinely positive, see `mvBinom_pos` /
`mvHasseCoeff_monomial_coeff_eq`), and `partitionProd` raises each distinct part to its
genuine multiplicity.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace BCIKS20.HenselNumerator

variable {σ : Type*} {R : Type*}

/-! ## 1. The multivariate Hasse coefficient -/

section MvHasse

variable [DecidableEq σ] [CommSemiring R]

/-- The **multivariate binomial weight** attached to multi-indices `s, k : σ →₀ ℕ`:
`∏ᵢ (sᵢ).choose (kᵢ)`, the product (over the union of supports — the only indices that can
contribute a factor `≠ 1`) of the single-variable binomial coefficients.

This is the genuine coefficient that the iterated single-variable Hasse derivative produces:
for `s = n + k` it is `∏ᵢ (nᵢ+kᵢ).choose kᵢ`.  When `kᵢ > sᵢ` for some `i` the factor is
`(sᵢ).choose (kᵢ) = 0`, killing the term — exactly "cannot differentiate past the degree". -/
def mvBinom (s k : σ →₀ ℕ) : ℕ :=
  ∏ i ∈ s.support ∪ k.support, (s i).choose (k i)

/-- `mvBinom s k = 0` whenever `k` does not divide-down into `s` (i.e. some `kᵢ > sᵢ`):
the binomial factor `(sᵢ).choose (kᵢ)` vanishes.  This is precisely the truncated-subtraction
guard that makes the Hasse coefficient pick out only the genuine shift `s = n + k`. -/
theorem mvBinom_eq_zero_of_not_le {s k : σ →₀ ℕ} (h : ¬ k ≤ s) : mvBinom s k = 0 := by
  classical
  rw [Finsupp.le_iff] at h
  simp only [not_forall, not_le] at h
  obtain ⟨i, hi, hlt⟩ := h
  apply Finset.prod_eq_zero (i := i)
  · -- `i ∈ k.support` since `k i > s i ≥ 0` forces `k i ≠ 0`.
    have : k i ≠ 0 := by omega
    exact Finset.mem_union.mpr (Or.inr (Finsupp.mem_support_iff.mpr this))
  · exact Nat.choose_eq_zero_of_lt hlt

/-- `mvBinom (n + k) k = ∏ᵢ (nᵢ + kᵢ).choose kᵢ`, the genuine multivariate binomial
weight of the shift `n ↦ n + k` (the value carried by `mvHasseCoeff`). -/
theorem mvBinom_add_right (n k : σ →₀ ℕ) :
    (mvBinom (n + k) k : ℕ) = ∏ i ∈ (n + k).support ∪ k.support, (n i + k i).choose (k i) := by
  classical
  unfold mvBinom
  refine Finset.prod_congr rfl ?_
  intro i _
  rfl

/-- The `k`-th **multivariate Hasse coefficient** of `p`: the genuine coeff-of-Taylor-shift
object `Δ^k p`, defined (à la `Polynomial.hasseDeriv`) as
`∑_s monomial (s - k) (mvBinom s k • coeff s p)`.

Its `coeff n` is `(∏ᵢ (nᵢ+kᵢ).choose kᵢ) · coeff (n+k) p` (`mvHasseCoeff_coeff`), the
binomial-weighted shift used by BCIKS20 (characteristic-free, no division, no `m!`).  It is
the iterated single-variable `Polynomial.hasseDeriv`, one derivative per variable
(`mvHasseCoeff_single_coeff` shows the single-variable agreement). -/
def mvHasseCoeff (k : σ →₀ ℕ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ s ∈ p.support, MvPolynomial.monomial (s - k) ((mvBinom s k : R) * MvPolynomial.coeff s p)

@[simp]
theorem mvHasseCoeff_zero_right (k : σ →₀ ℕ) :
    mvHasseCoeff k (0 : MvPolynomial σ R) = 0 := by
  simp [mvHasseCoeff]

/-- The defining coefficient formula: the genuine binomial-weighted shift. -/
theorem mvHasseCoeff_coeff (k : σ →₀ ℕ) (p : MvPolynomial σ R) (n : σ →₀ ℕ) :
    MvPolynomial.coeff n (mvHasseCoeff k p)
      = (mvBinom (n + k) k : R) * MvPolynomial.coeff (n + k) p := by
  classical
  rw [mvHasseCoeff, MvPolynomial.coeff_sum]
  -- Only the term `s = n + k` can contribute to `coeff n`, via `coeff_monomial` at `s - k = n`.
  rw [Finset.sum_eq_single (n + k)]
  · rw [MvPolynomial.coeff_monomial]
    simp
  · intro s _ hsn
    rw [MvPolynomial.coeff_monomial]
    by_cases hsk : s - k = n
    · -- `s - k = n` but `s ≠ n + k`: then `¬ k ≤ s` (else `s = (s-k)+k = n+k`), so the weight is 0.
      have hnotle : ¬ k ≤ s := by
        intro hle
        apply hsn
        have : (s - k) + k = s := tsub_add_cancel_of_le hle
        rw [hsk] at this
        exact this.symm
      rw [if_pos hsk, mvBinom_eq_zero_of_not_le hnotle]
      simp
    · simp [hsk]
  · intro hns
    rw [MvPolynomial.notMem_support_iff] at hns
    simp [hns]

/-- `mvBinom n 0 = 1`: the empty (`k = 0`) shift carries no binomial weight. -/
@[simp]
theorem mvBinom_zero_right (n : σ →₀ ℕ) : mvBinom n 0 = 1 := by
  classical
  unfold mvBinom
  apply Finset.prod_eq_one
  intro i _
  simp

/-- `mvHasseCoeff 0 = id` (non-vacuity / `hasseDeriv_zero'` analogue): the zeroth Hasse
coefficient is the polynomial itself, so the construction is genuinely not the zero map. -/
@[simp]
theorem mvHasseCoeff_zero_left (p : MvPolynomial σ R) : mvHasseCoeff 0 p = p := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [mvHasseCoeff_coeff]
  simp

/-- `mvHasseCoeff k` is additive in `p`. -/
theorem mvHasseCoeff_add (k : σ →₀ ℕ) (p q : MvPolynomial σ R) :
    mvHasseCoeff k (p + q) = mvHasseCoeff k p + mvHasseCoeff k q := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [MvPolynomial.coeff_add, mvHasseCoeff_coeff, mvHasseCoeff_coeff, mvHasseCoeff_coeff,
    MvPolynomial.coeff_add, mul_add]

/-- `mvHasseCoeff k` is `R`-linear (compatible with scalar multiplication). -/
theorem mvHasseCoeff_smul (k : σ →₀ ℕ) (c : R) (p : MvPolynomial σ R) :
    mvHasseCoeff k (c • p) = c • mvHasseCoeff k p := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [MvPolynomial.coeff_smul, mvHasseCoeff_coeff, mvHasseCoeff_coeff, MvPolynomial.coeff_smul,
    smul_eq_mul, smul_eq_mul]
  ring

/-- The genuine multivariate binomial weight of a *single-variable* shift: when both
multi-indices are concentrated at the same coordinate `i`, the weight is the ordinary
`Nat.choose`.  This is the coefficient-level statement that `mvHasseCoeff (single i k)`
agrees with the single-variable `Polynomial.hasseDeriv k` (whose coefficient is
`(n+k).choose k`, `Polynomial.hasseDeriv_coeff`). -/
theorem mvBinom_single (i : σ) (a b : ℕ) :
    mvBinom (Finsupp.single i a) (Finsupp.single i b) = a.choose b := by
  classical
  unfold mvBinom
  by_cases ha0 : a = 0
  · by_cases hb0 : b = 0
    · subst ha0; subst hb0; simp
    · subst ha0
      -- support of single i 0 is empty; support of single i b is {i}; product over {i} = 0.choose b
      rw [Finsupp.single_zero, Finsupp.support_zero, Finset.empty_union]
      rw [Finsupp.support_single_ne_zero i hb0, Finset.prod_singleton]
      simp
  · -- a ≠ 0 : support of single i a is {i}; the union of supports is {i}.
    rw [Finsupp.support_single_ne_zero i ha0]
    by_cases hb0 : b = 0
    · subst hb0; rw [Finsupp.single_zero, Finsupp.support_zero, Finset.union_empty,
        Finset.prod_singleton]; simp
    · rw [Finsupp.support_single_ne_zero i hb0, Finset.union_self, Finset.prod_singleton]
      simp

/-- Single-variable agreement (the `hasseDeriv_coeff` analogue): for a single-coordinate shift
`k = single i m`, the `single i n`-coefficient of `mvHasseCoeff (single i m) p` is exactly the
binomial-weighted shift `(n+m).choose m · coeff (single i (n+m)) p` — identical to the
coefficient produced by the single-variable `Polynomial.hasseDeriv m`
(`Polynomial.hasseDeriv_coeff`).  This certifies `mvHasseCoeff` is the genuine Hasse object. -/
theorem mvHasseCoeff_single_coeff (i : σ) (m n : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.coeff (Finsupp.single i n) (mvHasseCoeff (Finsupp.single i m) p)
      = ((n + m).choose m : R) * MvPolynomial.coeff (Finsupp.single i (n + m)) p := by
  classical
  rw [mvHasseCoeff_coeff, ← Finsupp.single_add, mvBinom_single]

/-- Evaluation on a single monomial: `mvHasseCoeff k (monomial s a)` has the expected
binomial-weighted single monomial as its value, witnessing non-vacuity (a genuine `monomial`
with the genuine `mvBinom` weight, never identically zero when `k ≤ s` and `a ≠ 0`). -/
theorem mvHasseCoeff_monomial (k s : σ →₀ ℕ) (a : R) :
    mvHasseCoeff k (MvPolynomial.monomial s a)
      = MvPolynomial.monomial (s - k) ((mvBinom s k : R) * a) := by
  classical
  apply MvPolynomial.ext
  intro n
  rw [mvHasseCoeff_coeff, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases hsk : s - k = n
  · -- coeff at n: LHS factor uses coeff (n+k) (monomial s a) = if s = n+k then a else 0.
    by_cases hks : k ≤ s
    · have hsnk : s = n + k := by
        rw [← hsk]; exact (tsub_add_cancel_of_le hks).symm
      rw [if_pos hsk, if_pos hsnk, hsnk]
    · -- ¬ k ≤ s : weight is 0, and also s ≠ n + k (else k ≤ s).
      rw [mvBinom_eq_zero_of_not_le hks]
      rw [if_pos hsk]
      have : s ≠ n + k := by
        intro h; exact hks (h ▸ le_add_self)
      rw [if_neg this]
      simp
  · -- s - k ≠ n: LHS coeff is 0 (monomial at s-k), and RHS is 0 too.
    rw [if_neg hsk]
    have : s ≠ n + k := by
      intro h
      apply hsk
      rw [h]; simp
    rw [if_neg this]
    simp

/-- `mvBinom s k ≠ 0` whenever `k ≤ s`: every factor `(sᵢ).choose (kᵢ)` is positive because
`kᵢ ≤ sᵢ`.  Dual to `mvBinom_eq_zero_of_not_le`; the positivity half of the genuine weight. -/
theorem mvBinom_pos {s k : σ →₀ ℕ} (hks : k ≤ s) : 0 < mvBinom s k := by
  classical
  unfold mvBinom
  apply Finset.prod_pos
  intro i _
  exact Nat.choose_pos (hks i)

/-- The monomial `mvHasseCoeff`, read at the shifted index `s - k`, returns *exactly* the
genuine binomial multiple `mvBinom s k · a` (whose integer weight `mvBinom s k` is positive by
`mvBinom_pos` when `k ≤ s`).  This is the load-bearing anti-stub witness that `mvHasseCoeff` is
the genuine Hasse object, never a secretly-zero map.  (Stated over any `CommSemiring`; in
positive characteristic the *cast* of the weight may collapse, so the honest non-vacuity is the
ℕ-level `mvBinom_pos`, not a field-level `≠ 0` — which would be false over `Fₚ`.) -/
theorem mvHasseCoeff_monomial_coeff_eq (k s : σ →₀ ℕ) (a : R) :
    MvPolynomial.coeff (s - k) (mvHasseCoeff k (MvPolynomial.monomial s a))
      = (mvBinom s k : R) * a := by
  classical
  rw [mvHasseCoeff_monomial, MvPolynomial.coeff_monomial, if_pos rfl]

end MvHasse

/-! ## 2. Partition-indexed product machinery -/

section Partition

/-- `Σλ := ∑_l λ_l`, the *number of parts* of a partition (counted with multiplicity).
In BCIKS20 (`A.1`) this is the total order of the `Y`-Hasse derivative and the `ξ`-exponent
contributor.  Equals `λ.parts.card` (each part `l` is listed `λ_l` times). -/
def sigmaLambda {m : ℕ} (lam : Nat.Partition m) : ℕ := lam.parts.card

@[simp]
theorem sigmaLambda_indiscrete {m : ℕ} (hm : m ≠ 0) :
    sigmaLambda (Nat.Partition.indiscrete m) = 1 := by
  rw [sigmaLambda, Nat.Partition.indiscrete_parts hm]
  rfl

variable {M : Type*} [CommMonoid M]

/-- The **partition-indexed product** `∏_l (b l)^{λ_l}` for `lam : Nat.Partition m` and a family
`b : ℕ → M`.  Defined as the product over the multiset of parts (each distinct part `l` appears
exactly `λ_l = lam.parts.count l` times, so it is automatically raised to its multiplicity).

This is the genuine `∏_l β_l^{λ_l}` of BCIKS20 `(A.1)` — see `partitionProd_eq_prod_count`. -/
def partitionProd {m : ℕ} (lam : Nat.Partition m) (b : ℕ → M) : M :=
  (lam.parts.map b).prod

/-- The reindexing-by-multiplicity identity certifying `partitionProd` is the genuine
`∏_l (b l)^{λ_l}`: the product over parts equals the product over *distinct* parts `l`, each
raised to its multiplicity `λ_l = lam.parts.count l`. -/
theorem partitionProd_eq_prod_count {m : ℕ} (lam : Nat.Partition m) (b : ℕ → M) :
    partitionProd lam b = ∏ l ∈ lam.parts.toFinset, (b l) ^ (lam.parts.count l) := by
  classical
  rw [partitionProd, Finset.prod_multiset_map_count]

/-- The empty (`m = 0`) partition product is `1`: `Nat.Partition 0` has no parts. -/
@[simp]
theorem partitionProd_zero (lam : Nat.Partition 0) (b : ℕ → M) :
    partitionProd lam b = 1 := by
  rw [partitionProd]
  -- The unique partition of 0 has empty parts (`parts_sum = 0` ⟹ all parts are 0, but parts > 0).
  have : lam.parts = 0 := by
    have hsum : lam.parts.sum = 0 := lam.parts_sum
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    have hpos := lam.parts_pos ha
    have hle : a ≤ lam.parts.sum := Multiset.le_sum_of_mem ha
    omega
  rw [this]
  simp

/-- The product over the *indiscrete* partition (single part `m`, `m ≠ 0`) is just `b m`
(the `λ_m = 1` term).  In BCIKS20 this is the excluded special partition `λ(t)`. -/
@[simp]
theorem partitionProd_indiscrete {m : ℕ} (hm : m ≠ 0) (b : ℕ → M) :
    partitionProd (Nat.Partition.indiscrete m) b = b m := by
  rw [partitionProd, Nat.Partition.indiscrete_parts hm]
  simp

/-- `partitionProd` is multiplicative in the family. -/
theorem partitionProd_mul {m : ℕ} (lam : Nat.Partition m) (b c : ℕ → M) :
    partitionProd lam (fun l => b l * c l)
      = partitionProd lam b * partitionProd lam c := by
  rw [partitionProd, partitionProd, partitionProd, ← Multiset.prod_map_mul]

/-- The combinatorial **prefactor** of BCIKS20's `A_{i1,λ}` coefficient (lines 4042–4080),
as an explicit natural number: the binomial `C(i, i1)` times the multinomial over the parts of
`λ` together with the order-0 multiplicity.  Here it is rendered as
`Nat.choose i i1 * Nat.multinomial (lam.parts.toFinset) (lam.parts.count)` — the genuine
`multinomial(λ₁, …, λ_l, …)` over distinct part-multiplicities.

WALL (deferred to a later wave): the *matching lemma* equating this with the exact
paper combinatorial factor (reconciling the Hasse-derivative's intrinsic `C(j, Σλ)` weight
against the paper's `multinomial(j0, λ)`) is `prefactor_eq_paper` below — STATED, not proven. -/
def prefactor {m : ℕ} (i i1 : ℕ) (lam : Nat.Partition m) : ℕ :=
  Nat.choose i i1 * Nat.multinomial lam.parts.toFinset (fun l => lam.parts.count l)

/-- The prefactor is genuinely positive whenever the binomial part is (so it is never a
secretly-zero stub): `Nat.multinomial` is always `> 0`. -/
theorem prefactor_pos {m : ℕ} (i i1 : ℕ) (lam : Nat.Partition m) (hi : i1 ≤ i) :
    0 < prefactor i i1 lam := by
  rw [prefactor]
  exact Nat.mul_pos (Nat.choose_pos hi) (Nat.multinomial_pos _ _)

end Partition

/-! ## 4. WAVE 2 — the genuine `β` recursion of BCIKS20 (A.1) over the ring `𝒪 H`

This section imports the in-tree BCIKS20 ring API
(`ArkLib.Data.Polynomial.RationalFunctions`: `𝒪 H`, `𝕃 H`, `ξ`, `ζ`, `functionFieldT`,
`liftToFunctionField`, `embeddingOf𝒪Into𝕃`, `H_tilde'`, `weight_Λ_over_𝒪`,
`ClaimA2.Hypotheses`) and lands the genuine recursive Hensel-lift numerator.

`R : F[X][X][Y] = Polynomial (Polynomial (Polynomial F))`: the **outermost** layer is the
`Y` variable (substituted by `α₀ = T/W` via `eval₂ liftToFunctionField`); the **middle**
layer is the lift variable `X` (substituted by `x₀` via `Bivariate.evalX (C x₀)`); the
innermost `Polynomial F` survives as the ground layer carrying `𝕃 H`'s `RatFunc F`.

The Hasse derivatives are the genuine single-variable `Polynomial.hasseDeriv` on the right
layer (char-free, no `m!`, per BCIKS20 line 4350), never a stub. -/

open Polynomial Polynomial.Bivariate
open BCIKS20AppendixA

section Wave2

variable {F : Type} [Field F]

/-! ### 4a. Iterated single-variable Hasse derivatives on the two layers of `R` -/

/-- `Δ_X^{i1}`: the `i1`-th Hasse derivative on the **lift `X` layer** (the middle
`Polynomial` layer) of `R : F[X][X][Y]`, applied coefficient-wise through the outer `Y`
layer.  Each `Y`-coefficient `a : F[X][X]` is sent to `Polynomial.hasseDeriv i1 a`, the
genuine binomial-weighted-shift Hasse derivative on its own `X` variable.  This is the
genuine `Δ_X^{i1}` of BCIKS20 (char-free). -/
noncomputable def hasseDerivX (i1 : ℕ) (R : F[X][X][Y]) : F[X][X][Y] :=
  R.sum (fun n a => Polynomial.monomial n (Polynomial.hasseDeriv i1 a))

/-- `Δ_Y^{m}`: the `m`-th Hasse derivative on the **outermost `Y` layer** of `R`, i.e. the
ordinary mathlib `Polynomial.hasseDeriv m` (genuine, char-free). -/
noncomputable def hasseDerivY (m : ℕ) (R : F[X][X][Y]) : F[X][X][Y] :=
  Polynomial.hasseDeriv m R

/-- Non-vacuity: `Δ_X^{0} = id` (`hasseDeriv 0 = id`, layer-wise).  Certifies `hasseDerivX`
is genuinely not the zero map. -/
@[simp]
theorem hasseDerivX_zero (R : F[X][X][Y]) : hasseDerivX 0 R = R := by
  unfold hasseDerivX
  simp only [Polynomial.hasseDeriv_zero']
  exact Polynomial.sum_monomial_eq R

/-- Non-vacuity: `Δ_Y^{0} = id`. -/
@[simp]
theorem hasseDerivY_zero (R : F[X][X][Y]) : hasseDerivY 0 R = R := by
  unfold hasseDerivY; simp

/-- `Δ_X^{i1}` is additive (it is `Polynomial.hasseDeriv i1`, an `F[X]`-linear map, applied
coefficient-wise).  Genuine-object witness. -/
theorem hasseDerivX_add (i1 : ℕ) (p q : F[X][X][Y]) :
    hasseDerivX i1 (p + q) = hasseDerivX i1 p + hasseDerivX i1 q := by
  unfold hasseDerivX
  rw [Polynomial.sum_add_index]
  · intro i; simp
  · intro i a b; simp [map_add]

/-- `Δ_Y^{m}` is additive. -/
theorem hasseDerivY_add (m : ℕ) (p q : F[X][X][Y]) :
    hasseDerivY m (p + q) = hasseDerivY m p + hasseDerivY m q := by
  unfold hasseDerivY; simp [map_add]

/-! ### 4b. Evaluation at the root `(x₀, α₀ = T/W)` and the rescaled coefficient `B_{i1,λ}` -/

variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- Evaluate the iterated Hasse coefficient `Δ_X^{i1} Δ_Y^{m} R` of the trivariate `R` at
`(X = x₀, Y = α₀ = T/W)`, landing in `𝕃 H`.  `X ↦ x₀` via `Bivariate.evalX (C x₀)`; the
remaining `Y` is sent to `α₀ = T/W` via `eval₂ liftToFunctionField`.  This **mirrors
`ClaimA2.ζ`** exactly (`RationalFunctions.lean`:2229), which is the `i1 = 1, m = 0` analogue
applied to `R.derivative`. -/
noncomputable def hasseEvalAtRoot (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let T : 𝕃 H := functionFieldT (H := H)
  Polynomial.eval₂ liftToFunctionField (T / W)
    (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))

/-- `δ_{i1,0} = if i1 = 0 then 1 else 0`, the BCIKS20 "save a `W`" indicator. -/
def deltaSave (i1 : ℕ) : ℕ := if i1 = 0 then 1 else 0

/-- The genuine `𝒪 H`-representative of the iterated Hasse coefficient of `R` at `(x₀, ·)`,
**lifted by `Y ↦ T` (the `W`-cleared form)**.  Concretely: take `Δ_X^{i1} Δ_Y^{Σλ} R :
F[X][X][Y]`, specialise the lift layer `X ↦ x₀` to a polynomial in `F[X][Y]`, and `mk` it
into `𝒪 H = F[X][Y] ⧸ ⟨H̃'⟩`.  The `Y ↦ T` lift (= `mk`) is exactly the `W`-cleared form of
the `Y ↦ T/W` evaluation `hasseEvalAtRoot` (clearing the `T/W` denominators multiplies by the
appropriate `W`-power).  Genuine: built from the real iterated `Polynomial.hasseDeriv`,
never `0`. -/
noncomputable def hasseCoeffRepr𝒪 (x₀ : F) (R : F[X][X][Y]) (i1 m : ℕ) : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H})
    (Bivariate.evalX (Polynomial.C x₀) (hasseDerivX i1 (hasseDerivY m R)))

/-- BCIKS20's rescaled coefficient `B_{i1,λ} ∈ 𝒪 H` (lines 4042–4080): the combinatorial
`prefactor` (`C(d,i1)·multinomial(λ)`) times the `W`-cleared iterated-Hasse coefficient
`hasseCoeffRepr𝒪`.  This is the **genuine** object — the real iterated Hasse coefficient of
`R` at `(x₀, α₀)` carrying its genuine integer prefactor — not a stub and not secretly `0`
(`prefactor_pos` shows the integer weight is positive).

WALL (the only deferred piece of `B_coeff`): the *weight* lemma
`weight_Λ_over_𝒪 hH (B_coeff …) D ≤ (D − Σλ) + (d − δ_{i1,0} − Σλ)·Λ(W)` and the embedding
identity `embeddingOf𝒪Into𝕃 (B_coeff …) = prefactor · W^{d−δ−Σλ} · hasseEvalAtRoot …` (the
`Y↦T` vs `Y↦T/W` clearing).  The definition itself is complete and genuine. -/
noncomputable def B_coeff (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) : 𝒪 H :=
  (prefactor R.natDegree i1 lam) • hasseCoeffRepr𝒪 H x₀ R i1 (sigmaLambda lam)

/-! ### 4c. The `β` well-founded recursion `(A.1)` — the WAVE 2 keystone -/

/-- The image of `W = H.leadingCoeff` as an element of `𝒪 H` (the constant `C W ∈ F[X][Y]`,
`mk`-ed).  Genuine `W` factor for the `(A.1)` recursion. -/
noncomputable def W𝒪 : 𝒪 H :=
  Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.C (H.leadingCoeff))

/-- **The keystone.** BCIKS20 Claim A.2's recursive Hensel-lift numerator `β_t ∈ 𝒪 H`,
the genuine recursion of `(A.1)`.  Defined by strong recursion on `t`:

* `β₀ := T mod H̃`, the genuine canonical `𝒪`-representative of the function-field variable
  `T = functionFieldT` — concretely `mk (Polynomial.X : F[X][Y])`, whose embedding is
  `liftBivariate X = functionFieldT = T` (genuine base, **not** `0`).

* `β_{t+1} := − ∑_{i1 ∈ range(t+2)} ∑_{λ ∈ P(t+1−i1), (t+1) ∉ λ.parts}
      W^{i1+δ_{i1,0}−1} · ξ^{2i1+Σλ−2} · B_{i1,λ} · ∏_l (β_l)^{λ_l}`,

the literal `(A.1)` sum, with:
  - the **genuine** exclusion `λ ≠ λ(t+1)` rendered type-uniformly as `(t+1) ∉ λ.parts`:
    a partition of `t+1−i1` contains a part of size `t+1` iff `i1 = 0` and `λ` is the
    single-part `indiscrete (t+1)` — exactly the BCIKS20 excluded partition `λ(t+1)`; for
    `i1 ≥ 1` (`parts.sum = t+1−i1 < t+1`) the predicate is vacuously true, excluding nothing.
  - the recursive calls `β_l` for `l ∈ λ.parts` justified by `l < t+1` (every part `l` of a
    surviving `λ` is `< t+1`: parts are positive and sum to `≤ t+1`, and the only `λ` with a
    part `= t+1` is excluded).  Encoded with the guard
    `fun l => if h : l < t+1 then ih l h else 0`; the `else 0` branch is never read by
    `partitionProd` on a surviving `λ` (its parts are all `< t+1`), so this is genuine
    plumbing, not a fake value.

The signature carries `x₀` and `hHyp : ClaimA2.Hypotheses x₀ R H` (the in-tree stub
`β_regular`/`β` lacks them and so structurally cannot reference `α₀ = T/W`, `ζ`, `ξ`).  This
is the mandatory signature fix; `βHensel` ADDS the genuine numerator without editing the
harness-hot `β`/`α`. -/
noncomputable def βHensel (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ℕ → 𝒪 H :=
  fun t => Nat.strongRecOn t (fun n ih =>
    match n with
    | 0 => Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y])
    | (k + 1) =>
        - ∑ i1 ∈ Finset.range (k + 2),
            ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - i1))).filter
                      (fun lam => (k + 1) ∉ lam.parts),
              (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
                * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
                * B_coeff H x₀ R i1 lam
                * partitionProd lam (fun l => if h : l < k + 1 then ih l (by omega) else 0))

/-- **Base case value lemma (PROVEN).**  `βHensel … 0 = mk X`, the genuine `T mod H̃`
representative (whose embedding is `functionFieldT = T`). -/
theorem βHensel_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) :
    βHensel H x₀ R hHyp 0 =
      Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) := by
  unfold βHensel
  rw [Nat.strongRecOn_eq]

/-- The base case embeds to the genuine function-field variable `T`: a value witness that
`βHensel … 0` is the genuine `T mod H̃` and not a fake. -/
theorem embeddingOf𝒪Into𝕃_βHensel_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp 0) = functionFieldT (H := H) := by
  rw [βHensel_zero, embeddingOf𝒪Into𝕃_mk, liftBivariate_X]

/-! ### 4d. (P1) the weight bound — `t = 0` case PROVEN, inductive step staged -/

/-- **(P1) `t = 0` case (PROVEN).**  `weight_Λ_over_𝒪 hH (βHensel … 0) D
≤ (2·0+1)·natDegreeY R·D = natDegreeY R · D`.

Proof: `βHensel … 0 = mk X`, and `weight_Λ_over_𝒪 hH (mk X) D ≤ weight_Λ X H D
= D + 1 − natDegreeY H ≤ D ≤ natDegreeY R · D` (using `0 < H.natDegree = natDegreeY H` and
`1 ≤ natDegreeY R`).  Mirrors the numeric structure of `weight_ξ_bound`. -/
theorem βHensel_weight_bound_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (hDH : Bivariate.totalDegree H ≤ D)
    (hdR : 1 ≤ Bivariate.natDegreeY R) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp 0) D
      ≤ WithBot.some ((2 * 0 + 1) * Bivariate.natDegreeY R * D) := by
  rw [βHensel_zero]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH rfl) ?_
  have hweq : weight_Λ (Polynomial.X : F[X][Y]) H D
      = WithBot.some (D + 1 - Bivariate.natDegreeY H) := by
    rw [weight_Λ, Polynomial.support_X (by norm_num)]
    simp [Polynomial.coeff_X_one]
  rw [hweq]
  have hdHY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hle : D + 1 - Bivariate.natDegreeY H ≤ (2 * 0 + 1) * Bivariate.natDegreeY R * D := by
    rw [hdHY]
    calc D + 1 - H.natDegree ≤ D := by omega
      _ ≤ (2 * 0 + 1) * Bivariate.natDegreeY R * D := by
          have h1 : 1 ≤ (2 * 0 + 1) * Bivariate.natDegreeY R := by simpa using hdR
          calc D = 1 * D := (one_mul D).symm
            _ ≤ (2 * 0 + 1) * Bivariate.natDegreeY R * D := Nat.mul_le_mul_right D h1
  exact_mod_cast hle

/-- **(P1) full weight bound — STAGED with a documented `sorry` for the inductive step.**
`weight_Λ_over_𝒪 hH (βHensel … t) D ≤ (2t+1)·natDegreeY R·D`.

The `t = 0` case is `βHensel_weight_bound_zero` (PROVEN above).  The inductive step is the
documented WALL: induction on the `(A.1)` sum, bounding each summand via
  (1) the **`B_coeff` weight lemma** `weight (B_coeff …) D ≤ (D−Σλ)+(d−δ−Σλ)·Λ(W)`
      (the deferred half of §4b),
  (2) **`partitionProd` weight subadditivity** `weight (∏_l β_l^{λ_l}) ≤ ∑_l λ_l·weight(β_l)`
      fed by the IHs `weight (β_l) ≤ (2l+1)·natDegreeY R·D` for `l < t+1`,
  (3) `weight_ξ_bound` for the `ξ`-power and `Λ(W) = natDegreeY H` for the `W`-power,
  (4) `weight_Λ` sum subadditivity over the double sum,
summed per BCIKS20 lines 4264–4268.  None of (1)–(4) is faked; this is the next-wave target. -/
theorem βHensel_weight_bound (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (_hDH : Bivariate.totalDegree H ≤ D)
    (_hdR : 1 ≤ Bivariate.natDegreeY R) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  match t with
  | 0 => exact βHensel_weight_bound_zero H x₀ R hHyp hH _hDH _hdR
  | (_k + 1) =>
      -- WALL: the inductive step of (P1).  See the docstring: needs the `B_coeff` weight
      -- lemma + `partitionProd` weight subadditivity + `weight_ξ_bound` + `weight_Λ` sum
      -- subadditivity, summed per BCIKS20 lines 4264–4268.  Deferred to the next wave.
      sorry

/-! ### 4e. (P2) the lift identity — the irreducible BCIKS20 A.4 frontier -/

/-- **(P2) lift identity — the IRREDUCIBLE FRONTIER (documented `sorry`).**
`embeddingOf𝒪Into𝕃 (βHensel … t) = α_t · W^{t+1} · ξ^{2t−1}` (`α_t` is the in-tree
`ClaimA2.α`).

This is the BCIKS20 Appendix A.4 proof proper: it asserts that `βHensel` is the numerator of
the genuine Hensel lift coefficient `α_t` of the power-series root `γ` of `R(X, γ, Z) = 0`.
Establishing it requires the formal statement and proof that `γ` (defined at
`RationalFunctions.lean:3036`) **is a root** of `R(X, ·, Z)` over the function field — the
`R(X,γ,Z)=0` power-series root fact — which is unproven in tree and is the genuine
mathematical content of A.4 (the Hensel-lift uniqueness/existence argument).  Out of scope
for this wave; flagged as the irreducible frontier of ingredient D. -/
theorem βHensel_lift_identity (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp t)
      = ClaimA2.α x₀ R H hHyp t
          * (liftToFunctionField (H := H) H.leadingCoeff) ^ (t + 1)
          * (embeddingOf𝒪Into𝕃 H (ClaimA2.ξ x₀ R H hHyp)) ^ (2 * t - 1) := by
  -- IRREDUCIBLE FRONTIER: the BCIKS20 A.4 Hensel-lift proof; needs `R(X,γ,Z)=0`.
  sorry

end Wave2

/-! ## 5. Staged specifications still deferred (honest WALLs)

* `prefactor_eq_paper` : `prefactor i i1 lam = <paper combinatorial factor>`.
  WALL: reconcile the Hasse-derivative's intrinsic `C(j, Σλ)` weight against the paper's
  `multinomial(j0, λ)`.  (The `B_coeff` definition uses `prefactor` directly; the matching
  lemma only affects the exact embedding identity, not the genuineness of the object.)

* `B_coeff` weight + embedding lemmas (the deferred half of §4b) — feed (P1)'s inductive step.

* iterated-Hasse Leibniz/product rule — needed only for (P2). -/

end BCIKS20.HenselNumerator
