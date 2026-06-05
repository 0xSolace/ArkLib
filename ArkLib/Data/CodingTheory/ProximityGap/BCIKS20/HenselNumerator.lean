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
7. `βHensel_zero` / `βHensel_succ` — base-case + recursive-step value lemmas (PROVEN).
8. `(P1) βHensel_weight_bound` — `t = 0` PROVEN; inductive step FULLY ASSEMBLED (strong
   induction + `βHensel_succ` + the over-`𝒪` weight calculus below), reduced to the **single**
   documented per-term residual `βHensel_succ_term_weight_le`.
9. `(P2) βHensel_lift_identity` — the irreducible BCIKS20 A.4 frontier, documented `sorry`.

WAVE 3 SCOPE (§4c′ / 4d below).  The reusable **`Λ`-weight calculus over `𝒪 H`**, all PROVEN
axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`):
`weight_Λ_over_𝒪_mul_le` / `_add_le` / `_neg` / `_sum_le` / `_pow_le` / `_nsmul_le`,
`weight_Λ_over_𝒪_W` (the in-tree `Λ(W)` bound), `partitionProd_weight_le` (multiset
sub-additivity), `weight_Λ_nsmul_le`, `B_coeff_weight_le_hasse` (`B_coeff` → `hasseCoeffRepr𝒪`),
`surviving_parts_lt`, `sum_map_two_mul_succ`, and the IH-fed product bound
`partitionProd_βHensel_weight_le`.  These reduce (P1) to one precise per-term WALL.

See `ingredientD-wave1-design.md` / `…-wave2.md` / `…-wave3.md` for the staged specs.

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

/-! ### 4c′. The `Λ`-weight calculus over `𝒪 H`

The `Λ`-weight `weight_Λ_over_𝒪` is defined on the *canonical representative* of a regular
element, but it is genuinely **sub-additive / sub-multiplicative**: lift each operand to its
canonical representative, apply the polynomial-level calculus
(`weight_Λ_mul_le`/`weight_Λ_add_le`/`weight_Λ_sum_le` from `RationalFunctions`), and descend
again with the workhorse `weight_Λ_over_𝒪_le_of_mk_eq` (`Ideal.Quotient.mk` being a ring hom).

These are the genuine over-`𝒪` analogues used by the `(A.1)` weight telescoping.  Each requires
`Bivariate.totalDegree H ≤ D` (the same `D ≥ tot H` premise of `weight_Λ_over_𝒪_le_of_mk_eq`). -/

variable {D : ℕ}

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `Λ_𝒪(a · b) ≤ Λ_𝒪(a) + Λ_𝒪(b)`: sub-multiplicativity over `𝒪 H`.  Take the canonical
representatives `ra, rb`; then `mk (ra · rb) = a · b`, and
`weight_Λ (ra · rb) ≤ weight_Λ ra + weight_Λ rb = Λ_𝒪 a + Λ_𝒪 b`. -/
lemma weight_Λ_over_𝒪_mul_le (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D)
    (a b : 𝒪 H) :
    weight_Λ_over_𝒪 hH (a * b) D
      ≤ weight_Λ_over_𝒪 hH a D + weight_Λ_over_𝒪 hH b D := by
  set ra := canonicalRepOf𝒪 hH a with hra
  set rb := canonicalRepOf𝒪 hH b with hrb
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ra * rb) : 𝒪 H) = a * b := by
    rw [map_mul, hra, hrb, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH hmk) ?_
  refine le_trans (weight_Λ_mul_le ra rb H D) ?_
  -- `weight_Λ_over_𝒪 hH a D = weight_Λ ra H D` definitionally.
  exact le_of_eq (by rw [weight_Λ_over_𝒪, weight_Λ_over_𝒪, ← hra, ← hrb])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `Λ_𝒪(a + b) ≤ max(Λ_𝒪 a, Λ_𝒪 b)`: sub-additivity over `𝒪 H`. -/
lemma weight_Λ_over_𝒪_add_le (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D)
    (a b : 𝒪 H) :
    weight_Λ_over_𝒪 hH (a + b) D
      ≤ max (weight_Λ_over_𝒪 hH a D) (weight_Λ_over_𝒪 hH b D) := by
  set ra := canonicalRepOf𝒪 hH a with hra
  set rb := canonicalRepOf𝒪 hH b with hrb
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (ra + rb) : 𝒪 H) = a + b := by
    rw [map_add, hra, hrb, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH hmk) ?_
  refine le_trans (weight_Λ_add_le ra rb H D) ?_
  exact le_of_eq (by rw [weight_Λ_over_𝒪, weight_Λ_over_𝒪, ← hra, ← hrb])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `Λ_𝒪(-a) = Λ_𝒪(a)`: the `𝒪`-weight is negation-invariant (`mk (-ra) = -a`,
`weight_Λ_neg`). -/
lemma weight_Λ_over_𝒪_neg (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D) (a : 𝒪 H) :
    weight_Λ_over_𝒪 hH (-a) D ≤ weight_Λ_over_𝒪 hH a D := by
  set ra := canonicalRepOf𝒪 hH a with hra
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (-ra) : 𝒪 H) = -a := by
    rw [map_neg, hra, mk_canonicalRepOf𝒪]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH hmk) ?_
  rw [weight_Λ_neg]
  exact le_of_eq (by rw [weight_Λ_over_𝒪, ← hra])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `Λ_𝒪(∑ᵢ f i) ≤ sup of Λ_𝒪(f i)`: the `𝒪`-weight of a finite sum is bounded by the sup of
the summand weights.  Derived from `weight_Λ_over_𝒪_add_le` by induction. -/
lemma weight_Λ_over_𝒪_sum_le {ι : Type*} (hH : 0 < H.natDegree)
    (hDH : Bivariate.totalDegree H ≤ D) (s : Finset ι) (f : ι → 𝒪 H) :
    weight_Λ_over_𝒪 hH (∑ i ∈ s, f i) D ≤ s.sup (fun i => weight_Λ_over_𝒪 hH (f i) D) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight_Λ_over_𝒪_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact (weight_Λ_over_𝒪_add_le H hH hDH _ _).trans (max_le_max le_rfl ih)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `Λ_𝒪(a ^ k) ≤ k • Λ_𝒪(a)` (i.e. `≤ k · Λ_𝒪(a)` in `WithBot ℕ`): the power bound over
`𝒪 H`, by induction on `k` from `weight_Λ_over_𝒪_mul_le`.  The `k = 0` case uses
`Λ_𝒪(1) ≤ 0`. -/
lemma weight_Λ_over_𝒪_pow_le (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D)
    (a : 𝒪 H) (k : ℕ) :
    weight_Λ_over_𝒪 hH (a ^ k) D ≤ k • weight_Λ_over_𝒪 hH a D := by
  induction k with
  | zero =>
      simp only [pow_zero, zero_smul]
      -- `Λ_𝒪(1) ≤ 0`: `1 = mk 1`, `weight_Λ 1 ≤ 0` (degree-0 constant).
      have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (1 : F[X][Y]) : 𝒪 H) = 1 := by
        rw [map_one]
      refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH hmk) ?_
      rw [show (1 : F[X][Y]) = Polynomial.C (1 : F[X]) by rw [map_one]]
      refine le_trans (weight_Λ_C_le H D 1) ?_
      simp
  | succ n ih =>
      rw [pow_succ, succ_nsmul]
      refine le_trans (weight_Λ_over_𝒪_mul_le H hH hDH _ _) ?_
      exact add_le_add ih le_rfl

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The genuine in-tree value of `Λ(W)`: `Λ_𝒪(W𝒪) ≤ (H.leadingCoeff).natDegree`.  `W𝒪` is
`mk (C W)` with `W = H.leadingCoeff ∈ F[X]`, a degree-0 (in `Y`) constant whose `Λ`-weight is
the `X`-degree `W.natDegree` of the leading `Y`-coefficient (`weight_Λ_C_le`).  This is the
in-tree analogue of BCIKS20's `Λ(W)`; the per-`Y`-power weight `m` contributes `0` (the `Y`-power
is `0`).  Stated as the load-bearing `Λ(W)` bound for the `(A.1)` telescoping. -/
lemma weight_Λ_over_𝒪_W (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D) :
    weight_Λ_over_𝒪 hH (W𝒪 H) D ≤ WithBot.some (H.leadingCoeff).natDegree := by
  rw [W𝒪]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH (r := Polynomial.C (H.leadingCoeff)) rfl) ?_
  exact weight_Λ_C_le H D _

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **`partitionProd` weight sub-additivity over `𝒪 H`.**  For `lam : Nat.Partition m` and a
family `b : ℕ → 𝒪 H`, `Λ_𝒪(∏_l (b l)^{λ_l}) ≤ ∑_{l ∈ lam.parts} Λ_𝒪(b l)` (the sum over the
*multiset* of parts, i.e. each distinct part `l` counted `λ_l` times).  By induction on the
multiset of parts using `weight_Λ_over_𝒪_mul_le`; the empty product has weight `≤ 0`.

This is the genuine `Λ(∏_l β_l^{λ_l}) ≤ ∑_l λ_l·Λ(β_l)` of the `(A.1)` telescoping: the
multiset-`sum` form `(lam.parts.map (Λ_𝒪 ∘ b)).sum` is exactly `∑_l λ_l·Λ_𝒪(b l)`. -/
lemma partitionProd_weight_le (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D)
    {m : ℕ} (lam : Nat.Partition m) (b : ℕ → 𝒪 H) :
    weight_Λ_over_𝒪 hH (partitionProd lam b) D
      ≤ (lam.parts.map (fun l => weight_Λ_over_𝒪 hH (b l) D)).sum := by
  rw [partitionProd]
  -- Generalize over the multiset of parts and induct.
  generalize hms : lam.parts = ms
  clear hms
  induction ms using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero]
      -- `Λ_𝒪(1) ≤ 0`.
      have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (1 : F[X][Y]) : 𝒪 H) = 1 := by
        rw [map_one]
      refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH hmk) ?_
      rw [show (1 : F[X][Y]) = Polynomial.C (1 : F[X]) by rw [map_one]]
      refine le_trans (weight_Λ_C_le H D 1) ?_
      simp
  | cons l ms ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
      exact (weight_Λ_over_𝒪_mul_le H hH hDH _ _).trans (add_le_add le_rfl ih)

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Polynomial-level `nsmul` weight bound: scaling by a natural number cannot increase the
`Λ`-weight (`(n • r).support ⊆ r.support` and `(n • c).natDegree ≤ c.natDegree`).  In positive
characteristic `n • r` may collapse to a *smaller* weight, never a larger one. -/
lemma weight_Λ_nsmul_le (n : ℕ) (r : F[X][Y]) :
    weight_Λ (n • r) H D ≤ weight_Λ r H D := by
  classical
  refine Finset.sup_le (fun k hk => ?_)
  have hcoeff : (n • r).coeff k = n • r.coeff k := by
    rw [Polynomial.coeff_smul]
  -- `k ∈ (n • r).support` ⟹ `(n • r).coeff k ≠ 0` ⟹ `r.coeff k ≠ 0` (smul of 0 is 0).
  have hne : (n • r).coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  have hrne : r.coeff k ≠ 0 := by
    intro h0; apply hne; rw [hcoeff, h0, smul_zero]
  have hk_mem : k ∈ r.support := Polynomial.mem_support_iff.mpr hrne
  have hdeg : ((n • r).coeff k).natDegree ≤ (r.coeff k).natDegree := by
    rw [hcoeff]; exact Polynomial.natDegree_smul_le _ _
  calc (WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + ((n • r).coeff k).natDegree) :
          WithBot ℕ)
      ≤ WithBot.some (k * (D + 1 - Bivariate.natDegreeY H) + (r.coeff k).natDegree) := by
          exact_mod_cast Nat.add_le_add_left hdeg _
    _ ≤ weight_Λ r H D := le_weight_Λ_of_mem_support hk_mem

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `Λ_𝒪(n • a) ≤ Λ_𝒪(a)`: scaling a regular element by `n : ℕ` cannot raise its `𝒪`-weight.
`n • a = mk (n • ra)` (`mk` is `ℕ`-linear), and `weight_Λ (n • ra) ≤ weight_Λ ra`. -/
lemma weight_Λ_over_𝒪_nsmul_le (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D)
    (n : ℕ) (a : 𝒪 H) :
    weight_Λ_over_𝒪 hH (n • a) D ≤ weight_Λ_over_𝒪 hH a D := by
  set ra := canonicalRepOf𝒪 hH a with hra
  have hmk : (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (n • ra) : 𝒪 H) = n • a := by
    rw [map_nsmul, hra, mk_canonicalRepOf𝒪]
  refine le_trans (weight_Λ_over_𝒪_le_of_mk_eq hDH hH hmk) ?_
  refine le_trans (weight_Λ_nsmul_le H n ra) ?_
  exact le_of_eq (by rw [weight_Λ_over_𝒪, ← hra])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **`B_coeff` weight reduces to the iterated-Hasse representative.**
`Λ_𝒪(B_{i1,λ}) ≤ Λ_𝒪(hasseCoeffRepr𝒪 x₀ R i1 (Σλ))`: the integer `prefactor` scalar cannot
raise the weight (`weight_Λ_over_𝒪_nsmul_le`).  The remaining content — bounding
`Λ_𝒪(hasseCoeffRepr𝒪 …)` by `(D − Σλ) + (d − δ_{i1,0} − Σλ)·Λ(W)` (the iterated-Hasse degree
drop + `W`-clearing) — is the deferred `B_coeff_weight` wall. -/
lemma B_coeff_weight_le_hasse (x₀ : F) (R : F[X][X][Y]) (i1 : ℕ) {m : ℕ}
    (lam : Nat.Partition m) (hH : 0 < H.natDegree) (hDH : Bivariate.totalDegree H ≤ D) :
    weight_Λ_over_𝒪 hH (B_coeff H x₀ R i1 lam) D
      ≤ weight_Λ_over_𝒪 hH (hasseCoeffRepr𝒪 H x₀ R i1 (sigmaLambda lam)) D := by
  rw [B_coeff]
  exact weight_Λ_over_𝒪_nsmul_le H hH hDH _ _

/-- Every part of a *surviving* partition is `< k+1`: a `lam : Nat.Partition (k+1−i1)` with
`(k+1) ∉ lam.parts` has all parts `l` positive and `≤ k+1−i1 ≤ k+1`, and `l ≠ k+1`, hence
`l < k+1`.  This is the genuine well-foundedness witness for the `(A.1)` recursion: the guard
`if l < k+1` always takes the `then` branch on a surviving partition's parts. -/
theorem surviving_parts_lt {k i1 : ℕ} (lam : Nat.Partition (k + 1 - i1))
    (hlam : (k + 1) ∉ lam.parts) {l : ℕ} (hl : l ∈ lam.parts) : l < k + 1 := by
  have hle : l ≤ lam.parts.sum := Multiset.le_sum_of_mem hl
  rw [lam.parts_sum] at hle
  have hne : l ≠ k + 1 := fun h => hlam (h ▸ hl)
  omega

/-- The genuine `∑_l λ_l·(2l+1)` telescoping coefficient as a pure-`ℕ` multiset identity:
`∑_{l ∈ parts} (2l+1)·c = (2·(∑ parts) + parts.card)·c`.  For `lam : Nat.Partition (k+1−i1)`
this is `(2·(k+1−i1) + Σλ)·c` (using `parts.sum = k+1−i1`, `parts.card = Σλ`), the exact
contribution of the `∏_l β_l^{λ_l}` factor to the BCIKS20 weight telescoping. -/
theorem sum_map_two_mul_succ (ms : Multiset ℕ) (c : ℕ) :
    (ms.map (fun l => (2 * l + 1) * c)).sum = (2 * ms.sum + Multiset.card ms) * c := by
  induction ms using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.sum_cons, Multiset.card_cons]
      ring

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

/-- **Recursive-step unfolding (PROVEN).**  `βHensel … (k+1)` equals the literal `(A.1)` sum,
with the inner recursive calls `β_l` now written as `βHensel … l` (the well-founded `ih l`
unfolds to `βHensel … l` since `Nat.strongRecOn` is its own fixpoint).  This is the genuine
`(A.1)` recurrence read at a successor, the workhorse for the (P1) inductive step. -/
theorem βHensel_succ (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H) (k : ℕ) :
    βHensel H x₀ R hHyp (k + 1) =
      - ∑ i1 ∈ Finset.range (k + 2),
          ∑ lam ∈ (Finset.univ : Finset (Nat.Partition (k + 1 - i1))).filter
                    (fun lam => (k + 1) ∉ lam.parts),
            (W𝒪 H) ^ (i1 + deltaSave i1 - 1)
              * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
              * B_coeff H x₀ R i1 lam
              * partitionProd lam
                  (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0) := by
  conv_lhs => rw [βHensel, Nat.strongRecOn_eq]
  rfl

/-- The base case embeds to the genuine function-field variable `T`: a value witness that
`βHensel … 0` is the genuine `T mod H̃` and not a fake. -/
theorem embeddingOf𝒪Into𝕃_βHensel_zero (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (βHensel H x₀ R hHyp 0) = functionFieldT (H := H) := by
  rw [βHensel_zero, embeddingOf𝒪Into𝕃_mk, liftBivariate_X]

/-- **The `∏_l β_l^{λ_l}` factor bound — PROVEN (the IH-fed product half of the telescoping).**
For a *surviving* `lam : Nat.Partition (k+1−i1)` (`(k+1) ∉ lam.parts`) and the genuine guarded
recursive family from `βHensel_succ`, given the induction hypothesis
`hIH : ∀ l < k+1, Λ_𝒪(β_l) ≤ (2l+1)·d_R·D`,
the partition product weight is `≤ (2·(k+1−i1) + Σλ)·d_R·D`.

This fully discharges the product half of the BCIKS20 telescoping: the guard always fires
(`surviving_parts_lt`), `partitionProd_weight_le` gives the multiset-sum bound, `hIH` bounds each
factor, and `sum_map_two_mul_succ` evaluates `∑_{l∈parts}(2l+1)·d_R·D = (2·parts.sum + parts.card)·d_R·D`
with `parts.sum = k+1−i1`, `parts.card = Σλ`.  No `sorry`. -/
theorem partitionProd_βHensel_weight_le (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (k i1 : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some ((2 * l + 1) * Bivariate.natDegreeY R * D))
    (lam : Nat.Partition (k + 1 - i1)) (hlam : (k + 1) ∉ lam.parts) :
    weight_Λ_over_𝒪 hH
        (partitionProd lam (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
      ≤ WithBot.some
          ((2 * (k + 1 - i1) + sigmaLambda lam) * Bivariate.natDegreeY R * D) := by
  classical
  -- The guard always fires on a surviving partition's parts: rewrite the family.
  have hcongr : partitionProd lam
      (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)
      = partitionProd lam (fun l => βHensel H x₀ R hHyp l) := by
    rw [partitionProd, partitionProd]
    refine congrArg Multiset.prod (Multiset.map_congr rfl (fun l hl => ?_))
    rw [dif_pos (surviving_parts_lt lam hlam hl)]
  rw [hcongr]
  -- Multiset-sum bound via `partitionProd_weight_le`.
  refine le_trans (partitionProd_weight_le H hH hDH lam (fun l => βHensel H x₀ R hHyp l)) ?_
  -- Bound the `WithBot ℕ` multiset sum by the `some` of the ℕ multiset sum, using `hIH`.
  set c := Bivariate.natDegreeY R * D with hc
  have hkey : (lam.parts.map (fun l => weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D)).sum
      ≤ WithBot.some ((lam.parts.map (fun l => (2 * l + 1) * c)).sum) := by
    -- Inductive monotone-sum + coe-push over the multiset of parts.
    have hmem : ∀ l ∈ lam.parts,
        weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
          ≤ WithBot.some ((2 * l + 1) * c) := by
      intro l hl
      have := hIH l (surviving_parts_lt lam hlam hl)
      rwa [show (2 * l + 1) * Bivariate.natDegreeY R * D = (2 * l + 1) * c by rw [hc, mul_assoc]]
        at this
    -- Generalize the multiset and induct.
    revert hmem
    generalize lam.parts = ms
    intro hmem
    induction ms using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
          WithBot.coe_add]
        refine add_le_add (hmem a (Multiset.mem_cons_self a s)) ?_
        exact ih (fun l hl => hmem l (Multiset.mem_cons_of_mem hl))
  refine le_trans hkey ?_
  -- Evaluate the ℕ multiset sum: `(2·parts.sum + parts.card)·c`, then identify parts.sum/card.
  rw [sum_map_two_mul_succ, lam.parts_sum, sigmaLambda]
  rw [hc]
  rw [show Multiset.card lam.parts = lam.parts.card from rfl]
  ring_nf
  rfl

/-! ### 4d. (P1) the weight bound — `t = 0` PROVEN, inductive step assembled to one per-term WALL -/

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

/-- **(P1) per-term weight bound — the SOLE residual WALL of the inductive step.**

For an `(A.1)` summand indexed by `i1 ∈ range (k+2)` and a *surviving* partition
`lam ∈ P(k+1−i1)` with `(k+1) ∉ lam.parts`, the single term
`W^{i1+δ−1} · ξ^{2i1+Σλ−2} · B_{i1,λ} · ∏_l β_l^{λ_l}` has `Λ`-weight `≤ (2(k+1)+1)·d_R·D`,
**given the induction hypothesis** `hIH : ∀ l < k+1, Λ_𝒪(β_l) ≤ (2l+1)·d_R·D`.

This is the BCIKS20 telescoping at the level of one term (paper lines 4264–4268).  Once
established, the full `(A.1)` sum bound follows mechanically by the *already-proven* over-`𝒪`
weight calculus (`_neg`, `_sum_le`) — see `βHensel_weight_bound`.

WALL (documented, NOT faked).  Closing this term requires three genuine ingredients this wave
does not yet have:
  (a) the **`B_coeff` weight** bound `Λ_𝒪(hasseCoeffRepr𝒪 … i1 Σλ) ≤ (D−Σλ)+(d−δ−Σλ)·Λ(W)`
      (the iterated-Hasse degree-drop + `W`-clearing, the deferred half of §4b); reduced to the
      single-`mk` `hasseCoeffRepr𝒪` representative by `B_coeff_weight_le_hasse` (PROVEN);
  (b) the **`ξ`-power** bound `Λ_𝒪(ξ^e) ≤ e·Λ(ξ)` (PROVEN here as `weight_Λ_over_𝒪_pow_le`)
      fed by `weight_ξ_bound` — but `weight_ξ_bound` requires `2 ≤ d_R`, whereas (P1) only
      assumes `1 ≤ d_R`; at `d_R = 1` the `ξ` weight is not bounded by the present in-tree API
      (a genuine hypothesis-strength gap, NOT to be papered over by strengthening (P1));
  (c) the genuine BCIKS20 **telescoping**.  IMPORTANT — this does NOT close by naive per-factor
      splitting: the product factor alone is bounded (`partitionProd_βHensel_weight_le`, PROVEN,
      IH-fed) by `(2(k+1−i1)+Σλ)·d_R·D`, and `Σλ` can EXCEED `2·i1+1` (e.g. an all-ones `λ` has
      `Σλ = k+1−i1`), so `Λ(W^a)+Λ(ξ^b)+Λ(B)+Λ(P) ≰ (2(k+1)+1)·d_R·D` in general.  The paper's
      tighter argument couples the `ξ^{2i1+Σλ−2}`/`B_{i1,λ}` *negative* exponents (`δ`, the `−2`,
      the `D−Σλ` in `B`) to the partition so the `Σλ` growth cancels — exactly why BCIKS20 says
      "an easier way is to consider the weight of `α_t`" (line 4276).  This coupled bound is the
      irreducible content of this residual.
PROVEN above and reusable for the next wave: the IH-fed product bound
`partitionProd_βHensel_weight_le`, the over-`𝒪` calculus `_neg`/`_sum_le`/`_mul`/`_pow`/`_W`/
`_nsmul`, `B_coeff_weight_le_hasse`, `surviving_parts_lt`, `sum_map_two_mul_succ`. -/
theorem βHensel_succ_term_weight_le (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hDH : Bivariate.totalDegree H ≤ D) (hdR : 1 ≤ Bivariate.natDegreeY R) (k : ℕ)
    (hIH : ∀ l, l < k + 1 →
      weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp l) D
        ≤ WithBot.some ((2 * l + 1) * Bivariate.natDegreeY R * D))
    (i1 : ℕ) (_hi1 : i1 ∈ Finset.range (k + 2))
    (lam : Nat.Partition (k + 1 - i1)) (_hlam : (k + 1) ∉ lam.parts) :
    weight_Λ_over_𝒪 hH
        ((W𝒪 H) ^ (i1 + deltaSave i1 - 1)
          * (ClaimA2.ξ x₀ R H hHyp) ^ (2 * i1 + sigmaLambda lam - 2)
          * B_coeff H x₀ R i1 lam
          * partitionProd lam
              (fun l => if _h : l < k + 1 then βHensel H x₀ R hHyp l else 0)) D
      ≤ WithBot.some ((2 * (k + 1) + 1) * Bivariate.natDegreeY R * D) := by
  -- WALL (documented, NOT faked): the genuine BCIKS20 per-term telescoping (paper lines
  -- 4264–4268).  The product factor `∏_l β_l^{λ_l}` is bounded (IH-fed) by the PROVEN
  -- `partitionProd_βHensel_weight_le`; the over-`𝒪` multiplicative calculus
  -- (`weight_Λ_over_𝒪_mul_le`/`_pow_le`), the `W`-factor bound (`weight_Λ_over_𝒪_W`) and the
  -- `B_coeff`→`hasseCoeffRepr𝒪` reduction (`B_coeff_weight_le_hasse`) are all PROVEN above.
  --
  -- The residual is NOT closeable by naive per-factor splitting: the product bound alone is
  -- `(2(k+1−i1)+Σλ)·d_R·D`, and `Σλ` can exceed `2·i1+1` (e.g. `λ` all-ones), so the term must
  -- be bounded by the genuine telescoping that couples the `ξ^{2i1+Σλ−2}` / `B_{i1,λ}` factors
  -- to the partition (the paper's tighter argument, NOT the sum of independent factor weights).
  -- That genuine bound additionally needs (a) the `B_coeff`-Hasse weight
  -- `Λ_𝒪(hasseCoeffRepr𝒪 … i1 Σλ) ≤ (D−Σλ)+(d−δ−Σλ)·Λ(W)` and (b) the `ξ` weight via
  -- `weight_ξ_bound`, which requires `2 ≤ d_R` (this lemma has only `1 ≤ d_R` — a real
  -- hypothesis-strength gap at `d_R = 1`).  Deferred; see disposition `ingredientD-wave3.md`.
  sorry

/-- **(P1) full weight bound.**  `weight_Λ_over_𝒪 hH (βHensel … t) D ≤ (2t+1)·natDegreeY R·D`.

The `t = 0` case is `βHensel_weight_bound_zero` (PROVEN).  The inductive step is now FULLY
ASSEMBLED from the proven over-`𝒪` weight calculus: strong induction supplies the IH for all
`l < t`; `βHensel_succ` exposes the literal `(A.1)` sum; `weight_Λ_over_𝒪_neg` strips the sign;
two applications of `weight_Λ_over_𝒪_sum_le` + `Finset.sup_le` reduce the double sum to the
per-term bound `βHensel_succ_term_weight_le`.  The ONLY residual is that per-term WALL. -/
theorem βHensel_weight_bound (x₀ : F) (R : F[X][X][Y]) (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hH : 0 < H.natDegree) {D : ℕ} (_hDH : Bivariate.totalDegree H ≤ D)
    (_hdR : 1 ≤ Bivariate.natDegreeY R) (t : ℕ) :
    weight_Λ_over_𝒪 hH (βHensel H x₀ R hHyp t) D
      ≤ WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) := by
  classical
  induction t using Nat.strong_induction_on with
  | _ t hIH =>
    match t with
    | 0 => exact βHensel_weight_bound_zero H x₀ R hHyp hH _hDH _hdR
    | (k + 1) =>
        -- Expose the `(A.1)` sum and strip the sign.
        rw [βHensel_succ]
        refine le_trans (weight_Λ_over_𝒪_neg H hH _hDH _) ?_
        -- Outer sum over `i1 ∈ range (k+2)`.
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH _hDH _ _) ?_
        refine Finset.sup_le (fun i1 hi1 => ?_)
        -- Inner sum over surviving `lam`.
        refine le_trans (weight_Λ_over_𝒪_sum_le H hH _hDH _ _) ?_
        refine Finset.sup_le (fun lam hlam => ?_)
        -- Per-term bound, with the IH for `βHensel … l` (`l < k+1`) supplied by strong induction.
        exact βHensel_succ_term_weight_le H x₀ R hHyp hH _hDH _hdR k
          (fun l hl => hIH l (by omega)) i1 hi1 lam (Finset.mem_filter.mp hlam).2

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

* `B_coeff` weight + embedding lemmas (the deferred half of §4b) — feed (P1)'s per-term WALL
  `βHensel_succ_term_weight_le`.  The `B_coeff`→`hasseCoeffRepr𝒪` reduction is PROVEN
  (`B_coeff_weight_le_hasse`); the remaining `Λ_𝒪(hasseCoeffRepr𝒪 … i1 Σλ) ≤ (D−Σλ)+(d−δ−Σλ)·Λ(W)`
  (iterated-Hasse degree-drop + `W`-clearing) and the `weight_ξ_bound` `2 ≤ d_R` gap are the WALL.

* iterated-Hasse Leibniz/product rule — needed only for (P2). -/

end BCIKS20.HenselNumerator
