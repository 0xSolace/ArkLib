/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.ProofSystem.Whir.BlockRelDistance
import ArkLib.ProofSystem.Whir.MutualCorrAgreement

/-!
# Folding

This file formalizes the notion of folding univariate functions and
lemmas showing that folding preserves list decocidng,
introduced in Section 4 of [ACFY24].

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes (corrections from paper)

- Theorem 4.20:
-- proximity generators should be defined for `C^(0),...,C^(k)` in place of `C^(1),...,C^(k)`
-- `\delta \in (0, 1 - max_{i \in [0,k]} {....})` in place of
   `\delta \in (0, 1 - max_{i \in [k]} {....})`
- Theorem 4.20 holds for `l = 2` as can be seen with `BStar(..,2)` and `errStar(..,2,..)`
  and so `Gen(l,alpha) = {1, alpha,...., alpha^{l-1}}` also corresponds to `l = 2`
  and not for a generic l.

- Lemmas 4.21,4.22,4.23
-- these lemmas refer to the specific case when k set to 1, so it's safe to use the hypothesis 1 ≤ m

## Tags
Open question: should we aim to add tags?
-/

namespace Fold

open BlockRelDistance Vector Finset

variable {F : Type} [Field F] {ι : Type} [Pow ι ℕ]

/-- `∃ x ∈ S`, such that `y = x ^ 2^(k+1)`. `extract_x` returns `z = x ^ 2^k` such that `y = z^2`.
-/
noncomputable def extract_x
  (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ (k + 1)) : indexPowT S φ k :=
  let x := Classical.choose y.property
  let hx := Classical.choose_spec y.property
  let z := (φ x) ^ (2^k)
  ⟨z, ⟨x, hx.1, rfl⟩⟩

/-- Given a function `f : (ι^(2ᵏ)) → F`, foldf operates on two inputs:
  element `y ∈ LpowT S (k+1)`, hence `∃ x ∈ S, s.t. y = x ^ 2^(k+1)` and `α ∈ F`.
  It obtains the square root of y as `xPow := extract_x S φ k y`,
    here xPow is of the form `x ^ 2^k`.
  It returns the value `f(xPow) + f(- xPow)/2 + α * (f(xPow) - f(- xPow))/ 2 * xPow`. -/
noncomputable def foldf (S : Finset ι) (φ : ι ↪ F)
  {k : ℕ} [Neg (indexPowT S φ k)] (y : indexPowT S φ (k + 1))
  (f : indexPowT S φ k → F) (α : F) : F :=
  let xPow := extract_x S φ k y
  let fx := f xPow
  let f_negx := f (-xPow)
  (fx + f_negx) / 2 + α * ((fx - f_negx) / (2 * (xPow.val : F)))

/-- The function `fold_k_core` runs a recursion,
    for a function `f : ι → F` and a vector `αs` of size i
  For `i = 0`, `fold_k_core` returns `f` evaluated at `x ∈ S`
  For `i = (k+1) ≠ 0`,
    αs is parsed as α || αs', where αs' is of size k
    function `fk : (ι^2ᵏ) → F` is obtained by making a recursive call to
      `fold_k_core` on input `αs'`
    we obtain the final function `(ι^(2^(k+1))) → F` by invoking `foldf` with `fk` and `α`. -/
noncomputable def fold_k_core {S : Finset ι} {φ : ι ↪ F} (f : (indexPowT S φ 0) → F)
  [∀ i : ℕ, Neg (indexPowT S φ i)] : (i : ℕ) → (αs : Fin i → F) →
    indexPowT S φ i → F
| 0, _ => fun x₀ => f x₀
| k+1, αs => fun y =>
    let α := αs 0
    let αs' : Fin k → F := fun i => αs (Fin.succ i)
    let fk := fold_k_core f k αs'
    foldf S φ y fk α

/-- Definition 4.14, part 1
  fold_k takes a function `f : ι → F` and a vector `αs` of size k
  and returns a function `Fold : (ι^2ᵏ) → F` -/
noncomputable def fold_k
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (f : (indexPowT S φ 0) → F) (αs : Fin k → F) (_hk : k ≤ m): indexPowT S φ k → F :=
  fold_k_core f k αs

/-- Definition 4.14, part 2
  fold_k takes a set of functions `set : Set (ι → F)` and a vector `αs` of size k
  and returns a set of functions `Foldset : Set ((ι^2ᵏ) → F)` -/
noncomputable def fold_k_set
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  [∀ j : ℕ, Neg (indexPowT S φ j)]
  (set : Set ((indexPowT S φ 0) → F)) (αs : Fin k → F) (hk : k ≤ m): Set (indexPowT S φ k → F) :=
    { g | ∃ f ∈ set, g = fold_k f αs hk}

section FoldingLemmas

open MutualCorrAgreement Generator LinearMvExtension ListDecodable
     NNReal ReedSolomon ProbabilityTheory

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Pow ι ℕ]

/--
The `GenMutualCorrParams` class captures the necessary parameters and assumptions
to model a sequence of proximity generators for a set of smooth ReedSolomon codes.
It contains the following:

for `i ∈ [0,k]` :
- `inst1`, `inst2`, `inst3`: typeclass instances required to operate on `ι^(2ⁱ)`
    (finiteness, nonemptiness, and decidable equality).
- `φ_i`: per-round embeddings from `ι^(2ⁱ)` into `F`.
- `inst4`: smoothness assumption for each `φ_i`.
- `Gen_α i`: the proximity generators wrt the generator function
  `Gen(parℓ,α) : {1,α,α²,..,α^{parℓ-1}}` defined as per `hgen` for code `Cᵢ`
- `inst5`, `inst6` : typeclass instances denoting finiteness of `parℓ`
    underlying `Gen_αᵢ` and `parℓ_type`
- `BStar`, `errStar`: parameters denoting proximity and error thresholds per round.
- `h`: main agreement assumption, stating that each `Gen_α` satisfies mutual correlated agreement
    for its underlying code.
- `hcard, hcard'` : `|Gen_αᵢ.parℓ| = 2` and `|parℓ_type| = 2`
-/
class GenMutualCorrParams [Fintype F] (S : Finset ι) (φ : ι ↪ F) (k : ℕ) where
  m : ℕ

  inst1 : ∀ i : Fin (k + 1), Fintype (indexPowT S φ i)
  inst2 : ∀ i : Fin (k + 1), Nonempty (indexPowT S φ i)
  inst3 : ∀ i : Fin (k + 1), DecidableEq (indexPowT S φ i)

  φ_i : ∀ i : Fin (k + 1), (indexPowT S φ i) ↪ F
  inst4 : ∀ i : Fin (k + 1), Smooth (φ_i i)

  parℓ_type : ∀ _ : Fin (k + 1), Type
  inst5 : ∀ i : Fin (k + 1), Fintype (parℓ_type i)

  exp : ∀ i : Fin (k + 1), (parℓ_type i) ↪ ℕ

  Gen_α : ∀ i : Fin (k + 1), ProximityGenerator (indexPowT S φ i) F :=
    fun i => RSGenerator.genRSC (parℓ_type i) (φ_i i) (m - i) (exp i)
  inst6 : ∀ i : Fin (k + 1), Fintype (Gen_α i).parℓ

  BStar : ∀ i : Fin (k + 1), (Set (indexPowT S φ i → F)) → Type → ℝ≥0
  errStar : ∀ i : Fin (k + 1), (Set (indexPowT S φ i → F)) → Type → ℝ → ENNReal

  h : ∀ i : Fin (k + 1), hasMutualCorrAgreement (Gen_α i)
                                             (BStar i (Gen_α i).C (Gen_α i).parℓ)
                                             (errStar i (Gen_α i).C (Gen_α i).parℓ)

  hcard : ∀ i : Fin (k + 1), Fintype.card ((Gen_α i).parℓ) = 2
  hcard' : ∀ i : Fin (k + 1), Fintype.card (parℓ_type i) = 2

end FoldingLemmas

end Fold
