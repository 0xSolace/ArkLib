/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Polynomial.SplitFold
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
Todo: should we aim to add tags?
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
     NNReal ReedSolomon ProbabilityTheory Polynomial

variable {F : Type} [Field F] [DecidableEq F]
         {ι : Type} [Pow ι ℕ]

/-! ### Fold bridge to univariate `foldNth`

The functions `extract_x`/`foldf` implement the WHIR 2-to-1 even/odd fold over the
`indexPowT` square-root tower. The lemmas below bridge them to the axiom-clean univariate
algebra of `Polynomial.foldNth 2` (`SplitFold.lean`), so that a folded smooth codeword can be
tracked through `decodeLT`/`mVdecode`.

The `Neg (indexPowT S φ k)` instance carried by `foldf` is, in this file's loose setting,
an **abstract** typeclass parameter with no law connecting `(-x).val` to `-(x.val)` in `F`
(`git grep` confirms no `Neg` instance and no negation law for `indexPowT` anywhere in ArkLib).
The bridge therefore takes that law (`hneg`) as an explicit hypothesis, exactly mirroring the
documented statement repairs on the sibling lemmas in `BlockRelDistance.lean`
(`relHammingDist_le_blockRelDistance` etc.), which thread `hφ' : ∀ x, φ' x = x.val` and the
2-adic cardinality relation as hypotheses because the file's `indexPowT` data does not pin them.
-/

omit [DecidableEq F] [Pow ι ℕ] in
/-- The square-root relation realized by `extract_x`: the value of `y ∈ indexPowT S φ (k+1)`
is the square of the value of its extracted root `extract_x S φ k y ∈ indexPowT S φ k`.
Direct from `extract_x`'s definition (`z = (φ x)^(2^k)`) and `Classical.choose_spec`
(`y.val = (φ x)^(2^(k+1))`), since `(2^(k+1)) = 2^k * 2`. -/
lemma extract_x_val_sq {S : Finset ι} {φ : ι ↪ F} (k : ℕ) (y : indexPowT S φ (k + 1)) :
    y.val = ((extract_x S φ k y).val) ^ 2 := by
  have hspec := Classical.choose_spec y.property
  -- `hspec.2 : y.val = (φ (choose ..)) ^ (2 ^ (k+1))`
  show y.val = ((φ (Classical.choose y.property)) ^ (2 ^ k)) ^ 2
  rw [← pow_mul, ← pow_succ]
  exact hspec.2

omit [DecidableEq F] [Pow ι ℕ] in
/-- **Fold bridge** (core algebraic identity). For a univariate polynomial `p` and the
"decoded" function `g x := p.eval x.val`, the WHIR fold value `foldf S φ y g α` coincides
with the univariate fold `(foldNth 2 p α).eval y.val`.

Hypotheses (all forced by the smooth-domain setting but not by the file's loose `indexPowT`):
* `hneg`: the abstract negation agrees with field negation on the extracted root,
  `(-(extract_x S φ k y)).val = -((extract_x S φ k y)).val`;
* `hx0`: the extracted root is nonzero in `F` (smooth domains avoid `0`);
* `h2`: `(2 : F) ≠ 0` (the field has odd characteristic, as for FRI/WHIR).

Proof: rewrite `g` at the two query points via `hneg`, apply `foldNth_two_eval` at
`x := (extract_x ..).val` (using `extract_x_val_sq` for `y.val = x^2`), and check the two
algebraic forms agree by `field_simp`. -/
lemma foldf_eq_foldNth_eval {S : Finset ι} {φ : ι ↪ F} {k : ℕ} [Neg (indexPowT S φ k)]
    (y : indexPowT S φ (k + 1)) (p : F[X]) (α : F)
    (hneg : (-(extract_x S φ k y)).val = -((extract_x S φ k y).val))
    (hx0 : (extract_x S φ k y).val ≠ 0) (h2 : (2 : F) ≠ 0) :
    foldf S φ y (fun x : indexPowT S φ k => p.eval x.val) α
      = (foldNth 2 p α).eval y.val := by
  set x : F := (extract_x S φ k y).val with hx
  unfold foldf
  simp only []
  rw [hneg]
  rw [extract_x_val_sq k y, ← hx]
  rw [foldNth_two_eval p x α hx0 h2]
  field_simp

/-- Claim 4.15 part 1
  Let `f : ι → F`, `α ∈ Fᵏ` is the folding randomness, and let `g : (ι^(2ᵏ) → F) = fold_k(f,α)`
  for k ≤ m, `f ∈ RS[F,ι,m]` then we have `g ∈ RS[F,ι^(2ᵏ),(m-k)]`
-/
lemma fold_f_g
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_k : (indexPowT S φ k) ↪ F}
  [Fintype (indexPowT S φ 0)] [Smooth φ_0]
  [Fintype (indexPowT S φ k)] [Smooth φ_k]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  (αs : Fin k → F) (hk : k ≤ m)
  (f : smoothCode φ_0 m) :
  let f_fun := (f : (indexPowT S φ 0) → F)
  let g := fold_k f_fun αs hk
  g ∈ smoothCode φ_k (m - k) := by sorry

/-- Claim 4.5 part 2
  If fPoly be the multilinear extension of f, then we have
  (m-k)-variate multilinear extension of g as `gPoly = fPoly(α₀,α₁,...α_{k-1},X_k,..,X_{m-1})`
-/
lemma fold_f_g_poly
  {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_k : (indexPowT S φ k) ↪ F}
  [Fintype (indexPowT S φ 0)] [DecidableEq (indexPowT S φ 0)] [Smooth φ_0]
  [Fintype (indexPowT S φ k)] [DecidableEq (indexPowT S φ k)] [Smooth φ_k]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  (αs : Fin k → F) (hk : k ≤ m)
  (f : smoothCode φ_0 m) (g : smoothCode φ_k (m-k)) :
  let fPoly := mVdecode f
  let gPoly := mVdecode g
  gPoly = partialEval fPoly αs hk :=
sorry

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

/-- Theorem 4.20
  Let C = RS[F,ι,m] be a smooth ReedSolomon code
  For k ≤ m and 0 ≤ i ≤ k,
  let Cⁱ = RS[F,ι^(2ⁱ),m-i] and let `Gen(2,α)` be a proxmity generator with
  mutual correlated agreement for `C⁰,...,C^{k}` with proximity bounds BStar and errStar
  Then for every `f : ι → F` and `δ ∈ (0, 1 - max {i ∈ [0,k]} BStar(Cⁱ, 2))`
    `Pr_{αs ← F^k} [ fold_k_set(Λᵣ(0,k,f,S',C,hcode,δ),αs) ≠ Λ(Cᵏ,fold_k(f,αs),δ)]`
      `< ∑ i ∈ [0,k] errStar(Cⁱ,2,δ)`,
  where fold_k_set and fold_k are as defined above,
  αs is a length-k vector of folding randomness,
  `Λᵣ(0,k,f,S',C,hcode,δ)` corresponds to the list of codewords of C δ-close to f,
  wrt (0,k)-wise block relative distance.
  `Λ(Cᵏ,fold_k(f,αs),δ)` is the list of codewords of Cᵏ δ-close to fold_k(f, αs),
  wrt the relative Hamming distance
  Below, we use an instance of the class `GenMutualCorrParams` to capture the
  conditions of proxmity generator with mutual correlated agreement for codes
  C⁰,...,C^{k}.
-/

-- NOTE: need to align this better with the inductive way this is shown via the other lemmas below.
theorem folding_listdecoding_if_genMutualCorrAgreement
  [Fintype F] {S : Finset ι} {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ] {k m : ℕ}
  {S' : Finset (indexPowT S φ 0)} {φ' : (indexPowT S φ 0) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [DecidableEq (indexPowT S φ 0)] [Smooth φ']
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S' φ']
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ' m) (hLe : k ≤ m)
  {δ : ℝ≥0}
  {params : GenMutualCorrParams S φ k} :

  -- necessary typeclasses of underlying domain (ιᵢ)^2ʲ regarding finiteness,
  -- non-emptiness and smoothness
    let _ : ∀ j : Fin (k + 1), Fintype (indexPowT S φ j) := params.inst1
    let _ : ∀ j : Fin (k + 1), Nonempty (indexPowT S φ j) := params.inst2

    ∀ (f : (indexPowT S φ 0) → F)
      (hδ :
        0 < δ ∧
          δ <
            1 - Finset.univ.sup (fun j => params.BStar j (params.Gen_α j).C (params.Gen_α j).parℓ)),
      Pr_{let αs ←$ᵖ (Fin k → F)}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S', C, hcode, δ)
          let fold := fold_k f αs hLe
          let foldSet := fold_k_set listBlock αs hLe
          let kFin : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
          let Cₖ := (params.Gen_α kFin).C
          let listHamming := closeCodewordsRel Cₖ fold δ
          foldSet ≠ listHamming
        ] <
        (∑ i : Fin (k + 1), params.errStar i (params.Gen_α i).C (params.Gen_α i).parℓ δ)
:= by sorry

/-- Lemma 4.21
  Let `C = RS[F,ι,m]` be a smooth ReedSolomon code and k ≤ m
  Denote `C' = RS[F,ι^2,m-1]`, then for every `f : ι → F` and `δ ∈ (0, 1 - BStar(C',2))`
    `Pr_{α ← F} [
      fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α)) ≠
        Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ)
    ]`
      `< errStar(C',2,δ)`
    where `fold_k(f,(fun _ : Fin 1 => α))` returns a function `ι^2 → F`,
    `S_0` and `S_1` denote finite sets of elements of type ι and ι², and
    `Λᵣ` denotes the list of δ-close codewords wrt block relative distance.
    `Λᵣ(0,k,f,S_0,C)` denotes Λᵣ at f : ι → F for code C and
    `Λᵣ(1,k,fold_k(f,(fun _ : Fin 1 => α)),S_1,C')` denotes Λᵣ at fold_k : ι^2 → F for code C'. -/
lemma folding_preserves_listdecoding_base
  [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
    ∀ (f : (indexPowT S φ 0) → F) (hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] < errStar C' 2 δ
  := by sorry

/-- Lemma 4.22
  Following same parameters as Lemma 4.21 above, and states
  `∀ α : F, fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α)) ⊆
      Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ)` -/
lemma folding_preserves_listdecoding_bound
  {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F} [Fintype ι] [DecidableEq ι] [Smooth φ]
  {δ : ℝ≥0} {f : (indexPowT S φ 0) → F}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
      ∀ α : F,
        let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
        let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
        let foldSet := fold_k_set listBlock vec_α hm
        let fold := fold_k f vec_α hm
        let listBlock' : Set ((indexPowT S φ 1) → F) := Λᵣ(1, k, fold, S_1, C', hcode', δ)
        foldSet ⊆ listBlock'
  := by sorry

/-- Lemma 4.23
  Following same parameters as Lemma 4.21 above, and states
  `Pr_{α ← F} [
      Λᵣ(1,k-1,fold_k(f,(fun _ : Fin 1 => α)),S_1,C',δ) ¬ ⊆
        fold_k_set(Λᵣ(0,k,f,S_0,C,δ),(fun _ : Fin 1 => α))
    ] < errStar(C',2,δ)` -/
lemma folding_preserves_listdecoding_base_ne_subset
  [Fintype F] {S : Finset ι} {k m : ℕ} (hm : 1 ≤ m) {φ : ι ↪ F}
  [Fintype ι] [DecidableEq ι] [Smooth φ] {δ : ℝ≥0}
  {S_0 : Finset (indexPowT S φ 0)} {S_1 : Finset (indexPowT S φ 1)}
  {φ_0 : (indexPowT S φ 0) ↪ F} {φ_1 : (indexPowT S φ 1) ↪ F}
  [∀ i : ℕ, Fintype (indexPowT S φ i)] [∀ i : ℕ, DecidableEq (indexPowT S φ i)]
  [Smooth φ_0] [Smooth φ_1]
  [h : ∀ {f : (indexPowT S φ 0) → F}, DecidableBlockDisagreement 0 k f S_0 φ_0]
  [h : ∀ {f : (indexPowT S φ 1) → F}, DecidableBlockDisagreement 1 k f S_1 φ_1]
  [∀ i : ℕ, Neg (indexPowT S φ i)]
  {C : Set ((indexPowT S φ 0) → F)} (hcode : C = smoothCode φ_0 m)
  (C' : Set ((indexPowT S φ 1) → F)) (hcode' : C' = smoothCode φ_1 (m-1))
  {BStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0}
  {errStar : (Set (indexPowT S φ 1 → F)) → ℕ → ℝ≥0 → ℝ≥0} :
    ∀ (f : (indexPowT S φ 0) → F) (hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) :=
            Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] < errStar C' 2 δ
  := by sorry

end FoldingLemmas

end Fold
