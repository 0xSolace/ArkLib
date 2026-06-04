/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das, Miguel Quaresma (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension
import ArkLib.Data.Probability.Instances
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

/-- Degree bookkeeping for one fold step: if `d < 2^(M+1)` then `d / 2 < 2^M`.
This is the `2^(m-j) → 2^(m-j-1)` degree halving (`foldNth 2` halves the degree bound). -/
lemma half_lt_pow_of_lt_pow_succ {d M : ℕ} (hd : d < 2 ^ (M + 1)) : d / 2 < 2 ^ M := by
  have h2 : 2 ^ (M + 1) = 2 ^ M * 2 := by rw [pow_succ]
  rw [h2] at hd
  omega

omit [Pow ι ℕ] in
/-- **Single fold step → membership** (the inductive heart of Claim 4.15 part 1).

Let `f : smoothCode φ_j (M+1)` with decoded univariate polynomial `p := decodeLT f`
(degree `< 2^(M+1)`). Then the function obtained by folding `f` once,
`g z := foldf S φ z f.val α`, lies in `smoothCode φ_{j+1} M`, with witness polynomial
`foldNth 2 p α` (degree `≤ (2^(M+1)-1)/2 < 2^M`).

Hypotheses make explicit the smooth-domain structure the loose `indexPowT` setup omits
(mirroring the documented repairs on the `BlockRelDistance.lean` sibling lemmas):
* `hφj  : ∀ x, φ_j x = x.val` and `hφj1 : ∀ z, φ_{j+1} z = z.val`
  pin the per-round embeddings to the canonical subtype inclusion;
* `hneg : ∀ z, (-(extract_x S φ j z)).val = -((extract_x S φ j z).val)`
  is the field-negation law for the abstract `Neg` (no such law is derivable in-file);
* `hx0  : ∀ z, (extract_x S φ j z).val ≠ 0` (smooth domains avoid `0`);
* `h2   : (2 : F) ≠ 0` (odd characteristic).

Proof: the witness is `q := foldNth 2 p α`. Its degree halves
(`foldNth_natDegree_le` + `half_lt_pow_of_lt_pow_succ`), and pointwise
`g z = foldf … = (foldNth 2 p α).eval z.val = q.eval (φ_{j+1} z)` by `foldf_eq_foldNth_eval`
(after rewriting `f.val x = p.eval (φ_j x) = p.eval x.val`). Membership then follows from
`mem_code_of_polynomial_of_natDegree_lt_of_eval`. -/
lemma foldf_step_mem_smoothCode
    {S : Finset ι} {φ : ι ↪ F} {j M : ℕ}
    {φ_j : (indexPowT S φ j) ↪ F} {φ_j1 : (indexPowT S φ (j + 1)) ↪ F}
    [Fintype (indexPowT S φ j)] [DecidableEq (indexPowT S φ j)] [Smooth φ_j]
    [Fintype (indexPowT S φ (j + 1))] [DecidableEq (indexPowT S φ (j + 1))]
    [Smooth φ_j1] [Neg (indexPowT S φ j)]
    (f : smoothCode φ_j (M + 1)) (α : F)
    (hφj : ∀ x : indexPowT S φ j, φ_j x = x.val)
    (hφj1 : ∀ z : indexPowT S φ (j + 1), φ_j1 z = z.val)
    (hneg : ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    (fun z : indexPowT S φ (j + 1) => foldf S φ z (f : indexPowT S φ j → F) α)
      ∈ smoothCode φ_j1 M := by
  classical
  -- Decoded univariate polynomial of `f` and its degree bound.
  set p : F[X] := (decodeLT (f : smoothCode φ_j (M + 1)) : Polynomial F) with hp
  have hp_deg : p.natDegree < 2 ^ (M + 1) := by
    have hmem := (decodeLT (f : smoothCode φ_j (M + 1))).2
    rw [Polynomial.mem_degreeLT] at hmem
    by_cases h0 : p = 0
    · rw [h0, Polynomial.natDegree_zero]; positivity
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hmem
  -- `f`'s value at `x` is `p.eval x.val` (decode roundtrip + canonical embedding).
  have hf_val : ∀ x : indexPowT S φ j, (f : indexPowT S φ j → F) x = p.eval x.val := by
    intro x
    have hroundtrip : p.eval (φ_j x) = (f : indexPowT S φ j → F) x :=
      Lagrange.eval_interpolate_at_node (f : indexPowT S φ j → F)
        (φ_j.injective.injOn) (Finset.mem_univ x)
    rw [← hroundtrip, hφj x]
  -- Witness polynomial: the univariate fold.
  set q : F[X] := foldNth 2 p α with hq
  -- Degree halving: `q.natDegree < 2^M`.
  have hq_deg : q.natDegree < 2 ^ M := by
    have hle : q.natDegree ≤ p.natDegree / 2 := by
      rw [hq]; exact foldNth_natDegree_le p α
    exact lt_of_le_of_lt hle (half_lt_pow_of_lt_pow_succ hp_deg)
  -- Pointwise: folded value equals `q.eval (φ_{j+1} z)`.
  have heval : ∀ z : indexPowT S φ (j + 1),
      foldf S φ z (f : indexPowT S φ j → F) α = q.eval (φ_j1 z) := by
    intro z
    have hfeq : (f : indexPowT S φ j → F)
        = fun x : indexPowT S φ j => p.eval x.val := by
      funext x; exact hf_val x
    rw [hfeq]
    rw [foldf_eq_foldNth_eval z p α (hneg z) (hx0 z) h2, hφj1 z, hq]
  -- Membership via the degree-bounded evaluation criterion.
  exact ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval q hq_deg heval

omit [Pow ι ℕ] in
/-- The `k`-fold tower membership, proven by induction on `k`, peeling the outermost fold
(level `k → k+1`, challenge `αs 0`) via `foldf_step_mem_smoothCode` and recursing into the
inner `fold_k_core … k (αs ∘ Fin.succ)` over `indexPowT S φ k`.

This is the engine behind `fold_f_g`. It threads, over **every** level `j ≤ k`, the
canonical-inclusion / negation / nonzero structure that the smooth-domain setting supplies but
the file's loose `indexPowT` data does not (see `foldf_step_mem_smoothCode`). The intermediate
levels `0 < j < k` are exactly why the original `fold_f_g`, carrying embeddings only for `j = 0`
and `j = k`, is not provable as literally stated — the induction needs the whole family. -/
lemma fold_f_g_core
    {S : Finset ι} {φ : ι ↪ F} {m : ℕ}
    (φ_all : ∀ j : ℕ, (indexPowT S φ j) ↪ F)
    [instFin : ∀ j : ℕ, Fintype (indexPowT S φ j)]
    [instDec : ∀ j : ℕ, DecidableEq (indexPowT S φ j)]
    [instSmooth : ∀ j : ℕ, Smooth (φ_all j)]
    [∀ j : ℕ, Neg (indexPowT S φ j)]
    (hφ : ∀ j : ℕ, ∀ x : indexPowT S φ j, φ_all j x = x.val)
    (hneg : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (f : smoothCode (φ_all 0) m) :
    ∀ (k : ℕ) (αs : Fin k → F) (_hk : k ≤ m),
      fold_k_core (f : indexPowT S φ 0 → F) k αs ∈ smoothCode (φ_all k) (m - k) := by
  intro k
  induction k with
  | zero =>
    intro αs _hk
    -- `fold_k_core … 0 αs = f.val`; `m - 0 = m`.
    simp only [fold_k_core, Nat.sub_zero]
    exact f.2
  | succ k ih =>
    intro αs hk
    -- Peel the outermost fold: `fold_k_core … (k+1) αs = foldf … (fold_k_core … k (αs∘succ)) (αs 0)`.
    have hk' : k ≤ m := Nat.le_of_succ_le hk
    -- Inner fold is a smooth codeword over level `k` of degree bound `m - k`.
    have hinner : fold_k_core (f : indexPowT S φ 0 → F) k (fun i => αs (Fin.succ i))
        ∈ smoothCode (φ_all k) (m - k) := ih (fun i => αs (Fin.succ i)) hk'
    -- `m - k = (m - (k+1)) + 1`, the `M + 1` shape the step lemma needs.
    have hM : m - k = (m - (k + 1)) + 1 := by omega
    -- Repackage the inner codeword at the `(M+1)` index expected by the step lemma.
    set fk : smoothCode (φ_all k) ((m - (k + 1)) + 1) :=
      ⟨fold_k_core (f : indexPowT S φ 0 → F) k (fun i => αs (Fin.succ i)), by
        rw [← hM]; exact hinner⟩ with hfk
    -- Apply the single fold step at level `j := k`, `M := m - (k+1)`.
    have hstep := foldf_step_mem_smoothCode
      (φ_j := φ_all k) (φ_j1 := φ_all (k + 1)) fk (αs 0)
      (hφ k) (hφ (k + 1)) (hneg k) (hx0 k) h2
    -- Identify the folded function with `fold_k_core … (k+1) αs`.
    have hfun : (fun z : indexPowT S φ (k + 1) =>
        foldf S φ z (fk : indexPowT S φ k → F) (αs 0))
        = fold_k_core (f : indexPowT S φ 0 → F) (k + 1) αs := by
      funext z
      simp only [fold_k_core, hfk]
    -- The target degree index `m - (k+1)` matches.
    rw [hfun] at hstep
    exact hstep

omit [Pow ι ℕ] in
/-- Claim 4.15 part 1 (statement repair, 2026-06-04).

  Let `f ∈ RS[F, ι, m]`, `α ∈ Fᵏ` the folding randomness, `g = fold_k(f, α)`; for `k ≤ m`,
  `g ∈ RS[F, ι^(2ᵏ), m - k]`.

  ## STATEMENT REPAIR (2026-06-04)

  As literally written the lemma is **not provable**: it carries evaluation embeddings only for
  the two extreme levels (`φ_0` at level `0`, `φ_k` at level `k`), but the `k`-fold tower passes
  through every intermediate level `0 < j < k`, and `foldf` at each level queries the abstract
  `Neg (indexPowT S φ j)` instance — for which the file provides **no** law connecting `(-x).val`
  to `-(x.val)`, and no constraint pinning `φ_j` to the canonical inclusion `x ↦ x.val`. Both
  `g = 0` and `g ≠ 0` codewords are then consistent with the loose data, so membership in the
  specific code `smoothCode φ_k (m-k)` cannot be forced. This mirrors the documented repairs on
  the sibling lemmas in `BlockRelDistance.lean` (`relHammingDist_le_blockRelDistance` etc.), which
  thread `hφ' : ∀ x, φ' x = x.val` and 2-adic structure as explicit hypotheses for the same reason.

  Repair: replace the two loose embeddings with a per-level family `φ_all` and supply, for every
  level, the canonical-inclusion law `hφ`, the field-negation law `hneg`, the nonzero-root law
  `hx0`, and `(2 : F) ≠ 0`. The proof is then the clean induction `fold_f_g_core`. -/
lemma fold_f_g
    {S : Finset ι} {φ : ι ↪ F} {k m : ℕ}
    (φ_all : ∀ j : ℕ, (indexPowT S φ j) ↪ F)
    [∀ j : ℕ, Fintype (indexPowT S φ j)]
    [∀ j : ℕ, DecidableEq (indexPowT S φ j)]
    [∀ j : ℕ, Smooth (φ_all j)]
    [∀ j : ℕ, Neg (indexPowT S φ j)]
    (hφ : ∀ j : ℕ, ∀ x : indexPowT S φ j, φ_all j x = x.val)
    (hneg : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1),
      (-(extract_x S φ j z)).val = -((extract_x S φ j z).val))
    (hx0 : ∀ j : ℕ, ∀ z : indexPowT S φ (j + 1), (extract_x S φ j z).val ≠ 0)
    (h2 : (2 : F) ≠ 0)
    (αs : Fin k → F) (hk : k ≤ m)
    (f : smoothCode (φ_all 0) m) :
    let f_fun := (f : (indexPowT S φ 0) → F)
    let g := fold_k f_fun αs hk
    g ∈ smoothCode (φ_all k) (m - k) := by
  intro f_fun g
  show fold_k (f : indexPowT S φ 0 → F) αs hk ∈ smoothCode (φ_all k) (m - k)
  unfold fold_k
  exact fold_f_g_core φ_all hφ hneg hx0 h2 f k αs hk

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
    ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
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
    ∀ (f : (indexPowT S φ 0) → F) (_hδ : 0 < δ ∧ δ < 1 - (BStar C' 2)),
      Pr_{let α ←$ᵖ F}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) :=
            Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] < errStar C' 2 δ
  := by
    intro f hδ
    let D : PMF F := PMF.uniformOfFintype F
    have hne := folding_preserves_listdecoding_base (S := S) (k := k) (m := m) hm
      (φ := φ) (S_0 := S_0) (S_1 := S_1) (φ_0 := φ_0) (φ_1 := φ_1)
      (C := C) hcode C' hcode' (BStar := BStar) (errStar := errStar) f hδ
    have hmono :
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) :=
            Λᵣ(1, k, fold, S_1, C', hcode', δ)
          ¬ (listBlock' ⊆ foldSet)
        ] ≤
        Pr_{let α ← D}[
          let listBlock : Set ((indexPowT S φ 0) → F) := Λᵣ(0, k, f, S_0, C, hcode, δ)
          let vec_α : Fin 1 → F := (fun _ : Fin 1 => α)
          let foldSet := fold_k_set listBlock vec_α hm
          let fold := fold_k f vec_α hm
          let listBlock' : Set ((indexPowT S φ 1) → F) :=
            Λᵣ(1, k, fold, S_1, C', hcode', δ)
          foldSet ≠ listBlock'
        ] := by
      refine Pr_le_Pr_of_implies D _ _ ?_
      intro α hnot
      dsimp only
      intro heq
      apply hnot
      rw [← heq]
    exact lt_of_le_of_lt hmono hne

end FoldingLemmas

end Fold
