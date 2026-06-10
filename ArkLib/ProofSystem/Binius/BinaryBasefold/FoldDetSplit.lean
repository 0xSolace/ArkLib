/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-!
# #317: prove `FoldMatrixDetNeZeroResidual`.

Strategy:
* `detSplitFactor`: det of the 2×2-block matrix
  `fromBlocks (xb • M) ((-xa) • N) ((-1) • M) N = (xb - xa)^m * det M * det N`
  via the factorization `fromBlocks (xb•1) ((-xa)•1) ((-1)•1) 1 * fromBlocks M 0 0 N`.
* `det_submatrix_equiv_ne_zero`: reindexing rows/cols by two (possibly different)
  equivs changes det only by a permutation sign (a unit), preserving nonvanishing.
* `qMap_total_fiber_one_step_ne`: the two single-step fiber points differ
  (their 0-th basis coefficients are the bits 0 ≠ 1 of the fiber index).
* `foldMatrixNat_succ_eq_submatrix`: the recursion is exactly the block matrix
  `fromBlocks (x₁•M₀) ((-x₀)•M₁) ((-1)•M₀) M₁` reindexed by the low-bit row split
  and the high-bit column split.
* Induction ⇒ `foldMatrixNat` has nonzero det ⇒ the `FoldMatrixDetNeZeroResidual`
  instance.
-/

namespace Binius.BinaryBasefold.DetNeZero

open Matrix Binius.BinaryBasefold

/-! ### Generic matrix bricks (no Binius dependencies) -/

section MatrixBricks

variable {L : Type} [Field L]

/-- Row split of `Fin (2^(n+1))` by the LOW bit: `a ↦ (a % 2, a / 2)`,
`inl` for low bit `0`, `inr` for low bit `1`. -/
def rowSplit (n : ℕ) : Fin (2 ^ (n + 1)) ≃ (Fin (2 ^ n) ⊕ Fin (2 ^ n)) where
  toFun a :=
    if a.val % 2 = 0 then
      Sum.inl ⟨a.val / 2, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := a.isLt; omega⟩
    else
      Sum.inr ⟨a.val / 2, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := a.isLt; omega⟩
  invFun p :=
    match p with
    | Sum.inl q => ⟨2 * q.val, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
    | Sum.inr q => ⟨2 * q.val + 1, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
  left_inv a := by
    by_cases h : a.val % 2 = 0 <;> simp only [h, if_true, if_false] <;>
      · apply Fin.ext
        simp only [Fin.val_mk]
        omega
  right_inv p := by
    rcases p with q | q
    · simp only [Nat.mul_mod_right, if_true]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · have h : (2 * q.val + 1) % 2 = 1 := by omega
      simp only [h, one_ne_zero, if_false]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- Column split of `Fin (2^(n+1))` by the HIGH bit: `b ↦ (b / 2^n, b % 2^n)`,
`inl` for high bit `0`, `inr` for high bit `1`. -/
def colSplit (n : ℕ) : Fin (2 ^ (n + 1)) ≃ (Fin (2 ^ n) ⊕ Fin (2 ^ n)) where
  toFun b :=
    if h : b.val < 2 ^ n then Sum.inl ⟨b.val, h⟩
    else Sum.inr ⟨b.val - 2 ^ n, by
      have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      have := b.isLt; omega⟩
  invFun p :=
    match p with
    | Sum.inl q => ⟨q.val, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
    | Sum.inr q => ⟨2 ^ n + q.val, by
        have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have := q.isLt; omega⟩
  left_inv b := by
    by_cases h : b.val < 2 ^ n
    · simp only [h, dif_pos]
    · simp only [h, dif_neg, not_false_iff]
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
  right_inv p := by
    rcases p with q | q
    · simp only [Fin.val_mk, q.isLt, dif_pos]
    · have h : ¬ (2 ^ n + q.val < 2 ^ n) := by omega
      simp only [Fin.val_mk, h, dif_neg, not_false_iff]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- `det (fromBlocks (xb•M) ((-xa)•N) ((-1)•M) N) = (xb - xa)^m * det M * det N`. -/
lemma detSplitFactor {m : ℕ} (xa xb : L) (M N : Matrix (Fin m) (Fin m) L) :
    (Matrix.fromBlocks (xb • M) ((-xa) • N) ((-1 : L) • M) N).det
      = (xb - xa) ^ m * M.det * N.det := by
  have hfact : Matrix.fromBlocks (xb • M) ((-xa) • N) ((-1 : L) • M) N =
      (Matrix.fromBlocks (xb • (1 : Matrix (Fin m) (Fin m) L)) ((-xa) • 1) ((-1 : L) • 1) 1) *
      (Matrix.fromBlocks M 0 0 N) := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      smul_zero, add_zero, zero_add, Matrix.mul_one]
  rw [hfact, Matrix.det_mul, Matrix.det_fromBlocks_one₂₂, Matrix.det_fromBlocks_zero₁₂]
  have hscal : (xb • (1 : Matrix (Fin m) (Fin m) L)) - ((-xa) • 1) * ((-1 : L) • 1) =
      (xb - xa) • 1 := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, neg_mul_neg, mul_one, sub_smul]
  rw [hscal, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, mul_assoc]

/-- Reindexing rows and columns by two (possibly different) equivalences preserves
nonvanishing of the determinant: the two reindexings differ by a column permutation,
whose sign is a unit. -/
lemma det_submatrix_equiv_ne_zero {m n : Type*} [DecidableEq m] [DecidableEq n]
    [Fintype m] [Fintype n] (e₁ e₂ : n ≃ m) (M : Matrix m m L) (h : M.det ≠ 0) :
    (M.submatrix e₁ e₂).det ≠ 0 := by
  have hsub : M.submatrix e₁ e₂ =
      (M.submatrix e₁ e₁).submatrix id (e₂.trans e₁.symm) := by
    ext a b
    simp [Matrix.submatrix_apply]
  rw [hsub, Matrix.det_permute' (e₂.trans e₁.symm) (M.submatrix e₁ e₁),
    Matrix.det_submatrix_equiv_self]
  apply mul_ne_zero _ h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e₂.trans e₁.symm)) with hs | hs <;>
    simp [hs]

end MatrixBricks

end Binius.BinaryBasefold.DetNeZero
