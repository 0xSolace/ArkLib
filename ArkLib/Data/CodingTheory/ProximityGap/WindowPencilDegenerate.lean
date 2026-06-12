/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WindowReconstructionPencil

/-!
# Branch (ii) of the window dichotomy: the degenerate pencil (#371, round 14)

When every square row-selection of the reconstruction pencil has identically-zero
determinant, the pencil carries a global POLYNOMIAL kernel vector (the signed
maximal minors of any (j+w+1)-row selection — the Laplace/repeated-row construction),
whose entries have γ-degree ≤ w+1.  Per-scalar Padé uniqueness
(`recSolvable_fraction_unique`, the `IsCoprime`-with-`Z_D` form of the landed
`witness_fraction_unique`) transfers every bad witness's denominator roots to the
kernel family, and the incidence count closes:

  **`#bad · (w − 2j) ≤ n(w+1)`  on the corank-one stratum**  (`w > 2j`),

with the deeper strata carried by a named residual (the corank recursion).
Together with branch (i) (`recSolvable_card_le`) this is the window dichotomy.
-/

open Finset Polynomial Matrix
open scoped NNReal

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

section Degenerate

variable (dom : Fin n ↪ F) {k w j : ℕ}
variable (ℓ₀ ℓ₁ R₀ R₁ : F[X])

/-- Domain nonvanishing makes the modulus coprime to the domain polynomial. -/
theorem isCoprime_mul_domZ
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0) :
    IsCoprime (ℓ₀ * ℓ₁) (domZ dom) := by
  rw [domZ]
  refine IsCoprime.prod_right fun i _ => ?_
  have hker : (ℓ₀ * ℓ₁).eval (dom i) ≠ 0 := by
    rw [eval_mul]
    exact mul_ne_zero (hℓ₀v i) (hℓ₁v i)
  -- X − dom i is prime; it divides ℓ₀ℓ₁ iff the evaluation vanishes
  refine ((prime_X_sub_C (dom i)).coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  exact hker (dvd_iff_isRoot.mp hdvd)

open Classical in
/-- **Per-scalar Padé uniqueness at the reconstruction level**: two solutions of
the inverse-free system at one scalar represent a single fraction
(`h·Z′ = h′·Z`) whenever the profile sits below the modulus degree. -/
theorem recSolvable_fraction_unique
    (hℓ₀v : ∀ i : Fin n, ℓ₀.eval (dom i) ≠ 0)
    (hℓ₁v : ∀ i : Fin n, ℓ₁.eval (dom i) ≠ 0)
    (hdeg2w : 2 * w ≤ (ℓ₀ * ℓ₁).natDegree) (hjw : j < w)
    {γ : F} {h Z h' Z' : F[X]}
    (hhd : h.natDegree ≤ j) (hZd : Z.natDegree ≤ w)
    (hh'd : h'.natDegree ≤ j) (hZ'd : Z'.natDegree ≤ w)
    (hdvd : (ℓ₀ * ℓ₁) ∣ (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z))
    (hdvd' : (ℓ₀ * ℓ₁) ∣ (domZ dom * h' - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z')) :
    h * Z' = h' * Z := by
  have helim : (ℓ₀ * ℓ₁) ∣ domZ dom * (h * Z' - h' * Z) := by
    have h1 : (ℓ₀ * ℓ₁) ∣ (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z) * Z'
        - (domZ dom * h' - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z') * Z :=
      dvd_sub (hdvd.mul_right Z') (hdvd'.mul_right Z)
    have h2 : (domZ dom * h - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z) * Z'
        - (domZ dom * h' - (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z') * Z
        = domZ dom * (h * Z' - h' * Z) := by ring
    rwa [h2] at h1
  have hcop := isCoprime_mul_domZ dom ℓ₀ ℓ₁ hℓ₀v hℓ₁v
  have hdvd2 : (ℓ₀ * ℓ₁) ∣ (h * Z' - h' * Z) := hcop.dvd_of_dvd_mul_left helim
  by_contra hne
  have hne' : h * Z' - h' * Z ≠ 0 := sub_ne_zero.mpr hne
  have hled := Polynomial.natDegree_le_of_dvd hdvd2 hne'
  have hd1 : (h * Z' - h' * Z).natDegree ≤ j + w := by
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans natDegree_mul_le (Nat.add_le_add hhd hZ'd)
    · exact le_trans natDegree_mul_le (Nat.add_le_add hh'd hZd)
  omega

/-- The reconstruction pencil as a polynomial matrix (the scalar is the variable). -/
noncomputable def recMatrixPoly (j w : ℕ) :
    Matrix (Fin (2 * w)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X] :=
  fun r => Sum.elim
    (fun t : Fin (j + 1) =>
      C ((((domZ dom * X ^ (t : ℕ))) %ₘ (ℓ₀ * ℓ₁)).coeff r))
    (fun s : Fin (w + 1) =>
      -(C ((((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)
        + X * C ((((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)).coeff r)))

/-- Entrywise evaluation recovers the instantiated matrix. -/
theorem recMatrixPoly_eval (j w : ℕ) (γ : F) (r : Fin (2 * w))
    (b : Fin (j + 1) ⊕ Fin (w + 1)) :
    ((recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w) r b).eval γ
      = recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ r b := by
  rcases b with t | s
  · rw [recMatrixPoly, recMatrix]
    simp only [Sum.elim_inl]
    rw [eval_C]
  · rw [recMatrixPoly, recMatrix]
    simp only [Sum.elim_inr]
    rw [eval_neg, eval_add, eval_C, eval_mul, eval_X, eval_C]
    have hlin : ((ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)
        = ((ℓ₁ * R₀) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)
          + γ • (((ℓ₀ * R₁) * X ^ (s : ℕ)) %ₘ (ℓ₀ * ℓ₁)) := by
      rw [← smul_modByMonic, ← add_modByMonic]
      congr 1
      rw [smul_eq_C_mul]
      ring
    rw [hlin, coeff_add, coeff_smul, smul_eq_mul]

/-- The square sub-pencil of a row assignment, over polynomials. -/
noncomputable def recSquarePoly (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) :
    Matrix (Fin (j + 1) ⊕ Fin (w + 1)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X] :=
  (recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w).submatrix τ id

/-- The square sub-pencil's determinant is the branch-(i) determinant polynomial. -/
theorem recSquarePoly_det (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)) :
    (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).det
      = recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ := by
  rfl

/-- **The adjugate kernel columns**: under square degeneracy
(`recDetPoly τ = 0`), every adjugate column of the square sub-pencil is a
polynomial kernel vector. -/
theorem recSquarePoly_mulVec_adjugate (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (hdeg0 : recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ = 0)
    (c : Fin (j + 1) ⊕ Fin (w + 1)) :
    (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).mulVec
      (fun b => (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).adjugate b c) = 0 := by
  funext a
  have hmul := Matrix.mul_adjugate (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ)
  have hentry := congrFun (congrFun hmul a) c
  rw [recSquarePoly_det, hdeg0] at hentry
  rw [Matrix.mulVec, dotProduct]
  rw [Matrix.mul_apply] at hentry
  rw [hentry]
  simp

/-- Evaluating an adjugate kernel column yields a kernel vector of the
instantiated square at each scalar. -/
theorem recSquare_eval_kernel (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (hdeg0 : recDetPoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ = 0)
    (c : Fin (j + 1) ⊕ Fin (w + 1)) (γ : F) :
    ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec
      (fun b => ((recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).adjugate b c).eval γ)
      = 0 := by
  funext a
  have hker := congrFun
    (recSquarePoly_mulVec_adjugate dom ℓ₀ ℓ₁ R₀ R₁ j w τ hdeg0 c) a
  have heval := congrArg (Polynomial.eval γ) hker
  rw [Matrix.mulVec, dotProduct] at heval ⊢
  rw [eval_finset_sum] at heval
  rw [Pi.zero_apply, eval_zero] at heval
  rw [Pi.zero_apply]
  rw [← heval]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [recSquarePoly, eval_mul]
  congr 1
  show recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ (τ a) b
    = Polynomial.eval γ ((recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w).submatrix τ id a b)
  rw [Matrix.submatrix_apply, id_eq, recMatrixPoly_eval]

/-- The singly-updated square sub-pencil: row `c₀` replaced by the `cs`-indicator
(the corank-one anchor, following the corank-two file's double-update pattern). -/
noncomputable def recSquareU (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)) :
    Matrix (Fin (j + 1) ⊕ Fin (w + 1)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X] :=
  (recSquarePoly dom ℓ₀ ℓ₁ R₀ R₁ j w τ).updateRow c₀ (Pi.single cs 1)

open Classical in
/-- **The corank-one span**: wherever the updated determinant survives, every
kernel vector of the instantiated square is spanned by the single adjugate
column — `det(γ)·v = v_{cs} · K(γ)`. -/
theorem corank1_span (j w : ℕ)
    {τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w)}
    {c₀ cs : Fin (j + 1) ⊕ Fin (w + 1)} {γ : F}
    {v : Fin (j + 1) ⊕ Fin (w + 1) → F}
    (hv : ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec v = 0)
    (hdet : ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).det).eval γ ≠ 0) :
    ∀ b, ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).det).eval γ * v b
      = v cs * ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate b c₀).eval γ := by
  classical
  set B1 := recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs with hB1
  set Bev := B1.map (Polynomial.eval γ) with hBev
  have hadj : Bev.adjugate = (B1.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) B1
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBev]
    exact h.symm
  have hdetev : Bev.det = (B1.det).eval γ := by
    rw [hBev, ← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  -- the evaluated updated matrix sends v to the c₀-indicator scaled by v cs
  have hBv : ∀ a, Bev a ⬝ᵥ v = (if a = c₀ then v cs else 0) := by
    intro a
    by_cases ha : a = c₀
    · subst ha
      rw [if_pos rfl, dotProduct]
      have hrow : ∀ b, Bev a b = (if b = cs then (1 : F) else 0) := by
        intro b
        rw [hBev, Matrix.map_apply, hB1, recSquareU, Matrix.updateRow_self]
        by_cases hb : b = cs
        · subst hb
          rw [Pi.single_eq_same]
          simp
        · rw [Pi.single_eq_of_ne hb]
          simp [hb]
      calc ∑ b, Bev a b * v b
          = ∑ b, (if b = cs then v b else 0) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hrow b]
            by_cases hb : b = cs <;> simp [hb]
        _ = v cs := by
            rw [Finset.sum_ite_eq' Finset.univ cs v, if_pos (Finset.mem_univ cs)]
    · rw [if_neg ha, dotProduct]
      have hrow : ∀ b, Bev a b
          = (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id a b := by
        intro b
        rw [hBev, Matrix.map_apply, hB1, recSquareU,
          Matrix.updateRow_ne ha]
        rw [recSquarePoly, Matrix.submatrix_apply, id_eq, recMatrixPoly_eval]
        rfl
      calc ∑ b, Bev a b * v b
          = ∑ b, (recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id a b * v b :=
            Finset.sum_congr rfl fun b _ => by rw [hrow b]
        _ = ((recMatrix dom ℓ₀ ℓ₁ R₀ R₁ j w γ).submatrix τ id).mulVec v a := rfl
        _ = 0 := by rw [hv]; rfl
  -- the adjugate column satisfies Bev · K = det · e_{c₀}
  have hBK : ∀ a, Bev a ⬝ᵥ (fun i => (B1.adjugate i c₀).eval γ)
      = Bev.det * (1 : Matrix (Fin (j + 1) ⊕ Fin (w + 1))
          (Fin (j + 1) ⊕ Fin (w + 1)) F) a c₀ := by
    intro a
    have hmul := congrFun (congrFun (Matrix.mul_adjugate Bev) a) c₀
    rw [Matrix.smul_apply, smul_eq_mul] at hmul
    rw [← hmul, Matrix.mul_apply]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj, Matrix.map_apply]
  -- the difference vector dies
  set u' : Fin (j + 1) ⊕ Fin (w + 1) → F := fun b =>
    Bev.det * v b - v cs * (B1.adjugate b c₀).eval γ with hu'def
  have hBu' : Bev.mulVec u' = 0 := by
    funext a
    show Bev a ⬝ᵥ u' = 0
    have hsplit : Bev a ⬝ᵥ u' = Bev.det * (Bev a ⬝ᵥ v)
        - v cs * (Bev a ⬝ᵥ (fun i => (B1.adjugate i c₀).eval γ)) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hu'def]
      ring
    rw [hsplit, hBv a, hBK a]
    by_cases ha : a = c₀
    · subst ha
      rw [if_pos rfl, Matrix.one_apply_eq]
      ring
    · rw [if_neg ha, Matrix.one_apply_ne ha]
      ring
  have hu'0 : u' = 0 := by
    by_contra hne
    have hdet0 : Bev.det = 0 :=
      (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBu'⟩
    rw [hdetev] at hdet0
    exact hdet hdet0
  intro b
  have h := congrFun hu'0 b
  rw [hu'def] at h
  have h' : Bev.det * v b - v cs * (B1.adjugate b c₀).eval γ = 0 := h
  rw [hdetev] at h'
  linear_combination h'

/-- **The generic pencil-determinant degree bound**: any square matrix over the
column sum-type whose `inl`-column entries are constants and `inr`-column entries
have degree ≤ 1 has determinant degree ≤ `w + 1`. -/
theorem det_natDegree_le_of_column_weights {j w : ℕ}
    (M : Matrix (Fin (j + 1) ⊕ Fin (w + 1)) (Fin (j + 1) ⊕ Fin (w + 1)) F[X])
    (hM : ∀ a b, (M a b).natDegree
      ≤ Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b) :
    M.det.natDegree ≤ w + 1 := by
  classical
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  have hprod' : (∏ b : Fin (j + 1) ⊕ Fin (w + 1), M (σ b) b).natDegree ≤ w + 1 := by
    refine le_trans (natDegree_prod_le _ _) ?_
    calc ∑ b : Fin (j + 1) ⊕ Fin (w + 1), (M (σ b) b).natDegree
        ≤ ∑ b : Fin (j + 1) ⊕ Fin (w + 1),
            Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b :=
          Finset.sum_le_sum fun b _ => hM (σ b) b
      _ = w + 1 := by
          rw [Fintype.sum_sum_type]
          simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsg | hsg
  · rw [hsg, one_smul]
    exact hprod'
  · rw [hsg]
    refine le_trans (le_of_eq ?_) hprod'
    rw [Units.neg_smul, one_smul, natDegree_neg]

/-- The entry-weight bound for the polynomial pencil. -/
theorem recMatrixPoly_entry_natDegree (j w : ℕ) (r : Fin (2 * w))
    (b : Fin (j + 1) ⊕ Fin (w + 1)) :
    ((recMatrixPoly dom ℓ₀ ℓ₁ R₀ R₁ j w) r b).natDegree
      ≤ Sum.elim (fun _ : Fin (j + 1) => 0) (fun _ : Fin (w + 1) => 1) b := by
  rcases b with t | s
  · simp only [recMatrixPoly, Sum.elim_inl, natDegree_C, le_refl]
  · simp only [recMatrixPoly, Sum.elim_inr, natDegree_neg]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · rw [natDegree_C]
      omega
    · refine le_trans natDegree_mul_le ?_
      rw [natDegree_X, natDegree_C]

/-- **Adjugate entries of the updated square have degree ≤ w + 1**: each is the
determinant of a doubly-updated pencil square whose entries keep the column
weights. -/
theorem recSquareU_adjugate_natDegree_le (j w : ℕ)
    (τ : Fin (j + 1) ⊕ Fin (w + 1) → Fin (2 * w))
    (c₀ cs b c : Fin (j + 1) ⊕ Fin (w + 1)) :
    ((recSquareU dom ℓ₀ ℓ₁ R₀ R₁ j w τ c₀ cs).adjugate b c).natDegree ≤ w + 1 := by
  rw [Matrix.adjugate_apply]
  have hsingle : ∀ (b'' b₂ : Fin (j + 1) ⊕ Fin (w + 1)),
      ((Pi.single b₂ 1 : (Fin (j + 1) ⊕ Fin (w + 1)) → F[X]) b'').natDegree = 0 := by
    intro b'' b₂
    by_cases h : b'' = b₂
    · subst h
      rw [Pi.single_eq_same]
      exact natDegree_one
    · rw [Pi.single_eq_of_ne h]
      exact natDegree_zero
  refine det_natDegree_le_of_column_weights _ fun a b' => ?_
  by_cases hac : a = c
  · subst hac
    rw [Matrix.updateRow_self, hsingle]
    exact Nat.zero_le _
  · rw [Matrix.updateRow_ne hac, recSquareU]
    by_cases hac₀ : a = c₀
    · subst hac₀
      rw [Matrix.updateRow_self, hsingle]
      exact Nat.zero_le _
    · rw [Matrix.updateRow_ne hac₀]
      rw [recSquarePoly, Matrix.submatrix_apply, id_eq]
      exact recMatrixPoly_entry_natDegree dom ℓ₀ ℓ₁ R₀ R₁ j w (τ a) b'

end Degenerate

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.isCoprime_mul_domZ
#print axioms ProximityGap.WBPencil.recSolvable_fraction_unique
#print axioms ProximityGap.WBPencil.recSquarePoly_mulVec_adjugate
#print axioms ProximityGap.WBPencil.recSquare_eval_kernel
#print axioms ProximityGap.WBPencil.corank1_span
#print axioms ProximityGap.WBPencil.det_natDegree_le_of_column_weights
#print axioms ProximityGap.WBPencil.recSquareU_adjugate_natDegree_le
