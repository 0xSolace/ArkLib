import ArkLib.ProofSystem.Spartan.Basic

open MvPolynomial Matrix

namespace Spartan114Scratch

universe u
variable {R : Type u} [CommRing R]

/-- Helper: `eqPolynomial` of a Boolean point, with row vars fixed at `r_x` via `C` then evaluated
at a column point `yBits`, collapses to the plain `R`-level `eqPolynomial` evaluated at `r_x`. -/
theorem eqPoly_evalC_eval {m n : ℕ}
    (xBits : Fin m → Fin 2) (r_x : Fin m → R) (yBits : Fin n → R) :
    eval yBits
        (eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x)
          (eqPolynomial (fun i => ((xBits i : Fin 2) : MvPolynomial (Fin n) R))))
      = eval r_x (eqPolynomial (fun i => ((xBits i : Fin 2) : R))) := by
  classical
  rw [eqPolynomial, eqPolynomial, map_prod, map_prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [singleEqPolynomial, singleEqPolynomial]
  simp only [Function.comp_apply, map_add, map_mul, map_sub, map_one, eval_C, eval_X,
    map_natCast]

/-- **toMLE partial-evaluation bridge.** Evaluating the bivariate matrix MLE with the row variables
fixed to a (general) point `r_x` via `C`, then the column variables at a *Boolean* point `yBits`,
equals the row-MLE of the `(finFunctionFinEquiv yBits)`-th column, evaluated at `r_x`. -/
theorem toMLE_eval_C_rowPoint_colBool {m n : ℕ}
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) (yBits : Fin n → Fin 2) :
    eval (fun i => ((yBits i : Fin 2) : R))
        (eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) M.toMLE)
      = eval r_x
          (MLE (fun xBits : Fin m → Fin 2 =>
            M (finFunctionFinEquiv xBits) (finFunctionFinEquiv yBits))) := by
  classical
  simp only [Matrix.toMLE, MLE']
  rw [MLE, map_sum, map_sum, MLE, map_sum]
  refine Finset.sum_congr rfl fun xBits _ => ?_
  rw [eval_mul, eval_mul, eval_mul]
  congr 1
  · -- eqPolynomial factor
    exact eqPoly_evalC_eval xBits r_x (fun i => ((yBits i : Fin 2) : R))
  · -- the column-entry factor: eval yBits (eval (C∘r_x) (C ((MLE'∘M)(ffe xBits)))) = M .. ..
    rw [eval_C]
    show eval (fun i => ((yBits i : Fin 2) : R)) (MLE' (M (finFunctionFinEquiv xBits)))
      = eval r_x (C (M (finFunctionFinEquiv xBits) (finFunctionFinEquiv yBits)))
    rw [MLE'_eval_zeroOne, eval_C]

/-- Local copy of the matrix-vector scaled-sum decomposition (from `R1CSMleEquivalence`, derived
from `MLE_eval_scaled_sum`). -/
theorem mulVec_MLE_eval_eq_scaled_sum {m n : ℕ}
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R) (r : Fin m → R) :
    eval r (MLE ((M *ᵥ z) ∘ finFunctionFinEquiv))
      = ∑ j : Fin (2 ^ n),
          z j * eval r (MLE (fun xBits : Fin m → Fin 2 =>
            M (finFunctionFinEquiv xBits) j)) := by
  classical
  have hfun : ((M *ᵥ z) ∘ finFunctionFinEquiv)
      = fun xBits : Fin m → Fin 2 =>
          ∑ j : Fin (2 ^ n), z j * M (finFunctionFinEquiv xBits) j := by
    funext xBits; simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [hfun]
  simpa using
    (MvPolynomial.MLE_eval_scaled_sum (σ := Fin m) (R := R)
      (s := (Finset.univ : Finset (Fin (2 ^ n)))) (z := z)
      (g := fun j (xBits : Fin m → Fin 2) => M (finFunctionFinEquiv xBits) j) r)

/-- **S2 inner identity (per matrix).** The Boolean-cube sum of the bivariate matrix MLE
`M(r_x, Y)` weighted by `Z(Y) = MLE(z∘ffe)(Y)` equals the bundled eval-claim value
`MLE((M *ᵥ z)∘ffe)(r_x)`. This is the heart of "second sum-check claimed sum = eval claim". -/
theorem secondSC_cubeSum_inner {m n : ℕ}
    (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R) (z : Fin (2 ^ n) → R) (r_x : Fin m → R) :
    (∑ Y : Fin n → Fin 2,
        eval (fun i => ((Y i : Fin 2) : R))
            (eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) M.toMLE)
          * eval (fun i => ((Y i : Fin 2) : R)) (MLE (z ∘ finFunctionFinEquiv)))
      = eval r_x (MLE ((M *ᵥ z) ∘ finFunctionFinEquiv)) := by
  classical
  rw [mulVec_MLE_eval_eq_scaled_sum]
  rw [← Equiv.sum_comp finFunctionFinEquiv
        (fun j => z j * eval r_x (MLE (fun xBits : Fin m → Fin 2 =>
          M (finFunctionFinEquiv xBits) j)))]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [toMLE_eval_C_rowPoint_colBool, MLE_eval_zeroOne]
  show eval r_x _ * (z ∘ finFunctionFinEquiv) Y = _
  rw [Function.comp_apply]
  ring

/-- Generic `Fin.append`-after-cast case split, used for the R1CS `𝕫 = x ‖ w` value. -/
theorem append_cast_apply {T : Type*} {a b N : ℕ} (x : Fin a → T) (w : Fin b → T)
    (hN : N = a + b) (e : Fin N) :
    Fin.append x w (Fin.cast hN e)
      = if he : (e : ℕ) < a then x ⟨e, he⟩ else w ⟨(e : ℕ) - a, by omega⟩ := by
  by_cases he : (e : ℕ) < a
  · rw [dif_pos he, show (Fin.cast hN e) = Fin.castAdd b ⟨(e : ℕ), he⟩ from Fin.ext (by simp),
      Fin.append_left]
  · rw [dif_neg he, show (Fin.cast hN e) = Fin.natAdd a ⟨(e : ℕ) - a, by omega⟩
        from Fin.ext (by simp; omega), Fin.append_right]

/-- Generic: `foldl (· + h ·)` from `c` over a list accumulates to `c + ∑ (map h)`. -/
theorem foldl_add_eq_sum {α : Type*} (h : α → R) (l : List α) (c : R) :
    l.foldl (fun acc a => acc + h a) c = c + (l.map h).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

/-- **S1 core (abstract).** The Boolean-indexed `eqPolynomial`-weighted sum of `z` equals the
evaluation of `MLE (z ∘ ffe)` at `r_y`. -/
theorem boolFold_eq_MLE_eval {k : ℕ} (r_y : Fin k → R) (z : Fin (2 ^ k) → R) :
    (∑ yEnum : Fin (2 ^ k),
        eval r_y (eqPolynomial
            (fun j => ((finFunctionFinEquiv.symm yEnum j : Fin 2) : R)))
          * z yEnum)
      = eval r_y (MLE (z ∘ finFunctionFinEquiv)) := by
  classical
  rw [MLE_eval_eq_sum_eqTilde,
    ← Equiv.sum_comp finFunctionFinEquiv
      (fun yEnum => eval r_y (eqPolynomial
          (fun j => ((finFunctionFinEquiv.symm yEnum j : Fin 2) : R))) * z yEnum)]
  refine Finset.sum_congr rfl fun Y _ => ?_
  simp only [Equiv.symm_apply_apply, Function.comp_apply, eqTilde]
  rw [eqPolynomial_symm]

section Outer
variable {S : Type} [CommRing S] [IsDomain S] [Fintype S] (pp : Spartan.PublicParams)

open Spartan.Spec

/-- The witness oracle answers a Boolean MLE-evaluation query with the underlying witness value. -/
theorem witness_answer (w : Spartan.Spec.Witness S pp) (k : Fin (2 ^ pp.ℓ_w)) :
    OracleInterface.answer w (boolPoint S k) = w k := by
  classical
  show eval (boolPoint S k) (MLE (w ∘ finFunctionFinEquiv)) = w k
  show eval (fun j => ((finFunctionFinEquiv.symm k j : Fin 2) : S)) (MLE (w ∘ finFunctionFinEquiv))
    = w k
  rw [MLE_eval_zeroOne]
  simp

/-- **S2 — second sum-check claimed-sum identity.** The Boolean-cube sum of Spartan's second
sum-check virtual polynomial equals the random-linear-combination of the bundled evaluation claims
(each `eval r_x (MLE ((M_idx *ᵥ z) ∘ ffe))`). -/
theorem secondSumcheck_cubeSum_eq_rlc
    (stmt : Statement.AfterLinearCombination S pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination S pp i) :
    (∑ Y : Fin pp.ℓ_n → Fin 2,
        eval (fun i => ((Y i : Fin 2) : S))
          (secondSumCheckVirtualPolynomial S pp stmt oStmt))
      = stmt.1 .A *
          eval stmt.2.1 (MLE ((oStmt (.inr (.inl .A)) *ᵥ
            R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0)))) ∘ finFunctionFinEquiv))
        + stmt.1 .B *
          eval stmt.2.1 (MLE ((oStmt (.inr (.inl .B)) *ᵥ
            R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0)))) ∘ finFunctionFinEquiv))
        + stmt.1 .C *
          eval stmt.2.1 (MLE ((oStmt (.inr (.inl .C)) *ᵥ
            R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0)))) ∘ finFunctionFinEquiv)) := by
  classical
  have h : ∀ Y : Fin pp.ℓ_n → Fin 2,
      eval (fun i => ((Y i : Fin 2) : S))
          (secondSumCheckVirtualPolynomial S pp stmt oStmt)
        = stmt.1 .A *
            (eval (fun i => ((Y i : Fin 2) : S))
                (eval ((C : S →+* MvPolynomial (Fin pp.ℓ_n) S) ∘ stmt.2.1)
                  (oStmt (.inr (.inl .A))).toMLE)
              * eval (fun i => ((Y i : Fin 2) : S))
                  (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv)))
          + stmt.1 .B *
            (eval (fun i => ((Y i : Fin 2) : S))
                (eval ((C : S →+* MvPolynomial (Fin pp.ℓ_n) S) ∘ stmt.2.1)
                  (oStmt (.inr (.inl .B))).toMLE)
              * eval (fun i => ((Y i : Fin 2) : S))
                  (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv)))
          + stmt.1 .C *
            (eval (fun i => ((Y i : Fin 2) : S))
                (eval ((C : S →+* MvPolynomial (Fin pp.ℓ_n) S) ∘ stmt.2.1)
                  (oStmt (.inr (.inl .C))).toMLE)
              * eval (fun i => ((Y i : Fin 2) : S))
                  (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv))) := by
    intro Y
    simp only [secondSumCheckVirtualPolynomial, eval_add, eval_mul, eval_C, Function.comp_def,
      Fin.cast_eq_self]
    ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, secondSC_cubeSum_inner]

/-- Replica of `Bricks.zEvalPureFoldStep` (post-`zVal`), to verify the S1 assembly technique. -/
noncomputable def zStepRep (stmt : Statement.AfterSecondSumcheck S pp)
    (oStmt : ∀ i, OracleStatement.AfterSecondSumcheck S pp i)
    (acc : S) (yEnum : Fin (2 ^ pp.ℓ_n)) : S :=
  acc + eval stmt.1 (eqPolynomial (boolPoint S yEnum)) *
    (if hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x then stmt.2.2.2.2 ⟨(yEnum : ℕ), hy⟩
      else OracleInterface.answer (oStmt (.inr (.inr 0)))
        (boolPoint S ⟨(yEnum : ℕ) - pp.toSizeR1CS.n_x, by
          have hlt := yEnum.isLt
          have hle : 2 ^ pp.ℓ_w ≤ 2 ^ pp.ℓ_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n
          have hnx : pp.toSizeR1CS.n_x = 2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w := rfl
          omega⟩))

/-- The per-step value is `acc + coeff_y · z y`, where `z = 𝕫 = x ‖ w`. -/
theorem zStepRep_eq_z (stmt : Statement.AfterSecondSumcheck S pp)
    (oStmt : ∀ i, OracleStatement.AfterSecondSumcheck S pp i)
    (acc : S) (yEnum : Fin (2 ^ pp.ℓ_n)) :
    zStepRep S pp stmt oStmt acc yEnum
      = acc + eval stmt.1 (eqPolynomial (boolPoint S yEnum)) *
          R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) yEnum := by
  classical
  unfold zStepRep
  congr 1
  congr 1
  rw [R1CS.𝕫, Function.comp_apply, append_cast_apply]
  by_cases hy : (yEnum : ℕ) < pp.toSizeR1CS.n_x
  · rw [dif_pos hy, dif_pos hy]
  · rw [dif_neg hy, dif_neg hy, witness_answer]

/-- Replica of `Bricks.zEvalPureFold`. -/
noncomputable def zFoldRep (stmt : Statement.AfterSecondSumcheck S pp)
    (oStmt : ∀ i, OracleStatement.AfterSecondSumcheck S pp i) : S :=
  (Finset.univ : Finset (Fin (2 ^ pp.ℓ_n))).toList.foldl (zStepRep S pp stmt oStmt) 0

/-- **S1 full — the verifier-side `Z(r_y)` reconstruction equals the MLE evaluation.** -/
theorem zFoldRep_eq_MLE (stmt : Statement.AfterSecondSumcheck S pp)
    (oStmt : ∀ i, OracleStatement.AfterSecondSumcheck S pp i) :
    zFoldRep S pp stmt oStmt
      = eval stmt.1
          (MLE (R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv)) := by
  classical
  unfold zFoldRep
  rw [show (zStepRep S pp stmt oStmt)
        = (fun acc yEnum => acc + (fun y => eval stmt.1 (eqPolynomial (boolPoint S y)) *
            R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))) y) yEnum)
      from by funext acc yEnum; exact zStepRep_eq_z S pp stmt oStmt acc yEnum]
  rw [foldl_add_eq_sum, zero_add, Finset.sum_to_list]
  exact boolFold_eq_MLE_eval stmt.1 (R1CS.𝕫 stmt.2.2.2.2 (oStmt (.inr (.inr 0))))

end Outer

end Spartan114Scratch
