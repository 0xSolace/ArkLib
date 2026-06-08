import ArkLib.Data.Matrix.Basic

open MvPolynomial Matrix

namespace Spartan114Light

universe u
variable {R : Type u} [CommRing R]

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
  · exact eqPoly_evalC_eval xBits r_x (fun i => ((yBits i : Fin 2) : R))
  · rw [eval_C]
    show eval (fun i => ((yBits i : Fin 2) : R)) (MLE' (M (finFunctionFinEquiv xBits)))
      = eval r_x (C (M (finFunctionFinEquiv xBits) (finFunctionFinEquiv yBits)))
    rw [MLE'_eval_zeroOne, eval_C]

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

theorem append_cast_apply {T : Type*} {a b N : ℕ} (x : Fin a → T) (w : Fin b → T)
    (hN : N = a + b) (e : Fin N) :
    Fin.append x w (Fin.cast hN e)
      = if he : (e : ℕ) < a then x ⟨e, he⟩ else w ⟨(e : ℕ) - a, by omega⟩ := by
  by_cases he : (e : ℕ) < a
  · rw [dif_pos he, show (Fin.cast hN e) = Fin.castAdd b ⟨(e : ℕ), he⟩ from Fin.ext (by simp),
      Fin.append_left]
  · rw [dif_neg he, show (Fin.cast hN e) = Fin.natAdd a ⟨(e : ℕ) - a, by omega⟩
        from Fin.ext (by simp; omega), Fin.append_right]

theorem foldl_add_eq_sum {α : Type*} (h : α → R) (l : List α) (c : R) :
    l.foldl (fun acc a => acc + h a) c = c + (l.map h).sum := by
  induction l generalizing c with
  | nil => simp
  | cons a t ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

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

end Spartan114Light
