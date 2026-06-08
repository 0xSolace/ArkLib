import ArkLib.ProofSystem.Spartan.Basic
open MvPolynomial Matrix Spartan.Spec
namespace D
variable {S : Type} [CommRing S] [IsDomain S] [Fintype S] (pp : Spartan.PublicParams)
example (stmt : Statement.AfterLinearCombination S pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination S pp i) (Y : Fin pp.ℓ_n → Fin 2) :
    eval (fun i => ((Y i : Fin 2) : S)) (secondSumCheckVirtualPolynomial S pp stmt oStmt)
      = stmt.1 .A * (eval (fun i => ((Y i : Fin 2):S)) (eval ((C : S →+* MvPolynomial (Fin pp.ℓ_n) S) ∘ stmt.2.1) (oStmt (.inr (.inl .A))).toMLE) * eval (fun i => ((Y i : Fin 2):S)) (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv)))
      + stmt.1 .B * (eval (fun i => ((Y i : Fin 2):S)) (eval ((C : S →+* MvPolynomial (Fin pp.ℓ_n) S) ∘ stmt.2.1) (oStmt (.inr (.inl .B))).toMLE) * eval (fun i => ((Y i : Fin 2):S)) (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv)))
      + stmt.1 .C * (eval (fun i => ((Y i : Fin 2):S)) (eval ((C : S →+* MvPolynomial (Fin pp.ℓ_n) S) ∘ stmt.2.1) (oStmt (.inr (.inl .C))).toMLE) * eval (fun i => ((Y i : Fin 2):S)) (MLE (R1CS.𝕫 stmt.2.2.2 (oStmt (.inr (.inr 0))) ∘ finFunctionFinEquiv))) := by
  simp only [secondSumCheckVirtualPolynomial, eval_add, eval_mul, eval_C, Function.comp_def,
    Fin.cast_eq_self]
  ring
end D
