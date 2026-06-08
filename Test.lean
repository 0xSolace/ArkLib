import Mathlib
import ArkLib.Data.Polynomial.Multivariate.HasseDerivative

open Polynomial MvPolynomial
variable {F : Type} [Field F]

lemma rootMultiplicity_aeval_ge (Q : MvPolynomial (Fin 2) F) (f : Polynomial F) (x : F) (m : ℕ)
  (h_mult : ArkLib.MvPolynomial.mult_ge ![x, f.eval x] m Q) :
  m ≤ rootMultiplicity x (MvPolynomial.aeval (fun i => if i = 0 then (X : Polynomial F) else f) Q) := by
  sorry
