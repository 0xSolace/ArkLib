import ArkLib.ProofSystem.Binius.FRIBinius.Prelude

namespace Binius.FRIBinius.ScratchDev
noncomputable section

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial
  MvPolynomial TensorProduct Module Binius.BinaryBasefold RingSwitching

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable [h_Fq_char_prime : Fact (Nat.Prime (ringChar K))] [hF₂ : Fact (Fintype.card K = 2)]
variable [Algebra K L]
variable (β : Basis (Fin (2 ^ κ)) K L)

-- decomposeRows_spec : z = ∑ u, φ₀ (decomposeRows z u) * φ₁ (basis u)
example (z : RingSwitching.TensorAlgebra K L) :
    z = ∑ u : Fin κ → Fin 2, RingSwitching.φ₀ L K
      (RingSwitching.decompose_tensor_algebra_rows (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) z u)
      * RingSwitching.φ₁ L K ((booleanHypercubeBasis κ L K β) u) := by
  conv_lhs => rw [← Basis.sum_repr ((booleanHypercubeBasis κ L K β).baseChange L) z]
  apply Finset.sum_congr rfl
  intro u _
  unfold RingSwitching.decompose_tensor_algebra_rows
  -- goal: (baseChange.repr z u) • (baseChange u) = φ₀ (baseChange.repr z u) * φ₁ (β u)
  rw [Basis.baseChange_apply]
  -- (repr z u) • (1 ⊗ₜ β u) = φ₀ (repr z u) * φ₁ (β u)
  simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]

-- decomposeRows_add : decomposeRows (z + w) u = decomposeRows z u + decomposeRows w u
example (z w : RingSwitching.TensorAlgebra K L) (u : Fin κ → Fin 2) :
    RingSwitching.decompose_tensor_algebra_rows (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) (z + w) u
      = RingSwitching.decompose_tensor_algebra_rows (L := L) (K := K)
          (β := booleanHypercubeBasis κ L K β) z u
        + RingSwitching.decompose_tensor_algebra_rows (L := L) (K := K)
          (β := booleanHypercubeBasis κ L K β) w u := by
  unfold RingSwitching.decompose_tensor_algebra_rows
  rw [map_add, Finsupp.add_apply]

-- decomposeRows_φ₀_mul_φ₁ : decomposeRows (φ₀ a * φ₁ b) u = basis.repr b u • a
example (a b : L) (u : Fin κ → Fin 2) :
    RingSwitching.decompose_tensor_algebra_rows (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) (RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b) u
      = (booleanHypercubeBasis κ L K β).repr b u • a := by
  have h : RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b = a ⊗ₜ[K] b := by
    simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  unfold RingSwitching.decompose_tensor_algebra_rows
  rw [Basis.baseChange_repr_tmul]

-- decomposeColumns_add : decomposeColumns (z + w) v = decomposeColumns z v + decomposeColumns w v
example (z w : RingSwitching.TensorAlgebra K L) (v : Fin κ → Fin 2) :
    RingSwitching.decompose_tensor_algebra_columns (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) (z + w) v
      = RingSwitching.decompose_tensor_algebra_columns (L := L) (K := K)
          (β := booleanHypercubeBasis κ L K β) z v
        + RingSwitching.decompose_tensor_algebra_columns (L := L) (K := K)
          (β := booleanHypercubeBasis κ L K β) w v := by
  letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
  show (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr (z + w) v
    = (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr z v
    + (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr w v
  rw [map_add, Finsupp.add_apply]

-- decomposeColumns_φ₀_mul_φ₁ : decomposeColumns (φ₀ a * φ₁ b) v = basis.repr a v • b
example (a b : L) (v : Fin κ → Fin 2) :
    RingSwitching.decompose_tensor_algebra_columns (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) (RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b) v
      = (booleanHypercubeBasis κ L K β).repr a v • b := by
  have h : RingSwitching.φ₀ L K a * RingSwitching.φ₁ L K b = a ⊗ₜ[K] b := by
    simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  unfold RingSwitching.decompose_tensor_algebra_columns
  rw [Basis.baseChangeRight_repr_tmul]

-- decomposeColumns_spec : z = ∑ v, φ₁ (decomposeColumns z v) * φ₀ (basis v)
example (z : RingSwitching.TensorAlgebra K L) :
    z = ∑ v : Fin κ → Fin 2, RingSwitching.φ₁ L K
      (RingSwitching.decompose_tensor_algebra_columns (L := L) (K := K)
        (β := booleanHypercubeBasis κ L K β) z v)
      * RingSwitching.φ₀ L K ((booleanHypercubeBasis κ L K β) v) := by
  letI rightAlgebra : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  letI rightModule : Module L (L ⊗[K] L) := rightAlgebra.toModule
  conv_lhs => rw [← Basis.sum_repr
    (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)) z]
  apply Finset.sum_congr rfl
  intro v _
  -- RHS: unfold the column decomposition to `baseChangeRight.repr`
  conv_rhs => rw [show RingSwitching.decompose_tensor_algebra_columns (L := L) (K := K)
    (β := booleanHypercubeBasis κ L K β) z v
    = (Basis.baseChangeRight (b := booleanHypercubeBasis κ L K β) (Right := L)).repr z v from rfl]
  rw [Basis.baseChangeRight_apply]
  simp only [RingSwitching.φ₀, RingSwitching.φ₁, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [Algebra.TensorProduct.rightAlgebra_smul_def]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end
end Binius.FRIBinius.ScratchDev
