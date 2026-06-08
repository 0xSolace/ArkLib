import Mathlib.Data.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.HammingWeight
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS

open scoped NNReal

namespace ArkLib.JohnsonBound
def johnsonDenom (n d e : ℕ) : ℤ := (d : ℤ) * n - 2 * e * n
end ArkLib.JohnsonBound

theorem hwitAll_common_center_false_above_half_johnson :
    ∃ (ι F : Type) (_ : Fintype ι) (_ : Nonempty ι) (_ : DecidableEq ι)
      (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (k : ℕ) (_ : NeZero k)
      (domain : ι ↪ F) (δ : ℝ≥0) (u : Code.WordStack F (Fin 2) ι),
      ((1 - Real.sqrt ((k:ℝ)/Fintype.card ι))/2 < (δ:ℝ)) ∧
      ((δ:ℝ) < 1 - Real.sqrt ((k:ℝ)/Fintype.card ι)) ∧
      ¬ (∃ x : ι, u 1 x ≠ 0 ∧ ∃ w : ι → F, ∃ e : ℕ,
          0 < ArkLib.JohnsonBound.johnsonDenom (Fintype.card ι) (Fintype.card ι - k + 1) e ∧
          ∀ γ : F, δᵣ(u 0 + γ • u 1, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ →
            ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
              Δ₀(c, w) ≤ e ∧ c x = u 0 x + γ * u 1 x) := by
  use Fin 4, ZMod 5, inferInstance, inferInstance, inferInstance
  use inferInstance, inferInstance, inferInstance, 2, inferInstance
  let domain : Fin 4 ↪ ZMod 5 := ⟨fun i => i.val, by decide⟩
  use domain, (1 : ℝ≥0) / 5
  let u : Code.WordStack (ZMod 5) (Fin 2) (Fin 4) :=
    fun i j => if i = 0 then 0 else j.val
  use u
  sorry
