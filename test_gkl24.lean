import Mathlib.LinearAlgebra.Matrix.LinearIndependent
import Mathlib.LinearAlgebra.Matrix.Basis

def pairs_lt : ℕ → List (ℕ × ℕ)
| 0 => []
| (m + 1) => pairs_lt m ++ (List.range (m + 1)).map (fun i => (i, m - i))

lemma length_pairs_lt (m : ℕ) : (pairs_lt m).length * 2 = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pairs_lt, List.length_append, List.length_map, List.length_range]
    linarith
