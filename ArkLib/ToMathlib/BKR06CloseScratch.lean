import Mathlib
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

open Polynomial BigOperators Finset

namespace BKR06ScratchTest

open ListDecodable

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- agreement set ≥ a  ⟹  hammingDist ≤ N - a
example (w c : ι → F) (a : ℕ)
    (hagree : a ≤ (Finset.univ.filter (fun i => w i = c i)).card) :
    hammingDist w c ≤ Fintype.card ι - a := by
  have hsplit :
      (Finset.univ.filter (fun i => w i = c i)).card
        + (Finset.univ.filter (fun i => ¬ (w i = c i))).card
        = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hham : hammingDist w c = (Finset.univ.filter (fun i => ¬ (w i = c i))).card := rfl
  omega

-- closeness from hammingDist ≤ floor bound (handle the Decidable diamond)
example (w c : ι → F) (δ : ℝ)
    (hδ : (hammingDist w c : ℝ) / Fintype.card ι ≤ δ) :
    c ∈ relHammingBall w δ := by
  simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist]
  push_cast
  convert hδ using 3
  congr!

-- the parameter arithmetic: agreement ≥ a, q^(β-1) ≤ a/N ⟹ (N-a)/N ≤ δ
example (N a : ℕ) (q : ℕ) (β δ : ℝ) (hN : 0 < N) (haN : a ≤ N)
    (hδdef : δ = 1 - (q : ℝ) ^ (β - 1))
    (hparam : (q : ℝ) ^ (β - 1) ≤ (a : ℝ) / N) :
    ((N : ℝ) - a) / N ≤ δ := by
  rw [hδdef]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr] at hparam
  rw [div_le_iff₀ hNr]
  nlinarith [hparam]

-- prime-power witness sequence: qs i = 2^(i+1) is StrictMono and each is a prime power
example : ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) := by
  refine ⟨fun i => 2 ^ (i + 1), ?_, ?_⟩
  · intro i j hij
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · intro i
    exact (Nat.prime_two.isPrimePow).pow (by omega)

end BKR06ScratchTest
