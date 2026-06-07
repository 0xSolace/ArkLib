/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The genuine FPRUNE one-step inequality (Lemma 3.4 with the agreement indicator + eq. (2))

The simplified `fprune_one_step` (in `FPRUNEPotential.lean`) proves the one-step potential
inequality under the implicit assumption that the candidate codeword agrees on *every* eligible
coordinate. The **actual** FPRUNE recursion (Chen–Zhang 2025 / arXiv 2512.08017, Def. 8) carries
an agreement indicator: the potential is

  `f_{η,η'}(ℋ,c,T) = [c agrees with the lists on all of T] · (1-η')^{|T|} / (dim ℋ + η)`,

so the expectation `G(ℋ,c) = E_T[X_{c,T}(1-η')^{|T|}]` obeys the recursion

  `G(ℋ,c) = ∑_{i eligible} (wt_η(ℋ_i)/W)·(1-η')·[c_i agrees]·G(ℋ_i,c)`,

summing only over **eligible** coordinates (`wt_η(ℋ_i) ≤ (1-η')·wt_η(ℋ)`) and crediting only the
ones where `c` **agrees**. Lower-bounding `G` therefore reduces to:

* the **arithmetic one-step** (`fprune_one_step_weighted`): with eligible-weight normaliser `W`
  and the eligible-agreeing coordinate set `J`, the bound `W ≤ |J|·(1-η')(r+η)` gives
  `η/(r+η) ≤ ∑_{j∈J} (wt_η(ℋ_j)/W)·(1-η')·(η/(dim ℋ_j + η))`;
* the **design weight bound** (`fprune_eligible_weight_bound`, Chen–Zhang eq. (2)): the
  subspace-design inequality (Def. 6) bounds the eligible weight
  `W ≤ ((τ(r)+η)·n - (ineligible)·(1-η'))·(r+η)`, and the distance hypothesis
  `(τ(r)+η)·n ≤ (agree)·(1-η')` (the candidate is close) forces, with
  `|J| ≥ agree - ineligible`, exactly `W ≤ |J|·(1-η')(r+η)`.

Composing the two yields the genuine Lemma 3.4 one-step, ready for the strong-induction
`fprune_potential_bound`. All `Finset`/order arithmetic; no `sorry`.
-/

namespace CodingTheory.ListDecoding

open Finset

variable {ι : Type*}

/-- **The genuine FPRUNE one-step (arithmetic core), with abstract eligible-weight `W`.** `J` is
the set of *eligible-and-agreeing* coordinates and `W > 0` the eligible-weight normaliser. From
the design weight bound `W ≤ |J|·(1-η')(r+η)`, the design-weighted survival sum dominates the
potential `η/(r+η)`. Each summand `[(d_j+η)(1-η')/W]·[η/(d_j+η)]` cancels to `(1-η')η/W`, so the
sum is `|J|·(1-η')η/W`, and the bound is exactly `W ≤ |J|(1-η')(r+η)`. -/
theorem fprune_one_step_weighted
    (η η' : ℝ) (hη : 0 < η) (hη' : 0 ≤ 1 - η')
    (r : ℕ) (J : Finset ι) (d : ι → ℕ) (W : ℝ) (hWpos : 0 < W)
    (hWle : W ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η))) :
    η / ((r : ℕ) + η) ≤
      ∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / W) * (η / ((d j : ℕ) + η)) := by
  have hposTerm : ∀ j, (0 : ℝ) < (d j : ℝ) + η := fun j =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hrη : (0 : ℝ) < (r : ℝ) + η := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hη
  -- Each summand collapses to `(1-η')·η / W`.
  have hterm : ∀ j ∈ J,
      ((((d j : ℝ) + η) * (1 - η')) / W) * (η / ((d j : ℕ) + η)) = (1 - η') * η / W := by
    intro j _
    have hdj : (d j : ℝ) + η ≠ 0 := ne_of_gt (hposTerm j)
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- `η/(r+η) ≤ |J|·(1-η')η / W`.
  have key : η / ((r : ℝ) + η) ≤ ((J.card : ℝ) * (1 - η') * η) / W := by
    rw [le_div_iff₀ hWpos, div_mul_eq_mul_div, div_le_iff₀ hrη]
    nlinarith [mul_le_mul_of_nonneg_left hWle (le_of_lt hη), hη, hWpos, hrη]
  calc η / ((r : ℕ) + η)
      = η / ((r : ℝ) + η) := by push_cast; ring_nf
    _ ≤ ((J.card : ℝ) * (1 - η') * η) / W := key
    _ = (J.card : ℝ) * ((1 - η') * η / W) := by ring

/-- **Chen–Zhang eq. (2): the eligible-weight bound from the subspace design.** With block length
`n`, candidate dimension `r`, design parameter `τr`, `agree` agreeing coordinates and `inelig`
ineligible coordinates, the τ-subspace-design property (Def. 6) gives the eligible-weight bound
`W ≤ ((τr+η)·n - inelig·(1-η'))·(r+η)`, and the distance hypothesis `(τr+η)·n ≤ agree·(1-η')`
(the candidate is within the decoding radius) together with `agree - inelig ≤ |J|` (eligible
agreeing ≥ agreeing − ineligible) yields exactly the bound consumed by `fprune_one_step_weighted`:
`W ≤ |J|·(1-η')(r+η)`. -/
theorem fprune_eligible_weight_bound
    (η η' : ℝ) (hη'pos : 0 < 1 - η')
    (r n : ℕ) (τr W agree inelig : ℝ) (J : Finset ι)
    (hrη : (0 : ℝ) ≤ (r : ℝ) + η)
    (hEq2 : W ≤ ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((r : ℝ) + η))
    (hDist : (τr + η) * (n : ℝ) ≤ agree * (1 - η'))
    (hJ : agree - inelig ≤ (J.card : ℝ)) :
    W ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η)) := by
  -- `|J|(1-η')(r+η) ≥ (agree-inelig)(1-η')(r+η) = (agree(1-η') - inelig(1-η'))(r+η)`
  --   `≥ ((τr+η)n - inelig(1-η'))(r+η) ≥ W`.
  have hstep : ((τr + η) * (n : ℝ) - inelig * (1 - η')) * ((r : ℝ) + η)
      ≤ (J.card : ℝ) * ((1 - η') * ((r : ℝ) + η)) := by
    have h1 : (τr + η) * (n : ℝ) - inelig * (1 - η')
        ≤ (J.card : ℝ) * (1 - η') := by
      nlinarith [mul_le_mul_of_nonneg_right hJ (le_of_lt hη'pos), hDist]
    nlinarith [mul_le_mul_of_nonneg_right h1 hrη]
  linarith [hEq2, hstep]

end CodingTheory.ListDecoding
