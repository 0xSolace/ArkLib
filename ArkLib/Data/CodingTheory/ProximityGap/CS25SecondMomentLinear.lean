/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25SecondMomentPairCount

/-!
# CS25 second moment — linear-code reduction (#82)

For a **linear** code `𝒞` (closed under `±`), the ordered-pair second-moment sum collapses to a
single sum weighted by `|𝒞|`.  Combined with `sum_closeCount_sq_eq_sum_ballInterCount`, this gives

  `∑_w (closeCount 𝒞 r w)² = |𝒞| · ∑_{v ∈ 𝒞} |B(0,r) ∩ B(v,r)|`.

Since `ballInterCount r v` depends only on `Δ₀(v,0)`, the inner sum is the weight-enumerator form
`∑_d A_d · I(d)` — the second-moment input to the CS25 covered-fraction / `ε_ca` bound (#82).
-/

namespace ArkLib.CS25

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- **Linear-code pair-sum reduction.**  For a code `𝒞` closed under `+` and `−`, an ordered-pair
sum of any difference-function collapses to a single sum weighted by `|𝒞|`:
`∑_{c, c' ∈ 𝒞} g(c' − c) = |𝒞| · ∑_{v ∈ 𝒞} g(v)`.  For each fixed `c`, `c' ↦ c' − c` bijects `𝒞`
(inverse `v ↦ v + c`). -/
theorem sum_pair_sub_eq_card_mul (𝒞 : Finset (ι → F)) (g : (ι → F) → ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞) :
    ∑ c ∈ 𝒞, ∑ c' ∈ 𝒞, g (c' - c) = 𝒞.card * ∑ v ∈ 𝒞, g v := by
  classical
  have hper : ∀ c ∈ 𝒞, ∑ c' ∈ 𝒞, g (c' - c) = ∑ v ∈ 𝒞, g v := by
    intro c hc
    refine Finset.sum_bij' (fun c' _ => c' - c) (fun v _ => v + c) ?_ ?_ ?_ ?_ ?_
    · intro c' hc'; exact hsub c' hc' c hc
    · intro v hv; exact hadd v hv c hc
    · intro c' _
      ext i
      simp [Pi.add_apply, sub_eq_add_neg, add_comm]
    · intro v _
      ext i
      simp [Pi.add_apply, Pi.sub_apply, sub_eq_add_neg, add_assoc, add_comm]
    · intro c' _; rfl
  rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]

/-- **Linear second moment.**  For a linear code `𝒞` (closed under `±`), the second moment is `|𝒞|`
times the centered ball-intersection sum:

  `∑_w (closeCount 𝒞 r w)² = |𝒞| · ∑_{v ∈ 𝒞} |B(0,r) ∩ B(v,r)|`.

Composes `sum_closeCount_sq_eq_sum_ballInterCount` with the linear reduction.  The inner sum is
the weight-enumerator second moment `∑_d A_d · I(d)` feeding the CS25 covered-fraction /
`ε_ca` bound. -/
theorem sum_closeCount_sq_eq_card_mul (𝒞 : Finset (ι → F)) (r : ℕ)
    (hsub : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a - b ∈ 𝒞)
    (hadd : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, a + b ∈ 𝒞) :
    (∑ w : ι → F, (closeCount 𝒞 r w) ^ 2)
      = 𝒞.card * ∑ v ∈ 𝒞, ballInterCount r v := by
  rw [sum_closeCount_sq_eq_sum_ballInterCount,
    sum_pair_sub_eq_card_mul 𝒞 (ballInterCount r) hsub hadd]

/-- **Two-ball intersection ≤ single-ball volume.**  `|B(0,r) ∩ B(v,r)| ≤ |B(0,r)|`, since the
intersection requires the extra constraint `Δ₀(x,v) ≤ r`.  (`ballInterCount r 0 = |B(0,r)|` is the
full ball.)  Hence the crude second-moment bound `E[N²] ≤ |𝒞|² · |B(0,r)|`. -/
theorem ballInterCount_le (r : ℕ) (v : ι → F) :
    ballInterCount r v ≤ ballInterCount r (0 : ι → F) := by
  unfold ballInterCount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.1⟩

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.sum_pair_sub_eq_card_mul
#print axioms ArkLib.CS25.sum_closeCount_sq_eq_card_mul
#print axioms ArkLib.CS25.ballInterCount_le
