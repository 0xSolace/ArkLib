/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.EntropyVolumeBound

/-!
# Entropy lower bound on the CS25 covered-fraction ball (#82)

The covered-fraction ball `V = |{w : Δ₀(0,w) ≤ r}|` used in the CS25 argument is exactly the Hamming
ball volume `Vol_q(r/n, n)`, so the entropy lower bound `q^{n·H_q(r/n)} ≤ (n+1)·Vol` applies directly:

  `q^{n·H_q(r/n)} ≤ (n+1) · |{w : Δ₀(0,w) ≤ r}|`.

This is the entropy (rate) form of the covered-fraction ball — combined with the explicit
covered-fraction bound `rs_card_close_mul_sum_ge`, it yields the asymptotic statement that the covered
set has size `≳ |RS| · q^{n·H_q(r/n)} / ((n+1) · ∑_{d≤2r} A_d)`.
-/

namespace ArkLib.CS25

open scoped BigOperators
open CodingTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Fintype F] [DecidableEq F] [Zero F]

/-- **Entropy lower bound on the radius-`r` Hamming ball** (`q = |F| ≥ 2`, `n = |ι|`, `0 < r < n`):
`q^{n·H_q(r/n)} ≤ (n+1)·|{w : Δ₀(0,w) ≤ r}|`.  The ball is exactly `Vol_q(r/n,n)`, to which the
entropy estimate `hammingBallVolume_ge_qEntropy` applies. -/
theorem filter_ball_card_ge_qEntropy (hq : 2 ≤ Fintype.card F) (r : ℕ)
    (hr0 : 0 < r) (hrn : r < Fintype.card ι) :
    (Fintype.card F : ℝ)
        ^ ((Fintype.card ι : ℝ) * qEntropy (Fintype.card F) ((r : ℝ) / (Fintype.card ι : ℝ)))
      ≤ ((Fintype.card ι : ℝ) + 1)
        * ((Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card : ℝ) := by
  set n := Fintype.card ι with hn
  have hn0 : 0 < n := lt_trans hr0 hrn
  have hfloor : ⌊(r : ℝ) / (n : ℝ) * (n : ℝ)⌋₊ = r := by
    rw [div_mul_cancel₀ _ (by positivity : (n : ℝ) ≠ 0)]
    exact Nat.floor_natCast r
  have hV : hammingBallVolume (Fintype.card F) ((r : ℝ) / (n : ℝ)) n
      = (Finset.univ.filter (fun w : ι → F => hammingDist (0 : ι → F) w ≤ r)).card := by
    rw [hammingBallVolume_eq_ncard_hammingBall ((r : ℝ) / (n : ℝ)) (0 : ι → F), hfloor,
        ListDecodable.hammingBall, Set.ncard_eq_toFinset_card']
    congr 1
    ext x
    simp [Set.mem_toFinset]
  have hent := hammingBallVolume_ge_qEntropy hq ((r : ℝ) / (n : ℝ)) n
    (by rw [hfloor]; exact hr0) (by rw [hfloor]; exact hrn)
  rw [hfloor, hV] at hent
  exact_mod_cast hent

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.filter_ball_card_ge_qEntropy
