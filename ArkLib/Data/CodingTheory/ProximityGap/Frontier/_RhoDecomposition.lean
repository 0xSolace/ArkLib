/-
# The exact ρ-decomposition: prize criterion = wraparound ≤ an explicit, partly-proven slack (#444)

This brick records the exact algebraic structure behind the corrected (DC-subtracted) prize criterion
`ρ_r ≤ 1`, isolating the **proven char-0 component** from the **open wraparound** in a single identity.

Setup (all over `F_p`, `n = 2^a`, depth `r`, `Wick = (2r−1)‼·n^r`):
* `E_r = E_char0 + W_r` — the char-`p` energy splits into the char-0 energy plus the wraparound `W_r ≥ 0`.
* `S_r = p·E_r − n^{2r}` — the DC-subtracted `2r`-th moment, `= Σ_{b≠0}‖η_b‖^{2r}`.
* `ρ_r = S_r / ((p−1)·Wick) = avg_{b≠0}‖η_b‖^{2r} / Wick` — the prize criterion (`ρ_r ≤ 1` ⟹ `M ≤ √e·√(2rn)`).

**Theorem `rho_le_one_iff_wraparound_le_slack`.** `ρ_r ≤ 1 ⟺ W_r ≤ slack`, where
`slack = (Wick − E_char0) + (n^{2r} − Wick)/p`.

The first summand `Wick − E_char0 = (1 − R_r)·Wick` is the **char-0 slack**, *nonnegative and proven* (the char-0
energy bound `gaussianEnergyBound_dyadic`, `R_r ≤ 1`), and — measured (`probe_rho_asymptotic`) — *growing* with
`r`, because `R_r → 0` super-geometrically (`R_r/R_{r-1}` falls `0.76→0.41` for `n=8`). The second summand is the
DC term, which at prize scale `n^{2r}/p ≫ Wick` dominates and is `≫ 0`. So the slack is large and *grows* with
depth; the open core is exactly "`W_r ≤ slack`", and the data shows `W_r` a tiny fraction of it
(`ρ_r ≈ R_r`, the wraparound perturbation `≈ 0.0007` against a slack giving `1 − ρ_r ≈ 0.33–0.64`).

This is not a closure — bounding `W_r` at deep `r ≈ log p` in the thin regime is the growing-order equidistribution
wall — but it is the cleanest exact reduction: it quarantines the proven half (the char-0 sub-Gaussian decay) and
names the open half (the wraparound) against an explicit, growing budget.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib.Tactic

namespace ProximityGap.RhoDecomposition

/-- The DC-subtracted moment `S_r = p·E_r − n^{2r}` with `E_r = E0 + W`. -/
def dcMoment (p E0 W n2r : ℝ) : ℝ := p * (E0 + W) - n2r

/-- The prize criterion ratio `ρ_r = S_r / ((p−1)·Wick)`. -/
noncomputable def rho (p E0 W n2r Wick : ℝ) : ℝ := dcMoment p E0 W n2r / ((p - 1) * Wick)

/-- The explicit slack: char-0 component `(Wick − E0)` plus the DC term `(n^{2r} − Wick)/p`. -/
noncomputable def slack (p E0 n2r Wick : ℝ) : ℝ := (Wick - E0) + (n2r - Wick) / p

/-- **The exact ρ-decomposition.**  With `p > 1` and `Wick > 0`, the corrected prize criterion `ρ_r ≤ 1`
is *equivalent* to the wraparound bound `W_r ≤ slack`, where `slack = (Wick − E0) + (n^{2r} − Wick)/p`.
This isolates the proven char-0 component `(Wick − E0) ≥ 0` from the open wraparound `W_r`. -/
theorem rho_le_one_iff_wraparound_le_slack
    (p E0 W n2r Wick : ℝ) (hp : 1 < p) (hW : 0 < Wick) :
    rho p E0 W n2r Wick ≤ 1 ↔ W ≤ slack p E0 n2r Wick := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hden : (0 : ℝ) < (p - 1) * Wick := mul_pos hp1 hW
  -- write the slack as a single fraction over `p`
  have hslack : slack p E0 n2r Wick = ((p - 1) * Wick - p * E0 + n2r) / p := by
    rw [slack]; field_simp; ring
  rw [rho, dcMoment, div_le_one hden, hslack, le_div_iff₀ hp0]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **The char-0 component is the proven, nonnegative part of the slack.**  If the char-0 energy obeys its
(proven) bound `E0 ≤ Wick` (`gaussianEnergyBound_dyadic`, i.e. `R_r ≤ 1`) and the DC term is nonnegative
(`Wick ≤ n^{2r}`, true at every depth past the DC crossover), then the slack is at least the char-0 slack
`Wick − E0 ≥ 0`.  Hence a wraparound within the char-0 slack alone already discharges the criterion. -/
theorem wraparound_within_char0_slack_suffices
    (p E0 W n2r Wick : ℝ) (hp : 1 < p) (hW : 0 < Wick)
    (hchar0 : E0 ≤ Wick) (hDC : Wick ≤ n2r) (hwrap : W ≤ Wick - E0) :
    rho p E0 W n2r Wick ≤ 1 := by
  have hp0 : (0 : ℝ) < p := lt_trans one_pos hp
  rw [rho_le_one_iff_wraparound_le_slack p E0 W n2r Wick hp hW, slack]
  have hDCnn : 0 ≤ (n2r - Wick) / p := div_nonneg (by linarith) (le_of_lt hp0)
  linarith

end ProximityGap.RhoDecomposition
