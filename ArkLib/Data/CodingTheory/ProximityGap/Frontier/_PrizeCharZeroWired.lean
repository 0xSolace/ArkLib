import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeConditionalCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselWickAllR

/-!
# Char-0 anchor wired into the prize capstone — discharge `hbessel`

The abstract prize capstone `prize_of_saddleEnergyBound` (in `_PrizeConditionalCapstone`)
takes the char-0 anchor `hbessel : E ≤ Wick` as a FREE hypothesis. The all-`r` char-0 Wick
energy bound `besselWick_allR : besselE r m ≤ wickRHS r m` (in `_AvW0_BesselWickAllR`, proven
axiom-clean) supplies exactly that content — but lived in isolation, never instantiated into
the capstone (a wiring gap surfaced by the #444 chain audit: char-0 proven but not wired).

This leaf closes that gap: instantiating the capstone with `E := besselE r m`
(= `E_r^{char0}(μ_{2m})`, the genuine char-0 energy by the antipodal-balance Bessel identity)
and `Wick := wickRHS r m` (= `(2r−1)‼·(2m)^r`), and discharging `hbessel` via the cast of
`besselWick_allR`. The result carries the SINGLE remaining open input — the saddle energy
bound (`SaddleEnergyBound`, = BGK/Paley at β=4, the recognized open core) — and no `hbessel`.

This does NOT close the prize: the saddle bound stays an explicit open hypothesis. It only
makes the (already-proven) char-0 discharge explicit, so the moment-face of the reduction
bottoms out on exactly one open Prop. Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroWired

open ArkLib.ProximityGap.Frontier.AvW0

/-- **Char-0 anchor discharged moment capstone.** With the char-0 Bessel energy `besselE r m`
(= `E_r^{char0}(μ_{2m})`) as `E` and its proven Wick bound `wickRHS r m` (= `(2r−1)‼·(2m)^r`)
as `Wick`, the b≠0 moment `μ` is sub-Gaussian (`μ ≤ (2r−1)‼·(2m)^r`) given ONLY the saddle
energy bound `hsaddle` (BGK at β=4) and the normalization `hμ : μ·(p−1) = S`. The char-0
hypothesis is discharged here (via `besselWick_allR`), not assumed. -/
theorem prize_moment_of_saddle_charZeroWired
    (S μ p : ℝ) (r m : ℕ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S)
    (hsaddle : S ≤ (p - 1) * (besselE r m : ℝ)) :
    μ ≤ (wickRHS r m : ℝ) :=
  ProximityGap.Frontier.PrizeCapstone.prize_of_saddleEnergyBound
    S (besselE r m : ℝ) (wickRHS r m : ℝ) μ p hp hμ hsaddle
    (by exact_mod_cast besselWick_allR r m)

/-- **Necessity, char-0 discharged.** Modulo the proven char-0 anchor, the saddle energy
bound is the load-bearing rung: if the sub-Gaussian moment conclusion fails
(`wickRHS r m < μ`), the saddle bound must fail too. Discharges `hbessel` in
`saddleEnergyBound_necessary` via `besselWick_allR`. -/
theorem saddle_necessary_charZeroWired
    (S μ p : ℝ) (r m : ℕ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S) (hfail : (wickRHS r m : ℝ) < μ) :
    (p - 1) * (besselE r m : ℝ) < S :=
  ProximityGap.Frontier.PrizeCapstone.saddleEnergyBound_necessary
    S (besselE r m : ℝ) (wickRHS r m : ℝ) μ p hp hμ
    (by exact_mod_cast besselWick_allR r m) hfail

end ProximityGap.Frontier.CharZeroWired

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ProximityGap.Frontier.CharZeroWired.prize_moment_of_saddle_charZeroWired
#print axioms ProximityGap.Frontier.CharZeroWired.saddle_necessary_charZeroWired
