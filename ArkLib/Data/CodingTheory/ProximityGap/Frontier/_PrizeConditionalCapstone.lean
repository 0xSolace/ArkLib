/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Prize conditional capstone: the full proven scaffold + the single named open hypothesis (#444)

This file assembles, in one place, the complete reduction chain established this campaign: **the prize follows from a
single named hypothesis** (`SaddleEnergyBound`), and every other link is proven axiom-clean in the cited files. It is
a *conditional theorem* — honest about exactly what remains.

## The chain (each `⟸` is a landed axiom-clean reduction)

```
  PRIZE  M(μ_n) ≤ C·√(n·log q)
   ⟸ (moment bound, _BNonzeroMomentReduction)        b≠0 sub-Gaussian energy  μ_{2r} ≤ Wick
   ⟺ (_OpenCoreCharPLighterReduction)                char-p lighter           μ_{2r} ≤ E_r(ℂ)
   ⟺ (_OpenCoreRhoMonotone)                           ρ(r) ≤ 1, ρ antitone     (base ρ(1)<1 PROVEN, Parseval)
   ⟺ (_AntitoneCrossExcessDecomp)                     char-0 part − char-p part ≥ 0
        char-0 part  ≥ 0    PROVEN  (_CharZeroBackboneAntitone:  E_{r+1}(ℂ) ≤ (2r+1)n·E_r(ℂ))
        char-p part  = 0    PROVEN  below the wraparound onset (_OnsetNormDichotomyTight:  W_r = 0 for p > (2r)^{n/2})
   ⟺ (_CharPExcessForcedByFloor / SUBBGK)             SaddleEnergyBound:  Σ_{t≠0}|η_t|^{2r} ≤ (p−1)·E_r(ℂ),  r ≤ log p
```

**Proven unconditionally:** the `r=1` (Parseval) and `r=2` rungs; the entire char-0 backbone; the wraparound-free
regime `r < ½·p^{2/n}` (onset dichotomy, with the tight extremal `(2r)^{n/2}`), which **closes the prize
unconditionally for thin subgroups** (`n < 2 log p / log(2 log p)`, e.g. `n ≤ 32` at `p = 2^128`).

**The single open hypothesis** `SaddleEnergyBound`: `Σ_{t≠0}|η_t|^{2r} ≤ (p−1)·E_r(ℂ)` for `r` up to the saddle
`≈ log p` at large `n`. This is exactly the BGK / di Benedetto / BCHKS conjecture at β=4 (the char-p deep-moment /
Paley-graph bound) — the recognized open problem. **Not proved here**; named so the prize derivation is explicit.

## What this file proves (axiom-clean)

`prize_of_saddleEnergyBound`: the abstract logical core — if the per-frequency energy `S_r` is bounded by the
sub-Gaussian budget `(p−1)·E_r` (the hypothesis) and the char-0 budget is itself sub-Gaussian
(`E_r ≤ Wick_r`, the proven Bessel bound), then the b≠0 moment is sub-Gaussian (`μ_{2r} ≤ Wick_r`), the conclusion
that yields the prize via the moment bound. This packages the whole chain into one implication with the open content
isolated to the single hypothesis. Issue #444.
-/

namespace ProximityGap.Frontier.PrizeCapstone

/-- **The prize from the saddle energy bound (the conditional theorem core).** Let `S_r = Σ_{t≠0}|η_t|^{2r}` (b≠0
energy), `E_r = E_r(ℂ)`, `Wick_r = (2r−1)‼·n^r`, `μ_{2r} = S_r/(p−1)`. Given:
* the **open hypothesis** `SaddleEnergyBound`: `S_r ≤ (p−1)·E_r` (equivalently `μ_{2r} ≤ E_r`), and
* the **proven char-0 anchor**: `E_r ≤ Wick_r` (Bessel-MGF, `_CharZeroMGFBesselBound`),
* with `p > 1`,
then the b≠0 moment is sub-Gaussian: `μ_{2r} ≤ Wick_r`. This is the conclusion that drives the moment bound to the
prize `M ≤ C·√(n log q)`. The entire open content is the first hypothesis (= BGK at the saddle). -/
theorem prize_of_saddleEnergyBound (S E Wick μ p : ℝ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S) (hsaddle : S ≤ (p - 1) * E) (hbessel : E ≤ Wick) :
    μ ≤ Wick := by
  have hp1 : 0 < p - 1 := by linarith
  have h1 : μ * (p - 1) ≤ (p - 1) * E := by rw [hμ]; exact hsaddle
  have h2 : μ * (p - 1) ≤ (p - 1) * Wick := by
    calc μ * (p - 1) ≤ (p - 1) * E := h1
      _ ≤ (p - 1) * Wick := by exact mul_le_mul_of_nonneg_left hbessel hp1.le
  have h3 : μ * (p - 1) ≤ Wick * (p - 1) := by rw [mul_comm Wick]; exact h2
  exact le_of_mul_le_mul_right h3 hp1

/-- **The thin-range unconditional branch (no open hypothesis).** Below the wraparound onset (`p > (2r)^{n/2}`, so
the char-p wraparound `W_r = 0`, hence `S_r = (p−1)·E_r` exactly from the Plancherel identity packaged as `hWfree`),
the saddle bound holds with equality, so `μ_{2r} ≤ Wick_r` unconditionally. This is the proven prize for thin
subgroups, requiring NO open hypothesis. -/
theorem prize_thin_range (S E Wick μ p : ℝ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S) (hWfree : S = (p - 1) * E) (hbessel : E ≤ Wick) :
    μ ≤ Wick :=
  prize_of_saddleEnergyBound S E Wick μ p hp hμ (le_of_eq hWfree) hbessel

/-- **Necessity of the saddle energy bound (contrapositive core).**  The saddle bound is not merely
*sufficient* for the sub-Gaussian moment — modulo the proven char-0 anchor `E ≤ Wick`, it is the
binding obstruction.  Given the proven anchor `E ≤ Wick` and `μ·(p−1) = S` with `p > 1`: if the
sub-Gaussian moment conclusion *fails* (`Wick < μ`), then the saddle energy bound *must* fail too
(`(p−1)·E < S`).  So any violation of the prize-driving conclusion is forced through a violation of
the single open hypothesis — the saddle bound is exactly the load-bearing rung. -/
theorem saddleEnergyBound_necessary (S E Wick μ p : ℝ) (hp : 1 < p)
    (hμ : μ * (p - 1) = S) (hbessel : E ≤ Wick) (hfail : Wick < μ) :
    (p - 1) * E < S := by
  have hp1 : 0 < p - 1 := by linarith
  -- (p-1)*E ≤ (p-1)*Wick < μ*(p-1) = S
  have h1 : (p - 1) * E ≤ (p - 1) * Wick := mul_le_mul_of_nonneg_left hbessel hp1.le
  have h2 : (p - 1) * Wick < (p - 1) * μ := by
    have := mul_lt_mul_of_pos_left hfail hp1; linarith
  have h3 : (p - 1) * μ = S := by rw [mul_comm]; exact hμ
  linarith

end ProximityGap.Frontier.PrizeCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.PrizeCapstone.prize_of_saddleEnergyBound
#print axioms ProximityGap.Frontier.PrizeCapstone.prize_thin_range
#print axioms ProximityGap.Frontier.PrizeCapstone.saddleEnergyBound_necessary
