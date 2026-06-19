/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Door IV: the FIRST monotonicity rung of the `ρ` open core, instantiated with the EXACT
# char-0 energies (#444)

`_OpenCoreRhoMonotone.lean` reduced the prize to the antitone step `ρ(r+1) ≤ ρ(r)`, equivalently
the **abstract** char-p / char-0 energy cross-inequality `S_{r+1}·E_r ≤ S_r·E_{r+1}`, with a PROVEN
base case `ρ(1) = (p−n)/(p−1) < 1`. That file left the char-0 energies `E_r(ℂ)` abstract.

This file makes the **first rung `r = 1` fully explicit** by plugging in the two char-0 energies that
the campaign has already pinned to closed form, turning the abstract cross-inequality into one
concrete, finite open target on the single char-p quantity `S_2`.

## The two explicit char-0 energies (already in-tree, exact)

* `E_1(ℂ) = n`  — the cardinality of `μ_n` (the `r = 1` energy is `|μ_n|`, Parseval).
* `E_2(ℂ) = 3·n·(n−1)`  — the EXACT additive energy of the roots of unity, proven axiom-clean in
  `ArkLib/Data/CodingTheory/ProximityGap/RootsOfUnityEnergyExact.lean`
  (`rootsOfUnity_additiveEnergy_eq`, conditional on the clean `hnc` Diophantine no-coincidence
  hypothesis; the inert-Frobenius variant `rootsOfUnity_additiveEnergy_eq_inert` discharges `hnc`).

Probe `probe_E2_closedform.py` re-confirmed `E_2 = 3n(n−1)` EXACTLY at `n = 4,8,16,32,64`
(decomposition: multiset-equal Type-A `= 2n²−n`, nontrivial coincidences Type-B `= n(n−2)`, total
`3n²−3n`). `probe_cross_r1.py` re-confirmed the `r = 1` cross-inequality `S_2·E_1 ≤ S_1·E_2` holds
on PROPER `μ_n`, `p ≈ n⁴ ≫ n³`, multiple structured primes (incl. non-Fermat), ratio `0.996–0.9997`.

## The explicit first rung

Plug `E_1 = n`, `E_2 = 3n(n−1)`, and the PROVEN Parseval value `S_1 = p·n − n²` into the abstract
cross-inequality `S_2·E_1 ≤ S_1·E_2`:
```
        ρ(2) ≤ ρ(1)   ⟺   S_2·n ≤ (p·n − n²)·(3·n·(n−1))   ⟺   S_2 ≤ 3·n·(n−1)·(p−n).
```
So the FIRST monotonicity rung is the SINGLE explicit char-p inequality
```
        S_2 ≤ 3·n·(n−1)·(p−n)
```
on the b≠0 4th-moment period energy `S_2 = Σ_{t≠0} |η_t|⁴`. This is the exact, finite, computable
open target whose discharge would extend the proven base `ρ(1) < 1` to `ρ(2) ≤ ρ(1) < 1` — the
first step of the antitone induction `open_core_of_rho_antitone`.

## What this file proves (axiom-clean)

* `rho_step_one_iff_cross_explicit` — the `r = 1` antitone step `ρ(2) ≤ ρ(1)`, written with the
  explicit energies `E_1 = n`, `E_2 = 3n(n−1)` (for `n > 1`, so `E_2 > 0`), is equivalent to the
  explicit cross-inequality `S_2·n ≤ S_1·(3n(n−1))`.
* `cross_one_iff_S2_target` — with the Parseval value `S_1 = p·n − n²` substituted, the cross
  inequality `S_2·n ≤ S_1·(3n(n−1))` is equivalent to the single explicit target
  `S_2 ≤ 3·n·(n−1)·(p−n)` (for `n > 0`).
* `rho_step_one_target` — the chained reduction: with `S_1 = p·n − n²` and `n > 1`, the explicit
  `r = 1` antitone step `ρ(2) ≤ ρ(1)` holds **iff** `S_2 ≤ 3·n·(n−1)·(p−n)`.

SCOPE (honest): this is a REDUCTION/instantiation of the first rung of the proven `ρ`-monotonicity
chain, using two already-proven exact char-0 energies. It does NOT prove `S_2 ≤ 3n(n−1)(p−n)` (that
char-p 4th-energy bound is the open content of the first rung), does NOT prove the full antitone
chain, and makes NO CORE/cancellation/completion/moment-saving/capacity claim. The prize remains the
open wall; this pins its first explicit rung to one concrete finite inequality.

Issue #444.
-/

namespace ProximityGap.Frontier.OpenCoreRhoStepOne

/-- **The first rung with explicit energies.** With `E_1(ℂ) = n` and `E_2(ℂ) = 3n(n−1)` (both proven
exact in-tree), `p − 1 > 0`, and `n > 1` (so `E_2 = 3n(n−1) > 0`), the antitone step `ρ(2) ≤ ρ(1)` —
written as `S_2 / ((p−1)·(3n(n−1))) ≤ S_1 / ((p−1)·n)` — is equivalent to the explicit
cross-inequality `S_2·n ≤ S_1·(3n(n−1))`. This is `rho_antitone_iff_energy_cross` from
`_OpenCoreRhoMonotone` specialized to `r = 1` with the two closed-form char-0 energies plugged in. -/
theorem rho_step_one_iff_cross_explicit (S1 S2 p n : ℝ)
    (hp1 : 0 < p - 1) (hn : 1 < n) :
    (S2 / ((p - 1) * (3 * n * (n - 1))) ≤ S1 / ((p - 1) * n))
      ↔ S2 * n ≤ S1 * (3 * n * (n - 1)) := by
  have hn0 : 0 < n := by linarith
  have hE2 : 0 < 3 * n * (n - 1) := by nlinarith [hn, hn0]
  have hd1 : 0 < (p - 1) * (3 * n * (n - 1)) := by positivity
  have hd0 : 0 < (p - 1) * n := by positivity
  rw [div_le_div_iff₀ hd1 hd0]
  constructor
  · intro h; nlinarith [h, hp1, hn0, hE2]
  · intro h; nlinarith [h, hp1, hn0, hE2]

/-- **Substitute the Parseval value `S_1 = p·n − n²`.** For `n > 0`, the cross inequality
`S_2·n ≤ S_1·(3n(n−1))` with `S_1 = p·n − n²` is equivalent to the single explicit target
`S_2 ≤ 3·n·(n−1)·(p−n)`. (Divide both sides of `S_2·n ≤ (p·n−n²)·3n(n−1) = n·[3n(n−1)(p−n)]` by
`n > 0`.) -/
theorem cross_one_iff_S2_target (S2 p n : ℝ) (hn : 0 < n) :
    (S2 * n ≤ (p * n - n ^ 2) * (3 * n * (n - 1)))
      ↔ S2 ≤ 3 * n * (n - 1) * (p - n) := by
  -- (p*n - n^2)*(3n(n-1)) = (3n(n-1)(p-n)) * n; cancel the common positive factor n > 0.
  have hkey : (p * n - n ^ 2) * (3 * n * (n - 1)) = (3 * n * (n - 1) * (p - n)) * n := by ring
  rw [hkey]
  exact mul_le_mul_iff_of_pos_right hn

/-- **The first explicit rung, chained.** With the Parseval value `S_1 = p·n − n²` and `n > 1`
(prize regime, `E_2 = 3n(n−1) > 0`), the explicit `r = 1` antitone step `ρ(2) ≤ ρ(1)` holds **iff**
the single concrete char-p inequality `S_2 ≤ 3·n·(n−1)·(p−n)` holds. This pins the FIRST monotonicity
rung of the open core to one finite, computable target on the 4th-moment period energy `S_2`. -/
theorem rho_step_one_target (S2 p n : ℝ) (hp1 : 0 < p - 1) (hn : 1 < n) :
    (S2 / ((p - 1) * (3 * n * (n - 1))) ≤ (p * n - n ^ 2) / ((p - 1) * n))
      ↔ S2 ≤ 3 * n * (n - 1) * (p - n) := by
  have hn0 : 0 < n := by linarith
  rw [rho_step_one_iff_cross_explicit (p * n - n ^ 2) S2 p n hp1 hn]
  exact cross_one_iff_S2_target S2 p n hn0

end ProximityGap.Frontier.OpenCoreRhoStepOne

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreRhoStepOne.rho_step_one_iff_cross_explicit
#print axioms ProximityGap.Frontier.OpenCoreRhoStepOne.cross_one_iff_S2_target
#print axioms ProximityGap.Frontier.OpenCoreRhoStepOne.rho_step_one_target
