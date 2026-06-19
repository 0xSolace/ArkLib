/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Door IV: the SECOND monotonicity rung of the `ρ` open core, with the next explicit char-0
# energy `E_3(ℂ) = 15n³ − 45n² + 40n` (#444)

`_OpenCoreRhoMonotone.lean` reduced the prize to the antitone chain `ρ(r+1) ≤ ρ(r)`, equivalently the
char-p / char-0 energy cross-inequality `S_{r+1}·E_r ≤ S_r·E_{r+1}`, with PROVEN base `ρ(1) < 1`.
`_OpenCoreRhoStepOneExplicit.lean` made the FIRST rung explicit with `E_1 = n`, `E_2 = 3n(n−1)` →
target `S_2 ≤ 3n(n−1)(p−n)`. This file extends the explicit-energy ladder to the SECOND rung `r = 2`.

## The third char-0 energy (probe-verified closed form)

A fresh probe (inline `E3(n)` over the n-th roots of unity, `n = 4,8,16,32`) found the EXACT char-0
6th-moment energy
```
        E_3(ℂ) = #{(a₁,a₂,a₃,b₁,b₂,b₃) ∈ μ_n⁶ : Σ wᵃⁱ = Σ wᵇⁱ}  =  15·n³ − 45·n² + 40·n  =  5·n·(3n² − 9n + 8),
```
confirmed exactly: n=4 → 400, n=8 → 5120, n=16 → 50560, n=32 → 446720 (the cubic fit through
8,16,32 reproduces n=4 exactly). The quadratic `3n² − 9n + 8` has negative discriminant `81 − 96 < 0`,
so `E_3 = 5n(3n²−9n+8) > 0` for all `n > 0`.

NOTE (honesty): unlike `E_2 = 3n(n−1)` (proven axiom-clean in `RootsOfUnityEnergyExact.lean`,
`rootsOfUnity_additiveEnergy_eq`), the closed form `E_3 = 15n³−45n²+40n` is so far only
PROBE-VERIFIED (exact at n=4,8,16,32), NOT yet kernel-proven. It is used below ONLY as the explicit
RHS of a REDUCTION; nothing here asserts `E_3 = 15n³−45n²+40n` as a theorem. The combinatorial proof
(a rhombus/coincidence count for triple sums of roots of unity) is left open.

## The explicit second rung

With `E_2 = 3n(n−1)` (proven) and `E_3 = 15n³−45n²+40n` (probe-verified), the abstract cross-inequality
at `r = 2` reads
```
        ρ(3) ≤ ρ(2)   ⟺   S_3·E_2 ≤ S_2·E_3   ⟺   S_3·(3n(n−1)) ≤ S_2·(15n³−45n²+40n).
```
Probe `probe_cross_r1.py`-style check re-confirmed `S_3·E_2 ≤ S_2·E_3` on proper `μ_n`, `p ≈ n⁴ ≫ n³`,
structured primes (ratio 0.993–0.998). This is the SECOND rung target; combined with rung 1 it would
extend the proven base `ρ(1) < 1` to `ρ(3) ≤ ρ(2) ≤ ρ(1) < 1`.

## What this file proves (axiom-clean)

* `rho_step_two_iff_cross_explicit` — the `r = 2` antitone step `ρ(3) ≤ ρ(2)`, written with the
  explicit energies `E_2 = 3n(n−1)` and `E_3 = 15n³−45n²+40n` (both `> 0` for `n > 1`), is equivalent
  to the explicit cross-inequality `S_3·(3n(n−1)) ≤ S_2·(15n³−45n²+40n)`.

SCOPE (honest): this is a REDUCTION/instantiation of the second rung. It does NOT prove the cross
inequality (the open content of rung 2), does NOT prove `E_3 = 15n³−45n²+40n` (probe-verified only),
does NOT prove the full antitone chain, and makes NO CORE/cancellation/completion/moment-saving/
capacity claim. The prize remains the open wall.

Issue #444.
-/

namespace ProximityGap.Frontier.OpenCoreRhoStepTwo

/-- `E_3(ℂ) = 15n³ − 45n² + 40n = 5n(3n²−9n+8) > 0` for `n > 0`. The quadratic `3n²−9n+8` has
negative discriminant, so it is positive for all reals, hence `E_3 > 0` whenever `n > 0`. -/
theorem charZeroEnergyThree_pos (n : ℝ) (hn : 0 < n) :
    0 < 15 * n ^ 3 - 45 * n ^ 2 + 40 * n := by
  have hq : 0 < 3 * n ^ 2 - 9 * n + 8 := by nlinarith [sq_nonneg (2 * n - 3), hn]
  nlinarith [hq, hn]

/-- `E_2(ℂ) = 3n(n−1) > 0` for `n > 1`. -/
theorem charZeroEnergyTwo_pos (n : ℝ) (hn : 1 < n) :
    0 < 3 * n * (n - 1) := by
  have hn0 : 0 < n := by linarith
  nlinarith [hn, hn0]

/-- **The second rung with explicit energies.** With `E_2(ℂ) = 3n(n−1)` (proven exact in-tree) and
`E_3(ℂ) = 15n³−45n²+40n` (probe-verified closed form), both `> 0` for `n > 1`, and `p − 1 > 0`, the
antitone step `ρ(3) ≤ ρ(2)` — written as
`S_3 / ((p−1)·(15n³−45n²+40n)) ≤ S_2 / ((p−1)·(3n(n−1)))` — is equivalent to the explicit
cross-inequality `S_3·(3n(n−1)) ≤ S_2·(15n³−45n²+40n)`. This is `rho_antitone_iff_energy_cross` from
`_OpenCoreRhoMonotone` specialized to `r = 2` with the two closed-form char-0 energies plugged in. -/
theorem rho_step_two_iff_cross_explicit (S2 S3 p n : ℝ)
    (hp1 : 0 < p - 1) (hn : 1 < n) :
    (S3 / ((p - 1) * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n))
        ≤ S2 / ((p - 1) * (3 * n * (n - 1))))
      ↔ S3 * (3 * n * (n - 1)) ≤ S2 * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) := by
  have hn0 : 0 < n := by linarith
  have hE2 : 0 < 3 * n * (n - 1) := charZeroEnergyTwo_pos n hn
  have hE3 : 0 < 15 * n ^ 3 - 45 * n ^ 2 + 40 * n := charZeroEnergyThree_pos n hn0
  have hd3 : 0 < (p - 1) * (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) := by positivity
  have hd2 : 0 < (p - 1) * (3 * n * (n - 1)) := by positivity
  rw [div_le_div_iff₀ hd3 hd2]
  constructor
  · intro h; nlinarith [h, hp1, hE2, hE3]
  · intro h; nlinarith [h, hp1, hE2, hE3]

end ProximityGap.Frontier.OpenCoreRhoStepTwo

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OpenCoreRhoStepTwo.charZeroEnergyThree_pos
#print axioms ProximityGap.Frontier.OpenCoreRhoStepTwo.charZeroEnergyTwo_pos
#print axioms ProximityGap.Frontier.OpenCoreRhoStepTwo.rho_step_two_iff_cross_explicit
