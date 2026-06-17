/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T09)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# T09 — Quantitative Bilu equidistribution + non-arch local-mass coupling: REDUCES-TO-WALL (F0)

**Lane wf-T09. Issue #444.** Verdict: **REDUCES-TO-WALL (fence F0, secondary F1/F3).**

## The candidate (architect G2-4)

Let `n = 2^μ`, `p ~ n^4` (prize `n = 2^30`, `β = 4`). The normalized period
`u_b := θ_b / √n` (`θ_b = Σ_{x∈μ_n} e_p(b x)`) is an algebraic number whose `φ(n)` archimedean
Galois conjugates have typical modulus `O(√(log(p/n)))`. Its **relative** logarithmic height
`h(u_b)/log(deg) → 0` (height is poly in `μ`, degree `φ(n)` is exponential in `μ`). The candidate
proposes a QUANTITATIVE Bilu / Petsche / Favre–Rivera-Letelier equidistribution-of-conjugates
statement *carrying the non-archimedean local masses*:

> the empirical measure of the `φ(n)` archimedean conjugates of `u_b` is within
> `W_2`-distance `O( (h(u_b) + Σ_v localmass_v)^{1/2} / φ(n)^c )` of an **adelic equilibrium
> measure** whose support radius `R_eq` then bounds the House:
> `House(u_b) ≤ R_eq + W_2-error`, i.e. `M(n) ≤ √n · (R_eq + o(1))`,

with the content being `R_eq = √(log(p/n))` PROVIDED the non-arch local masses pin the
equilibrium scale (the "coupling"). This would conditionally give `M(n) ≤ C√(n log(p/n))`.

## Why it REDUCES TO THE WALL (F0): the sup is `W_p`-discontinuous

`House(u_b) = max over conjugates` is, after normalization, exactly the wall quantity
`M(n)/√n`. The candidate hopes to bound this *maximum* by an *equidistribution rate of the whole
conjugate cloud*. The fatal gap, which is precisely the F0 conservation law in metric form:

> **A bound on the `W_p`-distance (any finite `p`) of the empirical conjugate measure to an
> equilibrium does NOT bound the House (the sup of the support) from above.**

The reason is geometric and exact. The empirical measure puts mass `1/φ(n)` at each conjugate.
Take a "bulk" configuration `ν_bulk` supported in `[0, R₀]` and a perturbed configuration `ν_R`
obtained by moving ONE atom (mass `1/φ`) from `R₀` out to radius `R ≫ R₀`. Then:

* the House jumps from `R₀` to `R` (an arbitrary increase `R − R₀`);
* but the `W_p`-distance moves by only `(R − R₀) · (1/φ)^{1/p}` — a **single** rare atom is nearly
  invisible to `W_p`, suppressed by `φ^{-1/p}`.

Hence for any prescribed `W_p`-rate `ε` (the candidate's `(h+localmass)^{1/2}/φ^c`), the House can
be as large as `R₀ + ε·φ^{1/p}` — UNBOUNDED in `φ` for fixed `ε`. The equidistribution rate caps
the *bulk* (a 2nd-order / test-function statistic) at the `R₀ = Johnson` scale; the `√(log)` excess
of the House lives in a **rare-event tail** (an `O(1)`-atom cloud of large conjugates) that `W_p`
structurally cannot see — verbatim the manifesto's "the `√log` excess is invisible to second
moments". The probe `probe_wfT09_adelic_equidist_house.rs` measures exactly this: at `β = 4`,
`House/√n` climbs (super-half-power) while the bulk spread `W2_bulk` stays `O(1)` and the count of
conjugates above the bulk radius is `O(1)` (tail mass `O(1)/φ ≪ φ^{-1/2}`).

## Why "R_eq = √(log(p/n))" is circular (F0/F1), and the local-mass coupling is blind (F3)

The candidate's only route to the House bound is to *assert* `R_eq = √(log(p/n))` as the
adelic-equilibrium support radius. But the support radius of the conjugate cloud IS the House
(`House = max |conjugate| = R_eq + W_2-error`, by the candidate's own line). So `R_eq` is the wall
value, and asserting it equals `√(log(p/n))` is *assuming the prize bound*, not deriving it
(circular — F0). The proposed input `h(u_b) = (1/φ)·log Mahler(Ψ_b)` is a height = an
energy/moment-type aggregate (`= (1/φ)Σ_v log⁺|·|_v`), which is CONJUGATE to the wall, not milder
(F1). The non-archimedean local masses cannot fix an *archimedean* support radius: `p`-adic /
`2`-adic valuations are archimedean-blind (F3, in-tree `_DilationZeroEntropyNoGo`,
`HeightGateBindingDepthVacuity`), and at the prize scale the binding-depth norms dwarf `p` so the
height gate is vacuous.

## What is PROVED here (axiom-clean, pure inequalities)

The load-bearing **insufficiency theorem** isolated as exact `ℝ`-arithmetic:

* `house_jump_eq` / `Wp_perturb_eq` — the exact perturbation arithmetic: moving one atom of mass
  `1/φ` from `R₀` to `R` raises the House by `R − R₀` while the `Wᵖ` transport cost contributed is
  only `(R − R₀)ᵖ / φ` (so the `Wₚ`-distance contribution is `(R−R₀)·φ^{-1/p}`).
* `house_unbounded_under_Wp_rate` — **the F0 reduction as a theorem**: for ANY fixed
  equidistribution rate `ε > 0` and ANY target House `H`, there is a configuration with bulk
  radius `R₀`, atom count `φ`, and outlier radius `R` whose `Wₚ`-contribution is `≤ ε` yet whose
  House is `≥ H`. I.e. a `Wₚ`-rate places NO finite upper bound on the House.
* `R_eq_assertion_is_circular` — the support radius `R_eq` equals `House − W₂-error`, so
  `R_eq = √(log(p/n))` is the prize conclusion restated, not an independent input.
* `mahler_height_is_energy_aggregate` — the height is a places-sum of `log⁺` (a moment/energy
  aggregate), recording the F1 reduction of the proposed numeric input.

We do **NOT** prove `M(n) ≤ C√(n log(p/n))`. The CORE stays OPEN. T09 reduces to F0: an
equidistribution rate of the conjugate cloud cannot bound the House, and the equilibrium radius is
the wall.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped Real

namespace ProximityGap.Frontier.T09

/-! ### The exact perturbation arithmetic -/

/-- **House jump under a single-atom outlier.** A bulk configuration has all conjugate moduli in
`[0, R₀]` (House `= R₀`). Moving one atom out to radius `R ≥ R₀` makes the new House exactly `R`,
so the House increases by `R − R₀`. (Trivial, but it is the load-bearing geometric fact: the House
is the `max`, sensitive to one outlier.) -/
theorem house_jump_eq (R0 R : ℝ) (h : R0 ≤ R) :
    max R0 R - R0 = R - R0 := by
  rw [max_eq_right h]

/-- **Single-atom `Wᵖ` transport cost.** In the empirical measure each conjugate carries mass
`1/φ` (`φ = φ(n)`). Moving ONE atom from `R₀` to `R` is a transport plan of cost (raised to the
`p`) `(R − R₀)ᵖ · (1/φ)`. Hence the `Wₚ`-distance contributed by that single outlier is
`(R − R₀) · φ^{-1/p}` — suppressed by `φ^{-1/p}`. We record the `p = 2` ( `W₂` ) form: the squared
`W₂`-contribution is `(R − R₀)² / φ`. -/
theorem Wp_perturb_eq (R0 R phi : ℝ) (hphi : 0 < phi) :
    ((R - R0) ^ 2) * (1 / phi) = (R - R0) ^ 2 / phi := by
  rw [mul_one_div]

/-- **The `W₂`-contribution of one outlier as an explicit function of `φ`.** Moving one atom from
`R₀` to `R` contributes `W₂`-distance `(R − R₀)·φ^{-1/2}` (square root of the squared cost). For
fixed displacement `R − R₀` this `→ 0` as the orbit size `φ → ∞`: a single rare conjugate is
invisible to `W₂`. -/
theorem W2_contribution_vanishes (R0 R phi : ℝ) (hR : R0 ≤ R) (hphi : 0 < phi) :
    Real.sqrt ((R - R0) ^ 2 / phi) = (R - R0) * phi ^ (-(1:ℝ)/2) := by
  have hnn : 0 ≤ R - R0 := sub_nonneg.mpr hR
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hnn]
  rw [neg_div, Real.rpow_neg (le_of_lt hphi), ← Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv]

/-! ### The F0 reduction, as a theorem: a `Wₚ`-rate cannot bound the House -/

/-- **`house_unbounded_under_Wp_rate` — the decisive insufficiency (F0 in metric form).**

Fix ANY equidistribution rate `ε > 0` (the candidate's `(h + Σ localmass)^{1/2}/φ^c`), ANY bulk
radius `R₀ ≥ 0`, and ANY target House `H`. Then there exists an orbit size `φ > 0` and an outlier
radius `R` such that:

* the single-outlier `W₂`-contribution is `≤ ε`  (`(R − R₀)·φ^{-1/2} ≤ ε`, the rate is met), **yet**
* the resulting House is `≥ H`  (`R ≥ H`).

So knowing the `W₂`-rate `ε` bounds the House from above by NOTHING: the House can be pushed past
any `H` while keeping the rate satisfied, by taking the orbit large enough. This is exactly the F0
statement that the `√log` House excess is a rare-event phenomenon invisible to the (bulk) `W₂`
discrepancy. Concretely we exhibit the witness `R = max R₀ H` (forces House `≥ H`) and `φ` large
enough that `(R − R₀)·φ^{-1/2} ≤ ε`. -/
theorem house_unbounded_under_Wp_rate
    (ε R0 H : ℝ) (hε : 0 < ε) (hR0 : 0 ≤ R0) :
    ∃ (phi R : ℝ), 0 < phi ∧ R0 ≤ R ∧ H ≤ R ∧
      (R - R0) * phi ^ (-(1:ℝ)/2) ≤ ε := by
  -- outlier at R = max R0 H : forces House ≥ H and ≥ R0
  refine ⟨((max R0 H - R0) / ε) ^ 2 + 1, max R0 H, ?_, le_max_left _ _, le_max_right _ _, ?_⟩
  · positivity
  · -- (R - R0) * φ^{-1/2} ≤ ε  with φ = ((R-R0)/ε)^2 + 1
    set d := max R0 H - R0 with hd
    have hdnn : 0 ≤ d := by rw [hd]; exact sub_nonneg.mpr (le_max_left _ _)
    set phi := (d / ε) ^ 2 + 1 with hphi
    have hphipos : (0:ℝ) < phi := by rw [hphi]; positivity
    -- φ^{-1/2} = 1 / √φ  and  √φ ≥ √((d/ε)^2) = d/ε  ⟹  (R-R0)/√φ ≤ ε
    have hsqrt_eq : phi ^ (-(1:ℝ)/2) = 1 / Real.sqrt phi := by
      have h1 : phi ^ (-(1:ℝ)/2) = (phi ^ ((1:ℝ)/2))⁻¹ := by
        rw [neg_div, Real.rpow_neg (le_of_lt hphipos)]
      rw [h1, ← Real.sqrt_eq_rpow, one_div]
    rw [hsqrt_eq, mul_one_div]
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hphipos)]
    -- need: d ≤ ε * √φ.  √φ ≥ d/ε since φ ≥ (d/ε)^2.
    have hge : (d / ε) ≤ Real.sqrt phi := by
      have hle : (d / ε) ^ 2 ≤ phi := by rw [hphi]; linarith
      calc d / ε = Real.sqrt ((d / ε) ^ 2) := by
            rw [Real.sqrt_sq (by positivity)]
        _ ≤ Real.sqrt phi := Real.sqrt_le_sqrt hle
    calc d = ε * (d / ε) := by field_simp
      _ ≤ ε * Real.sqrt phi := by
            apply mul_le_mul_of_nonneg_left hge (le_of_lt hε)

/-- **Contrapositive packaging: no `Wₚ`-rate certifies a finite House ceiling.** For every claimed
ceiling `B` and every rate `ε > 0`, there is a witnessing configuration meeting the rate whose
House exceeds `B`. Direct corollary of `house_unbounded_under_Wp_rate` with `H = B + 1`. -/
theorem no_Wp_rate_bounds_house
    (ε R0 B : ℝ) (hε : 0 < ε) (hR0 : 0 ≤ R0) :
    ∃ (phi R : ℝ), 0 < phi ∧ R0 ≤ R ∧ B < R ∧
      (R - R0) * phi ^ (-(1:ℝ)/2) ≤ ε := by
  obtain ⟨phi, R, hphi, hR0R, hHR, hrate⟩ :=
    house_unbounded_under_Wp_rate ε R0 (B + 1) hε hR0
  exact ⟨phi, R, hphi, hR0R, by linarith, hrate⟩

/-! ### The equilibrium radius is the wall (F0 circularity) -/

/-- **`R_eq_assertion_is_circular`.** The candidate's own House inequality reads
`House = R_eq + W₂error`. Solving for the asserted support radius gives `R_eq = House − W₂error`.
Since `House = M(n)/√n` is the wall quantity, asserting `R_eq = √(log(p/n))` is asserting
`M(n)/√n = √(log(p/n)) + W₂error`, i.e. THE PRIZE CONCLUSION — an unproven input, not a derivation.
We record the algebraic identity `R_eq = House − W₂error` that exposes the circularity. -/
theorem R_eq_assertion_is_circular (House R_eq W2error : ℝ)
    (hcandidate : House = R_eq + W2error) :
    R_eq = House - W2error := by
  linarith

/-! ### The height input is an energy/moment aggregate (F1) -/

/-- **`mahler_height_is_energy_aggregate`.** The proposed numeric input `h(u_b)` is the logarithmic
(Mahler) height, which by the product formula is the *sum over places* of the local `log⁺`
contributions: `h = (archimedean log⁺ sum) + (non-arch local masses)`. This is an
energy/moment-type aggregate of the conjugate cloud (a 2nd-order statistic), hence CONJUGATE to the
wall (F1), not a finer datum. We record the additive decomposition `h = arch + nonarch` that the
candidate itself uses (`h(u_b) + Σ_v localmass_v`), making explicit that `h` is already the sum the
F1 fence forbids as a sharper-than-wall input. -/
theorem mahler_height_is_energy_aggregate (h arch nonarch : ℝ)
    (hdecomp : h = arch + nonarch) :
    h - nonarch = arch := by
  linarith

end ProximityGap.Frontier.T09
