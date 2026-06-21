/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) constraint: an argmax-decoupled functional cannot absolutely control `M(n)` (#444)

Lane-1 probe `probe_dooriv_smallball_vs_energy.py` (proper `μ_n`, `p ≫ n³`, structured incl. Fermat
primes, never `n = q-1`) measured, jointly over the full group, the small-ball / anti-concentration
coherence functional `F = C_worst(b)` and the sup-norm mass `M-functional `η(b) = |Σ_{y∈μ_n} e_p(b·y)|`:

| n   | argmax(F) = argmax(η)? | spearman(η, F) |
|-----|------------------------|----------------|
| 16  | NO                     | 0.490          |
| 32  | NO                     | 0.194          |
| 64  | NO                     | 0.113          |
| 128 | NO                     | 0.074          |
| 256 | NO                     | 0.046          |

The candidate control functional and the target have **different argmaxes at every `n`**, and their
rank-correlation **decays to zero** as `n` grows: `F` is *asymptotically decoupled* from the target.

This file records, abstractly and axiom-cleanly, *why decoupling kills a candidate control*.  It is the
sharper companion to `_DoorIVCoherenceSlackVacuousAtArgmax` (which handled the special case where the
candidate is unit-coherent, hence vacuous, at the target's argmax).  Here the candidate `F` is merely
**small** at the target's argmax `b*` (because it peaks elsewhere), and the obstruction is a clean
inequality, not a degeneracy:

* A uniform multiplicative control `target b ≤ C · F b` evaluated at the target's argmax `b*` **forces**
  `C · F b* ≥ target b*`; if moreover `F b* > 0`, it forces the explicit lower bound `C ≥ target b* / F b*`.
* Hence the control constant is **at least the per-instance witness ratio** `target(b*) / F(b*)`.  If this
  ratio is **unbounded across the family** `n` (which decoupling produces empirically — the target peaks
  where `F` is small), **no single absolute constant `C`** can control the target.  This is exactly the
  door-(iv) requirement that an anti-concentration bound control `M(n)` up to *absolute* constants.

This is a **refutation with mechanism** (a DEAD lever class, precisely mapped): it does **not** bound
`M(n)`; it shows that any functional decoupled from `M` at the worst frequency cannot, even up to
constants, serve as the door-(iv) control.  No CORE / cancellation / completion / moment / capacity claim.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl

open Finset

variable {ι : Type*}

/-- A *uniform multiplicative control* of `target` by `F` with constant `C`: at every index the target
is at most `C` times the candidate functional.  This is the abstract shape of "an anti-concentration /
small-ball functional `F` controls the sup-norm `M` up to an absolute constant". -/
def UniformControl (target F : ι → ℝ) (C : ℝ) : Prop :=
  ∀ i, target i ≤ C * F i

/-- **Control at the target's argmax forces a multiplicative lower bound on the constant.**  If `target`
is maximised at `b*` and `F` is *strictly positive* there, then any uniform multiplicative control of
`target` by `F` must use a constant `C ≥ target b* / F b*`.

This is the exact quantitative content of "a control functional must be large where the target is
large".  When `F` is *small* at the target's argmax (decoupling), this forces a large constant. -/
theorem const_ge_ratio_at_argmax {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hctrl : UniformControl target F C) (hFpos : 0 < F bstar) :
    target bstar / F bstar ≤ C := by
  have h : target bstar ≤ C * F bstar := hctrl bstar
  rw [div_le_iff₀ hFpos]
  exact h

/-- **A control constant is impossible once the witness ratio exceeds it.**  If `F b* > 0` and the
per-instance witness ratio `target b* / F b*` strictly exceeds a candidate constant `C`, then there is
**no** uniform multiplicative control of `target` by `F` with that constant `C`. -/
theorem not_uniformControl_of_ratio_gt {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hFpos : 0 < F bstar) (hgt : C < target bstar / F bstar) :
    ¬ UniformControl target F C := by
  intro hctrl
  exact absurd (const_ge_ratio_at_argmax hctrl hFpos) (not_le.2 hgt)

/-- **Family form: an unbounded witness ratio rules out every absolute constant.**  Suppose for each
member `n` of a family we have a target `target n`, a candidate functional `F n`, a worst frequency
`bstar n` where `F n (bstar n) > 0`, and the per-`n` witness ratio
`r n := target n (bstar n) / (F n) (bstar n)`.  If the family of ratios is **unbounded above** (for
every candidate constant `C` there is an `n` with `C < r n`), then **no single absolute constant `C`**
uniformly controls every member: for each `C` some member has no `C`-control.

This is the door-(iv) no-go: a functional asymptotically decoupled from `M` at the worst frequency
cannot control `M` up to *absolute* constants. -/
theorem no_absolute_constant_of_unbounded_ratio {N : Type*}
    {target F : N → ι → ℝ} {bstar : N → ι}
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ UniformControl (target n) (F n) C := by
  intro C
  obtain ⟨n, hn⟩ := hunbdd C
  exact ⟨n, not_uniformControl_of_ratio_gt (hFpos n) hn⟩

/-- **Finite-support form matching the probe.**  Over a nonempty finite frequency set `s`, with
`bstar = argmax_{b∈s} target` carrying positive target value and strictly-positive candidate value, the
control constant is at least the witness ratio.  Here `target = |η|` (the sup-norm mass), `F = C_worst`
(the small-ball functional), `bstar` the empirical argmax, all over `s ⊆ F_p*`. -/
theorem const_ge_ratio_at_finsetArgmax {target F : ι → ℝ} {C : ℝ}
    {s : Finset ι} {bstar : ι} (_hbs : bstar ∈ s)
    (_hmax : ∀ i ∈ s, target i ≤ target bstar)
    (hFpos : 0 < F bstar) (hctrl : UniformControl target F C) :
    target bstar / F bstar ≤ C :=
  const_ge_ratio_at_argmax hctrl hFpos

/-- **The control constant cannot be smaller than the observed worst ratio.**  Contrapositive packaging
for the probe: if a proposal claims an absolute constant `C` strictly below the *measured* worst-frequency
ratio `target b* / F b*` (with `F b* > 0`), the claim is false — there is no such control. -/
theorem no_control_below_measured_ratio {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hFpos : 0 < F bstar) (hbelow : C < target bstar / F bstar) :
    ¬ UniformControl target F C :=
  not_uniformControl_of_ratio_gt hFpos hbelow

end ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl
