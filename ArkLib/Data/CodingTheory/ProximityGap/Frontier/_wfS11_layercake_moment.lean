/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-S11 layer-cake)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_subexp_tail_to_slack

set_option linter.style.longLine false

/-!
# S11 layer-cake — DERIVING the moment envelope from a sub-exponential MGF bound

Issue lalalune/ArkLib#444 (Ethereum Proximity Prize, the char-`p` energy-transfer wall).

## What this file closes (the asserted-but-unproven layer-cake step of S11)

The S11 file `_wfS11_subexp_tail_to_slack.lean` reduced the prize to the moment envelope

  `MomentEnvelope M A c :  ∀ r ≥ 1,  M r ≤ A · r ! / c ^ r`,

and its theorem `slack_of_subexp_moment` consumes that envelope to produce the S1 slack
hypothesis with the explicit constant `K = 1/c`. But the S11 docstring's promised lemma
`moment_le_of_subexp` (point 3 — "the layer-cake core: a uniform sub-exponential survival forces
all moments bounded by `A·r!/c^r`") was **stated in prose but never carried by a theorem**: the
file *takes* `MomentEnvelope` as a hypothesis and never derives it from a one-variable concentration
object. This file supplies that missing derivation, axiom-clean and fully discretely (no measure
theory / continuous layer-cake integral).

## The discrete layer-cake, via the MGF

The clean discrete route is to integrate the survival tail into a **moment generating function**
bound. Let `t : ι → ℝ` be the normalized spectrum (`t_b = |η_b|²/n ≥ 0`) over a finite nonempty
index set `ι` of cardinality `P = p−1` (or `p`), and let

  `MGF c := (1/P) · Σ_b exp (c · t_b)`,   `M r := (1/P) · Σ_b (t_b) ^ r`.

The **sub-exponential survival** `S(s) = (1/P)·#{b : t_b ≥ s} ≤ A·e^{−c s}` (`A, c` absolute) is
*equivalent under layer-cake integration* to the MGF bound `MGF c' ≤ A·c/(c−c')` for `c' < c`; in
particular at the working rate it gives `MGF c ≤ A` (a single one-variable inequality). The two
pieces below convert that one inequality into the entire moment family with the SHARP `r!/c^r`
constant:

* `pow_le_factorial_div_pow_mul_exp` : the pointwise envelope `t^r ≤ (r!/c^r)·exp(c·t)` (`t ≥ 0`,
  `c > 0`). This is exactly `(c t)^r / r! ≤ exp(c t)` (Mathlib `pow_div_factorial_le_exp`), the
  layer-cake kernel.
* `moment_le_of_mgf` : **the layer-cake brick** — summing the pointwise envelope and dividing by
  `P` gives `M r ≤ (r!/c^r) · MGF c`, hence under `MGF c ≤ A` the envelope
  `MomentEnvelope M A c`. THIS is the S11 `moment_le_of_subexp` made into a theorem.
* `slack_of_mgf` : composes with the in-tree `slack_of_subexp_moment` to land the S1 slack
  hypothesis `CharPEnergyTransferWithSlack (fun r => n^r · M r) n (1/c)` **directly from the
  one-variable MGF bound** `MGF c ≤ 1`.

Probe-verified (`scripts/probes/probe_s11_layercake_moment.py`): for the TRUE Gauss-period spectrum
of the thin `μ_n` (`n = 2^a`, proper subgroup `(p−1)/n ≥ 2`, `p > n³`, prize regime `β ≈ 4`, NEVER
`n = q−1`), with `A(c) = sup_s S(s)·e^{c s}` the rigorously-valid tail constant (so the tail holds
for ALL `s`), the moment envelope `M_r ≤ A·r!/c^r` holds for ALL `r` tested — and the MGF
factorization `M_r ≤ (r!/c^r)·MGF(c)` matches with `MGF(c)` a valid (looser) tail constant. The
earlier two-point fit `A=0.607, c=0.669` that *appeared* to violate the envelope at small `r` was a
bad fit, NOT a math failure: the layer-cake implication holds for the genuine uniform tail constant.

## Honesty

This file proves the **layer-cake IMPLICATION** (MGF bound ⟹ moment envelope ⟹ S1 slack) axiom-
clean. It does NOT prove the MGF / survival bound itself uniformly in `n` — that uniformity IS the
BGK wall (the S11 residual `SubExpSpectralTail`, here repackaged as `MGFBound`). What is new and
real: the load-bearing analytic step the S11 reduction *asserted but never carried* is now a
theorem, with the SHARP `r!/c^r` constant, fully discretely (no continuous layer-cake integral,
no new axiom). It also makes the residual a **single scalar inequality** `MGF c ≤ A` (one variable),
which is the genuine point of the concentration lens.

Tag: CONCENTRATION-REDUCED (layer-cake step closed). Residual `MGFBound` = OPEN = BGK.
`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
-/

open Finset
open Real
open ArkLib.ProximityGap.Frontier.WFS1
open ArkLib.ProximityGap.Frontier.WFS11

namespace ArkLib.ProximityGap.Frontier.WFS11

/-! ### 1. The pointwise layer-cake kernel `t^r ≤ (r!/c^r)·exp(c·t)` -/

/-- **Pointwise layer-cake envelope.** For `c > 0` and `t ≥ 0`,
`t ^ r ≤ (r ! / c ^ r) · exp (c · t)`.
This is `(c·t)^r / r! ≤ exp (c·t)` (Mathlib `pow_div_factorial_le_exp`) rearranged: it is the kernel
that, summed over the spectrum, converts an MGF (exponential-moment) bound into the `r`-th power
moment with the sharp factorial constant. -/
theorem pow_le_factorial_div_pow_mul_exp (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) (r : ℕ) :
    t ^ r ≤ (Nat.factorial r : ℝ) / c ^ r * Real.exp (c * t) := by
  have hct : 0 ≤ c * t := mul_nonneg hc.le ht
  -- (c t)^r / r! ≤ exp (c t)
  have hkey : (c * t) ^ r / (Nat.factorial r : ℝ) ≤ Real.exp (c * t) :=
    pow_div_factorial_le_exp (c * t) hct r
  have hcr : (0 : ℝ) < c ^ r := pow_pos hc r
  have hfac : (0 : ℝ) < (Nat.factorial r : ℝ) := by exact_mod_cast Nat.factorial_pos r
  -- multiply hkey by r!/c^r ≥ 0 and simplify (c t)^r = c^r t^r
  have hmul : (c * t) ^ r / (Nat.factorial r : ℝ) * ((Nat.factorial r : ℝ) / c ^ r)
      ≤ Real.exp (c * t) * ((Nat.factorial r : ℝ) / c ^ r) := by
    apply mul_le_mul_of_nonneg_right hkey
    positivity
  -- LHS simplifies to t^r
  have hlhs : (c * t) ^ r / (Nat.factorial r : ℝ) * ((Nat.factorial r : ℝ) / c ^ r) = t ^ r := by
    rw [mul_pow]
    field_simp
  rw [hlhs] at hmul
  calc t ^ r ≤ Real.exp (c * t) * ((Nat.factorial r : ℝ) / c ^ r) := hmul
    _ = (Nat.factorial r : ℝ) / c ^ r * Real.exp (c * t) := mul_comm _ _

/-! ### 2. The MGF residual (the one-variable concentration object) -/

/-- **The S11 MGF residual** (the layer-cake-integrated form of the sub-exponential survival tail).
For a finite index family `t : ι → ℝ` (the normalized spectrum, `t_b ≥ 0`) over `s : Finset ι` with
`P` elements, `MGFBound s t A c` says the empirical moment-generating function is bounded:
`(1/P)·Σ_{b∈s} exp (c · t_b) ≤ A`. (The honest residual: `A, c` are absolute, i.e. `n,p`-uniform —
that uniformity IS the BGK wall, here as a single one-variable inequality.) -/
def MGFBound {ι : Type*} (s : Finset ι) (t : ι → ℝ) (A c : ℝ) : Prop :=
  (∑ b ∈ s, Real.exp (c * t b)) ≤ A * (s.card : ℝ)

/-! ### 3. The layer-cake brick: MGF bound ⟹ moment envelope -/

/-- **THE LAYER-CAKE BRICK (axiom-clean).** Summing the pointwise kernel
`t_b^r ≤ (r!/c^r)·exp(c·t_b)` over the spectrum and dividing by `P` gives, for the empirical moment
`M r := (1/P)·Σ_b t_b^r`,
  `M r ≤ (r!/c^r) · MGF`,
so under the sub-exponential MGF bound `(1/P)·Σ_b exp(c·t_b) ≤ A`, every moment satisfies
  `M r ≤ A · r! / c^r`,
i.e. the full `MomentEnvelope M A c`. This is the S11 docstring's promised `moment_le_of_subexp`
made a theorem — the load-bearing layer-cake step the reduction assumed but never carried. -/
theorem moment_le_of_mgf {ι : Type*} (s : Finset ι) (t : ι → ℝ) {A c : ℝ}
    (hc : 0 < c) (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c) (r : ℕ) :
    (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ) ≤ A * (Nat.factorial r : ℝ) / c ^ r := by
  have hcr : (0 : ℝ) < c ^ r := pow_pos hc r
  have hfac : (0 : ℝ) ≤ (Nat.factorial r : ℝ) := by positivity
  -- Σ t_b^r ≤ (r!/c^r) · Σ exp(c t_b)
  have hsum : (∑ b ∈ s, (t b) ^ r)
      ≤ (Nat.factorial r : ℝ) / c ^ r * (∑ b ∈ s, Real.exp (c * t b)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    exact pow_le_factorial_div_pow_mul_exp c (t b) hc (ht b hb) r
  -- chain with the MGF bound Σ exp ≤ A·P
  have hsum2 : (∑ b ∈ s, (t b) ^ r) ≤ (Nat.factorial r : ℝ) / c ^ r * (A * (s.card : ℝ)) := by
    refine le_trans hsum ?_
    apply mul_le_mul_of_nonneg_left hMGF
    positivity
  -- divide by P > 0:  (Σ t^r)/P ≤ A·r!/c^r
  rw [div_le_iff₀ hP]
  -- Goal: Σ t^r ≤ A * r! / c^r * P.  From hsum2 with a rearrangement.
  calc (∑ b ∈ s, (t b) ^ r)
      ≤ (Nat.factorial r : ℝ) / c ^ r * (A * (s.card : ℝ)) := hsum2
    _ = A * (Nat.factorial r : ℝ) / c ^ r * (s.card : ℝ) := by ring

/-- **The moment envelope is produced by the MGF bound** (clean `MomentEnvelope` packaging).
Specializing `moment_le_of_mgf` to `M r := (1/P)·Σ_b t_b^r` yields `MomentEnvelope M A c` directly,
for every `r ≥ 1` (in fact for all `r ≥ 0`). -/
theorem momentEnvelope_of_mgf {ι : Type*} (s : Finset ι) (t : ι → ℝ) {A c : ℝ}
    (hc : 0 < c) (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t A c) :
    MomentEnvelope (fun r => (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)) A c := by
  intro r _
  exact moment_le_of_mgf s t hc ht hP hMGF r

/-! ### 4. End-to-end: the one-variable MGF bound lands the S1 slack hypothesis -/

/-- **MGF ⟹ S1 slack, end to end (axiom-clean).** The single one-variable concentration inequality
`(1/P)·Σ_b exp(c·t_b) ≤ 1` (the `A = 1` MGF bound, matching the measured `MGF ≈ 1` at the working
rate) yields, via the layer-cake brick and the in-tree `slack_of_subexp_moment`, the full S1
absolute-slack energy hypothesis
  `CharPEnergyTransferWithSlack (fun r => n^r · M r) n (1/c)`
with `M r := (1/P)·Σ_b t_b^r` and the EXPLICIT constant `K = 1/c`. This is the complete S11
concentration route with the layer-cake step now CARRIED, not assumed. -/
theorem slack_of_mgf {ι : Type*} (s : Finset ι) (t : ι → ℝ) {n c : ℝ}
    (hn : 0 ≤ n) (hc : 0 < c) (hc1 : c ≤ 1)
    (ht : ∀ b ∈ s, 0 ≤ t b) (hP : 0 < (s.card : ℝ))
    (hMGF : MGFBound s t 1 c) :
    CharPEnergyTransferWithSlack
      (fun r => n ^ r * ((∑ b ∈ s, (t b) ^ r) / (s.card : ℝ))) n (1 / c) := by
  have henv : MomentEnvelope (fun r => (∑ b ∈ s, (t b) ^ r) / (s.card : ℝ)) 1 c :=
    momentEnvelope_of_mgf s t hc ht hP hMGF
  exact slack_of_subexp_moment hn hc hc1 henv

end ArkLib.ProximityGap.Frontier.WFS11
