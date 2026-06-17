/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.RCLike.Basic

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# wf-A11 (#444): the Bourgain–Gamburd / superstrong-approximation affine envelope does NOT bound `M(n)` — an abelianness obstruction

**Angle.** The prize object `M(n) = max_{b≠0}‖η_b‖`, `η_b = ∑_{x∈μ_n} e_p(bx)`, is the
non-principal eigenvalue of the *additive* Cayley graph `Cay(F_p, μ_n)` (the generalized Paley
graph). The additive Cayley route is recorded dead (`_AttackR2_AbelianCayleyNonRamanujan`):
abelian Cayley graphs of growing degree are not Ramanujan. **This file attacks the orthogonal
hope**: package the *multiplicative dilation* action `x ↦ ux` (`u ∈ μ_n`) as a NON-abelian
envelope — the affine group `G = F_p ⋊ μ_n` — and ask whether a Bourgain–Gamburd /
superstrong-approximation spectral gap there bounds `M(n)`.

**The governing theorem (Lindenstrauss–Varjú, AFST 2016 "Spectral gap in the group of affine
transformations over prime fields", Thm 1):** for `G = F_p^d ⋊ SL_d(F_p)` and a lift `S` of a
linear generating set `S' ⊂ SL_d(F_p)`,
  `gap(G, S) ≥ c_d · min{ gap(SL_d(F_p), S'), |S|⁻¹ }`.
The Bourgain–Gamburd input `gap(SL_d(F_p), S') ≥ c` (Thm A) requires `S'` to be the reduction of
a **Zariski-dense subgroup of the PERFECT group `SL_d`, `d ≥ 2`** (quasirandomness: smallest
non-trivial irrep of `SL_2(F_p)` has dimension `(p−1)/2`).

**The obstruction.** The dilation action of `μ_n` is the `d = 1` case. There the linear part is
`SL_1 = {1}` and the "linear group" controlling the dilation is the **abelian torus** `μ_n ≤ F_p^*`.
Abelian groups have only `1`-dimensional irreducibles (no quasirandomness), so BG Thm A has no
analogue: the linear-part gap is `0`. Hence LV Thm 1 gives `gap(G,S) ≥ c·min{0, |S|⁻¹} = 0` — a
**vacuous** lower bound. The envelope is solvable/amenable, not perfect; superstrong approximation
fails by design for the multiplicative torus.

Moreover the BG *non-concentration / Fourier-flatness* input on the additive factor `F_p` is, for
the uniform measure `u` on `μ_n`, exactly `\hat u(b) = η_b/n`; its sup over `b≠0` is `M(n)/n`. So
even the input one would feed to a hypothetical affine gap **is the prize object itself** — the
route is circular.

## What this file lands (axiom-clean `ℝ`/`ℂ`-arithmetic, no Weil, no char-`p`):

1. `affine_fourier_input_eq_period` : the BG additive non-concentration input
   `\hat u(b) = (∑_{x∈μ_n} e_p(bx)) / n = η_b / n` is **definitionally** the prize Gauss period
   over `n`. So `‖\hat u(b)‖ = ‖η_b‖ / n`, and `sup_{b≠0}‖\hat u(b)‖ = M(n)/n`. (Circularity.)
2. `abelian_dilation_gap_le`        : the spectral gap of the cyclic dilation group `μ_n`
   (`gap = 1 − cos(2π/n)` for the standard symmetric generator) satisfies
   `1 − cos(2π/n) ≤ (2π/n)²/2 = 2π²/n²`. So `gap_lin → 0`: no uniform lower bound, BG cannot fire.
3. `abelian_dilation_no_uniform_gap`: for every `c > 0` there is `n` with `gap_lin(n) < c`
   (the abelian torus is NOT a uniform expander family) — the precise failure of superstrong
   approximation for the multiplicative subgroup.
4. `lv_envelope_vacuous`            : the LV Thm 1 lower bound `c·min{gap_lin, s}` is `0` when
   `gap_lin = 0`; packaged so the affine envelope yields no positive gap, hence no bound on `M`.

**Verdict: OBSTRUCTION.** The Bourgain–Gamburd / superstrong-approximation machinery does not
apply to the multiplicative dilation action: the natural non-abelian envelope (the affine group)
has an *abelian* linear part `μ_n`, whose gap collapses; and the only quantity it would control is
`M(n)/n` itself. No new control on `M(n)` is produced.
-/

open Finset Real Complex

namespace ArkLib.ProximityGap.Frontier.AffineBGGapObstruction

/-! ## 1. Circularity: the affine Fourier-flatness input IS the prize period. -/

/-- The additive character `e_p(t) = exp(2πi t / p)` as a unit complex number. -/
noncomputable def ep (p : ℕ) (t : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) / (p : ℂ))

/-- The Gauss period `η_b = ∑_{x ∈ S} e_p(b·x)` over a finite multiplicative-subgroup support `S`. -/
noncomputable def period (p : ℕ) (S : Finset ℕ) (b : ℕ) : ℂ := ∑ x ∈ S, ep p (b * x)

/-- The Fourier transform of the **uniform measure** `u` on the dilation support `S` (`|S| = n`),
evaluated at frequency `b`, is exactly the prize period divided by `n`. This is the additive
non-concentration / Fourier-flatness input the Bourgain–Gamburd machine reads on the `F_p` factor.
-/
noncomputable def affineFourierInput (p : ℕ) (S : Finset ℕ) (b : ℕ) : ℂ :=
  (period p S b) / (S.card : ℂ)

/-- **Circularity (definitional identity).** The BG additive non-concentration input
`\hat u(b)` equals the prize Gauss period `η_b` divided by `n = |S|`. Hence
`‖\hat u(b)‖ = ‖η_b‖ / n`, and the worst-case input `sup_{b≠0}‖\hat u(b)‖ = M(n)/n`: bounding the
quantity a hypothetical affine spectral gap would feed back is *exactly* bounding the prize
object. No new control is created by passing to the affine envelope. -/
theorem affine_fourier_input_eq_period (p : ℕ) (S : Finset ℕ) (b : ℕ) :
    affineFourierInput p S b * (S.card : ℂ) = period p S b := by
  unfold affineFourierInput
  by_cases h : (S.card : ℂ) = 0
  · simp only [h, mul_zero]
    -- card S = 0 ⟹ S = ∅ ⟹ period = 0
    have hcard : S.card = 0 := by exact_mod_cast h
    have hS : S = (∅ : Finset ℕ) := Finset.card_eq_zero.mp hcard
    simp [period, hS]
  · field_simp

/-- The norm form of the circularity: `‖\hat u(b)‖ = ‖η_b‖ / |S|`. The sup over `b ≠ 0` of the
LHS is `M(n)/n`; so the affine input's worst case is the prize wall over `n`. -/
theorem affine_fourier_input_norm (p : ℕ) (S : Finset ℕ) (b : ℕ) :
    ‖affineFourierInput p S b‖ = ‖period p S b‖ / (S.card : ℝ) := by
  unfold affineFourierInput
  rw [norm_div, Complex.norm_natCast]

/-! ## 2. The abelian dilation gap collapses (no Bourgain–Gamburd input). -/

/-- The spectral gap of the **cyclic** dilation group `μ_n ≅ ℤ/n` with the standard symmetric
generator `{±1}`: its non-trivial Cayley-graph eigenvalues are `cos(2πk/n)`, the largest being
`cos(2π/n)`, so the gap is `1 − cos(2π/n)`. This is the *best possible* uniform gap of the abelian
linear part — and it is the quantity entering LV Thm 1 as `gap(SL_d, S')` in the `d = 1` torus
analogue. -/
noncomputable def abelianDilationGap (n : ℕ) : ℝ := 1 - Real.cos (2 * Real.pi / n)

/-- **The abelian linear-part gap collapses as `n → ∞`.** Using `1 − cos θ ≤ θ²/2`, the cyclic
dilation gap is bounded by `2π²/n²`, hence tends to `0`. There is therefore NO uniform spectral
gap for the multiplicative-dilation linear part — the Bourgain–Gamburd input
`gap(linear part) ≥ c > 0` is unavailable for the abelian torus `μ_n`. -/
theorem abelian_dilation_gap_le (n : ℕ) (hn : 0 < n) :
    abelianDilationGap n ≤ 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by
  unfold abelianDilationGap
  -- 1 - cos θ ≤ θ²/2  with  θ = 2π/n, from  1 - θ²/2 ≤ cos θ
  have hcos : 1 - Real.cos (2 * Real.pi / n) ≤ (2 * Real.pi / n) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi / (n : ℝ))
    linarith
  refine hcos.trans ?_
  -- (2π/n)²/2 = 2π²/n²
  have heq : (2 * Real.pi / (n : ℝ)) ^ 2 / 2 = 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  rw [heq]

/-- **No uniform gap (the affine torus is not an expander family).** For every target `c > 0`
there is a dilation order `n` with `abelianDilationGap n < c`. This is the precise statement that
superstrong approximation FAILS for the multiplicative subgroup: the family `{Cay-eigengap(μ_n)}`
is not bounded below. Consequently LV Thm 1's `min{gap_lin, |S|⁻¹}` is driven to `0`. -/
theorem abelian_dilation_no_uniform_gap :
    ∀ c : ℝ, 0 < c → ∃ n : ℕ, 0 < n ∧ abelianDilationGap n < c := by
  intro c hc
  -- choose n with 2π²/n² < c, i.e. n > π√(2/c); take n ≥ that
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt (2 * Real.pi ^ 2 / c))
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  have hn : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hbound : abelianDilationGap (N + 1) ≤ 2 * Real.pi ^ 2 / ((N + 1 : ℕ) : ℝ) ^ 2 :=
    abelian_dilation_gap_le (N + 1) (Nat.succ_pos N)
  refine hbound.trans_lt ?_
  -- 2π²/n² < c  ⟺  n² > 2π²/c  ⟺  n > √(2π²/c)
  rw [div_lt_iff₀ (by positivity)]
  have hsqrt : Real.sqrt (2 * Real.pi ^ 2 / c) < ((N + 1 : ℕ) : ℝ) := by
    push_cast
    have : Real.sqrt (2 * Real.pi ^ 2 / c) < (N : ℝ) := hN
    linarith
  have hpos : 0 ≤ Real.sqrt (2 * Real.pi ^ 2 / c) := Real.sqrt_nonneg _
  -- square both sides:  2π²/c < n²
  have hsq : 2 * Real.pi ^ 2 / c < (((N + 1 : ℕ) : ℝ)) ^ 2 := by
    have h1 : (Real.sqrt (2 * Real.pi ^ 2 / c)) ^ 2 = 2 * Real.pi ^ 2 / c :=
      Real.sq_sqrt (by positivity)
    calc 2 * Real.pi ^ 2 / c = (Real.sqrt (2 * Real.pi ^ 2 / c)) ^ 2 := h1.symm
      _ < (((N + 1 : ℕ) : ℝ)) ^ 2 := by
          apply sq_lt_sq' <;> [linarith; linarith]
  -- 2π² < c · n²
  rw [div_lt_iff₀ hc] at hsq
  linarith [hsq]

/-! ## 3. The Lindenstrauss–Varjú envelope is vacuous for the abelian linear part. -/

/-- The Lindenstrauss–Varjú Theorem 1 lower bound on the affine spectral gap, as a function of the
linear-part gap `gLin`, the inverse generating-set size `sInv`, and the universal constant `c`:
`c · min{gLin, sInv}`. (We package only the *bound's value*, not the dynamics; the content here is
purely that this value is `0` when `gLin = 0`.) -/
noncomputable def lvLowerBound (c gLin sInv : ℝ) : ℝ := c * min gLin sInv

/-- **The affine envelope gives no gap when the linear part is abelian.** If the linear-part gap is
`0` (as it is for the abelian dilation torus `μ_n`, in the limit / for no uniform constant), the
Lindenstrauss–Varjú lower bound `c·min{gLin, sInv}` is `≤ 0` (it is `0` for `sInv ≥ 0`). So the
affine envelope produces no positive spectral gap, hence cannot certify any nontrivial bound on the
mixing of the affine walk — and therefore none on `M(n)`. -/
theorem lv_envelope_vacuous (c sInv : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ sInv) :
    lvLowerBound c 0 sInv = 0 := by
  unfold lvLowerBound
  rw [min_eq_left (le_trans (le_refl 0) hs)]
  · ring

/-- **Synthesis: the BG/superstrong route yields no bound on `M(n)`.** Combining 2+3: since for any
candidate uniform gap constant `c₀ > 0` there is `n` with the abelian dilation gap below `c₀`
(`abelian_dilation_no_uniform_gap`), the LV lower bound at that `n` (with `gLin := 0` in the limit)
is `0` (`lv_envelope_vacuous`). The affine envelope of the multiplicative dilation action is
solvable with abelian linear part; Bourgain–Gamburd / superstrong approximation does not apply, and
the only quantity it would feed back is `M(n)/n` (`affine_fourier_input_norm`). No new control on
`M(n)` is obtained: this angle is an obstruction, not a lever. -/
theorem bg_route_no_bound_on_M :
    (∀ c₀ : ℝ, 0 < c₀ → ∃ n : ℕ, 0 < n ∧ abelianDilationGap n < c₀) ∧
    (∀ c sInv : ℝ, 0 ≤ c → 0 ≤ sInv → lvLowerBound c 0 sInv = 0) :=
  ⟨abelian_dilation_no_uniform_gap, lv_envelope_vacuous⟩

end ArkLib.ProximityGap.Frontier.AffineBGGapObstruction

open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms affine_fourier_input_eq_period
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms affine_fourier_input_norm
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms abelian_dilation_gap_le
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms abelian_dilation_no_uniform_gap
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms lv_envelope_vacuous
open ArkLib.ProximityGap.Frontier.AffineBGGapObstruction in
#print axioms bg_route_no_bound_on_M
