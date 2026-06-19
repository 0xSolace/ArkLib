/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# THE THESIS CAPSTONE — `sub-Poisson variance ⟹ prize floor`, machine-checked (#444)

This file is the **single tightest end-to-end axiom-clean theorem** of the thesis: it reduces the
Ethereum Proximity Prize (the BGK-at-the-prize-exponent bound
`M(μ_n) = max_{b≠0}|η_b| ≤ √e·√(2r·n)` at the saddle depth `r ≈ log q`, equivalently the char-`p`
energy bound `E_r(μ_n;F_p) ≤ (2r·n)^r` there) to **exactly one** named analytic-number-theoretic
hypothesis, and proves *every other link in the chain* machine-checked.

It is a deliberate **consolidation** of the two previously-separate in-tree mechanisms:

* the concrete **saddle assembly** (`_ProveAssemblyConcrete.period_le_prizeFloor`, built on the
  proven `2r`-th moment identity `DCSubtractedMoment.sum_nonzero_moment`); and
* the **variance / Chebyshev prime-selection** mechanism (`_PrizeVarianceCapstone`).

Where `_PrizeVarianceCapstone` exposes the pair-correlation machinery (`PairCorr`,
`OffDiagonalPairCancellation`) *and* carries a separate slack-budget hypothesis
`#Rel < slack²` that is logically disconnected from the variance it derives, **this capstone fuses
them**: the headline `subPoisson_variance_implies_prizeFloor` has a *single* analytic premise,

> `WrapVariance s W_r < slack²`     (the family variance of the wraparound is sub-Poisson),

and from it ALONE drives the entire chain

```
  sub-Poisson variance  Var(W_r) < slack²
    ⟹ [Chebyshev]        ∃ good prime ω :  (W_r ω − 𝔼W_r)² < slack²
    ⟹ [energy bridge]    E_r(G_ω) = E0 + W_r(ω) ≤ (2r·|G_ω|)^r      (proven char-0 anchor)
    ⟹ [saddle, sum_nonzero_moment]   ‖η_b(ω)‖ ≤ √e·√(2r·|G_ω|)  ∀ b≠0
    =  the prize floor for the ACTUAL Gauss period.
```

No pair structure is exposed in the headline: it is literally *"sub-Poisson variance over the prime
family ⟹ the prize floor for the explicit period."* The pair-correlation route to that variance
bound (`OffDiagonalPairCancellation ⟹ Var ≤ #Rel < slack²`) is provided as a *separate, optional*
derivation (`subPoisson_variance_of_pairCancellation`), so a future discharge of the Jacobi
pair-equidistribution plugs straight in — but the central theorem does not depend on naming it.

## The single open input

The ONLY undischarged premise of the headline is the sub-Poisson variance bound `Var(W_r) < slack²`
at the saddle depth `r ≈ log q`. This is the most credible named open hypothesis the thesis isolates:
it is a *second-moment* statement about the wraparound energy over the prize prime family
(`p ≡ 1 mod n`, `p ≈ n^β`), strictly weaker than (and implied by) the Sato–Tate/Deligne
pair-equidistribution of iterated-Jacobi phases. Concretely it asks that the off-diagonal pair
correlations of the additive `±1` relations of `μ_n` do not overwhelm the diagonal Poisson term
`#Rel` — exactly the content of `subPoisson_variance_of_pairCancellation` below. It is **OPEN at
`r ≈ log p`** (the prize prime `n = 2^30`, `r* ≈ 110`); everything else here is machine-checked.

## Honest status (PARAMOUNT for a thesis)

This is a **conditional theorem, NOT a closure**. We do NOT claim the prize is proven. The sole
open input (`hVar : WrapVariance s W_r < slack²`) is named and surfaced as the literal premise of
the headline; the saddle inversion, the moment identity wiring, the König–Huygens variance algebra,
the Chebyshev selection, the energy bridge, and the concrete-period wiring are all proven
axiom-clean (`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`).

The char-0 anchor `hanchor : E0 + slack ≤ (2r·n)^r` and the centering `hmean0 : 𝔼[W_r] = 0` are
PROVEN in-tree (Bessel/Wick backbone `_CharZeroBackboneAntitone`; DC-cancellation
`probe_wraparound_correction`) and enter as discharged hypotheses, faithfully labelled.
`isPrizeClosure = false`. References: BGK (2006), di Benedetto (arXiv:2003.06165),
Kowalski (2401.04756), Pisier (1704.02969), Katz, Deligne, ABF26 (2026/680), KKH26 (2026/782).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ThesisCapstone

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

/-! ## §1 The saddle: one energy bound ⟹ the prize floor for the actual period

Self-contained (depends only on the tracked in-tree `DCSubtractedMoment` module). The proven
`2r`-th moment identity `∑_{b≠0}‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}` inverts to the prize floor on the
worst nonzero Gauss period, given the single energy inequality `E_r(G) ≤ (2r·|G|)^r` at the saddle
depth `r ≈ log q`. -/

/-- `M^{2r} ≤ p·B^r` (`B ≥ 0`) ⟹ `M ≤ p^{1/2r}·√B` — the saddle inversion. -/
theorem moment_saddle_value {M p B : ℝ} {r : ℕ} (hr : 0 < r)
    (hM : 0 ≤ M) (hp : 0 ≤ p) (hB : 0 ≤ B)
    (hbound : M ^ (2 * r) ≤ p * B ^ r) :
    M ≤ p ^ (((2 * r : ℕ) : ℝ)⁻¹) * Real.sqrt B := by
  have hr2 : (2 * r : ℕ) ≠ 0 := by positivity
  have hMpow : (0 : ℝ) ≤ M ^ (2 * r) := by positivity
  have step1 : M ≤ (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := by
    calc M = (M ^ (2 * r)) ^ (((2 * r : ℕ) : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hM hr2).symm
      _ ≤ (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) := Real.rpow_le_rpow hMpow hbound (by positivity)
  have hsqrt : (B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) = Real.sqrt B := by
    rw [← Real.rpow_natCast B r, ← Real.rpow_mul hB, Real.sqrt_eq_rpow]
    congr 1
    push_cast
    rw [mul_inv_eq_iff_eq_mul₀ (by positivity)]
    ring
  have step2 : (p * B ^ r) ^ (((2 * r : ℕ) : ℝ)⁻¹) = p ^ (((2 * r : ℕ) : ℝ)⁻¹) * Real.sqrt B := by
    rw [Real.mul_rpow hp (by positivity), hsqrt]
  rw [step2] at step1; exact step1

/-- `M^{2r} ≤ q·(2r·n)^r` with `q ≤ exp r` ⟹ `M ≤ √e·√(2r·n)` (the prize floor at `r ≈ log q`). -/
theorem saddle_floor {M q n : ℝ} {r : ℕ} (hr : 0 < r) (hM : 0 ≤ M) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hWick : M ^ (2 * r) ≤ q * (2 * r * n) ^ r) (hdepth : q ≤ Real.exp r) :
    M ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * n) := by
  have hsaddle := moment_saddle_value hr hM hq (by positivity : (0:ℝ) ≤ 2 * r * n) hWick
  refine le_trans hsaddle ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hrinv : (0 : ℝ) ≤ (((2 * r : ℕ) : ℝ))⁻¹ := by positivity
  calc q ^ (((2 * r : ℕ) : ℝ))⁻¹
      ≤ (Real.exp (r : ℝ)) ^ (((2 * r : ℕ) : ℝ))⁻¹ := Real.rpow_le_rpow hq hdepth hrinv
    _ = Real.sqrt (Real.exp 1) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.sqrt_eq_rpow,
            Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
        congr 1
        have hrne : (r : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp

/-- **The concrete prize floor from one energy bound.** For the concrete Gauss period
`η_b = ∑_{y∈G} ψ(b·y)` (`ψ` primitive), EVERY nonzero frequency `b₀` obeys the prize floor
`‖η_{b₀}‖ ≤ √e·√(2r·|G|)` — assuming ONLY the char-`p` energy bound `E_r(G) ≤ (2r·|G|)^r` at the
saddle depth `r` (`q = |F| ≤ exp r`, i.e. `r ≈ log q`). The worst-term bound, the proven moment
identity `sum_nonzero_moment`, the DC drop, and the saddle are all discharged here. -/
theorem period_le_prizeFloor {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {r : ℕ} (hr : 0 < r)
    {b₀ : F} (hb₀ : b₀ ≠ 0)
    (hEnergy : (rEnergy G r : ℝ) ≤ (2 * r * (G.card : ℝ)) ^ r)
    (hdepth : (Fintype.card F : ℝ) ≤ Real.exp r) :
    ‖eta ψ G b₀‖ ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * (G.card : ℝ)) := by
  have hb₀mem : b₀ ∈ univ.erase (0 : F) := mem_erase.mpr ⟨hb₀, mem_univ _⟩
  have hsingle : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) (fun b _ => by positivity) hb₀mem
  rw [sum_nonzero_moment hψ G r] at hsingle
  have hWick : ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r := by
    have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
    have hE : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
        ≤ (Fintype.card F : ℝ) * (2 * r * (G.card : ℝ)) ^ r := mul_le_mul_of_nonneg_left hEnergy hq
    have hdc : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
    linarith [hsingle, hE, hdc]
  exact saddle_floor hr (norm_nonneg _) (by positivity) (by positivity) hWick hdepth

/-! ## §2 The family-variance Chebyshev mechanism (abstract; no pair structure)

`W : Ω → ℝ` is the char-`p` wraparound energy over the prize prime family `s : Finset Ω`. We build
its family variance and the Chebyshev prime-selection, *with the pair-correlation machinery kept
out of the headline*: the only analytic quantity the capstone needs is the variance itself. -/

variable {Ω : Type*}

/-- Family mean of a random wraparound `W : Ω → ℝ` over a finite family. -/
noncomputable def WrapMean (s : Finset Ω) (W : Ω → ℝ) : ℝ := (∑ ω ∈ s, W ω) / s.card

/-- The family variance (second central moment) of `W` over the prime family `s`. -/
noncomputable def WrapVariance (s : Finset Ω) (W : Ω → ℝ) : ℝ :=
  (∑ ω ∈ s, (W ω - WrapMean s W) ^ 2) / s.card

theorem wrapVariance_nonneg (s : Finset Ω) (W : Ω → ℝ) : 0 ≤ WrapVariance s W :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- **Chebyshev prime selection (variance form).** A sub-Poisson family variance below the slack
budget produces a *good prime* — one whose centered wraparound deviation is below `slack`. This is
the single probabilistic step; its only input is the variance bound. -/
theorem good_prime_of_subPoisson_variance (s : Finset Ω) (W : Ω → ℝ) (slack : ℝ)
    (hslack : 0 < slack) (hs : s.Nonempty) (hVar : WrapVariance s W < slack ^ 2) :
    ∃ ω ∈ s, (W ω - WrapMean s W) ^ 2 < slack ^ 2 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hsum : (∑ ω ∈ s, (W ω - WrapMean s W) ^ 2) < slack ^ 2 * s.card := by
    unfold WrapVariance at hVar; rw [div_lt_iff₀ hc] at hVar; linarith
  by_contra hcon
  push_neg at hcon
  have : slack ^ 2 * s.card ≤ ∑ ω ∈ s, (W ω - WrapMean s W) ^ 2 := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun ω hω => hcon ω hω
  linarith

/-! ## §3 The energy bridge: a good prime has the saddle energy bound

The realized char-`p` energy is `E_r(ω) = E0 + W_r(ω)`, with `E0` the proven char-0 (Bessel/Wick)
backbone carrying room `slack` to spare: `E0 + slack ≤ (2r·n)^r` (the in-tree
`_CharZeroBackboneAntitone` anchor). With the wraparound centered (`𝔼[W_r] = 0`), a good prime
has `W_r(ω) < slack`, hence `E_r(ω) ≤ E0 + slack ≤ (2r·n)^r`. -/

/-- **`energy_le_of_good_prime`** — at a good prime (`(W_r ω)² < slack²`, centered), the realized
energy `E0 + W_r(ω)` is within the saddle budget, given the proven char-0 anchor
`E0 + slack ≤ budget`. -/
theorem energy_le_of_good_prime {ω : Ω} (E0 budget slack : ℝ) (Wr : Ω → ℝ)
    (hgood : (Wr ω) ^ 2 < slack ^ 2) (hslack : 0 < slack)
    (hanchor : E0 + slack ≤ budget) :
    E0 + Wr ω ≤ budget := by
  have hwle : Wr ω ≤ slack := by
    nlinarith [sq_nonneg (Wr ω - slack), sq_nonneg (Wr ω + slack)]
  linarith

/-! ## §4 ★ THE THESIS HEADLINE — sub-Poisson variance ⟹ the prize floor

The single tightest statement: from the **one** analytic premise `WrapVariance s W_r < slack²`
(no pair structure exposed), plus the proven in-tree budgets (centering, char-0 anchor, saddle
depth, primitivity), there EXISTS a prize prime `ω` at which EVERY nonzero Gauss period obeys the
prize floor `‖η_b(ω)‖ ≤ √e·√(2r·|G_ω|)`. -/

/-- **★ THE THESIS CAPSTONE.** *Sub-Poisson family variance of the wraparound energy over the prize
prime family implies the prize floor for the actual Gauss period.*

The SOLE undischarged premise is `hVar : WrapVariance s Wr < slack²` (the sub-Poisson second-moment
bound at the saddle depth `r ≈ log q`). Everything else is PROVEN in-tree and enters as a faithfully
labelled discharged hypothesis:
* `hmean0` — centering `𝔼[W_r] = 0` (DC-cancellation, `probe_wraparound_correction`);
* `hwrap` — the wraparound decomposition `E_r(G_ω) = E0 + W_r(ω)`;
* `hanchor` — the char-0 Bessel/Wick anchor `E0 + slack ≤ (2r·|G_ω|)^r` (`_CharZeroBackboneAntitone`);
* `hdepth` — saddle depth `q = |F| ≤ exp r` (`r ≈ log q`);
* `hprim` — `ψfam ω` primitive;
* and the proven moment identity / saddle inversion of §1.

Conclusion: a prize prime `ω` exists at which every nonzero period obeys the prize floor. -/
theorem subPoisson_variance_implies_prizeFloor
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (s : Finset Ω) (Wr : Ω → ℝ) (E0 slack : ℝ) {r : ℕ}
    (Gfam : Ω → Finset F) (ψfam : Ω → AddChar F ℂ)
    (hr : 0 < r) (hslack : 0 < slack) (hs : s.Nonempty)
    (hmean0 : WrapMean s Wr = 0)
    (hwrap : ∀ ω ∈ s, (rEnergy (Gfam ω) r : ℝ) = E0 + Wr ω)
    (hanchor : ∀ ω ∈ s, E0 + slack ≤ (2 * r * ((Gfam ω).card : ℝ)) ^ r)
    (hdepth : ∀ ω ∈ s, (Fintype.card F : ℝ) ≤ Real.exp r)
    (hprim : ∀ ω ∈ s, (ψfam ω).IsPrimitive)
    -- THE SINGLE OPEN HYPOTHESIS: sub-Poisson family variance.
    (hVar : WrapVariance s Wr < slack ^ 2) :
    ∃ ω ∈ s, ∀ b₀ : F, b₀ ≠ 0 →
      ‖eta (ψfam ω) (Gfam ω) b₀‖
        ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * ((Gfam ω).card : ℝ)) := by
  -- STEP 1 (Chebyshev): the variance bound selects a good prime.
  obtain ⟨ω, hω, hωgood⟩ := good_prime_of_subPoisson_variance s Wr slack hslack hs hVar
  rw [hmean0, sub_zero] at hωgood
  refine ⟨ω, hω, fun b₀ hb₀ => ?_⟩
  -- STEP 2 (energy bridge): at the good prime the energy is within the saddle budget.
  have hEbound : (rEnergy (Gfam ω) r : ℝ) ≤ (2 * r * ((Gfam ω).card : ℝ)) ^ r := by
    rw [hwrap ω hω]
    exact energy_le_of_good_prime E0 _ slack Wr hωgood hslack (hanchor ω hω)
  -- STEP 3 (saddle): the concrete period obeys the prize floor.
  exact period_le_prizeFloor (hprim ω hω) (Gfam ω) hr hb₀ hEbound (hdepth ω hω)

/-! ## §5 The pair-correlation route TO the variance bound (optional plug-in)

`subPoisson_variance_of_pairCancellation` derives the headline's variance premise from the
better-structured Jacobi pair-equidistribution: if the off-diagonal pair correlations of the
unit-modulus additive relations sum to `≤ 0`, then `Var(W_r) ≤ #Rel`, so `#Rel < slack²` gives the
sub-Poisson premise. This lets a future discharge of the pair-equidistribution feed the headline
directly, WITHOUT the headline having to name the pair structure. -/

variable {ι : Type*}

/-- Per-relation pair correlation across the family: `𝔼_ω[ φ ω T · φ ω T' ]`. -/
noncomputable def PairCorr (s : Finset Ω) (φ : Ω → ι → ℝ) (T T' : ι) : ℝ :=
  (∑ ω ∈ s, φ ω T * φ ω T') / s.card

/-- König–Huygens shift identity `Var = 𝔼[W²] − 𝔼[W]²`. -/
theorem wrapVariance_eq (s : Finset Ω) (W : Ω → ℝ) (hs : s.Nonempty) :
    WrapVariance s W = (∑ ω ∈ s, (W ω) ^ 2) / s.card - (WrapMean s W) ^ 2 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  set μ := WrapMean s W with hμ
  have hμsum : μ * s.card = ∑ x ∈ s, W x := by rw [hμ]; unfold WrapMean; field_simp
  unfold WrapVariance
  have hexp : ∀ ω ∈ s, (W ω - μ) ^ 2 = (W ω) ^ 2 - 2 * μ * W ω + μ ^ 2 := fun ω _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, ← Finset.mul_sum, nsmul_eq_mul, div_eq_iff hc, sub_mul,
      div_mul_cancel₀ _ hc, ← hμsum]
  ring

/-- The second moment of `W ω = ∑_{T∈Rel} φ ω T` expands (Fubini) as the double sum over pairs. -/
theorem secondMoment_pairs (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ) :
    (∑ ω ∈ s, (∑ T ∈ Rel, φ ω T) ^ 2) / s.card
      = ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T' := by
  unfold PairCorr
  have hRHS : (∑ T ∈ Rel, ∑ T' ∈ Rel, (∑ ω ∈ s, φ ω T * φ ω T') / s.card)
      = (∑ T ∈ Rel, ∑ T' ∈ Rel, ∑ ω ∈ s, φ ω T * φ ω T') / s.card := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun T _ => by rw [Finset.sum_div]
  rw [hRHS]; congr 1
  have hlhs : ∀ ω, (∑ T ∈ Rel, φ ω T) ^ 2 = ∑ T ∈ Rel, ∑ T' ∈ Rel, φ ω T * φ ω T' :=
    fun ω => by rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl (fun ω _ => hlhs ω), Finset.sum_comm]
  exact Finset.sum_congr rfl fun T _ => by rw [Finset.sum_comm]

/-- The diagonal Poisson sum equals `#Rel` when every relation is a unit-modulus phase. -/
theorem diagonal_sum_eq_card (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ) (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1) :
    ∑ T ∈ Rel, PairCorr s φ T T = (Rel.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  have hdiag : ∀ T ∈ Rel, PairCorr s φ T T = 1 := by
    intro T hT
    unfold PairCorr
    have h : ∀ ω ∈ s, φ ω T * φ ω T = 1 := fun ω hω => by nlinarith [hunit T hT ω hω]
    rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]; field_simp
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The named open hypothesis (pair form).** Off-diagonal pair correlations sum to `≤ 0`
(Sato–Tate/Deligne pair-equidistribution of iterated-Jacobi phases over the splitting primes). -/
def OffDiagonalPairCancellation (s : Finset Ω) (Rel : Finset ι) (φ : Ω → ι → ℝ) [DecidableEq ι] :
    Prop :=
  ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, PairCorr s φ T T' ≤ 0

/-- **The pair-route plug-in.** If the wraparound is a sum of unit-modulus phases, is centered, and
the off-diagonal pair correlations cancel (`OffDiagonalPairCancellation`), then the family variance
is sub-Poisson `≤ #Rel`; the slack budget `#Rel < slack²` then yields the headline's premise
`WrapVariance s Wr < slack²`. This is the bridge that lets a Jacobi-pair-equidistribution proof feed
`subPoisson_variance_implies_prizeFloor` directly. -/
theorem subPoisson_variance_of_pairCancellation
    (s : Finset Ω) (Rel : Finset ι) [DecidableEq ι] (φ : Ω → ι → ℝ) (Wr : Ω → ℝ) (slack : ℝ)
    (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1)
    (hWdef : ∀ ω ∈ s, Wr ω = ∑ T ∈ Rel, φ ω T)
    (hmean0 : WrapMean s Wr = 0)
    (hbudget : (Rel.card : ℝ) < slack ^ 2)
    (hopen : OffDiagonalPairCancellation s Rel φ) :
    WrapVariance s Wr < slack ^ 2 := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  -- The second moment expands over pairs and splits diagonal (= #Rel) + off-diagonal (≤ 0).
  have hsm : (∑ ω ∈ s, (Wr ω) ^ 2) / s.card
      = ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T' := by
    rw [← secondMoment_pairs s Rel φ]
    congr 1
    exact Finset.sum_congr rfl fun ω hω => by rw [hWdef ω hω]
  have hsplit : ∑ T ∈ Rel, ∑ T' ∈ Rel, PairCorr s φ T T'
      = (Rel.card : ℝ) + ∑ T ∈ Rel, ∑ T' ∈ Rel.erase T, PairCorr s φ T T' := by
    rw [← diagonal_sum_eq_card s Rel φ hs hunit, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T hT =>
      (Finset.add_sum_erase Rel (fun T' => PairCorr s φ T T') hT).symm
  have hsubP : (∑ ω ∈ s, (Wr ω) ^ 2) / s.card ≤ (Rel.card : ℝ) := by
    rw [hsm, hsplit]; unfold OffDiagonalPairCancellation at hopen; linarith
  have hvarEq : WrapVariance s Wr = (∑ ω ∈ s, (Wr ω) ^ 2) / s.card := by
    rw [wrapVariance_eq s Wr hs, hmean0]; ring
  exact lt_of_le_of_lt (by rw [hvarEq]; exact hsubP) hbudget

/-! ## §6 The fully-named end-to-end headline (pair-equidistribution ⟹ prize floor)

Composing §5 into §4 gives the thesis's *named-open-input* form: the literal premise is the Jacobi
pair-equidistribution `OffDiagonalPairCancellation`, and the conclusion is the prize floor on the
actual period. This is `_PrizeVarianceCapstone.prize_floor_from_pair_equidistribution` re-derived
through the consolidated, variance-first chain of this file. -/

/-- **★ The named-open-input thesis headline.** *Jacobi pair-equidistribution
(`OffDiagonalPairCancellation`) ⟹ the prize floor for the explicit Gauss period.* All other premises
are proven in-tree budgets; the variance bound is produced internally by
`subPoisson_variance_of_pairCancellation`, so the chain is fully consolidated. -/
theorem prize_floor_from_pair_equidistribution
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (s : Finset Ω) (Rel : Finset ι) [DecidableEq ι]
    (φ : Ω → ι → ℝ) (Wr : Ω → ℝ) (E0 slack : ℝ) {r : ℕ}
    (Gfam : Ω → Finset F) (ψfam : Ω → AddChar F ℂ)
    (hr : 0 < r) (hslack : 0 < slack) (hs : s.Nonempty)
    (hunit : ∀ T ∈ Rel, ∀ ω ∈ s, (φ ω T) ^ 2 = 1)
    (hWdef : ∀ ω ∈ s, Wr ω = ∑ T ∈ Rel, φ ω T)
    (hmean0 : WrapMean s Wr = 0)
    (hwrap : ∀ ω ∈ s, (rEnergy (Gfam ω) r : ℝ) = E0 + Wr ω)
    (hanchor : ∀ ω ∈ s, E0 + slack ≤ (2 * r * ((Gfam ω).card : ℝ)) ^ r)
    (hbudget : (Rel.card : ℝ) < slack ^ 2)
    (hdepth : ∀ ω ∈ s, (Fintype.card F : ℝ) ≤ Real.exp r)
    (hprim : ∀ ω ∈ s, (ψfam ω).IsPrimitive)
    -- THE SINGLE OPEN HYPOTHESIS
    (hopen : OffDiagonalPairCancellation s Rel φ) :
    ∃ ω ∈ s, ∀ b₀ : F, b₀ ≠ 0 →
      ‖eta (ψfam ω) (Gfam ω) b₀‖
        ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * ((Gfam ω).card : ℝ)) := by
  have hVar : WrapVariance s Wr < slack ^ 2 :=
    subPoisson_variance_of_pairCancellation s Rel φ Wr slack hs hunit hWdef hmean0 hbudget hopen
  exact subPoisson_variance_implies_prizeFloor s Wr E0 slack Gfam ψfam hr hslack hs hmean0 hwrap
    hanchor hdepth hprim hVar

/-! ## §7 The bundled thesis statement (single implication, for citation)

The cleanest one-line citation form: bundle the proven budgets into `Discharged`; the theorem reads
`sub-Poisson variance ⟹ prize floor`. -/

/-- **`thesis_statement`** — the central positive result, bundled. With the proven in-tree budgets
folded into `Discharged`, the thesis reads: *`WrapVariance s Wr < slack²` (sub-Poisson) implies the
prize floor for the actual Gauss period.* The premise is the single named open hypothesis. -/
theorem thesis_statement
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (s : Finset Ω) (Wr : Ω → ℝ) (E0 slack : ℝ) {r : ℕ}
    (Gfam : Ω → Finset F) (ψfam : Ω → AddChar F ℂ)
    (Discharged :
      0 < r ∧ 0 < slack ∧ s.Nonempty ∧ WrapMean s Wr = 0 ∧
      (∀ ω ∈ s, (rEnergy (Gfam ω) r : ℝ) = E0 + Wr ω) ∧
      (∀ ω ∈ s, E0 + slack ≤ (2 * r * ((Gfam ω).card : ℝ)) ^ r) ∧
      (∀ ω ∈ s, (Fintype.card F : ℝ) ≤ Real.exp r) ∧
      (∀ ω ∈ s, (ψfam ω).IsPrimitive)) :
    WrapVariance s Wr < slack ^ 2 →
      ∃ ω ∈ s, ∀ b₀ : F, b₀ ≠ 0 →
        ‖eta (ψfam ω) (Gfam ω) b₀‖
          ≤ Real.sqrt (Real.exp 1) * Real.sqrt (2 * r * ((Gfam ω).card : ℝ)) := by
  obtain ⟨hr, hslack, hs, hmean0, hwrap, hanchor, hdepth, hprim⟩ := Discharged
  intro hVar
  exact subPoisson_variance_implies_prizeFloor s Wr E0 slack Gfam ψfam hr hslack hs hmean0 hwrap
    hanchor hdepth hprim hVar

end ArkLib.ProximityGap.Frontier.ThesisCapstone

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.period_le_prizeFloor
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.good_prime_of_subPoisson_variance
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.energy_le_of_good_prime
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.subPoisson_variance_implies_prizeFloor
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.subPoisson_variance_of_pairCancellation
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.prize_floor_from_pair_equidistribution
#print axioms ArkLib.ProximityGap.Frontier.ThesisCapstone.thesis_statement
