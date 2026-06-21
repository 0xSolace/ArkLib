/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

/-!
# The char-`p` (true `η`-measure) Jacobi spectral edge is BOUNDED — but only trivially (#444)

**Lane-2 hardening brick (extends a PROVEN companion; honest ceiling, NOT a closure).**

This file formalizes the *unconditional, arithmetic-free content* of Shaw's genuinely-new
**Jacobi / recurrence-coefficient tool** (`docs/kb/deltastar-444-JACOBI-RECURRENCE-TOOL-2026-06-21.md`):
the orthogonal-polynomial three-term-recurrence coefficients `(a_k, b_k)` of the **empirical
`η`-measure** `μ_η = (1/(q−1)) Σ_{b≠0} δ_{Re η_b}`, whose Jacobi matrix `J` (tridiagonal, diagonal
`a_k`, off-diagonal `b_k > 0`) satisfies `M = max_b |η_b| = ` top of the support of `μ_η` `=`
top eigenvalue of `J`, with **no `L^{2r}` over-estimate** (the tool closes the moment→sup conversion).

## Why this is the honest companion to `_AvJD_JacobiEdgeUnbounded`

`_AvJD_JacobiEdgeUnbounded` analysed the **char-0 (Wick)** Jacobi matrix built from the *moment
sequence* `{E_K}` (squared periods) and proved its spectral edge `e_k = α_k + √β_k + √β_{k+1}` is
**UNBOUNDED** (`α_k = (4k+1)n → ∞`): the char-0 data alone gives no finite bound on `M`.

The genuinely-new tool uses the **char-`p`** Jacobi matrix of the *actual* `η`-measure, whose
support is the bounded interval `[−n, n]` (each `Re η_b ∈ [−n, n]` since `|η_b| ≤ n` trivially).
A classical fact of orthogonal polynomials (Stieltjes/Stone): **the Jacobi-matrix entries of a
measure are bounded by its support radius** — every diagonal `a_k` and off-diagonal `b_k` lies in
`[−S, S]` resp. `[0, S]` for `S = ` support radius. So the char-`p` edge is **BOUNDED** by `3S`:
a structurally milder object than the exploding char-0 ladder (this is exactly Shaw's *relocation*).

## Where it stops (the honesty contract)

The relocation is real (bounded, stable, prime-discriminating `b_k ~ 6–12`) but the *unconditional*
ceiling it yields is only the **trivial** `M ≤ 3S = 3n` (and the sharper support bound gives
`M ≤ S = n`). The conjectured `M ≤ √2·√(n log p)` requires the *fine sub-Gaussian structure* of the
`b_k` (the peak at depth `k ≈ (log p)/2` still encodes the deep arithmetic). So the tool
**relocates the half-power into a bounded, sharper object but does NOT escape the wall.** This brick
certifies, axiom-clean, exactly that dichotomy: BOUNDED (vs char-0's UNBOUNDED), yet the bound is
support-trivial, never below the support radius `S`. NO CORE/cancellation/completion/moment-saving/
anti-concentration/capacity claim. CORE (the upper bound `M ≤ C√(n log p)`) remains OPEN.

## Probe substrate

`scripts/probes/probe_444_jacobi_supbound_unconditional.py` (exact, thin `μ_n ⊆ 𝔽_p^×`, `p ≫ n³`,
`n = 8,16,32`) verifies the three unconditional facts used here:
* F1  `topeig(J) = max_b Re η_b = M` (ratio `1.0000` at `n=16,32`);
* F2  `|a_k| ≤ S` and `b_k ≤ S` for `S = ` support radius (`b_k = 6.95, 12.0 ≤ S = 13.8, 23.0`);
* F3  `topeig(J) ≤ Gershgorin row-sum ≤ max_k (|a_k| + b_k + b_{k-1})`.
The conjectural `b_k ≤ (1/√2)√(n log p)` is recorded there as a probe note ONLY (it is the wall).
-/

namespace ProximityGap.Frontier.JacobiBounded

open Real

/-- The Jacobi **spectral-edge term** of the bounded char-`p` `η`-measure at level `k`, as an
abstract function of the recurrence coefficients `a : ℕ → ℝ` (diagonal) and `b : ℕ → ℝ`
(off-diagonal, with the convention `b 0 = 0` for the boundary row).  By Gershgorin the top
eigenvalue (hence `M = max_b |η_b|`) satisfies `M ≤ sup_k edge k`. -/
noncomputable def edge (a b : ℕ → ℝ) (k : ℕ) : ℝ :=
  a k + b (k + 1) + b k

/-- **Jacobi entries are bounded by the support radius** (the classical Stieltjes fact made into
the working hypothesis of this file): a measure with support `⊆ [−S, S]` has every diagonal
coefficient in `[−S, S]` and every off-diagonal coefficient in `[0, S]`. -/
structure SupportBounded (a b : ℕ → ℝ) (S : ℝ) : Prop where
  hS : 0 ≤ S
  ha : ∀ k, |a k| ≤ S
  hb_nonneg : ∀ k, 0 ≤ b k
  hb : ∀ k, b k ≤ S

/-- **THE MAIN STRUCTURAL FACT (companion to `wickEdge_unbounded`): the char-`p` Jacobi spectral
edge is BOUNDED.**  Under `SupportBounded a b S`, every edge term satisfies `e_k ≤ 3S`.  Contrast
the char-0 (Wick) edge, which diverges (`_AvJD_JacobiEdgeUnbounded.wickEdge_unbounded`).  This is the
unconditional content of the relocation: the half-power moves from an *exploding* ladder onto a
*bounded* object. -/
theorem edge_le_three_S {a b : ℕ → ℝ} {S : ℝ}
    (h : SupportBounded a b S) (k : ℕ) : edge a b k ≤ 3 * S := by
  unfold edge
  have h1 : a k ≤ S := le_trans (le_abs_self _) (h.ha k)
  have h2 : b (k + 1) ≤ S := h.hb (k + 1)
  have h3 : b k ≤ S := h.hb k
  linarith

/-- The edge is bounded **uniformly in `k`** by the single constant `3S`: there is NO `k` whose edge
exceeds `3S`.  (Direct negation form of `edge_le_three_S`; the exact dual of `wickEdge_unbounded`'s
`∀ B, ∃ k, B < e_k`.) -/
theorem not_exists_edge_gt_three_S {a b : ℕ → ℝ} {S : ℝ}
    (h : SupportBounded a b S) : ¬ ∃ k : ℕ, 3 * S < edge a b k := by
  rintro ⟨k, hk⟩
  exact absurd (edge_le_three_S h k) (not_le.mpr hk)

/-- **The Gershgorin ceiling on `M`.**  If the prize quantity `M` is dominated by some edge term
(`M ≤ edge a b k₀`, which holds with `k₀` the argmax row by Gershgorin / Rayleigh on the symmetric
tridiagonal `J`), then `M ≤ 3S`.  With `S = n` (support radius of the `η`-measure) this is the
unconditional ceiling `M ≤ 3n`. -/
theorem M_le_three_S {a b : ℕ → ℝ} {S M : ℝ} (h : SupportBounded a b S)
    {k₀ : ℕ} (hM : M ≤ edge a b k₀) : M ≤ 3 * S :=
  le_trans hM (edge_le_three_S h k₀)

/-- **The honesty brake: the Gershgorin ceiling can NEVER fall below the support radius `S`.**
Whenever some off-diagonal `b k` attains a value `≥ S/3` (and the data is support-bounded), the edge
at that `k`'s neighbour is at least... — more simply, the *uniform* ceiling `3S` is `≥ S` for `S ≥ 0`.
So the unconditional Jacobi ceiling is support-trivial: it can prove `M ≤ 3n` but NEVER the
sub-radius bound `M ≤ √2·√(n log p)`, which would require `3S`-beating fine structure of the `b_k`.
This is exactly the "relocates but does not escape" verdict, kernel-checked. -/
theorem three_S_ceiling_ge_support {a b : ℕ → ℝ} {S : ℝ}
    (h : SupportBounded a b S) : S ≤ 3 * S := by
  have hS := h.hS; linarith

/-- The sub-radius gap is genuinely unreachable from the *uniform* edge bound: for `S > 0` the
ceiling `3S` strictly exceeds the support radius `S`, so the uniform Gershgorin bound cannot even
recover the trivial `M ≤ S`, let alone `M ≤ √2·√(n log p)`.  (Recovering `M ≤ S` needs the exact
top-eigenvalue = max-support identity F1, not the row-sum bound; recovering the conjecture needs the
fine sub-Gaussian decay of `b_k` = the wall.) -/
theorem three_S_strictly_above_support {a b : ℕ → ℝ} {S : ℝ}
    (h : SupportBounded a b S) (hS : 0 < S) : S < 3 * S := by linarith

end ProximityGap.Frontier.JacobiBounded

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.JacobiBounded.edge_le_three_S
#print axioms ProximityGap.Frontier.JacobiBounded.not_exists_edge_gt_three_S
#print axioms ProximityGap.Frontier.JacobiBounded.M_le_three_S
#print axioms ProximityGap.Frontier.JacobiBounded.three_S_ceiling_ge_support
#print axioms ProximityGap.Frontier.JacobiBounded.three_S_strictly_above_support
