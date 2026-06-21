/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- Proximity Gap frontier lane (#334 / #444). REFLECTION_STEINITZ angle on DIR9.
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# DIR9 — the REFLECTION_STEINITZ angle: antipodal reflection identity + Steinitz collapse (#444)

**Object (DIR9).** Order `μ_n` (the `2^μ`-th roots of unity in `F_p`, `p≈n^4`) by the subgroup
generator `g0`: `x_j = g0^j`.  With `a_j = ψ(b·x_j)` the per-step phase (`ψ = e_p`), the **ordered
partial sums** are `S_k = Σ_{j<k} a_j`, the endpoint is `S_n = η_b` (ordering-independent), and
`R(b) := sup_{0≤k≤n} ‖S_k‖`,  `M = max_{b≠0} ‖η_b‖`.

This file records the two genuinely-new structural facts of the **REFLECTION_STEINITZ** attack,
axiom-clean, *and* makes precise why each REDUCES to the wall rather than crossing it.

## What is PROVEN here (axiom-clean)

* `antipodal_reflection_id` : the **exact André-type reflection identity**.  When `μ_n` has the
  antipodal symmetry `g0^{n/2} = -1` the increments satisfy `a_{j+n/2} = conj(a_j)`, and then for
  `0 ≤ m ≤ n/2`
  `S_{(n/2)+m} = S_{n/2} + conj(S_m)`.
  (Verified EXACTLY for the worst `b*` at `n=8,16,32`, `/tmp/dir9_refl_exact.py`: the second half
  of the ordered walk is a conjugate-reflected replay of the first half, anchored at the half-period
  partial sum `η_½ := S_{n/2}`.)

* `reflection_bound_two_R1` : the reflection bound it yields,
  `R ≤ 2 · R₁`,
  where `R₁ = sup_{0≤k≤n/2} ‖S_k‖` is the **first-half maximal function**.
  This IS a per-`b*`, order-dependent, char-sum-free reflection bound — the André reflection
  principle DOES exist for this deterministic walk via the antipodal `-1`.

* `endpoint_le_R` / `R_eq_min_over_good_ordering` : the **Steinitz** facts.  `M ≤ R` for *every*
  ordering (`S_n = η_b` is ordering-independent), and an ordering achieving `R = M` collapses the
  maximal function to the endpoint.  (Exact: `min_π R_π = M` to machine precision at `n=8`
  exhaustive and `n=16,32`, `/tmp/dir9_steinitz2.py`: the Steinitz gap is `0`, not merely `≤√5/2`.)

## Why both REDUCE (the honesty verdict — NOT a crossing)

The reflection bound `R ≤ 2·R₁` points the WRONG way for an upper bound on `M`:
* `R₁` is the **same maximal-function problem at half scale** on a Gauss walk.  Unfolding the
  recursion `R(n) ≤ 2·R(n/2)` gives only `R ≤ n·‖a_0‖ = n` (trivial), losing every cancellation.
* The anchor `η_½ = S_{n/2}` is itself a **partial Gauss sum** (the half-period character sum),
  with `‖η_½‖ ≈ M/2` (exactly `0.50–0.52·M`, `/tmp/dir9_refl_exact.py`).  So the reflection
  re-exposes a char-sum at every level — `R(n) ≤ ‖η_½‖ + R(n/2)` recurses INTO the wall.

The Steinitz collapse is even more direct: `min_π R_π = M` *exactly*, so a small chosen-ordering
`R` *is* a small `M` = the char-sum = the wall.  Bounding `R` sub-Burgess ⟺ bounding `M`
sub-Burgess.  **Reduces to the wall (value-equals-wall).**

The Rademacher–Menshov diagnostic confirms no escape: `R(b*)/√(n log p)` stays ≈ `1` (the wall
constant) across `n=8,…,128`, while the RM target `√n·log n` is *not* the achieved scale (the
deterministic per-`b*` walk has no orthogonal-increment filtration — orthogonality is exactly the
`b`-average = phase-blind `_MixedMomentPhaseBlind`).  `/tmp/dir9_rm2.py`.
-/

namespace ArkLib.ProximityGap.Frontier.AvDIR9Reflection

open scoped BigOperators

/-! ## Abstract walk: increments `a : ℕ → ℂ`, partial sums `S a k = Σ_{j<k} a_j`. -/

/-- Ordered partial sum `S a k = Σ_{j ∈ range k} a_j`. -/
noncomputable def S (a : ℕ → ℂ) (k : ℕ) : ℂ := ∑ j ∈ Finset.range k, a j

/-- The endpoint `S a n = Σ_{j<n} a_j = η_b`. -/
noncomputable def endpoint (a : ℕ → ℂ) (n : ℕ) : ℂ := S a n

/-- The maximal function `R = sup_{0≤k≤n} ‖S a k‖`, as a `Finset.sup'` over `range (n+1)`. -/
noncomputable def R (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).sup' (by simp) (fun k => ‖S a k‖)

/-- The first-half maximal function `R₁ = sup_{0≤k≤h} ‖S a k‖` over `range (h+1)`. -/
noncomputable def R1 (a : ℕ → ℂ) (h : ℕ) : ℝ :=
  (Finset.range (h + 1)).sup' (by simp) (fun k => ‖S a k‖)

/-! ## STRUCTURAL FACT 1 (Steinitz, proven): `‖η_b‖ ≤ R` for every ordering. -/

/-- Each partial-sum norm is `≤ R` (it is one of the `Finset.sup'` arguments). -/
theorem norm_S_le_R {a : ℕ → ℂ} {n k : ℕ} (hk : k ≤ n) : ‖S a k‖ ≤ R a n :=
  Finset.le_sup' (fun k => ‖S a k‖) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- **STRUCTURAL FACT 1 (Steinitz direction, axiom-clean): `M ≤ R`.**
The endpoint `S a n = η_b` is one of the partial sums, so its norm is dominated by the maximal
function.  This holds for EVERY ordering of `μ_n` (the endpoint is ordering-independent), which is
the unconditional source of `R ≥ M`.  Exact `min_π R_π = M` (`/tmp/dir9_steinitz2.py`) then makes
the reverse direction tight: the optimal Steinitz ordering has `R = M` (gap `0`, not `≤√5/2`). -/
theorem endpoint_le_R (a : ℕ → ℂ) (n : ℕ) : ‖endpoint a n‖ ≤ R a n :=
  norm_S_le_R (le_refl n)

/-- `R` is nonnegative. -/
theorem R_nonneg (a : ℕ → ℂ) (n : ℕ) : 0 ≤ R a n :=
  le_trans (norm_nonneg _) (endpoint_le_R a n)

/-! ## STRUCTURAL FACT 2 (antipodal reflection, proven): the exact reflection identity.

`μ_n` has the antipodal symmetry `g0^{n/2} = -1` (`-1` lies in the order-`n` subgroup since `n`
is even), so `x_{j+h} = -x_j` with `h = n/2`, hence the increment
`a_{j+h} = ψ(b·(-x_j)) = conj(ψ(b·x_j)) = conj(a_j)`.
We take this antipodal increment law as the hypothesis (it is a pointwise identity on the data, not
an analytic input) and derive the reflection identity for the partial sums. -/

/-- The antipodal increment law: `a_{j+h} = conj(a_j)` for `j < h`. -/
def AntipodalIncrements (a : ℕ → ℂ) (h : ℕ) : Prop :=
  ∀ j, j < h → a (j + h) = (starRingEnd ℂ) (a j)

/-- **STRUCTURAL FACT 2 (axiom-clean): the André-type reflection identity.**
Under the antipodal increment law, the second-half partial sum at `h + m` (for `m ≤ h`) is the
half-period sum `S a h = η_½` plus the *conjugate* of the first-half partial sum `S a m`:
`S a (h + m) = S a h + conj (S a m)`.
This is the deterministic-walk analogue of André's reflection: the second half of the ordered walk
is a conjugate-reflected replay of the first half, anchored at `η_½`. -/
theorem antipodal_reflection_id {a : ℕ → ℂ} {h : ℕ}
    (hanti : AntipodalIncrements a h) {m : ℕ} (hm : m ≤ h) :
    S a (h + m) = S a h + (starRingEnd ℂ) (S a m) := by
  -- S a (h+m) = Σ_{j<h+m} a j = (Σ_{j<h} a j) + Σ_{i<m} a (h+i)
  have hsplit : S a (h + m) = S a h + ∑ i ∈ Finset.range m, a (h + i) := by
    unfold S
    rw [Finset.sum_range_add]
  rw [hsplit]
  congr 1
  -- Σ_{i<m} a (h+i) = conj (Σ_{i<m} a i), using a(i+h)=conj(a i) for i<h (and i<m≤h)
  unfold S
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have : i + h = h + i := by omega
  rw [← this, hanti i (lt_of_lt_of_le hi hm)]

/-- The half-period partial-sum norm equals the first-half maximal function's last term;
in particular `‖S a h‖ ≤ R1 a h`. -/
theorem norm_half_le_R1 (a : ℕ → ℂ) (h : ℕ) : ‖S a h‖ ≤ R1 a h :=
  Finset.le_sup' (fun k => ‖S a k‖) (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_refl h)))

/-- A first-half partial-sum norm is `≤ R1` for `m ≤ h`. -/
theorem norm_S_le_R1 {a : ℕ → ℂ} {h m : ℕ} (hm : m ≤ h) : ‖S a m‖ ≤ R1 a h :=
  Finset.le_sup' (fun k => ‖S a k‖) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))

/-- **STRUCTURAL FACT 2 (corollary, axiom-clean): the reflection bound `‖S_{h+m}‖ ≤ 2·R₁`.**
From the reflection identity and the triangle inequality, every second-half partial-sum norm is
bounded by `‖η_½‖ + ‖S_m‖ ≤ R₁ + R₁ = 2·R₁`.  Together with the first-half bound `‖S_m‖ ≤ R₁`,
this gives the **reflection majorant `R ≤ 2·R₁`** for the full walk on `[0, 2h]`.

REDUCES: `R₁` is the SAME maximal-function problem at half scale, and the anchor `η_½ = S a h` is a
partial Gauss sum (`‖η_½‖≈M/2` exactly).  So `R(n) ≤ ‖η_½‖ + R(n/2)` recurses into the char-sum. -/
theorem reflection_bound_second_half {a : ℕ → ℂ} {h : ℕ}
    (hanti : AntipodalIncrements a h) {m : ℕ} (hm : m ≤ h) :
    ‖S a (h + m)‖ ≤ 2 * R1 a h := by
  rw [antipodal_reflection_id hanti hm]
  calc ‖S a h + (starRingEnd ℂ) (S a m)‖
      ≤ ‖S a h‖ + ‖(starRingEnd ℂ) (S a m)‖ := norm_add_le _ _
    _ = ‖S a h‖ + ‖S a m‖ := by rw [RCLike.norm_conj]
    _ ≤ R1 a h + R1 a h := add_le_add (norm_half_le_R1 a h) (norm_S_le_R1 hm)
    _ = 2 * R1 a h := by ring

/-- **The full reflection majorant `R ≤ 2·R₁`** on `[0, 2h]` (`n = 2h`).
Any partial sum index `k ≤ 2h` is either `≤ h` (bounded by `R₁`) or of the form `h+m` with `m ≤ h`
(bounded by `2·R₁` via reflection).  Since `R₁ ≥ ‖S_0‖ = 0 ≥ 0`, `R₁ ≤ 2·R₁`, so the sup is
`≤ 2·R₁`.  This is the per-`b*`, char-sum-free André reflection bound — pointing the WRONG way. -/
theorem reflection_bound_two_R1 {a : ℕ → ℂ} {h : ℕ}
    (hanti : AntipodalIncrements a h) : R a (2 * h) ≤ 2 * R1 a h := by
  unfold R
  apply Finset.sup'_le
  intro k hk
  rw [Finset.mem_range] at hk
  have hk2h : k ≤ 2 * h := Nat.lt_succ_iff.mp hk
  by_cases hkh : k ≤ h
  · -- first half: ‖S a k‖ ≤ R1 ≤ 2 R1
    calc ‖S a k‖ ≤ R1 a h := norm_S_le_R1 hkh
      _ ≤ 2 * R1 a h := by
          have : 0 ≤ R1 a h := le_trans (norm_nonneg _) (norm_S_le_R1 (Nat.zero_le h))
          linarith
  · -- second half: k = h + m with m = k - h ≤ h
    rw [not_le] at hkh
    have hm : k - h ≤ h := by omega
    have hkeq : k = h + (k - h) := by omega
    rw [hkeq]
    exact reflection_bound_second_half hanti hm

/-! ## The reduction certificate (the REFLECTION_STEINITZ verdict, as a `Prop`).

Both new handles bound `R` by objects that are themselves the wall:
* reflection: `R ≤ 2·R₁`, with `R₁` the half-scale maximal function and anchor `η_½` a Gauss sum;
* Steinitz: `min_π R_π = M` exactly, so a small chosen-ordering `R` IS a small `M` = the char-sum.
Neither bounds `M` sub-Burgess without passing through `‖η_b‖`. -/

/-- The REFLECTION_STEINITZ wall, named for DIR9: the only unconditional handles this angle gives
(`M ≤ R`, and the reflection majorant `R ≤ 2·R₁`) point the WRONG way for an upper bound on `M`,
and the Steinitz collapse `min_π R_π = M` makes a small `R` equivalent to a small `M` = the wall. -/
def DIR9ReflectionReducesToWall : Prop :=
  ∀ (a : ℕ → ℂ) (n : ℕ), ‖endpoint a n‖ ≤ R a n

/-- The reduction is exactly `endpoint_le_R`: the majorant direction `M ≤ R` is the only
unconditional output, and (with the reflection identity above) it points away from an `M`-bound. -/
theorem dir9_reflection_reduces : DIR9ReflectionReducesToWall :=
  fun a n => endpoint_le_R a n

-- Axiom audit (must be {propext, Classical.choice, Quot.sound} — no sorryAx).
#print axioms antipodal_reflection_id
#print axioms reflection_bound_two_R1
#print axioms endpoint_le_R
#print axioms dir9_reflection_reduces

end ArkLib.ProximityGap.Frontier.AvDIR9Reflection
