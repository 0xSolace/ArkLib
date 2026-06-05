/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ListDecodability
import Mathlib.Algebra.Order.Chebyshev

/-!
# ABF26 §3.1 — Johnson family `J_{q,ℓ}, J_q, J` and Theorem 3.2 / Corollary 3.3

Extensions to `JohnsonBound/Basic.lean` matching the paper-shaped statements from
ABF26 §3.1 (Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026).

The existing `JohnsonBound.J q δ : ℝ` matches the paper's `J_q(δ)`. This file adds:

- `JohnsonBound.Jqℓ q ℓ δ` — paper's `J_{q,ℓ}(δ)`, with the additional `ℓ/(ℓ-1)` factor
  inside the square root.
- `JohnsonBound.Jcap δ` — paper's asymptotic Johnson bound `J(δ) := 1 - √(1 - δ)`.

The three are related by `J_{q,ℓ}(δ) →_{ℓ → ∞} J_q(δ) →_{q → ∞} J(δ)`; we state the
limit relationships in docstrings but do not formalise the limits (the paper does
not prove them either).

The file also states the paper-shaped versions of:

- `johnson_bound_lambda_le_ell` — ABF26 Theorem 3.2 [Joh62]:
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`.
- `mds_johnson_lambda_le` — ABF26 Corollary 3.3:
  for any MDS code `C` of rate `ρ` and `η > 0`, `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.

Both are admitted as external results (T3.2 has an existing in-tree proof via
`johnson_bound` / `johnson_bound_alphabet_free` in `JohnsonBound/Basic.lean` that
needs porting from the absolute-distance form to ABF26's `Lambda` form; C3.3
follows from L2.6 + T3.2, but uses the asymptotic Johnson radius which crosses
ArkLib's existing rate/distance bridge).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Joh62] Johnson. (Original Johnson bound paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace JohnsonBound

open Real

/-- **ABF26 Definition 3.1, `J_{q,ℓ}`.** Paper's q-ary ℓ-radius Johnson function:

  `J_{q,ℓ}(δ) := (1 - 1/q) · (1 - √(1 - q/(q-1) · ℓ/(ℓ-1) · δ))`

For `ℓ = 2` this is the binary Johnson radius; as `ℓ → ∞`, `Jqℓ q ℓ δ → J q δ`
(the existing `JohnsonBound.J`). The `ℓ` parameter is the target list size. -/
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ :=
  let frac : ℚ := q / (q - 1)
  let lFac : ℚ := ℓ / (ℓ - 1)
  ((1 - 1 / q) : ℚ) * (1 - √(1 - frac * lFac * δ))

/-- **ABF26 Definition 3.1, `J`.** Paper's asymptotic Johnson bound:

  `J(δ) := 1 - √(1 - δ)`

Equals the `q → ∞` limit of `J_q(δ)` and the `q, ℓ → ∞` limit of `J_{q,ℓ}(δ)`.
This is also the binary Johnson bound (q = 2, ℓ → ∞).

Distinct from the existing `JohnsonBound.J q δ`, which is the paper's `J_q(δ)`
(the q-ary limit, parametrised by `q`). To avoid renaming the existing `J`, we
name this `Jcap` (Johnson — *cap*acity). -/
noncomputable def Jcap (δ : ℝ) : ℝ := 1 - √(1 - δ)

@[simp]
lemma Jcap_zero : Jcap 0 = 0 := by simp [Jcap]

@[simp]
lemma Jcap_one : Jcap 1 = 1 := by simp [Jcap]

end JohnsonBound

namespace CodingTheory

open scoped NNReal
open ListDecodable JohnsonBound

/-- **ABF26 Theorem 3.2 [Joh62].** Johnson bound on list size. For any code
`C ⊆ Σ^n` with `|Σ| = q`,

  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`

where `δ_min(C) = minDist(C) / n` is the relative minimum distance and `J_{q,ℓ}`
is the paper's q-ary ℓ-radius Johnson function. **Admitted (tagged sorry).**

**Why the in-tree `johnson_bound` does NOT reach this radius (verified, 2026-06-04).**
A prior triage suggested "plug `e/n = J_{q,ℓ}` into the in-tree `johnson_bound`; its
`JohnsonConditionStrong` then fails at the boundary, forcing `|Λ| ≤ ℓ`". This was
re-checked symbolically and is **incorrect** — there is a factor inversion that makes
the in-tree bound land at a *strictly smaller* radius. The exact computation:

Write `frac = q/(q-1)`, `t = frac·δ_min`, `L = ℓ/(ℓ-1) > 1`. The boundary identity for
`Jqℓ` is `(1 - frac·Jqℓ)² = 1 - frac·L·δ_min = 1 - L·t`. The packaged bound
[`johnson_bound`](Basic.lean) gives `B.card ≤ (frac·d/n)/Denom` with
`Denom = (1 - frac·e/n)² - (1 - frac·d/n)`. Setting `e/n = Jqℓ`, `d/n = δ_min`:
`Denom = (1 - L·t) - (1 - t) = t·(1 - L) = -t/(ℓ-1) < 0`. So `JohnsonConditionStrong`
(`Denom > 0`) is *false* and the bound is unusable — but the failure does **not** force
`|Λ| ≤ ℓ`: the raw [`johnson_bound_lemma`](Lemmas.lean), which holds unconditionally
(`n>0`, `|B|≥2`, `|F|≥2`), reads `B.card · Denom ≤ frac·d/n`, and with `Denom < 0` this
is a *negative lower* bound on `B.card` — vacuous as an upper bound.

Inverting the packaging the other way: `johnson_bound` yields `B.card ≤ ℓ` exactly when
`Denom ≥ (frac·d/n)/ℓ = t/ℓ`, i.e. `(1 - frac·e/n)² ≥ 1 - t·(ℓ-1)/ℓ = 1 - t/L`, i.e.
`e/n ≤ (1/frac)·(1 - √(1 - frac·δ_min/L))`. That radius uses the factor `1/L = (ℓ-1)/ℓ`,
the **reciprocal** of the `L = ℓ/(ℓ-1)` factor inside `Jqℓ`. Since `L > 1`, the in-tree
radius is strictly *smaller* than the paper's `Jqℓ`. The paper's larger (tight) list-of-ℓ
radius is the Plotkin-refined Johnson radius and is not reachable from the second-moment
`johnson_bound` alone.

**Exact missing ingredient (citation upgrade).** Closing T3.2 at the paper's `Jqℓ`
requires the *q-ary Plotkin average-distance upper bound*

  `d(B') ≤ frac · n · M/(M-1)`     where `M = |B'|`, `frac = q/(q-1)`,

i.e. the convex *dual* of the in-tree `almost_johnson` (which lower-bounds
`∑_α C₂(K_i(α))`; the Plotkin step instead lower-bounds `∑_α K_i(α)² ≥ M²/q` by
Cauchy–Schwarz / power-mean, giving an *upper* bound on the average distance). The tree
currently has only `min_dist_le_d` (`δ_min ≤ d_avg`) and `johnson_d_le_n` (`d_avg ≤ n`),
neither of which suffices. Combining this Plotkin bound with `johnson_bound_lemma`
discharges T3.2 at `Jqℓ`. This is a self-contained ~150–250-line development over the
existing `K B i α` column-count machinery in [`JohnsonBound/Lemmas.lean`](Lemmas.lean)
and is the only nontrivial gap; see the four skeletons in the inline comment below.

**Two further mechanical gaps** (independent of the math wall above):
- *Alphabet*: this statement is over a bare alphabet `α` (`Fintype + DecidableEq`, no
  `Field`), but every in-tree Johnson lemma — including `johnson_bound_alphabet_free` —
  carries `[Field F]`. Either redo the column-count core over `DecidableEq α`, or weaken
  this statement to `[Field α]`.
- *Index type*: the in-tree apparatus (`e B v`, `d B`, the ball) is over `Fin n → F`;
  this statement is over `ι → α`. A `Fintype.equivFin ι` transport of `hammingDist`/`e`/`d`
  is needed (mechanical but not free).

Tracked in `docs/kb/ABF26_PLAN.md` and the audit log.

**Alphabet generality.** Stated over an arbitrary alphabet `α` (not necessarily a
field), matching the paper's `Σ`. The Johnson bound is a purely combinatorial fact
about Hamming distance — it does not need field structure. -/
theorem johnson_bound_lambda_le_ell
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  -- ABF26-T3.2; external admit. The ONLY nontrivial gap is the q-ary Plotkin
  -- average-distance upper bound `d(B') ≤ frac·n·M/(M-1)` (see docstring). Four
  -- attempted in-tree routes, each blocked at a precisely-identified step:
  --
  -- SKELETON 1 (direct `johnson_bound`, the route the docstring refutes).
  --   intro q δ_min; refine iSup_le fun f => ?_;  set B' := closeCodewordsRel C f _
  --   Transport B' to a `Finset (Fin n → α)`; apply `johnson_bound` to get
  --   `B'.card ≤ (frac·d/n)/Denom`.  BLOCKED: at `e/n = Jqℓ`, `Denom = -t/(ℓ-1) < 0`,
  --   so `JohnsonConditionStrong` is false; no `B'.card ≤ ℓ` follows (factor inversion).
  --
  -- SKELETON 2 (raw `johnson_bound_lemma` + Plotkin — the CORRECT route).
  --   From `johnson_bound_lemma`: `M·Denom ≤ frac·d_avg/n`, holds unconditionally.
  --   Need: q-ary Plotkin `d_avg ≤ frac·n·M/(M-1)` ⇒ substitute and solve for M.
  --   BLOCKED: the Plotkin bound is ABSENT in-tree (the convex dual of `almost_johnson`;
  --   would lower-bound `∑_α K_i(α)² ≥ M²/q`, opposite to `le_sum_sum_choose_K`).
  --
  -- SKELETON 3 (`johnson_bound_alphabet_free` ⇒ `q·d·n`).
  --   `johnson_bound_alphabet_free` gives `(B ∩ ball e).card ≤ q·d·n` under
  --   `e ≤ n - √(n·(n-d))`.  BLOCKED twice: (a) the bound `q·d·n` is far weaker than `ℓ`
  --   (it is the alphabet-free coarse form, not list-of-ℓ); (b) its radius hypothesis is
  --   the `J_q` (ℓ→∞) radius, not `Jqℓ` — wrong both in tightness and in the ℓ-factor.
  --
  -- SKELETON 4 (Lambda_mono down to the in-tree reachable radius `1/L`).
  --   By the docstring, `johnson_bound` *does* give `|Λ(C, R₀)| ≤ ℓ` at
  --   `R₀ = (1/frac)(1 - √(1 - frac·δ_min/L))`.  `Lambda_mono` needs `Jqℓ ≤ R₀` to
  --   transport ℓ from `R₀` up to `Jqℓ`.  BLOCKED: `Jqℓ > R₀` (since `L > 1/L`), so
  --   monotonicity runs the WRONG way — it would only give `|Λ(C, Jqℓ)| ≥ |Λ(C, R₀)|`.
  --   This is the formal restatement of the factor inversion: the in-tree bound is
  --   strictly inside the paper's radius, and Lambda is monotone INCREASING in radius.
  --
  -- All four bottom out at the missing q-ary Plotkin bound. Tagged sorry / external admit.
  --
  -- HONEST PARTIAL PROGRESS (integrated 2026-06-04): the q-ary Plotkin average-distance
  -- upper bound named above as "the only nontrivial gap" is now PROVEN sorry-free and
  -- axiom-clean as `MdsPlotkin.plotkin_d_le` below. The residual obstruction to closing
  -- T3.2 at the paper's `Jqℓ` is the M-point Gram/PSD (regular-simplex) ℓ-refinement
  -- step plus the bare-alphabet / `ι→Fin` / ℚ→ℝ transport plumbing; the Plotkin
  -- ingredient itself is no longer missing. Target still admitted.
  sorry

/-! ## q-ary Plotkin average-distance development (frontier helper)

The docstring of `johnson_bound_lambda_le_ell` (T3.2) identifies the **q-ary Plotkin
average-distance upper bound** as the only nontrivial gap blocking the ABF26 §3.1
Johnson family theorems:

  `d(B') ≤ (1 - 1/q) · n · M / (M - 1)`     where `M = |B'|`, `q = |F|`,

whose combinatorial core is the Cauchy–Schwarz / power-mean step
`∑_α K_i(α)² ≥ M²/q`.  This is realised below, fully `sorry`-free, **from scratch**
(the in-tree column-count machinery `K`, `sum_choose_K_i`, `Fi`, … in
`JohnsonBound/Lemmas.lean` is `private`, so it is rebuilt here in the `MdsPlotkin`
namespace; only the *exported* `JohnsonBound.d_eq_sum`,
`JohnsonBound.choose_2`, `JohnsonBound.d` are reused).

The pipeline:
* `agree_eq_sum_sq` — for each coordinate `i`, the number of ordered pairs of `B`
  agreeing at `i` equals `∑_α K_i(α)²` (double-counting).
* `cs_lb` — Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`): `∑_α K_i(α)² ≥ M²/q`.
* `split_pairs` / `filter_redundant` — agree + disagree counts sum to `M²`.
* `col_disagree_le` — per-coordinate disagreement count `≤ M²·(1 - 1/q)`.
* `sum_disagree_le` — summed over the `n` coordinates: `≤ n·M²·(1 - 1/q)`.
* `plotkin_d_le` — combined with `d_eq_sum` (`2·C₂(M)·d(B) = ∑_i (disagreements)`):
  the q-ary Plotkin bound `d(B) ≤ (1-1/q)·n·M/(M-1)`.

This closes the math wall documented in T3.2.  (The *final* assembly of C3.3 below
additionally needs the `Lambda`/`closeCodewordsRel` → `Finset (Fin n → F)` transport
and the second-moment / Plotkin real-analysis algebra; that bridge is left as the
remaining `sorry`.) -/
namespace MdsPlotkin

open JohnsonBound Finset Fintype

variable {n : ℕ} {F : Type} [Fintype F] [DecidableEq F]

/-- The `x.1 ≠ x.2` filter is redundant for the coordinate-`i` disagreement indicator
(the diagonal contributes `0` to `[x.1 i ≠ x.2 i]`). -/
lemma filter_redundant (B : Finset (Fin n → F)) (i : Fin n) :
    (∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    = (∑ x ∈ B ×ˢ B, (if x.1 i ≠ x.2 i then (1:ℚ) else 0)) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x.1 i = x.2 i
  · simp [h]
  · have : x.1 ≠ x.2 := fun he => h (by rw [he])
    simp [this, h]

/-- **Double counting.** The number of ordered pairs `(x, y) ∈ B × B` that *agree*
at coordinate `i` equals `∑_α (#{x ∈ B | x i = α})²`. -/
lemma agree_eq_sum_sq (B : Finset (Fin n → F)) (i : Fin n) :
    (∑ x ∈ B ×ˢ B, (if x.1 i = x.2 i then (1:ℚ) else 0))
    = ∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2 := by
  have expand : ∀ x y : Fin n → F,
      (if x i = y i then (1:ℚ) else 0)
      = ∑ α : F, (if x i = α then (1:ℚ) else 0) * (if y i = α then (1:ℚ) else 0) := by
    intro x y
    rw [Finset.sum_eq_single (x i)]
    · by_cases h : x i = y i <;> simp [h, eq_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ (x i)) h
  have colcount : ∀ α : F, ((B.filter (fun x => x i = α)).card : ℚ)
      = ∑ x ∈ B, (if x i = α then (1:ℚ) else 0) := by
    intro α; rw [Finset.sum_boole]
  have rhs_eq : (∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2)
      = ∑ α : F, ∑ x ∈ B, ∑ y ∈ B,
          (if x i = α then (1:ℚ) else 0) * (if y i = α then (1:ℚ) else 0) := by
    apply Finset.sum_congr rfl; intro α _
    rw [colcount α, sq, Finset.sum_mul_sum]
  rw [rhs_eq, Finset.sum_product]
  simp_rw [expand]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Agreement count plus disagreement count over `B × B` equals `M²`. -/
lemma split_pairs (B : Finset (Fin n → F)) (i : Fin n) :
    (∑ x ∈ B ×ˢ B, (if x.1 i = x.2 i then (1:ℚ) else 0))
    + (∑ x ∈ B ×ˢ B, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    = (B.card:ℚ)^2 := by
  rw [← Finset.sum_add_distrib]
  rw [show (B.card:ℚ)^2 = ∑ _x ∈ B ×ˢ B, (1:ℚ) by
    rw [Finset.sum_const, Finset.card_product]; push_cast; ring]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x.1 i = x.2 i <;> simp [h]

/-- **Cauchy–Schwarz lower bound.** `∑_α (#{x ∈ B | x i = α})² ≥ M²/q`, via
`sq_sum_le_card_mul_sum_sq` and `∑_α #{x ∈ B | x i = α} = M` (fiberwise count). -/
lemma cs_lb (B : Finset (Fin n → F)) (i : Fin n) (hq : 0 < Fintype.card F) :
    (B.card:ℚ)^2 / (Fintype.card F : ℚ)
      ≤ ∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2 := by
  have hsum : (∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)) = (B.card:ℚ) := by
    rw [← Nat.cast_sum]; congr 1
    exact (Finset.card_eq_sum_card_fiberwise (f := fun x => x i) (s := B) (t := univ)
      (fun x _ => Finset.mem_univ _)).symm
  have hcard : (Finset.univ : Finset F).card = Fintype.card F := by simp
  have cs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset F))
    (f := fun α => ((B.filter (fun x => x i = α)).card : ℚ))
  rw [hsum, hcard] at cs
  rw [div_le_iff₀ (by exact_mod_cast hq), mul_comm]; exact cs

/-- **Per-coordinate Plotkin step.** The number of distinct ordered pairs of `B`
disagreeing at coordinate `i` is at most `M²·(1 - 1/q)`. -/
lemma col_disagree_le (B : Finset (Fin n → F)) (i : Fin n) (hq : 0 < Fintype.card F) :
    (∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    ≤ (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
  rw [filter_redundant]
  have hsplit := split_pairs B i
  have hagree := agree_eq_sum_sq B i
  have hcs := cs_lb B i hq
  have hq' : (0:ℚ) < (Fintype.card F : ℚ) := by exact_mod_cast hq
  have hdis : (∑ x ∈ B ×ˢ B, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
      = (B.card:ℚ)^2 - (∑ α : F, ((B.filter (fun x => x i = α)).card : ℚ)^2) := by
    rw [← hagree]; linarith
  rw [hdis]
  have hexp : (B.card:ℚ)^2 * (1 - 1/(Fintype.card F : ℚ))
      = (B.card:ℚ)^2 - (B.card:ℚ)^2/(Fintype.card F : ℚ) := by field_simp
  rw [hexp]; linarith

/-- Sum over all `n` coordinates of the per-coordinate disagreement count. -/
lemma sum_disagree_le (B : Finset (Fin n → F)) (hq : 0 < Fintype.card F) :
    (∑ i : Fin n, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
    ≤ (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
  calc (∑ i : Fin n, ∑ x ∈ B ×ˢ B with x.1 ≠ x.2, (if x.1 i ≠ x.2 i then (1:ℚ) else 0))
      ≤ ∑ _i : Fin n, (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) :=
        Finset.sum_le_sum (fun i _ => col_disagree_le B i hq)
    _ = (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring

/-- **q-ary Plotkin average-distance bound** (the missing ingredient flagged in the
T3.2 docstring). For any `B ⊆ Fⁿ` with `|B| ≥ 2`,

  `d(B) ≤ (1 - 1/q) · n · |B| / (|B| - 1)`.

Proof: `JohnsonBound.d_eq_sum` rewrites `2·C₂(|B|)·d(B)` as the total coordinate
disagreement count `∑_i (…)`, which `sum_disagree_le` bounds by
`n·|B|²·(1 - 1/q)`; since `2·C₂(|B|) = |B|·(|B|-1)`, cancelling `|B| > 0` gives the
claim. -/
lemma plotkin_d_le (B : Finset (Fin n → F)) (h_B : 2 ≤ B.card) (hq : 0 < Fintype.card F) :
    JohnsonBound.d B
      ≤ (n:ℚ) * (B.card:ℚ) * (1 - 1/(Fintype.card F:ℚ)) / ((B.card:ℚ) - 1) := by
  have hM : (2:ℚ) ≤ (B.card:ℚ) := by exact_mod_cast h_B
  have hMpos : (0:ℚ) < (B.card:ℚ) := by linarith
  have hM1pos : (0:ℚ) < (B.card:ℚ) - 1 := by linarith
  have key : 2 * JohnsonBound.choose_2 (B.card:ℚ) * JohnsonBound.d B
      ≤ (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
    rw [JohnsonBound.d_eq_sum h_B]; exact sum_disagree_le B hq
  have hch : 2 * JohnsonBound.choose_2 (B.card:ℚ) = (B.card:ℚ) * ((B.card:ℚ) - 1) := by
    simp [JohnsonBound.choose_2]; ring
  have key2 : (B.card:ℚ) * ((B.card:ℚ) - 1) * JohnsonBound.d B
      ≤ (n:ℚ) * (B.card:ℚ)^2 * (1 - 1 / (Fintype.card F : ℚ)) := by
    rw [← hch]; linarith [key]
  rw [le_div_iff₀ hM1pos]
  nlinarith [key2, hMpos, mul_pos hMpos hM1pos]

/-- **Index transport for `hammingDist`.** Reindexing both arguments by a bijection
`κ ≃ ι` leaves the Hamming distance unchanged (used to move the `ι → F` statement of
C3.3 to the `Fin n → F` apparatus of `JohnsonBound`). -/
lemma hammingDist_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {G : Type} [DecidableEq G]
    (eqv : κ ≃ ι) (u v : ι → G) :
    hammingDist (u ∘ eqv) (v ∘ eqv) = hammingDist u v := by
  unfold hammingDist
  refine Finset.card_bij (fun a _ => eqv a) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at ha ⊢; exact ha
  · intro a _ b _ h; exact eqv.injective h
  · intro b hb
    refine ⟨eqv.symm b, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply] at hb ⊢; exact hb

/-- **Real-analysis closing step for C3.3.** Given the second-moment Johnson output
`M·(2η√ρ) ≤ 1` with `ρ ∈ (0,1]`, `η > 0`, one gets `M ≤ 1/(2ηρ)` (because
`√ρ ≥ ρ` on `(0,1]`). This is the final inequality of the C3.3 bound. -/
lemma mds_real_close (M ρ η : ℝ) (hM : 0 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hη : 0 < η) (hbound : M * (2 * η * Real.sqrt ρ) ≤ 1) :
    M ≤ 1 / (2 * η * ρ) := by
  have hsq : ρ ≤ Real.sqrt ρ := by
    have h := Real.sqrt_le_sqrt hρ1
    rw [Real.sqrt_one] at h
    nlinarith [Real.sq_sqrt hρ0.le, Real.sqrt_nonneg ρ, Real.sqrt_pos.mpr hρ0]
  have hden_pos : 0 < 2 * η * ρ := by positivity
  rw [le_div_iff₀ hden_pos]
  calc M * (2 * η * ρ) ≤ M * (2 * η * Real.sqrt ρ) := by
        apply mul_le_mul_of_nonneg_left _ hM; nlinarith [hsq]
    _ ≤ 1 := hbound

/-- **Reduced denominator inequality (frac-free core).** With `s = √ρ`, average radius
`e0 ∈ [0, 1 - s - η]`, relative distance `δ ≥ 1 - s²`, the elementary inequality
`2·η·s²·δ ≤ δ - 2·e0 + e0²` holds. This is the `frac = 1` reduction of the
second-moment denominator (the general `frac ≥ 1` case follows by `frac·e0² ≥ e0²`).
The proof is by monotonicity: the LHS-minus-RHS is decreasing in `e0` (on `[0,1]`) and
increasing in `δ`, so its minimum is the boundary value
`η·(η + 2s³ - 2s² + 2s) ≥ 0` (using `2s³ - 2s² + 1 > 0` on `(0,1)`). -/
lemma den_reduced
    (e0 δ s η : ℝ)
    (hη : 0 < η) (hs0 : 0 < s) (hs1 : s < 1)
    (he0_nonneg : 0 ≤ e0) (he0_le : e0 ≤ 1 - s - η) (hδ_ge : 1 - s^2 ≤ δ) :
    2 * η * s^2 * δ ≤ δ - 2 * e0 + e0^2 := by
  have hη_le : η ≤ 1 - s := by linarith
  have he0_le1 : e0 ≤ 1 := by linarith
  have hpoly : 0 < 2*s^3 - 2*s^2 + 1 := by
    nlinarith [sq_nonneg (s - 1), mul_nonneg hs0.le (sq_nonneg (s-1)), sq_nonneg s,
      mul_pos hs0 hs0, mul_nonneg hs0.le hs0.le]
  have h2ηs2 : 0 < 1 - 2 * η * s^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hη_le (mul_nonneg hs0.le hs0.le), hpoly]
  have hstep1 : (1 - s^2) * (1 - 2*η*s^2) ≤ δ * (1 - 2*η*s^2) :=
    mul_le_mul_of_nonneg_right hδ_ge h2ηs2.le
  have hmono : 2*e0 - e0^2 ≤ 2*(1-s-η) - (1-s-η)^2 := by
    nlinarith [he0_le, he0_nonneg, he0_le1]
  have hbdry : 0 ≤ (1 - s^2) * (1 - 2*η*s^2) - (2*(1-s-η) - (1-s-η)^2) := by
    nlinarith [mul_pos hη hη, mul_pos hη hs0, mul_pos hs0 (mul_pos hs0 hs0),
      mul_nonneg hη.le (mul_nonneg hs0.le (mul_nonneg hs0.le hs0.le)),
      mul_nonneg hη.le hs0.le, sq_nonneg s, mul_pos hη (mul_pos hs0 hs0)]
  nlinarith [hstep1, hmono, hbdry]

/-- **C3.3 second-moment core (over ℝ).** This is the complete, sound real-analysis
argument behind ABF26 Corollary 3.3 via the second-moment (`johnson_bound_lemma`) route.

Given the raw Johnson output `M · Den ≤ frac·δ` with `Den = (1 - frac·e0)² - (1 - frac·δ)`,
where `frac = q/(q-1) ≥ 1`, the average ball radius `e0 ∈ [0, 1 - √ρ - η]`, and the MDS
relative distance `δ ≥ 1 - ρ`, one concludes `M ≤ 1/(2·η·ρ)`.

**This generalises and corrects the `frac = 1` heuristic** in the prior C3.3 inline note:
the denominator there was approximated as `(√ρ+η)² - ρ = η(2√ρ+η)`, which is the `frac → 1`
(asymptotic) value. Here the bound is established for *every* `frac ≥ 1` (hence every finite
alphabet `q ≥ 2`), since `Den = frac·(δ - 2e0 + frac·e0²) ≥ frac·(δ - 2e0 + e0²) ≥
frac·(2ηρδ)` by `frac·e0² ≥ e0²` (`frac ≥ 1`) and `den_reduced`. Cancelling `frac·δ > 0`
from `M·(2ηρ·frac·δ) ≤ M·Den ≤ frac·δ` gives `M·(2ηρ) ≤ 1`. -/
lemma c33_core
    (M frac δ e0 ρ η : ℝ)
    (hM : 0 ≤ M)
    (hfrac1 : 1 ≤ frac)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hη : 0 < η)
    (he0_nonneg : 0 ≤ e0)
    (he0_le : e0 ≤ 1 - Real.sqrt ρ - η)
    (hδ_ge : 1 - ρ ≤ δ) (hδ_le : δ ≤ 1)
    (hjohnson : M * ((1 - frac * e0)^2 - (1 - frac * δ)) ≤ frac * δ) :
    M ≤ 1 / (2 * η * ρ) := by
  set s := Real.sqrt ρ with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hρ0
  have hs1 : s < 1 := by
    rw [hs]; calc Real.sqrt ρ < Real.sqrt 1 := Real.sqrt_lt_sqrt hρ0.le hρ1
      _ = 1 := Real.sqrt_one
  have hssq : s^2 = ρ := Real.sq_sqrt hρ0.le
  have hfrac_pos : 0 < frac := by linarith
  have hδ_pos : 0 < δ := by linarith [hρ1, hδ_ge]
  have hfracδ_pos : 0 < frac * δ := mul_pos hfrac_pos hδ_pos
  have hred : 2 * η * s^2 * δ ≤ δ - 2 * e0 + e0^2 := by
    apply den_reduced e0 δ s η hη hs0 hs1 he0_nonneg he0_le
    rw [hssq]; exact hδ_ge
  have hfe2 : e0^2 ≤ frac * e0^2 := le_mul_of_one_le_left (sq_nonneg e0) hfrac1
  have hDen_eq : (1 - frac * e0)^2 - (1 - frac * δ) = frac * (δ - 2*e0 + frac*e0^2) := by ring
  have hDen_ge : 2 * η * s^2 * (frac * δ) ≤ (1 - frac * e0)^2 - (1 - frac * δ) := by
    rw [hDen_eq, show 2 * η * s^2 * (frac * δ) = frac * (2 * η * s^2 * δ) by ring]
    apply mul_le_mul_of_nonneg_left _ hfrac_pos.le
    calc 2 * η * s^2 * δ ≤ δ - 2*e0 + e0^2 := hred
      _ ≤ δ - 2*e0 + frac*e0^2 := by linarith [hfe2]
  have hchain : M * (2 * η * s^2 * (frac * δ)) ≤ frac * δ := by
    calc M * (2 * η * s^2 * (frac * δ))
        ≤ M * ((1 - frac * e0)^2 - (1 - frac * δ)) := mul_le_mul_of_nonneg_left hDen_ge hM
      _ ≤ frac * δ := hjohnson
  have hcancel : M * (2 * η * s^2) ≤ 1 := by
    have h : (M * (2 * η * s^2)) * (frac * δ) ≤ 1 * (frac * δ) := by
      rw [show (M * (2 * η * s^2)) * (frac * δ) = M * (2 * η * s^2 * (frac * δ)) by ring, one_mul]
      exact hchain
    exact le_of_mul_le_mul_right h hfracδ_pos
  rw [hssq] at hcancel
  rw [le_div_iff₀ (by positivity)]
  linarith [hcancel]

end MdsPlotkin

/-- **ABF26 Corollary 3.3.** MDS coarse Johnson corollary. For every MDS code `C` with
rate `ρ := dim C / n` and `η > 0`:

  `|Λ(C, 1 - √ρ - η)| ≤ 1 / (2 · η · ρ)`

Derives from L2.6 (Singleton bound: MDS implies `δ_min = 1 - ρ + 1/n`, available via
the `IsMDS_iff_rate_distance` bridge) plus T3.2 (or its asymptotic version via `Jcap`).
Admitted as an external result; the path to a machine-checked proof requires the
asymptotic-Johnson form `Lambda C δ ≤ 1/(2·(Jcap δ - δ))` plus MDS rate-distance
manipulation.

**Rate derivation.** `ρ` is bound inline as `(Module.finrank F C : ℝ) / Fintype.card ι`
rather than passed as a separate parameter — this matches the upstream `IsMDS`
signature (additive Nat form, no rate parameter) and lets call sites use
`IsMDS_iff_rate_distance` to extract the rate-distance equation when needed. -/
theorem mds_johnson_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (η : ℝ) (_hη_pos : 0 < η)
    (_h_mds : LinearCode.IsMDS C) :
    let ρ : ℝ := (Module.finrank F C : ℝ) / Fintype.card ι
    (Lambda ((C : Set (ι → F))) (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  -- ABF26-C3.3; PARTIAL. The MATHEMATICAL core of C3.3 via the second-moment
  -- (`johnson_bound_lemma`) route is now FULLY PROVEN, `sorry`-free and axiom-clean,
  -- as `MdsPlotkin.c33_core` above:
  --
  --   M·[(1-frac·e0)² - (1-frac·δ)] ≤ frac·δ,  frac = q/(q-1) ≥ 1,  e0 ∈ [0,1-√ρ-η],
  --   δ ≥ 1-ρ                                ⟹   M ≤ 1/(2·η·ρ).
  --
  -- CORRECTION to the prior C3.3 inline FINDING: that note approximated the Johnson
  -- denominator as `(√ρ+η)² - ρ = η(2√ρ+η)`, which is the `frac → 1` (asymptotic q→∞)
  -- value only. The in-tree `johnson_bound_lemma` carries the genuine factor
  -- `frac = q/(q-1) > 1`, so the `frac = 1` algebra does not apply directly. `c33_core`
  -- (with helper `MdsPlotkin.den_reduced`) establishes the bound for EVERY `frac ≥ 1`:
  --   Den = frac·(δ - 2e0 + frac·e0²) ≥ frac·(δ - 2e0 + e0²) ≥ frac·(2ηρδ),
  -- using `frac·e0² ≥ e0²` and the elementary `2ηρδ ≤ δ - 2e0 + e0²` (`den_reduced`,
  -- proven by `e0`/`δ` monotonicity to the boundary value `η(η+2s³-2s²+2s) ≥ 0`,
  -- `s = √ρ`). Cancelling `frac·δ > 0` gives `M·2ηρ ≤ 1`. This is the real wall and it
  -- is now down.
  --
  -- Also reusable above (all `sorry`-free / axiom-clean):
  -- `plotkin_d_le` (q-ary Plotkin avg-distance, the tight-ℓ T3.2 ingredient),
  -- `hammingDist_reindex` (index transport), `mds_real_close` (√ρ ≥ ρ step).
  --
  -- REMAINING (the single `sorry`): the mechanical `Lambda`→`c33_core` bridge —
  --   (a) `Lambda C r = ⨆_f ncard`; `ι → F` finite ⇒ sup attained at some `f`
  --       (`Finite.exists_max`); reduce to `((closeCodewordsRel C f r).ncard : ℝ) ≤ B`
  --       then `(· : ℕ∞) ≤ ENNReal.ofReal B` via `ENNReal.ofReal_natCast`.
  --   (b) materialise `closeCodewordsRel C f r` as `Set.toFinset`; rewrite membership
  --       `Code.relHammingDist f c ≤ r` to `(Δ₀(f,c) : ℝ)/card ι ≤ r`.
  --   (c) reindex the ball + centre `ι → F` ⇝ `Fin (card ι) → F` via `σ : Fin n ≃ ι`,
  --       transport `e`, `d`, `Code.minDist` through `hammingDist_reindex`-style maps.
  --   (d) `e B' f ≤ r·n` (`e_ball_le_radius`), `d B' ≥ minDist` (`min_dist_le_d`),
  --       MDS `minDist/n = 1-ρ+1/n ≥ 1-ρ` (`IsMDS_iff_rate_distance`), `ρ ∈ (0,1)`.
  --   (e) feed `johnson_bound_lemma` (after its ℚ→ℝ cast) into `c33_core`.
  -- Left as `sorry` rather than risk a subtle unsound cast/reindex step; false PROVEN
  -- is the worst outcome. The non-mechanical mathematics of C3.3 is fully discharged.
  sorry

end CodingTheory
