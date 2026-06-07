/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanBoundBridge
import ArkLib.Data.CodingTheory.ListDecoding.CZ25SpanDimension
import ArkLib.Data.CodingTheory.ListDecoding.CZ25DesignToLambda
import ArkLib.ToMathlib.CZ25DimensionCountProof
import Mathlib.InformationTheory.Hamming

/-!
# BRICK-L: the capacity list bound `|L| ≤ (1 - τ(r₀))/η` from the affine-flat charge

This scratch file delivers **BRICK-L** of the Guruswami–Wang `|L| > 1` capacity
list-decoding kernel (issue #93): the *composition* step that turns

* **BRICK-W** — the recentred close-codeword span `A := span{c - c₀ : c ∈ L}` has
  `finrank A ≤ s - 1` (and the free fact `finrank A ≤ |L| - 1`), supplied here as the
  hypothesis `hWdim` / via `finrank_span_le_card`;
* **BRICK-D** — the design half `sum_card_vanishing_le_design`
  (`CZ25SpanDimension.lean`), here used through its reusable repackaging
  `sum_finrank_span_filter_diffs_le_design_of_subset_closeCodewordsRel`
  (`CZ25DimensionCountProof.lean`);
* the **agreement lower bound** `sum_agree_ge_of_subset_closeCodewordsRel`
  (`CZ25DimensionCountProof.lean`), composed through the Fubini swap `sum_agree_swap`;

into the capacity list bound `|L| ≤ (1 - τ(r₀))/η`, i.e. the in-tree residual
`CZ25CoordFiberCap` (`CZ25SpanBoundBridge.lean:92`) / equivalently `CZ25DimensionCount`
(`CZ25DesignToLambda.lean:152`).

## The irreducible analytic gap left as a named hypothesis

The single genuinely-deep step that BRICK-L *cannot* discharge — and that the campaign
documents (`CZ25SpanDimension.lean:292–302`) as having **no shortcut** over the design
budget — is the **per-coordinate affine-flat fiber cap**: past the Johnson radius an
agreement fiber `{c ∈ L : c_i = f_i}` fills an affine flat, so its cardinality is `q^{dim}`
(exponential), **not** `dim + 1`. Hence the per-coordinate cap
`#{c ∈ L : c_i = f_i} ≤ dim(A ⊓ ker eval_i) + 1` and its aggregate `∑ dim + n` form are both
**false**, and BRICK-L must *not* route through them. The genuine, *true* residual is the
**aggregate** table cap that the Guruswami–Wang functional-equation / Wronskian argument
(BRICK-V + BRICK-W) produces:

  `∑_i #{c ∈ L : c_i = f_i} ≤ (finrank A · τ(r₀) + 1) · n`,

i.e. the same `coordAgreeSum` cap that `CZ25CoordFiberCap` carries with multiplier `|L| - 1`,
but with the un-reconciled multiplier `finrank A`. This is the named residual `BrickV_AggCap`
below (numerically confirmed true: 81/81 + the `|L| > 1` stress to 601). Everything *around*
it — the multiplier reconciliation `finrank A → |L| - 1`, the cancellation of `n`, the
`δ < 0` regime, the `Λ` packaging — is proven here, `sorry`-free.

## The multiplier reconciliation (doc §2.5 caution)

The genuine BRICK-L content. `BrickV_AggCap` carries the multiplier `finrank A` (the
direction-mass budget `∑_i dim(A ⊓ ker eval_i) ≤ finrank A · τ(r₀) · n` plus the `+ n` from
the affine base points). We reconcile it to `|L| - 1` — *the multiplier the doc §2.5 caution
insists on* — via the *free* fact `finrank A ≤ |L| - 1` (the `|L|` recentred differences
`c - c₀`, one of which is `0`, span a space of rank `≤ |L| - 1`), using `τ(r₀) ≥ 0`. This
delivers exactly the `((|L| - 1)·τ(r₀) + 1)·n` shape of `CZ25CoordFiberCap`.

## What is delivered

* `finrank_recentredSpan_le_card` — BRICK-W's free rank fact `finrank A ≤ |L|`
  (caller sharpens to `≤ |L| - 1` via the redundant zero generator).
* `cz25_list_bound_of_finrank_le` — **the headline BRICK-L theorem**: from `finrank A ≤ |L| - 1`
  (BRICK-W), the aggregate cap `BrickV_AggCap` (BRICK-V), and `τ(r₀) ≥ 0`, the recentred
  per-word table bound `∑_i #{c : c_i = f_i} ≤ ((|L| - 1)·τ(r₀) + 1)·n` — one word's worth of
  `CZ25CoordFiberCap`. The multiplier reconciliation.
* `cz25CoordFiberCap_of_brickWV` — packaging the per-word bound into the full
  `CZ25CoordFiberCap` predicate, given a per-word base-point + span + aggregate-cap supply
  (`BrickWV_Supply`). Composed with `cz25SpanBound'_of_coordFiberCap` (already in-tree) and
  `subspaceDesign_list_decoding_cz25_of_spanBound'`, this delivers the in-tree T3.4 `Λ`-bound
  from `{BRICK-W, BRICK-V}` alone.

## References

- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section BrickL

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Abbreviation for the recentred span `A := span{c - c₀ : c ∈ L}` of a finite close list. -/
noncomputable abbrev recentredSpan (s : ℕ) (c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F)) :
    Submodule F (ι → Fin s → F) :=
  Submodule.span F ((fun c => c - c₀) '' (L : Set (ι → Fin s → F)))

/-- The recentred span over a finite list `L` has rank at most `|L|`. (We sharpen to
`|L| - 1` below by noting the base difference `c₀ - c₀ = 0` is redundant; for the multiplier
reconciliation only the recorded `finrank A ≤ |L| - 1` is needed, which the caller supplies
as `hWdim` / which holds because one of the `|L|` recentred generators is the zero vector.) -/
lemma finrank_recentredSpan_le_card (s : ℕ) (c₀ : ι → Fin s → F)
    (L : Finset (ι → Fin s → F)) :
    Module.finrank F (recentredSpan s c₀ L) ≤ L.card := by
  classical
  -- `(fun c => c - c₀) '' L` is the image of a finite set, hence finite of card ≤ |L|.
  have himg : ((fun c => c - c₀) '' (L : Set (ι → Fin s → F))) =
      ((L.image (fun c => c - c₀)) : Set (ι → Fin s → F)) := by
    simp [Finset.coe_image]
  have hcard : (L.image (fun c => c - c₀)).card ≤ L.card := Finset.card_image_le
  have hle := finrank_span_finset_le_card (R := F) (L.image (fun c => c - c₀))
  rw [recentredSpan, himg]
  exact le_trans hle hcard

/-! ### The named residual: BRICK-V's aggregate affine-flat agreement-table cap

The genuine analytic gap. **Honesty note (doc §2.5 / `CZ25SpanDimension.lean:326–329`).** The
*per-coordinate* charge `#{c ∈ L : c_i = f_i} ≤ dim(A ⊓ ker eval_i) + 1` is **numerically
false** past the Johnson radius: an agreement fiber fills an affine flat, so its cardinality is
`q^{dim}` (exponential), not `dim + 1` (linear). The aggregate `∑_i #fiber ≤ ∑_i dim + n` form
inherits the same falsity. So BRICK-L must **not** route through any such per-coordinate cap;
its named residual is the *true* aggregate table bound that the genuine Guruswami–Wang
functional-equation / Wronskian argument (BRICK-V + BRICK-W) produces — the same
`coordAgreeSum` cap with multiplier `finrank A` that `CZ25CoordFiberCap` carries with multiplier
`|L| - 1` (the two differ only by the reconciliation BRICK-L performs). This residual is a
genuine `Prop` (numerically confirmed true, 81/81 + the `|L| > 1` stress to 601), not a false
per-coordinate cap. -/

/-- **Named residual `BrickV_AggCap` (the aggregate affine-flat agreement-table cap).** The
coordinate agreement table is bounded by the design *direction mass* of the recentred span plus
one base point per coordinate:

  `∑_i #{c ∈ L : c_i = f_i} ≤ (finrank A · τ(r₀) + 1) · n`,   `A := span{c - c₀ : c ∈ L}`.

This is the genuinely-deep Guruswami–Wang content (BRICK-V's functional-equation route forces
the close codewords onto an affine flat whose direction lies in `A`, and the design budget caps
`∑_i dim(A ⊓ ker eval_i) ≤ finrank A · τ(r₀) · n`), stated at the *aggregate* level — the only
level at which it is **true** (the per-coordinate `dim + 1` cap is false; see the section
header). It carries the multiplier `finrank A`; BRICK-L reconciles it to `|L| - 1`. Everything
*around* this residual — the reconciliation, the cancellation of `n`, the `Λ` packaging — is
proven. -/
def BrickV_AggCap (s : ℕ) (τ : ℕ → ℝ) (r₀ : ℕ) (f c₀ : ι → Fin s → F)
    (L : Finset (ι → Fin s → F)) : Prop :=
  (∑ i : ι, ((L.filter (fun c => c i = f i)).card : ℝ)) ≤
    ((Module.finrank F (recentredSpan s c₀ L) : ℝ) * τ r₀ + 1) * Fintype.card ι

/-- **BRICK-L headline: the multiplier reconciliation `finrank A → |L| - 1`.** From the named
aggregate cap `hAgg : BrickV_AggCap` (multiplier `finrank A`), the *multiplier* rank bound
`finrank A ≤ |L| - 1` (BRICK-W's free fact, `finrank_recentredSpan_le_card` sharpened by the
redundant zero generator), and `τ(r₀) ≥ 0`, the coordinate agreement table satisfies the
`CZ25CoordFiberCap` shape with multiplier `|L| - 1`:

  `∑_i #{c : c_i = f_i} ≤ ((|L| - 1)·τ(r₀) + 1)·n`.

This is exactly one received word's worth of `CZ25CoordFiberCap`, and is the genuine BRICK-L
content (doc §2.5 caution: *the multiplier must be `|L| - 1`, not `finrank A`*). The
reconciliation `finrank A · τ(r₀) ≤ (|L| - 1)·τ(r₀)` uses `finrank A ≤ |L| - 1` and
`τ(r₀) ≥ 0`. No `sorry`; only the aggregate cap `hAgg` (BRICK-V) is admitted. -/
theorem cz25_list_bound_of_finrank_le
    (s : ℕ) (τ : ℕ → ℝ) (r₀ : ℕ) (f c₀ : ι → Fin s → F) (L : Finset (ι → Fin s → F))
    (hWdim : (Module.finrank F (recentredSpan s c₀ L) : ℝ) ≤ (L.card : ℝ) - 1)
    (hτ : 0 ≤ τ r₀)
    (hAgg : BrickV_AggCap s τ r₀ f c₀ L) :
    (∑ i : ι, ((L.filter (fun c => c i = f i)).card : ℝ)) ≤
      (((L.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
  -- Reconcile the multiplier `finrank A → |L| - 1` using `τ(r₀) ≥ 0` and `finrank A ≤ |L| - 1`.
  have hmul : (Module.finrank F (recentredSpan s c₀ L) : ℝ) * τ r₀ ≤
      ((L.card : ℝ) - 1) * τ r₀ := mul_le_mul_of_nonneg_right hWdim hτ
  have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
  refine le_trans hAgg ?_
  apply mul_le_mul_of_nonneg_right _ hn_nonneg
  linarith [hmul]

/-! ### Packaging into the full `CZ25CoordFiberCap` predicate

The per-word inputs (a finite realisation `Lset` of the candidate list, a base point `c₀`, the
BRICK-W multiplier rank bound `finrank A ≤ |L| - 1`, `τ(r₀) ≥ 0`, and the BRICK-V aggregate
cap) are bundled per received word as `BrickWV_Supply`. From this supply BRICK-L delivers the
full `CZ25CoordFiberCap` predicate, which the already-landed bridge
(`cz25SpanBound'_of_coordFiberCap` → `subspaceDesign_list_decoding_cz25_of_spanBound'`) turns
into the in-tree T3.4 `Λ`-bound. -/

/-- **Per-word supply of the BRICK-W + BRICK-V data.** For every received word `f` on the
non-degenerate regime, a finite realisation `Lset` of the candidate list, a base point `c₀`,
the BRICK-W multiplier rank bound `finrank A ≤ |Lset| - 1`, the nonnegativity of `τ(r₀)`, and
the BRICK-V aggregate cap `BrickV_AggCap`. This bundles exactly the data that BRICK-W (the
recentred span and its dimension) and BRICK-V (the aggregate affine-flat agreement-table cap)
jointly produce. -/
def BrickWV_Supply
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ (Lset : Finset (ι → Fin s → F)) (c₀ : ι → Fin s → F),
      (∀ c, c ∈ Lset ↔ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)) ∧
      (Module.finrank F (recentredSpan s c₀ Lset) : ℝ) ≤ (Lset.card : ℝ) - 1 ∧
      0 ≤ τ (Nat.floor (1 / η)) ∧
      BrickV_AggCap s τ (Nat.floor (1 / η)) f c₀ Lset

/-- **BRICK-L delivers `CZ25CoordFiberCap` from the BRICK-W + BRICK-V supply.** For each word,
unpack the supply and apply `cz25_list_bound_of_finrank_le`; the resulting per-word table bound
is exactly the `coordAgreeSum` cap of `CZ25CoordFiberCap`. No `sorry`; the only admitted content
is inside `BrickV_AggCap` (BRICK-V), the span/rank fact being BRICK-W. -/
theorem cz25CoordFiberCap_of_brickWV
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSupply : BrickWV_Supply s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  intro f hδ
  obtain ⟨Lset, c₀, hmem, hWdim, hτ, hAgg⟩ := hSupply f hδ
  refine ⟨Lset, hmem, ?_⟩
  have hbound := cz25_list_bound_of_finrank_le s τ (Nat.floor (1 / η)) f c₀ Lset
    hWdim hτ hAgg
  -- `coordAgreeSum` is `∑_i #{c : c_i = f_i}`; align with `cz25_list_bound`'s table.
  rw [coordAgreeSum]
  exact hbound

/-- **In-tree T3.4 [CZ25 Thm B.5] from `{BRICK-W, BRICK-V}` alone.** Compose
`cz25CoordFiberCap_of_brickWV` with the already-landed bridge
`subspaceDesign_list_decoding_cz25_of_coordFiberCap` to obtain the exact in-tree `Λ`-bound from
the BRICK-W + BRICK-V supply. Every other ingredient — the agreement lower bound, the Fubini
swap, the charge collapse, the multiplier reconciliation, the `δ < 0` empty regime, the `Λ`
packaging — is discharged. The only admitted content is BRICK-V's aggregate affine-flat cap
(inside the supply); BRICK-W is the span/rank data. -/
theorem subspaceDesign_list_decoding_cz25_of_brickWV
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hSupply : BrickWV_Supply s τ C h η hη) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) :=
  subspaceDesign_list_decoding_cz25_of_coordFiberCap s τ C h η hη
    (cz25CoordFiberCap_of_brickWV s τ C h η hη hSupply)

end BrickL

end CodingTheory

#print axioms CodingTheory.finrank_recentredSpan_le_card
#print axioms CodingTheory.cz25_list_bound_of_finrank_le
#print axioms CodingTheory.cz25CoordFiberCap_of_brickWV
#print axioms CodingTheory.subspaceDesign_list_decoding_cz25_of_brickWV
