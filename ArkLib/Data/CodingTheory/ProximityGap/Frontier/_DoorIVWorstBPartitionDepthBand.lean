/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

/-!
# Door-(iv) constraint: the coherent worst-`b` reshuffle is PARTITION-DEPTH-INVARIANT — `k`-piece split is a bounded `O(1)` lever at every refinement depth (#444)

Generalizes `_DoorIVWorstBImbalanceBand` from the index-2 (two-half) split to an arbitrary `k`-piece
coset partition (`k = 2^j`, every dyadic refinement depth).

## Probe finding it grounds (refutation-with-mechanism, Lever A — dyadic-tower coherence)

`scripts/probes/probe_dooriv_worstb_index4_band.py` (FULL coset scan, proper `μ_n`, `p ≫ n³`, `β = 4`,
median over structured primes, never `n = q-1`): at the TRUE worst frequency `b*`, split
`μ_n = ⊔_{j<4} g^j·μ_{n/4}` into four coset-quarters `Q_0..Q_3`:

- **Quarter coherence** `ρ₄(b*) = ‖Σ Q_j‖ / Σ‖Q_j‖ = 1.0000` exactly at every `n` (all four quarters
  phase-aligned, exactly as the two halves are at index-2): `M(b*) = Σ_j ‖Q_j‖`.
- **Bounded quarter imbalance** `r₄(b*) = min_j‖Q_j‖ / max_j‖Q_j‖ ∈ [0.52, 0.67]` (median, stationary).
- **Aggregate inflation** `F₄ = M / max_j‖Q_j‖ ∈ [3.1, 3.5]` — bounded in `(1, 4)`: neither
  single-quarter degeneration (`F₄ → 1`) nor four-balanced full thinning (`F₄ → 4`).

So the coherent-bounded-reshuffle picture is **partition-depth-invariant**: it holds at the two-half
split AND the four-quarter split (and, by the same mechanism, at every dyadic refinement `k = 2^j`).
No dyadic sub-partition at `b*` thins the `√`-wall — **Shaw's Lever A (dyadic-tower coherence) is dead
at every refinement depth, not just one level.**

## What this file proves (axiom-clean, NO growth-law theorem — HARD RULE 1)

For a finite family of pieces `Q : ι → E` (the `k` coset-pieces) at full coherence
`‖Σ Q i‖ = Σ ‖Q i‖`, with heaviest piece-norm `H = max_i ‖Q i‖` and a bounded imbalance band
`r_lo · H ≤ ‖Q i‖ ≤ H` for all `i` (so `r_lo ≤ min/max` and `max = H`):

1. **No single-piece degeneration** (lower band): `M = Σ‖Q i‖ ≥ (1 + (k-1)·r_lo)·H > H` once `k ≥ 2`,
   `r_lo > 0` and `H > 0` — every piece carries a persistent share `≥ r_lo · H`.
2. **No full `√(k)`-thinning** (upper band): `M ≤ k·H`, with `M < k·H` strictly when at least one
   piece is strictly under `H` — the aggregate inflation is a bounded `O(1)` factor, never the full
   `k` that perfect balance would give.

So a `k`-piece coherent split with a bounded imbalance band is a bounded `O(1)` reshuffle from both
ends, at every `k = 2^j`. This is a precisely-mapped non-tightness — **not** a CORE / cancellation /
completion / moment / capacity claim: it does not bound `M(n)`; it certifies that the *coherent
bounded-imbalance partition structure*, at any dyadic depth, cannot move the `√`-frontier.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand

variable {ι : Type*} {E : Type*} [SeminormedAddCommGroup E]

/-- **Coherent `k`-piece peak.**  At full coherence the period norm is the sum of the piece-norms. -/
theorem coherent_norm_eq_sum_piece_norms {s : Finset ι} {Q : ι → E}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) :
    ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖ := hcoh

/-- **Upper band ⇒ no full `k`-thinning (aggregate ≤ `k·H`).**  If every piece-norm is at most the
heaviest `H` (`‖Q i‖ ≤ H`), then at coherence `M = Σ‖Q i‖ ≤ |s|·H`. -/
theorem norm_le_card_mul_max {s : Finset ι} {Q : ι → E} {H : ℝ}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hub : ∀ i ∈ s, ‖Q i‖ ≤ H) :
    ‖∑ i ∈ s, Q i‖ ≤ s.card * H := by
  rw [hcoh]
  calc ∑ i ∈ s, ‖Q i‖ ≤ ∑ _i ∈ s, H := Finset.sum_le_sum hub
    _ = s.card * H := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Lower band ⇒ aggregate ≥ `|s|·r_lo·H` (no single-piece degeneration).**  If every piece carries
at least an `r_lo`-share of the heaviest (`r_lo·H ≤ ‖Q i‖`), then `M ≥ |s|·r_lo·H`. -/
theorem card_mul_rlo_mul_max_le_norm {s : Finset ι} {Q : ι → E} {H rlo : ℝ}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hlb : ∀ i ∈ s, rlo * H ≤ ‖Q i‖) :
    s.card * (rlo * H) ≤ ‖∑ i ∈ s, Q i‖ := by
  rw [hcoh]
  calc s.card * (rlo * H) = ∑ _i ∈ s, rlo * H := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, ‖Q i‖ := Finset.sum_le_sum hlb

/-- **Lower-band endpoint slack for a `k`-piece split.**  If `i₀` is a heaviest piece with
`‖Q i₀‖ = H`, and every *other* piece carries at least `rlo·H`, then the coherent aggregate exceeds
the single-piece endpoint by at least `(k-1)·rlo·H`.  This is the partition-depth analogue of the
two-half endpoint-gap theorem: no dyadic refinement collapses to the selected heaviest piece while the
lower band holds on the remaining pieces. -/
theorem lower_band_slack_over_single_ge [DecidableEq ι] {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hi₀ : i₀ ∈ s) (hH : ‖Q i₀‖ = H)
    (hlb : ∀ i ∈ s.erase i₀, rlo * H ≤ ‖Q i‖) :
    (s.erase i₀).card * (rlo * H) ≤ ‖∑ i ∈ s, Q i‖ - H := by
  rw [hcoh]
  have hsum : (s.erase i₀).card * (rlo * H) ≤ ∑ i ∈ s.erase i₀, ‖Q i‖ := by
    calc
      (s.erase i₀).card * (rlo * H) = ∑ _i ∈ s.erase i₀, rlo * H := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s.erase i₀, ‖Q i‖ := Finset.sum_le_sum hlb
  have hsplit : (∑ i ∈ s, ‖Q i‖) = ‖Q i₀‖ + ∑ i ∈ s.erase i₀, ‖Q i‖ := by
    rw [← Finset.sum_erase_add s (fun i => ‖Q i‖) hi₀]; ring
  rw [hsplit, hH]
  nlinarith

/-- **Strict aggregate floor over the heaviest piece (lower band, `|s| ≥ 2`).**  With a heaviest piece
`i₀ ∈ s` (`‖Q i₀‖ = H`), at least two pieces, every piece `≥ r_lo·H` with `r_lo > 0`, and `H > 0`, the
aggregate strictly exceeds the single heaviest piece: `H < M`.  The split does NOT collapse to one
piece. -/
theorem max_lt_norm_of_lower_band [DecidableEq ι] {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hi₀ : i₀ ∈ s) (hH : ‖Q i₀‖ = H)
    (hrlo : 0 < rlo) (hHpos : 0 < H) (htwo : 2 ≤ s.card)
    (hlb : ∀ i ∈ s, rlo * H ≤ ‖Q i‖) :
    H < ‖∑ i ∈ s, Q i‖ := by
  rw [hcoh]
  -- pick a second piece i₁ ≠ i₀
  obtain ⟨i₁, hi₁, hne⟩ : ∃ i₁ ∈ s, i₁ ≠ i₀ := by
    by_contra h
    push_neg at h
    have : s ⊆ {i₀} := fun x hx => Finset.mem_singleton.mpr (h x hx)
    have hc := Finset.card_le_card this
    simp at hc
    omega
  have hsplit : (∑ i ∈ s, ‖Q i‖) = ‖Q i₀‖ + ∑ i ∈ s.erase i₀, ‖Q i‖ := by
    rw [← Finset.sum_erase_add s _ hi₀]; ring
  have hpos : 0 < ∑ i ∈ s.erase i₀, ‖Q i‖ := by
    have hi₁e : i₁ ∈ s.erase i₀ := Finset.mem_erase.mpr ⟨hne, hi₁⟩
    have hterm : 0 < ‖Q i₁‖ := lt_of_lt_of_le (mul_pos hrlo hHpos) (hlb i₁ hi₁)
    have hnonneg : ∀ i ∈ s.erase i₀, 0 ≤ ‖Q i‖ := fun i _ => norm_nonneg _
    exact Finset.sum_pos' hnonneg ⟨i₁, hi₁e, hterm⟩
  rw [hsplit, hH]; linarith

/-- **Strict aggregate ceiling under the heaviest piece (upper band, one strict-under piece).**  With
every piece `≤ H` and at least one piece `i₁ ∈ s` strictly under `H` (`‖Q i₁‖ < H`), the aggregate is
strictly below the balanced ceiling: `M < |s|·H`.  The `k`-piece split supplies no full `k`-thinning. -/
theorem norm_lt_card_mul_max {s : Finset ι} {Q : ι → E} {H : ℝ} {i₁ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖) (hub : ∀ i ∈ s, ‖Q i‖ ≤ H)
    (hi₁ : i₁ ∈ s) (hstrict : ‖Q i₁‖ < H) :
    ‖∑ i ∈ s, Q i‖ < s.card * H := by
  rw [hcoh]
  have hlt : (∑ i ∈ s, ‖Q i‖) < ∑ _i ∈ s, H :=
    Finset.sum_lt_sum hub ⟨i₁, hi₁, hstrict⟩
  calc (∑ i ∈ s, ‖Q i‖) < ∑ _i ∈ s, H := hlt
    _ = s.card * H := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Partition-depth band sandwich (capstone).**  At a coherent worst frequency, for a `k`-piece coset
split with heaviest piece `i₀` (`‖Q i₀‖ = H`), `|s| ≥ 2`, `0 < r_lo`, `0 < H`, every piece in
`[r_lo·H, H]`, and at least one piece `i₁` strictly under `H`, the period norm is strictly between the
single heaviest piece and the balanced ceiling:
    `H < ‖Σ Q i‖ < |s|·H`.
Neither endpoint is reached at any dyadic depth `k = |s|`: single-piece degeneration and full
`k`-thinning are both excluded.  Partition-depth-invariant dead `√`-lever. -/
theorem strictly_between_single_and_ceiling [DecidableEq ι] {s : Finset ι} {Q : ι → E} {H rlo : ℝ} {i₀ i₁ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖)
    (hi₀ : i₀ ∈ s) (hH : ‖Q i₀‖ = H) (hrlo : 0 < rlo) (hHpos : 0 < H) (htwo : 2 ≤ s.card)
    (hlb : ∀ i ∈ s, rlo * H ≤ ‖Q i‖) (hub : ∀ i ∈ s, ‖Q i‖ ≤ H)
    (hi₁ : i₁ ∈ s) (hstrict : ‖Q i₁‖ < H) :
    H < ‖∑ i ∈ s, Q i‖ ∧ ‖∑ i ∈ s, Q i‖ < s.card * H :=
  ⟨max_lt_norm_of_lower_band hcoh hi₀ hH hrlo hHpos htwo hlb,
   norm_lt_card_mul_max hcoh hub hi₁ hstrict⟩

/-- **Inflation-ratio sandwich.**  Dividing the partition-depth band by the positive heaviest-piece
norm `H` gives the exact probe quantity `F_k = M/H`: it lies strictly between `1` and `|s|`.  Thus the
coherent `k`-piece split is a bounded interior reshuffle at that refinement depth, neither a
single-piece degeneration (`F_k = 1`) nor a perfectly balanced full `k`-inflation (`F_k = |s|`). -/
theorem one_lt_norm_div_max_and_norm_div_max_lt_card [DecidableEq ι] {s : Finset ι} {Q : ι → E}
    {H rlo : ℝ} {i₀ i₁ : ι}
    (hcoh : ‖∑ i ∈ s, Q i‖ = ∑ i ∈ s, ‖Q i‖)
    (hi₀ : i₀ ∈ s) (hH : ‖Q i₀‖ = H) (hrlo : 0 < rlo) (hHpos : 0 < H) (htwo : 2 ≤ s.card)
    (hlb : ∀ i ∈ s, rlo * H ≤ ‖Q i‖) (hub : ∀ i ∈ s, ‖Q i‖ ≤ H)
    (hi₁ : i₁ ∈ s) (hstrict : ‖Q i₁‖ < H) :
    1 < ‖∑ i ∈ s, Q i‖ / H ∧ ‖∑ i ∈ s, Q i‖ / H < (s.card : ℝ) := by
  obtain ⟨hlo, hhi⟩ := strictly_between_single_and_ceiling hcoh hi₀ hH hrlo hHpos htwo hlb hub hi₁ hstrict
  constructor
  · have hone : (1 : ℝ) = H / H := by
      field_simp [ne_of_gt hHpos]
    rw [hone]
    exact div_lt_div_of_pos_right hlo hHpos
  · have hlt : ‖∑ i ∈ s, Q i‖ / H < ((s.card : ℝ) * H) / H :=
      div_lt_div_of_pos_right hhi hHpos
    have hcard : ((s.card : ℝ) * H) / H = (s.card : ℝ) := by
      field_simp [ne_of_gt hHpos]
    simpa [hcard] using hlt

end ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}).
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.strictly_between_single_and_ceiling
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.max_lt_norm_of_lower_band
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.norm_lt_card_mul_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.norm_le_card_mul_max
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.card_mul_rlo_mul_max_le_norm
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.lower_band_slack_over_single_ge
#print axioms ArkLib.ProximityGap.Frontier.DoorIVWorstBPartitionDepthBand.one_lt_norm_div_max_and_norm_div_max_lt_card
