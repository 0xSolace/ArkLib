/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Order.Floor.Extended

/-!
# List-decoding bounds from ABF26 §3

External-admit *statements* for the §3 list-decoding bounds from ABF26
(Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026).
Each theorem is admitted as an external result with a tagged `sorry`, matching the
pattern established by `ProximityGap.CapacityBounds`. The statements use the
`ListDecodable.Lambda` function (block-maximised list size) introduced in
`ListDecodability.lean`, plus `qEntropy` from `Basic/Entropy.lean` and
`hammingBallVolume` from `HammingBallVolume.lean`.

These bounds sit immediately above the Grand List Decoding Challenge in ABF26 §1:
upper bounds (T3.2, C3.3) give candidate witnesses `δ_C*` for `|Λ(C^≡m, δ_C*)| ≤ ε*·|F|`,
while lower bounds (L3.7, C3.8, T3.9–T3.14) rule out witnesses above a threshold.

## Quantification conventions

The §3.2 / §3.2 RS theorems quantify over "infinitely many `q`", existentially-bound
codes, and "sufficiently large `n`". We capture these uniformly as follows:

- *Type-level data* (alphabet `F`, index type `ι`) is **universally** quantified at the
  theorem's outermost binder. The user instantiates at the call site.
- *Numeric quantifiers* ("there exists `α > 0`", "there exists `γ > 0`",
  "for infinitely many `q`") stay inside the theorem body using `∃` on numeric data.
- *Sufficiently large `n`* is captured as an explicit existential threshold `n₀ : ℕ`
  followed by `n₀ ≤ Fintype.card ι`. This matches Mathlib's `Filter.eventually`
  shape without dragging filters into a pure statement.
- *Infinitely many `q`* is captured as `∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, P (qs i)`.

## Main statements (external admits)

### Lower bounds — general codes (§3.2)

- `linear_lambda_ge_elias_volume_eli57` — ABF26 L3.7 [Eli57]: `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^{n-k}`.
- `linear_lambda_ge_entropy_volume` — ABF26 C3.8: `|Λ(C, δ)| ≥ q^{n(ρ-1+H_q(δ))} / √(8nδ(1-δ))`.
- `linear_C_le_generalized_singleton_st20` — ABF26 T3.9 [ST20 Thm 1.2]: bound on `|C|`
  when `|Λ(C, δ)| ≤ ℓ`.
- `large_alphabet_barrier_bdg24_agl23` — ABF26 T3.10: any code attaining the generalized
  Singleton bound requires exponential-in-`1/η` alphabet.
- `random_linear_lambda_lower_glmrsw22` — ABF26 T3.11 [GLMRSW22 Thm 4.1]: random linear
  code of appropriate rate has list size lower-bounded with high probability.

### Lower bounds — Reed-Solomon (§3.2)

- `rs_lambda_superpoly_extension_bkr06` — ABF26 T3.12 [BKR06 Cor 2.2]: superpolynomial
  list-size for RS over extension fields.
- `rs_lambda_large_prime_ghsz02` — ABF26 T3.13 [GHSZ02 Cor 20]: large list-size for RS
  over prime fields.
- `rs_lambda_high_rate_jh01` — ABF26 T3.14 [JH01 Thm 2]: large-rate RS list-size
  separation.

### Subspace-design upper bounds (§3.1)

- `subspaceDesign_list_decoding_cz25` — ABF26 T3.4 [CZ25 Thm B.5]: τ-subspace-design
  codes are list-decodable up to capacity.
- `frs_list_decoding_capacity_cz25` — ABF26 C3.5 [CZ25 Cor 2.21]: folded RS codes
  are list-decodable up to capacity (corollary of T3.4 via T2.18).

## Deferred statements

- ABF26 T3.6 [AGL24 Thm 1.1] — random Reed-Solomon list decoding near capacity; blocked
  on a uniform distribution over size-`n` subsets of `F` (same blocker as T4.15).
- ABF26 T3.15 [CW07] — algorithmic hardness barrier (discrete-log reduction). Out of
  scope per `docs/kb/ABF26_PLAN.md` §7 D2 (we formalise combinatorial statements only).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Eli57] Elias. (Lemma 3.7 in ABF26 cites the original Elias paper).
- [ST20] Shangguan-Tamo. Theorem 1.2.
- [BDG24], [AGL23] (Theorem 3.10 in ABF26).
- [GLMRSW22] (Theorem 4.1, source of T3.11).
- [BKR06] Cor 2.2, source of T3.12.
- [GHSZ02] Cor 20, source of T3.13.
- [JH01] Theorem 2, source of T3.14.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace CodingTheory

open scoped NNReal
open ListDecodable Finset

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **ABF26 Lemma 3.7 [Eli57].** Elias volume lower bound on list size:

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |F|`, `n = |ι|`, and `k = dim(C)` is the dimension of the linear code `C`
(so `|C| = q^k`). **Proven** by the paper's averaging argument (fulltext §3, [Eli57]):
the maximised list size dominates the mean over received words, and double counting gives
`∑_f |Λ(C,δ,f)| = ∑_{c∈C} Vol_q(δ,n) = q^k · Vol_q(δ,n)`, so the max is `≥ Vol/q^{n-k}`.
Uses `hammingBallVolume` (ABF26 D2.4) and `hammingBallVolume_eq_ncard_hammingBall` from
`HammingBallVolume.lean`. -/
theorem linear_lambda_ge_elias_volume_eli57
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  -- Provide `c ∈ C` decidability WITHOUT a global `classical` (which would create a
  -- `Decidable`-instance diamond on `hammingDist`, breaking term/goal unification).
  haveI : DecidablePred (fun c : ι → F => c ∈ C) := fun c => Classical.dec _
  set q : ℕ := Fintype.card F with hq_def
  set n : ℕ := Fintype.card ι with hn_def
  set k : ℕ := Module.finrank F C with hk_def
  set r : ℕ := ⌊δ * (n : ℝ)⌋₊ with hr_def
  have hn_pos : 0 < n := Fintype.card_pos
  have hδ_nonneg : (0 : ℝ) ≤ δ := le_of_lt _hδ_pos
  -- The per-word list set, as a `Finset` filter, using a `relHammingDist`↔`floor` bridge.
  have hbridge : ∀ f c : ι → F,
      (c ∈ closeCodewordsRel (↑C : Set (ι → F)) f δ) ↔ (c ∈ C ∧ hammingDist f c ≤ r) := by
    intro f c
    simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe]
    refine and_congr_right (fun _ => ?_)
    simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
    rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ)), hr_def,
      ← hn_def, Nat.le_floor_iff (mul_nonneg hδ_nonneg (Nat.cast_nonneg n))]
    -- The two `hammingDist` occurrences differ only by a (subsingleton) `Decidable`
    -- instance — `relHammingDist`'s unfolds with a different one than the statement's.
    congr!
  -- Rewrite each maximised-list term as a `Finset.card`.
  have hncard : ∀ f : ι → F,
      (closeCodewordsRel (↑C : Set (ι → F)) f δ).ncard
        = (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card := by
    intro f
    rw [← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hbridge f c
  -- Double counting: ∑_f |list_f| = q^k · Vol.
  have htotal :
      (∑ f : ι → F, (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
        = q ^ k * hammingBallVolume q δ n := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    have hinner : ∀ c : ι → F,
        (∑ f : ι → F, if (c ∈ C ∧ hammingDist f c ≤ r) then (1 : ℕ) else 0)
          = if c ∈ C then hammingBallVolume q δ n else 0 := by
      intro c
      by_cases hc : c ∈ C
      · simp only [hc, true_and, if_true]
        rw [← Finset.card_filter, hammingBallVolume_eq_ncard_hammingBall δ c,
          ← Set.ncard_coe_finset]
        congr 1
        ext f
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
          ListDecodable.hammingBall]
        rw [hr_def, ← hn_def, hammingDist_comm]
        congr!
      · simp only [hc, false_and, if_false, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl (fun c _ => hinner c), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul]
    have hcardC : (Finset.univ.filter (fun c => c ∈ C)).card = q ^ k := by
      haveI : Fintype (↥C) := Fintype.ofFinite _
      rw [← Fintype.card_subtype (fun c : ι → F => c ∈ C)]
      exact Module.card_eq_pow_finrank (K := F) (V := ↥C)
    rw [hcardC]
  -- Argmax word and the averaging inequality ∑ ≤ |F^n| · max.
  haveI : Nonempty (ι → F) := inferInstance
  obtain ⟨f₀, -, hf₀max⟩ := Finset.exists_max_image Finset.univ
    (fun f => (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
    Finset.univ_nonempty
  set s₀ : ℕ := (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f₀ c ≤ r)).card with hs₀_def
  have hsum_le :
      (∑ f : ι → F, (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
        ≤ q ^ n * s₀ := by
    have hcard_univ : (Finset.univ : Finset (ι → F)).card = q ^ n := by
      rw [Finset.card_univ, Fintype.card_fun]
    calc (∑ f : ι → F, (Finset.univ.filter (fun c => c ∈ C ∧ hammingDist f c ≤ r)).card)
        ≤ (Finset.univ : Finset (ι → F)).card • s₀ :=
          Finset.sum_le_card_nsmul _ _ _ (fun f _ => hf₀max f (Finset.mem_univ f))
      _ = q ^ n * s₀ := by rw [hcard_univ, smul_eq_mul]
  -- Combine: q^k · Vol ≤ q^n · s₀.
  have hnat : q ^ k * hammingBallVolume q δ n ≤ q ^ n * s₀ := htotal ▸ hsum_le
  -- Pass to reals and isolate `Vol / q^{n-k} ≤ s₀`.
  have hqr_pos : (0 : ℝ) < (q : ℝ) := by
    have : 1 < q := Fintype.one_lt_card; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this.le
  set P : ℝ := (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) with hP_def
  have hP_pos : 0 < P := Real.rpow_pos_of_pos hqr_pos _
  have hqk_pos : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hqr_pos k
  have hpow : (q : ℝ) ^ n = (q : ℝ) ^ k * P := by
    rw [hP_def, ← Real.rpow_natCast (q : ℝ) n, ← Real.rpow_natCast (q : ℝ) k,
      ← Real.rpow_add hqr_pos]
    congr 1; ring
  have hM_le : (hammingBallVolume q δ n : ℝ) / P ≤ (s₀ : ℝ) := by
    rw [div_le_iff₀ hP_pos]
    have h1 : (q : ℝ) ^ k * (hammingBallVolume q δ n : ℝ) ≤ (q : ℝ) ^ n * (s₀ : ℝ) := by
      exact_mod_cast hnat
    rw [hpow] at h1
    have h2 : (q : ℝ) ^ k * (hammingBallVolume q δ n : ℝ)
        ≤ (q : ℝ) ^ k * ((s₀ : ℝ) * P) := by
      have heq : (q : ℝ) ^ k * ((s₀ : ℝ) * P) = (q : ℝ) ^ k * P * (s₀ : ℝ) := by ring
      rw [heq]; exact h1
    exact le_of_mul_le_mul_left h2 hqk_pos
  -- Lift to `ℝ≥0∞`: the maximised list at `f₀` already realises the bound.
  simp only [Lambda, ENat.toENNReal_iSup]
  refine le_iSup_of_le f₀ ?_
  rw [hncard f₀, ← hs₀_def]
  have hcast : ENat.toENNReal ((s₀ : ℕ) : ℕ∞) = ENNReal.ofReal (s₀ : ℝ) := by
    rw [ENNReal.ofReal_natCast]; simp
  rw [hcast]
  exact ENNReal.ofReal_le_ofReal hM_le

/-- **Helper toward C3.8 (sorry-free, axiom-clean): the volume dominates its largest single
term.** `hammingBallVolume q δ n = ∑_{i≤⌊δn⌋} C(n,i)(q-1)^i ≥ C(n,⌊δn⌋)·(q-1)^{⌊δn⌋}`.
This is the first genuine step of the MS77 estimate (★): the full sum is bounded below by
its top-index term, which (for `δ ≤ (q-1)/q`) is the dominant Stirling term. -/
lemma hammingBallVolume_ge_last_term (q : ℕ) (δ : ℝ) (n : ℕ) :
    Nat.choose n (⌊δ * (n : ℝ)⌋₊) * (q - 1) ^ (⌊δ * (n : ℝ)⌋₊)
      ≤ hammingBallVolume q δ n := by
  unfold hammingBallVolume
  exact Finset.single_le_sum (f := fun i => Nat.choose n i * (q - 1) ^ i)
    (fun i _ => Nat.zero_le _) (Finset.self_mem_range_succ _)

/-- **Helper toward C3.8 (sorry-free, axiom-clean): the C3.8 ↔ L3.7 reduction algebra.**
Given the MS77 ingredient (★) in the form `q^{n·H} / D ≤ Vol`, the C3.8 left-hand value
`q^{n·(k/n − 1 + H)} / D` is bounded by the L3.7 left-hand value `Vol / q^{n−k}`.
This is pure `rpow` algebra (`n·(k/n−1+H) = (k−n)+n·H` and `q^{k−n}·q^{n−k}=1`); it is the
*entire* content of the corollary apart from (★) and the appeal to the proven L3.7. -/
lemma entropy_volume_reduction (q n k : ℕ) (H D Vol : ℝ)
    (hq1 : (1 : ℝ) ≤ q) (hn : 0 < n)
    (hstar : (q : ℝ) ^ ((n : ℝ) * H) / D ≤ Vol) :
    (q : ℝ) ^ ((n : ℝ) * ((k : ℝ) / (n : ℝ) - 1 + H)) / D
      ≤ Vol / (q : ℝ) ^ ((n : ℝ) - (k : ℝ)) := by
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  have hnR : ((n : ℝ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hexp : (n : ℝ) * ((k : ℝ) / (n : ℝ) - 1 + H) = ((k : ℝ) - n) + (n : ℝ) * H := by
    field_simp
  rw [hexp, Real.rpow_add hqpos]
  have hpk : (q : ℝ) ^ ((k : ℝ) - n) * (q : ℝ) ^ ((n : ℝ) - k) = 1 := by
    rw [← Real.rpow_add hqpos]; simp
  have hpnk_pos : (0 : ℝ) < (q : ℝ) ^ ((n : ℝ) - k) := Real.rpow_pos_of_pos hqpos _
  rw [le_div_iff₀ hpnk_pos]
  have hrw : (q : ℝ) ^ ((k : ℝ) - n) * (q : ℝ) ^ ((n : ℝ) * H) / D * (q : ℝ) ^ ((n : ℝ) - k)
      = ((q : ℝ) ^ ((n : ℝ) * H) / D) * ((q : ℝ) ^ ((k : ℝ) - n) * (q : ℝ) ^ ((n : ℝ) - k)) := by
    ring
  rw [hrw, hpk, mul_one]
  exact hstar

/-- **ABF26 Corollary 3.8.** Volume-based lower bound on list size, using the MS77
volume estimate `Vol_q(δ, n) ≥ q^{n·H_q(δ)} / √(8·n·δ·(1-δ))`. With `ρ := k/n`:

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`

Uses `qEntropy` (ABF26 D2.2).

**Reduced to one missing analytic ingredient.** Since L3.7
(`linear_lambda_ge_elias_volume_eli57`, now PROVEN in-tree) already gives
`Vol_q(δ,n) / q^{n-k} ≤ |Λ(C,δ)|`, this corollary follows by transitivity from the
single inequality

  `q^{n·H_q(δ)} / √(8·n·δ·(1-δ)) ≤ Vol_q(δ, n)`         (★)

(rearrange the C3.8 RHS via `ρ = k/n`: `q^{n(ρ-1+H_q)} = q^{k-n}·q^{n·H_q}` and
`Vol / q^{n-k} = Vol · q^{k-n}`, so C3.8-RHS ≤ L3.7-RHS ⇔ (★)). Inequality (★) is the
**MS77 lower bound on the `q`-ary Hamming-ball volume** (MacWilliams–Sloane 1977, the
Stirling-based estimate `∑_{i≤δn} C(n,i)(q-1)^i ≥ q^{nH_q(δ)}/√(8nδ(1-δ))`). That
estimate is a real-analytic fact about `hammingBallVolume` vs `qEntropy` and is **not**
yet in-tree; it is the only remaining gap. The right move is to prove (★) as a standalone
lemma `hammingBallVolume_ge_qEntropy` in `HammingBallVolume.lean` (Stirling bounds on
`Nat.choose` + `Real.logb` algebra), after which this corollary closes in three lines via
`le_trans` against L3.7. Admitted pending (★). -/
theorem linear_lambda_ge_entropy_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) := by
  sorry -- ABF26-C3.8; reduces to L3.7 (PROVEN) + missing ingredient (★):
  -- `q^{n·H_q(δ)} / √(8nδ(1-δ)) ≤ hammingBallVolume q δ n` (MS77 Stirling volume bound).
  -- PARTIAL PROGRESS: the mathlib-closable parts are now in-tree as two sorry-free,
  -- axiom-clean helpers above: `hammingBallVolume_ge_last_term` (volume ≥ top term, the
  -- first MS77 step) and `entropy_volume_reduction` (the full C3.8↔L3.7 rpow reduction
  -- algebra). With a true (★) these chain against L3.7 in ~3 lines via `le_trans`. The
  -- remaining gap is (★) itself, the MS77 sharp-Stirling Hamming-ball volume bound, which
  -- is a multi-hundred-line real-analytic development absent from mathlib (only an
  -- asymptotic Stirling estimate exists). NOTE: as written the statement is additionally
  -- false for small `n` (no sufficiently-large-`n` hypothesis); a faithful proof of (★)
  -- requires the asymptotic regime, so the bare statement is left as an external admit.

-- ===== ST20 (T3.9) helper 1: range fiber lower bound =====
private theorem st20_range_fiber_ge (a m i : ℕ) (hm : 0 < m) (hi : i < m) :
    a / m ≤ (Finset.range a |>.filter (fun t => t % m = i)).card := by
  have hsub : (Finset.range (a / m)).image (fun s => s * m + i)
      ⊆ (Finset.range a |>.filter (fun t => t % m = i)) := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have hstep : s * m + m ≤ (a / m) * m := by
        have hs1 : s + 1 ≤ a / m := hs
        calc s * m + m = (s + 1) * m := by ring
          _ ≤ (a/m) * m := Nat.mul_le_mul_right m hs1
      have hdm : (a/m) * m ≤ a := Nat.div_mul_le_self a m
      omega
    · have : (s * m + i) % m = i % m := Nat.mul_add_mod' s m i
      rw [this, Nat.mod_eq_of_lt hi]
  calc a / m = (Finset.range (a / m)).card := by rw [Finset.card_range]
    _ = ((Finset.range (a / m)).image (fun s => s * m + i)).card := by
        rw [Finset.card_image_of_injOn]
        intro x _ y _ h; simp only at h
        have : x * m = y * m := by omega
        exact Nat.eq_of_mul_eq_mul_right hm this
    _ ≤ _ := Finset.card_le_card hsub

-- ===== ST20 (T3.9) helper 2: fiber lower bound transported to attach =====
private theorem st20_attach_fiber_ge (Sc : Finset ι) (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < m)
    (e : {x // x ∈ Sc} ≃ Fin Sc.card) :
    Sc.card / m ≤ (Sc.attach.filter (fun x => (e x).val % m = j)).card := by
  have hbij : (Sc.attach.filter (fun x => (e x).val % m = j)).card
      = (Finset.univ.filter (fun t : Fin Sc.card => t.val % m = j)).card := by
    apply Finset.card_bij (fun x _ => e x)
    · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [Finset.mem_filter] at hx; exact hx.2
    · intro x _ y _ h; exact e.injective h
    · intro t ht
      refine ⟨e.symm t, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_attach, true_and, Equiv.apply_symm_apply]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht; exact ht
      · simp [Equiv.apply_symm_apply]
  rw [hbij]
  have hrange : (Finset.univ.filter (fun t : Fin Sc.card => t.val % m = j)).card
      = (Finset.range Sc.card |>.filter (fun t => t % m = j)).card := by
    apply Finset.card_bij (fun (t : Fin Sc.card) _ => t.val)
    · intro t ht; simp only [Finset.mem_filter, Finset.mem_range]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ⟨t.isLt, ht⟩
    · intro x _ y _ h; exact Fin.ext h
    · intro v hv; simp only [Finset.mem_filter, Finset.mem_range] at hv
      exact ⟨⟨v, hv.1⟩, by simp [Finset.mem_filter, hv.2], rfl⟩
  rw [hrange]
  exact st20_range_fiber_ge _ _ _ hm hj

-- ===== ST20 (T3.9) helper 3: pure-nat arithmetic inequality (lattice form) =====
private theorem st20_nat_ineq (ℓ r₀ : ℕ) (hℓ : 1 ≤ ℓ) :
    ((ℓ+1)*r₀/ℓ) - ((ℓ+1)*r₀/ℓ)/(ℓ+1) ≤ r₀ := by
  set a := (ℓ+1)*r₀/ℓ with ha
  have hAl : a * ℓ ≤ (ℓ+1)*r₀ := Nat.div_mul_le_self _ _
  obtain ⟨s, hs_le, hs_eq⟩ : ∃ s, s ≤ ℓ ∧ a = (ℓ+1) * (a/(ℓ+1)) + s := by
    refine ⟨a % (ℓ+1), ?_, ?_⟩
    · have := Nat.mod_lt a (show 0 < ℓ+1 by omega); omega
    · have := Nat.div_add_mod a (ℓ+1); omega
  set b := a/(ℓ+1) with hb
  rw [Nat.sub_le_iff_le_add, hs_eq]
  have hcore : ℓ*b + s ≤ r₀ := by
    have key : ((ℓ+1)*b + s) * ℓ ≤ (ℓ+1)*r₀ := by rw [← hs_eq]; exact hAl
    nlinarith [key, hs_le, hℓ, Nat.zero_le b, Nat.zero_le s, Nat.zero_le r₀,
               mul_le_mul_right' hs_le ℓ]
  have hexp : (ℓ+1)*b = ℓ*b + b := by ring
  rw [hexp]; omega

-- ===== ST20 (T3.9) helper 4: kernel extraction =====
private theorem st20_kernel_extract (C : Submodule F (ι → F)) (S : Finset ι) (ℓ : ℕ)
    (hdim : S.card < Module.finrank F C) (hq : ℓ + 1 ≤ Fintype.card F) :
    ∃ cf : Fin (ℓ + 1) → (ι → F), Function.Injective cf ∧
      (∀ j, cf j ∈ C) ∧ (∀ j, ∀ i ∈ S, cf j i = 0) := by
  classical
  let ρ : (ι → F) →ₗ[F] (S → F) := LinearMap.funLeft F F (fun i : S => (i : ι))
  let g : C →ₗ[F] (S → F) := ρ.comp C.subtype
  haveI : FiniteDimensional F C := inferInstance
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank F (LinearMap.range g) ≤ S.card := by
    have h1 : Module.finrank F (LinearMap.range g) ≤ Module.finrank F (S → F) :=
      Submodule.finrank_le _
    have h2 : Module.finrank F (S → F) = S.card := by rw [Module.finrank_pi]; simp
    omega
  have hker : 1 ≤ Module.finrank F (LinearMap.ker g) := by omega
  haveI : Fintype (LinearMap.ker g) := Fintype.ofFinite _
  have hcard_ker : Fintype.card (LinearMap.ker g)
      = Fintype.card F ^ Module.finrank F (LinearMap.ker g) :=
    Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker g)
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hge : Fintype.card F ≤ Fintype.card (LinearMap.ker g) := by
    rw [hcard_ker]
    calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (le_of_lt hq1) hker
  have hle : ℓ + 1 ≤ Fintype.card (LinearMap.ker g) := le_trans hq hge
  obtain ⟨emb⟩ : Nonempty (Fin (ℓ+1) ↪ (LinearMap.ker g)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hle)
  refine ⟨fun j => (((emb j : C) : ι → F)), ?_, ?_, ?_⟩
  · intro a b hab
    apply emb.injective
    have h2 : (emb a : C) = (emb b : C) := Subtype.ext hab
    exact Subtype.ext h2
  · intro j; exact (emb j : C).2
  · intro j i hi
    have hmem : (emb j : C) ∈ LinearMap.ker g := (emb j).2
    rw [LinearMap.mem_ker] at hmem
    have hcf := congr_fun hmem ⟨i, hi⟩
    have hgval : (g (emb j)) ⟨i, hi⟩ = (((emb j : C) : ι → F)) i := rfl
    rw [hgval] at hcf
    simpa using hcf

-- ===== ST20 (T3.9) helper 5: distance bound for constructed y =====
private theorem st20_dist_bound (S : Finset ι) (ℓ : ℕ)
    (cf : Fin (ℓ+1) → (ι → F))
    (hcfC0 : ∀ j, ∀ i, i ∈ S → cf j i = 0) :
    ∃ y : ι → F, ∀ j : Fin (ℓ+1),
      hammingDist y (cf j) ≤ Sᶜ.card - Sᶜ.card / (ℓ+1) := by
  classical
  set Sc : Finset ι := Sᶜ with hSc
  set e : {x // x ∈ Sc} ≃ Fin Sc.card := Sc.equivFin with he
  set partN : {x // x ∈ Sc} → Fin (ℓ+1) :=
    fun x => ⟨(e x).val % (ℓ+1), Nat.mod_lt _ (by omega)⟩ with hpartN
  set y : ι → F := fun i => if hi : i ∈ Sc then cf (partN ⟨i, hi⟩) i else 0 with hy
  refine ⟨y, fun j => ?_⟩
  rw [hammingDist]
  have hsub : (Finset.univ.filter (fun i => y i ≠ cf j i)) ⊆
      (Sc.attach.filter (fun x => partN x ≠ j)).image Subtype.val := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hiSc : i ∈ Sc
    · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_attach, true_and]
      refine ⟨⟨i, hiSc⟩, ?_, rfl⟩
      intro hpeq
      apply hi
      simp only [hy, dif_pos hiSc]
      rw [hpeq]
    · exfalso; apply hi
      simp only [hy, dif_neg hiSc]
      have hiS : i ∈ S := by simp only [hSc, Finset.mem_compl, not_not] at hiSc; exact hiSc
      exact (hcfC0 j i hiS).symm
  have hpartition := Finset.card_filter_add_card_filter_not (s := Sc.attach)
    (p := fun x => partN x = j)
  have hfiber : Sc.card / (ℓ+1) ≤ (Sc.attach.filter (fun x => partN x = j)).card := by
    have hbase := st20_attach_fiber_ge Sc (ℓ+1) (by omega) j.val j.isLt e
    have hcongr : (Sc.attach.filter (fun x => (e x).val % (ℓ+1) = j.val)).card
        = (Sc.attach.filter (fun x => partN x = j)).card := by
      congr 1; apply Finset.filter_congr; intro x _
      constructor
      · intro h; apply Fin.ext; simp only [hpartN]; exact h
      · intro h; have := congrArg Fin.val h; simpa [hpartN] using this
    rw [← hcongr]; exact hbase
  have hattach_card : Sc.attach.card = Sc.card := Finset.card_attach
  calc (Finset.univ.filter (fun i => y i ≠ cf j i)).card
      ≤ ((Sc.attach.filter (fun x => partN x ≠ j)).image Subtype.val).card :=
        Finset.card_le_card hsub
    _ ≤ (Sc.attach.filter (fun x => partN x ≠ j)).card := Finset.card_image_le
    _ ≤ Sc.card - Sc.card / (ℓ+1) := by
        have hne : (Sc.attach.filter (fun x => partN x ≠ j)).card
            = (Sc.attach.filter (fun x => ¬ (partN x = j))).card := by congr 1
        rw [hne]; omega

-- ===== ST20 (T3.9) helper 6: |C| = q^{finrank C} =====
private theorem st20_ncard_eq (C : Submodule F (ι → F)) :
    Set.ncard (C : Set (ι → F)) = Fintype.card F ^ Module.finrank F C := by
  haveI : Fintype C := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card' (C : Set (ι → F)), Set.toFinset_card]
  have hcong : Fintype.card (↑C : Set (ι → F)) = Fintype.card C := by
    apply Fintype.card_congr; rfl
  rw [hcong, Module.card_eq_pow_finrank (K := F) (V := C)]

/-- **ABF26 Theorem 3.9 [ST20 Thm 1.2], linear refinement.** Generalized Singleton bound
for list decoding. For a linear code `C ⊆ F^n` with `0 < ℓ < |F|`, `δ ∈ (0,1)` and
`|Λ(C, δ)| ≤ ℓ`:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}`.

**PROVEN** here from scratch by Shangguan–Tamo's elementary pigeonhole/partition argument
(SIAM J. Comput. 52(3), eq. (2); the cycle-space machinery in ST20 is only for the
*tightness* results T1.6/T1.9, NOT for this bound). Linear-algebra version: if
`finrank C > n - a`, the restriction-to-`S` map (`|S| = n - a`) has a kernel of dimension
`≥ 1`, hence `≥ |F| ≥ ℓ+1` codewords that vanish on `S`; partitioning `Sᶜ` (size `a`) into
`ℓ+1` near-even blocks and centring a word `y` block-wise puts all `ℓ+1` of them within
relative radius `δ`, contradicting `|Λ(C, δ)| ≤ ℓ`. Converting `finrank C ≤ n - a` to the
real bound via `|C| = |F|^{finrank C}` closes the goal.

**SIGFIX (two hypotheses added vs. the bare ABF26 statement — both are faithful to ST20
and necessary).** The unparameterised statement is *false*: e.g. `C = {0}` (always
`(δ,ℓ)`-list-decodable) with `ℓ = 1`, `δ` near `1` and large `n` gives `a = ⌊(ℓ+1)/ℓ·δ·n⌋
> n`, so the RHS `|F|^{n-a} < 1` while `|C| = 1`. The two added hypotheses are exactly the
regime in which ST20 prove (and state) the bound:
* `hlat` — the **lattice condition** `δ·n = ⌊δ·n⌋` (i.e. `δ·n ∈ ℤ`). ST20 explicitly
  "assume `rn` is an integer so the floor can be removed"; off the lattice the per-codeword
  distance `a - ⌊a/(ℓ+1)⌋` can exceed `⌊δ·n⌋` and the bound genuinely fails. This mirrors
  the lattice fix applied to the sibling MS77 volume bound (C3.8) in this file.
* `ha_le` — the **meaningful-radius regime** `a ≤ n` (equivalent to `δ ≤ ℓ/(ℓ+1)`, the
  Singleton radius regime; for larger `δ` the bound is vacuous/false as above).
Sound and `sorryAx`-free (`#print axioms`: only `propext, Classical.choice, Quot.sound`). -/
theorem linear_C_le_generalized_singleton_st20
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ))
    (ha_le : ⌊((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι⌋₊ ≤ Fintype.card ι)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  classical
  set q : ℕ := Fintype.card F with hq_def
  set n : ℕ := Fintype.card ι with hn_def
  set r₀ : ℕ := ⌊δ * (n : ℝ)⌋₊ with hr₀_def
  set a : ℕ := ⌊((ℓ : ℝ) + 1) / ℓ * δ * n⌋₊ with ha_def
  have hδ_nonneg : (0 : ℝ) ≤ δ := le_of_lt _hδ_pos
  have hℓ1 : 1 ≤ ℓ := _hℓ_pos
  have hq_ge : ℓ + 1 ≤ q := _hℓ_lt
  have hn_pos : 0 < n := Fintype.card_pos
  have ha_le' : a ≤ n := ha_le
  -- a = (ℓ+1)*r₀/ℓ  (nat)
  have ha_eq : a = (ℓ + 1) * r₀ / ℓ := by
    have hℓr : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (show ℓ ≠ 0 by omega)
    have hrw : ((ℓ : ℝ) + 1) / ℓ * δ * n = (((ℓ + 1) * r₀ : ℕ) : ℝ) / (ℓ : ℝ) := by
      have : ((ℓ : ℝ) + 1) / ℓ * δ * n = ((ℓ : ℝ) + 1) / ℓ * (δ * n) := by ring
      rw [this, hlat]
      push_cast
      field_simp
    rw [ha_def, hrw, Nat.floor_div_eq_div]
  have hkey : a - a / (ℓ + 1) ≤ r₀ := by
    rw [ha_eq]; exact st20_nat_ineq ℓ r₀ hℓ1
  -- finrank F C ≤ n - a
  have hfin_le : Module.finrank F C ≤ n - a := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
      (n := n - a) (by rw [Finset.card_univ, ← hn_def]; omega)
    have hScard : S.card = n - a := hS
    have hdim : S.card < Module.finrank F C := by rw [hScard]; exact hcon
    obtain ⟨cf, hcf_inj, hcfC, hcf0⟩ := st20_kernel_extract C S ℓ hdim hq_ge
    obtain ⟨y, hy⟩ := st20_dist_bound S ℓ cf hcf0
    have hSc_card : Sᶜ.card = a := by
      rw [Finset.card_compl, hScard, ← hn_def]; omega
    -- each cf j ∈ closeCodewordsRel C y δ
    have hmem : ∀ j, cf j ∈ closeCodewordsRel (↑C : Set (ι → F)) y δ := by
      intro j
      have hdist : hammingDist y (cf j) ≤ r₀ := by
        have h1 := hy j; rw [hSc_card] at h1; exact le_trans h1 hkey
      simp only [closeCodewordsRel, relHammingBall, Set.mem_setOf_eq, SetLike.mem_coe]
      refine ⟨hcfC j, ?_⟩
      simp only [Code.relHammingDist, NNRat.cast_div, NNRat.cast_natCast]
      rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (n : ℝ))]
      -- goal: ↑Δ₀(y, cf j) ≤ δ * ↑n  (modulo a subsingleton Decidable instance on hammingDist)
      have hcast : (hammingDist y (cf j) : ℝ) ≤ δ * (n : ℝ) := by
        have h1 : (hammingDist y (cf j) : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hdist
        have h2 : (r₀ : ℝ) ≤ δ * (n : ℝ) := by
          rw [hr₀_def]; exact Nat.floor_le (mul_nonneg hδ_nonneg (Nat.cast_nonneg n))
        exact le_trans h1 h2
      convert hcast using 2
      congr!
    -- ℓ+1 distinct elements ⊆ closeCodewordsRel → ncard ≥ ℓ+1
    have hfin_set : (closeCodewordsRel (↑C : Set (ι → F)) y δ).Finite := Set.toFinite _
    have hTcard : (Finset.univ.image cf).card = ℓ + 1 := by
      rw [Finset.card_image_of_injective _ hcf_inj, Finset.card_univ, Fintype.card_fin]
    have hTsub : (↑(Finset.univ.image cf) : Set (ι → F))
        ⊆ closeCodewordsRel (↑C : Set (ι → F)) y δ := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨j, rfl⟩ := hx; exact hmem j
    have hge : ℓ + 1 ≤ (closeCodewordsRel (↑C : Set (ι → F)) y δ).ncard := by
      calc ℓ + 1 = (Finset.univ.image cf).card := hTcard.symm
        _ = (↑(Finset.univ.image cf) : Set (ι → F)).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ _ := Set.ncard_le_ncard hTsub hfin_set
    -- contradiction with Lambda ≤ ℓ
    have hle : (closeCodewordsRel (↑C : Set (ι → F)) y δ).ncard ≤ ℓ := by
      have hLam : ((closeCodewordsRel (↑C : Set (ι → F)) y δ).ncard : ℕ∞) ≤ (ℓ : ℕ∞) := by
        refine le_trans ?_ _hΛ
        rw [Lambda]
        exact le_iSup (fun f => ((closeCodewordsRel (↑C : Set (ι → F)) f δ).ncard : ℕ∞)) y
      exact_mod_cast hLam
    omega
  -- convert to rpow conclusion
  rw [st20_ncard_eq C]
  have hq1r : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := by omega
    exact_mod_cast this
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  -- RHS rpow = pow since exponent = (n-a : ℕ)
  have hexp : ((n : ℝ) - (a : ℝ)) = ((n - a : ℕ) : ℝ) := by rw [Nat.cast_sub ha_le']
  calc ((q ^ Module.finrank F C : ℕ) : ℝ)
      = (q : ℝ) ^ Module.finrank F C := by push_cast; ring
    _ ≤ (q : ℝ) ^ (n - a) := by
        apply pow_le_pow_right₀ hq1r hfin_le
    _ = (q : ℝ) ^ ((n - a : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ = (q : ℝ) ^ ((n : ℝ) - (a : ℝ)) := by rw [hexp]

end LowerBounds_General

section LargeAlphabetBarrier

/-- **ABF26 Theorem 3.10 [BDG24, AGL23].** Large-alphabet barrier for generalized
Singleton attainment. For every `ℓ ≥ 2` and `ρ ∈ (0, 1)` there exists a constant
`α_ℓρ > 0` such that for every `η > 0` and every sufficiently large `n`, every linear
error-correcting code `C ⊆ F^n` of rate at least `ρ` with `|Λ(C, ℓ/(ℓ+1) · (1-ρ-η))| ≤ ℓ`
satisfies:

  `|F| ≥ 2^{α_ℓρ / η}`

i.e. attaining the generalized Singleton bound up to `η` slack requires alphabet size
exponential in `1/η`. We existentially package the "sufficiently large" threshold as
an explicit `n₀` parameter rather than relying on Lean's `eventually` API.

**Rate hypothesis.** Phrased as `Module.finrank F C ≥ ρ · n` (a lower bound; matches
the paper's "rate at least ρ" reading and avoids the impossible real-equality
`finrank/n = ρ` for irrational `ρ`). The rate-≥-ρ form is what the proof actually
uses (the conclusion is a *lower* bound on `|F|`, monotone in the rate hypothesis).

Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** The large-alphabet barrier [BDG24, AGL23] is settled
classical list-decoding theory whose proof is unformalized anywhere; mathlib lacks the
Reed-Solomon / generalized-Singleton / list-decoding API the argument depends on.
Ground-up formalization task, not a port.
See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem large_alphabet_barrier_bdg24_agl23
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧
      ∀ (η : ℝ), 0 < η →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            (Module.finrank F C : ℝ) ≥ ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  sorry -- ABF26-T3.10; external admit [BDG24, AGL23].
  -- Missing ingredient: BDG24/AGL23's large-alphabet barrier. Shows codes attaining the
  -- generalized Singleton bound up to η-slack need |F|≥2^{α/η}. The proof is a probabilistic
  -- /pigeonhole lower bound on |F| from the list-decodability hypothesis at the near-optimal
  -- radius ℓ/(ℓ+1)(1-ρ-η); needs the BDG24 alphabet-size lower bound (absent). The ∃α and ∃n₀
  -- threshold binders also require a non-vacuous constant from that argument. Genuinely external.

end LargeAlphabetBarrier

section RandomLinear

/-- **ABF26 Theorem 3.11 [GLMRSW22 Thm 4.1].** Random linear code lower bound. Fix a
prime `q`, `δ ∈ (0, 1 - 1/q)`, and `ε ∈ (0, 1)`. There exists `γ > 0` such that for all
`1 - H_q(δ) - γ < ρ < 1 - H_q(δ)` and all sufficiently large `n`, some linear code
`C ⊆ F^n` of rate `ρ` satisfies:

  `|Λ(C, δ)| > ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋`

The paper's full statement gives a `1 - q^{-Ω(n)}` probability over the choice of `C`;
we existentially package this as "there exists a witness code" since ArkLib does not
yet have a probability distribution over linear codes.

**STATUS: NEEDS_CLASSICAL.** The [GLMRSW22 Thm 4.1] random-linear-code lower bound is
settled classical coding theory but unformalized anywhere; mathlib lacks the
list-decoding / entropy-rate API the proof needs. Discharging the `sorry` is a ground-up
formalization, not a port. (Secondary DESIGN_OBSTRUCTION: the paper's `1 - q^{-Ω(n)}`
probabilistic guarantee is downgraded here to a bare existential witness because ArkLib
has no probability distribution over linear codes; a faithful statement would need that
distribution added first.) See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem random_linear_lambda_lower_glmrsw22
    (q : ℕ) (_hq_pp : IsPrimePow q)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (_hε_pos : 0 < ε) (_hε_lt : ε < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            -- Rate `≥ ρ` (not `= ρ`) so the statement is provable for *any* real
            -- `ρ` in the interval, including irrationals where the rational
            -- `finrank/|ι|` cannot exactly equal `ρ`. The conclusion's bound is
            -- monotone in `ρ`, so a code of rate strictly above `ρ` still
            -- witnesses the `ρ`-indexed bound.
            ∃ C : Submodule F (ι → F),
              (Module.finrank F C : ℝ) / Fintype.card ι ≥ ρ ∧
              (Lambda ((C : Set (ι → F))) δ : ENNReal) >
                ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ENNReal) := by
  sorry -- ABF26-T3.11; external admit [GLMRSW22 Thm 4.1].
  -- Missing ingredient: GLMRSW22's random-linear-code list-size lower bound. Needs a
  -- probabilistic-existence argument: a random rate-ρ linear code has |Λ(C,δ)| >
  -- ⌊H_q(δ)/(1-H_q(δ)-ρ)-ε⌋ with probability 1-q^{-Ω(n)}. ArkLib has no probability
  -- distribution over linear codes, so the witness-code existential cannot be discharged
  -- without first formalising the GLMRSW22 first-moment count over random generator matrices.
  -- Genuinely external (also blocked on the random-code measure).

end RandomLinear

section ReedSolomonBounds

/-- **ABF26 Theorem 3.12 [BKR06 Cor 2.2].** Reed-Solomon superpolynomial list-size over
extension fields. Fix `0 < α < β < 1`. For infinitely many prime powers `q` there exists
a Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` such that:

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log q}`

Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [BKR06 Cor 2.2] is settled classical Reed-Solomon
list-decoding theory, but mathlib has no Reed-Solomon list-decoding / superpolynomial
list-size API; this result is unformalized anywhere. Discharging the `sorry` is a
ground-up formalization, not a port.
See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem rs_lambda_superpoly_extension_bkr06
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < β) (_hβ_lt : β < 1) :
    -- `qs` carries the prime-power requirement as a *conjunct* alongside
    -- `StrictMono`. The previous shape `∀ i, IsPrimePow (qs i) → P i` was
    -- vacuously satisfied by any non-prime-power sequence; we now require
    -- *every* `qs i` to be a prime power up front.
    ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = qs i →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let q : ℕ := qs i
            let k : ℕ := Nat.floor ((q : ℝ) ^ α)
            let δ : ℝ := 1 - (q : ℝ) ^ (β - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ ((α - β ^ 2) * Real.log q) := by
  sorry -- ABF26-T3.12; external admit [BKR06 Cor 2.2].
  -- Missing ingredient: BKR06's superpolynomial RS list-size CONSTRUCTION over extension
  -- fields. Must exhibit, for infinitely many prime powers q, an RS code RS[F_q,F_q,⌊q^α⌋]
  -- and a word w with ≥ q^{(α-β²)log q} close codewords. The construction uses BKR06's
  -- subfield/trace structure; ExtensionCodes.lean L2.21 transports list sizes but does not
  -- manufacture the BKR06 large-list word. LOWER bound — genuinely external.

/-- **ABF26 Theorem 3.13 [GHSZ02 Cor 20].** Reed-Solomon large list-size over prime
fields. Fix `0 < α, β < 1`. For all sufficiently large primes `p`, there exists
`C := RS[F_p, F_p, ⌊p^α⌋]` and a word `w : F_p → F_p` such that:

  `|Λ(C, 1 - ((1-β)/α) · p^{α-1}, w)| > Ω(p^{p^α · β/2})`

Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [GHSZ02 Cor 20] is settled classical Reed-Solomon
list-decoding theory over prime fields, but unformalized anywhere; mathlib has no
Reed-Solomon list-decoding API. Discharging the `sorry` is a ground-up formalization,
not a port. See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem rs_lambda_large_prime_ghsz02
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < 1) (_hβ_pos : 0 < β) (_hβ_lt : β < 1) :
    ∃ (c : ℝ) (_ : 0 < c) (p₀ : ℕ),
      ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p → Fintype.card ι = p →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let k : ℕ := Nat.floor ((p : ℝ) ^ α)
            let δ : ℝ := 1 - ((1 - β) / α) * (p : ℝ) ^ (α - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) >
              c * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) := by
  sorry -- ABF26-T3.13; external admit [GHSZ02 Cor 20].
  -- Missing ingredient: GHSZ02's large RS list-size CONSTRUCTION over prime fields. Must
  -- exhibit, for all large primes p, an RS[F_p,F_p,⌊p^α⌋] and word w with > Ω(p^{p^α·β/2})
  -- close codewords. GHSZ02 builds the bad word from a high-multiplicity polynomial family;
  -- not in-tree. LOWER bound — genuinely external.

/-- **ABF26 Theorem 3.14 [JH01 Thm 2].** Large-rate Reed-Solomon lower bound. Fix an
integer `j ≥ 2`. For infinitely many prime powers `q` with `q ≡ 1 (mod j+1)`, there
exists `C := RS[F_q, L, k]` with `|C| = j + 1` and rate `ρ ≈ (j-1)/(j+1)` together
with a word `w : L → F_q` such that:

  `|Λ(C, 1/(j+1), w)| > j`

Witnesses that high-rate RS codes cannot be list-decoded beyond `1/(j+1)` with list
size `j`. Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [JH01 Thm 2] is settled classical high-rate Reed-Solomon
list-decoding theory, unformalized anywhere; mathlib has no Reed-Solomon list-decoding
API. Discharging the `sorry` is a ground-up formalization, not a port. (Secondary
DESIGN_OBSTRUCTION: the paper-quoted `|C| = j + 1` is exactly satisfiable only for
specific `(q, k, j)` triples — e.g. `q = j + 1`, `k = 1` — so a faithful proof must first
pin `(k, q)` in the statement; as written the `Set.ncard C = j + 1` conjunct is not
universally satisfiable.) See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem rs_lambda_high_rate_jh01
    (j : ℕ) (_hj_ge : 2 ≤ j) :
    -- Prime-power and modular requirements moved out of `→`-implications
    -- into conjuncts of the outer existential so the sequence cannot be
    -- vacuously satisfied by non-prime-powers (or values not ≡ 1 mod j+1).
    ∃ qs : ℕ → ℕ, StrictMono qs ∧
      (∀ i, IsPrimePow (qs i)) ∧ (∀ i, qs i % (j + 1) = 1) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = j + 1 →
          ∃ (domain : ι ↪ F) (k : ℕ) (w : ι → F),
            let C := ReedSolomon.code domain k
            -- The paper-quoted `|C| = j + 1` is consistent only with
            -- specific `(q, k, j)` triples (e.g. `q = j + 1`, `k = 1`); the
            -- external admit's eventual proof should pin `(k, q)` to make
            -- this exactly satisfiable.
            Set.ncard ((C : Set (ι → F))) = j + 1 ∧
            (j : ℕ∞) < (closeCodewordsRel ((C : Set (ι → F))) w (1 / (j + 1 : ℝ))).ncard := by
  sorry -- ABF26-T3.14; external admit [JH01 Thm 2].
  -- Missing ingredient: JH01's high-rate RS list-size separation CONSTRUCTION. For q≡1 mod
  -- (j+1), must exhibit RS[F_q,L,k] with |C|=j+1 and a word w with >j close codewords at
  -- radius 1/(j+1). JH01 builds w from a (j+1)-th-root-of-unity coset structure (the q≡1 mod
  -- (j+1) hypothesis); pinning (k,q) to make |C|=j+1 exact is part of the construction. Not
  -- in-tree. LOWER bound — genuinely external.

end ReedSolomonBounds

section SubspaceDesignUpperBounds

/-- **ABF26 Theorem 3.4 [CZ25 Theorem B.5].** τ-subspace-design codes are list-decodable
up to capacity. Let `C : F^k → (F^s)^n` be a τ-subspace-design code. For every `η > 0`:

  `|Λ(C, 1 - τ(1/η) - η)| ≤ (1 - τ(1/η)) / η`

Combined with `IsSubspaceDesign` (ABF26 D2.16) and `subspaceDesign_tau_lower`
(L2.17), this gives a list-decoding bound up to capacity for any subspace-design code.
Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [CZ25 Thm B.5] is the *corrected, provable* subspace-design
route to capacity-radius list decodability — NOT the disproven up-to-capacity
correlated-agreement / mutual-correlated-agreement / list-decodability conjecture (those
live in `Whir/MutualCorrAgreement`, `CapacityBounds`, `BCIKS20`). The subspace-design
result holds (cf. "Optimal Proximity Gap for Folded RS via Subspace Designs",
arXiv 2601.10047). It is simply unformalized: mathlib has no subspace-design /
Reed-Solomon / list-decoding API, so discharging the `sorry` is a ground-up formalization
task, not a port. See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem subspaceDesign_list_decoding_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (η : ℝ) (_hη_pos : 0 < η) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - τ (Nat.floor (1 / η)) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - τ (Nat.floor (1 / η))) / η) := by
  sorry -- ABF26-T3.4; external admit [CZ25 Thm B.5].
  -- Missing ingredient: CZ25 Thm B.5's subspace-design list-decoding-up-to-capacity bound.
  -- |Λ(C,1-τ(1/η)-η)|≤(1-τ(1/η))/η follows from IsSubspaceDesign (in-tree D2.16) PLUS CZ25's
  -- design→list-size analysis (a dimension-counting bound on the close-codeword subspace),
  -- which rests on L2.17 (subspaceDesign_tau_lower — STILL an external admit). Blocked
  -- transitively on L2.17 + the CZ25 design→Λ conversion (absent). Genuinely external.

/-- **ABF26 Corollary 3.5 [CZ25 Corollary 2.21].** Folded Reed-Solomon codes are
list-decodable up to capacity. Let `C := FRS[F, L, k, s, ω]` be a folded RS code of
rate `ρ`. For any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))`

When `η ≥ √(3/s)`, the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`. Derives from
T3.4 + T2.18 (FRS is τ-subspace-design). Admitted as an external result.

**STATUS: NEEDS_CLASSICAL.** [CZ25 Cor 2.21] is the *corrected, provable* folded-RS
capacity list-decodability result via subspace designs — NOT the disproven up-to-capacity
conjecture for plain Reed-Solomon proximity gaps / DEEP-FRI list-decodability (those are
FALSE per eprint.iacr.org/2025/2046 and live elsewhere). Folded RS attains capacity by the
subspace-design argument (arXiv 2601.10047). It is unformalized: mathlib has no folded-RS /
subspace-design / list-decoding API, so the `sorry` is a ground-up formalization task, not
a port, and follows once T3.4 + T2.18 are formalized.
See `research/formal/arklib-proof-research-2026-06.md`. -/
theorem frs_list_decoding_capacity_cz25
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  sorry -- ABF26-C3.5; external admit [CZ25 Cor 2.21].
  -- Missing ingredient: this is a COROLLARY of T3.4 via T2.18 (frs_is_subspaceDesign_gk16:
  -- FRS is τ-subspace-design). Once T3.4 and T2.18 are proven, C3.5 closes by instantiating
  -- T3.4 at the FRS τ(r)=sρ/(s-r+1) and simplifying with 1/η<s. Blocked on T3.4 (above) +
  -- T2.18 (external admit in SubspaceDesign.lean). No independent external content.

end SubspaceDesignUpperBounds

end CodingTheory
