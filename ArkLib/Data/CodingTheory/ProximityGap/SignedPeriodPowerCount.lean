/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
set_option linter.unusedSectionVars false

/-!
# The SIGNED period-power sum IS a zero-sum count (#444, #407)

The campaign's thinness-discriminator search (`DISPROOF_LOG`, "SIGNED deep period-power cancellation
IS thinness-essential") located the prize's rule-3 lever in the **signed** deep period-power sum
`∑_{b≠0} η_b^r`, NOT the absolute moment `∑_b |η_b|^{2r}` — taking `|·|` (as every moment / energy /
Wick / count packaging does) destroys exactly the signed cancellation that distinguishes the thin
`β≈4-5` regime from the thick one. The signed sum is therefore the object a CORE proof must exploit,
and the moment route's `|·|` is provably the rule-3 leak.

This file formalizes the **exact algebraic content** of that object: for a finite field `F`
(`card F = q`), additive characters `ψ : AddChar F ℂ`, and any finite set `S ⊆ F`, the Gauss period
`η_ψ = ∑_{x∈S} ψ x` satisfies

>   `∑_ψ η_ψ^r = q · #{ (x : Fin r → S) : ∑_i x i = 0 }`,

the **signed period-power sum is `q` times the `r`-fold zero-sum count**. (Probe
`scripts/probes/probe_signed_periodpow_count_identity.py`, `18/18` EXACT over proper thin `μ_n`,
verifies both this and the nonzero-character form `∑_{ψ≠0} η_ψ^r = q·W_r − |S|^r`.)

This is the `r`-fold power generalization of `SubgroupCharacterSumNoGo.charSum_zero_count` (the `r=1`
indicator) and the general-`r` companion of `CS25FourierIdentity.fourier_pair_identity` (the `r=2`
pair form). Mechanism: a character carries sums to products, `(∑_x ψ x)^r = ∑_{tuples} ψ(∑_i x i)`,
then orthogonality `∑_ψ ψ a = q·[a=0]` collapses the character sum to the count.

Honest scope: this is the EXACT structural identity for the signed period-power sum — a NON-MOMENT,
char-free, field-universal Fourier identity (NO `|·|` anywhere, so it preserves the thin signal). It
is NOT a CORE bound: bounding `∑_{ψ≠0} η_ψ^r` quantitatively at `r ≈ log q` (the deep signed
cancellation) is the open BGK wall. This brick makes the object the wall is about exact + reusable.
`CORE  M(μ_n) ≤ C·√(n·log(q/n))  OPEN.`

Issues #444, #407.
-/

open scoped BigOperators

namespace ArkLib.ProximityGap.SignedPeriodPowerCount

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-element character orthogonality.** `∑_ψ ψ a = q·[a = 0]` over `F`. -/
lemma sum_char_eq_ite (a : F) :
    (∑ ψ : AddChar F ℂ, ψ a) = if a = 0 then (Fintype.card F : ℂ) else 0 :=
  AddChar.sum_apply_eq_ite a

/-- **A character of an additive group carries an `r`-fold sum to the product of its values.**
`ψ (∑_i x i) = ∏_i ψ (x i)` for `x : Fin r → F`. -/
lemma char_sum_eq_prod (ψ : AddChar F ℂ) {r : ℕ} (x : Fin r → F) :
    ψ (∑ i, x i) = ∏ i, ψ (x i) := by
  classical
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ, AddChar.map_add_eq_mul, ih]

/-- **The Gauss period's `r`-th power expands as a tuple character sum.** For `S : Finset F` and a
character `ψ`, `(∑_{x∈S} ψ x)^r = ∑_{t : Fin r → S} ψ(∑_i t i)`, summing over the `|S|^r` tuples of
elements of `S` (via `Fintype.piFinset`). -/
lemma period_pow_eq_tuple_sum (S : Finset F) (ψ : AddChar F ℂ) (r : ℕ) :
    (∑ x ∈ S, ψ x) ^ r
      = ∑ t ∈ Fintype.piFinset (fun _ : Fin r => S), ψ (∑ i, t i) := by
  classical
  -- expand the power of a sum into the tuple product sum (Finset.sum_pow'),
  -- then fold ∏ ψ back into ψ(∑·) via the character-of-sum lemma
  rw [Finset.sum_pow' S (fun x => ψ x) r]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [char_sum_eq_prod ψ]

/-- **The signed period-power sum is `q` times the `r`-fold zero-sum count.** For any finite `S ⊆ F`
and any `r`,
`∑_ψ (∑_{x∈S} ψ x)^r = q · #{ t : Fin r → S : ∑_i t i = 0 }`,
an identity in `ℂ`. This is the EXACT algebraic form of the thinness-essential signed period-power
sum (`DISPROOF_LOG`): no `|·|`, so the signed cancellation is preserved. The `r=1` case is
`SubgroupCharacterSumNoGo.charSum_zero_count`; this is the general-`r` power generalization. -/
theorem signedPeriodPow_eq_zeroSumCount (S : Finset F) (r : ℕ) :
    (∑ ψ : AddChar F ℂ, (∑ x ∈ S, ψ x) ^ r)
      = (Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card := by
  classical
  -- expand each power into the tuple character sum, swap ∑_ψ and ∑_t
  have hexp : (∑ ψ : AddChar F ℂ, (∑ x ∈ S, ψ x) ^ r)
      = ∑ ψ : AddChar F ℂ,
          ∑ t ∈ Fintype.piFinset (fun _ : Fin r => S), ψ (∑ i, t i) :=
    Finset.sum_congr rfl (fun ψ _ => period_pow_eq_tuple_sum S ψ r)
  rw [hexp, Finset.sum_comm]
  -- inner orthogonality: ∑_ψ ψ(∑_i t i) = q·[∑_i t i = 0]
  have hpt : ∀ t : Fin r → F,
      (∑ ψ : AddChar F ℂ, ψ (∑ i, t i))
        = if (∑ i, t i) = 0 then (Fintype.card F : ℂ) else 0 :=
    fun t => sum_char_eq_ite (∑ i, t i)
  rw [Finset.sum_congr rfl (fun t _ => hpt t)]
  -- ∑_t [q·1_{∑ = 0}] = q · #{t : ∑ = 0}
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The principal-character split: the nonzero signed period-power sum is `q·W_r − |S|^r`.**
Splitting off the principal character `ψ = 0` (whose period is `∑_{x∈S} ψ x = |S|`, contributing
`|S|^r`), the nonzero-character signed sum is the zero-sum count minus the diagonal:
`∑_{ψ≠0} η_ψ^r = q · #{t : ∑_i t i = 0} − |S|^r`. This is the prize-relevant form (`∑_{b≠0} η_b^r`,
`DISPROOF_LOG`: nonzero-character signed sum `= q·W_r − n^r`); probe-confirmed `18/18`. -/
theorem nonzeroSignedPeriodPow_eq (S : Finset F) (r : ℕ) :
    (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      = (Fintype.card F : ℂ)
          * ((Fintype.piFinset (fun _ : Fin r => S)).filter
              (fun t => ∑ i, t i = 0)).card
        - (S.card : ℂ) ^ r := by
  classical
  -- principal character: ∑_{x∈S} (0 : AddChar) x = ∑_{x∈S} 1 = |S|
  have h0 : (∑ x ∈ S, (0 : AddChar F ℂ) x) ^ r = (S.card : ℂ) ^ r := by
    have hz : (∑ x ∈ S, (0 : AddChar F ℂ) x) = (S.card : ℂ) := by
      simp only [AddChar.zero_apply]
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hz]
  -- split the full character sum: ∑_{ψ≠0} η^r + η_0^r = ∑_ψ η^r
  have hsplit : (∑ ψ ∈ (univ.erase (0 : AddChar F ℂ)), (∑ x ∈ S, ψ x) ^ r)
      + (∑ x ∈ S, (0 : AddChar F ℂ) x) ^ r
      = ∑ ψ : AddChar F ℂ, (∑ x ∈ S, ψ x) ^ r :=
    Finset.sum_erase_add (univ) (fun ψ : AddChar F ℂ => (∑ x ∈ S, ψ x) ^ r)
      (Finset.mem_univ (0 : AddChar F ℂ))
  rw [h0] at hsplit
  -- hsplit : (∑_{ψ≠0} η^r) + |S|^r = ∑_ψ η^r ; subtract |S|^r and apply the count identity
  have hfull := signedPeriodPow_eq_zeroSumCount S r
  rw [← hsplit] at hfull
  -- hfull : (∑_{ψ≠0} η^r) + |S|^r = q · #{...}
  linear_combination hfull

end ArkLib.ProximityGap.SignedPeriodPowerCount

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SignedPeriodPowerCount.signedPeriodPow_eq_zeroSumCount
#print axioms ArkLib.ProximityGap.SignedPeriodPowerCount.nonzeroSignedPeriodPow_eq
