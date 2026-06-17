/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilPairwiseBonferroni

set_option linter.style.longLine false

/-!
# The Cauchy-Schwarz / Fisher double-count for the dilation pencil (#407/#444)

`_PencilSunflowerCore.lean` mapped the clean **sunflower** rung of the pencil degradation (all
pairwise intersections equal a *single common* core `T`) and its scope note named the harder honest
target it deferred:

> "The general pairwise-`≤ M` core (`r² ≲ M·N` by a **Cauchy-Schwarz/Fisher double-count**, with no
> common `T`) is the harder honest target and **stays a separate brick**."

`PencilPairwiseBonferroni.lean` then proved the general-pairwise rung in the **Bonferroni** form
`r·(r−1) ≤ C(r,2)·M + (|univ|−1)` (a *quadratic-in-r* RHS via `mult − C(mult,2) ≤ 1`). This file
supplies the deferred **Cauchy-Schwarz** form, which is **strictly sharper** in the small-`M` range:

> `pencil_cs_fisher` :  `r·(r−1) ≤ (M+1)·(|univ|−1)`.

(*Linear* in `M` and `|univ|`, no `C(r,2)` blow-up.) At `M = 0` this is `r·(r−1) ≤ |univ|−1`, the
`pencil_card_core` count; at `M = 1` it is `r·(r−1) ≤ 2(|univ|−1)`. It is **always** at least as
strong as the Bonferroni bound on the punctured family (probe: strictly tighter in every prize
instance, and TIGHT at `M = 0` and the saturating `n = 4` pencil `12 ≤ 12`).

## The double-count (Cauchy-Schwarz on the multiplicity profile)

Work with the **punctured** blocks `Cᵢ := (Bᵢ).erase p` (size `r−1`, all sharing no point that
isn't shared by the originals; the apex `p` is removed). Let `U = ⋃ᵢ Cᵢ` be the non-apex support and
`deg(x) = #{i : x ∈ Cᵢ}` (`PencilPairwiseBonferroni.mult`). Two in-tree identities give the two
moments of `deg`:

* `∑_{x∈U} deg(x) = ∑ᵢ |Cᵢ| = r·(r−1)`  (`sum_card_eq_sum_mult`, `card_pencilBlock`-style).
* `∑_{x∈U} C(deg(x),2) = ∑_{i<j} |Cᵢ ∩ Cⱼ| ≤ C(r,2)·M`  (`sum_inter_eq_sum_choose_two` + the
  pairwise hypothesis).

Now `d² = 2·C(d,2) + d` for every `d : ℕ`, so the second moment is
`∑ deg² = 2·∑ C(deg,2) + ∑ deg ≤ 2·C(r,2)·M + r·(r−1) = r·(r−1)·M + r·(r−1) = r·(r−1)·(M+1)`
(using `2·C(r,2) = r·(r−1)`). Cauchy-Schwarz (`Finset.sq_sum_le_card_mul_sum_sq`) over the support
`U` gives `(∑ deg)² ≤ |U|·∑ deg²`, i.e.

  `(r·(r−1))² ≤ |U| · r·(r−1)·(M+1) ≤ (|univ|−1) · r·(r−1)·(M+1)`

(`U ⊆ univ.erase p`, so `|U| ≤ |univ|−1`). Dividing by `r·(r−1)` (when `r ≥ 2`) yields the headline.

## Honest scope (rules 1,3,4,6 + ASYMPTOTIC GUARD)

This is **NOT** a closure and **NOT** thinness-essential: it is field-universal set-system
combinatorics (holds for ANY family with the size/apex/pairwise hypotheses, independent of
thickness), valid exactly where the second-moment / Johnson layer is vacuous (the polynomial-method
side). It is a **refutation-with-mechanism** rung (rule 4): for the prize-relevant general
`t = k+2` worst case `S = (coset of size n/2) ∪ {straggler}` the autocorrelation is `M ≍ n/2`
(`PencilAutocorrelation.autocorr_ge_coset_core`), so the RHS `(M+1)(N−1) ≍ (n/2)·N` **dominates**,
the bound gives only `r ≲ n` (**Johnson**, not sub-Johnson): the Cauchy-Schwarz double-count
**collapses to Johnson** at the prize core exactly as the cliff-at-n/2 guard demands. The genuine
beyond-Johnson `√(log)` cancellation lives in the agreement-sharing / BGK contribution, untouched.
The prize CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**. Probe:
`scripts/probes/probe_fisher_cs_pencil.py` (PROPER thin `μ_n ⊊ F_p*`, `p ≫ n³`, `p ≡ 1 mod n`,
NEVER `n = q−1`): `r·(r−1) ≤ (M+1)(N−1)` in every instance, TIGHT at `M = 0` and `n = 4` (`12≤12`),
strictly tighter than the Bonferroni RHS everywhere.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.PencilCauchySchwarzFisher

open ProximityGap.Frontier.PencilPairwiseBonferroni

variable {G : Type*} [DecidableEq G]

/-- The elementary identity `d^2 = 2·C(d,2) + d` for every natural `d` (the bridge from the second
moment `∑ deg²` to the pairwise-overlap sum `∑ C(deg,2)`). -/
theorem sq_eq_two_mul_choose_two_add (d : ℕ) : d ^ 2 = 2 * d.choose 2 + d := by
  rw [Nat.choose_two_right]
  -- d * (d-1) is even; 2 * (d*(d-1)/2) = d*(d-1); then d^2 = d*(d-1) + d.
  have heven : 2 ∣ d * (d - 1) := (Nat.even_mul_pred_self d).two_dvd
  obtain ⟨t, ht⟩ := heven
  rw [ht, Nat.mul_div_cancel_left t (by norm_num)]
  rcases d with _ | d
  · simp at ht ⊢; omega
  · simp only [Nat.add_sub_cancel] at ht ⊢
    nlinarith [ht]

/-- **The Cauchy-Schwarz / Fisher pencil double-count.** Suppose `univ : Finset G` carries a family
of `r` blocks `B : Fin r → Finset G`, each of size `r`, all containing a common apex `p`, with the
**punctured** blocks pairwise overlapping in `≤ M` (`|(B i).erase p ∩ (B j).erase p| ≤ M` for
`i ≠ j`). Then

  `r·(r−1) ≤ (M + 1)·(|univ| − 1)`.

No sunflower hypothesis (the pairwise intersections may differ per pair, and need not share a common
core). This is strictly sharper than `PencilPairwiseBonferroni.pencil_pairwise_bonferroni`
(`r·(r−1) ≤ C(r,2)·M + (|univ|−1)`) for small `M`, and is `pencil_card_core` at `M = 0`. -/
theorem pencil_cs_fisher (univ : Finset G)
    (r M : ℕ) (hr : 1 ≤ r) (B : Fin r → Finset G) (p : G)
    (hsub : ∀ i, B i ⊆ univ)
    (hsize : ∀ i, (B i).card = r)
    (hp : ∀ i, p ∈ B i)
    (hpair : ∀ i j, i ≠ j → ((B i).erase p ∩ (B j).erase p).card ≤ M) :
    r * (r - 1) ≤ (M + 1) * (univ.card - 1) := by
  classical
  -- punctured blocks
  set C : Fin r → Finset G := fun i => (B i).erase p with hC
  set U : Finset G := Finset.univ.biUnion C with hU
  -- |C i| = r - 1
  have hCcard : ∀ i, (C i).card = r - 1 := by
    intro i; rw [hC]; simp only; rw [Finset.card_erase_of_mem (hp i), hsize i]
  -- U ⊆ univ.erase p  (every punctured block point is in univ and ≠ p)
  have hUsub : U ⊆ univ.erase p := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    rw [hC] at hxi; simp only at hxi
    rw [Finset.mem_erase] at hxi ⊢
    exact ⟨hxi.1, hsub i hxi.2⟩
  -- |U| ≤ |univ| - 1
  have hpuniv : p ∈ univ := hsub ⟨0, hr⟩ (hp ⟨0, hr⟩)
  have hUcard : U.card ≤ univ.card - 1 := by
    calc U.card ≤ (univ.erase p).card := Finset.card_le_card hUsub
      _ = univ.card - 1 := Finset.card_erase_of_mem hpuniv
  -- FIRST MOMENT: ∑_{x∈U} deg(x) = ∑_i |C i| = r * (r-1).
  have hfirst : (∑ x ∈ U, mult r C x) = r * (r - 1) := by
    rw [hU, ← sum_card_eq_sum_mult r C]
    rw [Finset.sum_congr rfl (fun i _ => hCcard i)]
    simp [Finset.sum_const, Finset.card_univ]
  -- PAIRWISE SUM: ∑_{i<j} |C i ∩ C j| = ∑_{x∈U} C(deg x, 2) ≤ C(r,2) * M.
  have hpairsum_le :
      (∑ x ∈ U, (mult r C x).choose 2) ≤ (r.choose 2) * M := by
    rw [hU, ← sum_inter_eq_sum_choose_two r C]
    -- bound each summand by M over the < r-pairs filter
    calc (∑ q ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2),
              (C q.1 ∩ C q.2).card)
        ≤ ∑ _q ∈ (Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2), M := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_filter] at hq
          have hne : q.1 ≠ q.2 := ne_of_lt hq.2
          rw [hC]; exact hpair q.1 q.2 hne
      _ = ((Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2)).card * M := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (r.choose 2) * M := by
          have huniv : ((Finset.univ : Finset (Fin r × Fin r)).filter (fun q => q.1 < q.2))
              = ((Finset.univ : Finset (Fin r)).offDiag.filter (fun q => q.1 < q.2)) := by
            apply Finset.ext
            rintro ⟨i, j⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
            constructor
            · intro h; exact ⟨ne_of_lt h, h⟩
            · intro h; exact h.2
          rw [huniv, filter_lt_offDiag_card, Finset.card_univ, Fintype.card_fin]
  -- SECOND MOMENT (over ℝ): ∑ deg² = 2 ∑ C(deg,2) + ∑ deg ≤ r(r-1) M + r(r-1) = r(r-1)(M+1).
  -- First the nat identity summed.
  have hsq_sum : (∑ x ∈ U, (mult r C x) ^ 2)
      = 2 * (∑ x ∈ U, (mult r C x).choose 2) + (∑ x ∈ U, mult r C x) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => sq_eq_two_mul_choose_two_add (mult r C x))
  have hsq_le : (∑ x ∈ U, (mult r C x) ^ 2) ≤ r * (r - 1) * (M + 1) := by
    rw [hsq_sum, hfirst]
    have h2 : 2 * (∑ x ∈ U, (mult r C x).choose 2) ≤ 2 * ((r.choose 2) * M) := by
      exact Nat.mul_le_mul_left 2 hpairsum_le
    have h2choose : 2 * (r.choose 2) = r * (r - 1) := by
      rw [Nat.choose_two_right]
      have heven : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
      obtain ⟨t, ht⟩ := heven
      rw [ht, Nat.mul_div_cancel_left t (by norm_num)]
    calc 2 * (∑ x ∈ U, (mult r C x).choose 2) + r * (r - 1)
        ≤ 2 * ((r.choose 2) * M) + r * (r - 1) := by omega
      _ = (r * (r - 1)) * M + r * (r - 1) := by rw [← mul_assoc, h2choose]
      _ = r * (r - 1) * (M + 1) := by ring
  -- CAUCHY-SCHWARZ over ℝ: (∑ deg)² ≤ |U| · ∑ deg².
  have hCS : (∑ x ∈ U, ((mult r C x : ℝ))) ^ 2
      ≤ (U.card : ℝ) * ∑ x ∈ U, ((mult r C x : ℝ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- cast the nat sums to ℝ
  have hfirstR : (∑ x ∈ U, ((mult r C x : ℝ))) = ((r * (r - 1) : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, hfirst]
  have hsqR : (∑ x ∈ U, ((mult r C x : ℝ)) ^ 2) = ((∑ x ∈ U, (mult r C x) ^ 2 : ℕ) : ℝ) := by
    push_cast; rfl
  -- assemble: (r(r-1))² ≤ |U| · (r(r-1)(M+1)) ≤ (N-1) · (r(r-1)(M+1)) over ℝ.
  set A : ℕ := r * (r - 1) with hA
  have hkey : ((A : ℝ)) ^ 2 ≤ ((univ.card - 1 : ℕ) : ℝ) * ((A * (M + 1) : ℕ) : ℝ) := by
    calc ((A : ℝ)) ^ 2
        = (∑ x ∈ U, ((mult r C x : ℝ))) ^ 2 := by rw [hfirstR]
      _ ≤ (U.card : ℝ) * ∑ x ∈ U, ((mult r C x : ℝ)) ^ 2 := hCS
      _ = (U.card : ℝ) * ((∑ x ∈ U, (mult r C x) ^ 2 : ℕ) : ℝ) := by rw [hsqR]
      _ ≤ ((univ.card - 1 : ℕ) : ℝ) * ((A * (M + 1) : ℕ) : ℝ) := by
          apply mul_le_mul
          · exact_mod_cast hUcard
          · exact_mod_cast hsq_le
          · exact_mod_cast Nat.zero_le _
          · exact_mod_cast Nat.zero_le _
  -- back to ℕ: A² ≤ (N-1) · A · (M+1).  If A = 0 trivial; else divide by A.
  have hkeyN : A ^ 2 ≤ (univ.card - 1) * (A * (M + 1)) := by exact_mod_cast hkey
  -- conclude A ≤ (M+1)(N-1)
  rcases Nat.eq_zero_or_pos A with hA0 | hApos
  · rw [hA0]; exact Nat.zero_le _
  · -- A² = A·A ≤ (N-1)·A·(M+1) = A·((M+1)(N-1)), cancel A.
    have hfactor : (univ.card - 1) * (A * (M + 1)) = A * ((M + 1) * (univ.card - 1)) := by ring
    rw [hfactor, pow_two] at hkeyN
    exact Nat.le_of_mul_le_mul_left hkeyN hApos

end ProximityGap.Frontier.PencilCauchySchwarzFisher

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.PencilCauchySchwarzFisher.sq_eq_two_mul_choose_two_add
#print axioms ProximityGap.Frontier.PencilCauchySchwarzFisher.pencil_cs_fisher
