/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Instances
import Mathlib.Algebra.Polynomial.Roots

/-!
# Weakened-KState Schwartz–Zippel residual bridge (sum-check rounds)

This module provides the **CompPoly-free** Schwartz–Zippel probability bridge that underpins the
"weakened" round-by-round knowledge state (KState) used by the sum-check phase of ring-switching
(GitHub issue #29).

## The design obstruction

The honest sum-check round verifier checks only the *Boolean-cube sum*
`∑_{b} hᵢ(b) = sumcheck_target`; it never checks that the prover's univariate message `hᵢ` equals the
ground-truth round polynomial `h⋆` derived from the witness. Consequently a per-round KState whose
local check is `hᵢ = h⋆` (`localizedRoundPolyCheck`) is **not provable** from the verifier run: a
malicious prover can send any `hᵢ` with the same Boolean-cube sum.

The standard resolution (round-by-round knowledge soundness, DP24 §2.5 / sum-check folklore) keeps
the strong local check `hᵢ = h⋆` *inside* the KState, but discharges the resulting extraction-failure
("doom-escape") branch *probabilistically*: when the verifier draws a uniform challenge `r`, the
event that `hᵢ ≠ h⋆` yet `hᵢ(r) = h⋆(r)` (so the next-round target is still consistent and extraction
silently fails) has probability at most `deg / |F|` by Schwartz–Zippel root counting. This is the
`d / |F|` per-round knowledge error.

## What this file proves

* `badPolyAgreement` — the *named residual surface* for one round: `hᵢ ≠ h⋆ ∧ hᵢ(r) = h⋆(r)`. This is
  the `hᵢ = h⋆`-shaped KState check, *negated and localized to the challenge* `r`, i.e. exactly the
  event the weakened KState tolerates.
* `card_filter_eval_eq_le_natDegree` — root counting: the challenges on which two distinct
  polynomials agree number at most `max (natDegree p) (natDegree q)` (`≤` the degree of `p - q`).
* `prob_badPolyAgreement_le` — Schwartz–Zippel: `Pr_{r ← $ᵖ F}[badPolyAgreement r p q] ≤ D / |F|`
  for any degree bound `D` with `natDegree p ≤ D` and `natDegree q ≤ D`.
* `prob_badPolyAgreement_degree_two_le` — the degree-2 specialization
  (`Pr ≤ 2 / |F|`) matching the ring-switching/Binius round polynomial `↥F⦃≤ 2⦄[X]`.

Everything is stated over plain `Polynomial F` (`F[X]`) with a `natDegree` hypothesis, so consumers
holding a bounded-degree carrier `↥F⦃≤ d⦄[X]` discharge the hypotheses via `.val` and the carrier's
`natDegree` bound. Crucially nothing here imports the CompPoly-backed `⦃≤ d⦄[X]` carrier nor the
`Binius.BinaryBasefold` soundness stack, so it can be consumed from the profile-based ring-switching
tree (`ArkLib/ProofSystem/RingSwitching/`) without dragging in the in-flight CompPoly refactor.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
-/

open Polynomial Finset ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace KStateWeaken

variable {F : Type} [Field F] [Fintype F]

/-- **Named per-round residual (weakened KState surface).**
`badPolyAgreement r p q` is the bad event tolerated by the weakened sum-check KState at a single
round: the prover message `p` differs from the ground-truth round polynomial `q` (so the strong local
check `p = q` *fails*), yet they agree at the verifier's challenge `r` (so the next-round target stays
consistent and round-by-round extraction silently fails). The whole point of the weakening is that
this event is *rare* (`prob_badPolyAgreement_le`), not impossible. -/
def badPolyAgreement (r : F) (p q : F[X]) : Prop :=
  p ≠ q ∧ p.eval r = q.eval r

/-- **Root-counting core (CompPoly-free).** For two *distinct* polynomials, the set of challenges on
which they agree has cardinality at most `natDegree (p - q)`, hence at most any common degree bound.
This is the finite-field instance of "distinct polynomials of degree `≤ D` agree on `≤ D` points",
proven from Mathlib's `Polynomial.card_roots'` applied to `p - q`. -/
theorem card_filter_eval_eq_le_natDegree [DecidableEq F] {p q : F[X]} (hpq : p ≠ q) :
    (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card ≤ (p - q).natDegree := by
  classical
  have hd0 : p - q ≠ 0 := sub_ne_zero.mpr hpq
  -- The agreement set is the root set of `p - q`.
  have hsub :
      (Finset.univ.filter (fun r : F => p.eval r = q.eval r)) ⊆ (p - q).roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    have hroot : (p - q).IsRoot r := by
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, hr.2, sub_self]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hd0).mpr hroot)
  calc (Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card
      ≤ (p - q).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (p - q).roots := (p - q).roots.toFinset_card_le
    _ ≤ (p - q).natDegree := Polynomial.card_roots' (p - q)

/-- **Schwartz–Zippel probability bound (general degree).**
For any common degree bound `D` (`natDegree p ≤ D`, `natDegree q ≤ D`) and a uniform challenge `r`,
the weakened-KState bad event holds with probability at most `D / |F|`. -/
theorem prob_badPolyAgreement_le {p q : F[X]} {D : ℕ}
    (hp : p.natDegree ≤ D) (hq : q.natDegree ≤ D) :
    Pr_{ let r ←$ᵖ F }[ badPolyAgreement r p q ] ≤ (D : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  by_cases hpq : p = q
  · -- Equal polynomials: the event `p ≠ q ∧ …` is unsatisfiable, so the probability is `0`.
    have hzero : Pr_{ let r ←$ᵖ F }[ badPolyAgreement r p q ] = 0 := by
      rw [prob_uniform_eq_card_filter_div_card]
      have hempty : (Finset.univ.filter (fun r : F => badPolyAgreement r p q)) = ∅ := by
        apply Finset.filter_false_of_mem
        intro r _
        exact fun hbad => hbad.1 hpq
      rw [hempty, Finset.card_empty]
      simp
    rw [hzero]; exact zero_le _
  · -- Distinct polynomials: bound the agreement-set cardinality by the degree budget `D`.
    rw [prob_uniform_eq_card_filter_div_card]
    -- Reduce the `badPolyAgreement` filter to the bare agreement filter (the `p ≠ q` conjunct is
    -- globally true since `p ≠ q`).
    have hfilter :
        (Finset.univ.filter (fun r : F => badPolyAgreement r p q))
          = Finset.univ.filter (fun r : F => p.eval r = q.eval r) := by
      apply Finset.filter_congr
      intro r _
      simp only [badPolyAgreement, and_iff_right_iff_imp]
      exact fun _ => hpq
    rw [hfilter]
    -- Now apply root counting and the degree budget, then divide.
    have hcard := card_filter_eval_eq_le_natDegree (F := F) hpq
    have hdeg : (p - q).natDegree ≤ D :=
      le_trans (Polynomial.natDegree_sub_le p q) (max_le hp hq)
    have hnum :
        ((Finset.univ.filter (fun r : F => p.eval r = q.eval r)).card : ℝ≥0) ≤ (D : ℝ≥0) := by
      exact_mod_cast le_trans hcard hdeg
    gcongr

/-- **Degree-2 specialization (ring-switching round polynomial).**
The ring-switching / Binius round polynomial is degree `≤ 2` (carrier `↥F⦃≤ 2⦄[X]`), giving the
sharp `2 / |F|` per-round knowledge error. Discharge `hp`, `hq` from a `↥F⦃≤ 2⦄[X]` carrier via its
`natDegree`-≤-2 property on `.val`. -/
theorem prob_badPolyAgreement_degree_two_le {p q : F[X]}
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    Pr_{ let r ←$ᵖ F }[ badPolyAgreement r p q ] ≤ (2 : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  have h := prob_badPolyAgreement_le (F := F) (D := 2) hp hq
  simpa using h

end KStateWeaken
