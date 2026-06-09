/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Probability.Instances
import ArkLib.OracleReduction.Security.Basic

/-!
# Marginal domination bricks for run-marginal arguments (issue #13)

Two protocol-independent probability lemmas isolating the measure-theoretic core of the
"run-marginal" walls in the LogUp (and sumcheck) soundness analyses:

* `probEvent_bind_le_of_forall_support` — support-quantified bind domination: if every
  continuation satisfies `Pr[q] ≤ c`, so does the bind.  This is the outer-layer step that peels
  the prover prefix / state initialization off a soundness game.

* `probEvent_bind_le_uniform_marginal` — **uniform-marginal domination**: if the first stage's
  output distribution is dominated by the uniform one (`Pr[= x] ≤ 1/|F|`, true in particular for
  the uniform challenge draw itself), and the event is *supported inside* `L` through the drawn
  value (continuations at `x ∉ L` give the event probability `0`), then the whole game's event
  probability is at most the uniform measure of `L`.  This is exactly the inequality shape of the
  `OuterRunMarginalToUniform` / `hMarginal`-style residuals: the bad-accept probability of a run
  whose acceptance pins the drawn challenge into `L` is bounded by the uniform marginal of `L`.

* `probEvent_bind_le_prob_uniform` — the same bound with the right-hand side packaged as the
  `Pr_{ let x ←$ᵖ F }[ x ∈ L ]` notation used throughout the LogUp security files.
-/

open OracleComp OracleSpec ProbabilityTheory
open scoped ENNReal NNReal

universe u v

section MarginalBound

variable {α β : Type u} {m : Type u → Type v} [Monad m] [HasEvalSPMF m]

/-- **Support-quantified bind domination.**  If every continuation reachable from the first stage
satisfies the event bound `≤ c`, then so does the bind. -/
lemma probEvent_bind_le_of_forall_support (mx : m α) (my : α → m β) (q : β → Prop) (c : ℝ≥0∞)
    (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ c) :
    Pr[ q | mx >>= my] ≤ c := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ q | my x]
      ≤ ∑' x, Pr[= x | mx] * c := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul' le_rfl (h x hx)
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ = (∑' x, Pr[= x | mx]) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = c := one_mul c

/-- **Uniform-marginal domination (card form).**  If the first stage's output distribution is
dominated by the uniform distribution on a fintype `F`, and the event is supported inside
`L ⊆ F` through the drawn value (the event has probability `0` after drawing any `x ∉ L`),
then the game's event probability is at most `|L| / |F|`. -/
lemma probEvent_bind_le_uniform_marginal {F : Type u} [Fintype F]
    (mx : m F) (k : F → m β) (q : β → Prop) (L : Set F) [DecidablePred (· ∈ L)]
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ x : F, x ∉ L → Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k]
      ≤ ((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[ q | k x]
      ≤ ∑' x : F, (if x ∈ L then (Fintype.card F : ℝ≥0∞)⁻¹ else 0) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ L
        · rw [if_pos hx]
          exact le_trans (mul_le_mul' (hunif x) probEvent_le_one) (by rw [mul_one])
        · rw [if_neg hx, hsupp x hx, mul_zero]
    _ = ∑ x : F, (if x ∈ L then (Fintype.card F : ℝ≥0∞)⁻¹ else 0) := tsum_fintype _
    _ = ((Finset.univ.filter (· ∈ L)).card : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [div_eq_mul_inv]

end MarginalBound

section ProbUniform

variable {β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- **Uniform-marginal domination (probability-notation form).**  The same bound as
`probEvent_bind_le_uniform_marginal`, with the right-hand side packaged as the uniform-sampling
probability `Pr_{ let x ←$ᵖ F }[ x ∈ L ]` consumed by the LogUp security interfaces
(`OuterRunMarginalToUniform`, `outerSoundness_sharp`, …). -/
lemma probEvent_bind_le_prob_uniform {F : Type} [Fintype F] [Nonempty F]
    (mx : m F) (k : F → m β) (q : β → Prop) (L : Set F) [DecidablePred (· ∈ L)]
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsupp : ∀ x : F, x ∉ L → Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k] ≤ Pr_{ let x ←$ᵖ F }[ x ∈ L ] := by
  refine le_trans
    (probEvent_bind_le_uniform_marginal mx k q L hunif hsupp) ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  exact le_refl _

end ProbUniform

/-! ### Axiom audit (issue #13 marginal-domination bricks) -/

#print axioms probEvent_bind_le_of_forall_support
#print axioms probEvent_bind_le_uniform_marginal
#print axioms probEvent_bind_le_prob_uniform
