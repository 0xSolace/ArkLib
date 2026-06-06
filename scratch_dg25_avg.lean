import ArkLib.Data.Probability.Notation

/-!
# Scratch: DG25 L4.19 covering-radius sampling — the generic averaging brick

Goal (issue #77 / ABF26 L4.19 / DG25 Thm 2.5): the mathematical heart of the covering-radius
sampling lower bound is a *translation-averaging* identity that needs no coding theory:

  `∑_{u₀} unif(ι→F)(u₀) · Pr_{γ ← $ᵖ F}[P (u₀ + γ • w)]  =  Pr_{u ← $ᵖ (ι→F)}[P u]`

for any predicate `P` on words and any fixed `w`. Intuition: averaging the line-event over a
uniform base word `u₀` (and the line slope `γ`) re-uniformizes the sampled point `u₀ + γ•w`.

Once proven, the epsCA bound assembles as:
  epsCA ≥ ⨆_{u₀} body(u₀,w) ≥ ∑_{u₀} unif(u₀)·body(u₀,w) = Pr_u[…] ≥ ((q-1)/q)·Pr_u[…],
choosing `w` beyond the covering radius so `¬ jointProximity` for every `u₀`.
-/

open scoped ProbabilityTheory NNReal ENNReal BigOperators
open ProbabilityTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Nonempty F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Translation-averaging identity (the DG25 L4.19 heart).** Averaging the line-proximity event
`P (u₀ + γ•w)` over a uniform base word `u₀` and uniform slope `γ` equals the uniform-word event
`P u`. Proof: distribute, swap the two finite sums, apply the bijection `u₀ ↦ u₀ + γ•w` (which fixes
the uniform weight, since it is constant), then collapse the `γ`-sum via `|F|·|F|⁻¹ = 1`. -/
lemma avg_line_indicator (P : (ι → F) → Prop) [DecidablePred P] (w : ι → F) :
    (∑ u₀ : ι → F, (PMF.uniformOfFintype (ι → F)) u₀ * Pr_{ let γ ← $ᵖ F }[P (u₀ + γ • w)])
      = Pr_{ let u ← $ᵖ (ι → F) }[P u] := by
  classical
  simp only [Pr_eq_tsum_indicator, tsum_fintype, PMF.uniformOfFintype_apply]
  -- goal: ∑ u₀, cᵢ * (∑ γ, c_F * ind (P (u₀ + γ•w))) = ∑ u, cᵢ * ind (P u)
  --   cᵢ = (card (ι→F))⁻¹,  c_F = (card F)⁻¹
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- goal: ∑ γ, ∑ u₀, cᵢ * (c_F * ind (P (u₀ + γ•w))) = ∑ u, cᵢ * ind (P u)
  have tr : ∀ γ : F,
      (∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P (u₀ + γ • w) then (1 : ℝ≥0∞) else 0)))
        = ∑ u₀ : ι → F, (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0)) := by
    intro γ
    simpa using Equiv.sum_comp (Equiv.addRight (γ • w))
      (fun v : ι → F => (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
        ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P v then (1 : ℝ≥0∞) else 0)))
  simp_rw [tr]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
  have hcard : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine Finset.sum_congr rfl (fun u₀ _ => ?_)
  calc (Fintype.card F : ℝ≥0∞) * ((Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          ((Fintype.card F : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0)))
      = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ *
          (((Fintype.card F : ℝ≥0∞) * (Fintype.card F : ℝ≥0∞)⁻¹) *
            (if P u₀ then (1 : ℝ≥0∞) else 0)) := by ring
    _ = (Fintype.card (ι → F) : ℝ≥0∞)⁻¹ * (if P u₀ then (1 : ℝ≥0∞) else 0) := by
          rw [ENNReal.mul_inv_cancel hcard htop, one_mul]
