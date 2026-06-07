import ArkLib.ProofSystem.Logup.Security.Completeness
import ArkLib.OracleReduction.Completeness
import ArkLib.ProofSystem.Logup.Security.OuterRun

open scoped NNReal ENNReal
open OracleComp ProtocolSpec

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Logup

/-- **Completeness from a complement-zero predicate and a failure bound (general, axiom-clean).**

If the event's complement has probability `0` (i.e. the predicate `p` holds on *every successful*
outcome of `mx`) and the failure probability `Pr[⊥ | mx]` is at most `err`, then the event
probability is at least `1 - err`.  Proof: `probEvent_compl` gives
`Pr[p] + Pr[¬p] = 1 - Pr[⊥]`; with `Pr[¬p] = 0` this is `Pr[p] = 1 - Pr[⊥] ≥ 1 - err`.

This is the *probability core* of the outer LogUp completeness obligation
(`OuterCompletenessRunResidual`): because `midRelation = Set.univ` and the honest prover/verifier
agree on every accepting transcript, the completeness predicate `prvStmtOut = stmtOut` holds on
every successful run (so its complement has probability `0`), and the run's failure event is exactly
the table-pole event bounded by `probEvent_pole_le` / `probEvent_outerVerify_reject_le`.  With this
lemma, the remaining content of `OuterCompletenessRunResidual` is exactly those two run-level
facts (`Pr[¬p] = 0` and `probFailure ≤ logupCompletenessError`), with all probability arithmetic
discharged. -/
theorem probEvent_ge_one_sub_of_compl_zero {m : Type → Type} [Monad m] [HasEvalSPMF m] {α : Type}
    (mx : m α) (p : α → Prop) (err : ℝ≥0∞)
    (hA : Pr[fun x => ¬ p x | mx] = 0) (hB : Pr[⊥ | mx] ≤ err) :
    Pr[p | mx] ≥ 1 - err := by
  have key : Pr[p | mx] = 1 - Pr[⊥ | mx] := by
    rw [← probEvent_compl mx p, hA, add_zero]
  rw [key]
  exact tsub_le_tsub_left hB 1

section OuterCompleteness

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance : Inhabited F := ⟨0⟩

-- OptionT-level collapse (no outer .run): applies directly inside Reduction.run's bind.
example {ι : Type} {oSpec : OracleSpec ι} {α β γ : Type} (pr : α) (sv : β) (e : γ) (P : Prop) [Decidable P] :
    (do
      let stmtOut ← (liftM (((fun a => (a, e)) <$> (if P then pure sv else (failure : OptionT (OracleComp oSpec) β))).run)
          : OptionT (OracleComp oSpec) (Option (β × γ)))
      Prod.mk pr <$> stmtOut.getM)
      = (if P then pure (pr, (sv, e)) else failure) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

lemma OptionT_collapse_lemma {ι : Type} {oSpec : OracleSpec ι} {α β γ : Type} (pr : α) (sv : β) (e : γ) (P : Prop) [Decidable P] :
    (do
      let stmtOut ← (liftM (((fun a => (a, e)) <$> (if P then pure sv else (failure : OptionT (OracleComp oSpec) β))).run)
          : OptionT (OracleComp oSpec) (Option (β × γ)))
      Prod.mk pr <$> stmtOut.getM)
      = (if P then pure (pr, (sv, e)) else failure) := by
  by_cases h : P
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- Honest residual for the unfinished outer LogUp completeness run-unfolding.

The verifier-side pole bound is already proved in `OuterAcceptance.lean`, and
`OptionT_collapse_lemma` above records the local verifier-tail simplification that the previous
proof attempt used. The remaining work is the full prover-run marginal calculation: unfold
`Reduction.run (outerOracleReduction ...)`, show the `x` challenge supplied to the verifier is
uniform, and transport the `none` output probability to the pole event. This is a real
probability/formalization obligation, so this module keeps it as a named `Prop` rather than a
broken theorem body. -/
def OuterCompletenessRunResidual : Prop :=
  NeverFail init →
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)

/-- Consumer for the honest outer LogUp completeness run-unfolding residual. -/
theorem outer_completeness_of_runResidual
    (h : OuterCompletenessRunResidual oSpec F n M params init impl) (hInit : NeverFail init) :
    (outerOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) :=
  h hInit

/-- The residual is definitionally the outer completeness theorem under `NeverFail init`. -/
theorem outerCompletenessRunResidual_iff :
    OuterCompletenessRunResidual oSpec F n M params init impl ↔
      (NeverFail init →
        (outerOracleReduction oSpec F n M params).completeness init impl
          (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n)) :=
  Iff.rfl

end OuterCompleteness

end Logup

/- Axiom audit for the honest outer completeness frontier. -/
#print axioms Logup.OptionT_collapse_lemma
#print axioms Logup.OuterCompletenessRunResidual
#print axioms Logup.outer_completeness_of_runResidual
#print axioms Logup.outerCompletenessRunResidual_iff
