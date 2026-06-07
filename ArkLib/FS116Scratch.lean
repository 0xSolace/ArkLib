import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.LiftContext.Reduction

/-! WIP (#116B): coupled FS soundness transfer. NOT in build. -/

noncomputable section
open ProtocolSpec OracleComp OracleSpec
open scoped NNReal

namespace Reduction

variable {n : ℕ}
variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Challenge i)]

theorem fiatShamir_soundness_of_stateRestoration_coupled
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (soundnessError : ℝ≥0)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (hSR : Verifier.StateRestoration.soundness srInit srImpl langIn langOut V soundnessError) :
    Verifier.soundness srInit (srImpl.addLift srChallengeQueryImpl')
      langIn langOut V.fiatShamir soundnessError := by
  classical
  haveI : ProtocolSpec.ProverOnly
      (⟨!v[Direction.P_to_V], !v[pSpec.Messages]⟩ : ProtocolSpec 1) :=
    { toProverFirst := { prover_first' := by simp } }
  intro WitIn' WitOut' witIn' prover stmtIn hstmtIn
  set srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec :=
    (do
      let st := prover.input (stmtIn, witIn')
      let ⟨msg, st'⟩ ← prover.sendMessage ⟨0, by simp⟩ st
      let _ ← prover.output st'
      return (stmtIn, msg)) with hsrProver
  refine le_trans ?_ (hSR srProver)
  unfold srSoundnessGame
  rw [Reduction.run_of_prover_first]
  simp only [hsrProver, Verifier.fiatShamir_verify_eq, Verifier.run, bind_assoc, pure_bind,
    liftComp_eq_liftM]
  -- REMAINS (mechanical, conjecture-free): the FS computation lives in `OptionT ProbComp`
  -- (verifier output Option-wrapped, peeled by `getM`), the SR computation in `ProbComp`
  -- returning `StmtIn × Option StmtOut`. Closing needs (1) the empty FS-NI challenge-oracle
  -- collapse `simulateQ (impl.addLift challengeQueryImpl) (liftM ·) = simulateQ impl ·`
  -- (`LiftContext.Reduction.simulateQ_addLift_liftM` + the OptionT variant), (2) an
  -- `OptionT`↔`ProbComp`-with-`Option` `probEvent` transport, and (3) event reconciliation:
  -- the SR predicate's `∧ stmtIn ∉ langIn` conjunct is discharged by `hstmtIn`.
  sorry

end Reduction
