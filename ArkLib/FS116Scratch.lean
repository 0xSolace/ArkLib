import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.Security.StateRestoration

/-!
# WIP (#116B): coupled basic Fiat–Shamir soundness transfer

**Not part of the build** (not in `ArkLib.lean`). This is a verified-down-to-one-`sorry`
proof skeleton for the genuine state-restoration → Fiat–Shamir *soundness* transfer, under the
natural oracle coupling `fsImpl := srImpl.addLift srChallengeQueryImpl'`, `fsInit := srInit`.

What is **verified** here (type-checks, no `sorry` in this part):
* The coupled statement is well-formed.
* The whole *reduction* is sound: the FS malicious prover (over `oSpec + fsChallengeOracle`,
  the SAME spec as the SR prover since `fsChallengeOracle := srChallengeOracle`) is mapped to an
  SR prover that **replays its full state evolution** — `sendMessage` THEN `output` — which is
  required for exact distribution equality because `output` runs (and shares the StateT
  oracle-table state) before the verifier derives the transcript. `refine le_trans ?_ (hSR srProver)`
  closes the conceptual reduction.
* `Reduction.run_of_prover_first` + `Verifier.fiatShamir_verify_eq` + an initial `simp` reduce the
  goal to a concrete distribution-inequality between two fully explicit computations.

What **remains** (the single `sorry`): a mechanical normalization showing the two `simulateQ … .run'`
computations agree, then `probEvent` congruence + event reconciliation under `hstmtIn`. The needed
toolkit (`liftM_eq_monadLift`, the empty-NI-challenge-oracle collapse, OptionT/`getM` ↔ Option) is
currently **private** to `FiatShamir/BasicCompleteness` (`CompletenessAux`) and `Component/NoInteraction`;
finishing means reconstructing those helpers for the soundness setting. `deriveTranscriptFS =
deriveTranscriptSR` is definitional (alias).
-/

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
  -- SR prover replays the FS prover's full state evolution: sendMessage THEN output.
  set srProver : Prover.StateRestoration.Soundness oSpec StmtIn pSpec :=
    (do
      let st := prover.input (stmtIn, witIn')
      let ⟨msg, st'⟩ ← prover.sendMessage ⟨0, by simp⟩ st
      let _ ← prover.output st'
      return (stmtIn, msg)) with hsrProver
  -- Conceptual reduction: VERIFIED sound (this `le_trans` type-checks).
  refine le_trans ?_ (hSR srProver)
  unfold srSoundnessGame
  rw [Reduction.run_of_prover_first]
  simp only [hsrProver, Verifier.fiatShamir_verify_eq, Verifier.run, bind_assoc, pure_bind,
    liftComp_eq_liftM]
  -- REMAINS: mechanical `simulateQ`/OptionT normalization + `probEvent` congruence + event ext.
  sorry

end Reduction
