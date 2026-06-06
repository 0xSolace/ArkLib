import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Completeness

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [∀ i, SampleableType (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

theorem run_eq_honestExecution
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    Reduction.duplexSpongeFiatShamir_run_eq_honestExecution (U := U) R stmtIn witIn := by
  unfold Reduction.duplexSpongeFiatShamir_run_eq_honestExecution
  unfold Reduction.run Reduction.duplexSpongeFiatShamir
  unfold Reduction.duplexSpongeFiatShamirHonestExecution
  unfold Reduction.duplexSpongeFiatShamirHonestRun
  unfold Reduction.prover
  -- let's try rfl
  rfl
