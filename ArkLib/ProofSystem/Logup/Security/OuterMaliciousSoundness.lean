/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterVerifierSupport
import ArkLib.ProofSystem.Logup.Security.OuterMaliciousClaim
import ArkLib.ProofSystem.Logup.Security.Soundness

/-!
# Outer malicious soundness, part 1: verifier readback and the transcript claim (issue #13)

The verifier-side foundation of the `hOuter@midLanguage` run-level wiring (design:
issue #13 comment `4668149886`), consuming the challenge-level analysis of
`OuterMaliciousClaim.lean`:

* `outer_toVerifier_verify_support_full` — every surviving output of the compiled outer verifier
  reads its **entire** statement off the transcript: challenge fields are the round-1/round-3
  draws and the output oracles are the input oracles plus the round-0/round-2 prover messages
  (all `rfl` after the closed-form `simulateQ_outerVerify_eq` collapse).
* `transcriptClaim` — the after-outer mid-claim read directly off a full outer transcript.
* `outer_accept_mem_midLanguage_iff` — **accepted outputs land in `midLanguage` iff the
  transcript claim vanishes** — the `toFun_full` payload of the claim-based RBR state function:
  the final state "transcript claim = 0" is exactly acceptance into the intermediate language.

Axiom-clean. The remaining wiring (the state function, the two flip bounds via
`outerBadChallenges_card_le` / `claim_not_identicallyZero` / `card_filter_claimZero_mul_card_le`,
and the bridge assembly) instantiates the proven `OuterRbrSoundness` RBR pattern.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped BigOperators NNReal ENNReal

namespace Logup

variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- **Full-field readback for the compiled outer verifier.** Every surviving output reads its
entire statement off the transcript — the challenge fields are the round-1/round-3 draws and the
output oracles are the input oracles plus the round-0/round-2 prover messages. -/
theorem outer_toVerifier_verify_support_full
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    res.1.xChallenge = chalX F n M params (transcript.challenges) ∧
    res.1.zChallenge = (chalBatch F n M params (transcript.challenges)).1 ∧
    res.1.batchingScalars = (chalBatch F n M params (transcript.challenges)).2 ∧
    (∀ i, res.2 (.input i) = oStmt i) ∧
    res.2 .multiplicity = transcript.messages ⟨0, rfl⟩ ∧
    res.2 .helpers = transcript.messages ⟨2, rfl⟩ := by
  classical
  simp only [OracleVerifier.toVerifier] at hres
  rw [simulateQ_outerVerify_eq (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
    (stmt := stmt) (oStmt := oStmt) (chal := transcript.challenges)
    (msgs := transcript.messages)] at hres
  by_cases hacc : ∀ u : Hypercube n,
      chalX F n M params transcript.challenges + evalOnHypercube (tableOracle oStmt) u ≠ 0
  · rw [if_pos hacc] at hres
    simp only [OptionT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at hres
    subst hres
    exact ⟨rfl, rfl, rfl, fun i => rfl, rfl, rfl⟩
  · rw [if_neg hacc] at hres
    simp only [OptionT.run_failure, failure_bind] at hres
    simp at hres

end Logup

#print axioms Logup.outer_toVerifier_verify_support_full

namespace Logup

variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- The after-outer mid-claim read directly off a full outer transcript: the batched hypercube
sum at the transcript's challenges and prover messages, against the input oracles. -/
noncomputable def transcriptClaim (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params)) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) oStmt
      (transcript.messages ⟨0, rfl⟩) (transcript.messages ⟨2, rfl⟩)
      (chalX F n M params (transcript.challenges))
      (chalBatch F n M params (transcript.challenges)).1
      (chalBatch F n M params (transcript.challenges)).2 u

/-- **Accepted outputs land in `midLanguage` iff the transcript claim vanishes.** Combining the
full readback with the definition of `logupOuterSumcheckClaim`. -/
theorem outer_accept_mem_midLanguage_iff
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    res ∈ midLanguage F n M params ↔ transcriptClaim oStmt transcript = 0 := by
  obtain ⟨hx, hz, hb, hin, hm, hh⟩ :=
    outer_toVerifier_verify_support_full stmt oStmt transcript res hres
  unfold midLanguage
  rw [Set.mem_setOf_eq]
  unfold logupOuterSumcheckClaim transcriptClaim
  constructor <;> intro h <;> rw [← h] <;>
    exact Finset.sum_congr rfl (fun u _ => by rw [hx, hz, hb, hm, hh, funext hin])

end Logup

#print axioms Logup.outer_accept_mem_midLanguage_iff
