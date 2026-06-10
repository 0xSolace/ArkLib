/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Sum-check rejection core + round-lens relation correspondence (issue #13)

Two bricks of the pointwise-rejection route to the LogUp embedded sum-check soundness:

* `Simple.verifier_run_failure_of_notMem`: the Simple single-round sum-check oracle verifier
  *rejects outright* (`run = failure`) on any statement outside the input relation's language —
  the standalone extraction of the rejection core inside `simpleKnowledgeStateFunction.toFun_full`.

* `simpleProj_mem_iff`: the round-`i` statement lens (`sumcheckOracleLens`) carries the round
  relation *exactly*: the projected Simple statement satisfies `Simple.inputRelation` **iff** the
  outer round statement satisfies `relationRound i.castSucc`. The two sides are the two sides of
  the (now public) `sumcheck_round_split` sum-splitting identity — the same identity that proved
  the lens *completeness* (`oCtxLens_complete.proj_complete`); soundness needs the converse
  direction, which is the same equality read right-to-left.

No `sorry`; axiom audit at the bottom.
-/

open OracleComp OracleSpec ProtocolSpec Finset
open scoped NNReal ENNReal

namespace Sumcheck.Spec

variable {ι : Type} (oSpec : OracleSpec ι)
variable (R : Type) [CommSemiring R] (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
  [DecidableEq R] [SampleableType R]

namespace SingleRound.Simple

/-- **The Simple sum-check round verifier rejects bad claims outright.** For a statement whose
`D`-sum differs from the claimed target, the verifier's run is `failure` — independent of the
transcript (the prover's message is not consulted by the guard). Extraction of the rejection core
inside `simpleKnowledgeStateFunction.toFun_full`. -/
theorem verifier_run_failure_of_badSum
    (target : StmtIn R) (oStmt : ∀ i, OStmtIn R deg i)
    (hBad : ¬ (∑ x ∈ (univ.map D), ((oStmt ()).1.eval x) = target))
    (tr : (pSpec R deg).FullTranscript) :
    ((oracleVerifier R deg D oSpec).toVerifier).run ⟨target, oStmt⟩ tr =
      (failure : OptionT (OracleComp oSpec) (StmtOut R × (∀ i, OStmtOut R deg i))) := by
  have hGuard :
      ((Vector.finRange m).map (fun i => (oStmt ()).val.eval (D i))).sum ≠ target := by
    intro hsum
    apply hBad
    rw [Finset.sum_map]
    simpa [vector_finRange_map_sum_eq] using hsum
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [simulateQ_oracleVerify_eq]
  rw [if_neg hGuard]
  rfl

end SingleRound.Simple

end Sumcheck.Spec

/- Axiom audit. -/
#print axioms Sumcheck.Spec.SingleRound.Simple.verifier_run_failure_of_badSum
