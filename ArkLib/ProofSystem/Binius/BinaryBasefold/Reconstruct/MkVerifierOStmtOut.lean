/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Basic

/-!
## Computation rules for `OracleVerifier.mkVerifierOStmtOut`

`OracleVerifier.mkVerifierOStmtOut` (defined in `ArkLib.OracleReduction.Basic`) builds the
output oracle statements of an oracle verifier by routing each output index `i : ιₛₒ` through an
embedding `embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx`:

* if `embed i = Sum.inl j` the output oracle is taken from the input oracle statement `oStmt j`;
* if `embed i = Sum.inr j` the output oracle is taken from the prover's message `transcript j`.

This file packages the two corresponding *computation rules* — `mkVerifierOStmtOut_inl` and
`mkVerifierOStmtOut_inr` — which rewrite an application of `mkVerifierOStmtOut` once the value of
`embed i` is known. They are consumed by the Binius `BinaryBasefold.ReductionLogic` step logic
(e.g. `snoc_oracle_eq_mkVerifierOStmtOut_commitStep`), where the commit-step embedding routes the
old codeword oracles via `Sum.inl` and the freshly committed oracle via `Sum.inr`.

The two lemmas live in the `OracleVerifier` namespace so that the existing call sites
`OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ h_embed` and the analogous `inr` form resolve
against them.
-/

open OracleSpec ProtocolSpec

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

omit Oₛᵢ Oₘ in
/-- Computation rule for `mkVerifierOStmtOut` on the `Sum.inl` branch: when the embedding sends the
output index `i` to an input oracle index `j` (`embed i = Sum.inl j`), the corresponding output
oracle statement is the input oracle statement `oStmt j`, transported along `hEq i` and `h`. -/
@[simp]
lemma mkVerifierOStmtOut_inl
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hEq : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    (oStmt : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (i : ιₛₒ) (j : ιₛᵢ) (h : embed i = Sum.inl j) :
    mkVerifierOStmtOut embed hEq oStmt transcript i = (hEq i ▸ h ▸ oStmt j : OStmtOut i) := by
  simp only [mkVerifierOStmtOut, MessageIdx, Message]
  split
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, Sum.inl.injEq] at heq
    subst heq
    rfl
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, reduceCtorEq] at heq

omit Oₛᵢ Oₘ in
/-- Computation rule for `mkVerifierOStmtOut` on the `Sum.inr` branch: when the embedding sends the
output index `i` to a prover-message index `j` (`embed i = Sum.inr j`), the corresponding output
oracle statement is the prover's message `transcript.messages j`, transported along `hEq i` and
`h`. -/
@[simp]
lemma mkVerifierOStmtOut_inr
    (embed : ιₛₒ ↪ ιₛᵢ ⊕ pSpec.MessageIdx)
    (hEq : ∀ i, OStmtOut i = match embed i with
      | Sum.inl j => OStmtIn j
      | Sum.inr j => pSpec.Message j)
    (oStmt : ∀ i, OStmtIn i) (transcript : FullTranscript pSpec)
    (i : ιₛₒ) (j : pSpec.MessageIdx) (h : embed i = Sum.inr j) :
    mkVerifierOStmtOut embed hEq oStmt transcript i =
      (hEq i ▸ h ▸ transcript.messages j : OStmtOut i) := by
  simp only [mkVerifierOStmtOut, MessageIdx, Message]
  split
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, reduceCtorEq] at heq
  · rename_i heq
    rw [h] at heq
    simp only [MessageIdx, Sum.inr.injEq] at heq
    subst heq
    rfl

end OracleVerifier
