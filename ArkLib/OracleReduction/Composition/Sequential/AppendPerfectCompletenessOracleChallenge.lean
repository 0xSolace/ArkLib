/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessOracle
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessChallenge

/-!
# Oracle-level challenge-seam append perfect completeness

The `V_to_P`-seam (challenge) analogue of `OracleReduction.append_perfectCompleteness_msg_proof`.
Identical structure: an `OracleReduction`'s perfect completeness is the perfect completeness of its
`toReduction`; the verifier-fusion bridge `appendToReductionResidual` rewrites
`(R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction`; the underlying Reduction-level
result is now `Reduction.append_perfectCompleteness_challenge` (proven for the challenge seam from the
three per-phase relabel bridges). The only difference from the message case is the seam direction and
the honest-implementation side conditions (`himplSP`/`himplNF`/`hInit` instead of `hImplSupp`).
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level challenge-seam append perfect completeness.** The `V_to_P` analogue of
`append_perfectCompleteness_msg_proof`: from perfectly-complete oracle reductions `R₁`, `R₂` over a
challenge seam, plus the verifier-fusion bridge `appendToReductionResidual`, the appended oracle
reduction is perfectly complete. Reduces to `Reduction.append_perfectCompleteness_challenge` through
the `toReduction` view exactly as the message case does. -/
theorem append_perfectCompleteness_challenge
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hInit : NeverFail init)
    (hBridge : appendToReductionResidual R₁ R₂)
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂.Challenge]ₒ).Inhabited] :
    (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  change Reduction.perfectCompleteness init impl rel₁ rel₃ (R₁.append R₂).toReduction
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from hBridge]
  exact Reduction.append_perfectCompleteness_challenge
    R₁.toReduction R₂.toReduction h₁ h₂ hn hDir hDir₂ himplSP himplNF hInit

end OracleReduction
