/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ToMathlib.OracleCompEvalDistBindComm

/-!
# Distributional (`evalDist`-level) run-factoring for the appended prover

The syntactic run-factoring keystone `Prover.append_run` is proven *conditional* on
`Prover.appendRunRightResidual`, a **syntactic** `OracleComp` equality between the appended run and
the sequential `P₁.run ≫ P₂.run`. That syntactic residual is **false** when the first `pSpec₂` round
is a challenge: the appended prover samples the seam `getChallenge` *before* consuming `P₁.output`
(see `Prover.append_continueFromTo_seam_step_challenge`), whereas the factored form runs `P₁.output`
*first*. The two are different free-monad trees, hence unequal syntactically — but **equal as
distributions**, because `getChallenge` (a uniform sample) is independent of `P₁.output` (a
computation in `oSpec`), and `SPMF` is commutative (`OracleComp.evalDist_bind_comm`).

This file restates the residual and the keystone at the `evalDist` level, the form actually consumed
by completeness/soundness proofs (which only ever compare `evalDist`s). `appendRunRightResidualDist`
is the distribution-level residual; it is **dischargeable** (unlike its syntactic counterpart) by
assembling the proven left-block / message-seam / interior pieces together with
`evalDist_bind_comm` at the challenge seam. `append_run_evalDist` reduces the appended run to the
sequential composition, conditional on that residual, via the *same* seam-split backbone as the
syntactic `append_run`.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Prover

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- **Distribution-level right-block residual of `append_run`.** The `evalDist` analogue of
`appendRunRightResidual`: after the seam-split, the appended run-distribution equals the sequential
`P₁.run ≫ P₂.run` distribution. Unlike the syntactic residual, this holds even when the seam round
is a challenge, since the `getChallenge`/`P₁.output` reordering at the seam is a *distributional*
commutation (`OracleComp.evalDist_bind_comm`), not a syntactic one. -/
def appendRunRightResidualDist [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁) : Prop :=
  evalDist
      (((do
          let ⟨transcript, state⟩ ←
            (Prover.runToRound (⟨m, by omega⟩ : Fin (m + n + 1)) stmt wit (P₁.append P₂)
              >>= (P₁.append P₂).continueFromTo stmt wit ⟨m, by omega⟩ (Fin.last (m + n)))
          let output ← @liftM (OracleComp oSpec)
            (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
            (instMonadLiftTOfMonadLift (OracleComp oSpec) (OracleComp oSpec)
              (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)))
            (Stmt₃ × Wit₃) ((P₁.append P₂).output state)
          pure (transcript, output)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)))
    = evalDist
      ((do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃))

/-- **Distributional run-factoring keystone.** Running the appended prover `P₁.append P₂` equals, as
a distribution, running `P₁` then `P₂` sequentially. Proven by the same seam-split backbone as the
syntactic `append_run` (`run_eq_runToRound_last` then `runToRound_eq_bind_continueFromTo` at the seam
round `⟨m⟩`), reducing to the distribution-level residual `appendRunRightResidualDist`. This is the
form the completeness/soundness proofs consume; it sidesteps the syntactic
`getChallenge`/`P₁.output` non-commutation that blocks the syntactic `appendRunRightResidual`. -/
theorem append_run_evalDist [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).Inhabited]
    (stmt : Stmt₁) (wit : Wit₁)
    (hRight : appendRunRightResidualDist (P₁ := P₁) (P₂ := P₂) stmt wit) :
      evalDist ((P₁.append P₂).run stmt wit)
        = evalDist ((do
          let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
          let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
          return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)) := by
  rw [run_eq_runToRound_last,
      runToRound_eq_bind_continueFromTo (P₁.append P₂) stmt wit
        (⟨m, by omega⟩ : Fin (m + n + 1)) (Fin.last (m + n)) (by
          simp only [Fin.le_def, Fin.val_last]; omega)]
  simpa [appendRunRightResidualDist] using hRight

end Prover
