/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof
import ArkLib.ProofSystem.Logup.Security.SumcheckLensProjSound
import ArkLib.ProofSystem.Sumcheck.Spec.SeqComposeRbrSoundness

/-!
# Wiring the proven `MarginalBridge` into the LogUp sum-check soundness residual (issue #13)

`Logup.sumcheckSoundnessResidual_holds_of_rbr` (`Security/RbrToSoundBridge.lean`) reduces the LogUp
embedded sum-check plain-soundness residual `SumcheckSoundnessResidual` to four inputs:

* `hError`     — the union-bound error equation `sumcheckSoundnessError = ∑ rbrSoundnessError`;
* `hProj`      — the projection soundness algebra (Schwartz–Zippel / grand-sum brick);
* `hInnerRbr`  — the inner concrete sum-check oracle reduction's round-by-round soundness; and
* `hMarginal`  — the measure-theoretic `Verifier.MarginalBridge` per-round marginal-domination
  residual, *specialized* to `sumcheckVerifier`.

The fourth slot, `hMarginal`, is now **proven**: `Verifier.marginalBridge_holds`
(`Security/MarginalBridgeProof.lean`) establishes `Verifier.MarginalBridge … verifier …` for *any*
verifier, under the three standard honest-`impl` side conditions

* `himplSP` — state-preserving (each query implementation returns the state it was handed);
* `himplNF` — never-failing (`Pr[⊥ | (impl t).run s] = 0`); and
* `himplVB` — value-blind (the value marginal `(impl t).run'` is independent of the input state).

These are exactly the three honest-`impl` conditions the downstream consumer
`Logup.issue13_soundness_msgSeam` already threads.

This file performs the wiring: instantiating `Verifier.marginalBridge_holds` at
`verifier := (sumcheckVerifier oSpec F n M params).toVerifier`,
`langIn := midLanguage F n M params`, `langOut := outputRelation.language`, with the rbr error
`rbrSoundnessError`, discharges the `hMarginal` slot.  The result,
`Logup.sumcheckSoundnessResidual_holds_wired`, proves `SumcheckSoundnessResidual` modulo only the
genuine algebraic / round-by-round residuals `hProj` and `hInnerRbr` (plus the union-bound error
equation and the three honest-`impl` side conditions).
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ENNReal

namespace Logup

section SumcheckSoundnessWired

variable {ι : Type} (oSpec : OracleSpec ι) [oSpec.Fintype]
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed when transferring lifted round-by-round soundness. -/
local instance instInhabitedFieldSumcheckSoundnessWired : Inhabited F := ⟨0⟩

/-- The inner sum-check output statement type is inhabited by the zero target/challenge vector. -/
local instance instInhabitedLogupSumcheckStmtOutWired :
    Inhabited (LogupSumcheckStmtOut F n M params) :=
  ⟨{ target := 0, challenges := fun _ => 0 }⟩

/-- The inner sum-check oracle statement family is inhabited by the zero polynomial. -/
noncomputable local instance instInhabitedLogupSumcheckOracleStatementWired :
    ∀ i, Inhabited (LogupSumcheckOracleStatement F n M params i) :=
  fun _ => ⟨0⟩

/-- **`SumcheckSoundnessResidual` with the `MarginalBridge` slot discharged from the proven
`Verifier.marginalBridge_holds` (issue #13).**

This is `Logup.sumcheckSoundnessResidual_holds_of_rbr` with its fourth named hypothesis
`hMarginal` *eliminated*: instead of assuming the per-round marginal-domination residual
abstractly, we supply it via the now-proven `Verifier.marginalBridge_holds`, specialized to the
LogUp embedded sum-check verifier.  The remaining inputs are exactly

* `hError`     — the union-bound error equation `sumcheckSoundnessError = ∑ i, rbrSoundnessError i`;
* `hProj`      — the projection soundness algebra (upstream Schwartz–Zippel / grand-sum brick);
* `hInnerRbr`  — the inner concrete sum-check oracle reduction's round-by-round soundness; and the
  three standard honest-`impl` side conditions
* `himplSP` / `himplNF` / `himplVB` — state-preserving / never-failing / value-blind, the same three
  conditions the downstream consumer `Logup.issue13_soundness_msgSeam` supplies.

Thus the LogUp embedded sum-check plain-soundness residual is reduced to *only* the algebraic /
round-by-round residuals `hProj` + `hInnerRbr` (modulo the union-bound bookkeeping and the honest
`impl` conditions). -/
theorem sumcheckSoundnessResidual_holds_wired
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    SumcheckSoundnessResidual oSpec F n M params init impl sumcheckSoundnessError :=
  sumcheckSoundnessResidual_holds_of_rbr oSpec F n M params init impl sumcheckSoundnessError
    hError hProj hInnerRbr
    (Verifier.marginalBridge_holds himplSP himplNF himplVB)

/-! ### Language-parametric soundness wiring

The original `SumcheckSoundnessResidual` is pinned to `midLanguage`.  The corrected LogUp soundness
close uses the non-degenerate `midSoundnessProtocolLanguage`, so the same lift/marginal wiring is
made language-parametric below.  The only language-specific input is the projection-soundness
condition for the chosen outer language.
-/

/-- **Projection soundness for an arbitrary outer language.**

If an outer after-phase statement is outside `outerLangIn`, its projection through the LogUp
sum-check lens is outside the chosen inner input language.  This is the exact `proj_sound` field
needed by `OracleStatement.Lens.IsSound`; making the outer language explicit lets the issue #13
soundness close use the corrected non-degenerate intermediate language rather than the historical
`midLanguage`. -/
def SumcheckLensProjSoundFor
    (outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i)))
    (innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))) : Prop :=
  ∀ outerStmtIn : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i),
    outerStmtIn ∉ outerLangIn →
    (logupSumcheckOracleLens.{0} oSpec F n M params).toLens.proj outerStmtIn ∉ innerLangIn

omit [oSpec.Fintype] [Fact ((-1 : F) ≠ 1)] in
/-- Promote the historical `midLanguage` projection-soundness fact to any outer language containing
`midLanguage`.

This is the exact monotonicity principle for the `proj_sound` half of the LogUp sum-check lens: if
every zero-claim after-outer state is admitted by `outerLangIn`, then being outside `outerLangIn`
implies being outside `midLanguage`, so the existing `SumcheckLensProjSound` proof applies. -/
theorem SumcheckLensProjSoundFor_of_midLanguage_subset
    {outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i))}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hSubset : midLanguage F n M params ⊆ outerLangIn)
    (hProj : SumcheckLensProjSound oSpec F n M params innerLangIn) :
    SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn := by
  intro outerStmtIn hNotOuter
  exact hProj outerStmtIn (fun hMid => hNotOuter (hSubset hMid))

/-- `OracleStatement.Lens.IsSound` for the LogUp sum-check lens, parametrized by the outer input
language.  The output side is still vacuous because the inner output language is `Set.univ`. -/
@[reducible] def sumcheckLensSoundFor
    (outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i)))
    (innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i)))
    (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn) :
    (logupSumcheckOracleLens.{0} oSpec F n M params).toLens.IsSound
      outerLangIn outputRelation.language innerLangIn (Set.univ)
      ((logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.toVerifier.compatStatement
        (logupSumcheckOracleLens.{0} oSpec F n M params).toLens) where
  proj_sound := hProj
  lift_sound := by
    intro _ _ _ hNot
    exact absurd (Set.mem_univ _) hNot

/-- `OracleStatement.Lens.IsSound` for the LogUp sum-check lens with an arbitrary inner output
language.

The lifted LogUp output language is `outputRelation.language = Set.univ`, so the `lift_sound` half
is vacuous independently of the terminal language used by the inner sum-check. This lets callers
thread the canonical final sum-check relation instead of forcing the inner theorem to target
`Set.univ`. -/
@[reducible] def sumcheckLensSoundForOut
    (outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i)))
    (innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i)))
    (innerLangOut : Set (LogupSumcheckStmtOut F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i)))
    (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn) :
    (logupSumcheckOracleLens.{0} oSpec F n M params).toLens.IsSound
      outerLangIn outputRelation.language innerLangIn innerLangOut
      ((logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.toVerifier.compatStatement
        (logupSumcheckOracleLens.{0} oSpec F n M params).toLens) where
  proj_sound := hProj
  lift_sound := by
    intro _ _ _ hNot
    exact absurd (Set.mem_univ _) hNot

/-- **Lifted RBR soundness of the embedded sum-check over an arbitrary outer language.** -/
theorem sumcheckVerifier_rbrSoundness_forLang
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i))}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError) :
    (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
      outerLangIn outputRelation.language rbrSoundnessError := by
  haveI := logupSumcheck_liftContextCoherent oSpec F n M params
  haveI := sumcheckLensSoundFor oSpec F n M params outerLangIn innerLangIn hProj
  exact OracleVerifier.liftContext_rbr_soundness
    (lens := logupSumcheckOracleLens.{0} oSpec F n M params)
    (logupConcreteSumcheckOracleReduction oSpec F n M params (Fact.out : (-1 : F) ≠ 1)).verifier
    hInnerRbr

/-- **Lifted RBR soundness of the embedded sum-check with an arbitrary inner output language.**

This is the variant needed by the canonical generic sum-check theorem: the inner verifier may end in
`relationRound (Fin.last n)` while the lifted LogUp verifier still targets `outputRelation.language`,
which is `Set.univ`. -/
theorem sumcheckVerifier_rbrSoundness_forLangOut
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i))}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    {innerLangOut : Set (LogupSumcheckStmtOut F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn innerLangOut rbrSoundnessError) :
    (sumcheckVerifier oSpec F n M params).rbrSoundness init impl
      outerLangIn outputRelation.language rbrSoundnessError := by
  haveI := logupSumcheck_liftContextCoherent oSpec F n M params
  haveI := sumcheckLensSoundForOut oSpec F n M params outerLangIn innerLangIn innerLangOut hProj
  exact OracleVerifier.liftContext_rbr_soundness
    (lens := logupSumcheckOracleLens.{0} oSpec F n M params)
    (logupConcreteSumcheckOracleReduction oSpec F n M params (Fact.out : (-1 : F) ≠ 1)).verifier
    hInnerRbr

/-- **Plain soundness of the embedded sum-check over an arbitrary outer language, with the generic
MarginalBridge slot discharged.**

This is the corrected-language analogue of `sumcheckSoundnessResidual_holds_wired`: it transfers the
inner RBR soundness through `liftContext`, then applies the proven `Verifier.marginalBridge_holds`
under the standard honest-`impl` side conditions. -/
theorem sumcheckVerifier_soundness_forLang_wired
    (outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i)))
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn (Set.univ) rbrSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (sumcheckVerifier oSpec F n M params).soundness init impl
      outerLangIn outputRelation.language sumcheckSoundnessError := by
  have hRbr := sumcheckVerifier_rbrSoundness_forLang oSpec F n M params init impl hProj hInnerRbr
  subst hError
  exact Verifier.rbrSoundness_imp_soundness_of_marginal init impl hRbr
    (Verifier.marginalBridge_holds himplSP himplNF himplVB)

/-- **Plain embedded-sumcheck soundness with an arbitrary inner output language.** -/
theorem sumcheckVerifier_soundness_forLang_wired_innerOut
    (outerLangIn : Set (StmtAfterOuter F n M params ×
      (∀ i, OStmtAfterOuter F n M params i)))
    (sumcheckSoundnessError : ℝ≥0)
    {rbrSoundnessError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0}
    {innerLangIn : Set (LogupSumcheckStmtIn F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    {innerLangOut : Set (LogupSumcheckStmtOut F n M params ×
      (∀ i, LogupSumcheckOracleStatement F n M params i))}
    (hError : sumcheckSoundnessError = ∑ i, rbrSoundnessError i)
    (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn innerLangIn)
    (hInnerRbr :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        innerLangIn innerLangOut rbrSoundnessError)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (sumcheckVerifier oSpec F n M params).soundness init impl
      outerLangIn outputRelation.language sumcheckSoundnessError := by
  have hRbr :=
    sumcheckVerifier_rbrSoundness_forLangOut oSpec F n M params init impl hProj hInnerRbr
  subst hError
  exact Verifier.rbrSoundness_imp_soundness_of_marginal init impl hRbr
    (Verifier.marginalBridge_holds himplSP himplNF himplVB)

/-! ### Inner multi-round RBR assembly from per-round facts

  The theorem above still accepts the whole concrete inner sum-check RBR statement as `hInnerRbr`.
  The generic sum-check development can assemble that statement from per-round RBR soundness plus the
  binary append-RBR keystone.  The next two theorems expose that smaller residual surface directly to
  LogUp callers.
  -/

omit [oSpec.Fintype] [Fintype F] in
/-- **Concrete LogUp inner sum-check RBR from per-round RBR plus binary append-RBR.**

  This specializes `Sumcheck.Spec.oracleVerifier_rbrSoundness_of_round_append` to LogUp's degree and
  `{±1}` domain, producing exactly the concrete inner verifier RBR statement consumed by the LogUp
  `liftContext` soundness bridge. -/
theorem logupConcreteSumcheckOracleReduction_rbrSoundness_roundAppend
      (lang : (i : Fin (n + 1)) →
        Set (Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
      (rbrSoundnessError :
        ∀ _ : Fin n,
          (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
      (hRound : ∀ i : Fin n,
        (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
            (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
          (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
      (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
          {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
          [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
          (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
          {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
          {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
          V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
          (V₁.append V₂).rbrSoundness init impl l₁ l₃
            (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm)) :
      (logupConcreteSumcheckOracleReduction oSpec F n M params
          (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
        (lang 0) (lang (Fin.last n))
        (fun combinedIdx =>
          letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
          rbrSoundnessError ij.1 ij.2) :=
    Sumcheck.Spec.oracleVerifier_rbrSoundness_of_round_append lang rbrSoundnessError hRound hAppend

/-- **Plain embedded-sumcheck soundness from per-round inner RBR and append-RBR.**

  Compared with `sumcheckVerifier_soundness_forLang_wired`, this no longer asks for the opaque
  multi-round inner RBR fact.  It assembles that fact from:

  * per-round RBR soundness of each single-round generic sum-check oracle verifier;
  * the binary `Verifier.append` RBR keystone; and
  * the final-language equation `hLast : lang (Fin.last n) = Set.univ`.

  The remaining language-specific algebra is still exactly the projection-soundness hypothesis
  `hProj` for the chosen outer language. -/
theorem sumcheckVerifier_soundness_forLang_wired_roundAppend
      (outerLangIn : Set (StmtAfterOuter F n M params ×
        (∀ i, OStmtAfterOuter F n M params i)))
      (sumcheckSoundnessError : ℝ≥0)
      (lang : (i : Fin (n + 1)) →
        Set (Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
      (rbrSoundnessError :
        ∀ _ : Fin n,
          (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
      (hLast : lang (Fin.last n) = Set.univ)
      (hError : sumcheckSoundnessError =
        ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
          (fun combinedIdx =>
            letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
            rbrSoundnessError ij.1 ij.2) i)
      (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn (lang 0))
      (hRound : ∀ i : Fin n,
        (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
            (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
          (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
      (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
          {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
          [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
          (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
          {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
          {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
          V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
          (V₁.append V₂).rbrSoundness init impl l₁ l₃
            (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
      (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
        x ∈ support ((impl t).run s) → x.2 = s)
      (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
      (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
        evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        outerLangIn outputRelation.language sumcheckSoundnessError := by
    let composedError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0 :=
      fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2
    have hInner :
        (logupConcreteSumcheckOracleReduction oSpec F n M params
            (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
          (lang 0) (Set.univ) composedError := by
      rw [← hLast]
      exact logupConcreteSumcheckOracleReduction_rbrSoundness_roundAppend
        oSpec F n M params init impl lang rbrSoundnessError hRound hAppend
    exact sumcheckVerifier_soundness_forLang_wired oSpec F n M params init impl outerLangIn
      sumcheckSoundnessError hError hProj hInner himplSP himplNF himplVB

/-- **Plain embedded-sumcheck soundness from per-round inner RBR and append-RBR, preserving the
inner terminal language.**

Unlike `sumcheckVerifier_soundness_forLang_wired_roundAppend`, this theorem does not require
`lang (Fin.last n) = Set.univ`. The lifted LogUp output relation is already universal, so the inner
multi-round RBR fact may end at the canonical final sum-check relation. -/
theorem sumcheckVerifier_soundness_forLang_wired_roundAppend_innerOut
      (outerLangIn : Set (StmtAfterOuter F n M params ×
        (∀ i, OStmtAfterOuter F n M params i)))
      (sumcheckSoundnessError : ℝ≥0)
      (lang : (i : Fin (n + 1)) →
        Set (Sumcheck.Spec.StatementRound F n i ×
          (∀ j, Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params) j)))
      (rbrSoundnessError :
        ∀ _ : Fin n,
          (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
      (hError : sumcheckSoundnessError =
        ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
          (fun combinedIdx =>
            letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
            rbrSoundnessError ij.1 ij.2) i)
      (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn (lang 0))
      (hRound : ∀ i : Fin n,
        (Sumcheck.Spec.SingleRound.oracleVerifier F n (logupSumcheckDegree M params)
            (signDomain F (Fact.out : (-1 : F) ≠ 1)) oSpec i).rbrSoundness init impl
          (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
      (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
          {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
          [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
          (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
          {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
          {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
          V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
          (V₁.append V₂).rbrSoundness init impl l₁ l₃
            (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
      (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
        x ∈ support ((impl t).run s) → x.2 = s)
      (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
      (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
        evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        outerLangIn outputRelation.language sumcheckSoundnessError := by
    let composedError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0 :=
      fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2
    have hInner :
        (logupConcreteSumcheckOracleReduction oSpec F n M params
            (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
          (lang 0) (lang (Fin.last n)) composedError :=
      logupConcreteSumcheckOracleReduction_rbrSoundness_roundAppend
        oSpec F n M params init impl lang rbrSoundnessError hRound hAppend
    exact sumcheckVerifier_soundness_forLang_wired_innerOut oSpec F n M params init impl
      outerLangIn sumcheckSoundnessError hError hProj hInner himplSP himplNF himplVB

/-- **Plain embedded-sumcheck soundness with the canonical per-round relation chain.**

The per-round RBR facts and the final-language transport are both internal: generic sum-check closes
each single round over `relationRound i.castSucc → relationRound i.succ`, and the LogUp lift accepts
the canonical final relation because its outer output language is `Set.univ`.  The only remaining
inner composition hypothesis is the binary `Verifier.append` RBR keystone. -/
theorem sumcheckVerifier_soundness_forLang_wired_canonicalRoundAppend
      [(oSpec + [(Sumcheck.Spec.SingleRound.pSpec F
        (logupSumcheckDegree M params)).Challenge]ₒ'challengeOracleInterface).Fintype]
      [(oSpec + [(Sumcheck.Spec.SingleRound.pSpec F
        (logupSumcheckDegree M params)).Challenge]ₒ'challengeOracleInterface).Inhabited]
      (outerLangIn : Set (StmtAfterOuter F n M params ×
        (∀ i, OStmtAfterOuter F n M params i)))
      (sumcheckSoundnessError : ℝ≥0)
      (rbrSoundnessError :
        ∀ _ : Fin n,
          (Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params)).ChallengeIdx → ℝ≥0)
      (hError : sumcheckSoundnessError =
        ∑ i : (logupSumcheckPSpec F n M params).ChallengeIdx,
          (fun combinedIdx =>
            letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
            rbrSoundnessError ij.1 ij.2) i)
      (hProj : SumcheckLensProjSoundFor oSpec F n M params outerLangIn
        (logupSumcheckInputLanguage F n M params (Fact.out : (-1 : F) ≠ 1)))
      (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
          {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
          [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
          (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
          {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃}
          {e₁ : p₁.ChallengeIdx → ℝ≥0} {e₂ : p₂.ChallengeIdx → ℝ≥0},
          V₁.rbrSoundness init impl l₁ l₂ e₁ → V₂.rbrSoundness init impl l₂ l₃ e₂ →
          (V₁.append V₂).rbrSoundness init impl l₁ l₃
            (Sum.elim e₁ e₂ ∘ ChallengeIdx.sumEquiv.symm))
      (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
        x ∈ support ((impl t).run s) → x.2 = s)
      (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
      (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
        evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
      (sumcheckVerifier oSpec F n M params).soundness init impl
        outerLangIn outputRelation.language sumcheckSoundnessError := by
    let composedError : (logupSumcheckPSpec F n M params).ChallengeIdx → ℝ≥0 :=
      fun combinedIdx =>
        letI ij := ProtocolSpec.seqComposeChallengeIdxToSigma combinedIdx
        rbrSoundnessError ij.1 ij.2
    have hInner :
        (logupConcreteSumcheckOracleReduction oSpec F n M params
            (Fact.out : (-1 : F) ≠ 1)).verifier.rbrSoundness init impl
          (logupSumcheckInputLanguage F n M params (Fact.out : (-1 : F) ≠ 1))
          (Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params)
            (signDomain F (Fact.out : (-1 : F) ≠ 1)) (Fin.last n)).language
          composedError :=
      Sumcheck.Spec.oracleVerifier_rbrSoundness_of_canonical_round_append
        (R := F) (n := n) (deg := logupSumcheckDegree M params)
        (D := signDomain F (Fact.out : (-1 : F) ≠ 1)) (oSpec := oSpec)
        (init := init) (impl := impl) rbrSoundnessError hAppend
    exact sumcheckVerifier_soundness_forLang_wired_innerOut oSpec F n M params init impl
      outerLangIn sumcheckSoundnessError hError hProj hInner himplSP himplNF himplVB

end SumcheckSoundnessWired

end Logup

#print axioms Logup.sumcheckVerifier_rbrSoundness_forLang
#print axioms Logup.sumcheckVerifier_rbrSoundness_forLangOut
#print axioms Logup.sumcheckVerifier_soundness_forLang_wired
#print axioms Logup.sumcheckVerifier_soundness_forLang_wired_innerOut
#print axioms Logup.SumcheckLensProjSoundFor_of_midLanguage_subset
#print axioms Logup.logupConcreteSumcheckOracleReduction_rbrSoundness_roundAppend
#print axioms Logup.sumcheckVerifier_soundness_forLang_wired_roundAppend
#print axioms Logup.sumcheckVerifier_soundness_forLang_wired_roundAppend_innerOut
#print axioms Logup.sumcheckVerifier_soundness_forLang_wired_canonicalRoundAppend
