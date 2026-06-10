/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendChallengeSeam
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDistChallenge

/-!
# Challenge-seam append game-factoring (`hGameFactor` discharge for a `V_to_P` seam)

`AppendChallengeSeam.lean` discharges the completeness `hGameFactor` residual of
`append_completeness_msg_proof` for the **message seam** via `append_game_factor_msg`, whose only
seam-specific step is `append_run_natural_msg` (the *syntactic* run factoring through
`Prover.append_run_msg`). At a **challenge seam** (`pSpec₂`'s round 0 is `V_to_P`) the syntactic run
factoring is *false* — the appended prover samples the seam `getChallenge` before consuming
`P₁.output` — but the appended honest *game* still factors as a distribution: the seam challenge is a
uniform sample that commutes, under the honest state-preserving implementation, past the prover's
`oSpec`-computation (the simulated analogue of the bare `evalDist_bind_comm` used in
`Prover.append_run_evalDist_challenge`, here `RunUnroll.evalDist_simulateQ_swap_prefix`).

`append_game_factor_challenge` discharges `hGameFactor` for the challenge seam; combined with the
(seam-direction-agnostic) bridges in `AppendSeamBridges.lean` it gives challenge-seam append
completeness, the missing keystone for the Spartan composed perfect completeness (#114).
-/

open OracleComp OracleSpec ProtocolSpec OptionTStateT
open scoped ENNReal NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

set_option maxHeartbeats 1000000 in
/-- **Simulated analogue of `Prover.append_continueFromTo_seam_start_challenge_evalDist`.** The seam
continuation, simulated under the state-preserving honest implementation, equals the challenge-first
`P₁.output ≫ P₂.processRound` form: the same syntactic challenge-first unroll as the bare lemma, but
the lone distributional commute (`getChallenge` past `liftComp (P₁.output)`) is done at the
`simulateQ` level via `evalDist_simulateQ_swap_prefix` (valid since the honest impl is
state-preserving). -/
private theorem simulateQ_continueFromTo_seam_challenge_evalDist
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    [instSC : ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc
          (⟨m, by omega⟩ : Fin (m + n)).succ rSeam)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctxIn₂ =>
        (liftM
          (P₂.processRound (⟨0, hn⟩ : Fin n)
            (pure
              ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            (pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ ×
              P₂.PrvState (⟨0, hn⟩ : Fin n).succ)) >>= fun p =>
        (pure
          (Transcript.appendRight T₁ p.1,
            cast (Prover.append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm p.2) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
            ((pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).succ
              × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).succ)))) s) := by
  rw [eq_of_heq (Prover.append_continueFromTo_seam_start_challenge_split
    (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit) hn hDir hDir₂ T₁ rSeam hT)]
  conv_rhs =>
    enter [1, 1, 2, 2, ctxIn₂]
    rw [show (liftM (P₂.processRound (⟨0, hn⟩ : Fin n)
              (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂))) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
          = OracleComp.liftComp (P₂.processRound (⟨0, hn⟩ : Fin n)
              (pure ((default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))),
                P₂.input ctxIn₂)))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) from
          (OracleComp.liftComp_eq_liftM _).symm]
    rw [Prover.liftComp_processRound_zero_challenge_appendRight
      (P₁ := P₁) (P₂ := P₂) hn hDir₂ T₁ ctxIn₂]
  rw [Prover.liftM_via_leftChallenge_eq_liftComp
    (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
    (X := P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2))]
  exact evalDist_simulateQ_swap_prefix _ (addLift_state_preserving impl himplSP)
    (pure ())
    (fun _ => (liftM (pSpec₂.getChallenge ⟨⟨0, hn⟩, hDir₂⟩) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (pSpec₂.Challenge ⟨⟨0, hn⟩, hDir₂⟩)))
    (fun _ => (OracleComp.liftComp (P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2))
      (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)))
    (fun _ challenge ctxIn₂ =>
      OracleComp.liftComp
        (P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂))
        (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) >>= fun f =>
      pure (Transcript.appendRight T₁
          (Transcript.concat challenge
            (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1)))),
        cast (Prover.append_PrvState_seam_succ (P₁ := P₁) (P₂ := P₂) hn).symm (f challenge))) s


/-- **State-fixed `simulateQ` bind decomposition (`run'` level).** For a state-preserving handler, the
`run'`-distribution of a simulated bind factors as the bind of the factors' `run'`-distributions
(both run from the same fixed state `s`). The `run'`-level companion of `simulateQ_run_bind_state_fixed`,
used to thread per-stage `evalDist` equalities (e.g. the seam commute) through the surrounding run. -/
theorem StateT_run'_simulateQ_bind_state_fixed {ιₒ : Type} {spec : OracleSpec ιₒ} {σ : Type}
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {α β : Type} (a : OracleComp spec α) (k : α → OracleComp spec β) (s : σ) :
    StateT.run' (simulateQ so (a >>= k)) s
      = StateT.run' (simulateQ so a) s >>= fun x => StateT.run' (simulateQ so (k x)) s := by
  rw [StateT.run'_eq, simulateQ_run_bind_state_fixed so hso a k s, map_bind]
  conv_rhs => rw [StateT.run'_eq, bind_map_left]
  refine bind_congr fun p => ?_
  rw [StateT.run'_eq]


set_option maxHeartbeats 1000000 in
/-- **OptionT-bind lifting of a `run'`-marginal equality.** If two `oSpec`-computations `A`, `B` have
the same simulated `run'`-distribution from every state, then prepending either (via `liftM`) to a
common OptionT continuation `K` gives the same simulated `run'`-distribution. The OptionT/`liftM`
companion of `StateT_run'_simulateQ_bind_state_fixed`, used to lift the prover-run factoring through the
verifier tail of `Reduction.run`. -/
theorem evalDist_simulateQ_liftM_bind_run_congr {ιₒ : Type} {spec : OracleSpec ιₒ} {σ : Type}
    (so : QueryImpl spec (StateT σ ProbComp))
    (hso : ∀ (t : spec.Domain) (s : σ) (x : spec.Range t × σ),
      x ∈ support ((so t).run s) → x.2 = s)
    {γ δ : Type} (A B : OracleComp spec γ) (K : γ → OptionT (OracleComp spec) δ) (s : σ)
    (hAB : ∀ s', evalDist (StateT.run' (simulateQ so A) s')
      = evalDist (StateT.run' (simulateQ so B) s')) :
    evalDist (StateT.run' (simulateQ so ((liftM A : OptionT (OracleComp spec) γ) >>= K).run) s)
      = evalDist (StateT.run' (simulateQ so ((liftM B : OptionT (OracleComp spec) γ) >>= K).run) s) := by
  rw [simulateQ_run'_optionT_bind_run, simulateQ_run'_optionT_bind_run]
  have key : ∀ (X : OracleComp spec γ),
      evalDist ((simulateQ so (liftM X : OptionT (OracleComp spec) γ).run).run s
          >>= fun p => p.1.elim (pure none) (fun a => (simulateQ so (K a).run).run' p.2))
        = evalDist (StateT.run' (simulateQ so X) s) >>=
            fun a => evalDist ((simulateQ so (K a).run).run' s) := by
    intro X
    have hrun : (simulateQ so (liftM X : OptionT (OracleComp spec) γ).run).run s
        = (simulateQ so X).run s >>= fun q => pure (some q.1, q.2) := by
      rw [show (liftM X : OptionT (OracleComp spec) γ).run = some <$> X from rfl, simulateQ_map,
        StateT.run_map, map_eq_bind_pure_comp]
      rfl
    rw [hrun, bind_assoc]
    have hstep : ((simulateQ so X).run s >>= fun q =>
          pure (some q.1, q.2) >>= fun p => p.1.elim (pure none)
            (fun a => (simulateQ so (K a).run).run' p.2))
        = (simulateQ so X).run s >>= fun q => (simulateQ so (K q.1).run).run' s := by
      refine bind_congr_of_forall_mem_support _ (fun q hq => ?_)
      rw [pure_bind, Option.elim_some,
        show q.2 = s from simulateQ_state_preserving so hso X s q hq]
    rw [hstep, evalDist_bind, StateT.run'_eq, evalDist_map, bind_map_left]
  rw [key A, key B, hAB]


set_option maxHeartbeats 1000000 in
/-- **Simulated right-block commute at a challenge seam.** The `simulateQ` analogue of
`Prover.append_continueFromTo_right_challenge_evalDist`: split the right block at the seam successor
(`continueFromTo_trans`), thread the proven seam commute through the interior via the state-fixed
decomposition, then fold via the syntactic, direction-agnostic
`append_right_block_from_seam_boundary_heq`. -/
private theorem simulateQ_continueFromTo_right_challenge_evalDist
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    [instSC : ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    (T₁ : FullTranscript pSpec₁)
    (rSeam : (pSpec₁ ++ₚ pSpec₂).Transcript (⟨m, by omega⟩ : Fin (m + n)).castSucc
      × (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc)
    (hT : rSeam.1 =
      Transcript.appendRight T₁
        (default : pSpec₂.Transcript (⟨0, by omega⟩ : Fin (n + 1))))
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        (Prover.continueFromTo (P₁.append P₂) stmt wit
          (⟨m, by omega⟩ : Fin (m + n)).castSucc (Fin.last (m + n)) rSeam)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((liftM (P₁.output (cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2)) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (Stmt₂ × Wit₂)) >>= fun ctx =>
          ((fun p => (Transcript.appendRight T₁ p.1,
              cast (Prover.append_PrvState_last (P₁ := P₁) (P₂ := P₂) hn).symm p.2)) <$>
            OracleComp.liftComp (P₂.runToRound (Fin.last n) ctx.1 ctx.2)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              ((pSpec₁ ++ₚ pSpec₂).Transcript (Fin.last (m + n))
                × (P₁.append P₂).PrvState (Fin.last (m + n)))))) s) := by
  rw [Prover.continueFromTo_trans (P₁.append P₂) stmt wit
    (⟨m, by omega⟩ : Fin (m + n)).castSucc (⟨m, by omega⟩ : Fin (m + n)).succ (Fin.last (m + n))
    (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)
    (by rw [Fin.le_def, Fin.val_succ, Fin.val_last]; omega) rSeam]
  rw [StateT_run'_simulateQ_bind_state_fixed _ (addLift_state_preserving impl himplSP) _ _ s,
    evalDist_bind,
    simulateQ_continueFromTo_seam_challenge_evalDist P₁ P₂ stmt wit hn hDir hDir₂ himplSP T₁ rSeam hT s,
    ← evalDist_bind,
    ← StateT_run'_simulateQ_bind_state_fixed _ (addLift_state_preserving impl himplSP) _ _ s]
  exact congrArg
    (fun X => evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
      QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s))
    (eq_of_heq (Prover.append_right_block_from_seam_boundary_heq stmt wit hn T₁ rSeam))




set_option maxHeartbeats 1000000 in
/-- **Simulated appended prover-run factoring at a challenge seam.** The `simulateQ` analogue of
`Prover.append_run_evalDist_challenge`: unroll the appended run to `runToRound seam ≫ right-block ≫
output` (`run_eq_runToRound_last` + `runToRound_eq_bind_continueFromTo`), thread the proven right-block
commute through per seam value (state-fixed decomposition + free `hT` via `seam_transcript_appendRight`),
then reconcile with the sequential `P₁;P₂` run by the same syntactic HEq factoring the bare keystone uses
(`append_runToRound_seam` + `bind_heq_congr`). -/
private theorem simulateQ_append_prover_run_evalDist
    (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    [instSC : ∀ i, SampleableType ((pSpec₁ ++ₚ pSpec₂).Challenge i)]
    (s : σ) :
    evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        ((P₁.append P₂).run stmt wit)) s)
      = evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
        QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp))
        (liftM (P₁.run stmt wit) >>= fun p₁ =>
          liftM (P₂.run p₁.2.1 p₁.2.2) >>= fun p₂ =>
          (pure ⟨p₁.1 ++ₜ p₂.1, p₂.2.1, p₂.2.2⟩ :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
              (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)))) s) := by
  rw [Prover.run_eq_runToRound_last,
    Prover.runToRound_eq_bind_continueFromTo (P₁.append P₂) stmt wit
      (⟨m, by omega⟩ : Fin (m + n)).castSucc (Fin.last (m + n))
      (by rw [Fin.le_def, Fin.val_castSucc, Fin.val_last]; omega), bind_assoc]
  rw [StateT_run'_simulateQ_bind_state_fixed _ (addLift_state_preserving impl himplSP) _ _ s,
    evalDist_bind]
  conv_lhs =>
    enter [2, rSeam]
    rw [StateT_run'_simulateQ_bind_state_fixed _ (addLift_state_preserving impl himplSP) _ _ s,
      evalDist_bind,
      simulateQ_continueFromTo_right_challenge_evalDist P₁ P₂ stmt wit hn hDir hDir₂ himplSP
        (cast (Prover.append_Transcript_seam_castSucc hn) rSeam.1) rSeam
        (Prover.seam_transcript_appendRight hn rSeam.1),
      ← evalDist_bind,
      ← StateT_run'_simulateQ_bind_state_fixed _ (addLift_state_preserving impl himplSP) _ _ s]
  rw [← evalDist_bind,
    ← StateT_run'_simulateQ_bind_state_fixed _ (addLift_state_preserving impl himplSP) _ _ s]
  refine congrArg
    (fun X => evalDist (StateT.run' (simulateQ (impl.addLift challengeQueryImpl :
      QueryImpl (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (StateT σ ProbComp)) X) s)) ?_
  apply eq_of_heq
  have hseam : HEq ((P₁.append P₂).runToRound (⟨m, by omega⟩ : Fin (m + n)).castSucc stmt wit)
      (liftM (P₁.runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
    have := Prover.append_runToRound_seam (P₁ := P₁) (P₂ := P₂) (stmt := stmt) (wit := wit)
    rwa [show ((Fin.last m).castLE (by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  simp only [Prover.run_eq_runToRound_last, liftM_bind, bind_assoc, liftM_pure, pure_bind,
    bind_map_left]
  refine Prover.bind_heq_congr
    (by rw [Prover.append_Transcript_seam_castSucc hn, Prover.append_PrvState_seam_castSucc hn]; rfl)
    rfl hseam (fun rSeam x hr => ?_)
  obtain ⟨ht, hs⟩ := Prover.prod_heq_split (Prover.append_Transcript_seam_castSucc hn)
    (Prover.append_PrvState_seam_castSucc hn) hr
  have hc2 : cast (Prover.append_PrvState_seam_castSucc hn) rSeam.2 = x.2 :=
    eq_of_heq ((cast_heq _ _).trans hs)
  have hc1 : cast (Prover.append_Transcript_seam_castSucc hn) rSeam.1 = x.1 :=
    eq_of_heq ((cast_heq _ _).trans ht)
  rw [hc2, hc1]
  apply heq_of_eq
  simp only [OracleComp.liftComp_eq_liftM, Prover.append_output_last hn,
    Transcript.appendRight_full, cast_cast, cast_eq]
  refine bind_congr fun x_1 => bind_congr fun a => ?_
  simp only [← OracleComp.liftComp_eq_liftM]
  rw [Prover.liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₂.Challenge]ₒ)
    (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)]


/-- **The simulated appended honest game factors at a challenge seam (`evalDist`-level).** The
distributional core of completeness `hGameFactor` for a `V_to_P` seam: the simulated honest game of
`R₁.append R₂` — running its rounds under `impl.addLift challengeQueryImpl` — has the same `evalDist`
as the **union-bound order** `appendStage₁ ; appendStage₂` (= `(P₁→V₁) ; (P₂→V₂)`), in the `mx >>= my`
shape `probComp_seam_completeness` consumes.

The natural-order chain `P₁ → P₂ → V₁ → V₂` is reached from the appended run by the simulated seam
swap `evalDist_simulateQ_swap_prefix` (the seam `getChallenge` commutes past `P₁.output` under the
state-preserving `impl.addLift challengeQueryImpl`); the `P₂`-past-`V₁` reorder to the stage chain is
the proven `seam_swap_evalDist_eq`. -/
theorem append_game_factor_challenge
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (stmt : Stmt₁) (wit : Wit₁) (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0) :
    evalDist (gameOf init impl (R₁.append R₂) stmt wit)
      = evalDist (init >>= fun s =>
          StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
            ((appendStage₁ R₁ R₂ stmt wit) >>= (appendStage₂ R₁ R₂)).run) s) := by
  -- The `P₂`-past-`V₁` reorder (natural-order → stage chain), seam-direction-agnostic. Pin the
  -- seam-swap `spec` (and `challengeQueryImpl`'s `pSpec`) to the combined challenge oracle so every
  -- instance (the combined `SampleableType` for `challengeQueryImpl`, the per-phase `SubSpec` lifts in
  -- `W1`/`W2`) is synthesized the *same* way the goal's are — no `haveI` indirection, no instance-term
  -- mismatch under `Eq.trans`.
  have hswap := seam_swap_evalDist_eq
    (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) init
    (impl.addLift (challengeQueryImpl))
    (addLift_state_preserving impl himplSP)
    (liftM (R₁.prover.run stmt wit)) (fun x => liftM (R₂.prover.run x.2.1 x.2.2))
    (fun x => (MonadLift.monadLift (R₁.verifier.verify stmt x.1) :
        OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₂))
    (fun x a s₂ => (MonadLift.monadLift (R₂.verifier.verify s₂ a.1) :
          OptionT (OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)) Stmt₃) >>= fun s₃ =>
      pure ((x.1 ++ₜ a.1, a.2.1, a.2.2), s₃))
    (fun x s' => simulateQ_run_neverFail _ (addLift_neverFail impl himplNF) _ s')
  -- Unfold `gameOf` (LHS) and the stage chain (RHS) so the goal's RHS becomes `hswap`'s union-bound
  -- RHS *syntactically*; `appendStageᵢ` unfold to exactly the `liftM FSTᵢ ≫ Wᵢ ≫ pure` legs.
  simp only [gameOf, appendStage₁, appendStage₂]
  -- Bridge to `hswap` (the `P₂`-past-`V₁` reorder). `convert` absorbs the defeq instance-term
  -- differences (the combined-challenge `SampleableType`); the residual goal is the seam-challenge
  -- swap (`appended game = natural-order game`).
  refine Eq.trans ?_ hswap
  -- `gameOf` (`abbrev`) unfolds to `init >>= fun s => (simulateQ so (·.run)).run' s`; pull `evalDist`
  -- through the `init` bind so the residual is the per-seed seam-challenge swap.
  simp only [gameOf]
  rw [evalDist_bind, evalDist_bind]
  refine bind_congr fun s => ?_
  -- Unfold the appended `Reduction.run` to `liftM (P₁.append P₂).run ≫ verifier-tail` (no *syntactic*
  -- prover factoring — false at a challenge seam); the seam reorder is the proven distributional
  -- prover factoring `simulateQ_append_prover_run_evalDist`, lifted through the verifier tail by
  -- `evalDist_simulateQ_liftM_bind_run_congr`, then refold to the natural chain.
  simp only [Reduction.run, Reduction.append, Verifier.append, Verifier.run, liftM_bind,
    bind_assoc, OptionT.liftM_run_getM_bind, liftM_pure, pure_bind,
    FullTranscript.append_fst, FullTranscript.append_snd]
  rw [evalDist_simulateQ_liftM_bind_run_congr (impl.addLift challengeQueryImpl)
    (addLift_state_preserving impl himplSP)
    ((R₁.prover.append R₂.prover).run stmt wit)
    (liftM (R₁.prover.run stmt wit) >>= fun p₁ =>
      liftM (R₂.prover.run p₁.2.1 p₁.2.2) >>= fun p₂ =>
      (pure ⟨p₁.1 ++ₜ p₂.1, p₂.2.1, p₂.2.2⟩ :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
          (FullTranscript (pSpec₁ ++ₚ pSpec₂) × Stmt₃ × Wit₃)))
    _ s
    (fun s' => simulateQ_append_prover_run_evalDist R₁.prover R₂.prover stmt wit hn hDir hDir₂
      himplSP s')]
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind, FullTranscript.append_fst,
    FullTranscript.append_snd]
  rfl

/-- **Challenge-seam append completeness (`hGameFactor` discharged via the seam-challenge swap).**
The challenge-seam analogue of `append_completeness_msg_via_seamFactor`: threads
`append_game_factor_challenge` into `append_completeness_msg_proof` for the same two-stage
decomposition, leaving only the (seam-direction-agnostic) per-phase challenge-oracle relabel bridges
`hStage1Bridge`/`hStage2Bridge` and the game totality `hTot` (all discharged in
`AppendSeamBridges.lean`). -/
theorem append_completeness_challenge_via_seamFactor
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .V_to_P)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .V_to_P)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (hStage1Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      evalDist (Prod.fst <$> (init >>= fun s =>
          StateT.run (simulateQ (impl.addLift challengeQueryImpl)
            (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s))
        = evalDist (gameOf init impl R₁ stmt wit))
    (hStage2Bridge : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      ∀ a s', (some a, s') ∈ support
            (init >>= fun s =>
              StateT.run (simulateQ (impl.addLift challengeQueryImpl)
                (OptionT.run (appendStage₁ R₁ R₂ stmt wit))) s) →
          goodOf m pSpec₁ rel₂ a →
          Pr[fun o => ¬ Option.elim o False (goodOf (m + n) (pSpec₁ ++ₚ pSpec₂) rel₃ ·)
              | (StateT.run' (simulateQ (impl.addLift challengeQueryImpl)
                  (OptionT.run (appendStage₂ R₁ R₂ a))) s' : ProbComp (Option _))]
            ≤ Pr[fun o => ¬ Option.elim o False (goodOf n pSpec₂ rel₃ ·)
              | gameOf init impl R₂ a.2 a.1.2.2])
    (hTot : ∀ stmt wit, (stmt, wit) ∈ rel₁ →
      Pr[⊥ | gameOf init impl (R₁.append R₂) stmt wit] = 0) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) :=
  append_completeness_msg_proof R₁ R₂ h₁ h₂
    (so := impl.addLift challengeQueryImpl)
    (mx := fun p => appendStage₁ R₁ R₂ p.1 p.2)
    (my := fun p => appendStage₂ R₁ R₂)
    (fun stmt wit _ =>
      append_game_factor_challenge R₁ R₂ stmt wit hn hDir hDir₂ himplSP himplNF)
    hStage1Bridge hStage2Bridge hTot

end Reduction
