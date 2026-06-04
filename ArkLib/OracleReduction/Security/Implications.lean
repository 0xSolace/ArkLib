/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Salt

/-!
# Implications between security notions

This file collects the implications between the various security notions.

For now, we only state the theorems. It's likely that we will split this file into multiple files in
a single `Implication` folder in the future, each file for the proof of a single implication.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/- TODO: add the following results
- `knowledgeSoundness` implies `soundness`
- `roundByRoundSoundness` implies `soundness`
- `roundByRoundKnowledgeSoundness` implies `roundByRoundSoundness`
- `roundByRoundKnowledgeSoundness` implies `knowledgeSoundness`

In other words, we have a lattice of security notions, with `knowledge` and `roundByRound` being
two strengthenings of soundness.
-/

/-- Knowledge soundness with knowledge error `knowledgeError < 1` implies soundness with the same
soundness error `knowledgeError`, and for the corresponding input and output languages. -/
theorem knowledgeSoundness_implies_soundness
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (knowledgeError : ℝ≥0) (hLt : knowledgeError < 1) :
      knowledgeSoundness init impl relIn relOut verifier knowledgeError →
        soundness init impl relIn.language relOut.language verifier knowledgeError := by
  simp [knowledgeSoundness, soundness, Set.language]
  intro extractor hKS WitIn' WitOut' witIn' prover stmtIn hStmtIn
  sorry
  -- have hKS' := hKS stmtIn witIn' prover
  -- clear hKS
  -- contrapose! hKS'
  -- constructor
  -- · convert hKS'; rename_i result
  --   obtain ⟨transcript, queryLog, stmtOut, witOut⟩ := result
  --   simp
  --   placeholder
  -- · simp only [Set.language, Set.mem_setOf_eq, not_exists] at hStmtIn
  --   simp only [Functor.map, Seq.seq, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, hStmtIn,
  --     PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte,
  --     zero_add, ℝ≥0.coe_lt_one_iff, hLt]

/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`. -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by
  -- PROOF SPINE (probability bridge, ArkLib#1). The combinatorial + union-bound + first-crossing
  -- backbone is fully banked and assembled below; the single remaining gap is the per-round
  -- distributional marginal (see FRONTIER below and the FRONTIER NOTE in Execution.lean).
  --
  -- 1. Destructure the rbr hypothesis to get the state function `sf` and the per-round bound `hsf`.
  -- 2. `intro` the soundness game's prover/statement; reduce the goal to
  --      `Pr[verifierOut ∈ langOut | full game] ≤ ∑ i, rbrSoundnessError i`.
  -- 3. `Verifier.StateFunction.probEvent_le_sum_of_imp_exists` reduces (2) to: on the support, the
  --    accept event implies `∃ i : ChallengeIdx, flip_i` (a per-round flip on the realized
  --    transcript prefix), PLUS the per-round bound `Pr[flip_i | full game] ≤ rbrSoundnessError i`.
  -- 4. The support-implication is `Verifier.StateFunction.exists_challenge_flip_of_full` applied to
  --    each accepting support point: `toFun_full` (contrapositive, via `probEvent_pos`) gives
  --    `sf (last n) stmtIn (tr.take)` for the realized full transcript `tr`, and `stmtIn ∉ langIn`
  --    gives `¬ sf 0`, so the first-crossing lands on a challenge round.
  -- 5. The per-round bound chains: `Pr[flip_i | full game] ≤ Pr[flip_i | rbr game i] ≤
  --    rbrSoundnessError i = hsf i`, where the first `≤` is the failure-monotone marginal.
  --
  -- FRONTIER (the only missing connective): the first `≤` in step 5. The flip event depends only on
  -- the round-`i.succ` transcript prefix; in the full game that prefix is produced by
  -- `runToRound (last n)` followed by the trailing `receiveChallenge`/`sendMessage`/`output` and
  -- verifier steps, whereas the rbr game produces it via `runToRound i.castSucc >>= getChallenge`.
  --
  -- BANKED bridge ingredients (all proven, committed):
  --   • `Verifier.StateFunction.probEvent_bind_trailing_le` — failure-monotone trailing bind;
  --   • `Verifier.StateFunction.probEvent_simulateQ_run'_bind_trailing_le` — the STATE-AWARE
  --     transport of that across `simulateQ so · |>.run' s` for an *arbitrary* stateful `so`
  --     (this was the previously-identified hard probabilistic frontier — now closed);
  --   • `Prover.fst_map_runToRound_succ_challenge` — per-round prover factorization;
  --   • `Prover.fin_take_snoc_of_le` — geometric prefix preservation under `snoc`;
  --   • `exists_challenge_flip_of_full`, `probEvent_le_sum_of_imp_exists` — combinatorial backbone.
  --
  -- KEYSTONE (DONE): the `runToRound` *round-range decomposition*
  --   `runToRound (last n) = runToRound i.succ >>= continueFromTo i.succ (last n)`
  -- is now proven, axiom-clean, in Execution.lean as
  -- `Prover.runToRound_eq_bind_continueFromTo` (plus `Prover.continueFromTo`,
  -- `continueFromTo_self`, `continueFromTo_succ_of_ne`, `processRound_eq_bind`).  It rewrites
  -- `Prover.run` / `Reduction.run` to expose the `runToRound i.succ` prefix as a `>>=`-prefix of the
  -- full run (verified to rewrite `Prover.run` directly).
  --
  -- REMAINING FRONTIER (probability-plumbing assembly; no new combinatorial/keystone content):
  --   (A) First-crossing wiring — apply
  --       `Verifier.StateFunction.probEvent_le_sum_of_imp_exists` over `κ = pSpec.ChallengeIdx` with
  --       `q` = the accept event `(_, stmtOut) ↦ stmtOut ∈ langOut` on the soundness game's result
  --       `((FullTranscript × StmtOut × WitOut) × StmtOut)` (type `OptionT ProbComp _`), and
  --       `p i x := ¬ sf i.castSucc stmtIn (x.1.1.take i.castSucc) ∧
  --                  sf i.succ stmtIn ((x.1.1.take i.castSucc).concat (x.1.1 i))`
  --       (prefix-only, via `take_succ_eq_concat`).  The support-implication `himp` is
  --       `exists_challenge_flip_of_full`, whose `hlast` hypothesis (`sf (last n) stmtIn tr`) is
  --       supplied by the contrapositive of `sf.toFun_full`; `¬ sf 0` comes from `stmtIn ∉ langIn`
  --       via `toFun_empty`.  The `OptionT ProbComp`/`run'` plumbing that ties a support point's
  --       transcript `x.1.1` to its verifier verdict `x.2` is now banked as
  --       `Reduction.support_run_verdict` (Execution.lean, axiom-clean).
  --
  --       ⚠ STATEMENT BLOCKER (2026-06-04).  Wiring (A) through `support_run_verdict` +
  --       `toFun_full`'s contrapositive reduces (A) to the SINGLE residual goal `s' ∈ support init`,
  --       where `s'` is the POST-PROVER simulation state and `init` is the (abstract) start
  --       distribution.  This is FALSE in general: a malicious prover that queries the shared oracle
  --       `oSpec` (routed through the stateful `impl`) advances the `σ`-state, so the verifier in the
  --       soundness game runs from a state outside `support init`, whereas `toFun_full` only forbids
  --       acceptance from a FRESH `init` sample.  Hence `rbrSoundness_implies_soundness` is NOT
  --       provable as stated for an arbitrary stateful `impl` (counterexample: `σ = Bool`,
  --       `init = pure false`, an `impl` whose prover-query flips the state to a verifier-accepting
  --       value while `sf (last n)` is identically false — rbr-sound with error 0, yet unsound).  It
  --       closes once `toFun_full` is strengthened to all starting states, or `impl` is restricted so
  --       prover simulation preserves `support init` (subsingleton `σ` / stateless or
  --       distribution-preserving `impl`; cf. `probEvent_simulateQ_run'_eq`).  See the expanded
  --       ASSEMBLY UPDATE in Execution.lean's FRONTIER NOTE.  This is a STATEMENT-level finding for
  --       the orchestrator, NOT closable by further plumbing.
  --   (B) Per-round bound — for each fixed `i`, show
  --       `Pr[p i | soundness game] ≤ Pr[rbr event i | rbr game i] ≤ rbrSoundnessError i (= hsf i)`.
  --       Rewrite the soundness game's `Prover.run` by the keystone to
  --       `runToRound i.succ >>= (continueFromTo … >>= output)`, push that through `Reduction.run`'s
  --       `OptionT` (verifier/`getM` tail), and drop every trailing bind by
  --       `Verifier.StateFunction.probEvent_simulateQ_run'_bind_trailing_le` (the state-aware
  --       failure-monotone transport) — applied per `s` and lifted over the shared `init` by
  --       `probEvent_bind_mono`.  The surviving `runToRound i.succ` prefix is rewritten by
  --       `Prover.fst_map_runToRound_succ_challenge` into the rbr game's
  --       `runToRound i.castSucc >>= getChallenge` shape (its trailing `receiveChallenge` dropped by
  --       the same failure-monotone step), matching `hsf i` exactly.
  --       (B) does NOT suffer the (A) state mismatch: both the soundness game and the rbr game
  --       thread `init` through the prover identically, so the per-`s` failure-monotone keystone
  --       transport applies over the shared `init`.  (B) is therefore the legitimately-closable half,
  --       blocked here only because (A) blocks the overall `sorry` regardless.
  -- The combinatorial backbone, the keystone, and the verifier-verdict support bridge
  -- (`Reduction.support_run_verdict`) are fully banked; the remaining obstruction is the (A)
  -- statement-level state-threading gap above.
  sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies round-by-round
soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrKnowledgeError := by
  unfold rbrSoundness
  unfold rbrKnowledgeSoundness at h
  obtain ⟨WitMid, extractor, kSF, h⟩ := h
  refine ⟨kSF.toStateFunction, ?_⟩
  intro stmtIn hRelIn WitIn' WitOut' witIn' prover chalIdx
  simp_all
  sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies knowledge soundness
with error `∑ i, rbrKnowledgeError i`, where the sum is over all rounds `i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
        knowledgeSoundness init impl relIn relOut verifier (∑ i, rbrKnowledgeError i) := by sorry

-- /-- Round-by-round soundness for a protocol implies state-restoration soundness for the same
-- protocol with arbitrary added non-empty salts. -/
-- theorem rbrSoundness_implies_srSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (langIn : Set StmtIn) (langOut : Set StmtOut)
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
--         Verifier.StateRestoration.soundness init impl langIn langOut (verifier.addSalt Salt)
--           (∑ i, (rbrSoundnessError i)) := by placeholder

-- /-- Round-by-round knowledge soundness for a protocol implies state-restoration
-- knowledge soundness for the same protocol with arbitrary added non-empty salts. -/
-- theorem rbrKnowledgeSoundness_implies_srKnowledgeSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
--         Verifier.StateRestoration.knowledgeSoundness init impl relIn relOut
--           (verifier.addSalt Salt) (∑ i, rbrKnowledgeError i) := by placeholder

-- STATEMENT REPAIR (2026-06-04): DELETED `srSoundness_addSalt_implies_srSoundness_original` and
-- `srKnowledgeSoundness_addSalt_implies_srKnowledgeSoundness_original`.
--
-- Both theorems were provably misconceived (and had literal `sorry` placeholders inside their own
-- *statements*, for the original game's `init`/`impl`, so they could not even be coherently stated).
-- They asserted that state-restoration (knowledge) soundness of the *salted* protocol implies
-- state-restoration (knowledge) soundness of the *original* protocol. But:
--
--   1. There is no principled way to source the original SR game's `(init, impl)` over
--      `srChallengeOracle StmtIn pSpec` from the salted game's `(srInit, srImpl)` over
--      `srChallengeOracle StmtIn (pSpec.addSalt Salt)` — the salted SR challenge oracle ranges over
--      strictly more transcripts. The two `sorry`s in the conclusion stood exactly where that
--      (nonexistent) derivation was required.
--
--   2. State-restoration soundness is precisely the soundness notion that is **NOT preserved** under
--      salting: ArkLib/OracleReduction/Salt.lean (L198-205) records an explicit in-repo
--      counterexample — "the verifier sends one random bit per round, and accepts iff it sends zero
--      for every round" — for which SR (knowledge) soundness fails to transfer across `addSalt`.
--
-- See docs/kb/audits/gh-issues-campaign-2026-06-04.md ("Design gaps", salt counterexample item) and
-- the (commented-out, deliberately deferred) `rbrSoundness_implies_srSoundness_addSalt` family above,
-- which captures the only salt/SR relationship that is conjectured to hold (rbr ⇒ SR under salt).

/-- State-restoration soundness implies basic (straightline) soundness.

This theorem shows that state-restoration security is a strengthening of basic soundness.
The error is preserved in the implication. -/
theorem srSoundness_implies_soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut verifier srSoundnessError →
        soundness init impl langIn langOut verifier srSoundnessError := by
  sorry

/-- State-restoration knowledge soundness implies basic (straightline) knowledge soundness.

This theorem shows that state-restoration knowledge soundness is a strengthening of basic
knowledge soundness. The error is preserved in the implication. -/
theorem srKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        verifier srKnowledgeError →
      knowledgeSoundness init impl relIn relOut verifier srKnowledgeError := by sorry

-- TODO: state that round-by-round security implies state-restoration security for protocol with
-- arbitrary added (non-empty?) salts

-- TODO: state that state-restoration security for added salts imply state-restoration security for
-- the original protocol (with some better parameters)

-- TODO: state that state-restoration security implies basic security

end Implications

end Verifier
