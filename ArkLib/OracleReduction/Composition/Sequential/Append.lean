/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This file gives the definition & properties of the sequential composition of two (oracle)
  reductions. For composition to be valid, we need that the output context (statement + oracle
  statement + witness) for the first (oracle) reduction is the same as the input context for the
  second (oracle) reduction.

  We have refactored the composition logic for `ProtocolSpec` and its associated structures into
  `ProtocolSpec.lean`, and we will use the definitions from there.

  We will prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed (with extra conditions on the extractor).
-/

open OracleComp OracleSpec SubSpec

universe u v

section find_home

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

end find_home

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/--
Appending two provers corresponding to two reductions, where the output statement & witness type for
the first prover is equal to the input statement & witness type for the second prover. We also
require a verifier for the first protocol in order to derive the intermediate statement for the
second prover.

This is defined by combining the two provers' private states and functions, with the exception that
the last private state of the first prover is "merged" into the first private state of the second
prover (via outputting the new statement and witness, and then inputting these into the second
prover). -/
def Prover.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where

  /- The combined prover's states are the concatenation of the first prover's states and the second
  prover's states (except the first one). -/
  PrvState := Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState) ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun ctxIn => by
    simp only [Function.comp_apply, Fin.cast_zero]
    exact P₁.input ctxIn

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m`, then it sends the message & updates the state as the first prover
  - if `i = m`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. -/
  sendMessage := fun ⟨i, hDir⟩ state => by
    dsimp [Fin.vappend_eq_append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp [hi, Fin.vappend_left_of_lt] at hDir ⊢
      simp [this] at state
      exact P₁.sendMessage ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp [hi', Fin.vappend_right_of_not_lt] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.sendMessage ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp [hi, Fin.vappend_right_of_not_lt] at hDir ⊢
        simp [hi1] at state
        exact P₂.sendMessage ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨i, hDir⟩ state => by
    dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp only [hi, Fin.vappend_left_of_lt, dif_pos (show ↑i + 1 < m + 1 by omega)] at hDir ⊢
      simp only [this, dif_pos] at state
      exact P₁.receiveChallenge ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp [hi', Fin.vappend_right_of_not_lt] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.receiveChallenge ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp [hi, Fin.vappend_right_of_not_lt] at hDir ⊢
        simp [hi1] at state
        exact P₂.receiveChallenge ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- The combined prover's output function has two cases:
  - if the second protocol is empty, then it is the composition of the first prover's output
    function, the second prover's input function, and the second prover's output function.
  - if the second protocol is non-empty, then it is the second prover's output function. -/
  output := fun state => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.cast, Fin.last, Fin.subNat] at state
    by_cases hn : n = 0
    · simp only [hn, Nat.add_zero, dif_pos (show m < m + 1 from lt_add_one m)] at state
      exact (do
        let ctxIn₂ ← P₁.output state
        letI state₂ := P₂.input ctxIn₂
        P₂.output (dcast (by simp [hn]) state₂))
    · haveI : m + n - (m + 1) + 1 = n := by omega
      simp only [Order.lt_add_one_iff, add_le_iff_nonpos_right, nonpos_iff_eq_zero, hn, ↓reduceDIte,
        eq_rec_constant] at state
      exact P₂.output (dcast (by simp [this, Fin.last]) state)

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
      Verifier oSpec Stmt₁ Stmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Composition of reductions boils down to composing the provers and verifiers. -/
def Reduction.append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Reduction oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

open Function Embedding in
def OracleVerifier.append (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt challenges => by
    -- First, invoke the first oracle verifier, handling queries as necessary
    have := V₁.verify stmt (fun chal =>
      by
        simpa [ChallengeIdx.inl, ProtocolSpec.append] using challenges (ChallengeIdx.inl chal))
    simp at this
    -- Then, invoke the second oracle verifier, handling queries as necessary
    -- Return the final output statement
    sorry

  -- Need to provide an embedding `ιₛ₃ ↪ ιₛ₁ ⊕ (pSpec₁ ++ₚ pSpec₂).MessageIdx`
  embed :=
    -- `ιₛ₃ ↪ ιₛ₂ ⊕ pSpec₂.MessageIdx`
    .trans V₂.embed <|
    -- `ιₛ₂ ⊕ pSpec₂.MessageIdx ↪ (ιₛ₁ ⊕ pSpec₁.MessageIdx) ⊕ pSpec₂.MessageIdx`
    .trans (.sumMap V₁.embed (.refl _)) <|
    -- re-associate the sum `_ ↪ ιₛ₁ ⊕ (pSpec₁.MessageIdx ⊕ pSpec₂.MessageIdx)`
    .trans (Equiv.sumAssoc _ _ _).toEmbedding <|
    -- use the equivalence `pSpec₁.MessageIdx ⊕ pSpec₂.MessageIdx ≃ (pSpec₁ ++ₚ pSpec₂).MessageIdx`
    .sumMap (.refl _) MessageIdx.sumEquiv.toEmbedding

  hEq := fun i => by
    rcases h : V₂.embed i with j | j
    · rcases h' : V₁.embed j with k | k
      · have h1 := V₁.hEq j
        have h2 := V₂.hEq i
        simp [h, h'] at h1 h2 ⊢
        exact h2.trans h1
      · have h1 := V₁.hEq j
        have h2 := V₂.hEq i
        simp [h, h', MessageIdx.inl] at h1 h2 ⊢
        exact h2.trans h1
    · have := V₂.hEq i
      simp [h] at this ⊢
      simp [this, MessageIdx.inr]

@[simp]
lemma OracleVerifier.append_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      (OracleVerifier.append V₁ V₂).toVerifier =
        Verifier.append V₁.toVerifier V₂.toVerifier := sorry

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

@[simp]
lemma OracleReduction.append_toReduction
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      (OracleReduction.append R₁ R₂).toReduction =
        Reduction.append R₁.toReduction R₂.toReduction := by
  ext : 1 <;> simp [toReduction, OracleReduction.append, Reduction.append]

end OracleProtocol

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below are temporary until further development. -/

namespace Extractor

/-- The sequential composition of two straightline extractors.

TODO: state a monotone condition on the extractor, namely that if extraction succeeds on a given
query log, then it also succeeds on any extension of that query log -/
def Straightline.append (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) :
      Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) :=
  fun stmt₁ wit₃ transcript proveQueryLog verifyQueryLog => do
    let stmt₂ ← V₁.verify stmt₁ transcript.fst
    let wit₂ ← E₂ stmt₂ wit₃ transcript.snd proveQueryLog verifyQueryLog
    let wit₁ ← E₁ stmt₁ wit₂ transcript.fst proveQueryLog verifyQueryLog
    return wit₁

/-- The round-by-round extractor for the sequential composition of two (oracle) reductions -/
def RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂) :
      Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
        (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) where
  eqIn := by
    simp only [Function.comp_apply, Fin.cast_zero]
    exact E₁.eqIn
  extractMid := fun idx stmt₁ tr h => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast] at h ⊢
    by_cases hi : idx < m
    · simp [hi] at h
      have hiSucc : (idx : ℕ) < m + 1 := by omega
      simpa [hiSucc] using E₁.extractMid ⟨idx, hi⟩ stmt₁ (by simpa [hi] using tr.fst) h
    -- do casing
    sorry
  extractOut := fun stmt₁ tr wit₃ => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
    sorry

end Extractor

namespace Verifier

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- The sequential composition of two state functions. -/
def StateFunction.append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    -- Assume the first verifier is deterministic for now
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) :
      (V₁.append V₂).StateFunction init impl lang₁ lang₃ where
  toFun := fun roundIdx stmt₁ transcript =>
    if h : roundIdx.val ≤ m then
    -- If the round index falls in the first protocol, then we simply invokes the first state fn
      S₁ ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst)
    else
    -- If the round index falls in the second protocol, then we returns the conjunction of
    -- the first state fn on the first protocol's transcript, and the second state fn on the
    -- remaining transcript.
      S₁ ⟨m, by omega⟩ stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst) ∧
      S₂ ⟨roundIdx - m, by omega⟩ (verify stmt₁
        (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst))
        (by simpa [h] using transcript.snd)
  toFun_empty := by
    intro stmt
    split
    · constructor <;> intro h
      · have h' := (S₁.toFun_empty stmt).mp h
        convert h' using 2; exact funext fun i => i.elim0
      · exact (S₁.toFun_empty stmt).mpr (by convert h using 2; exact funext fun i => i.elim0)
    · exact absurd (Nat.zero_le m) ‹_›
  toFun_next := sorry
  toFun_full := sorry

end Verifier

section Execution

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

-- #print Prover.processRound

-- theorem append_processRound (roundIdx : Fin (m + n)) (stmt : Stmt₁) (wit : Wit₁)
--     (transcript : pSpec₁.FullTranscript) (proveQueryLog : Set (Stmt₁ × Wit₁))
--     (verifyQueryLog : Set (Stmt₂ × Wit₂)) :
--       (P₁.append P₂).processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog =
--         (P₁.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) ∧
--         (P₂.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) := placeholder

-- theorem append_runToRound

/-- The challenge type at index `i` of the left protocol coincides with the challenge type at the
  embedded index `ChallengeIdx.inl i` of the appended protocol. This is the response-type equality
  underlying the `SubSpec` inclusion of the left challenge oracle into the appended one. -/
private theorem range_challenge_append_inl (i : pSpec₁.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inl i, ()⟩
      = [pSpec₁.Challenge]ₒ.Range ⟨i, ()⟩ := by
  show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i
  simp [ChallengeIdx.inl, ProtocolSpec.append]

/-- The challenge type at index `i` of the right protocol coincides with the challenge type at the
  embedded index `ChallengeIdx.inr i` of the appended protocol. This is the response-type equality
  underlying the `SubSpec` inclusion of the right challenge oracle into the appended one. -/
private theorem range_challenge_append_inr (i : pSpec₂.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inr i, ()⟩
      = [pSpec₂.Challenge]ₒ.Range ⟨i, ()⟩ := by
  show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i
  simp [ChallengeIdx.inr, ProtocolSpec.append]

/-- The left protocol's challenge oracle is a sub-spec of the appended protocol's challenge oracle:
  a query to challenge round `i` of `pSpec₁` is forwarded to round `ChallengeIdx.inl i` of
  `pSpec₁ ++ₚ pSpec₂`, with responses transported back along `range_challenge_append_inl`. -/
instance : [(pSpec₁).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift := fun q => ⟨⟨ChallengeIdx.inl q.input.1, ()⟩,
    q.cont ∘ (fun r => (range_challenge_append_inl q.input.1) ▸ r)⟩
  onQuery := fun t => ⟨ChallengeIdx.inl t.1, ()⟩
  onResponse := fun t r => (range_challenge_append_inl t.1) ▸ r

/-- The right protocol's challenge oracle is a sub-spec of the appended protocol's challenge oracle:
  a query to challenge round `i` of `pSpec₂` is forwarded to round `ChallengeIdx.inr i` of
  `pSpec₁ ++ₚ pSpec₂`, with responses transported back along `range_challenge_append_inr`. -/
instance : [(pSpec₂).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift := fun q => ⟨⟨ChallengeIdx.inr q.input.1, ()⟩,
    q.cont ∘ (fun r => (range_challenge_append_inr q.input.1) ▸ r)⟩
  onQuery := fun t => ⟨ChallengeIdx.inr t.1, ()⟩
  onResponse := fun t r => (range_challenge_append_inr t.1) ▸ r

/-! ### Left-block run characterization support

The following support lemmas (proven by `Fin.induction` + the HEq transport toolkit) establish that running the appended prover `P₁.append P₂` up to a *left-half* round `j ≤ m` is heterogeneously the `liftM` (along the left challenge `SubSpec`) of running `P₁` up to round `j`.  The keystone is `append_runToRound_left`; its seam specialization `append_runToRound_seam` (target round `m`) is the entry point for `append_run`. -/

/-- Support lemma: PrvState of the appended prover matches `P₁`'s on the left half. -/
theorem append_PrvState_castLE (j : Fin (m + 1)) :
    (P₁.append P₂).PrvState (j.castLE (by omega)) = P₁.PrvState j := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (j.castLE (by omega)) : Fin (m + 1 + n)) = Fin.castAdd n j from by
        ext; simp]
  rw [Fin.append_left]

/-- Support lemma `append_Transcript_castLE`: the appended-protocol transcript type at a left-half
round equals `pSpec₁`'s transcript type. -/
theorem append_Transcript_castLE (j : Fin (m + 1)) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (j.castLE (by omega)) = pSpec₁.Transcript j := by
  show ((pSpec₁ ++ₚ pSpec₂).take _ _).FullTranscript = (pSpec₁.take _ _).FullTranscript
  unfold ProtocolSpec.FullTranscript ProtocolSpec.take
  apply pi_congr
  intro i
  have hi : (i : ℕ) < m := by
    have h1 := i.isLt
    have h2 := j.isLt
    simp only [Fin.val_castLE] at h1
    omega
  simp only [Fin.take_apply, Fin.vappend_eq_append]
  rw [show (Fin.castLE (by omega) i : Fin (m + n)) = Fin.castAdd n ⟨i, hi⟩ from by ext; simp]
  rw [Fin.append_left]
  congr 1

/-- Support lemma `append_input_heq`: the appended prover's `input` is heterogeneously equal to
`P₁`'s `input`. -/
theorem append_input_heq :
    HEq ((P₁.append P₂).input (stmt, wit)) (P₁.input (stmt, wit)) := by
  unfold Prover.append
  dsimp only
  simp only [id_eq]
  exact HEq.rfl

/-- Support lemma `prodMk_heq`: heterogeneous congruence for pairs whose component types vary. -/
theorem prodMk_heq {α α' β β' : Type _} {a : α} {a' : α'} {b : β} {b' : β'}
    (hα : α = α') (hβ : β = β') (ha : HEq a a') (hb : HEq b b') :
    HEq (Prod.mk a b) (Prod.mk a' b') := by
  subst hα hβ
  rw [eq_of_heq ha, eq_of_heq hb]

/-- Support lemma `pure_heq_pure`: heterogeneous congruence for `pure` in `OracleComp`, lifting a
HEq of values (over equal element types) to a HEq of the pure computations. -/
theorem pure_heq_pure {ι : Type} {spec : OracleSpec ι} {α α' : Type _} {a : α} {a' : α'}
    (hα : α = α') (ha : HEq a a') :
    HEq (pure a : OracleComp spec α) (pure a' : OracleComp spec α') := by
  subst hα
  rw [eq_of_heq ha]

/-- HEq congruence for `sendMessage`: equal message index and HEq state imply HEq results. -/
theorem sendMessage_heq_congr {P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {idx₁ idx₂ : pSpec₁.MessageIdx} (hidx : idx₁ = idx₂)
    {s₁ : P.PrvState idx₁.1.castSucc} {s₂ : P.PrvState idx₂.1.castSucc} (hs : HEq s₁ s₂) :
    HEq (P.sendMessage idx₁ s₁) (P.sendMessage idx₂ s₂) := by
  subst hidx
  rw [eq_of_heq hs]

/-- HEq congruence for `receiveChallenge`: equal challenge index and HEq state imply HEq results. -/
theorem receiveChallenge_heq_congr {P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {idx₁ idx₂ : pSpec₁.ChallengeIdx} (hidx : idx₁ = idx₂)
    {s₁ : P.PrvState idx₁.1.castSucc} {s₂ : P.PrvState idx₂.1.castSucc} (hs : HEq s₁ s₂) :
    HEq (P.receiveChallenge idx₁ s₁) (P.receiveChallenge idx₂ s₂) := by
  subst hidx
  rw [eq_of_heq hs]

/-- Split a HEq of pairs (over componentwise-equal types) into HEqs of the components. -/
theorem prod_heq_split {α α' β β' : Type _} (hα : α = α') (hβ : β = β')
    {a : α} {a' : α'} {b : β} {b' : β'} (h : HEq (Prod.mk a b) (Prod.mk a' b')) :
    HEq a a' ∧ HEq b b' := by
  subst hα hβ
  rw [heq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- HEq congruence for monadic `bind` in `OracleComp` where the element types may differ
propositionally.  If the bound computations are HEq (over equal element types) and the
continuations send HEq inputs to HEq outputs, the binds are HEq. -/
theorem bind_heq_congr {ι : Type} {spec : OracleSpec ι} {α α' β β' : Type _}
    (hα : α = α') (hβ : β = β')
    {ma : OracleComp spec α} {ma' : OracleComp spec α'}
    {f : α → OracleComp spec β} {f' : α' → OracleComp spec β'}
    (hma : HEq ma ma') (hf : ∀ (a : α) (a' : α'), HEq a a' → HEq (f a) (f' a')) :
    HEq (ma >>= f) (ma' >>= f') := by
  subst hα hβ
  rw [eq_of_heq hma]
  have : f = f' := funext fun a => eq_of_heq (hf a a HEq.rfl)
  rw [this]

/-- HEq congruence for `OracleComp.liftComp` (along the canonical query-level `MonadLiftT`): HEq
inputs (over equal element types) give HEq lifts.  Unlike `liftM_heq_congr`, `liftComp` depends only
on the *query-level* `MonadLiftT (OracleQuery spec) (OracleQuery superSpec)`, which is canonical, so
this avoids the OracleComp-level `MonadLiftT` instance diamond. -/
theorem liftComp_heq_congr {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] {α α' : Type}
    (hα : α = α') {ma : OracleComp spec α} {ma' : OracleComp spec α'} (hma : HEq ma ma') :
    HEq (OracleComp.liftComp ma superSpec) (OracleComp.liftComp ma' superSpec) := by
  subst hα
  rw [eq_of_heq hma]


/-- HEq congruence for `liftM` (along a fixed transitive `MonadLiftT` of `OracleComp`s): HEq inputs
(over equal element types) give HEq lifts. -/
theorem liftM_heq_congr {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [MonadLiftT (OracleComp spec) (OracleComp superSpec)] {α α' : Type}
    (hα : α = α') {ma : OracleComp spec α} {ma' : OracleComp spec α'} (hma : HEq ma ma') :
    HEq (liftM ma : OracleComp superSpec α) (liftM ma' : OracleComp superSpec α') := by
  subst hα
  rw [eq_of_heq hma]

/-- HEq congruence: `liftM` (the `OracleQuery → OracleComp` embedding over the SAME spec) of HEq
queries (over equal response types) gives HEq computations. -/
theorem liftM_query_heq {ιs : Type} {spec : OracleSpec ιs} {α α' : Type}
    (hα : α = α') {q : OracleQuery spec α} {q' : OracleQuery spec α'} (hq : HEq q q') :
    HEq (liftM q : OracleComp spec α) (liftM q' : OracleComp spec α') := by
  subst hα; rw [eq_of_heq hq]

/-- HEq of two oracle queries over the same spec whose inputs agree and whose response types are
propositionally equal, with HEq continuations. -/
theorem oracleQuery_heq {ιs : Type} {spec : OracleSpec ιs} {α α' : Type}
    {t t' : spec.Domain} (ht : t = t')
    {f : spec.Range t → α} {f' : spec.Range t' → α'} (hα : α = α') (hf : HEq f f') :
    HEq (OracleQuery.mk t f) (OracleQuery.mk t' f') := by
  subst ht; subst hα; rw [eq_of_heq hf]

/-- **OracleComp-level lift-coherence.**  Lifting `mx : OracleComp spec` first through an intermediate
spec `midSpec` and then to `superSpec` agrees, as a *function*, with lifting it directly to
`superSpec`, provided the two query-level `MonadLiftT`s cohere
(`OracleQuery.liftM_eq_liftM_liftM`, which is `rfl` for the canonical `+`/transitive instances).
Proved by induction on `mx`: the `query_bind` head reduces both sides to `q.cont <$> liftM (...)`
where the inner lifts coincide by `hquery`.

This is the bridge that defuses the `OracleComp`-level `MonadLiftT` instance diamond: the *transitive*
instance `instMonadLiftTOfMonadLift spec midSpec superSpec` lifts as
`liftComp (liftComp mx midSpec) superSpec`, while the *direct* instance lifts as
`liftComp mx superSpec`. -/
theorem liftComp_liftComp {ι₁ ι₂ ι₃ : Type} {spec : OracleSpec ι₁} {midSpec : OracleSpec ι₂}
    {superSpec : OracleSpec ι₃}
    [MonadLiftT (OracleQuery spec) (OracleQuery midSpec)]
    [MonadLiftT (OracleQuery midSpec) (OracleQuery superSpec)]
    [hsd : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (hquery : ∀ (t : spec.Domain),
      OracleComp.liftComp
          (liftM (spec.query t) : OracleComp midSpec (spec.Range t)) superSpec
        = (liftM (spec.query t) : OracleComp superSpec (spec.Range t)))
    {α : Type} (mx : OracleComp spec α) :
    OracleComp.liftComp (OracleComp.liftComp mx midSpec) superSpec
      = OracleComp.liftComp mx superSpec := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    -- Distribute both `liftComp`s through the outer bind; the tails match by `ih`.
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_bind, OracleComp.liftComp_bind]
    rw [show (fun x => OracleComp.liftComp (OracleComp.liftComp (k x) midSpec) superSpec)
          = (fun x => OracleComp.liftComp (k x) superSpec) from funext ih]
    -- Reduce the (single-query) head on both sides; the inner lift coheres by `hquery`.
    congr 1
    rw [OracleComp.liftComp_query, OracleComp.liftComp_map]
    simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [hquery t, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]


/-- `processRound` resolved at a message (`P_to_V`) round (mirror of the library's
`processRound_challenge`). -/
theorem processRound_message {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {N : ℕ} {pSpec : ProtocolSpec N}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin N)
    (hDir : pSpec.dir j = .P_to_V)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
      return ⟨transcript.concat msg, newState⟩) := by
  rw [Prover.processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  dsimp only
  split <;> rename_i hDir'
  · exact absurd (hDir.symm.trans hDir') (by decide)
  · rfl

/-- Generic HEq congruence for `Fin.snoc` over dependent codomain families.  If the lengths agree,
the codomain families are HEq, the tuples are HEq and the appended elements are HEq, the two snocs
are HEq. -/
theorem Fin_snoc_heq {N N' : ℕ} (hN : N = N')
    {β : Fin (N + 1) → Type _} {β' : Fin (N' + 1) → Type _} (hβ : HEq β β')
    {T : (j : Fin N) → β j.castSucc} {T' : (j : Fin N') → β' j.castSucc} (hT : HEq T T')
    {x : β (Fin.last N)} {x' : β' (Fin.last N')} (hx : HEq x x') :
    HEq (Fin.snoc T x) (Fin.snoc T' x') := by
  subst hN
  obtain rfl : β = β' := eq_of_heq hβ
  rw [eq_of_heq hT, eq_of_heq hx]

/-- Dependent function-application HEq congruence: HEq functions (over equal domain and HEq
codomain families) applied to HEq arguments give HEq results. -/
theorem heq_app {α α' : Type _} {β : α → Type _} {β' : α' → Type _}
    (hα : α = α') (hβ : HEq β β')
    {f : (a : α) → β a} {g : (a : α') → β' a} (hfg : HEq f g)
    {a : α} {a' : α'} (haa : HEq a a') :
    HEq (f a) (g a') := by
  subst hα
  obtain rfl : β = β' := eq_of_heq hβ
  rw [eq_of_heq hfg, eq_of_heq haa]

/-- The appended-protocol message type at a left round equals `pSpec₁`'s. -/
theorem append_Message_castLE (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V) (hDir₁ : pSpec₁.dir i = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩ = pSpec₁.Message ⟨i, hDir₁⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
  rw [Fin.vappend_eq_append,
    show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]

/-- HEq congruence for `Transcript.concat` across left-round transcripts of the appended and the
`pSpec₁` protocols.  `Transcript.concat = Fin.snoc`; compared as dependent functions on `Fin (·.succ)`
via `Function.hfunext`, splitting each index into the appended `msg` (last) or an interior entry
read from the transcript. -/
theorem concat_heq (i : Fin m)
    {t : (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc}
    {t' : pSpec₁.Transcript i.castSucc}
    {msg : (pSpec₁ ++ₚ pSpec₂).«Type» (i.castLE (by omega))} {msg' : pSpec₁.«Type» i}
    (ht : HEq t t') (hm : HEq msg msg') :
    HEq (Transcript.concat msg t) (Transcript.concat msg' t') := by
  unfold Transcript.concat
  have hlenC : (↑(i.castLE (show m ≤ m + n by omega)).castSucc : ℕ) = ↑i.castSucc := by simp
  -- The two `Fin.snoc`s differ only in (equal) length, (HEq) codomain family, tuple and element.
  refine Fin_snoc_heq hlenC ?_ ht ?_
  · -- codomain families agree: for `j < m`, the appended `«Type»` coincides with `pSpec₁`'s.
    have hsucc : (↑(i.castLE (show m ≤ m + n by omega)).succ : ℕ) = ↑i.succ := by simp
    apply Function.hfunext (by congr 1)
    intro b b' hbb
    have hbv : (b : ℕ) = (b' : ℕ) :=
      Fin.heq_ext_iff hsucc |>.mp hbb
    apply heq_of_eq
    show (pSpec₁ ++ₚ pSpec₂).«Type» _ = pSpec₁.«Type» _
    -- Both indices have value `< m` (or, for the last, `= m`), but only `< m` codomain entries
    -- are read; in all cases the appended `«Type»` at a left index equals `pSpec₁`'s.
    rcases lt_or_eq_of_le (show (↑b : ℕ) ≤ m by
        have := b.isLt; simp only [Fin.val_succ] at this; omega) with hbm | hbm
    · rw [show (Fin.castLE (by omega) b : Fin (m + n)) = Fin.castAdd n ⟨b, hbm⟩ from by ext; simp]
      show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castAdd n _) = _
      rw [Fin.vappend_eq_append, Fin.append_left]
      congr 1
      ext; simpa using hbv
    · -- `b = m` only when `b` is the last index of the snoc domain; the families still agree there
      -- because both sides evaluate the message type, equal by `append_Message_castLE`.
      exfalso
      have := b.isLt
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
  · -- the appended message ≍ `pSpec₁`'s message (`hm`).
    exact hm

/-- The appended protocol's direction at a left-half round matches `pSpec₁`'s. -/
theorem append_dir_castLE (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = pSpec₁.dir i := by
  show Fin.vappend pSpec₁.dir pSpec₂.dir (i.castLE (by omega)) = pSpec₁.dir i
  rw [Fin.vappend_eq_append,
    show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- State-type equality used to transport the appended prover's state into `P₁`'s state at the
`castSucc` of a left round. -/
theorem append_PrvState_castSucc (i : Fin m) :
    (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc = P₁.PrvState i.castSucc := by
  rw [show (i.castLE (by omega)).castSucc = (i.castSucc).castLE (by omega) from by ext; simp,
    append_PrvState_castLE i.castSucc]

/-- State-type equality at the `succ` of a left round. -/
theorem append_PrvState_succ (i : Fin m) :
    (P₁.append P₂).PrvState (i.castLE (by omega)).succ = P₁.PrvState i.succ := by
  rw [show (i.castLE (by omega)).succ = (i.succ).castLE (by omega) from by ext; simp,
    append_PrvState_castLE i.succ]

/-- Transcript-type equality at the `castSucc` of a left round. -/
theorem append_Transcript_castSucc (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc = pSpec₁.Transcript i.castSucc := by
  rw [show (i.castLE (by omega)).castSucc = (i.castSucc).castLE (by omega) from by ext; simp]
  exact append_Transcript_castLE i.castSucc

/-- Transcript-type equality at the `succ` of a left round. -/
theorem append_Transcript_succ (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ = pSpec₁.Transcript i.succ := by
  rw [show (i.castLE (by omega)).succ = (i.succ).castLE (by omega) from by ext; simp]
  exact append_Transcript_castLE i.succ

/-- **Left-round `sendMessage` reduction.**  The appended prover's `sendMessage` at a left round
`i < m` reduces (heterogeneously) to `P₁`'s `sendMessage`. -/
theorem append_sendMessage_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V)
    (hDir₁ : pSpec₁.dir i = .P_to_V)
    (state : (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ state)
        (P₁.sendMessage ⟨i, hDir₁⟩ (cast (append_PrvState_castSucc i) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hlt : (↑(i.castLE (show m ≤ m + n by omega)) : ℕ) < m := by simp
  rw [id_eq, dif_pos hlt]
  have hidxeq : (⟨⟨↑(i.castLE (show m ≤ m + n by omega)), hlt⟩, by exact hDir₁⟩
      : pSpec₁.MessageIdx) = ⟨i, hDir₁⟩ := by ext; simp
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact sendMessage_heq_congr hidxeq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Left-round `receiveChallenge` reduction.**  The appended prover's `receiveChallenge` at a
left round `i < m` reduces (heterogeneously) to `P₁`'s `receiveChallenge`. -/
theorem append_receiveChallenge_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P)
    (hDir₁ : pSpec₁.dir i = .V_to_P)
    (state : (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ state)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ (cast (append_PrvState_castSucc i) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hlt : (↑(i.castLE (show m ≤ m + n by omega)) : ℕ) < m := by simp
  rw [dif_pos hlt]
  have hidxeq : (⟨⟨↑(i.castLE (show m ≤ m + n by omega)), hlt⟩, by exact hDir₁⟩
      : pSpec₁.ChallengeIdx) = ⟨i, hDir₁⟩ := by ext; simp
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact receiveChallenge_heq_congr hidxeq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Left-round `getChallenge` reduction.**  The appended protocol's `getChallenge` at a left
challenge round `i < m` is heterogeneously equal to the `liftM` (along the left challenge `SubSpec`
`[pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`) of `pSpec₁`'s `getChallenge`.  The two
single queries coincide on the (value-equal) challenge index `i.castLE = ChallengeIdx.inl ⟨i,_⟩`; the
response types differ only by the propositional `range_challenge_append_inl` transport carried by the
SubSpec `onResponse`, so the queries are HEq. -/
theorem append_getChallenge_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P)
    (hDir₁ : pSpec₁.dir i = .V_to_P) :
    HEq ((pSpec₁ ++ₚ pSpec₂).getChallenge ⟨i.castLE (by omega), hDir⟩)
        (liftM (pSpec₁.getChallenge ⟨i, hDir₁⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) := by
  unfold ProtocolSpec.getChallenge
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]
  show HEq (liftM (OracleSpec.query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        ⟨⟨i.castLE (by omega), hDir⟩, ()⟩))
      (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩) :
        OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
  -- Make the OracleQuery-level lift explicit so both sides are `liftM (· : OracleQuery superSpec)`.
  rw [show (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
        = liftM (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩)
            : OracleQuery [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) from rfl]
  refine liftM_query_heq hChalEq ?_
  rw [OracleSpec.query_def]
  show HEq (OracleQuery.mk (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) ⟨⟨i.castLE (by omega), hDir⟩, ()⟩ id)
      (MonadLift.monadLift (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩))
  rw [SubSpec.liftM_eq_lift]
  refine oracleQuery_heq ?_ hChalEq ?_
  · -- inputs agree: `⟨i.castLE, hDir⟩ = onQuery ⟨i,hDir₁⟩ = ⟨ChallengeIdx.inl ⟨i,hDir₁⟩, ()⟩`.
    show (⟨⟨i.castLE (by omega), hDir⟩, ()⟩ : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Domain)
      = ⟨ChallengeIdx.inl ⟨i, hDir₁⟩, ()⟩
    congr 1
  · -- continuations: `id ≍ onResponse ⟨i,hDir₁⟩`, which is the `range_challenge_append_inl` transport.
    simp only [OracleQuery.cont_query, OracleQuery.input_query, Function.id_comp]
    have hdom : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨⟨i.castLE (by omega), hDir⟩, ()⟩
        = [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range
            ((inferInstance : [(pSpec₁).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).onQuery
              ⟨⟨i, hDir₁⟩, ()⟩) := by
      show (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
        = (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl ⟨i, hDir₁⟩)
      congr 1
    refine Function.hfunext hdom (fun a a' haa => ?_)
    refine haa.trans ?_
    -- `a' ≍ onResponse ⟨i,hDir₁⟩ a'`; `onResponse` is a type-level `▸` (= `cast`) transport.
    dsimp only [SubSpec.onResponse]
    refine HEq.symm ?_
    generalize_proofs h
    exact cast_heq h a'

/-- `processRound` resolved at a challenge (`V_to_P`) round (mirror of `processRound_message`). -/
theorem processRound_challenge' {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin N)
    (hDir : pSpec.dir j = .V_to_P)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let challenge ← pSpec.getChallenge ⟨j, hDir⟩
      letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
      return ⟨transcript.concat challenge, newState⟩) := by
  rw [Prover.processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  dsimp only
  split <;> rename_i hDir'
  · rfl
  · exact absurd (hDir.symm.trans hDir') (by decide)

/-- **Left-round `processRound` compatibility (message branch).**  Working scratch lemma to inspect
the message-round goal shape. -/
theorem append_processRound_left_message (i : Fin m) (hDir₁ : pSpec₁.dir i = .P_to_V)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc
        × (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × P₁.PrvState i.castSucc))
    (hcur : HEq curA (liftM cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq ((P₁.append P₂).processRound (i.castLE (by omega)) curA)
      (liftM (P₁.processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_message (P₁.append P₂) (i.castLE (by omega)) hDir curA,
    processRound_message P₁ i hDir₁ cur₁]
  -- Push the outer `liftM` through the RHS `do`-block (keep binds explicit, no `map` rewrite).
  simp only [liftM_bind, liftM_pure]
  -- Outer bind over the (HEq) input results.
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, append_PrvState_castSucc i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (append_PrvState_castSucc i) hr
  dsimp only
  -- Collapse the double `liftM` on the RHS (composition of lifts oSpec → appended spec).
  have hcollapse : (liftM (liftM (P₁.sendMessage ⟨i, hDir₁⟩ s') :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = liftM (P₁.sendMessage ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by
    rfl
  rw [hcollapse]
  -- Normalize the RHS continuation `liftM (pure _) = pure _`.
  simp only [liftM_pure]
  -- Bind over the (HEq) `sendMessage` computations, then `pure (concat, newState)`.
  apply bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    (β := (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ
      × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
    (β' := pSpec₁.Transcript i.succ × P₁.PrvState i.succ)
    (α := (pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩
      × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
    (α' := pSpec₁.Message ⟨i, hDir₁⟩ × P₁.PrvState i.succ)
    (by rw [append_Message_castLE i hDir hDir₁, append_PrvState_succ i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i])
  · -- `sendMessage` HEq (lifted): both sides are oSpec→S lifts (direct vs transitive, defeq) of
    -- HEq-equal `sendMessage` computations (`append_sendMessage_left` + `s ≍ s'`).
    have hαeq : ((pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩
          × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
        = (pSpec₁.Message ⟨i, hDir₁⟩ × P₁.PrvState i.succ) := by
      rw [append_Message_castLE i hDir hDir₁, append_PrvState_succ i]
    have hbase : HEq ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ s)
        (P₁.sendMessage ⟨i, hDir₁⟩ s') :=
      (append_sendMessage_left i hDir hDir₁ s).trans
        (sendMessage_heq_congr rfl ((cast_heq _ _).trans hs))
    -- Lift the base `sendMessage` HEq (`hbase`) through the lift to `S`.
    --
    -- The goal's two `liftM`s both lift `OracleComp oSpec → S`, but via DIFFERENT `MonadLiftT`
    -- instances: the goal's RHS (`liftM_bind`-pushed `P₁.processRound` side) uses the *transitive*
    -- instance `instMonadLiftTOfMonadLift oSpec (oSpec + [pSpec₁.Challenge]ₒ) S`, whereas the
    -- appended-prover side and `liftM_heq_congr` use the *direct* instance
    -- `instMonadLiftTOfMonadLift oSpec oSpec S`.  These two `monadLift`s are EQUAL as functions
    -- (`liftComp_liftComp`: the transitive lift `liftComp (liftComp · mid) super` equals the direct
    -- `liftComp · super`, the single-query coherence being `rfl` for the canonical `+` instances),
    -- but they are NOT defeq at the `OracleComp` structure level.  We bridge them via
    -- `liftComp_liftComp` and then apply `liftM_heq_congr` on the (common) direct instance.
    -- The goal is `liftM (appended.sendMessage ..) ≍ liftM (P₁.sendMessage ..)`, where the LHS
    -- lifts `OracleComp oSpec → S` via the DIRECT instance and the RHS via the TRANSITIVE instance
    -- `oSpec → oSpec+[pSpec₁.Challenge]ₒ → S`.  Definitionally the transitive RHS unfolds to the
    -- nested `liftComp (liftComp (P₁.sendMessage ..) (oSpec+[pSpec₁.Challenge]ₒ)) S`; expose that via
    -- `show`, collapse it to the direct `liftComp (P₁.sendMessage ..) S` via `liftComp_liftComp`,
    -- and likewise expose the LHS as the direct `liftComp (appended.sendMessage ..) S`.
    show HEq (OracleComp.liftComp ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ s)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (OracleComp.liftComp
          (OracleComp.liftComp (P₁.sendMessage ⟨i, hDir₁⟩ s') (oSpec + [pSpec₁.Challenge]ₒ))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
    rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
      (P₁.sendMessage ⟨i, hDir₁⟩ s')]
    -- Both sides are now `liftComp · (oSpec+[(pSpec₁++pSpec₂).Challenge]ₒ)` on the (HEq) base
    -- `sendMessage` computations; close via the query-level `liftComp` HEq congruence.
    exact liftComp_heq_congr (spec := oSpec)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hbase
  · rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
    refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_
    obtain ⟨hm, hns⟩ :=
      prod_heq_split (append_Message_castLE i hDir hDir₁) (append_PrvState_succ i) hmsg
    refine prodMk_heq (append_Transcript_succ i) (append_PrvState_succ i) ?_ hns
    -- `Transcript.concat msg t ≍ Transcript.concat msg' t'`
    exact concat_heq i ht hm

/-- **Left-round `processRound` compatibility (challenge branch).**  The `V_to_P` analogue of
`append_processRound_left_message`: at a left challenge round `i < m`, the appended prover's
`processRound` (heterogeneously) equals the `liftM` of `P₁`'s, assuming the run-up-to inputs are
HEq.  Mirrors the message branch, with `getChallenge` (`append_getChallenge_left`) and
`receiveChallenge` (`append_receiveChallenge_left`) in place of `sendMessage`, plus the extra
function-application of the `receiveChallenge` result to the sampled challenge. -/
theorem append_processRound_left_challenge (i : Fin m) (hDir₁ : pSpec₁.dir i = .V_to_P)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc
        × (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × P₁.PrvState i.castSucc))
    (hcur : HEq curA (liftM cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq ((P₁.append P₂).processRound (i.castLE (by omega)) curA)
      (liftM (P₁.processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_challenge' (P₁.append P₂) (i.castLE (by omega)) hDir curA,
    processRound_challenge' P₁ i hDir₁ cur₁]
  simp only [liftM_bind, liftM_pure]
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, append_PrvState_castSucc i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (append_PrvState_castSucc i) hr
  dsimp only
  -- Collapse the RHS double-lifts (oSpec'-level transitive ⇒ direct) of the challenge-oracle
  -- computations.  Here both `getChallenge` and `receiveChallenge` already live in the appended
  -- challenge oracle on the RHS after the inner `liftM`; the outer `liftM` to the full spec is the
  -- challenge `SubSpec` lift, common to both sides.
  -- Challenge value type equality.
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]
  -- Bind over the (HEq) `getChallenge` computations.
  refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    hChalEq
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_ ?_
  · -- `getChallenge` HEq, lifted to the full spec.  Both sides lift the appended challenge oracle
    -- `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` into the full spec via the same `+`-right `SubSpec`; the
    -- underlying `getChallenge` HEq is `append_getChallenge_left`.
    exact liftM_heq_congr (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq
      (append_getChallenge_left i hDir hDir₁)
  · -- continuation: bind over `receiveChallenge`, then `pure (concat, f challenge)`.
    rintro chalA chal₁ hchal
    -- Collapse the RHS double-lift of `receiveChallenge` (transitive oSpec→S ⇒ direct).
    have hcollapse : (liftM (liftM (P₁.receiveChallenge ⟨i, hDir₁⟩ s') :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM (P₁.receiveChallenge ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by rfl
    rw [hcollapse]
    -- `receiveChallenge` returns `Challenge → State`; the bind result `f` is applied to the
    -- challenge.  HEq of the receiveChallenge computations:
    have hrecvBase : HEq ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ s)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ s') :=
      (append_receiveChallenge_left i hDir hDir₁ s).trans
        (receiveChallenge_heq_congr rfl ((cast_heq _ _).trans hs))
    refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (α := (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
        → (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
      (α' := pSpec₁.Challenge ⟨i, hDir₁⟩ → P₁.PrvState i.succ)
      (β := (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ
        × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
      (β' := pSpec₁.Transcript i.succ × P₁.PrvState i.succ)
      (by rw [hChalEq, append_PrvState_succ i])
      (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_ ?_
    · -- lifted `receiveChallenge` HEq, transitive RHS ⇒ direct via `liftComp_liftComp`.
      have hαeq : ((pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
            → (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
          = (pSpec₁.Challenge ⟨i, hDir₁⟩ → P₁.PrvState i.succ) := by
        rw [hChalEq, append_PrvState_succ i]
      show HEq (OracleComp.liftComp ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ s)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
          (OracleComp.liftComp
            (OracleComp.liftComp (P₁.receiveChallenge ⟨i, hDir₁⟩ s') (oSpec + [pSpec₁.Challenge]ₒ))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ s')]
      exact liftComp_heq_congr (spec := oSpec)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hrecvBase
    · -- `pure (concat chal t, f chal)`: concat + function-application HEq.
      rintro fA f₁ hf
      refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_
      refine prodMk_heq (append_Transcript_succ i) (append_PrvState_succ i) ?_ ?_
      · -- `concat chalA t ≍ concat chal₁ t'`
        exact concat_heq i ht hchal
      · -- `fA chalA ≍ f₁ chal₁`: application of HEq (non-dependent) functions to HEq arguments.
        refine heq_app hChalEq ?_ hf hchal
        -- codomain families are the constant `fun _ => PrvState succ`; HEq via the state equality.
        rw [hChalEq, append_PrvState_succ i]

/-- **The corrected well-founded `append_runToRound_left`.**  Running the appended prover up to a
left-half round `j ≤ m` (embedded as `j.castLE` into `Fin (m + n + 1)`) is heterogeneously equal to
the `liftM` (along the left challenge `SubSpec`) of running `P₁` up to round `j`. -/
theorem append_runToRound_left (j : Fin (m + 1)) :
    HEq ((P₁.append P₂).runToRound (j.castLE (by omega)) stmt wit)
      (liftM (P₁.runToRound j stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  induction j using Fin.induction with
  | zero =>
    rw [show ((0 : Fin (m + 1)).castLE (by omega) : Fin (m + n + 1)) = 0 from by ext; simp]
    rw [Prover.runToRound_zero_of_prover_first, Prover.runToRound_zero_of_prover_first]
    rw [liftM_pure]
    have hT : Transcript 0 (pSpec₁ ++ₚ pSpec₂) = Transcript 0 pSpec₁ := by
      unfold ProtocolSpec.Transcript ProtocolSpec.FullTranscript
      apply pi_congr; intro i; exact absurd i.isLt (by simp)
    have hS : (P₁.append P₂).PrvState 0 = P₁.PrvState 0 := append_PrvState_castLE 0
    apply pure_heq_pure
    · rw [hT, hS]
    · apply prodMk_heq
      · exact hT
      · exact hS
      · exact Subsingleton.helim hT _ _
      · exact append_input_heq
  | succ i ih =>
    -- Express the left-embedded successor index as a successor in `Fin (m + n)`.
    have hidx : ((i.succ).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (i.castLE (show m ≤ m + n by omega)).succ := by ext; simp
    rw [hidx, Prover.runToRound_succ]
    rw [Prover.runToRound_succ]
    -- Goal: `processRound (i.castLE) appended (runToRound (i.castLE).castSucc appended)
    --        ≍ liftM (processRound i P₁ (runToRound i.castSucc P₁))`.
    -- `ih` carries the run up to the seam-predecessor round: `runToRound (i.castSucc.castLE) appended
    --   ≍ liftM (runToRound i.castSucc P₁)`.  Normalize its index to `(i.castLE).castSucc`.
    have hcur : HEq ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (liftM (P₁.runToRound i.castSucc stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
      have hcastSucc : (i.castSucc.castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
          = (i.castLE (show m ≤ m + n by omega)).castSucc := by ext; simp
      rw [← hcastSucc]; exact ih
    -- Case-split on the direction of the left round `i`.
    cases hd : pSpec₁.dir i with
    | V_to_P => ?_
    | P_to_V => ?_
    · -- `V_to_P` (challenge round): close via the proven challenge-branch lemma.
      exact append_processRound_left_challenge i hd
        ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (P₁.runToRound i.castSucc stmt wit) hcur
    · -- `P_to_V` (message round): close directly via the proven message-branch lemma.
      exact append_processRound_left_message i hd
        ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (P₁.runToRound i.castSucc stmt wit) hcur

/-- **Seam specialization of `append_runToRound_left`.**  Running the appended prover up to the
*seam* round `m` (the last round of `pSpec₁`, embedded as `(Fin.last m).castLE` into the appended
protocol) is heterogeneously equal to the `liftM` of running `P₁` to its last round — i.e. the full
honest run of `P₁`'s message phase.  This is the entry point for assembling `Prover.append_run`:
after the seam, the continuation runs `P₂` (rounds `m+1 .. m+n`) starting from `P₁.output`-fed
`P₂.input`. -/
theorem append_runToRound_seam :
    HEq ((P₁.append P₂).runToRound ((Fin.last m).castLE (by omega)) stmt wit)
      (liftM (P₁.runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :=
  append_runToRound_left (Fin.last m)

/-! ### Right-block run characterization support (in progress)

The right block mirrors the left, but the appended prover's right half is indexed through
`Fin.natAdd (m + 1)` (interior rounds `m+1 .. m+n`) and—crucially—the **seam round** `m`
(`Prover.append`'s `i = m` branch) is *not* a uniform right round: it threads `P₁.output >>= P₂.input`
before `P₂`'s round-`0` step.  We record here the proven right-half state transport; the remaining
right reductions and the seam-merge lemma are the documented obstruction of `append_run`. -/

/-- PrvState of the appended prover at a *right interior* round `m + 1 + k` (`k : Fin n`) equals
`P₂`'s state at round `k + 1`.  Mirror of `append_PrvState_castLE` via `Fin.append_right`/`Fin.tail`
(here `Fin.tail P₂.PrvState ∘ Fin.cast` reduces to `P₂.PrvState ∘ Fin.succ` on the right). -/
theorem append_PrvState_natAdd_succ (k : Fin n) :
    (P₁.append P₂).PrvState (Fin.natAdd (m + 1) k |>.cast (by omega)) = P₂.PrvState k.succ := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (Fin.natAdd (m + 1) k |>.cast (by omega)) : Fin (m + 1 + n))
        = Fin.natAdd (m + 1) k from by ext; simp]
  rw [Fin.append_right]
  rfl

/-- The appended protocol's direction at a *right interior* round `Fin.natAdd m k` (`k : Fin n`)
matches `pSpec₂`'s direction at `k`.  Mirror of `append_dir_castLE` via `Fin.append_right`. -/
theorem append_dir_natAdd (k : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = pSpec₂.dir k := by
  show Fin.vappend pSpec₁.dir pSpec₂.dir (Fin.natAdd m k) = pSpec₂.dir k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-protocol message type at a right interior round equals `pSpec₂`'s. -/
theorem append_Message_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V) (hDir₂ : pSpec₂.dir k = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.natAdd m k, hDir⟩ = pSpec₂.Message ⟨k, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-protocol challenge type at a right interior round equals `pSpec₂`'s. -/
theorem append_Challenge_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P) (hDir₂ : pSpec₂.dir k = .V_to_P) :
    (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩ = pSpec₂.Challenge ⟨k, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-! ### Seam-round reductions

The seam round `m` is the genuinely-new monadic-interleaving step of `Prover.append` (the `i = m`
branch): it threads `P₁.output state >>= P₂.input` before `P₂`'s round-`0` step.  We characterize the
two seam shapes (`sendMessage`/`receiveChallenge`) heterogeneously in terms of `P₁.output` /
`P₂.input` / `P₂`'s round-0 step.  These feed the seam-round `processRound` in the right-block run. -/

/-- State-type equality: the appended prover's state at the seam-round `castSucc` index `m`
(the state going INTO the seam round) equals `P₁`'s last state. -/
theorem append_PrvState_seam_castSucc (hn : 0 < n) :
    (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc = P₁.PrvState (Fin.last m) := by
  have := append_PrvState_castLE (P₁ := P₁) (P₂ := P₂) (Fin.last m)
  rw [show ((Fin.last m).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  exact this

/-- **Seam-round `sendMessage` reduction.**  At the seam round `m` (the `i = m` branch of
`Prover.append.sendMessage`), the appended prover's `sendMessage` is heterogeneously equal to
`P₁.output state >>= fun ctx => P₂.sendMessage ⟨0,_⟩ (P₂.input ctx)`. -/
theorem append_sendMessage_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (state : (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨m, by omega⟩, hDir⟩ state)
      (do
        let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) state)
        P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) : OracleComp oSpec _) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) < m := by simp
  rw [id_eq, dif_neg hnlt]
  have heqm : (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) = m := by simp
  rw [dif_pos heqm]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  -- Both sides are `P₁.output (·) >>= fun ctx => P₂.sendMessage ⟨0,_⟩ (P₂.input ctx)` over oSpec;
  -- the seam's internally-cast `state` and our `cast _ state` target the same `P₁.PrvState (last m)`.
  refine bind_heq_congr (α := Stmt₂ × Wit₂) (α' := Stmt₂ × Wit₂) rfl
    (by congr 1) ?_ ?_
  · apply heq_of_eq; congr 1
  · rintro c c' rfl; rfl

/-- **Seam-round `receiveChallenge` reduction.**  The `V_to_P` analogue of `append_sendMessage_seam`:
at the seam round `m`, the appended prover's `receiveChallenge` is heterogeneously equal to
`P₁.output state >>= fun ctx => P₂.receiveChallenge ⟨0,_⟩ (P₂.input ctx)`. -/
theorem append_receiveChallenge_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .V_to_P)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .V_to_P)
    (state : (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨⟨m, by omega⟩, hDir⟩ state)
      (do
        let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) state)
        P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) : OracleComp oSpec _) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) < m := by simp
  rw [dif_neg hnlt]
  have heqm : (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) = m := by simp
  rw [dif_pos heqm]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  refine bind_heq_congr (α := Stmt₂ × Wit₂) (α' := Stmt₂ × Wit₂) rfl
    (by congr 1) ?_ ?_
  · apply heq_of_eq; congr 1
  · rintro c c' rfl; rfl

/-! ### Right interior-round reductions

The right *interior* rounds `m+1 .. m+n-1` are the `i > m` branch of `Prover.append`: uniform `P₂`
rounds.  These mirror the left-block reductions (`append_sendMessage_left` etc.), now indexed through
`Fin.natAdd m k` (`k : Fin n`, `k > 0`); the appended step reduces heterogeneously to `P₂`'s step at
round `k`, with the state transported by `append_PrvState_natAdd_castSucc`. -/

/-- State-type equality: the appended prover's state at the interior right round `Fin.natAdd m k`'s
`castSucc` (state going INTO interior round `k`, where `k > 0`) equals `P₂`'s state at `k`. -/
theorem append_PrvState_natAdd_castSucc (k : Fin n) (hk : 0 < (k : ℕ)) :
    (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc = P₂.PrvState k.castSucc := by
  have hpred : (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ = k.castSucc := by ext; simp; omega
  have := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) ⟨(k : ℕ) - 1, by omega⟩
  rw [hpred] at this
  rw [show ((Fin.natAdd m k).castSucc : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) from by
        ext; simp; omega]
  exact this

/-- State-type equality at the interior right round `succ` index (state AFTER interior round `k`,
`k > 0`).  Equals `P₂.PrvState k.succ`. -/
theorem append_PrvState_natAdd_interior_succ (k : Fin n) (hk : 0 < (k : ℕ)) :
    (P₁.append P₂).PrvState (Fin.natAdd m k).succ = P₂.PrvState k.succ := by
  have := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) k
  rw [show ((Fin.natAdd m k).succ : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) k).cast (by omega) from by ext; simp; omega]
  exact this

/-- **Right interior-round `sendMessage` reduction.**  At an interior right round `Fin.natAdd m k`
(`k : Fin n`, `k > 0`, the `i > m` branch of `Prover.append.sendMessage`), the appended prover's
`sendMessage` is heterogeneously equal to `P₂`'s `sendMessage` at round `k`. -/
theorem append_sendMessage_natAdd (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (state : (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨Fin.natAdd m k, hDir⟩ state)
      (P₂.sendMessage ⟨k, hDir₂⟩ (cast (append_PrvState_natAdd_castSucc k hk) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(Fin.natAdd m k) : ℕ) < m := by simp
  rw [id_eq, dif_neg hnlt]
  have hne : (↑(Fin.natAdd m k) : ℕ) ≠ m := by simp; omega
  rw [dif_neg hne]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  have hkeq : (⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ : Fin n) = k := by ext; simp
  have hdir₂' : pSpec₂.dir ⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ = .P_to_V := by
    rw [hkeq]; exact hDir₂
  have hidx : (⟨⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩, hdir₂'⟩ : pSpec₂.MessageIdx)
      = ⟨k, hDir₂⟩ := by ext; simp
  refine sendMessage_heq_congr hidx ?_
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Right interior-round `receiveChallenge` reduction.**  Mirror of `append_sendMessage_natAdd`
for the `V_to_P` direction. -/
theorem append_receiveChallenge_natAdd (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (state : (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨Fin.natAdd m k, hDir⟩ state)
      (P₂.receiveChallenge ⟨k, hDir₂⟩ (cast (append_PrvState_natAdd_castSucc k hk) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(Fin.natAdd m k) : ℕ) < m := by simp
  rw [dif_neg hnlt]
  have hne : (↑(Fin.natAdd m k) : ℕ) ≠ m := by simp; omega
  rw [dif_neg hne]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  have hkeq : (⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ : Fin n) = k := by ext; simp
  have hdir₂' : pSpec₂.dir ⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ = .V_to_P := by
    rw [hkeq]; exact hDir₂
  have hidx : (⟨⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩, hdir₂'⟩ : pSpec₂.ChallengeIdx)
      = ⟨k, hDir₂⟩ := by ext; simp
  refine receiveChallenge_heq_congr hidx ?_
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.
-/
theorem append_run (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) := by
  -- **WIP — left block DONE; ALL per-round seam+interior reductions now PROVEN; run-assembly
  -- (transcript-prefix family + right-block run induction + output) remains.**
  --
  -- Strategy: expose `run` as `runToRound (Fin.last (m+n))` ≫ `output` (`run_eq_runToRound_last`),
  -- then factor the full run at the seam `k = ⟨m,_⟩` via the keystone
  -- `runToRound_eq_bind_continueFromTo`:
  --   (P₁.append P₂).runToRound (last (m+n)) stmt wit
  --     = (P₁.append P₂).runToRound ⟨m,_⟩ stmt wit
  --         >>= continueFromTo (P₁.append P₂) stmt wit ⟨m,_⟩ (last (m+n)).
  -- The first factor = `append_runToRound_seam` (PROVEN): ≍ `liftM (P₁.runToRound (last m))`.
  --
  -- PROVEN per-round handles (all #print-axioms clean), ready to feed the run induction:
  --   • SEAM round `m` (`i = m` branch): `append_sendMessage_seam` / `append_receiveChallenge_seam`
  --     reduce the seam step to `P₁.output (cast _ state) >>= fun ctx => P₂.{send,recv} ⟨0,_⟩
  --     (P₂.input ctx)` — exactly the `liftM (P₁.run) >>= fun ⟨_,s₂,w₂⟩ => liftM (P₂.run s₂ w₂)`
  --     boundary (state transport `append_PrvState_seam_castSucc`, dir `append_dir_natAdd ⟨0,_⟩`).
  --   • RIGHT interior rounds `m+1..m+n-1` (`i > m` branch): `append_sendMessage_natAdd` /
  --     `append_receiveChallenge_natAdd` reduce to `P₂`'s step at round `k`; state transports
  --     `append_PrvState_natAdd_castSucc` / `_interior_succ`; types `append_{dir,Message,Challenge}_natAdd`.
  --
  -- REMAINING OBSTRUCTION (the genuinely new content, blocking assembly):
  --   (T) Transcript-PREFIX family.  Unlike the left block (where the appended transcript truncated
  --       to `j ≤ m` IS `pSpec₁.Transcript j`), the RIGHT block carries the full `transcript₁`
  --       prefix: `(pSpec₁++pSpec₂).Transcript (natAdd m k).castSucc ≅ transcript₁ ⊕ pSpec₂.Transcript
  --       k.castSucc`.  Need `Fin.happend`/`Fin.snoc` interaction lemmas — a prefix analogue of the
  --       proven `concat_heq` — proving `Transcript.concat msg (transcript₁ ++ₜ tr₂)
  --       ≍ transcript₁ ++ₜ (Transcript.concat msg tr₂)` (i.e. `Fin.happend` commutes with the
  --       seam-side `Fin.snoc`), plus the seam boundary `transcript₁ ++ₜ (default : Transcript 0)
  --       ≍ transcript₁`.
  --   (R) Right-block run induction.  By `Fin.induction` on `k : Fin (n+1)`, with the prefix `(T)`
  --       threaded: `continueFromTo (P₁++P₂) stmt wit ⟨m,_⟩ (natAdd m k) rSeam`
  --       ≍ (do `⟨tr₂,s₂'⟩ ← P₂.runToRound k (P₂.input (←P₁.output …)) …; pure (transcript₁ ++ₜ tr₂, …)`)
  --       — base `k=0` is `continueFromTo_self`; succ steps peel via `continueFromTo_succ_of_ne` +
  --       `processRound_{message,challenge}` and the PROVEN per-round seam/interior reductions above.
  --   (O) `output` assembly: combine via `++ₜ` (`append_fst`/`append_snd`) + `P₂.output` tail
  --       (`output` branch of `Prover.append`, incl. `n = 0` degenerate seam where the right block is
  --       empty and `P₁.output >>= P₂.input >>= P₂.output` collapses).
  --
  -- All round-local reductions are discharged; the residue is the transcript-prefix dependent-tuple
  -- bookkeeping (T) + its induction (R) + output (O).  This is a `HEq`/`Fin.happend` engineering
  -- task on top of the now-complete reduction layer, with NO remaining monadic-interleaving gap.
  sorry

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Prover

namespace Verifier

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {stmt : Stmt₁}

/-- Running the sequential composition of two verifiers on a transcript of the combined protocol
  is equivalent to running the first verifier on the first part of the transcript, and the second
  verifier on the second part of the transcript, and returning the final statement. -/
theorem append_run (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
      (V₁.append V₂).run stmt tr =
        (do
          let stmt₂ ← V₁.run stmt tr.fst
          let stmt₃ ← V₂.run stmt₂ tr.snd
          return stmt₃) := rfl

end Verifier

namespace Reduction

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/- Unfortunately this is not true due to sequencing: `(R₁.append R₂).run` runs the two provers
first, then the two verifiers, whereas `R₁.run` and then `R₂.run` runs the first prover and
verifier, then the second prover and verifier.

We need justification to be able to swap the first verifier with the second prover, which would be
true if we interpret / maps this oracle computation (a priori a term of the free monad) into a
commutative monad (such as `Id`, i.e. all oracle queries are answered deterministically, `PMF`, i.e.
all oracle queries are answered probabilistically, `Option`, `ReaderT ρ`, `Set`, `WriterT` into a
commutative monoid, etc.). -/

-- TODO: prove this after VCVio refactor
-- theorem append_run_interp {m : Type → Type} [Monad m] [m.IsCommutative]
--     {interp : OracleImpl oSpec m} : ((R₁.append R₂).run stmt wit).runM interp =
--         (do
--           let ⟨ctx₁, stmt₂, transcript₁⟩ ← liftM (R₁.run stmt wit)
--           let ⟨ctx₂, stmt₃, transcript₂⟩ ← liftM (R₂.run stmt₂ ctx₁.2)
--           return ⟨ctx₂, stmt₃, transcript₁ ++ₜ transcript₂⟩).runM interp := by
--   unfold run append
--   simp [Prover.append_run, Verifier.append_run]
--   placeholder

end Reduction

end Execution

section Security

open scoped NNReal

section Protocol

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-
TODO: when do these theorems hold? The answer may be that when oracle queries are answered according
to a _commutative_ monad, which are then interpreted into a probability distribution.

Unfortunately, this means that `StateT` is out; this works for `ReaderT` and `WriterT` into a
commutative monoid. If we still want composition to work for `StateT`, then we need to have extra
conditions (what are they?)
-/

namespace Reduction

/-- Sequential composition preserves completeness

  Namely, two reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for `R₁` and
  `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
  `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies
  completeness with respect to `rel₁` and `rel₃`.

  The completeness error of the appended reduction is the sum of the individual errors
  (`completenessError₁ + completenessError₂`). -/
theorem append_completeness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness at h₁ h₂ ⊢
  intro stmtIn witIn hRelIn
  have h₁' := h₁ stmtIn witIn hRelIn
  clear h₁
  unfold Reduction.append Reduction.run
  simp [Prover.append_run, Verifier.append_run]
  sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem append_perfectCompleteness (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.append_completeness R₁ R₂ h₁ h₂
  simp only [add_zero]

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

-- Synthesization issues...
-- So maybe no synthesization but simp is fine? Maybe not...
-- instance [R₁.IsComplete rel₁ rel₂] [R₂.IsComplete rel₂ rel₃] :
--     (R₁.append R₂).IsComplete rel₁ rel₃ := by placeholder

end Reduction

namespace Verifier

/-- If two verifiers satisfy soundness with compatible languages and respective soundness errors,
    then their sequential composition also satisfies soundness.
    The soundness error of the appended verifier is the sum of the individual errors. -/
theorem append_soundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  sorry

/-- If two verifiers satisfy knowledge soundness with compatible relations and respective knowledge
    errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl
        rel₁ rel₃ (knowledgeError₁ + knowledgeError₂) := by
  sorry

/-- If two verifiers satisfy round-by-round soundness with compatible languages and respective RBR
    soundness errors, then their sequential composition also satisfies round-by-round soundness.
    The RBR soundness error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrSoundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

/-- If two verifiers satisfy round-by-round knowledge soundness with compatible relations and
    respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

end Verifier

end Protocol

section OracleProtocol

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

namespace OracleReduction

/-- Sequential composition preserves completeness

  Namely, two oracle reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for
  `R₁` and `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
  `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies completeness
  with respect to `rel₁` and `rel₃`.

  The completeness error of the appended reduction is the sum of the individual errors
  (`completenessError₁ + completenessError₂`). -/
theorem append_completeness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness
  convert Reduction.append_completeness R₁.toReduction R₂.toReduction h₁ h₂
  simp only [append_toReduction]

/-- If two oracle reductions satisfy perfect completeness with compatible relations, then their
  sequential composition also satisfies perfect completeness. -/
theorem append_perfectCompleteness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  unfold perfectCompleteness Reduction.perfectCompleteness
  convert OracleReduction.append_completeness R₁ R₂ h₁ h₂
  simp

end OracleReduction

namespace OracleVerifier

variable {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))} {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- If two oracle verifiers satisfy soundness with compatible languages and respective soundness
    errors, then their sequential composition also satisfies soundness.
    The soundness error of the appended verifier is the sum of the individual errors. -/
theorem append_soundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold soundness
  convert Verifier.append_soundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy knowledge soundness with compatible relations and respective
    knowledge errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃
        (knowledgeError₁ + knowledgeError₂) := by
  unfold knowledgeSoundness
  convert Verifier.append_knowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy round-by-round soundness with compatible languages and
  respective RBR soundness errors, then their sequential composition also satisfies
  round-by-round soundness. The RBR soundness error of the appended verifier extends the
  individual errors appropriately. -/
theorem append_rbrSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrSoundness
  convert Verifier.append_rbrSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy round-by-round knowledge soundness with compatible relations
    and respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrKnowledgeSoundness
  convert Verifier.append_rbrKnowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

end OracleVerifier

end OracleProtocol

end Security
