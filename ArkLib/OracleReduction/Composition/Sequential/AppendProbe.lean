/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # PROBE: development scratch for `Prover.append_run`

  This is a leaf probe file (not imported anywhere) used to develop the support lemmas and the
  corrected `append_runToRound_left` statement before moving them into `Append.lean`.
-/

open OracleComp OracleSpec SubSpec ProtocolSpec

universe u v

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

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
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V)
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
    exact concat_heq i hDir ht hm

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
    sorry

end Prover
