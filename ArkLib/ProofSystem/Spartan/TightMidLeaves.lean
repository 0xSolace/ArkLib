/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.MidChainWithTarget
import ArkLib.ProofSystem.Spartan.TightRLCKernel
import ArkLib.ProofSystem.Spartan.SumcheckPhaseRbr

/-!
# The tight mid-chain rbr knowledge-soundness leaves (issue #329, X-lane)

The heart of the #329 campaign: the relation chain through the carried middle rounds whose
`linearCombination` flip probability is `1/|R|` — Spartan's Lemma 5.1 bound, replacing the
proven-forced `err₅ = 1` of the target-dropping chain.

## The chain

With `e₁` carried (`FirstSumcheckWithTarget`), define over the carried statements:

* `evalClaimBindingRel` — the *first-terminal identity over the sent claims*:
  `e₁ = eq̃(τ)(r_x) · (v_A·v_B − v_C)`, with `v` read from the bundled claim oracle. This is the
  pass-through invariant that the final guard checks; conjoining it is what defeats the
  true-claims attack (the v=t attack of #114) — its flip is challenge-independent.
* `tightRelE` — the carried first sum-check transported output relation (read back through the
  claim-oracle split) **and** the binding identity.
* `tightRelF` — the *RLC match* (`∑ r·v^sent = ∑ r·v^true`) **and** the binding identity.
  Deliberately NOT carrying the sum-check conjunct past the challenge: the doomed-but-bound
  prover's flip is then exactly the kernel event of a nonzero linear form.
* `tightRelG` — the prepended target equals the true RLC (`T = ∑ r·v^true`) **and** binding.

## The flip analysis at `linearCombination` (leaf `h₅`)

For `stmtIn ∉ tightRelE`:
* if the binding identity fails, it fails in every output (pass-through) — flip probability 0;
* if the binding holds, the transported conjunct fails: its ∀-quantification *hands us* a
  compatible inner output failing the terminal sum-check relation; the oracle-pinning keystone
  (`mem_support_oracleVerifier_run_oStmt`) pins that output's oracle to the honest virtual
  polynomial, so `e₁ ≠ eval r_x F̂`. The product factorization
  `eval r_x F̂ = eq̃(τ)(r_x)·(v^true_A·v^true_B − v^true_C)` and the binding identity then force
  `v^sent ≠ v^true`, and the RLC-match event is the kernel of the nonzero linear form
  `r ↦ ∑ r·(v^sent − v^true)` — probability **exactly** `1/|R|`
  (`TightRLCKernel.probEvent_linearForm_eq`).

Together with `h₄` (message round, error 0) and `h₆` (adapter, error 0) this completes the tight
mid-chain. The flanking sum-check and final-guard leaves are the Y/Z-lane bricks (see the issue
thread); the assembly consumes all of them.
-/

open OracleComp OracleSpec ProtocolSpec Function Finset
open scoped NNReal

namespace Spartan.Spec.Bricks

set_option linter.unusedSectionVars false

noncomputable section

variable {R : Type 0} [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R]
  [SampleableType R] (pp : PublicParams)

variable {ι : Type} (oSpec : OracleSpec ι)

/-! ## Algebraic bridges -/

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R] in
/-- The first sum-check virtual polynomial's evaluation factors through the **true** evaluation
claims: `eval r_x F̂ = eq̃(τ)(r_x) · (v^true_A · v^true_B − v^true_C)`. -/
theorem firstVirtual_eval_eq_product
    (stmt : Statement.AfterFirstSumcheck R pp)
    (oStmt : ∀ i, OracleStatement.AfterFirstSumcheck R pp i) :
    MvPolynomial.eval stmt.1
      (firstSumCheckVirtualPolynomial pp stmt.2.1 stmt.2.2 oStmt)
      = MvPolynomial.eval stmt.1 (MvPolynomial.eqPolynomial stmt.2.1) *
        (evalClaimValue R pp stmt oStmt .A * evalClaimValue R pp stmt oStmt .B
          - evalClaimValue R pp stmt oStmt .C) := by
  simp only [firstSumCheckVirtualPolynomial, matVecMLE, evalClaimValue,
    MvPolynomial.eval_mul, MvPolynomial.eval_sub]

omit [IsDomain R] [Fintype R] [DecidableEq R] [Inhabited R] [SampleableType R] in
/-- Evaluating at the full-challenge concatenation with an empty tail is evaluation at the
challenges: the `⸨challenges, x⸩` of the terminal sum-check relation collapses. -/
theorem eval_append_empty_tail {n m : ℕ} (h : n = n + m) (c : Fin n → R) (x : Fin m → R)
    (F : MvPolynomial (Fin n) R) :
    MvPolynomial.eval (Fin.append c x ∘ Fin.cast h) F = MvPolynomial.eval c F := by
  have hm : m = 0 := by omega
  subst hm
  have hpt : (Fin.append c x ∘ Fin.cast h) = c := by
    funext i
    show Fin.append c x (Fin.cast h i) = c i
    rw [show Fin.cast h i = Fin.castAdd 0 i from rfl, Fin.append_left]
  exact congrArg (fun pt => MvPolynomial.eval pt F) hpt

/-- **The terminal sum-check relation at `Fin.last` is the direct evaluation identity**: the
remaining cube is empty, so the relation says exactly `eval challenges poly = target`. -/
theorem relationRound_last_iff {n : ℕ}
    (t : R) (c : Fin n → R)
    (polyO : ∀ _ : Unit, Sumcheck.Spec.OracleStatement R n 3 ()) :
    (((⟨t, fun i => c i⟩ : Sumcheck.Spec.StatementRound R n (Fin.last n)), polyO), ())
        ∈ Sumcheck.Spec.relationRound R n 3 (boolEmbedding R) (Fin.last n)
      ↔ MvPolynomial.eval c (polyO ()).val = t := by
  haveI : IsEmpty (Fin (n - ((Fin.last n) : Fin (n+1)).val)) := by
    simp only [Fin.val_last, Nat.sub_self]
    exact Fin.isEmpty'
  have hset : ((univ.map (boolEmbedding R)) ^ᶠ (n - ((Fin.last n) : Fin (n+1)).val))
      = {(fun a => isEmptyElim a :
          Fin (n - ((Fin.last n) : Fin (n+1)).val) → R)} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Fintype.mem_piFinset.mpr (fun i => isEmptyElim i),
       fun y _ => funext fun i => isEmptyElim i⟩
  have key : ∀ pf : n = ((Fin.last n) : Fin (n+1)).val
        + (n - ((Fin.last n) : Fin (n+1)).val),
      MvPolynomial.eval ((Fin.append (fun i : Fin ((Fin.last n) : Fin (n+1)).val => c i)
        (fun a : Fin (n - ((Fin.last n) : Fin (n+1)).val) => isEmptyElim a)) ∘ Fin.cast pf)
        (polyO ()).val
      = MvPolynomial.eval c (polyO ()).val := by
    intro pf
    apply congrArg (fun pt => MvPolynomial.eval pt (polyO ()).val)
    funext i
    show Fin.append _ _ (Fin.cast pf i) = c i
    rw [show Fin.cast pf i = Fin.castAdd (n - ((Fin.last n) : Fin (n+1)).val)
        ⟨i.val, by simpa using i.isLt⟩ from Fin.ext rfl, Fin.append_left]
    rfl
  simp only [Sumcheck.Spec.relationRound, Set.mem_setOf_eq]
  rw [hset, Finset.sum_singleton]
  simp only [key]

/-! ## The tight relation chain -/

/-- **The first-terminal binding identity over the *sent* claims** (the conjoined invariant of
the tight chain): the carried target `e₁` equals `eq̃(τ)(r_x) · (v_A·v_B − v_C)`, with the claims
read from the bundled claim oracle `.inl 0`. Statement format: after `sendEvalClaimWithTarget`,
i.e. `(e₁, (r_x, τ, 𝕩))` with the bundled-claim oracle family. -/
@[reducible]
def evalClaimBindingRel :
    Set (Statement.AfterSendEvalClaimWithTarget R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) :=
  { x | x.1.1 = MvPolynomial.eval x.1.2.1 (MvPolynomial.eqPolynomial x.1.2.2.1) *
      (x.2 (.inl 0) .A * x.2 (.inl 0) .B - x.2 (.inl 0) .C) }

/-- **`relE` of the tight chain**: the carried first sum-check transported output relation, read
back through the claim-oracle split, *and* the binding identity. -/
@[reducible]
def tightRelE :
    Set ((Statement.AfterSendEvalClaimWithTarget R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i)) × Unit) :=
  { x | ((x.1.1, fun j => x.1.2 (.inr j)), ())
        ∈ firstSumcheckWithTargetRbrRelOut (R := R) pp oSpec
      ∧ x.1 ∈ evalClaimBindingRel (R := R) pp }

/-- **`relF` of the tight chain**: the RLC-match (`∑ r·v^sent = ∑ r·v^true`) and the binding
identity. The sum-check conjunct is deliberately dropped: under the binding, its failure forces
`v^sent ≠ v^true`, and the RLC-match becomes the `1/|R|` kernel event. -/
@[reducible]
def tightRelF :
    Set ((Statement.AfterLinearCombinationWithTarget R pp ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | (∑ idx, x.1.1.1 idx * x.1.2 (.inl 0) idx
        = ∑ idx, x.1.1.1 idx *
            evalClaimValue R pp x.1.1.2.2 (fun j => x.1.2 (.inr j)) idx)
      ∧ (x.1.1.2, x.1.2) ∈ evalClaimBindingRel (R := R) pp }

/-- **`relG` of the tight chain**: the prepended target is the *true* RLC, and the binding
identity. (The adapter computes `T = ∑ r·v^sent`; membership forces `∑ r·v^sent = ∑ r·v^true`.) -/
@[reducible]
def tightRelG :
    Set (((R × Statement.AfterLinearCombinationWithTarget R pp) ×
      (∀ i, OracleStatement.AfterLinearCombination R pp i)) × Unit) :=
  { x | x.1.1.1 = (∑ idx, x.1.1.2.1 idx *
        evalClaimValue R pp x.1.1.2.2.2 (fun j => x.1.2 (.inr j)) idx)
      ∧ (x.1.1.2.2, x.1.2) ∈ evalClaimBindingRel (R := R) pp }

/-! ## The doomed-case extraction -/

/-- **The doom extraction.** If the binding identity holds but the transported sum-check conjunct
fails, then the sent claims differ from the true ones. The ∀-quantified transported relation hands
us a compatible inner output failing the terminal relation; the oracle-pinning keystone pins its
polynomial to the honest virtual polynomial, so `e₁ ≠ eval r_x F̂`; the product factorization and
the binding identity then separate the claims. -/
theorem sent_ne_true_of_binding_of_not_transported
    (x : Statement.AfterSendEvalClaimWithTarget R pp ×
      (∀ i, OracleStatement.AfterSendEvalClaim R pp i))
    (hbind : x ∈ evalClaimBindingRel (R := R) pp)
    (hnotD : ¬ (((x.1, fun j => x.2 (.inr j)), ())
        ∈ firstSumcheckWithTargetRbrRelOut (R := R) pp oSpec)) :
    (fun idx => x.2 (.inl 0) idx)
      ≠ (fun idx => evalClaimValue R pp x.1.2 (fun j => x.2 (.inr j)) idx) := by
  -- Constructive contraposition: if the claims were true, the transported relation would hold.
  intro hclaims
  apply hnotD
  rintro ⟨stmtIn, oStmtIn⟩ ⟨⟨t', r_x'⟩, innerO⟩ hCompat hLift
  -- `lift (stmtIn, oStmtIn) ((t', r_x'), innerO) = ((t', (r_x', stmtIn)), oStmtIn)` pins both
  -- the outer pre-image and the inner statement-out.
  have h1 : (t', (r_x', stmtIn)) = x.1 := congrArg Prod.fst hLift
  have h2 : oStmtIn = (fun j => x.2 (.inr j)) := congrArg Prod.snd hLift
  -- The oracle-pinning keystone: the compatible inner oracle is the honest virtual polynomial.
  have hpin : innerO = ((firstSumcheckOracleLensWithTarget (R := R) pp oSpec).toLens.proj
      (stmtIn, oStmtIn)).2 := by
    obtain ⟨tr, htr⟩ := hCompat
    exact Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt htr
  rw [hpin]
  refine (relationRound_last_iff (R := R) t' r_x' _).mpr ?_
  -- The terminal identity `eval r_x' F̂ = t'`, from the product factorization, the binding
  -- identity, and the truth of the claims — everything at value level in `x`-language.
  have hb : x.1.1 = MvPolynomial.eval x.1.2.1 (MvPolynomial.eqPolynomial x.1.2.2.1) *
      (x.2 (.inl 0) .A * x.2 (.inl 0) .B - x.2 (.inl 0) .C) := hbind
  have he : t' = x.1.1 := congrArg (fun p => p.1) h1
  have hr : r_x' = x.1.2.1 := congrArg (fun p => p.2.1) h1
  have hst : stmtIn = x.1.2.2 := congrArg (fun p => p.2.2) h1
  have hprod := firstVirtual_eval_eq_product (R := R) pp x.1.2 (fun j => x.2 (.inr j))
  -- Rewrite the true claims into the sent claims.
  have hA := congrFun hclaims R1CS.MatrixIdx.A
  have hB := congrFun hclaims R1CS.MatrixIdx.B
  have hC := congrFun hclaims R1CS.MatrixIdx.C
  simp only at hA hB hC
  show MvPolynomial.eval r_x'
      (firstSumCheckVirtualPolynomial pp stmtIn.1 stmtIn.2 oStmtIn) = t'
  rw [hr, hst, h2, he]
  refine hprod.trans ?_
  rw [← hA, ← hB, ← hC]
  exact hb.symm

/-! ## The compiled carried RLC-adapter verifier is pure -/

omit [IsDomain R] [SampleableType R] in
/-- The carried honest RLC-target verifier, simulated against the true oracle, deterministically
emits `(∑ idx, r idx · oStmt(.inl 0) idx, stmt)`. Clone of
`simulateQ_prependRLCTargetVerifier` at the carried statement (the verifier body reads only
`stmt.1`, which is still the RLC challenge). -/
theorem simulateQ_prependRLCTargetWithTargetVerifier
    (stmt : Statement.AfterLinearCombinationWithTarget R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i)
    (msgs : ∀ i, (!p[] : ProtocolSpec 0).Message i)
    (chals : (!p[] : ProtocolSpec 0).Challenges) :
    simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((prependRLCTargetWithTargetVerifier (R := R) pp oSpec).verify stmt chals
        : OracleComp _ (Option (R × Statement.AfterLinearCombinationWithTarget R pp)))
      = pure (some (∑ idx, stmt.1 idx * oStmt (.inl 0) idx, stmt)) := by
  show simulateQ (OracleInterface.simOracle2 oSpec oStmt msgs)
      ((liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) >>=
        fun claims => (pure ((claims.map (fun p => stmt.1 p.1 * p.2)).sum, stmt) :
          OptionT (OracleComp _) (R × Statement.AfterLinearCombinationWithTarget R pp))) :
        OptionT (OracleComp _)
          (R × Statement.AfterLinearCombinationWithTarget R pp)).run = _
  rw [simulateQ_optionT_bind']
  rw [show ((liftM ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) :
      OptionT (OracleComp _) (List (R1CS.MatrixIdx × R)))) =
      ((Finset.univ : Finset R1CS.MatrixIdx).toList.mapM (rlcStep pp oSpec)) from rfl]
  erw [simulateQ_optionT_list_mapM_pure (OracleInterface.simOracle2 oSpec oStmt msgs)
      (rlcStep pp oSpec)
      (fun idx => ((idx, oStmt (.inl 0) idx) : R1CS.MatrixIdx × R)) _
      (fun idx => simulateQ_rlcStep pp oSpec oStmt msgs idx)]
  simp only [OptionT.run_pure, simulateQ_pure]
  refine Eq.trans (pure_bind _ _) (congrArg (fun z => pure (some (z, stmt))) ?_)
  rw [List.map_map,
    ← Finset.sum_map_toList Finset.univ (fun idx => stmt.1 idx * oStmt (.inl 0) idx)]
  rfl

omit [IsDomain R] [SampleableType R] in
/-- The compiled carried RLC-target adapter verifier is pure. -/
theorem prependRLCTargetWithTarget_toVerifier_pure :
    (prependRLCTargetWithTarget (R := R) pp oSpec).verifier.toVerifier
      = ⟨fun p _tr => pure ((∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1), p.2)⟩ := by
  have h := OracleVerifier.toVerifier_eq_pure_of_collapse
    (prependRLCTargetWithTarget (R := R) pp oSpec).verifier
    (fun p _tr => (∑ idx, p.1.1 idx * p.2 (.inl 0) idx, p.1))
    (fun stmt oStmt tr => by
      exact_mod_cast simulateQ_prependRLCTargetWithTargetVerifier (R := R) pp oSpec stmt oStmt
        tr.messages tr.challenges)
  rw [h]
  congr 1

/-! ## The three tight mid-chain leaves -/

section Leaves

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Leaf `h₄` (tight chain).** The carried `sendEvalClaim` round is perfectly rbr
knowledge-sound from the carried first sum-check's transported output relation to `tightRelE`:
the statement and matrix/witness oracles are forwarded, so the transported conjunct of any
output in `tightRelE` *is* input membership; the (adversarial) claim message only feeds the
binding conjunct, which is discarded. -/
theorem sendEvalClaimWithTarget_rbrKnowledgeSoundness_leaf :
    (sendEvalClaimWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (firstSumcheckWithTargetRbrRelOut (R := R) pp oSpec)
      (tightRelE (R := R) pp oSpec) 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [sendEvalClaimWithTarget_toVerifier_closed]
  exact Verifier.rbrKnowledgeSoundness_singleMessage_pure init impl _
    (fun stmtIn msg h => h.1)

/-- **Leaf `h₅` (tight chain) — the point of issue #329.** The carried `linearCombination`
round is rbr knowledge-sound from `tightRelE` to `tightRelF` with per-round error `1/|R|` —
Spartan Lemma 5.1's bound. A doomed input either fails the binding identity (whose flip is
challenge-independent: probability 0) or fails the transported sum-check conjunct while bound
(then the sent claims provably differ from the true ones and the RLC-match is the kernel event
of a nonzero linear form: probability exactly `1/|R|`). -/
theorem linearCombinationWithTarget_rbrKnowledgeSoundness_leaf :
    (linearCombinationWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (tightRelE (R := R) pp oSpec)
      (tightRelF (R := R) pp)
      (fun _ => (1 : ℝ≥0) / (Fintype.card R : ℝ≥0)) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [linearCombinationWithTarget_toVerifier_closed]
  refine Verifier.rbrKnowledgeSoundness_singleChallenge_pure
    (C := LinearCombinationChallenge R)
    init impl
    (fun (p : Statement.AfterSendEvalClaimWithTarget R pp ×
        ∀ i, OracleStatement.AfterSendEvalClaim R pp i) c => ((c, p.1), p.2))
    (tightRelE (R := R) pp oSpec)
    (tightRelF (R := R) pp) _ ?_
  intro stmtIn hnotE
  by_cases hbind : stmtIn ∈ evalClaimBindingRel (R := R) pp
  · -- The transported conjunct fails: the claims differ, and the flip is the kernel event.
    have hnotD : ¬ (((stmtIn.1, fun j => stmtIn.2 (.inr j)), ())
        ∈ firstSumcheckWithTargetRbrRelOut (R := R) pp oSpec) := by
      intro hD
      exact hnotE ⟨hD, hbind⟩
    have hne := sent_ne_true_of_binding_of_not_transported pp oSpec stmtIn hbind hnotD
    refine le_trans (probEvent_mono ?_) (probEvent_linearForm_eq_le
      (fun idx => stmtIn.2 (.inl 0) idx)
      (fun idx => evalClaimValue R pp stmtIn.1.2 (fun j => stmtIn.2 (.inr j)) idx) hne)
    intro c _ hc
    exact hc.1
  · -- The binding identity fails: it is challenge-independent, so no output lands in `relF`.
    refine le_trans (le_of_eq (probEvent_eq_zero_iff.mpr ?_)) (zero_le _)
    intro c _ hc
    exact hbind hc.2

/-- **Leaf `h₆` (tight chain).** The carried honest RLC-target adapter is perfectly rbr
knowledge-sound from `tightRelF` to `tightRelG`: it emits `T = ∑ r·v^sent`, so `tightRelG`'s
target equation *is* the RLC-match, and the binding conjunct forwards. -/
theorem prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf :
    (prependRLCTargetWithTarget (R := R) pp oSpec).verifier.rbrKnowledgeSoundness init impl
      (tightRelF (R := R) pp)
      (tightRelG (R := R) pp) 0 := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  rw [prependRLCTargetWithTarget_toVerifier_pure]
  exact Verifier.rbrKnowledgeSoundness_zeroRound_pure init impl _
    (fun stmtIn h => ⟨h.1, h.2⟩)

end Leaves

end

end Spartan.Spec.Bricks

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Spartan.Spec.Bricks.firstVirtual_eval_eq_product
#print axioms Spartan.Spec.Bricks.relationRound_last_iff
#print axioms Spartan.Spec.Bricks.sent_ne_true_of_binding_of_not_transported
#print axioms Spartan.Spec.Bricks.simulateQ_prependRLCTargetWithTargetVerifier
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTarget_toVerifier_pure
#print axioms Spartan.Spec.Bricks.sendEvalClaimWithTarget_rbrKnowledgeSoundness_leaf
#print axioms Spartan.Spec.Bricks.linearCombinationWithTarget_rbrKnowledgeSoundness_leaf
#print axioms Spartan.Spec.Bricks.prependRLCTargetWithTarget_rbrKnowledgeSoundness_leaf
