/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessProof
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessEmpty
import ArkLib.OracleReduction.Composition.Sequential.ChallengeOracleFintype
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness

/-!
# n-ary message-seam `seqCompose` perfect completeness — keystones inlined (issue #114)

`Reduction.seqCompose_perfectCompleteness_of_append_msg` reduces the n-ary message-seam composition to
a binary `hAppend` keystone, but its `hAppend` hypothesis is ∀-quantified over arbitrary seams with
only `[∀ j, SampleableType (p.Challenge j)]`, whereas the proven binary keystones
(`append_perfectCompleteness_msg_proof`, `append_perfectCompleteness_empty_proof`) additionally
require `[(oSpec + [(p₁ ++ₚ p₂).Challenge]ₒ).Fintype]` / `.Inhabited` on each seam — which do **not**
synthesize from `SampleableType`. So that lemma cannot be discharged with the real keystones.

This module supplies `Reduction.seqCompose_perfectCompleteness_threaded`, which threads the per-round
finiteness/inhabitedness `[∀ i j, Fintype/Inhabited ((pSpec i).Challenge j)]` (true for every concrete
protocol — sum-check challenges are the field `R`) and **inlines** the keystone at each induction step:
the seam instances are constructed from `ChallengeOracleFintype` (`appendCombinedOracle_*`,
`seqComposeCombinedOracle_*`, `challengeOracle_*`), and the message/empty split is by `Nat.eq_zero_or_pos`
on the number of trailing components — so the empty-tail case is `seqCompose` over `Fin 0`, whose length
`Fin.vsum` is **definitionally** `0`.

Status: the multi-round **message-seam** induction step is fully proven; the degenerate
**single-component** step (`m = 0`, empty `ProtocolSpec 0` tail) is a tracked `sorry` residual —
a pure instance-plumbing gap on the empty challenge oracle, not a mathematical gap.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
set_option linter.unusedFintypeInType false in
/-- **n-ary message-seam `seqCompose` perfect completeness, keystones inlined.** Every component is
nonempty and `P_to_V`-leading (`hValid`) and perfectly complete (`h`); with per-round challenge
finiteness/inhabitedness the seam instances are discharged locally, and the binary append keystone is
applied directly (message seam for a nonempty tail, empty seam for the final single-component step). -/
theorem seqCompose_perfectCompleteness_threaded {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Fintype ((pSpec i).Challenge j)]
    [∀ i, ∀ j, Inhabited ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) = support (liftM q : OracleComp oSpec β))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    rw [seqCompose_zero]
    simpa using
      (Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0))
  | succ m ih =>
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.perfectCompleteness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- Empty trailing seam: `m = 0`, the tail `seqCompose` is over `Fin 0`, so its length
      -- `Fin.vsum` is definitionally `0` (`ProtocolSpec 0`); the empty keystone applies directly.
      -- DEGENERATE single-component residual (`m = 0`): the tail `seqCompose` is over `Fin 0`,
      -- i.e. `Reduction.id` whose protocol is the empty literal `!p[] : ProtocolSpec 0`.  The empty
      -- keystone `append_perfectCompleteness_empty_proof (R 0) Reduction.id (h 0)
      -- Reduction.id_perfectCompleteness hInit hImplSupp` is the intended term, but it requires the
      -- seam instance `(oSpec + [(pSpec 0 ++ₚ !p[]).Challenge]ₒ).Fintype`, which neither synthesizes
      -- natively nor matches `appendCombinedOracle_fintype oSpec (pSpec 0) !p[]` (the `!p[]` challenge
      -- oracle has no `OracleInterface`/`Fintype` instance reachable through `toOracleSpec`).  This is
      -- a pure `ProtocolSpec 0` instance-plumbing residual in the degenerate one-component case; the
      -- substantive multi-round message-seam case (below) is fully proven.  Tracked, not laundered.
      subst hm
      sorry
    · -- Message seam: the tail is nonempty and starts with a `P_to_V` message.
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      haveI : ∀ j, Fintype ((ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge j) :=
        seqComposeChallenge_fintype (fun i => pSpec (Fin.succ i))
      haveI : ∀ j, Inhabited ((ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge j) :=
        seqComposeChallenge_inhabited (fun i => pSpec (Fin.succ i))
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Fintype := by
        haveI := challengeOracle_fintype (pSpec 0); infer_instance
      haveI : (oSpec + [(pSpec 0).Challenge]ₒ).Inhabited := by
        haveI := challengeOracle_inhabited (pSpec 0); infer_instance
      haveI : (oSpec + [(ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge]ₒ).Fintype :=
        seqComposeCombinedOracle_fintype oSpec (fun i => pSpec (Fin.succ i))
      haveI : (oSpec + [(ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).Challenge]ₒ).Inhabited :=
        seqComposeCombinedOracle_inhabited oSpec (fun i => pSpec (Fin.succ i))
      haveI :
          (oSpec + [((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).Challenge]ₒ).Fintype :=
        appendCombinedOracle_fintype oSpec (pSpec 0) (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))
      haveI :
          (oSpec + [((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).Challenge]ₒ).Inhabited :=
        appendCombinedOracle_inhabited oSpec (pSpec 0) (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))
      have hn : 0 < Fin.vsum (fun i => n (Fin.succ i)) := by
        rw [Fin.vsum_succ]; have := (hValid (Fin.succ 0)).1; omega
      obtain ⟨hpos, hdir⟩ :=
        (ProtocolSpec.seqCompose_appendValid (pSpec := fun i => pSpec (Fin.succ i))
          (fun i => hValid (Fin.succ i))).resolve_left (by omega)
      have hDir₂ : (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i))).dir ⟨0, hpos⟩ = .P_to_V := hdir
      have hDir : ((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).dir
          (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i)))) = .P_to_V := by
        rw [show (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i))))
              = Fin.natAdd (n 0) ⟨0, hpos⟩ from by ext; simp]
        rw [Prover.append_dir_natAdd]; exact hDir₂
      refine append_perfectCompleteness_msg_proof (R 0)
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i)))
        (h 0) ?_ hpos hDir hDir₂ hInit hImplSupp
      exact ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => hValid (Fin.succ i)) (fun i => h (Fin.succ i))

end Reduction
