/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.ZKDefA

/-!
  # Brick C (scratch): A concrete perfect-HVZK instance — the trivial (`DoNothing`) reduction

  The trivial reduction `Reduction.id` (the `DoNothing` component) is a zero-round reduction whose
  prover sends no messages and whose verifier returns its input statement.  Its full transcript is
  the unique element of `FullTranscript !p[]` (a function out of `Fin 0`).  Crucially the transcript
  is *witness-independent*: the honest interaction produces the empty transcript regardless of the
  witness.  Hence the simulator that simply returns the empty transcript (using only the statement,
  in fact not even that) achieves *perfect* honest-verifier zero-knowledge.

  This is the minimal meaningful HVZK instance: it exhibits a non-witness-leaking simulator and
  proves it matches the honest transcript distribution exactly.

  Witness-*dependent* prover messages (as in sumcheck and other interactive proofs) genuinely leak
  information in the clear and require masking / commitment to achieve HVZK; that is out of scope for
  this brick and noted in the integration file.
-/

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn : Type}
  {σ : Type}

/-- The simulator for the trivial reduction: ignore the statement and emit the unique empty
  transcript of the empty protocol specification. -/
def idTranscriptSimulator :
    TranscriptSimulator oSpec StmtIn (!p[] : ProtocolSpec 0) :=
  fun _ => pure default

/-- The honest transcript distribution of the trivial reduction is `pure default`: the empty
  transcript with probability one (the verifier always accepts and there are no messages). -/
theorem honestTranscriptDist_id
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (stmtIn : StmtIn) (witIn : WitIn) :
    honestTranscriptDist init impl
        (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) stmtIn witIn =
      (pure default : OptionT ProbComp (FullTranscript !p[])) := by
  unfold honestTranscriptDist
  simp only [Reduction.id_run]
  -- The transcript marginal of `pure ⟨⟨default, stmt, wit⟩, stmt⟩` is `pure default`.
  rw [OptionT.ext_iff]
  rw [show ((fun result => result.1.1) <$>
      (pure (⟨⟨default, stmtIn, witIn⟩, stmtIn⟩ :
        (FullTranscript !p[] × StmtIn × WitIn) × StmtIn) :
          OptionT (OracleComp (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ)) _)).run
      = (pure (some default) : OracleComp (oSpec + [(!p[] : ProtocolSpec 0).Challenge]ₒ) _) by
        simp [OptionT.run, map_pure]]
  -- Now `simulateQ pImpl (pure (some default))` is `pure (some default)`, and `run'` drops state.
  rw [simulateQ_pure]
  simp only [StateT.run'_eq, OptionT.run_pure]
  rw [show ((pure (some default) :
      StateT σ ProbComp (Option (FullTranscript (!p[] : ProtocolSpec 0)))).run) =
      fun s => pure (some default, s) from rfl]
  -- `do let s ← init; (pure (some default, s)).fst` collapses to `pure (some default)`.
  conv_lhs =>
    rw [show (OptionT.mk do
        (fun a => (Prod.fst <$> (pure (some default, ·) : σ → ProbComp _) a))
          =<< (init >>= fun s => pure s) : OptionT ProbComp _) =
          OptionT.mk (init >>= fun _ => pure (some default)) from by
            simp [Functor.map, bind_assoc]]
  simp [OptionT.mk, bind_pure_comp, map_pure]

/-- **Concrete perfect HVZK instance.**  The trivial / `DoNothing` reduction satisfies perfect
  honest-verifier zero-knowledge for *any* input relation, witnessed by `idTranscriptSimulator`. -/
theorem id_perfectHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    perfectHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[])
      idTranscriptSimulator := by
  intro stmtIn witIn _
  rw [honestTranscriptDist_id init impl stmtIn witIn]
  rfl

/-- The trivial reduction is honest-verifier zero-knowledge for any relation. -/
theorem id_isHVZK
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (rel : Set (StmtIn × WitIn)) :
    isHVZK init impl rel
      (Reduction.id : Reduction oSpec StmtIn WitIn StmtIn WitIn !p[]) :=
  ⟨idTranscriptSimulator, id_perfectHVZK init impl rel⟩

end Reduction
