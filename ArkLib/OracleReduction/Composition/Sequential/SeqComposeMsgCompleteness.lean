/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.AppendPerfectCompletenessMsg

/-!
# n-ary message-seam `seqCompose` perfect completeness (issue #114)

`Reduction.seqCompose_perfectCompleteness_of_append` (in `General.lean`) reduces the n-ary
`seqCompose` perfect completeness to a binary `append` keystone — but it requires the binary keystone
to hold *unconditionally* (for every pair `R₁`, `R₂`). The proven binary keystone
`reduction_append_perfectCompleteness_msg` is only available for the **message seam** (its second
protocol starts with a `P_to_V` message), not for arbitrary seams.

This module supplies the variant `seqCompose_perfectCompleteness_of_append_msg` whose binary
hypothesis `hAppend` is restricted to "append-valid" seams: the trailing protocol is either *empty*
(0 rounds) or *starts with a `P_to_V` message*. Every component of the composition is required to be
nonempty and to start with `P_to_V` (`hValid`); this is exactly the shape of the sum-check protocol
(`Sumcheck.Spec.oracleReduction`), whose every round is a `SingleRound` starting with the prover's
univariate-polynomial message. The trailing `seqCompose` of such components is itself either empty
(when no rounds remain) or starts with `P_to_V`, discharged by `seqCompose_appendValid`.

Feeding `reduction_append_perfectCompleteness_msg` (for the nonempty message-seam case) and an
empty-trailing append-completeness lemma (for the 0-round tail) as `hAppend` then yields the full
multi-round completeness.
-/

open ProtocolSpec OracleComp
open scoped NNReal

namespace ProtocolSpec

/-- **Append-validity of a `seqCompose` of `P_to_V`-leading components.** If every component protocol
is nonempty and its first message is `P_to_V`, then their `seqCompose` is either empty (no
components) or itself nonempty with a leading `P_to_V` message. This is the side condition consumed by
the message-seam composition keystone at each induction step. -/
theorem seqCompose_appendValid {m : ℕ} {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V) :
    Fin.vsum n = 0 ∨ ∃ h : 0 < Fin.vsum n, (seqCompose pSpec).dir ⟨0, h⟩ = .P_to_V := by
  cases m with
  | zero => left; rfl
  | succ k =>
    right
    have h0 := hValid 0
    obtain ⟨hpos0, hdir0⟩ := h0
    have hvsum_pos : 0 < Fin.vsum n := by
      rw [Fin.vsum_succ]
      omega
    refine ⟨hvsum_pos, ?_⟩
    -- `(seqCompose pSpec).dir 0 = (pSpec 0).dir 0 = .P_to_V` via the `Fin.vflatten` at index 0
    rw [seqCompose_succ_eq_append]
    show (append (pSpec 0) (seqCompose fun i => pSpec (Fin.succ i))).dir ⟨0, hvsum_pos⟩ = .P_to_V
    rw [ProtocolSpec.append_dir_eq_left (pSpec 0) _ ⟨0, hpos0⟩ (by omega)]
    exact hdir0

end ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- **Brick (issue #114): n-ary message-seam `seqCompose` perfect completeness.** Reduces the n-ary
`seqCompose` perfect completeness to a binary `append` keystone `hAppend` that need only hold for
*append-valid* seams (empty trailing protocol, or trailing protocol starting with `P_to_V`). Modeled
on the proven `seqCompose_perfectCompleteness_of_append`; the only addition is threading the
append-validity side condition (discharged at each step by `ProtocolSpec.seqCompose_appendValid`).
Every component is required to be nonempty and `P_to_V`-leading (`hValid`), the shape of the
sum-check protocol. -/
theorem seqCompose_perfectCompleteness_of_append_msg {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)},
        (k₂ = 0 ∨ ∃ h : 0 < k₂, p₂.dir ⟨0, h⟩ = .P_to_V) →
        R₁.perfectCompleteness init impl r₁ r₂ → R₂.perfectCompleteness init impl r₂ r₃ →
        (R₁.append R₂).perfectCompleteness init impl r₁ r₃)
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
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
    refine hAppend (R 0) _
      (ProtocolSpec.seqCompose_appendValid (fun i => hValid (Fin.succ i)))
      (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => hValid (Fin.succ i)) (fun i => h (Fin.succ i)))

end Reduction
