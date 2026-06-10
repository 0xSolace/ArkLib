/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma512Honest

/-!
# Lemma 5.12 migration to paper semantics — inversion bricks (statement repair, step 3a)

First bricks of the `Lemma512Honest.lean` migration onto the paper-faithful dedup
`redundantEntryDSPaper` (CO25 Def. 5.5): the per-slot inversion lemmas and the capacity-transport
corollaries. The key semantic difference vs the legacy chain: a redundant *forward* entry's
certificate is now an earlier forward entry with the **same** pair or an earlier **inverse** entry
with the same pair (opposite direction) — the state pair is preserved, only the direction flips,
so capacity transports carry **both** sides unchanged (cleaner than the legacy reversed-pair
attribution). Downstream consumers must therefore case on the prior entry's direction — this is
exactly the "raw inverse entries can dedup into forward entries" shape-change the refutation
analysis predicted.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleSpec

namespace QueryLog

section DuplexSpongeFS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- Inversion of `redundantEntryDSPaper` at a forward slot: the certificate is an earlier entry
with the **same state pair**, in either direction. -/
lemma redundantEntryDSPaper_forward_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stateIn stateOut : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDSPaper idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDSPaper at hred
  rw [hval] at hred
  exact hred

/-- Inversion of `redundantEntryDSPaper` at an inverse slot: the certificate is an earlier entry
with the **same state pair**, in either direction. -/
lemma redundantEntryDSPaper_inverse_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stateOut stateIn : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDSPaper idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDSPaper at hred
  rw [hval] at hred
  exact hred

/-- Inversion of `redundantEntryDSPaper` at a hash slot: an earlier copy of the same hash entry
(unchanged from legacy — the repair only touches the permutation arms). -/
lemma redundantEntryDSPaper_hash_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C)
    (hval : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDSPaper idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      tr[j'] = (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) := by
  unfold redundantEntryDSPaper at hred
  rw [hval] at hred
  exact hred

/-- A paper-redundant forward entry sharing a target capacity has an earlier **permutation**
replacement (in either direction) carrying the same state pair, hence the same capacity sides. -/
theorem redundantPaper_forward_capacity_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {capSeg : Vector U SpongeSize.C} {stateIn stateOut : CanonicalSpongeState U}
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hred : tr.redundantEntryDSPaper idx)
    (hcap : stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) :
    ∃ j' : Fin tr.length, j' < idx ∧
      ∃ stateIn' stateOut' : CanonicalSpongeState U,
        (tr[j'] =
            (⟨Sum.inr (Sum.inl stateIn'), stateOut'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∨
          tr[j'] =
            (⟨Sum.inr (Sum.inr stateOut'), stateIn'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) ∧
        (stateOut'.capacitySegment = capSeg ∨ stateIn'.capacitySegment = capSeg) := by
  obtain ⟨j', hj', hcase⟩ :=
    redundantEntryDSPaper_forward_inversion tr idx stateIn stateOut hval hred
  exact ⟨j', hj', stateIn, stateOut, hcase, hcap⟩

/-- A paper-redundant inverse entry sharing a target capacity has an earlier **permutation**
replacement (in either direction) carrying the same state pair, hence the same capacity sides. -/
theorem redundantPaper_inverse_capacity_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {capSeg : Vector U SpongeSize.C} {stateOut stateIn : CanonicalSpongeState U}
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hred : tr.redundantEntryDSPaper idx)
    (hcap : stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) :
    ∃ j' : Fin tr.length, j' < idx ∧
      ∃ stateIn' stateOut' : CanonicalSpongeState U,
        (tr[j'] =
            (⟨Sum.inr (Sum.inl stateIn'), stateOut'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∨
          tr[j'] =
            (⟨Sum.inr (Sum.inr stateOut'), stateIn'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) ∧
        (stateOut'.capacitySegment = capSeg ∨ stateIn'.capacitySegment = capSeg) := by
  obtain ⟨j', hj', hcase⟩ :=
    redundantEntryDSPaper_inverse_inversion tr idx stateOut stateIn hval hred
  refine ⟨j', hj', stateIn, stateOut, ?_, hcap⟩
  rcases hcase with hinv | hfwd
  · exact Or.inr hinv
  · exact Or.inl hfwd

end DuplexSpongeFS

end QueryLog

end OracleSpec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_forward_inversion
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_inverse_inversion
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_hash_inversion
#print axioms OracleSpec.QueryLog.redundantPaper_forward_capacity_prior
#print axioms OracleSpec.QueryLog.redundantPaper_inverse_capacity_prior
