/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Sumcheck.Spec.General
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompletenessExplicit

/-!
# Full multi-round sum-check perfect completeness

`Sumcheck.Spec.reduction_perfectCompleteness` assembles the multi-round sum-check perfect
completeness from the per-round `SingleRound.reduction_perfectCompleteness` via the explicit-instance
n-ary keystone `Reduction.seqCompose_pc_msg'`. The per-round challenge `Fintype`/`Inhabited` are built
deterministically (`SingleRound.chalFintype`/`chalInhab`) from `[Fintype R]`/`[Inhabited R]`,
side-stepping the fragile challenge-spec instance synthesis.

This is the `h_inner` consumed by the Spartan sum-check phase completeness theorems.
-/

open ProtocolSpec OracleComp OracleSpec Polynomial
open scoped NNReal

namespace Sumcheck.Spec.SingleRound
open Reduction.ChalInst

/-- Challenge `Fintype` base case for a `P_to_V` singleton (vacuous: no challenge round). -/
def chalBaseFintypeP {Msg : Type} : ∀ i, Fintype (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i) :=
  fun i => isEmptyElim i
/-- Challenge `Fintype` base case for a `V_to_P` singleton (the unique challenge of type `Chal`). -/
def chalBaseFintypeV {Chal : Type} [Fintype Chal] :
    ∀ i, Fintype (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i) :=
  fun i => Unique.uniq inferInstance i ▸ (inferInstanceAs (Fintype Chal))
def chalBaseFintypeE : ∀ i, Fintype (Challenge (!p[] : ProtocolSpec 0) i) := fun ⟨i, _⟩ => Fin.elim0 i
def chalBaseInhabP {Msg : Type} : ∀ i, Inhabited (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i) :=
  fun i => isEmptyElim i
def chalBaseInhabV {Chal : Type} [Inhabited Chal] :
    ∀ i, Inhabited (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i) :=
  fun i => Unique.uniq inferInstance i ▸ (inferInstanceAs (Inhabited Chal))
def chalBaseInhabE : ∀ i, Inhabited (Challenge (!p[] : ProtocolSpec 0) i) := fun ⟨i, _⟩ => Fin.elim0 i

/-- The per-round sum-check challenge spec is finite when the ring is (each challenge is a field
element). Constructed explicitly to avoid the fragile `∀ i, Fintype (Challenge i)` synthesis. -/
def chalFintype {R : Type} [CommSemiring R] [Fintype R] {deg : ℕ} :
    ∀ i, Fintype ((pSpec R deg).Challenge i) :=
  appendChalFintype _ _
    (appendChalFintype _ _ (appendChalFintype _ _ chalBaseFintypeP chalBaseFintypeE)
      chalBaseFintypeV) chalBaseFintypeE
def chalInhab {R : Type} [CommSemiring R] [Inhabited R] {deg : ℕ} :
    ∀ i, Inhabited ((pSpec R deg).Challenge i) :=
  appendChalInhab _ _
    (appendChalInhab _ _ (appendChalInhab _ _ chalBaseInhabP chalBaseInhabE)
      chalBaseInhabV) chalBaseInhabE

/-- The sum-check round protocol leads with the prover's univariate-polynomial message. -/
theorem pSpec_dir_zero {R : Type} [CommSemiring R] {deg : ℕ} :
    (pSpec R deg).dir ⟨0, by omega⟩ = .P_to_V := rfl

end Sumcheck.Spec.SingleRound

namespace Sumcheck.Spec
open Reduction

variable {R : Type} [CommSemiring R] [SampleableType R] [DecidableEq R] [Fintype R] [Inhabited R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
  {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- **Full multi-round sum-check perfect completeness (`Reduction` level).** Assembled from the
per-round `SingleRound.reduction_perfectCompleteness` through the explicit-instance message-seam
n-ary keystone. -/
theorem reduction_perfectCompleteness (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β)) :
    (reduction R deg D n oSpec).perfectCompleteness init impl
      (relationRound R n deg D 0) (relationRound R n deg D (Fin.last n)) :=
  Reduction.seqCompose_pc_msg'
    (Stmt := fun i => StatementRound R n i × (∀ j, OracleStatement R n deg j))
    (Wit := fun _ => Unit)
    (R := SingleRound.reduction R n deg D oSpec)
    (rel := fun i => relationRound R n deg D i)
    (hFin := fun _ => SingleRound.chalFintype)
    (hInh := fun _ => SingleRound.chalInhab)
    (hValid := fun _ => ⟨by omega, SingleRound.pSpec_dir_zero⟩)
    hInit hImplSupp
    (fun i => SingleRound.reduction_perfectCompleteness i)

end Sumcheck.Spec
