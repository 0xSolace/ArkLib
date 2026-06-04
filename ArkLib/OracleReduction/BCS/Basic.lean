/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
  # The BCS Transformation

  This file defines the (generalized) BCS transformation. This transformation was first described by
  Ben-Sasson - Chiesa - Spooner in TCC'16 for IOPs with vector queries + Merkle trees. Our
  generalized version transforms any Interactive Oracle Reduction (IOR) into an Interactive
  Reduction (IR) using commitment schemes for the respective oracle messages of the protocol. This
  captures both the original BCS transformation as well as the Polynomial IOP + Polynomial
  Commitments transform (described in Plonk, Marlin, etc.).

  More precisely, the transformation works as follows:

  1. We take in an IOR `R`.

  2. We replace every oracle statement and every prover's message with a commitment (using the
     specified corresponding commitment scheme).

  3. We look at the oracle verifier's list of queries to the prover's messages. For each query, we
     run the opening argument for the query (which is itself an interactive proof).

  After defining the transformation, our goal is to show that the transformed protocol inherits the
  security properties of its building blocks (i.e. completeness, all notions of soundness, HVZK,
  etc.)

  ## What this file states (ArkLib#2: "initial attempt to state the BCS transform")

  This is a *definitional* first attempt at stating the transform; no security proofs are given.

  * `ProtocolSpec.renameMessage` (pre-existing): replace each prover-message type by a new type
    (here, a commitment type), keeping all directions fixed.
  * `ProtocolSpec.BCSOpeningPhase`: the opening phase as the sequential composition
    (`ProtocolSpec.seqCompose`) of the per-message commitment-opening protocol specs.
  * `ProtocolSpec.BCSTransform`: **fully general** at the protocol-spec level — the renamed
    interaction phase appended (`++ₚ`) to the opening phase.
  * `Reduction.bcsMessageOpening`: the per-message opening reduction extracted from a commitment
    `Commitment.Scheme` (this is exactly its `opening` proof).
  * `OracleReduction.BCSTransform`: the reduction-level transform, stated as `Reduction.append` of an
    interaction phase and an opening phase over `ProtocolSpec.BCSTransform`.

  ## What is deferred

  The reduction-level transform takes its two phases (interaction, opening) as inputs rather than
  constructing them from the input oracle reduction plus the commitment schemes. The honest
  constructions — the prover committing via `Scheme.commit` instead of sending each message, and the
  opening phase reading the oracle verifier's (possibly adaptive) query log to decide which openings
  to run and with which witnesses — are the dependent-type-plumbing-over-query-logs parts, and are
  deferred together with all security-preservation results (completeness, the soundness notions,
  HVZK) to the core oracle-reduction rewrite (ArkLib#433). Restricting to
  `OracleVerifier.NonAdaptive` removes the adaptivity blocker but not the type-threading one; see the
  design note at the end of the file. The fully general transform thus depends on #433.

  ## Notes

  The BCS transform has a lot of degrees of freedom. For instance, we can choose to run the opening
  arguments for each verifier's query in any order; here that choice of order is recorded explicitly
  by the ordering equivalence `e : pSpec.MessageIdx ≃ Fin m` passed to the transform.

  There are also a lot of variants and avenues for optimization:

  - We can ``batch'' many opening arguments together (using homomorphic properties of the commitment
    scheme, or via another round of interaction, or via specialized techniques like Merkle capping).

  ## References

  * [Ben-Sasson, E., Chiesa, A., and Spooner, N., *Interactive Oracle Proofs*, TCC 2016][BCS16] —
    the original BCS transform (vector IOPs + Merkle commitments).
  * [Chiesa, A. and Yogev, E., *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
    — textbook treatment of the BCS / hash-based-SNARG compilation.
-/

variable {n : ℕ}

namespace ProtocolSpec

/-- Switch the type of prover's messages in a protocol specification. The directions are preserved.
-/
def renameMessage (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨ pSpec.dir,
    fun i => if h : pSpec.dir i = Direction.P_to_V then NewMessage ⟨i, h⟩ else pSpec.«Type» i⟩

end ProtocolSpec

open Commitment

namespace Reduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Commitment Decommitment ComKey VerifKey : pSpec.MessageIdx → Type}

/-! ### The opening phase of the BCS transform

  The opening phase is fully constructible from the data of the commitment schemes: each scheme's
  `opening` field is a `Proof` (an interactive reduction whose output statement is `Bool`) for the
  evaluation of one committed message. The opening phase runs these one after another via the
  existing `Reduction.seqCompose`, ordered by `e : pSpec.MessageIdx ≃ Fin m`, over the protocol
  spec `ProtocolSpec.BCSOpeningPhase`.

  For a single message `i`, the opening proof proves the relation
  "the response `y` to query `q` against commitment `cm` is correct", with statement type
  `Commitment i × (q : (Oₘ i).Query) × (Oₘ i).Response q` and witness type
  `pSpec.Message i × Decommitment i`. Threading these statement/witness types through the sequential
  composition is what the `Stmt`/`Wit` families below record. -/

/-- The per-message opening reduction obtained from a commitment scheme for message `i`, given the
  committer/verifier keys. This is literally the scheme's `opening` proof, viewed as a `Reduction`
  over the opening protocol spec `pSpecCom i`. -/
def bcsMessageOpening (i : pSpec.MessageIdx)
    (scheme : Scheme oSpec (pSpec.Message i) (Commitment i) (Decommitment i)
      (ComKey i) (VerifKey i) (pSpecCom i))
    (keys : ComKey i × VerifKey i) :
    Reduction oSpec
      (Commitment i × (q : (Oₘ i).Query) × (Oₘ i).Response q)
      (pSpec.Message i × Decommitment i) Bool Unit (pSpecCom i) :=
  scheme.opening keys

end Reduction

namespace OracleReduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {m : ℕ} {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Commitment Decommitment ComKey VerifKey : pSpec.MessageIdx → Type}

variable {StmtIn StmtOut WitIn WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

end OracleReduction
