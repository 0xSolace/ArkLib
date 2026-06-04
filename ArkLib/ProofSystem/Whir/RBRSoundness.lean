/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poulami Das (Least Authority), Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.OracleReduction.VectorIOR
import ArkLib.ProofSystem.Whir.BlockRelDistance
import ArkLib.ProofSystem.Whir.MutualCorrAgreement
import ArkLib.ProofSystem.Whir.ProximityGen

/-!
# Round by round soundness theorem

This file formalizes the round by round soundness theorem of the WHIR IOPP,
introduced in the Section 5 [ACFY24].

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]

## Implementation notes (corrections from paper)

- Theorem 5.2:
-- `(δᵢ, l_{i,s})`-list decodable in place of `(l_{i,s}, δᵢ)`-list decodable
-- proximity generators should be defined for `C^(0),...,C^(k)` in place of `C^(1),...,C^(k)`

- Theorem 5.2 holds for `l = 2` as can be seen with `BStar(..,2)` and `errStar(..,2,..)`
  and so `Gen(l,alpha) = {1, alpha,...., alpha^{l-1}}` also corresponds to `l = 2`
  and not for a generic l.

- In in Construction 5.1 and Theorem 5.2,
  we use M + 1 iterations instead of M, for ease of representation in Lean

## Tags
Open question: should we aim to add tags?
-/
namespace WhirIOP

open BigOperators BlockRelDistance MutualCorrAgreement Generator Finset
     ListDecodable NNReal ReedSolomon

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {M : ℕ} (ι : Fin (M + 1) → Type) [∀ i : Fin (M + 1), Fintype (ι i)]

/-- ** Per‑round protocol parameters. **
For a fixed depth `M`, the reduction runs `M + 1` rounds.
In round `i ∈ {0,…,M}` we fold by a factor `foldingParamᵢ`,
evaluate on the point set `ιᵢ` through the embedding `φᵢ : ιᵢ ↪ F`,
and repeat certain proximity checks `repeatParamᵢ` times. -/
structure Params (F : Type) where
  foldingParam : Fin (M + 1) → ℕ
  varCount : Fin (M + 1) → ℕ
  φ : (i : Fin (M + 1)) → (ι i) ↪ F
  repeatParam : Fin (M + 1) → ℕ

/-- ** Conditions that protocol parameters must satisfy. **
  h_m : m = varCount₀
  h_sumkLt : ∑ i : Fin (M + 1), foldingParamᵢ ≤ m
  h_varCount_i : ∀ i : Fin (M + 1), i ≠ 0, varCountᵢ = m - ∑ j < i foldingParamⱼ
  h_smooth : each φᵢ must embed a smooth evaluation domain
  h_repeatPLt : ∀ i : Fin (M + 1), repeatParamᵢ ≤ |ιᵢ| -/
structure ParamConditions (P : Params ι F) where
  m : ℕ -- m = P.varCount 0
  h_m : m = P.varCount 0
  h_sumkLt : ∑ i : Fin (M + 1), P.foldingParam i ≤ m
  h_varCount_i : ∀ i : Fin (M + 1),
    P.varCount i = m - ∑ j : Fin i, P.foldingParam (Fin.castLT j (Nat.lt_trans j.isLt i.isLt))
  h_smooth : ∀ i : Fin (M + 1), Smooth (P.φ i)
  h_repeatPLt : ∀ i : Fin (M + 1), P.repeatParam i ≤ Fintype.card (ι i)

/-- `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes
  `C_{i : M + 1, j : foldingParamᵢ + 1} = RS[F, ιᵢ^(2ʲ), (varCountᵢ - j)]` with
  `Gen_α_ij` which is a proximity generator with mutual correlated agreement
  for `C_ij` with proximity parameters `BStar_ij` and `errStar_ij`.

  Additionally, it includes the condition that
    C_ij is `(δᵢ, dist_ij)`-list decodeable,
  where `δᵢ = 1 - max_{j : foldingParamᵢ + 1} BStar(C_ij,2)`
-/
-- NOTE: fix this after fixing folding
class GenMutualCorrParams (P : Params ι F) (S : ∀ i : Fin (M + 1), Finset (ι i)) where

  δ : Fin (M + 1) → ℝ≥0
  dist : (i : Fin (M + 1)) → Fin ((P.foldingParam i) + 1) → ℝ≥0

-- φ i j : ιᵢ^(2ʲ) ↪ F
  φ : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), (indexPowT (S i) (P.φ i) j) ↪ F

  inst1 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (indexPowT (S i) (P.φ i) j)
  inst2 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    Nonempty (indexPowT (S i) (P.φ i) j)
  inst3 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    DecidableEq (indexPowT (S i) (P.φ i) j)
  inst4 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Smooth (φ i j)

  parℓ_type : ∀ i : Fin (M + 1), ∀ _ : Fin ((P.foldingParam i) + 1), Type
  inst5 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (parℓ_type i j)

  exp : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), (parℓ_type i j) ↪ ℕ

-- this ensures that Gen_α_ij is a proxmity generator for C_ij = RS[F, ιᵢ^(2^j), (varCountᵢ - j)]
-- wrt proximity function Gen_α (α,l) = {1,α²,...,α^{parℓ-1}}
  Gen_α : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    ProximityGenerator (indexPowT (S i) (P.φ i) j) F :=
      fun i j => RSGenerator.genRSC (parℓ_type i j) (φ i j) (P.varCount i - j) (exp i j)

  inst6 : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Fintype (Gen_α i j).parℓ

  BStar : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → Type → ℝ≥0
  errStar : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    (Set ((indexPowT (S i) (P.φ i) j) → F)) → Type → ℝ → ENNReal

  C : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), Set ((indexPowT (S i) (P.φ i) j) → F)
  hcode : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1), (C i j) = (Gen_α i j).C

  h : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    hasMutualCorrAgreement (Gen_α i j)
      (BStar i j (C i j) (Gen_α i j).parℓ)
      (errStar i j (C i j) (Gen_α i j).parℓ)

  hℓ_bound : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    Fintype.card (Gen_α i j).parℓ = 2
  hℓ_bound' : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    Fintype.card (parℓ_type i j) = 2

  hδLe : ∀ i : Fin (M + 1),
    (δ i) ≤ 1 - Finset.univ.sup (fun j => BStar i j (C i j) (Gen_α i j).parℓ)

  hlistDecode : ∀ i : Fin (M + 1), ∀ j : Fin ((P.foldingParam i) + 1),
    listDecodable (C i j) (δ i) (dist i j)

section RBR

open NNRat OracleComp OracleSpec ProtocolSpec VectorIOP

/-- `OracleStatement` defines the oracle message type for a multi-indexed setting:
  given base input type `ι`, and field `F`, the output type at each index
  is a function `ι → F` representing an evaluation over `ι`.
-/
@[reducible]
def OracleStatement (ι F : Type) : Unit → Type :=
    fun _ => ι → F

/-- Provides a default OracleInterface instance that leverages
  the oracle statement defined above. The oracle simply applies
  the function `f : ι → F` to the query input `i : ι`,
  producing the response. -/
instance {ι : Type} : OracleInterface (OracleStatement ι F ()) := OracleInterface.instFunction

/-- WHIR relation: the oracle's output is δᵣ-close to a codeword of a smooth ReedSolomon code
with number of variables at most `varCount` over domain `φ`, within error `err`.
-/
def whirRelation
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [Nonempty ι]
    (varCount : ℕ) (φ : ι ↪ F) [Smooth φ] (err : ℝ≥0)
    : Set ((Unit × ∀ i, (OracleStatement ι F i)) × Unit) :=
  { ⟨⟨_, oracle⟩, _⟩ | δᵣ(oracle (), smoothCode φ varCount) ≤ err }

end RBR

end WhirIOP
