/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.MvPolynomial.RestrictDegree

/-!
# Structured (Witness-Mode) Sumcheck — Types and Helpers

This file collects the data types and degree-bookkeeping helpers used by the
**structured sumcheck**: the witness-mode degree-2 multilinear-times-multilinear sumcheck
that underlies Binius BinaryBasefold, Binius RingSwitching, and (in the future) Hachi.

Unlike the canonical, oracle-mode sumcheck in `ArkLib/ProofSystem/Sumcheck/Spec/*`, where
the polynomial being sumchecked is an oracle statement accessible to the verifier, here
the polynomial `H = m · t` is the prover's *witness*: `t` is a committed multilinear, `m`
is a context-dependent multilinear multiplier, and `H` is their degree-2 product. The
verifier sees only the prover's round polynomials `pᵢ`, not `H` directly.

The two modes coexist as parallel primitives under `Sumcheck`.

## TODO (option C, tracked separately)

A refinement theorem connecting the two modes — given `H = m · t`, derive structured-mode
soundness from canonical-mode soundness — is left for follow-up work. Until then, the two
modes carry independent proofs.

## Contents (lifted from `Binius.BinaryBasefold.Basic` § `SumcheckOperations` and
`Binius.RingSwitching.SumcheckWitness`)

- `MultilinearPoly`, `MultiquadraticPoly` — degree-1 / degree-2 `MvPolynomial` abbreviations.
- `SumcheckMultiplierParam` — bundles a `Context → MultilinearPoly` (the multiplier `m`).
- `computeInitialSumcheckPoly` — `H := m · t` with the degree-2 proof.
- `projectToMidSumcheckPoly`, `projectToNextSumcheckPoly` — partial evaluation of `H` at
  the verifier's previous challenges.
- `SumcheckBaseContext` — `(t_eval_point, original_claim)` shared input.
- `Statement Context i` — per-round state: `(sumcheck_target, challenges, ctx)`.
- `sumcheckConsistencyProp` — claim equals hypercube sum.
- `SumcheckWitness` — per-round witness `(t', H)` (the committed multilinear + projected
  round polynomial).
-/

noncomputable section

namespace Sumcheck.Structured

open Finset MvPolynomial

section SumcheckOperations

abbrev MultilinearPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 1⦄[X Fin ℓ]
abbrev MultiquadraticPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 2⦄[X Fin ℓ]

/-- Parameters describing how the round polynomial `H` is built from the witness `t`:
`H = P · Q(t)`, where `P` is a public multilinear multiplier and `Q` is a public univariate
*combinator* applied to the (multilinear) witness. The round polynomial then has degree
`≤ degCombinator + 1` in each variable.

No instantiation is privileged: every consumer specifies its own `combinator`, `degCombinator`,
and degree proof. The plain degree-2 case `H = P · t` (Binary Basefold, ring-switching) takes
`combinator := X`, `degCombinator := 1`; Hachi's range/smallness check uses `Q := ∏ⱼ (X − j)` of
degree `2b`, giving a degree-`(2b+1)` round polynomial.

For example, in Binary Basefold `multpoly` is `eqTilde(r₀, .., r_{ℓ-1}, X₀, .., X_{ℓ-1})`. -/
structure SumcheckMultiplierParam (L : Type) [CommRing L] (ℓ : ℕ) (Context : Type) where
  /-- Public multilinear multiplier `P`. -/
  multpoly : (ctx : Context) → MultilinearPoly L ℓ
  /-- Public univariate combinator `Q`, applied to the witness: `H = P · Q(t)`.
  The identity-like `X` recovers the plain degree-2 case `H = P · t`. -/
  combinator : (ctx : Context) → Polynomial L
  /-- Uniform degree bound on `combinator`; the round polynomial is degree `≤ degCombinator + 1`. -/
  degCombinator : ℕ
  /-- `combinator` respects its degree bound. For the `combinator := X`, `degCombinator := 1`
  case, discharge with `Polynomial.natDegree_X_le` (which needs only `Semiring`, so it holds even
  over a trivial ring — unlike `natDegree_X`, which needs `Nontrivial`). -/
  combinator_natDegree_le : ∀ ctx, (combinator ctx).natDegree ≤ degCombinator

-- The variable block matches the original `Binius.BinaryBasefold.Basic`'s line-19 block
-- (`ℓ` explicit + `[NeZero ℓ]` instance) so that positional callers like
-- `projectToMidSumcheckPoly ℓ wit.t ...` continue to typecheck. PR 4 will weaken these
-- once `ProofSystem/RingSwitching/*` no longer uses positional `ℓ`.
variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]

/-- `H₀(X₀, ..., X_{ℓ-1}) = h(X₀, ..., X_{ℓ-1}) =`
  `m(X_0, ..., X_{ℓ-1}) · t(X_0, ..., X_{ℓ-1})` -/
def computeInitialSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) : MultiquadraticPoly L ℓ :=
  ⟨m * t, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    have h_t_deg: degreeOf i t.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (t.property) a i
    have h_m_deg: degreeOf i m.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (m.property) a i
    calc
      _ ≤ (degreeOf i m.val) + (degreeOf i t.val) :=
        degreeOf_mul_le i m.val t.val
      _ ≤ 2 := by omega
  ⟩

/-- The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public
multilinear multiplier and `Q = param.combinator ctx` is the public univariate combinator applied
to the multilinear witness `t`. Its degree in each variable is `≤ param.degCombinator + 1`.

Specializes to `computeInitialSumcheckPoly t (param.multpoly ctx)` when `combinator = X`. -/
def computeRoundPoly {Context : Type} (param : SumcheckMultiplierParam L ℓ Context)
    (ctx : Context) (t : MultilinearPoly L ℓ) : L⦃≤ param.degCombinator + 1⦄[X Fin ℓ] :=
  ⟨(param.multpoly ctx).val * Polynomial.aeval t.val (param.combinator ctx), by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    have hP : degreeOf i (param.multpoly ctx).val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (param.multpoly ctx).property a i
    have ht : degreeOf i t.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ t.property a i
    calc degreeOf i ((param.multpoly ctx).val * Polynomial.aeval t.val (param.combinator ctx))
        ≤ degreeOf i (param.multpoly ctx).val
            + degreeOf i (Polynomial.aeval t.val (param.combinator ctx)) := degreeOf_mul_le i _ _
      _ ≤ 1 + (param.combinator ctx).natDegree := by
          gcongr
          exact MvPolynomial.degreeOf_aeval_le i (param.combinator ctx) t.val ht
      _ ≤ 1 + param.degCombinator := by gcongr; exact param.combinator_natDegree_le ctx
      _ = param.degCombinator + 1 := by ring⟩

/-- `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = ∑ ω ∈ 𝓑ᵢ, H₀(ω₀, …, ω_{i-1}, Xᵢ, …, X_{ℓ-1}) (where H₀=h)` -/
def projectToMidSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : MultiquadraticPoly L (ℓ-i) :=
  let H₀: MultiquadraticPoly L ℓ := computeInitialSumcheckPoly (ℓ:=ℓ) t m
  let Hᵢ := fixFirstVariablesOfMQP (ℓ := ℓ) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)
  ⟨Hᵢ, by
    have hp := H₀.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ) (v := ⟨i, by omega⟩)
        (poly := H₀.val) (challenges := challenges) (deg := 2) hp)
  ⟩

/-- Derive `H_{i+1}` from `H_i` by projecting the first variable -/
def projectToNextSumcheckPoly (i : Fin (ℓ)) (Hᵢ : MultiquadraticPoly L (ℓ - i))
    (rᵢ : L) : -- the current challenge
    MultiquadraticPoly L (ℓ - i.succ) := by
  let projectedH := fixFirstVariablesOfMQP (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
    (H := Hᵢ.val) (challenges := fun _ => rᵢ)
  exact ⟨projectedH, by
    have hp := Hᵢ.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
        (poly := Hᵢ.val) (challenges := fun _ => rᵢ) (deg := 2) hp)
  ⟩

end SumcheckOperations

section ContextAndStatement

/-- Input context for the sumcheck protocol, used mainly in BinaryBasefold.
For other protocols, there might be other context data.
NOTE: might add a flag `rejected` to indicate if prover has been rejected before. But that seems
like a fundamental feature of OracleReduction instead, so no action taken for now. -/
structure SumcheckBaseContext (L : Type) (ℓ : ℕ) where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

-- `[NeZero ℓ]` matches the original auto-bind on `Statement` (the variable block in
-- `Binius.BinaryBasefold.Basic` line 384 had `[NeZero ℓ]` in scope, so `Statement` carried it).
variable {L : Type} {ℓ : ℕ} [NeZero ℓ]

/-- Statement per iterated sumcheck round -/
structure Statement (Context : Type) (i : Fin (ℓ + 1)) where
  -- Current round state
  sumcheck_target : L              -- s_i (current sumcheck target for round i)
  challenges : Fin i → L           -- R'_i = (r'_0, ..., r'_{i-1}) from previous rounds
  ctx : Context -- external context for composition from the outer protocol

end ContextAndStatement

section ConsistencyProp

variable {L : Type} [CommRing L]
variable {𝓑 : Fin 2 ↪ L}

/-- Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum -/
def sumcheckConsistencyProp {k : ℕ} (sumcheckTarget : L) (H : L⦃≤ 2⦄[X Fin (k)]) : Prop :=
  sumcheckTarget = ∑ x ∈ (univ.map 𝓑) ^ᶠ (k), H.val.eval x

end ConsistencyProp

section Witness

/-- Witness for the structured sumcheck at round `i`:
- `t'` — the original multilinear polynomial (the "data" being committed); same across rounds.
- `H`  — the projected round polynomial `H_i(X_i, …, X_{ℓ-1})` of degree `≤ d`, equal to the
  round polynomial `P · Q(t')` with the first `i` variables fixed to the verifier's previous
  challenges.

The degree bound `d` is explicit (no privileged instantiation): the `H = P · t'` case passes
`d := 2`, Hachi's degree-`(2b+1)` smallness check passes `d := 2b+1`.

Generic in shape; the per-round prover/verifier consume this witness uniformly across all
structured-sumcheck instantiations. -/
structure SumcheckWitness (L : Type) [CommSemiring L] (ℓ : ℕ) (i : Fin (ℓ + 1)) (d : ℕ) where
  t' : MultilinearPoly L ℓ
  H : L⦃≤ d⦄[X Fin (ℓ - i)]

end Witness

end Sumcheck.Structured
