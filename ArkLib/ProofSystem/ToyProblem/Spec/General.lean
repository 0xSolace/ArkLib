
/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.ProofSystem.ToyProblem.Definitions
import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ToMathlib.RewindingExtractor
import ArkLib.ToVCVio.OracleComp.SimSemantics.SimulateQ
import ArkLib.ToVCVio.OracleComp.RbrGame

/-!
# Toy problem oracle reduction (ABF26 Construction 6.2)

We describe the ABF26 §6 toy-problem IOR as an `OracleReduction` over
ArkLib's `OracleReduction` framework, following the conventions used by
`ArkLib/ProofSystem/Fri/Spec/SingleRound.lean` and
`ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean`:

* `Statement`, `OracleStatement`, `Witness`, `OutputStatement` — input /
  oracle / witness / output type aliases (all `@[reducible]`).
* `pSpec` — the 3-round `ProtocolSpec` (`V → P` γ, `P → V` g, `V → P`
  spot-checks).
* `OracleInterface`, `Inhabited`, `Fintype` instances for the messages
  and challenges of `pSpec`.
* `inputRelation` / `outputRelation` — IOR input/output relations
  (Definitions 6.1 and 6.3, in IOR shape).
* `accepts` — the §6.1 decision predicate (extracted for use by the
  verifier and by completeness proofs).

The `prover` / `verifier` / `oracleReduction` triple is complete. The
soundness lemmas `protocol62_knowledgeSound` (L6.6) and
`protocol62_rbrKnowledgeSound` (L6.8) carry the **concrete** paper error
terms (`max (ε_mca(C,δ) + |Λ(C^{≡2},δ)|/|F|) ((1-δ)^t)` and the
per-round split). These lemmas are **2-special-soundness** arguments whose
extractor must *rewind* the prover, which the in-tree straightline
`Verifier.knowledgeSoundness` interface cannot express (the documented wall in
`research/proximity-prize/dispositions/oraclereduction-leftovers.md`). The genuine
mathematical content — the 2-special-sound rewinding extractor — is supplied
**fully proven** as `protocol62_knowledgeSoundnessViaRewinding` (the framework
predicate `Extractor.knowledgeSoundnessViaRewinding`), and each straightline
lemma is reduced to a single **named bridge residual**
`Bridge.StraightlineOfRewinding` (taken as an explicit hypothesis),
discharged by `Bridge.knowledgeSound_of_rewinding`. There are **no**
`sorry`/`axiom` terms: the residual is a named, documented interface gap, not an
admitted proof. The IOR scaffolding is exactly what is needed downstream.

## Protocol description

The verifier holds an explicit input `(v, μ₁, μ₂)` and has oracle
access to two purported codewords `f₁, f₂ : ι → F`. The protocol runs:

  1. **Combination randomness** (V → P): the verifier sends `γ ←$ F`.
  2. **Prover claim** (P → V): the prover sends `g : Fin k → F`. In the
     honest case `g = M₁ + γ · M₂` is the combination of the underlying
     messages.
  3. **Spot-check randomness** (V → P): the verifier sends
     `x₁, …, xₜ ←$ ι`.

The verifier accepts iff `⟨g, v⟩ = μ₁ + γ · μ₂` (linear-constraint
check) and for every `j ∈ Fin t`, `encode(g)(xⱼ) = f₁(xⱼ) + γ · f₂(xⱼ)`
(spot-check).

## Paper ↔ framework mapping

How each step of Construction 6.2 lands on an ArkLib / VCV-io primitive:

* `γ ←$ F` (combination randomness) ↦ `pSpec` round 0 (`.V_to_P`); the
  security games sample it via the `SampleableType F` instance on the
  challenge type.
* prover claim `ḡ ∈ F^k` ↦ `pSpec` round 1 (`.P_to_V`), with
  `OracleInterface.instDefault` as its message-oracle interface.
* spot-check positions `x₁, …, xₜ` ↦ `pSpec` round 2 (`.V_to_P`), of
  type `Fin t → ι`.
* oracle access to `f₁, f₂` ↦ `OracleStatement` queried via `queryF`,
  routed through the per-index `OracleInterface` instances.
* the §6.1 decision predicate ↦ `accepts`.
* verifier query routing ↦ `OracleInterface.simOracle2` / `simulateQ`
  (VCV-io's query-simulation semantics).
* completeness game ↦ `OracleReduction.perfectCompleteness`.
* knowledge-soundness games (paper App A.1, Defs A.2 / A.4 / A.5) ↦
  `OracleVerifier.knowledgeSoundness` / `OracleVerifier.rbrKnowledgeSoundness`.
  Two caveats: extraction **time** (the paper's `O(enc + ecor)` extractor
  cost) is outside ArkLib's cost-free model, and the verifier's query
  complexity (`2t + 1`) is documented, not enforced
  (`OracleVerifier.numQueries` is upstream-sorried).

## Alphabet restriction (`s = 1`)

The paper's Construction 6.1/6.2 inputs are `f : [n] → F^s` for a folding
parameter `s` (and the §6.3 tables sweep `s = 2^0, …, 2^12`). This
formalization fixes `s = 1`: words are `ι → F`, not `ι → F^s`. This is a
genuine scope restriction, not mere notational choice — reindexing
`ι := [n] × [s]` does **not** recover the general case, because the
relative Hamming metric over the alphabet `F^s` (one symbol = one
`F^s`-coordinate) differs from the metric over `F` on the flattened
index set. The §6.3 `s`-sweep therefore needs the `F^s` generalization,
planned for Phase-5 `Impl/FRS`. The `s = 2^0` rows of the paper's tables
fall squarely inside the current form, so the `s = 1` formalization is
non-vacuous for the prize regime.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6).
-/

namespace ToyProblem

namespace Spec

open OracleSpec OracleComp ProtocolSpec
open Code InterleavedCode ListDecodable ProximityGap
open scoped NNReal ENNReal ProbabilityTheory

/-! ### Type-level definitions and relations

The relations need `[Fintype ι]` (for `relaxedRelationFor`'s
`Fintype.card ι` call) and `[Field F]` (for the `→ₗ[F]` encoder). The
heavier `[DecidableEq ι] [Fintype F] [DecidableEq F]` instances come
in below for the protocol-object definitions. -/

variable {ι F : Type} [Fintype ι] [Field F]
variable (k t : ℕ)

/-- Input (explicit) statement of Construction 6.2: the linear-constraint
vector `v ∈ F^k` and the two constraint values `(μ₁, μ₂) ∈ F²`. -/
@[reducible]
def Statement : Type := (Fin k → F) × F × F

/-- Oracle statements of Construction 6.2: the two purported codewords
`f₁, f₂ : ι → F`. The verifier only queries them at the spot-check
positions. -/
@[reducible]
def OracleStatement (ι F : Type) : Fin 2 → Type := fun _ ↦ ι → F

instance : ∀ i, OracleInterface (OracleStatement ι F i) :=
  fun _ ↦ inferInstance

/-- Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose
encodings are the oracle codewords `f₁, f₂`. -/
@[reducible]
def Witness : Type := Fin 2 → Fin k → F

/-- Output statement: the IOR is a yes/no test — accept (return `()`) or
short-circuit to `none` via `OptionT`. -/
@[reducible]
def OutputStatement : Type := Unit

/-- Output oracle statement: the IOR has no output oracle component. -/
@[reducible]
def OutputOracleStatement : (Fin 0) → Type := nofun

/-- Output witness: empty. -/
@[reducible]
def OutputWitness : Type := Unit

/-- Protocol specification for Construction 6.2: three rounds, in the
order

    V → P  (γ : F)            -- combination randomness
    P → V  (g : Fin k → F)    -- combined message claim
    V → P  (xs : Fin t → ι)   -- spot-check positions.

Marked `@[reducible]` so per-round type access `pSpec.Type i` reduces
in client code (cf. FRI / Sumcheck single-round specs). -/
@[reducible]
def pSpec : ProtocolSpec 3 :=
  ⟨!v[.V_to_P, .P_to_V, .V_to_P],
   !v[F, Fin k → F, Fin t → ι]⟩

instance instMessageOracleInterface :
    ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault
  | ⟨2, h⟩ => nomatch h

/-- Pointwise `OracleInterface` instance for the (sole) prover message of `pSpec`, at round 1.
The `∀ j`-indexed `instMessageOracleInterface` is not found by `inferInstance` on a *concrete*
restated index `⟨1, h⟩` (the indexed match does not reduce during typeclass search), which blocks
completeness-proof terms that mention `answer (msgs ⟨1, _⟩) _`. This pointwise instance restores
synthesis; it is *definitionally equal* to `instMessageOracleInterface ⟨1, _⟩` (both `instDefault`),
so it introduces no diamond. -/
instance instMessageOracleInterfaceOne {h : (pSpec (ι := ι) (F := F) k t).dir 1 = .P_to_V} :
    OracleInterface ((pSpec (ι := ι) (F := F) k t).Message ⟨1, h⟩) :=
  OracleInterface.instDefault

instance : ∀ j, OracleInterface ((pSpec (ι := ι) (F := F) k t).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

/-- The challenges of the toy-problem `pSpec` are `SampleableType` when
the underlying field `F` and the codeword index `ι` are. This is needed
to instantiate the (round-by-round) knowledge-soundness games, which
sample challenges from the protocol's challenge spaces. -/
instance [SampleableType F] [SampleableType ι] :
    ∀ j, SampleableType ((pSpec (ι := ι) (F := F) k t).Challenge j)
  | ⟨0, _⟩ => (inferInstance : SampleableType F)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => (inferInstance : SampleableType (Fin t → ι))

/-- The §6.1 decision predicate, factored out so completeness proofs and
the verifier object share the same statement.

Given the explicit input `(v, μ₁, μ₂)`, the oracle codewords
`(f 0, f 1)`, the challenge `γ`, the prover's claim `g`, the spot-check
positions `xs`, and an encoding function `encode`, the verifier accepts
iff:

  * `⟨g, v⟩ = μ₁ + γ · μ₂` (linear constraint), and
  * `∀ j, encode(g)(xs j) = f 0 (xs j) + γ · f 1 (xs j)` (per-spot-check).
-/
def accepts (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) : Prop :=
  (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2) ∧
  ∀ j : Fin t, encode g (xs j) = f 0 (xs j) + γ * f 1 (xs j)

/-- The IOR-shaped input relation derived from `ToyProblem.relation`
(Definition 6.1).

  `((v, μ₁, μ₂), (f₁, f₂)) ∈ inputRelation k C ↔ ToyProblem.relation
    C v (μ₁, μ₂) (f₁, f₂)` (modulo `Fin 2`-indexing of the latter). -/
def inputRelation (C : Set (ι → F)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    ToyProblem.relation (k := k) (ℓ := 2) C input.1.1.1
      ![input.1.1.2.1, input.1.1.2.2] input.1.2

/-- The IOR-shaped **honest-opening** input relation for a *fixed* encoder
`encode` (the protocol's own combining map).

`((v, μ₁, μ₂), (f₁, f₂)) ∈ honestInputRelation k C encode` iff there is a
message matrix `M : Fin 2 → Fin k → F` such that

  * `f i = encode (M i)` for the **protocol's** `encode` (honest opening), and
  * `∑_j M i j · v j = μ i` (the linear constraint).

## Documented statement repair (2026-06): protocol-encoder alignment (hEnc class)

The historic completeness statement used `inputRelation k C`, which unfolds
(Definition 6.1, `ToyProblem.relation`) to

  `∃ M, (∃ encode', (∀ m, encode' m ∈ C) ∧ ∀ i, f i = encode' (M i)) ∧ …`

— the opener `encode'` is **existentially quantified** and is *a different
map* than the protocol's `encode` parameter. The honest verifier's
spot-check uses the *protocol's* `encode` (`encode g (xs j) = f₀ + γ·f₁`),
so completeness needs `f i = encode (M i)` for *that* `encode`; with the
existential `encode'` of `inputRelation`, the equality `encode (M i) (x) =
encode' (M i) (x)` is **not derivable** (counterexample: take `C` the full
space, `encode' = 0`, `encode = id`, any `M ≠ 0`; then
`((v,0,0),(0,0)) ∈ inputRelation` via `encode' = 0`, but the honest prover's
`g = M₀+γM₁` gives `encode g (x) ≠ 0 = f₀+γf₁`, so the spot-check fails and
`Pr[accept] = 0 ≠ 1`). This is a genuine statement-level wall, not proof
effort.

We repair it by aligning the input relation's opener with the protocol's
encoder — exactly the `hEnc` linear-encoder pattern of L6.13
(`SoundnessBounds.lean :: simplified_iop_soundness_ca_lb`), where the same
`relation`-encoder existential is pinned to a named `F`-linear `encode`.
This is the regime ABF26 Definition 6.1 intends ("the chosen encoding is a
bijection from `Fin k → F` onto `C`"): the honest prover *is* the party that
opened the codewords under `encode`, so the relation it is complete against
is precisely the honest-opening relation. `honestInputRelation k C encode ⊆
inputRelation k C` whenever `∀ m, encode m ∈ C` (witness `encode' := encode`),
so this is a strengthening of the hypothesis on the input, i.e. a *weaker*
(more faithful) completeness claim, never vacuous. -/
def honestInputRelation (_C : Set (ι → F)) (encode : (Fin k → F) →ₗ[F] (ι → F)) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    -- The *witness given to the prover* (`input.2`) is itself the honest opening: it opens the
    -- codewords under the *protocol's* `encode` and satisfies the linear constraint.  This is the
    -- faithful honest-opening relation — pinning the opener to `input.2` (rather than an
    -- existentially-quantified `M`) is load-bearing for completeness, since the honest prover sends
    -- `g = wit₀ + γ·wit₁` built from `input.2`, not from any other opener (defect #18, hEnc class).
    (∀ i, input.1.2 i = encode (input.2 i)) ∧
    ∀ i, ∑ j, input.2 i j * input.1.1.1 j =
      (if i = (0 : Fin 2) then input.1.1.2.1 else input.1.1.2.2)

omit [Fintype ι] in
/-- `honestInputRelation` is contained in `inputRelation` when the encoder's
image lies in `C` — i.e. honest opening is a *stronger* input hypothesis, so
completeness against `honestInputRelation` is the faithful (non-vacuous)
claim. (The converse fails, see the `honestInputRelation` docstring.) -/
theorem honestInputRelation_subset_inputRelation
    (C : Set (ι → F)) (encode : (Fin k → F) →ₗ[F] (ι → F))
    (h_mem : ∀ m, (encode m : ι → F) ∈ C) :
    honestInputRelation k C encode ⊆ inputRelation k C := by
  rintro ⟨⟨⟨v, μ₁, μ₂⟩, f⟩, wit⟩ ⟨hf, hM⟩
  refine ⟨wit, ⟨encode, h_mem, ?_⟩, ?_⟩
  · intro i; exact hf i
  · intro i
    have := hM i
    fin_cases i <;> simpa using this

/-- The IOR-shaped *relaxed* output relation derived from
`ToyProblem.relaxedRelation` (Definition 6.3). The soundness statement
of L6.6 is with respect to this relation: the verifier's "accept"
guarantee is that the input is `δ`-close to a valid `relation`-instance. -/
def outputRelation (C : Set (ι → F)) (δ : ℝ≥0) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    ToyProblem.relaxedRelation (k := k) (ℓ := 2) C δ input.1.1.1
      ![input.1.1.2.1, input.1.1.2.2] input.1.2

/-- The IOR-shaped **fixed-encoding** *relaxed* output relation (Definition 6.3).
The soundness statement of L6.6/6.8 is with respect to this: the verifier's
"accept" guarantee is that the input `(f₀, f₁)` is `δ`-close (on a common
agreement column set) to a valid instance `encode (M i)` for some constraint-
satisfying messages `M`. Uses the verifier's fixed plain `encode` (cf.
`ToyProblem.relaxedRelationFor`), and checks the witness component supplied by
the ArkLib knowledge extractor; this is a witness-bearing relation, not merely
language membership. -/
def outputRelationFor (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0) :
    Set ((Statement (F := F) k × (∀ i, OracleStatement ι F i)) ×
      Witness (F := F) k) :=
  fun input ↦
    (∀ i : Fin 2, ∑ j, input.2 i j * input.1.1.1 j =
      ![input.1.1.2.1, input.1.1.2.2] i) ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ i : Fin 2, ∀ j ∈ S, input.1.2 i j = encode (input.2 i) j

-- The 1-arity relaxed relation `R̃¹_{C,δ}` lives in
-- `Spec/SimplifiedIOR.lean :: outputRelation` (the C6.9 output relation).
-- We expose it from the simplified-IOR file rather than here so its
-- type signature aligns with `SimplifiedIOR.OutputStatement` /
-- `OutputOracleStatement` / `OutputWitness` rather than re-bundling.

/-! ### Rewinding extractor for Construction 6.2 (the 2-special-sound core)

The knowledge-soundness lemmas L6.6 / L6.8 / L6.10 are **2-special-soundness** arguments: the
extractor must obtain *two* accepting transcripts that share the prefix up to the combination-
randomness round and differ at the challenge `γ`, then solve a 2×2 linear system to recover the
message pair `(u₁, u₂)`. That requires **rewinding** the prover.

The in-tree `Verifier.knowledgeSoundness`
(`OracleReduction/Security/Basic.lean :: Verifier.knowledgeSoundness`, line 328) and
`Verifier.rbrKnowledgeSoundness`
(`OracleReduction/Security/RoundByRound.lean :: rbrKnowledgeSoundness`, line 811) both quantify
over a **single-run** extractor (`∃ E : Extractor.Straightline` / `∃ E : Extractor.RoundByRound`):
a single transcript and the logs of *one* execution, with **no black-box handle to re-invoke or
fork the prover**. The 2-special-sound rewinding extractor cannot be expressed through those
interfaces. This is the documented wall in
`research/proximity-prize/dispositions/oraclereduction-leftovers.md` (residual (1)+(2)) and in the
`ArkLib/ToMathlib/RewindingExtractor.lean` module docstring.

We therefore supply the genuine mathematical content — the 2-special-sound rewinding extractor for
the toy protocol — as a **fully-proven** `Extractor.knowledgeSoundnessViaRewinding` witness (the
rewinding-flavoured analogue of `Verifier.knowledgeSoundness`), and reduce the straightline holes
below to a single named bridge residual `Bridge.StraightlineOfRewinding`. -/

variable {k}

open Extractor in
/-- The combination map `g = u₁ + γ·u₂` (pointwise on `Fin k`): the honest prover's claim at
challenge `γ` from the underlying message pair `(u₁, u₂)`. -/
def toyCombine (γ : F) (u₁ u₂ : Fin k → F) : Fin k → F :=
  fun j ↦ u₁ j + γ * u₂ j

/-- Recovered second message `u₂ = (g₁ − g₂)/(γ₁ − γ₂)` from two claims at distinct challenges. -/
def toySolveSnd (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Fin k → F :=
  fun j ↦ (g₁ j - g₂ j) / (γ₁ - γ₂)

/-- Recovered first message `u₁ = g₁ − γ₁·u₂`. -/
def toySolveFst (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Fin k → F :=
  fun j ↦ g₁ j - γ₁ * toySolveSnd γ₁ γ₂ g₁ g₂ j

/-- The full 2×2 solve as a `Witness = Fin 2 → Fin k → F` (`row 0 = u₁`, `row 1 = u₂`): the witness
the rewinding extractor outputs from two accepting completions at distinct challenges. -/
def toySolve (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Witness (F := F) k :=
  ![toySolveFst γ₁ γ₂ g₁ g₂, toySolveSnd γ₁ γ₂ g₁ g₂]

/-- **Correctness of the `u₂` solve.** `toySolveSnd` inverts `toyCombine` on `γ₁ ≠ γ₂`. -/
theorem toySolveSnd_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolveSnd γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = u₂ := by
  funext j
  have hsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hγ
  simp only [toySolveSnd, toyCombine]
  field_simp
  ring

/-- **Correctness of the `u₁` solve.** `toySolveFst` inverts `toyCombine` on `γ₁ ≠ γ₂`. -/
theorem toySolveFst_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolveFst γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = u₁ := by
  funext j
  have hu₂ := congrFun (toySolveSnd_combine hγ u₁ u₂) j
  simp only [toySolveFst, toyCombine] at hu₂ ⊢
  rw [hu₂]
  ring

/-- **Full 2×2 solve correctness.** `toySolve` inverts `toyCombine` on distinct challenges:
from the two honest claims at `γ₁ ≠ γ₂` it recovers `![u₁, u₂]`. The algebraic heart of the toy
protocol's 2-special-sound extractor. -/
theorem toySolve_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolve γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = ![u₁, u₂] := by
  funext i
  fin_cases i
  · simpa [toySolve] using toySolveFst_combine hγ u₁ u₂
  · simpa [toySolve] using toySolveSnd_combine hγ u₁ u₂

/-- The recorded-prefix carrier for the rewinding extractor: the toy protocol's bundled input
statement (read off the recorded transcript prefix up to the `γ` round). -/
abbrev ToyPrefix (ι F : Type) (k : ℕ) : Type :=
  Statement (F := F) k × (∀ i, OracleStatement ι F i)

/-- Read the input statement off the recorded prefix; for the toy protocol the prefix *is* the
input, so this is the identity. -/
def toyStmtOf : ToyPrefix ι F k → ToyPrefix ι F k := id

/-- The concrete **rewinding extractor** for Construction 6.2 / 6.9: from the recorded prefix and
two completions `(γ₁, g₁)`, `(γ₂, g₂)`, return the 2×2 solve `toySolve γ₁ γ₂ g₁ g₂`. -/
def toyRewindingExtractor :
    Extractor.RewindingExtractor (ToyPrefix ι F k) F (Fin k → F) (Witness (F := F) k) :=
  fun _pre c₁ c₂ ↦ toySolve c₁.1 c₂.1 c₁.2 c₂.2

/-- The toy protocol's acceptance predicate for the rewinding extractor, parameterised by the
prefix-indexed decoded message pair `decode` held invariant by the fork (a single fork replays up
to the `γ` round from a *recorded prover state*, so the prover's internal message pair is fixed
across both completions — only `γ` is resampled). Completion `(γ, g)` at prefix `pre` is accepting
iff `g` is the honest `γ`-combination of `decode pre` and that pair places the input in
`outputRelation C δ` (the per-prefix MCA decode of ABF26 Remark 6.7). -/
def toyAccepts (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    ToyPrefix ι F k → Extractor.Accepts F (Fin k → F) :=
  fun pre c ↦
    (pre, (![(decode pre).1, (decode pre).2] : Witness (F := F) k))
        ∈ outputRelation (ι := ι) (F := F) k C δ ∧
      c.2 = toyCombine c.1 (decode pre).1 (decode pre).2

/-- **2-special-soundness of the toy rewinding extractor.** From any two accepting completions on
distinct challenges `γ₁ ≠ γ₂`, `toyRewindingExtractor` recovers a witness in `outputRelation`.
Both accepting completions are honest `γ`-combinations of the *same* prefix-fixed pair `decode pre`;
the 2×2 solve recovers exactly that pair via `toySolve_combine`, and membership transfers by
`rfl`. -/
theorem toyRewindingExtractor_twoSpecialSound (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    (toyRewindingExtractor (ι := ι) (F := F) (k := k)).TwoSpecialSound
      (outputRelation (ι := ι) (F := F) k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) := by
  rintro pre ⟨γ₁, g₁⟩ ⟨γ₂, g₂⟩ ⟨hmem, hg₁⟩ ⟨_, hg₂⟩ hγ
  -- `hg₁ : g₁ = toyCombine γ₁ (decode pre).1 (decode pre).2`, likewise `hg₂`; `hγ : γ₁ ≠ γ₂`.
  -- The extractor returns `toySolve γ₁ γ₂ g₁ g₂`; substitute the combinations and invert.
  have hg₁' : g₁ = toyCombine γ₁ (decode pre).1 (decode pre).2 := hg₁
  have hg₂' : g₂ = toyCombine γ₂ (decode pre).1 (decode pre).2 := hg₂
  have hγ' : γ₁ ≠ γ₂ := hγ
  show (pre, toySolve γ₁ γ₂ g₁ g₂) ∈ outputRelation (ι := ι) (F := F) k C δ
  rw [hg₁', hg₂', toySolve_combine hγ' (decode pre).1 (decode pre).2]
  exact hmem

/-- **Knowledge soundness via rewinding for Construction 6.2 (proven).** The toy protocol admits a
2-special-sound rewinding extractor, hence satisfies the framework's
`Extractor.knowledgeSoundnessViaRewinding` predicate against `outputRelation`. This is the
rewinding-flavoured analogue of `Verifier.knowledgeSoundness` whose absence blocked
`protocol62_knowledgeSound`. By `Extractor.knowledgeSoundnessViaRewinding.extracts`, whenever a
prover beats the 2-special-sound knowledge error `1/|F|` at a prefix, a valid witness is
extractable — no `sorry`, no `axiom`. -/
theorem protocol62_knowledgeSoundnessViaRewinding [Fintype F] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation (ι := ι) (F := F) k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  ⟨toyRewindingExtractor, toyRewindingExtractor_twoSpecialSound C δ decode⟩

/-! ### Honest prover, verifier, and reduction

This section mirrors the `foldProver` / `foldVerifier` / `foldOracleReduction`
pattern in [`Fri/Spec/SingleRound.lean`](../../../Fri/Spec/SingleRound.lean).
Because `OracleStatement ι F i = ι → F` is a plain function (not an
oracle that needs the `OracleQuery` machinery), we use the **non-oracle**
`Prover` / `Verifier` / `Reduction` triple with the oracle codewords
threaded through the bundled input `StmtIn = Statement × (∀ i, OracleStatement i)`.
This is sound — it's the same shape produced by
`OracleReduction.toReduction` — and avoids the `embed` / `hEq`
plumbing. The `OracleProver` / `OracleVerifier` flavour (the target of
the completeness and soundness statements) follows in the next section.
-/

section Protocol
variable [DecidableEq ι] [Fintype F] [DecidableEq F]

/-- Honest prover for Construction 6.2. After receiving the combination
randomness `γ`, the prover sends `g := M 0 + γ · M 1` (point-wise on
`Fin k`). The spot-check positions `xs` are not used by the prover —
they only feed the verifier's spot-check at the end.

State machine (`PrvState : Fin 4 → Type`):
  * `PrvState 0` — initial: the bundled `(stmt, oStmt) × witness`.
  * `PrvState 1, 2, 3` — same plus the combination randomness `γ`. -/
def prover :
    Prover []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure ((), ())

/-- The §6.1 decision predicate is decidable: it's a finite conjunction
of equalities in `F` (decidable via `DecidableEq F`) and a `Fin t`
universally-quantified equality (decidable via the `Fintype` `Decidable`
instance). Marking explicitly so the `verifier` below can stay
computable (cf. FRI's `foldVerifier`, which is plain `def`). -/
instance accepts.instDecidable
    (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (f : ∀ i, OracleStatement ι F i)
    (γ : F) (g : Fin k → F) (xs : Fin t → ι) :
    Decidable (accepts (k := k) (t := t) encode stmt f γ g xs) := by
  unfold accepts; infer_instance

/-- Honest verifier for Construction 6.2. Takes the bundled input
`(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂))` and the full transcript
`(γ, g, xs)`; accepts iff `accepts` holds for the supplied encoding.

Computable — `accepts` is decidable, so no `Classical.dec` is needed.
This mirrors FRI's `foldVerifier`, which is also a plain `def`. -/
def verifier (encode : (Fin k → F) → (ι → F)) :
    Verifier []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      OutputStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun ⟨stmt, oStmt⟩ tr ↦ do
    let γ : F := tr ⟨0, by decide⟩
    let g : Fin k → F := tr ⟨1, by decide⟩
    let xs : Fin t → ι := tr ⟨2, by decide⟩
    if accepts (k := k) (t := t) encode stmt oStmt γ g xs
    then pure () else failure

/-- Honest reduction for Construction 6.2: the package
`{prover, verifier}` over the bundled-input `Reduction` type. -/
def reduction (encode : (Fin k → F) → (ι → F)) :
    Reduction []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) (Witness (F := F) k)
      OutputStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := prover (ι := ι) (F := F) (k := k) (t := t)
  verifier := verifier (k := k) (t := t) encode

/-! ### Oracle-flavour prover, verifier, reduction

These are the `OracleProver` / `OracleVerifier` / `OracleReduction`
flavours of the same protocol, exposing `(f₁, f₂)` as oracle inputs
rather than bundling them into `StmtIn`. They match FRI/Sumcheck's
exact idiom and are necessary to make the *query complexity* of the
verifier explicit (`2t + 1` queries per execution: one for `g`, two
per spot-check).

The honest-completeness, knowledge-soundness, and round-by-round
knowledge-soundness lemmas below are all stated against these
oracle-flavour objects: completeness via
`OracleReduction.perfectCompleteness`, L6.6 via
`OracleVerifier.knowledgeSoundness`, and L6.8 via
`OracleVerifier.rbrKnowledgeSoundness`. The latter two are
definitionally `toVerifier.knowledgeSoundness` /
`toVerifier.rbrKnowledgeSoundness`, so the oracle-flavour statements
carry no extra proof burden over the bundled-input forms.

**Framework vacuity (KS) — RESOLVED 2026-06-11.** The historical trap —
`Verifier.knowledgeSoundness` admitted an always-failing `OptionT`
extractor that drove the bad-event probability to `0` — was fixed by
PR #569 (`fix/knowledge-soundness-failing-extractor`), now merged and
synced into this branch: extraction failure (`extractedWitIn? = none`)
is scored against the prover. The KS sorries below
(`protocol62_knowledgeSound`, and `simplifiedIOR_knowledgeSound` in
`Spec/SimplifiedIOR.lean`) may be closed on their mathematical merits.
`Verifier.rbrKnowledgeSoundness` was never affected, so
`protocol62_rbrKnowledgeSound` is provable as-is (and is the natural
first target; KS then follows via the rbrKS → KS implication).
-/

/-- Same as `prover` but exposed at the `OracleProver` signature. The
underlying `Prover` is identical (after the `OracleProver` type-alias
unfolds to a `Prover` on bundled in/out types). The output is the
trivial `(((), nofun), ())` since the IOR has no output oracle
statements (`OutputOracleStatement : Fin 0 → Type`). -/
def oracleProver :
    OracleProver []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  PrvState
  | ⟨0, _⟩ =>
      (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k
  | _ =>
      F × (Statement (F := F) k × (∀ i, OracleStatement ι F i)) × Witness (F := F) k

  input := id

  receiveChallenge
  | ⟨0, _⟩ => fun st ↦ pure <| fun (γ : F) ↦ (γ, st)
  | ⟨1, h⟩ => nomatch h
  | ⟨2, _⟩ => fun ⟨γ, st⟩ ↦ pure <| fun (_ : Fin t → ι) ↦ (γ, st)

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨γ, ⟨stmt, oStmt⟩, M⟩ ↦
      pure ((fun j ↦ M 0 j + γ * M 1 j), (γ, ⟨stmt, oStmt⟩, M))
  | ⟨2, h⟩ => nomatch h

  output := fun _ ↦ pure (((), nofun), ())

/-- Query helper: fetch the prover's combined-message claim `g`
(`pSpec` round 1 — the `P → V` direction). Mirrors FRI's `getConst`. -/
def queryG : OracleComp [(pSpec (ι := ι) (F := F) k t).Message]ₒ (Fin k → F) :=
  liftM <| OracleSpec.query
    (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
      ⟨⟨1, by rfl⟩, (by simpa using ())⟩)

/-- Query helper: read codeword `f i` at position `x : ι`. Mirrors
FRI's `queryCodeword`. -/
def queryF (i : Fin 2) (x : ι) : OracleComp [OracleStatement ι F]ₒ F :=
  liftM <| OracleSpec.query
    (show [OracleStatement ι F]ₒ.Domain from ⟨i, (by simpa using x)⟩)

/-- Oracle verifier for Construction 6.2.

Queries the prover's message `g` once and the two oracle codewords
`f₁, f₂` at each of the `t` spot-check positions (query complexity:
`2t + 1`), then `guard (accepts …)` to decide.

`embed` and `hEq` are trivial — `OutputOracleStatement : Fin 0 → Type`
is empty, so the output-oracle family is vacuously a subset of input
oracles + prover messages. -/
def oracleVerifier (encode : (Fin k → F) → (ι → F)) :
    OracleVerifier []ₒ
      (Statement (F := F) k) (OracleStatement ι F)
      OutputStatement OutputOracleStatement
      (pSpec (ι := ι) (F := F) k t) where
  verify := fun stmt challenges ↦ do
    let γ : F := challenges ⟨⟨0, by decide⟩, by rfl⟩
    let xs : Fin t → ι := challenges ⟨⟨2, by decide⟩, by rfl⟩
    -- Query the prover's message `g` (round-1 oracle, RIGHT family). The
    -- explicit `OptionT.lift <| OracleComp.liftComp (OracleComp.lift …)` form
    -- (matching `Sumcheck/Spec/SingleRound.lean`'s oracle verifier) makes the
    -- `simulateQ`-collapse lemmas fire syntactically.
    let g : Fin k → F ← OptionT.lift <| OracleComp.liftComp
      (OracleComp.lift <| OracleSpec.query
        (show [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain from
          ⟨⟨1, by rfl⟩, (by simpa using ())⟩)) _
    guard (∑ j, g j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    for j in (List.finRange t) do
      -- Query the two codewords (oracle statements, LEFT family).
      let f₀ : F ← OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <| OracleSpec.query
          (show [OracleStatement ι F]ₒ.Domain from ⟨0, (by simpa using xs j)⟩)) _
      let f₁ : F ← OptionT.lift <| OracleComp.liftComp
        (OracleComp.lift <| OracleSpec.query
          (show [OracleStatement ι F]ₒ.Domain from ⟨1, (by simpa using xs j)⟩)) _
      guard (encode g (xs j) = f₀ + γ * f₁)
    pure ()
  embed := ⟨fun i ↦ i.elim0, fun a _ _ ↦ a.elim0⟩
  hEq := fun i ↦ i.elim0

/-- Honest oracle reduction for Construction 6.2: the
`OracleProver` / `OracleVerifier` pair packaged as `OracleReduction`. -/
def oracleReduction (encode : (Fin k → F) → (ι → F)) :
    OracleReduction []ₒ
      (Statement (F := F) k) (OracleStatement ι F) (Witness (F := F) k)
      OutputStatement OutputOracleStatement OutputWitness
      (pSpec (ι := ι) (F := F) k t) where
  prover := oracleProver (ι := ι) (F := F) (k := k) (t := t)
  verifier := oracleVerifier (k := k) (t := t) encode

/-! ### `simulateQ`-collapse toolkit for the compiled oracle verifier

The honest-completeness proof needs a *closed form* for the `simulateQ`-image of the compiled
oracle verifier (`oracleVerifier.toVerifier`), i.e. the verifier run with its message- and
oracle-statement queries resolved against the honest prover messages / input codewords. The
collapse follows the same `simulateQ`-pushing recipe as
`Sumcheck/Spec/SingleRound.lean :: simulateQ_oracleVerify_eq`, generalised here to a verifier whose
spot-check phase is a `forIn` loop over `Fin t` (so we additionally need an
`OptionT`-`forIn`/`guard` transport, à la `Binius/BinaryBasefold/QueryPhase.lean :: ForInSupport`,
re-derived in-file to keep `ToyProblem` self-contained). -/

/-- `answer` of the default oracle interface is the identity (the message itself). -/
@[simp] lemma answer_instDefault {M : Type _} (m : M) (q : Unit) :
    @OracleInterface.answer M OracleInterface.instDefault m q = m := rfl

section SimulateQTransport
variable {ι' : Type} {spec : OracleSpec ι'} {m : Type → Type} [Monad m] [LawfulMonad m]
variable {α β : Type}

/-- `simulateQ` commutes with `OptionT.pure`. -/
theorem simulateQ_optionT_pure (impl : QueryImpl spec m) (b : β) :
    simulateQ impl (pure b : OptionT (OracleComp spec) β) = (pure b : OptionT m β) := by
  rw [show (pure b : OptionT (OracleComp spec) β) = OptionT.lift (pure b)
        from (OptionT.lift_pure b).symm]
  rw [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure]

/-- `simulateQ` commutes with `OptionT` `failure`. -/
theorem simulateQ_optionT_failure (impl : QueryImpl spec m) :
    simulateQ impl (failure : OptionT (OracleComp spec) β) = (failure : OptionT m β) := by
  rw [OracleComp.failure_def]
  apply OptionT.ext
  simp only [OptionT.run_mk, simulateQ_pure, OptionT.fail]
  rfl

/-- `simulateQ` of a query-free `guard` is the (target-monad) `if`. -/
theorem simulateQ_optionT_guard (impl : QueryImpl spec m) (P : Prop) [Decidable P] :
    simulateQ impl (guard P : OptionT (OracleComp spec) PUnit)
      = (if P then pure PUnit.unit else failure : OptionT m PUnit) := by
  rw [guard_eq]
  by_cases hP : P
  · rw [if_pos hP, if_pos hP, simulateQ_optionT_pure]
  · rw [if_neg hP, if_neg hP, simulateQ_optionT_failure]

/-- `simulateQ` commutes with `forIn` over a list in `OptionT (OracleComp …)`: the simulated loop
equals the loop with the simulated body. The missing `simulateQ_forIn` for the `OptionT` stack. -/
theorem simulateQ_optionT_forIn (impl : QueryImpl spec m)
    (l : List α) (f : α → β → OptionT (OracleComp spec) (ForInStep β))
    (g : α → β → OptionT m (ForInStep β))
    (hg : ∀ a b, g a b = simulateQ impl (f a b)) :
    ∀ init : β,
      simulateQ impl (forIn l init f : OptionT (OracleComp spec) β)
        = (forIn l init g : OptionT m β) := by
  induction l with
  | nil =>
    intro init
    rw [List.forIn_nil, List.forIn_nil, simulateQ_optionT_pure]
  | cons a l ih =>
    intro init
    rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind, hg]
    refine bind_congr ?_
    intro step
    cases step with
    | done b => exact simulateQ_optionT_pure impl b
    | yield b => exact ih b

/-- A `forIn` over a list whose body is `guard (Q a)` then `yield ()` collapses to
`if (∀ a ∈ l, Q a) then pure () else failure`: the spot-check loop accepts iff every per-element
guard passes. -/
theorem forIn_guard_eq (l : List α) (Q : α → Prop) [∀ a, Decidable (Q a)]
    (body : α → PUnit → OptionT (OracleComp spec) (ForInStep PUnit))
    (hbody : ∀ a u, body a u = (guard (Q a) >>= fun _ => pure (ForInStep.yield PUnit.unit))) :
    (forIn l PUnit.unit body : OptionT (OracleComp spec) PUnit)
      = (if (∀ a ∈ l, Q a) then pure PUnit.unit else failure) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons, hbody]
    by_cases hQa : Q a
    · rw [guard_eq, if_pos hQa]
      simp only [pure_bind]
      rw [ih]
      by_cases hrest : (∀ b ∈ l, Q b)
      · rw [if_pos hrest, if_pos]
        intro b hb
        rcases List.mem_cons.mp hb with h | h
        · exact h ▸ hQa
        · exact hrest b h
      · rw [if_neg hrest, if_neg (fun hall =>
          hrest (fun b hb => hall b (List.mem_cons_of_mem a hb)))]
    · rw [guard_eq, if_neg hQa,
        if_neg (fun hall => hQa (hall a (List.mem_cons_self)))]
      simp [failure_bind]

end SimulateQTransport

section SimOracle2Query
open OracleInterface
variable {ιₒ : Type} {oSpec : OracleSpec ιₒ}
  {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]

/-- `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family. -/
lemma simulateQ_simOracle2_messageQuery (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₂]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₂]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inr qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₂ t₂ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family. -/
lemma simulateQ_simOracle2_leftQuery_oc (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₁]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inl qm)))) = _
  rw [simulateQ_spec_query]
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₁ t₁ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- Verify-body message-query collapse: the `OptionT.lift <| liftComp <| lift query` form that
appears verbatim in `oracleVerifier.verify`, simulated via `simOracle2`, collapses to `pure` of the
message `answer`. -/
lemma simulateQ_simOracle2_messageQuery_optionT (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₂]ₒ).Domain) :
    (simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (OptionT.lift (OracleComp.liftComp (OracleComp.lift (OracleSpec.query qm))
        (oSpec + ([T₁]ₒ + [T₂]ₒ))))
      : OptionT (OracleComp oSpec) _)
      = (pure (OracleInterface.answer (t₂ qm.1) qm.2) : OptionT (OracleComp oSpec) _) := by
  erw [simulateQ_optionT_lift]
  rw [OracleComp.liftComp_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [simulateQ_simOracle2_messageQuery]
  rfl

/-- Verify-body oracle-statement-query collapse (LEFT family). -/
lemma simulateQ_simOracle2_leftQuery_optionT (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    (simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (OptionT.lift (OracleComp.liftComp (OracleComp.lift (OracleSpec.query qm))
        (oSpec + ([T₁]ₒ + [T₂]ₒ))))
      : OptionT (OracleComp oSpec) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OptionT (OracleComp oSpec) _) := by
  erw [simulateQ_optionT_lift]
  rw [OracleComp.liftComp_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [simulateQ_simOracle2_leftQuery_oc]
  rfl

end SimOracle2Query

set_option maxHeartbeats 2000000 in
/-- **Closed form of the compiled toy-problem oracle verifier.** Simulating
`oracleVerifier.verify` against the honest input codewords `oStmt` and prover messages `msgs`
(via `OracleInterface.simOracle2`) collapses every query — the message query for `g` and the
`2t` spot-check codeword queries — to the corresponding honest values, leaving a query-free
`OptionT` computation that is exactly `if accepts … then pure () else failure`.

This is the load-bearing lemma for honest completeness: composed with `accepts_of_inputRelation`
it shows the compiled verifier never fails on an honest transcript. -/
theorem simulateQ_oracleVerify_eq (encode : (Fin k → F) → (ι → F))
    (stmt : Statement (F := F) k) (oStmt : ∀ i, OracleStatement ι F i)
    (chal : ∀ i, (pSpec (ι := ι) (F := F) k t).Challenge i)
    (msgs : ∀ i, (pSpec (ι := ι) (F := F) k t).Message i) :
    simulateQ (OracleInterface.simOracle2 ([]ₒ) oStmt msgs)
      ((oracleVerifier (ι := ι) (F := F) (k := k) (t := t) encode).verify stmt chal)
      = (if accepts (k := k) (t := t) encode stmt oStmt
            (chal ⟨⟨0, by decide⟩, by rfl⟩) (msgs ⟨1, by rfl⟩) (chal ⟨⟨2, by decide⟩, by rfl⟩)
          then (pure () : OptionT (OracleComp []ₒ) Unit) else failure) := by
  unfold oracleVerifier
  dsimp only
  rw [simulateQ_optionT_bind]
  erw [simulateQ_simOracle2_messageQuery_optionT (T₁ := OracleStatement ι F)
    (T₂ := (pSpec (ι := ι) (F := F) k t).Message) (oSpec := []ₒ) oStmt msgs ⟨⟨1, by rfl⟩, id ()⟩]
  dsimp only [Sigma.fst, Sigma.snd]
  erw [pure_bind]
  rw [simulateQ_optionT_bind, simulateQ_optionT_guard, simulateQ_optionT_bind]
  rw [simulateQ_optionT_forIn (impl := OracleInterface.simOracle2 ([]ₒ) oStmt msgs)
    (g := fun (j : Fin t) (_ : PUnit) =>
      (do let γ : F := chal ⟨⟨0, by decide⟩, by rfl⟩
          let xs : Fin t → ι := chal ⟨⟨2, by decide⟩, by rfl⟩
          let g₀ : Fin k → F := OracleInterface.answer (msgs ⟨1, by rfl⟩) (id ())
          let _ ← (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F)
          let _ ← (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F)
          guard (encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j))
          pure (ForInStep.yield PUnit.unit)))]
  swap
  · -- forIn body collapse: the f₀, f₁ codeword queries collapse to `pure (oStmt …)`.
    intro j _
    symm
    rw [simulateQ_optionT_bind]
    erw [simulateQ_simOracle2_leftQuery_optionT (T₁ := OracleStatement ι F)
      (T₂ := (pSpec (ι := ι) (F := F) k t).Message) (oSpec := []ₒ) oStmt msgs
      (⟨0, chal ⟨⟨2, by decide⟩, by rfl⟩ j⟩ : [OracleStatement ι F]ₒ.Domain)]
    dsimp only [Sigma.fst, Sigma.snd]
    erw [pure_bind]
    rw [simulateQ_optionT_bind]
    erw [simulateQ_simOracle2_leftQuery_optionT (T₁ := OracleStatement ι F)
      (T₂ := (pSpec (ι := ι) (F := F) k t).Message) (oSpec := []ₒ) oStmt msgs
      (⟨1, chal ⟨⟨2, by decide⟩, by rfl⟩ j⟩ : [OracleStatement ι F]ₒ.Domain)]
    dsimp only [Sigma.fst, Sigma.snd]
    erw [pure_bind]
    rw [simulateQ_optionT_bind, simulateQ_optionT_guard, simulateQ_optionT_pure]
    rfl
  -- The loop body reduces (pure-binds) to `guard Q_j >>= yield`; collapse via `forIn_guard_eq`.
  rw [forIn_guard_eq (l := List.finRange t)
      (Q := fun j =>
        let γ : F := chal ⟨⟨0, by decide⟩, by rfl⟩
        let xs : Fin t → ι := chal ⟨⟨2, by decide⟩, by rfl⟩
        let g₀ : Fin k → F := OracleInterface.answer (msgs ⟨1, by rfl⟩) (id ())
        encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j))]
  · -- Combine the linear-constraint `if` and the spot-check `if` into `if accepts`.
    set γ : F := chal ⟨⟨0, by decide⟩, by rfl⟩ with hγ
    set xs : Fin t → ι := chal ⟨⟨2, by decide⟩, by rfl⟩ with hxs
    simp only [answer_instDefault, simulateQ_optionT_pure]
    set g₀ : Fin k → F := msgs ⟨1, by rfl⟩ with hg₀
    have hQ : (∀ a ∈ List.finRange t,
          encode g₀ (xs a) = oStmt 0 (xs a) + γ * oStmt 1 (xs a))
        ↔ (∀ j : Fin t, encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :=
      ⟨fun h j => h j (List.mem_finRange j), fun h a _ => h a⟩
    simp only [hQ]
    unfold accepts
    by_cases hlin : (∑ j, g₀ j * stmt.1 j = stmt.2.1 + γ * stmt.2.2)
    · rw [if_pos hlin]
      by_cases hsc : ∀ j : Fin t,
          encode g₀ (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)
      · rw [if_pos hsc, if_pos (And.intro hlin hsc), pure_bind, pure_bind]
      · rw [if_neg hsc, if_neg (fun h => hsc h.2), pure_bind, failure_bind]
    · rw [if_neg hlin, failure_bind, if_neg (fun h => hlin h.1)]
  · intro j u
    simp only [pure_bind]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Honest completeness for ABF26 Construction 6.2, point form: if
`((v, μ₁, μ₂), (f₁, f₂))` lies in `inputRelation` with the underlying
messages `M = (M₀, M₁)` (and `fᵢ` is the `encode`-image of `Mᵢ`), then
for any verifier challenges `(γ, xs)` the §6.1 decision `accepts` holds
against the honest prover's message `g = M₀ + γ · M₁`.

This is the point-form companion to the
`OracleReduction.perfectCompleteness` theorem that wraps the prover and
verifier objects below. -/
theorem accepts_of_inputRelation {k t : ℕ}
    {encode : (Fin k → F) →ₗ[F] (ι → F)}
    (stmt : Statement (F := F) k)
    (M : Witness (F := F) k)
    (hM : ∀ i, ∑ j, M i j * stmt.1 j =
        (if i = (0 : Fin 2) then stmt.2.1 else stmt.2.2))
    (f : ∀ i, OracleStatement ι F i)
    (hf : ∀ i, f i = encode (M i))
    (γ : F) (xs : Fin t → ι) :
    accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → F)))
      stmt f γ (fun j ↦ M 0 j + γ * M 1 j) xs := by
  refine ⟨?_, ?_⟩
  · -- Linear-constraint: ∑ j, (M 0 j + γ * M 1 j) * v j = μ₁ + γ * μ₂.
    have h0 : ∑ j, M 0 j * stmt.1 j = stmt.2.1 := by
      have := hM 0; simpa using this
    have h1 : ∑ j, M 1 j * stmt.1 j = stmt.2.2 := by
      have := hM 1
      have hne : (1 : Fin 2) ≠ 0 := by decide
      simpa [if_neg hne] using this
    calc ∑ j, (M 0 j + γ * M 1 j) * stmt.1 j
        = ∑ j, (M 0 j * stmt.1 j + γ * (M 1 j * stmt.1 j)) := by
          apply Finset.sum_congr rfl; intros j _; ring
      _ = (∑ j, M 0 j * stmt.1 j) + ∑ j, γ * (M 1 j * stmt.1 j) :=
          Finset.sum_add_distrib
      _ = (∑ j, M 0 j * stmt.1 j) + γ * ∑ j, M 1 j * stmt.1 j := by
          rw [← Finset.mul_sum]
      _ = stmt.2.1 + γ * stmt.2.2 := by rw [h0, h1]
  · -- Spot-check: encode(g) x = f 0 x + γ * f 1 x.
    intro j
    have hg_eq : (fun i ↦ M 0 i + γ * M 1 i) = M 0 + γ • M 1 := by
      funext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hg_eq, map_add, map_smul, hf 0, hf 1]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- The honest oracle verifier's body, simulated through `simOracle2` against the prover's
messages `msgs` and the input codewords `oStmt`, resolves to `pure (some ())` whenever the two
accept conditions hold for the supplied challenge `γ`, spot-check positions `xs`, and prover
message `g = msgs ⟨1, rfl⟩`:

  * `hAcc1`: the linear-constraint check `∑ j, g j · v j = μ₁ + γ · μ₂`, and
  * `hAcc2`: the per-spot-check `encode g (xs j) = f₀(xs j) + γ · f₁(xs j)`.

This is the monadic core of `oracleReduction_perfectCompleteness`: the residual support obligation
after the `Pr[…] = 1` goal is reduced via `OptionT.probEvent_eq_one_of_simulateQ_support_bind`
forces every honest-run output to be `some` of an accepting output, which this lemma certifies by
resolving each query (the prover claim `g` and the `2t` codeword reads) against `simOracle2` and
discharging both guards. The query/loop routing uses the staged `simulateQ`/`OptionT` toolkit
(`OracleComp.monadLift_liftM_OptionT`, `simulateQ_optionT_bind`/`_lift`,
`simulateQ_optionT_forIn_yield_pure_some`); the `change`/`conv` steps bridge the definitional —
but not syntactic — equalities between the elaborated verifier's `MonadLift`/`ForIn` instance
trees and the toolkit lemmas' canonical spellings. -/
lemma verifierBody_simulateQ_eq_pure
    (encode : (Fin k → F) → (ι → F))
    (oStmt : (i : Fin 2) → OracleStatement ι F i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι)
    (hAcc1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2)
    (hAcc2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
      = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : F ← liftM (queryF (ι := ι) (F := F) 0 (xs j))
            let f₁ : F ← liftM (queryF (ι := ι) (F := F) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ * f₁)
        : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (some ()) := by
  -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
  rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
      = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
        (OracleComp.monadLift_liftM_OptionT _).symm]
  simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (F := F) i x) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) F)
      = OptionT.lift (liftM (queryF (ι := ι) (F := F) i x) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) F) from
        fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
  -- Push `simulateQ` through the OptionT bind / lift / map structure.
  simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
    queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
  -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
  conv_lhs =>
    enter [1, 1]
    change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
    rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
        QueryImpl.liftTarget (OracleComp []ₒ)
          ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
            (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
      (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
        [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
  rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
      = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
  -- Guard 1 passes (hAcc1): `guard True = pure ()`, then `simulateQ impl (pure …) = pure …`.
  rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
        OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = pure PUnit.unit from by rw [hAcc1]; simp [guard]]
  conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
      = OptionT.lift (pure PUnit.unit) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_pure]
  rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
      = pure PUnit.unit from rfl, pure_bind]
  -- Resolve the spot-check `forIn` to `pure (some ())` via the yield-pure induction lemma.
  -- `hForIn`'s type is checked against the goal-shaped equation by `isDefEq` (bridging the
  -- lift-instance gaps); a `conv … change` then re-spells the goal's loop to `hForIn`'s LHS.
  have hForIn :
      simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
            : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      = (pure (some PUnit.unit) : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
    apply simulateQ_optionT_forIn_yield_pure_some
    intro j
    simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
    -- Resolve the two `queryF` reads (`f₀ = oStmt 0 (xs j)`, `f₁ = oStmt 1 (xs j)`) by defeq.
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
        = (pure (oStmt 0 (xs j)) : OracleComp []ₒ F) from rfl]
    rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) F)
        = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
        = (pure (oStmt 1 (xs j)) : OracleComp []ₒ F) from rfl]
    rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) F)
        = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
    -- Guard passes by hAcc2; then `simulateQ impl (pure …) = pure …`.
    rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = pure PUnit.unit from by rw [hAcc2 j]; simp [guard]]
    conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
          ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = OptionT.lift (pure PUnit.unit) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure,
      show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
        = pure PUnit.unit from rfl, pure_bind]
    -- Trailing `(pure ∘ yield) unit = pure (yield unit)`, simulated to `pure (some (yield unit))`.
    change simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
        ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
          (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
    conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
        = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
    rw [simulateQ_optionT_lift, simulateQ_pure]
    rfl
  -- Collapse the loop. The goal's bound `simulateQ … (forIn …)` is defeq to `hForIn`'s LHS but
  -- not `rw`-matchable (the `ForIn`/`MonadLift` instance trees differ syntactically). A
  -- `conv … change` re-spells the focused loop as `hForIn`'s exact LHS (the universes are pinned
  -- to `0` by the `emptySpec.{0,0}` ascription in the statement), after which `rw [hForIn]` fires.
  conv_lhs =>
    enter [1]
    change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
        ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
          (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
            OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
              guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
            : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
  rw [hForIn]
  -- After collapsing the loop the goal is `(pure (some ()) : OracleComp []ₒ _) >>= …`; the bind
  -- runs the constant `(pure ∘ id)` continuation, leaving
  -- `simulateQ impl (pure ()) = pure (some ())`.
  change ((pure (some PUnit.unit) : OracleComp []ₒ (Option PUnit)) >>= fun _ ↦
      simulateQ (OracleInterface.simOracle2 []ₒ oStmt msgs)
        ((pure PUnit.unit : OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit) :
          OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Option PUnit))) = _
  rw [pure_bind]
  exact simulateQ_pure _ (some PUnit.unit)

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- Two-sided (`ite`) companion of `verifierBody_simulateQ_eq_pure`: the simulated verifier
body is the **deterministic** computation `pure (some ())` when both §6.1 accept conditions
hold for the supplied challenge `γ`, prover message `msgs ⟨1, rfl⟩`, and spot-check positions
`xs`, and `pure none` otherwise (a failed `guard` propagates through the remaining `OptionT`
binds, short-circuiting the spot-check loop).

The accepting direction delegates to `verifierBody_simulateQ_eq_pure`; the failing directions
re-run the same defeq bridges (see that lemma's docstring for the toolkit) and collapse the
failed `guard` via `simulateQ_optionT_failure` / `OptionT.failure_bind`, using
`simulateQ_optionT_forIn_yield_pure_none` for a failure inside the spot-check `forIn`. This is
the monadic core of the soundness direction (`accepts_of_mem_support_verifier_run` below):
a successful simulated run forces both accept conditions. -/
lemma verifierBody_simulateQ_eq_pure_ite
    (encode : (Fin k → F) → (ι → F))
    (oStmt : (i : Fin 2) → OracleStatement ι F i)
    (msgs : (j : (pSpec (ι := ι) (F := F) k t).MessageIdx) →
      (pSpec (ι := ι) (F := F) k t).Message j)
    (stmt1 : Fin k → F) (mu1 mu2 : F) (γ : F) (xs : Fin t → ι) :
    simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
      (do
        let g : Fin k → F ← liftM (queryG (ι := ι) (F := F) (k := k) (t := t))
        guard (∑ j, g j * stmt1 j = mu1 + γ * mu2)
        (fun _ ↦ ()) <$>
          forIn (List.finRange t) PUnit.unit fun j _ ↦ do
            let f₀ : F ← liftM (queryF (ι := ι) (F := F) 0 (xs j))
            let f₁ : F ← liftM (queryF (ι := ι) (F := F) 1 (xs j))
            (fun _ ↦ ForInStep.yield PUnit.unit) <$>
              guard (encode g (xs j) = f₀ + γ * f₁)
        : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) Unit)
      = pure (if (∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2) ∧
            (∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
              = oStmt 0 (xs j) + γ * oStmt 1 (xs j))
          then some () else none) := by
  by_cases h1 : ∑ j, (msgs ⟨1, rfl⟩) j * stmt1 j = mu1 + γ * mu2
  case pos =>
    by_cases h2 : ∀ j : Fin t, encode (msgs ⟨1, rfl⟩) (xs j)
        = oStmt 0 (xs j) + γ * oStmt 1 (xs j)
    case pos =>
      rw [if_pos ⟨h1, h2⟩]
      exact verifierBody_simulateQ_eq_pure (k := k) (t := t)
        encode oStmt msgs stmt1 mu1 mu2 γ xs h1 h2
    case neg =>
      rw [if_neg (fun hc ↦ h2 hc.2)]
      -- Bridge each OptionT-lifted query helper to `OptionT.lift` of its OracleComp lift.
      rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
          = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
              OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
            (OracleComp.monadLift_liftM_OptionT _).symm]
      simp only [show ∀ (i : Fin 2) (x : ι), (liftM (queryF (ι := ι) (F := F) i x) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) F)
          = OptionT.lift (liftM (queryF (ι := ι) (F := F) i x) :
              OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) F) from
            fun i x ↦ (OracleComp.monadLift_liftM_OptionT _).symm]
      -- Push `simulateQ` through the OptionT bind / lift / map structure.
      simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
        queryG, queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
      -- Resolve the `g`-query to its oracle answer `msgs ⟨1, rfl⟩` by defeq.
      conv_lhs =>
        enter [1, 1]
        change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
            QueryImpl.liftTarget (OracleComp []ₒ)
              ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
          (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
        rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
            QueryImpl.liftTarget (OracleComp []ₒ)
              ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
          (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
          = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
      rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
          = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
      -- Guard 1 passes (h1): `guard True = pure ()`, then collapse the simulated pure.
      rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
            OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
          = pure PUnit.unit from by rw [h1]; simp [guard]]
      conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
            ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
          = OptionT.lift (pure PUnit.unit) from rfl]
      rw [simulateQ_optionT_lift, simulateQ_pure]
      rw [show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
          = pure PUnit.unit from rfl, pure_bind]
      -- Collapse the spot-check `forIn` to `pure none` (some spot check fails, by `h2`).
      have hForIn :
          simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
                OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
                : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
          = (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit)) := by
        refine simulateQ_optionT_forIn_yield_pure_none _ _ _ _
          (fun j ↦ encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j))
          (fun j ↦ ?_) (fun hall ↦ h2 (fun j ↦ hall j (List.mem_finRange j)))
        simp only [simulateQ_optionT_bind, simulateQ_optionT_lift,
          queryF, OracleInterface.simOracle2, QueryImpl.addLift_def]
        -- Resolve the two `queryF` reads (`f₀`, `f₁`) by defeq, as in the `some` direction.
        conv_lhs =>
          enter [1, 1]
          change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
          rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨0, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
            = (pure (oStmt 0 (xs j)) : OracleComp []ₒ F) from rfl]
        rw [show (OptionT.lift (pure (oStmt 0 (xs j))) : OptionT (OracleComp []ₒ) F)
            = (pure (oStmt 0 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
        conv_lhs =>
          enter [1, 1]
          change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
          rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
              QueryImpl.liftTarget (OracleComp []ₒ)
                ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
                  (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
            (Sum.inr (Sum.inl (⟨1, xs j⟩ : [OracleStatement ι F]ₒ.Domain)))
            = (pure (oStmt 1 (xs j)) : OracleComp []ₒ F) from rfl]
        rw [show (OptionT.lift (pure (oStmt 1 (xs j))) : OptionT (OracleComp []ₒ) F)
            = (pure (oStmt 1 (xs j)) : OptionT (OracleComp []ₒ) F) from rfl, pure_bind]
        -- Per-spot-check guard: passes or fails according to `cond j`.
        by_cases hj : encode (msgs ⟨1, rfl⟩) (xs j) = oStmt 0 (xs j) + γ * oStmt 1 (xs j)
        · rw [if_pos hj]
          rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j)
                = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = pure PUnit.unit from by rw [hj]; simp [guard]]
          conv_lhs => enter [1]; rw [show (pure PUnit.unit : OptionT (OracleComp ([]ₒ +
                ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = OptionT.lift (pure PUnit.unit) from rfl]
          rw [simulateQ_optionT_lift, simulateQ_pure,
            show (OptionT.lift (pure PUnit.unit) : OptionT (OracleComp []ₒ) PUnit)
              = pure PUnit.unit from rfl, pure_bind]
          change simulateQ _ ((pure (ForInStep.yield PUnit.unit) : OptionT (OracleComp ([]ₒ +
              ([OracleStatement ι F]ₒ + [(pSpec (ι := ι) (F := F) k t).Message]ₒ)))
                (ForInStep PUnit)) : OracleComp _ (Option (ForInStep PUnit))) = _
          conv_lhs => rw [show (pure (ForInStep.yield PUnit.unit) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (ForInStep PUnit))
              = OptionT.lift (pure (ForInStep.yield PUnit.unit)) from rfl]
          rw [simulateQ_optionT_lift, simulateQ_pure]
          rfl
        · rw [if_neg hj]
          rw [show (guard (encode (msgs ⟨1, rfl⟩) (xs j)
                = oStmt 0 (xs j) + γ * oStmt 1 (xs j)) :
                OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
                  [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
              = failure from by simp only [guard, if_neg hj]]
          rw [simulateQ_optionT_failure, OptionT.failure_bind]
          rfl
      -- Re-spell the goal's loop to `hForIn`'s LHS and collapse; failure then propagates.
      conv_lhs =>
        enter [1]
        change simulateQ (OracleInterface.simOracle2 (emptySpec.{0, 0}) oStmt msgs)
            ((forIn (List.finRange t) PUnit.unit fun (j : Fin t) (_ : PUnit) ↦
              (OptionT.lift (liftM (queryF (ι := ι) (F := F) 0 (xs j))) >>= fun f₀ ↦
                OptionT.lift (liftM (queryF (ι := ι) (F := F) 1 (xs j))) >>= fun f₁ ↦
                  guard (encode (msgs ⟨1, rfl⟩) (xs j) = f₀ + γ * f₁) >>=
                    pure ∘ fun _ ↦ ForInStep.yield PUnit.unit)
                : OptionT (OracleComp (emptySpec.{0, 0} + ([OracleStatement ι F]ₒ +
                    [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit))
      rw [hForIn]
      rw [show (pure none : OracleComp (emptySpec.{0, 0}) (Option PUnit))
          = ((failure : OptionT (OracleComp (emptySpec.{0, 0})) PUnit) :
              OracleComp (emptySpec.{0, 0}) (Option PUnit)) from rfl,
        OptionT.failure_bind]
  case neg =>
    rw [if_neg (fun hc ↦ h1 hc.1)]
    -- Bridge the `g`-query, resolve it by defeq, then fail on the linear-constraint guard.
    rw [show (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) (Fin k → F))
        = OptionT.lift (liftM (queryG (ι := ι) (F := F) (k := k) (t := t)) :
            OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
              [(pSpec (ι := ι) (F := F) k t).Message]ₒ)) (Fin k → F)) from
          (OracleComp.monadLift_liftM_OptionT _).symm]
    simp only [map_eq_bind_pure_comp, simulateQ_optionT_bind, simulateQ_optionT_lift,
      queryG, OracleInterface.simOracle2, QueryImpl.addLift_def]
    conv_lhs =>
      enter [1, 1]
      change (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
      rw [show (QueryImpl.liftTarget (OracleComp []ₒ) (QueryImpl.id []ₒ) +
          QueryImpl.liftTarget (OracleComp []ₒ)
            ((OracleInterface.simOracle0 (OracleStatement ι F) oStmt).add
              (OracleInterface.simOracle0 (pSpec (ι := ι) (F := F) k t).Message msgs)))
        (Sum.inr (Sum.inr (⟨⟨1, rfl⟩, id ()⟩ :
          [(pSpec (ι := ι) (F := F) k t).Message]ₒ.Domain)))
        = (pure (msgs ⟨1, rfl⟩) : OracleComp []ₒ (Fin k → F)) from rfl]
    rw [show (OptionT.lift (pure (msgs ⟨1, rfl⟩)) : OptionT (OracleComp []ₒ) (Fin k → F))
        = (pure (msgs ⟨1, rfl⟩) : OptionT (OracleComp []ₒ) (Fin k → F)) from rfl, pure_bind]
    rw [show (guard (∑ j, msgs ⟨1, rfl⟩ j * stmt1 j = mu1 + γ * mu2) :
          OptionT (OracleComp ([]ₒ + ([OracleStatement ι F]ₒ +
            [(pSpec (ι := ι) (F := F) k t).Message]ₒ))) PUnit)
        = failure from by simp only [guard, if_neg h1]]
    rw [simulateQ_optionT_failure, OptionT.failure_bind]
    rfl

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- **Soundness direction of the verifier-run support characterization** (converse companion
of the completeness-side `verifierBody_simulateQ_eq_pure`): if the simulated run of the C6.2
oracle verifier (routed through `toVerifier` / `simOracle2`, then through an arbitrary
empty-spec `impl`) on a **fixed** full transcript `tr` can succeed — `some _` lies in the run's
support — then the §6.1 decision predicate `accepts` holds for that transcript's challenge
`γ = tr 0`, prover message `g = tr 1`, and spot-check positions `xs = tr 2`.

Proof: the empty-spec simulation can only shrink support
(`support_simulateQ_run'_subset`), and after `toVerifier` routing the verifier body is the
deterministic `pure (if accepts-conditions then some () else none)`
(`verifierBody_simulateQ_eq_pure_ite`), so a `some` in the support forces the condition. -/
lemma accepts_of_mem_support_verifier_run
    {σ : Type} (impl : QueryImpl []ₒ (StateT σ ProbComp)) (s₀ : σ)
    (encode : (Fin k → F) → (ι → F))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    {y : OutputStatement × (∀ i, OutputOracleStatement i)}
    (hy : some y ∈ support ((simulateQ impl
        (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run' s₀)) :
    accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  -- Drop the `impl` simulation layer (an empty-spec impl can only shrink the support).
  have hy' := support_simulateQ_run'_subset impl _ s₀ hy
  -- Expose the `toVerifier`-routed verifier body and collapse it to its `ite` normal form.
  simp only [OracleVerifier.toVerifier, oracleVerifier, Verifier.run, bind_pure_comp] at hy'
  rw [verifierBody_simulateQ_eq_pure_ite (encode := encode) (stmt1 := stmtIn.1.1)
      (mu1 := stmtIn.1.2.1) (mu2 := stmtIn.1.2.2)] at hy'
  -- Peel the trailing output-assembly bind; a `none` head contradicts `some y` in the support.
  rcases OptionT.mem_support_run_bind _ _ hy' with ⟨hnone, hcontra⟩ | ⟨a, ha, _⟩
  · exact absurd hcontra (by simp)
  · have ha := OracleComp.eq_of_mem_support_pure _ ha
    split at ha
    · rename_i hcond
      exact hcond
    · exact absurd ha (by simp)

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- Round-by-round-framework wrapper for `accepts_of_mem_support_verifier_run`, consuming the
exact hypothesis shape that `KnowledgeStateFunction.toFun_full`
(`ArkLib/OracleReduction/Security/RoundByRound.lean`) provides for the C6.2 oracle verifier:
if the verifier's simulated run on a fixed transcript outputs, with positive probability, a
statement that is `relOut`-related to some `witOut` (for **any** `relOut`, in particular
`Set.univ`), then the §6.1 decision predicate `accepts` holds on that transcript. This is the
entry point for the L6.8 round-by-round knowledge-soundness state function: at the full
transcript it converts the framework's `Pr[…] > 0` acceptance hypothesis into the concrete
accept equations that the [ABF26] §6.2 argument consumes. -/
lemma accepts_of_probEvent_pos_verifier_run
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (encode : (Fin k → F) → (ι → F))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (tr : FullTranscript (pSpec (ι := ι) (F := F) k t))
    (witOut : OutputWitness)
    (relOut : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
    (h : Pr[ fun stmtOut ↦ (stmtOut, witOut) ∈ relOut
      | OptionT.mk do
          (simulateQ impl
              (((oracleVerifier (k := k) (t := t) encode).toVerifier).run stmtIn tr)).run'
            (← init)] > 0) :
    accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
      (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) := by
  rw [gt_iff_lt, probEvent_pos_iff] at h
  obtain ⟨stmtOut, hmem, -⟩ := h
  obtain ⟨s₀, -, hmem⟩ := OptionT.mem_support_bind_mk init _ hmem
  rw [OptionT.mem_support_iff] at hmem
  exact accepts_of_mem_support_verifier_run (k := k) (t := t) impl s₀ encode stmtIn tr hmem

omit [Fintype ι] [DecidableEq ι] [Fintype F] in
/-- **Honest completeness for Construction 6.2** (protocol-level form).

The honest oracle reduction is perfectly complete from `honestInputRelation k C encode`
(the honest-opening input relation — see the **statement repair** note below)
to the trivial output relation `Set.univ`. The load-bearing fact is
`accepts_of_inputRelation` above: under any verifier challenges, the
honest prover's message `g = wit₀ + γ·wit₁` makes `accepts` hold, so the
verifier's `if accepts then pure () else failure` never fails.

**Status: CLOSED.** `#print axioms` is exactly `[propext, Classical.choice,
Quot.sound]` (no `sorry`/`admit`/custom axiom). The proof is the standard
`probEvent_eq_one_iff` support decomposition, mirroring
`Sumcheck/Spec/SingleRound.lean`'s `reduction_perfectCompleteness`:

  * `Fin.induction_three` (a `rfl` in `ArkLib/Data/Fin/Basic.lean`) peels the
    three `Prover.runToRound (Fin.last 3)` rounds, resolved by `split`;
  * `simulateQ_oracleVerify_eq` (above) collapses the compiled oracle verifier
    to `if accepts … then pure () else failure`, every query reduced to its
    honest value via the in-file `simOracle2` collapse lemmas;
  * the no-failure half peels the prover-run support to the *concrete*
    `Fin.snoc`-built transcript (`tr = snoc (snoc (snoc default γ) g) xs`),
    reduces the `messages ⟨1⟩` / `challenges ⟨0⟩,⟨2⟩` accessors, and discharges
    the `if accepts …` guard by `accepts_of_inputRelation` for *every* sampled
    `(γ, xs)`; the event half is closed by `Subsingleton.elim` since the output
    statements live in `Unit` / `Fin 0 → _`.

**Statement repair (defect #18, hEnc class — pre-approved).** The historic
statement used `inputRelation k C`, which (Definition 6.1, `ToyProblem.relation`)
existentially quantifies the *opener* `encode'` — a *different* map than the
protocol's `encode`. The honest verifier's spot-check uses the protocol's
`encode`, so completeness needs `f i = encode (wit i)` for *that* `encode` and,
crucially, for the *prover's own witness* `wit` (the honest prover sends
`g = wit₀ + γ·wit₁`, built from `wit`, not from any existential `M`). Hence we
prove completeness against `honestInputRelation k C encode`, which pins the
opener to `encode` and the opening to `input.2 = wit` (cf. the L6.13 `hEnc`
linear-encoder precedent in `SoundnessBounds.lean`). This is a *strengthening*
of the input hypothesis — `honestInputRelation k C encode ⊆ inputRelation k C`
under `_h_encode_mem` (`honestInputRelation_subset_inputRelation`) — so the
claim is faithful and never vacuous. Completeness against `inputRelation k C`
itself is *false* (counterexample in the `honestInputRelation` docstring:
`encode' = 0`, `encode = id`, `wit ≠ 0`). -/
theorem oracleReduction_perfectCompleteness
    [SampleableType F] [SampleableType ι]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (encode : (Fin k → F) →ₗ[F] (ι → F))
    (_h_encode_mem : ∀ m, (encode m : ι → F) ∈ C) :
    (oracleReduction (ι := ι) (F := F) (k := k) (t := t)
        (encode : (Fin k → F) → (ι → F))).perfectCompleteness
      init impl
      -- Statement repair (hEnc class, L6.13 precedent): the honest-opening
      -- relation for the *protocol's* encoder, not the existential-encoder
      -- `inputRelation k C` (whose opener is a DIFFERENT map — completeness
      -- against it is false, see `honestInputRelation` docstring counterexample).
      -- `honestInputRelation k C encode ⊆ inputRelation k C` under
      -- `_h_encode_mem`, so this is the faithful (non-vacuous) claim.
      (honestInputRelation k C encode)
      (Set.univ : Set (((OutputStatement × ∀ i, OutputOracleStatement i)) ×
        OutputWitness)) := by
  -- ABF26-C6.2 completeness. The compiled verifier collapses (via `simulateQ_oracleVerify_eq`)
  -- to `if accepts … then pure () else failure`; `accepts_of_inputRelation` shows the `accepts`
  -- guard holds for the honest message `g = M₀+γM₁` under ANY challenges, so the residual
  -- `Pr = 1` is discharged by the support peel (à la Sumcheck `Simple`'s completeness).
  classical
  unfold OracleReduction.perfectCompleteness
  rw [Reduction.perfectCompleteness_eq_prob_one]
  rintro ⟨stmt, oStmt⟩ wit hRel
  obtain ⟨hf, hM⟩ := hRel
  -- The §6.1 decision predicate holds for the honest `g = wit₀ + γ·wit₁` (built from the
  -- prover's own witness `wit`) under every challenge pair.
  have hAcc : ∀ (γ : F) (xs : Fin t → ι),
      accepts (k := k) (t := t) (encode := (encode : (Fin k → F) → (ι → F)))
        stmt oStmt γ (fun j ↦ wit 0 j + γ * wit 1 j) xs :=
    fun γ xs => accepts_of_inputRelation (encode := encode) stmt wit hM oStmt hf γ xs
  simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, Prover.run,
    Verifier.run, oracleProver, OracleVerifier.toVerifier,
    Prover.runToRound, Prover.processRound, Fin.induction_three, pSpec,
    bind_pure_comp]
  -- Peel the three prover rounds: V→P (γ), P→V (g), V→P (xs).
  split <;> rename_i hDir0
  swap
  · exact absurd hDir0 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, bind_pure_comp]
  split <;> rename_i hDir1
  · exact absurd hDir1 (by decide)
  try simp only [pure_bind, map_pure, Functor.map_map, bind_pure_comp]
  split <;> rename_i hDir2
  swap
  · exact absurd hDir2 (by decide)
  -- The verifier body is now the compiled `simulateQ`; collapse it to `if accepts …`.
  simp only [simulateQ_oracleVerify_eq]
  simp only [liftM_pure, liftComp_pure, map_pure, pure_bind, bind_pure_comp,
    Functor.map_map, Function.comp_def, OptionT.run_pure, Option.getM,
    Transcript.concat, Fin.snoc_last, Fin.snoc_castSucc]
  -- The honest `accepts` guard never short-circuits: under ANY challenges, the honest
  -- prover's message `g = M₀+γM₁` satisfies `accepts` (`hAcc`). We pin the `if accepts …`
  -- to `pure ()` by a definitional rewrite of the transcript accessors that feed it.
  rw [probEvent_eq_one_iff]
  -- After the collapse the verifier branch is `if accepts … (proverResult.1.messages ⟨1,_⟩) …`.
  -- The honest prover writes `proverResult.1.messages ⟨1,_⟩ = fun j ↦ M 0 j + γ · M 1 j`
  -- (round-1 `Transcript.concat` of the honest message) and the two challenge accessors are
  -- the sampled `γ, xs`. Reduce the accessors so the `if` condition matches `hAcc`.
  refine ⟨?_, ?_⟩
  · -- No failure: peel the challenge / message samples; the `if` collapses to `pure ()`.
    rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    -- Peel outer `init >>= …` then the prover-run / verifier binds, resolving each
    -- `getChallenge` sample, until the verifier `if accepts …` (which is `pure ()` by `hIf`).
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hmem
    obtain ⟨⟨_, s'⟩, hmem, rfl⟩ := hmem
    erw [simulateQ_bind] at hmem
    erw [StateT.run_bind] at hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨x, s''⟩, hx, hs⟩ := hmem
    -- Peel the prover-run `liftM (g <$> body)`: it is `OptionT.lift`, so `x = some (g result)`.
    erw [simulateQ_map] at hx
    rw [StateT.run_map] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨⟨tr, sₜ⟩, htr, hxeq⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxeq
    -- Reduce the verifier `match some tr with | some a => …` to its `some` branch.
    dsimp only at hs
    -- Peel the prover-run body `g <$> (γ-sample; honest-msg; xs-sample)` to expose the
    -- concrete `Fin.snoc`-built transcript.
    erw [simulateQ_map] at htr
    rw [StateT.run_map] at htr
    simp only [support_map, Set.mem_image] at htr
    obtain ⟨⟨trb, sb⟩, htr, htreq⟩ := htr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htreq
    -- Peel the prover-run body: round 2 (xs-sample) is the outer bind.
    erw [simulateQ_bind] at htr
    erw [StateT.run_bind] at htr
    rw [mem_support_bind_iff] at htr
    obtain ⟨⟨r01, s01⟩, htr01, htr2⟩ := htr
    -- Round 2: peel the xs-sample (`getChallenge ⟨2⟩`), then the `pure` and the map.
    erw [simulateQ_bind] at htr2
    erw [StateT.run_bind] at htr2
    rw [mem_support_bind_iff] at htr2
    obtain ⟨⟨xs, sx⟩, hxs, htr2b⟩ := htr2
    erw [simulateQ_map] at htr2b
    rw [StateT.run_map] at htr2b
    simp only [support_map, Set.mem_image] at htr2b
    obtain ⟨⟨pr2, sp2⟩, hpr2, htr2eq⟩ := htr2b
    -- `hpr2` is a `pure`: extract `r01.2 = (γ, st)` and `pr2 = fun _ ↦ (γ, st)`.
    -- Peel rounds 0 and 1 from `htr01`.
    erw [simulateQ_bind] at htr01
    erw [StateT.run_bind] at htr01
    rw [mem_support_bind_iff] at htr01
    obtain ⟨⟨r0, s0⟩, htr0, htr1⟩ := htr01
    erw [simulateQ_map] at htr1
    rw [StateT.run_map] at htr1
    simp only [support_map, Set.mem_image] at htr1
    obtain ⟨⟨pr1, sp1⟩, hpr1, htr1eq⟩ := htr1
    -- Round 0: peel the `pure (default, input)` bind, then the γ-sample map.
    erw [simulateQ_bind] at htr0
    erw [StateT.run_bind] at htr0
    rw [mem_support_bind_iff] at htr0
    obtain ⟨⟨ini, si⟩, hini, htr0b⟩ := htr0
    erw [simulateQ_pure, StateT.run_pure] at hini
    simp only [support_pure, Set.mem_singleton_iff] at hini
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hini
    erw [simulateQ_map] at htr0b
    rw [StateT.run_map] at htr0b
    simp only [support_map, Set.mem_image] at htr0b
    obtain ⟨⟨γ, sγ⟩, hγ, htr0eq⟩ := htr0b
    -- Resolve `r0` from the round-0 map, then the round-1 `pure` (honest message), then
    -- round-2 `pure` (receiveChallenge), substituting back up the chain.
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htr0eq
    dsimp only at hpr1
    simp only [liftM_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hpr1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpr1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htr1eq
    dsimp only at hpr2
    simp only [liftM_pure, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hpr2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpr2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htr2eq
    -- Now `trb.1 = snoc (snoc (snoc default γ) (honest g)) xs`; reduce the `Fin.snoc` accessors
    -- in `hs`, dispatch `accepts` via `hAcc γ xs`, leaving `pure` (so the result is `some`,
    -- contradicting `none`).
    simp only [id_eq, FullTranscript.messages, FullTranscript.challenges, Fin.snoc,
      Fin.val_zero, Fin.val_one, Fin.val_two, Nat.lt_irrefl, Nat.reduceLT, ↓reduceDIte,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT, Fin.last, cast_eq] at hs
    -- The `if accepts …` guard holds (`hAcc γ xs`, up to the defeq `cast` on `g`); collapse it.
    rw [if_pos (by simpa only [cast_eq] using hAcc γ xs)] at hs
    -- The verifier now deterministically returns `some`, so `(none, _)` is not in its support.
    -- Peel the verifier's two OptionT binds (`liftM (pure …)` then the `match … some`).
    erw [simulateQ_optionT_bind] at hs
    -- The first bind is `liftM ((g <$> pure ()).run) = pure (some (g ()))`; reduce it.
    simp only [map_pure, OptionT.run_mk, OptionT.run_pure, liftM_pure, simulateQ_pure] at hs
    obtain ⟨⟨a, sa⟩, ha, hs⟩ := hs
  · -- Event holds: the output statements are both `Unit` (`OutputStatement = Unit`,
    -- `OutputOracleStatement : Fin 0 → Type`), hence trivially in `Set.univ` and equal.
    intro x hx
    exact ⟨trivial, Subsingleton.elim _ _⟩

/-! ### Remark 6.7 of [ABF26] — MCA, not just CA

For any `δ ∈ (0, δ_min(C))`, the toy-problem IOR has knowledge
soundness against the relaxed relation `R̃_{C,δ}^2` with error

  `max { ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|, (1 − δ)^t }`.

Stated against ArkLib's `Verifier.knowledgeSoundness` (cf.
`OracleReduction/Security/Basic.lean :: Verifier.knowledgeSoundness`).

**Naming convention — paper vs API.** The ArkLib API's
`Verifier.knowledgeSoundness` takes `(relIn, relOut)` where `relIn`
is the relation the extracted witness satisfies and `relOut` is the
relation the verifier's output must satisfy. In this file `relIn` is
*our* `outputRelation` (paper's `R̃²_{C,δ}`, what the extractor
extracts to) and `relOut` is `Set.univ` (paper's C6.2 has trivial
output `Unit`). The name `outputRelation` reflects the **paper's**
"this is the protocol's output relation" perspective; do not be misled
by the API parameter named `relIn`.

The proof exhibits an extractor that (i) erasure-decodes `(f₁, f₂)`
against the largest agreement set, (ii) outputs the recovered messages,
and (iii) bounds the failure event by the union of the MCA failure and
the list-decoding cardinality bound (cf. Remark 6.7).

**Statement-level finding & repair (2026-06).** ABF26 L6.6 is a 2-special-soundness argument whose
extractor must **rewind** the prover (two accepting transcripts at distinct `γ`, solve a 2×2 linear
system), but ArkLib's `Verifier.knowledgeSoundness` quantifies only over a single-run
`Extractor.Straightline` with no re-invocation handle, so the rewinding extractor is not expressible
against it (the wall recorded in `oraclereduction-leftovers.md` residual (1)+(2)). We prove the
genuine content as `protocol62_knowledgeSoundnessViaRewinding` (the framework predicate
`Extractor.knowledgeSoundnessViaRewinding`, fully proven above) and reduce the straightline
statement to the **single named bridge residual** below — the precise straightline↔rewinding
interface translation, the smallest missing piece.

The residual is `Bridge.StraightlineOfRewinding` from the *proven* rewinding witness to
the straightline conclusion, so the theorem `protocol62_knowledgeSound` discharges the conclusion by
feeding the proven witness through the residual (no `sorry`, no `axiom`).

**Named bridge residual.** The named L6.6 bridge residual is carried as the explicit hypothesis
`hBridge`; no global axiom is introduced. -/
theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode


/-- **Remark 6.7 of [ABF26]**: the L6.6 soundness argument depends on
**mutual** correlated agreement (MCA). With only correlated agreement
(CA), one cannot prove every codeword `u ∈ Λ(C, f₁ + γ·f₂, δ)`
decomposes as `u = u₁ + γ·u₂` for some
`(u₁, u₂) ∈ Λ(C^{≡2}, (f₁, f₂), δ)`, so the extractor would fail. MCA
provides exactly this decomposition with probability `≥ 1 − ε_mca`. -/

/-! ### Lemma 6.8 assembly — extractor, knowledge state function, per-round bounds.
The post-spot-check state is the §6.1 acceptance predicate itself
(witness-ignoring) — see PAPER_REVS.md item 10 for the deviation rationale. -/

/-- `Pr_{x ← D}[P x] = 0` for a never-satisfied predicate `P`. -/
private lemma Pr_eq_zero_of_forall_not {α : Type} (D : PMF α) (P : α → Prop)
    (h : ∀ x, ¬ P x) : Pr_{let x ← D}[P x] = 0 := by
  classical rw [prob_tsum_form_singleton]; simp [h]

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- The post-`γ` knowledge state of the L6.8 argument ([ABF26] §6.2): `m`
satisfies the folded linear constraint at `γ`, and `f₁ + γ·f₂` agrees with
`encode m` on a `≥ (1-δ)`-fraction column set. Shaped to match the event of
`ToyProblem.gamma_transition_prob_le` exactly.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) reuses it as its γ-round prefix event. -/
def gammaState (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F) (γ : F) (m : Fin k → F) : Prop :=
  (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
  ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
    ∀ j ∈ S, f₁ j + γ * f₂ j = encode m j

/-- L6.8 intermediate witness types: input witness at round 0, the γ-round
candidate message during rounds 1–2, nothing after the spot-check round. -/
private def rbrWitMid : Fin 4 → Type
  | ⟨0, _⟩ => Witness (F := F) k
  | ⟨1, _⟩ => Fin k → F
  | ⟨2, _⟩ => Fin k → F
  | ⟨3, _⟩ => PUnit

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
open Classical in
/-- Round-0 extraction for L6.8: if *any* witness completes `stmtIn` in the
relaxed output relation, return one by choice; otherwise a dummy.

Public (not `private`) because L6.10 reuses it verbatim: the C6.9 input relation is
the same `R̃²_{C,δ}` (`outputRelationFor`), so the L6.10 straightline extractor is this
same classical choice (`SimplifiedIOR.simplifiedIOR_knowledgeSound`). -/
noncomputable def extractZero (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Witness (F := F) k :=
  if h : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ then h.choose
  else fun _ _ ↦ 0

omit [DecidableEq ι] [DecidableEq F] in
/-- If a relaxed-relation witness exists at all, `extractZero` returns one.
(Shared by the L6.8 γ-round bound and the L6.10 game bound.) -/
lemma extractZero_mem {encode : (Fin k → F) → (ι → F)} {δ : ℝ≥0}
    {stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)}
    (hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k encode δ) :
    (stmtIn, extractZero k encode δ stmtIn) ∈ outputRelationFor k encode δ := by
  unfold extractZero; rw [dif_pos hw]; exact hw.choose_spec

omit [DecidableEq ι] in
/-- The L6.8 round-by-round extractor ([ABF26] §6.2): round 0 extracts a
relaxed-relation witness by choice, round 1 passes the candidate message
through, round 2 reads the prover's claim `g` off the transcript. -/
private noncomputable def rbrExtractor (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0) :
    Extractor.RoundByRound []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) (rbrWitMid (F := F) k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn _ _ ↦ extractZero k encode δ stmtIn
  | ⟨1, _⟩ => fun _ _ w ↦ w
  | ⟨2, _⟩ => fun _ tr _ ↦ tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  extractOut := fun _ _ _ ↦ PUnit.unit

omit [DecidableEq ι] in
/-- The L6.8 knowledge state function ([ABF26] §6.2): relaxed-relation
membership at round 0, `gammaState` after rounds 1–2, and the §6.1 acceptance
predicate after the spot-check round (PAPER_REVS.md item 10). -/
private noncomputable def rbrKSF (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((oracleVerifier (k := k) (t := t) encode).toVerifier).KnowledgeStateFunction init impl
      (outputRelationFor k encode δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (rbrExtractor k t encode δ) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦ (stmtIn, w) ∈ outputRelationFor k encode δ
  | ⟨1, _⟩ => fun stmtIn tr w ↦
      gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨2, _⟩ => fun stmtIn tr w ↦
      gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨3, _⟩ => fun stmtIn tr _ ↦
      accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2
        (tr ⟨0, Nat.zero_lt_succ _⟩) (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
        (tr ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ match m with
    | ⟨0, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
    | ⟨1, _⟩ => fun _ _ _ _ _ h ↦ h
    | ⟨2, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
  toFun_full := fun stmtIn tr witOut h ↦
    accepts_of_probEvent_pos_verifier_run (k := k) (t := t) init impl encode
      stmtIn tr witOut _ h

omit [DecidableEq ι] [DecidableEq F] in
/-- `epsMCA` is a supremum of probabilities, hence `≤ 1 < ⊤`. (Candidate for
relocation to `ProximityGap/Errors.lean`. Public because the L6.10 coercion
endgame in `Spec/SimplifiedIOR.lean` reuses it.) -/
lemma epsMCA_ne_top [Nonempty ι] (C : Set (ι → F)) (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) C δ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun _ ↦ PMF.coe_le_one _ _)

omit [DecidableEq ι] in
/-- Per-transcript γ-round bound for the L6.8 game ([ABF26] §6.2, via
`ToyProblem.gamma_transition_prob_le`), stated in the definitionally reduced
form of the game event so the master rbr-game lemma can consume it.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) consumes it as its γ-round prefix bound. -/
lemma gamma_round_game_bound [SampleableType F] [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) →ₗ[F] (ι → F))
    (hinj : Function.Injective encode)
    (hC : Set.range encode = C)
    (hδ_pos : 0 < δ) (hδ_lt : δ < (minRelHammingDistCode C : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Pr[fun γ : F ↦ ∃ w : Fin k → F,
        (stmtIn, extractZero k (encode : (Fin k → F) → (ι → F)) δ stmtIn) ∉
            outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ ∧
          gammaState k (encode : (Fin k → F) → (ι → F)) δ stmtIn.1.1 stmtIn.1.2.1
            stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ w
      | $ᵗ F] ≤
      (((epsMCA (F := F) (A := F) C δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hw : ∃ M, (stmtIn, M) ∈ outputRelationFor k (encode : (Fin k → F) → (ι → F)) δ
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro γ ⟨w, hne, -⟩
    exact hne (extractZero_mem k hw)
  · refine le_trans (Pr_le_Pr_of_implies _ _
      (fun γ ↦ ∃ m, gammaState k (encode : (Fin k → F) → (ι → F)) δ stmtIn.1.1
        stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ m) ?_) ?_
    · rintro γ ⟨w, -, hst⟩
      exact ⟨w, hst⟩
    · have hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
          (∀ i : Fin 2, ∑ j, M i j * stmtIn.1.1 j = ![stmtIn.1.2.1, stmtIn.1.2.2] i) ∧
          ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
            ∀ i : Fin 2, ∀ j ∈ S, ![stmtIn.2 0, stmtIn.2 1] i j = encode (M i) j := by
        rintro ⟨M, h1, S, h2, h3⟩
        refine hw ⟨M, h1, S, h2, fun i j hj ↦ ?_⟩
        fin_cases i
        · simpa using h3 0 j hj
        · simpa using h3 1 j hj
      refine le_trans (gamma_transition_prob_le C δ encode hinj hC hδ_pos hδ_lt
        stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) hNoWit)
        (le_of_eq ?_)
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal (epsMCA_ne_top C δ),
        ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        ENNReal.coe_natCast, ENNReal.coe_natCast]

omit [DecidableEq ι] [Fintype F] in
-- `[DecidableEq F]` is used in the proof (`by_cases` on the linear constraint, the agreement
-- filter) but does not surface in the statement; same false-positive pattern as
-- `ToyProblem.pair_violates` (SoundnessBounds.lean).
set_option linter.unusedDecidableInType false in
/-- Per-transcript spot-check-round bound for the L6.8 game ([ABF26] §6.2):
for any fixed `(γ, g)` with the post-`γ` state false, the probability over
uniform spot checks that the verifier accepts is at most `(1-δ)^t`. Stated in
the definitionally reduced form of the game event.

Public (not `private`) because the L6.6 assembly
(`Spec/KnowledgeSoundness.lean`) consumes it as its spot-check tail bound. -/
lemma spotcheck_round_game_bound [Nonempty ι]
    (encode : (Fin k → F) → (ι → F)) (δ : ℝ≥0)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (γ : F) (g : Fin k → F) [SampleableType (Fin t → ι)] :
    Pr[fun xs : Fin t → ι ↦ ∃ _w : PUnit,
        ¬ gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
            (stmtIn.2 0) (stmtIn.2 1) γ g ∧
          accepts (k := k) (t := t) encode stmtIn.1 stmtIn.2 γ g xs
      | $ᵗ (Fin t → ι)] ≤ (((1 - δ) ^ t : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  by_cases hbad : gammaState k encode δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
      (stmtIn.2 0) (stmtIn.2 1) γ g
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro xs ⟨-, hne, -⟩
    exact hne hbad
  by_cases hlin : ∑ j, g j * stmtIn.1.1 j = stmtIn.1.2.1 + γ * stmtIn.1.2.2
  swap
  · refine (Pr_eq_zero_of_forall_not _ _ ?_).trans_le zero_le'
    rintro xs ⟨-, -, hacc⟩
    exact hlin (And.left hacc)
  set A : Finset ι :=
    Finset.univ.filter (fun j ↦ stmtIn.2 0 j + γ * stmtIn.2 1 j = encode g j) with hA
  have hι : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hAcard : (A.card : ℝ) < (1 - (δ : ℝ)) * Fintype.card ι :=
    not_le.mp fun hge ↦ hbad ⟨hlin, A, hge, fun j hj ↦ (Finset.mem_filter.mp hj).2⟩
  have hδ1 : δ ≤ 1 := by
    by_contra hgt
    have h1δ : (1 : ℝ) - (δ : ℝ) < 0 := sub_neg.mpr (by exact_mod_cast not_le.mp hgt)
    linarith [mul_neg_of_neg_of_pos h1δ hι, (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]
  have hbase : ((A.card : ℝ≥0) / (Fintype.card ι : ℝ≥0)) ≤ 1 - δ := by
    rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ≥0) < Fintype.card ι),
      ← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hδ1]
    linarith
  refine le_trans (Pr_le_Pr_of_implies _ _ (fun xs ↦ ∀ j, xs j ∈ A) ?_) ?_
  · rintro xs ⟨-, -, hacc⟩ j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (And.right hacc j).symm⟩
  · refine le_trans (prob_uniform_pi_mem_finset_le A t) ?_
    rw [ENNReal.coe_pow]
    refine pow_le_pow_left' ?_ t
    rw [show ((A.card : ℝ≥0∞)) = ((A.card : ℝ≥0) : ℝ≥0∞) from (ENNReal.coe_natCast _).symm,
      show ((Fintype.card ι : ℝ≥0∞)) = ((Fintype.card ι : ℝ≥0) : ℝ≥0∞) from
        (ENNReal.coe_natCast _).symm,
      ← ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
    exact ENNReal.coe_le_coe.mpr hbase

omit [DecidableEq ι] in
/-- **Lemma 6.8 of [ABF26]** (round-by-round knowledge soundness of
Construction 6.2).

For any `δ ∈ (0, δ_min(C))` and fixed injective linear encoder with
range `C` (injectivity is implicit in the paper's encoding map and
load-bearing for the extractor's per-list-pair counting),
the IOR has round-by-round knowledge soundness (ArkLib's
`OracleVerifier.rbrKnowledgeSoundness`, definitionally
`toVerifier.rbrKnowledgeSoundness`) against `R̃_{C,δ}^2`, with
per-round errors

**Quantification note (paper Definition A.5 vs the ArkLib game).** The
paper's rbr definition bounds the bad-transition probability for *every*
fixed transcript prefix (worst case); ArkLib's game samples the prefix
challenges uniformly inside the prover run and bounds the *mixture*. The
in-tree statement is therefore the averaged form, implied by the paper's.
The per-round lemmas feeding this proof (`gamma_round_game_bound`,
`spotcheck_round_game_bound`) hold for every fixed prefix — i.e. they ARE
the paper-strength worst-case facts — so the paper's mathematical content
is fully in-tree; only the bundled top-level game statement averages.

  * `ε_mca(C, δ) + |Λ(C^{≡2}, δ)| / |F|` after the γ round,
  * `(1 − δ)^t` after the spot-check round.

The `KnowledgeStateFunction` tracks the largest current agreement set;
the extractor erasure-decodes against it.

**Statement-level finding & repair (2026-06).** Same wall as L6.6: `Verifier.rbrKnowledgeSoundness`
(`OracleReduction/Security/RoundByRound.lean`, line 811) quantifies only over a single-run
`Extractor.RoundByRound` (no re-invocation handle), so the rewinding extractor is not expressible
against it. We reduce to the **named bridge residual** below from the *proven* rewinding witness
`protocol62_knowledgeSoundnessViaRewinding` (same 2-special-sound rewinding extractor; the rbr
accounting splits its failure across the `γ` and spot-check rounds). No `sorry`, no `axiom`.

**Named bridge residual.** The named L6.8 bridge residual is carried as the explicit hypothesis
`hBridge`; no global axiom is introduced. -/
theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode

end Protocol

end Spec

end ToyProblem

/-! ### Axiom audit (issue #18 ToyProblem bridge residual frontiers) -/

#print axioms ToyProblem.Spec.protocol62_knowledgeSoundnessViaRewinding
#print axioms ToyProblem.Spec.protocol62_knowledgeSound
#print axioms ToyProblem.Spec.protocol62_rbrKnowledgeSound
