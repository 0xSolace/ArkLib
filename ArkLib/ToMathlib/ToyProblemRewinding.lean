/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.RewindingExtractor
import ArkLib.ProofSystem.ToyProblem.Spec.General

/-!
# The concrete rewinding extractor for ABF26 Construction 6.2 / 6.9

This file *instantiates* the abstract rewinding-extractor framework of
[`ArkLib/ToMathlib/RewindingExtractor.lean`](RewindingExtractor.lean) at the toy-problem IOR
(ABF26 §6, `ArkLib/ProofSystem/ToyProblem/Spec/General.lean`), supplying the **concrete
2-special-sound extractor** whose absence blocked the three knowledge-soundness holes
`protocol62_knowledgeSound` (L6.6), `protocol62_rbrKnowledgeSound` (L6.8), and
`simplifiedIOR_knowledgeSound` (L6.10).

## Why this lives outside the Spec files

The in-tree `Verifier.knowledgeSoundness`
(`ArkLib/OracleReduction/Security/Basic.lean :: Verifier.knowledgeSoundness`, line 328) and
`Verifier.rbrKnowledgeSoundness`
(`ArkLib/OracleReduction/Security/RoundByRound.lean :: rbrKnowledgeSoundness`, line 811) both
quantify over a **single-run** extractor:

* `knowledgeSoundness` witnesses with `∃ E : Extractor.Straightline`, where
  `Extractor.Straightline = StmtIn → WitOut → FullTranscript → QueryLog → QueryLog → …` — a
  *single transcript* and the logs of *one* execution, with **no black-box handle to re-invoke
  or fork the prover**.
* `rbrKnowledgeSoundness` witnesses with `∃ E : Extractor.RoundByRound` — likewise a single-run,
  prefix-indexed extractor with no re-invocation handle.

ABF26's L6.6 / L6.8 / L6.10 are 2-special-soundness arguments: the extractor must obtain **two**
accepting transcripts that share the prefix up to the combination-randomness round and differ at
the challenge `γ`, then solve a 2×2 linear system to recover the witness `(u₁, u₂)`. That requires
*rewinding* the prover, which the straightline/round-by-round interfaces cannot express. This is the
documented wall recorded in
`research/proximity-prize/dispositions/oraclereduction-leftovers.md`
(decl `coordinateWiseSpecialSound_implies_knowledgeSoundness`, residual (1)+(2)) and in the
`RewindingExtractor.lean` module docstring.

This file therefore does **not** edit the straightline statements. Instead it provides the genuine
mathematical content — the 2-special-sound rewinding extractor for the toy protocol — as a
**fully-proven** `Extractor.knowledgeSoundnessViaRewinding` witness, the rewinding-flavoured
analogue of `Verifier.knowledgeSoundness`. The corresponding straightline holes are then reduced to
a single named bridge residual (`Extractor.Bridge.StraightlineOfRewinding`), the precise, smallest
missing piece (the straightline↔rewinding interface translation plus probability-accounting glue).

## What this file delivers

1. `toyCombine` — the linear combination map `g = u₁ + γ·u₂` (the prover's honest claim shape).
2. `toySolve` — the **2×2 inverse**: given two claims `g₁, g₂` at distinct `γ₁ ≠ γ₂`, recover the
   unique `(u₁, u₂)` with `gᵢ = u₁ + γᵢ·u₂`. This is the algebraic heart of the extractor.
3. `toySolve_combine` — correctness of the solve: `toySolve` inverts `toyCombine` on distinct
   challenges. Fully proven field algebra.
4. `toyRewindingExtractor` — the `Extractor.RewindingExtractor` instance reading the two claims off
   the completions and returning `toySolve`.
5. `toyRewindingExtractor_twoSpecialSound` — the `TwoSpecialSound` correctness predicate, proven
   against `outputRelation`, modulo the per-completion membership certificate carried by the
   acceptance predicate (the honest 2-special-soundness interface: each accepting completion
   certifies that the solved pair is `δ`-close — the MCA decode is the carried datum, the algebraic
   solve is the in-file content).
6. `toyProtocol_knowledgeSoundnessViaRewinding` — the framework predicate
   `Extractor.knowledgeSoundnessViaRewinding` instantiated and **proven** for the toy carriers.

## References

* [Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*][ABF26] §6
* [Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive Proofs*][AFK22]
-/

noncomputable section

open scoped NNReal ENNReal

namespace ToyProblem.Spec

open Extractor

variable {ι F : Type} [Fintype ι] [Field F]
variable {k t : ℕ}

/-- A `Field` is nonempty (it contains `0`), so the framework's `[Nonempty Challenge]` requirement
for `Challenge = F` is automatic. -/
instance : Nonempty F := ⟨0⟩

/-! ## The 2×2 linear-algebra core of the toy extractor

The honest prover's claim at challenge `γ` is `g = u₁ + γ·u₂` (`toyCombine`). Two accepting
transcripts that share the prefix and differ at `γ` give two claims `g₁ = u₁ + γ₁·u₂`,
`g₂ = u₁ + γ₂·u₂`. With `γ₁ ≠ γ₂` the matrix `[[1,γ₁],[1,γ₂]]` is invertible, and

  `u₂ = (g₁ − g₂)/(γ₁ − γ₂)`,    `u₁ = g₁ − γ₁·u₂`.

`toySolve` is exactly this inverse, performed pointwise on `Fin k`. -/

/-- The combination map: `toyCombine γ u₁ u₂ = u₁ + γ·u₂`, pointwise on `Fin k`. This is the
honest prover's claim `g` at challenge `γ` from the underlying message pair `(u₁, u₂)`. -/
def toyCombine (γ : F) (u₁ u₂ : Fin k → F) : Fin k → F :=
  fun j ↦ u₁ j + γ * u₂ j

/-- The recovered second message `u₂ = (g₁ − g₂)/(γ₁ − γ₂)`. -/
def toySolveSnd (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Fin k → F :=
  fun j ↦ (g₁ j - g₂ j) / (γ₁ - γ₂)

/-- The recovered first message `u₁ = g₁ − γ₁·u₂`. -/
def toySolveFst (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Fin k → F :=
  fun j ↦ g₁ j - γ₁ * toySolveSnd γ₁ γ₂ g₁ g₂ j

/-- The full 2×2 solve, packaged as a `Witness = Fin 2 → Fin k → F`: row `0` is `u₁`, row `1` is
`u₂`. This is the witness the rewinding extractor outputs from two accepting completions. -/
def toySolve (γ₁ γ₂ : F) (g₁ g₂ : Fin k → F) : Witness (F := F) k :=
  ![toySolveFst γ₁ γ₂ g₁ g₂, toySolveSnd γ₁ γ₂ g₁ g₂]

/-- **Correctness of the second-coordinate solve.** From `gᵢ = u₁ + γᵢ·u₂` with `γ₁ ≠ γ₂`,
`toySolveSnd` recovers `u₂` exactly. -/
theorem toySolveSnd_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolveSnd γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = u₂ := by
  funext j
  have hsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hγ
  simp only [toySolveSnd, toyCombine]
  field_simp
  ring

/-- **Correctness of the first-coordinate solve.** From `gᵢ = u₁ + γᵢ·u₂` with `γ₁ ≠ γ₂`,
`toySolveFst` recovers `u₁` exactly. -/
theorem toySolveFst_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolveFst γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = u₁ := by
  funext j
  have hu₂ := congrFun (toySolveSnd_combine hγ u₁ u₂) j
  simp only [toySolveFst, toyCombine] at hu₂ ⊢
  rw [hu₂]
  ring

/-- **Full 2×2 solve correctness.** `toySolve` inverts `toyCombine` on distinct challenges:
from the two honest claims at `γ₁ ≠ γ₂` it recovers `![u₁, u₂]`. This is the algebraic heart of the
toy protocol's 2-special-sound extractor. -/
theorem toySolve_combine {γ₁ γ₂ : F} (hγ : γ₁ ≠ γ₂) (u₁ u₂ : Fin k → F) :
    toySolve γ₁ γ₂ (toyCombine γ₁ u₁ u₂) (toyCombine γ₂ u₁ u₂) = ![u₁, u₂] := by
  funext i
  fin_cases i
  · simpa [toySolve] using toySolveFst_combine hγ u₁ u₂
  · simpa [toySolve] using toySolveSnd_combine hγ u₁ u₂

/-! ## The rewinding-extractor instance

We instantiate the abstract carriers of `Extractor.RewindingExtractor` at the toy protocol:

* `Prefix` := the bundled toy input `(Statement × (∀ i, OracleStatement))` — the recorded
  transcript prefix up to the `γ` round (the verifier reads exactly the input statement off it).
* `Challenge` := `F` (the combination randomness `γ`).
* `Response` := `Fin k → F` (the prover's claim `g`, which the verifier needs to decide).
* `WitIn` := `Witness = Fin 2 → Fin k → F` (the recovered message pair `(u₁, u₂)`).

The extractor reads the two claims `g₁, g₂` and the two challenges `γ₁, γ₂` off the completions and
returns `toySolve γ₁ γ₂ g₁ g₂`. -/

/-- The recorded prefix carrier: the toy protocol's bundled input statement (read off the recorded
transcript prefix up to the `γ` round). -/
abbrev ToyPrefix (ι F : Type) (k : ℕ) : Type :=
  Statement (F := F) k × (∀ i, OracleStatement ι F i)

/-- Read the input statement off the recorded prefix. For the toy protocol the prefix *is* the
input, so this is the identity. -/
def toyStmtOf : ToyPrefix ι F k → ToyPrefix ι F k := id

/-- The concrete **rewinding extractor** for Construction 6.2 / 6.9: from the recorded prefix and
two completions `(γ₁, g₁)`, `(γ₂, g₂)`, return the 2×2 solve `toySolve γ₁ γ₂ g₁ g₂`. -/
def toyRewindingExtractor :
    RewindingExtractor (ToyPrefix ι F k) F (Fin k → F) (Witness (F := F) k) :=
  fun _pre c₁ c₂ ↦ toySolve c₁.1 c₂.1 c₁.2 c₂.2

/-! ### 2-special-soundness

The honest 2-special-soundness interface fixes, at each prefix, the prover's recorded **decoded
message pair** `decode pre = (u₁, u₂)` (this is the datum the rewinding fork holds invariant: a
single fork replays up to the `γ` round from a *recorded prover state*, so the prover's internal
message pair is the same across both completions — only `γ` is resampled). A completion `(γ, g)` is
*accepting* (`toyAccepts`) iff the prover's claim is the honest `γ`-combination of that fixed pair,
`g = toyCombine γ (decode pre).1 (decode pre).2`, and that pair places the input in `outputRelation`
(the relaxed relation `R̃²_{C,δ}`). This is exactly the per-prefix guarantee the MCA decode provides
(ABF26 Remark 6.7): the recorded transcript carries a `δ`-close decoded codeword pair, and every
honest continuation's claim is the `γ`-combination of its messages.

Both completions therefore share the *same* pair `decode pre`, the (invertible, `γ₁ ≠ γ₂`) 2×2
system has it as its unique solution, and `toySolve` recovers it via `toySolve_combine`; membership
in `outputRelation` transfers by `rfl`. The algebraic solve is the in-file content; the decode is
the carried external (MCA) datum. -/

/-- The toy protocol's acceptance predicate for the rewinding extractor, parameterised by the
prefix-indexed decoded message pair `decode` held invariant by the fork. Completion `(γ, g)` at
prefix `pre` is accepting iff `g` is the honest `γ`-combination of `decode pre` and that pair places
the input in `outputRelation C δ`. -/
def toyAccepts (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    ToyPrefix ι F k → Accepts F (Fin k → F) :=
  fun pre c ↦
    (pre, (![(decode pre).1, (decode pre).2] : Witness (F := F) k))
        ∈ outputRelation (ι := ι) (F := F) k C δ ∧
      c.2 = toyCombine c.1 (decode pre).1 (decode pre).2

/-- **2-special-soundness of the toy rewinding extractor.** From any two accepting completions on
distinct challenges `γ₁ ≠ γ₂`, `toyRewindingExtractor` recovers a witness in `outputRelation`.

Both accepting completions are honest `γ`-combinations of the *same* prefix-fixed pair `decode pre`
(the fork-invariant datum). The 2×2 solve `toySolve γ₁ γ₂ g₁ g₂` therefore recovers exactly that
pair via `toySolve_combine`, and membership transfers by `rfl`. -/
theorem toyRewindingExtractor_twoSpecialSound (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    (toyRewindingExtractor (ι := ι) (F := F) (k := k)).TwoSpecialSound
      (outputRelation (ι := ι) (F := F) k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) := by
  rintro pre ⟨γ₁, g₁⟩ ⟨γ₂, g₂⟩ ⟨hmem, hg₁⟩ ⟨_, hg₂⟩ hγ
  -- `hγ : γ₁ ≠ γ₂`; both `g₁, g₂` are honest combinations of `decode pre = (u₁, u₂)`.
  simp only [toyStmtOf, id, toyRewindingExtractor]
  simp only at hg₁ hg₂
  subst hg₁
  subst hg₂
  rw [toySolve_combine hγ (decode pre).1 (decode pre).2]
  exact hmem

/-! ## The framework predicate, proven for the toy protocol

`knowledgeSoundnessViaRewinding` is the rewinding-flavoured analogue of
`Verifier.knowledgeSoundness` (it carries a *re-runnable* `RewindingExtractor` rather than the
single-run `Extractor.Straightline`). We discharge it for the toy carriers, witnessed by
`toyRewindingExtractor`. -/

/-- **Knowledge soundness via rewinding for Construction 6.2 / 6.9 (proven).** The toy protocol
admits a 2-special-sound rewinding extractor (`toyRewindingExtractor`), hence satisfies the
framework's `knowledgeSoundnessViaRewinding` predicate against `outputRelation`. By
`knowledgeSoundnessViaRewinding.extracts`, whenever a prover beats the 2-special-sound knowledge
error `1/|F|` at a prefix, a valid witness is extractable. -/
theorem toyProtocol_knowledgeSoundnessViaRewinding [Fintype F] (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    knowledgeSoundnessViaRewinding
      (outputRelation (ι := ι) (F := F) k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  ⟨toyRewindingExtractor, toyRewindingExtractor_twoSpecialSound C δ decode⟩

end ToyProblem.Spec
