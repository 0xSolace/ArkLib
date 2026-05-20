/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Erasure
import ArkLib.Data.CodingTheory.InterleavedCode

/-!
# Toy problem definitions (ABF26 §6)

Statement-layer definitions for the toy problem of ABF26 §6 — the small
protocol whose analysis motivates mutual correlated agreement (MCA) over
mere correlated agreement (CA), and which doubles as a textbook example of
the complexities of real list-decoding-based protocol analyses.

This file is the code-theoretic foundation:

* `ToyProblem.relation` — Definition 6.1, the toy problem relation
  `R_C^ℓ` over a code `C` and constraint shape `ℓ`.
* `ToyProblem.relaxedRelation` — Definition 6.3, the `δ`-relaxed version
  used as the soundness target.
* `ToyProblem.SupportsErasureCorrection` — Definition 6.4, the erasure-
  correction predicate for a code with a stated correction-time budget.
  Re-exported from `CodingTheory.SupportsErasureCorrection` in
  [`ArkLib/Data/CodingTheory/Erasure.lean`](../../Data/CodingTheory/Erasure.lean)
  (the predicate is generic across proof systems).
* `ToyProblem.winningSet` — Definition 6.11, the set of "winning"
  challenges `γ` for the simplified IOR attack of §6.4.

Protocol-level items (Construction 6.2, Lemmas 6.6 / 6.8, Construction
6.9, Lemma 6.10) live in `ToyProblem/Spec/General.lean` and are stated
over ArkLib's `OracleReduction/` machinery, following the conventions
of `ProofSystem/Fri/Spec/` and `ProofSystem/Sumcheck/Spec/`. Soundness
bounds (L6.5, L6.12, L6.13) live in `ToyProblem/SoundnessBounds.lean`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS25]
-/

namespace ToyProblem

open Code InterleavedCode
open scoped NNReal

variable {ι F : Type*} [Fintype ι] [Field F]

/-- **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`).

Given a base code `C ⊆ (ι → F)` (the paper writes `C : F^k → (F^s)^n`
for an `F`-additive code; we use the Set-form for compatibility with the
rest of ArkLib's coding-theory API), a constraint shape `(ℓ, k)`, a
linear-constraint vector `v : Fin k → F`, and constraint values
`μ : Fin ℓ → F`, the toy problem relation pairs an input
`((v, μ), W)`, where `W : Fin ℓ → ι → F` is a stack of `ℓ` words,
with the witness "underlying message matrix" `M : Fin ℓ → Fin k → F`
such that:

  * each row `W i` is a codeword of `C`, with `M i` an associated
    pre-image under some `F`-linear encoding,
  * the linear constraint `(M · v) i = μ i` holds for every `i`.

For the linear-code special case, the pre-image `M i` is unique (the
chosen encoding is a bijection from `Fin k → F` onto `C`); the
existence form below subsumes both linear and general `F`-additive
codes.

This is what the paper calls "constrained codes". -/
def relation {k ℓ : ℕ} (C : Set (ι → F))
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → F) : Prop :=
  ∃ M : Fin ℓ → Fin k → F,
    (∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ i, W i = encode (M i)) ∧
    ∀ i, ∑ j, M i j * v j = μ i

/-- **Definition 6.3 of [ABF26]** (relaxed toy problem relation
`R̃_{C,δ}^ℓ`).

The relaxed relation only requires that the input word stack `W` is
`δ`-close (in interleaved Hamming distance) to a valid instance `W*`
of `relation C v μ`. This is both necessary (the verifier in the IOR
only reads a few entries of `W`) and sufficient (for downstream uses)
for soundness with respect to `δ`. -/
def relaxedRelation {k ℓ : ℕ} (C : Set (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ : Fin ℓ → F) (W : Fin ℓ → ι → F) : Prop :=
  ∃ Wstar : Fin ℓ → ι → F,
    relation C v μ Wstar ∧
      -- Interleaved Hamming distance between the two word stacks is at
      -- most `δ`: at least `(1 - δ) · |ι|` coordinates agree on every
      -- row.
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i, ∀ j ∈ S, W i j = Wstar i j

/-- **Definition 6.4 of [ABF26]** (erasure-correction predicate) —
re-export of the generic `CodingTheory.SupportsErasureCorrection` (see
[`ArkLib/Data/CodingTheory/Erasure.lean`](../../Data/CodingTheory/Erasure.lean)).
Exposed under the `ToyProblem` namespace so existing references to
`ToyProblem.SupportsErasureCorrection` continue to resolve. -/
@[reducible] def SupportsErasureCorrection [DecidableEq F]
    (C : Set (ι → F)) (ecor : ℕ) : Prop :=
  CodingTheory.SupportsErasureCorrection C ecor

/-- **Definition 6.11 of [ABF26]** (winning set `Ω^{f_1, f_2}_{v, μ_1, μ_2}`).

For the simplified IOR `T'[C, t]` of §6.4 (Construction 6.9), this is the
set of challenges `γ ∈ F` for which the "new instance" output by the
verifier — `(v, μ_1 + γ·μ_2, f_1 + γ·f_2)` — lies in the relaxed
relation `R̃_{C,δ}^1`. The soundness error of `T'` is then exactly
`max_{x,y} |Ω^y_x| / |F|` over inputs `(x, y)` whose original instance
`(v, μ_1, μ_2)` violates `R̃_{C,δ}^2`. -/
def winningSet {k : ℕ} (C : Set (ι → F)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F)
    (f₁ f₂ : ι → F) : Set F :=
  { γ | relaxedRelation (k := k) (ℓ := 1) C δ v
         (fun _ ↦ μ₁ + γ * μ₂)
         (fun _ j ↦ f₁ j + γ * f₂ j) }

end ToyProblem
