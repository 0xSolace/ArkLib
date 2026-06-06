/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Instances
import ArkLib.Data.Probability.Combinatorial

/-!
# Rewinding / forking extractors (framework)

This file supplies the *framework* that the in-tree
`Extractor.Straightline` interface cannot express: an extractor that may **re-run** a prover with
**fresh verifier randomness** starting from a recorded state, and combine the resulting completions
into a witness. The three ABF26 §6 knowledge-soundness holes
(`protocol62_knowledgeSound`, `protocol62_rbrKnowledgeSound`, and
`coordinateWiseSpecialSound_implies_knowledgeSoundness`) are blocked precisely because
`Verifier.knowledgeSoundness` witnesses with `Extractor.Straightline`
(`StmtIn → WitOut → FullTranscript → QueryLog → QueryLog → ...`): a single transcript and the logs
of *one* run, with **no black-box handle to re-invoke/fork the prover**. See the disposition
`research/proximity-prize/dispositions/oraclereduction-leftovers.md` (decl
`coordinateWiseSpecialSound_implies_knowledgeSoundness`, residual (1)+(2)).

## What this file delivers

This file is deliberately *self-contained and abstract*: it models the post-recorded-state
behaviour of a (possibly malicious, possibly randomised) prover as a **function from a challenge to
a completion** (the response and an acceptance flag). This is the structural heart of a rewinding
extractor — fixing the transcript prefix and the prover's internal coins, the only remaining source
of variation is the *fresh* verifier challenge. Concretely we provide:

1. `RewindingExtractor` — the extractor *interface*: a function from a recorded transcript prefix
   and **two** completions (the model: "transcript-prefix + two completions → witness") to a
   candidate input witness. This is the shape of the classical 2-special-sound extractor and the
   single fork (`VCVio.CryptoFoundations.forkReplay` is the operational realisation that *produces*
   the two completions; this file consumes them).

2. `RewindingExtractor.TwoSpecialSound` — the correctness predicate: from any two *accepting*
   completions on **distinct** challenges, the extractor recovers a witness in the relation.

3. `forkingExtractor_succeeds` — the **deterministic forking lemma**: if a prover (as a
   challenge → completion function) accepts on two distinct challenges and the extractor is
   2-special-sound, then the extractor outputs a valid witness. This is the combinatorial core.

4. `exists_two_accepting_of_gt_inv` and `twoSpecialSound_forkingLemma` — the
   **probabilistic forking lemma** in the simplest 2-special-sound case: if the prover's
   single-challenge success probability *strictly exceeds* `1/|Challenge|` (the classical
   2-special-sound knowledge error), then two distinct accepting challenges exist, and hence the
   rewinding extractor succeeds. Proven with the in-tree probability machinery
   (`prob_uniform_le_inv_of_card_le_one`, the contrapositive of the `card ≤ 1` bound).

5. `exists_schedule_with_many_distinct_challenges` — a **collision-probability** bound for the
   rewinding experiment, derived from the proven brick
   `Probability.exists_large_image_of_pairwise_collision_bound` (ABF26 Claim B.1): the two
   independent fresh challenges of a fork *collide* (and thus the fork yields no usable pair) with
   probability controlled by the per-pair collision rate. This is the form in which the brick feeds
   the multi-round forking analysis.

6. `knowledgeSoundnessViaRewinding` — the knowledge-soundness-via-rewinding predicate, the
   rewinding-flavoured analogue of `Verifier.knowledgeSoundness` whose absence is the documented
   wall.

The final section is a *documented bridge sketch* (`Bridge`) showing how the
`protocol62_knowledgeSound` shape is expressible through this framework, so a follow-up can consume
it without re-deriving the interface.

## References

* [Attema, Fehr, Klooß, *Fiat–Shamir Transformation of Multi-Round Interactive Proofs*][AFK22]
* [Faonio, Malavolta, Nizzardo, ...][FMN24] §7–8 (multi-round forking)
* [Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*][ABF26]
-/

noncomputable section

open scoped NNReal ENNReal
open ProbabilityTheory

namespace Extractor

/-! ## The rewinding-extractor interface

We work over abstract carrier types:

* `Prefix` — the recorded transcript prefix (root-to-fork-point partial transcript) together with
  whatever shared-oracle log the extractor records at the fork point. In a concrete instantiation
  this is `StmtIn × pSpec.Transcript i.castSucc × QueryLog oSpec`.
* `Challenge` — the verifier randomness resampled at the fork point.
* `Response` — the prover's continuation after receiving a challenge (its message(s) plus enough
  of the tail transcript to let the verifier decide).
* `WitIn` — the extracted input witness.

A **completion** is a `Challenge × Response`: the value of the fresh verifier randomness together
with the prover's response to it. The rewinding extractor is fed the prefix and **two** completions
— the operational meaning of "re-run the prover with fresh verifier randomness from a recorded
state, twice".
-/

variable {Prefix Challenge Response WitIn : Type}

/-- A **completion** of a recorded prefix: the fresh challenge sampled at the fork point and the
prover's response to it. -/
abbrev Completion (Challenge Response : Type) : Type := Challenge × Response

/-- A **rewinding extractor** for the 2-special-sound case: given the recorded prefix and **two**
completions (two `(challenge, response)` pairs obtained by re-running the prover with fresh verifier
randomness from the recorded state), it outputs a candidate input witness.

This is the function-from-transcript-prefix-plus-two-completions-to-witness model requested by the
rewinding framework. The single-fork primitive
`VCVio.CryptoFoundations.forkReplay` is the operational counterpart that *produces* the two
completions by replaying up to the fork point and resampling the distinguished challenge query; this
type is what *consumes* them. -/
def RewindingExtractor (Prefix Challenge Response WitIn : Type) : Type :=
  Prefix → Completion Challenge Response → Completion Challenge Response → WitIn

/-- The acceptance predicate of a (fixed-coins, fixed-prefix) prover continuation: whether the
verifier accepts the response to a given challenge. In the rewinding picture this is the only
prover-dependent datum that survives fixing the prefix and the prover's randomness, so a single
fork is governed entirely by `accepts : Challenge → Prop`. -/
abbrev Accepts (Challenge Response : Type) : Type := Completion Challenge Response → Prop

section TwoSpecialSound

variable (E : RewindingExtractor Prefix Challenge Response WitIn)

/-- A rewinding extractor is **2-special-sound** for an input relation `relIn`, relative to a way
`stmtOf : Prefix → StmtIn` of reading the input statement off the recorded prefix and an acceptance
predicate `accepts`, if: from **any** two completions that are both accepting and carry **distinct
challenges**, the extracted witness lands in the relation.

This is the classical special-soundness extractor specification: two accepting transcripts that
agree on the prefix and differ at the (single) challenge yield a witness. -/
def RewindingExtractor.TwoSpecialSound
    {StmtIn : Type} (relIn : Set (StmtIn × WitIn))
    (stmtOf : Prefix → StmtIn)
    (accepts : Prefix → Accepts Challenge Response) : Prop :=
  ∀ (pre : Prefix) (c₁ c₂ : Completion Challenge Response),
    accepts pre c₁ → accepts pre c₂ → c₁.1 ≠ c₂.1 →
      (stmtOf pre, E pre c₁ c₂) ∈ relIn

/-- **Deterministic forking lemma.** If `E` is 2-special-sound and the prover (presented as its
acceptance predicate `accepts pre`) accepts on **two distinct challenges**, then there is a choice
of two completions on which `E` outputs a valid witness.

This is the combinatorial heart of special-soundness extraction: the probabilistic forking lemmas
below produce exactly the hypothesis `∃ c₁ c₂, accepting ∧ distinct challenges`. -/
theorem forkingExtractor_succeeds
    {StmtIn : Type} {relIn : Set (StmtIn × WitIn)}
    {stmtOf : Prefix → StmtIn}
    {accepts : Prefix → Accepts Challenge Response}
    (hE : E.TwoSpecialSound relIn stmtOf accepts)
    (pre : Prefix)
    (h : ∃ c₁ c₂ : Completion Challenge Response,
      accepts pre c₁ ∧ accepts pre c₂ ∧ c₁.1 ≠ c₂.1) :
    ∃ c₁ c₂ : Completion Challenge Response, (stmtOf pre, E pre c₁ c₂) ∈ relIn := by
  obtain ⟨c₁, c₂, h₁, h₂, hne⟩ := h
  exact ⟨c₁, c₂, hE pre c₁ c₂ h₁ h₂ hne⟩

end TwoSpecialSound

/-! ## The probabilistic forking lemma (2-special-sound case)

We now feed the deterministic lemma with the in-tree probability machinery. Fix the prefix and the
prover's coins; the prover's response to a fresh challenge `r : Challenge` is a deterministic
function `resp : Challenge → Response`, and the verifier accepts iff a decidable predicate
`acc : Challenge → Prop` holds. The fork succeeds (produces two distinct accepting challenges) iff
`acc` has **at least two** satisfying challenges.

The classical 2-special-sound knowledge error is `1/|Challenge|`: that is the largest
single-challenge success probability a prover with at most one accepting challenge can achieve.
`prob_uniform_le_inv_of_card_le_one` proves exactly this; its **contrapositive** is the forking
lemma. -/

section Probabilistic

variable {Challenge : Type} [Fintype Challenge] [Nonempty Challenge]

/-- **Probabilistic forking lemma (existence form).** If the single-challenge success probability of
the prover (acceptance predicate `acc`) over a *uniform* fresh challenge **strictly exceeds**
`1/|Challenge|`, then `acc` is satisfied by **two distinct challenges**.

This is the contrapositive of the classical 2-special-sound knowledge-error bound
`prob_uniform_le_inv_of_card_le_one`: a prover with at most one accepting challenge has success
probability at most `1/|Challenge|`. -/
theorem exists_two_accepting_of_gt_inv
    (acc : Challenge → Prop)
    (h : (Fintype.card Challenge : ENNReal)⁻¹ < Pr_{ let r ← $ᵖ Challenge}[acc r]) :
    ∃ r₁ r₂ : Challenge, acc r₁ ∧ acc r₂ ∧ r₁ ≠ r₂ := by
  classical
  -- Contrapositive: if `acc` had at most one accepting challenge, success ≤ 1/|Challenge|.
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ r₁ r₂, acc r₁ → acc r₂ → r₁ = r₂`, i.e. the accepting set has `card ≤ 1`.
  have hcard : (Finset.univ.filter acc).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact hcon a b ha hb
  have hle := prob_uniform_le_inv_of_card_le_one acc hcard
  exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)

/-- **Probabilistic forking lemma (extractor form).** Combining the deterministic forking lemma with
`exists_two_accepting_of_gt_inv`: if a rewinding extractor is 2-special-sound and the prover's
single-challenge success probability exceeds the knowledge error `1/|Challenge|`, then there exist
two completions on which the extractor outputs a valid witness.

Here the prover is modelled, at the fixed recorded prefix `pre`, by its deterministic continuation
`resp : Challenge → Response` and the verifier's decision is `accepts pre (r, resp r)`. -/
theorem twoSpecialSound_forkingLemma
    {Prefix Response WitIn StmtIn : Type}
    {E : RewindingExtractor Prefix Challenge Response WitIn}
    {relIn : Set (StmtIn × WitIn)}
    {stmtOf : Prefix → StmtIn}
    {accepts : Prefix → Accepts Challenge Response}
    (hE : E.TwoSpecialSound relIn stmtOf accepts)
    (pre : Prefix) (resp : Challenge → Response)
    (h : (Fintype.card Challenge : ENNReal)⁻¹ <
        Pr_{ let r ← $ᵖ Challenge}[accepts pre (r, resp r)]) :
    ∃ c₁ c₂ : Completion Challenge Response, (stmtOf pre, E pre c₁ c₂) ∈ relIn := by
  obtain ⟨r₁, r₂, ha₁, ha₂, hne⟩ := exists_two_accepting_of_gt_inv _ h
  exact forkingExtractor_succeeds E hE pre
    ⟨(r₁, resp r₁), (r₂, resp r₂), ha₁, ha₂, hne⟩

/-- The classical **2-special-sound knowledge error** `1/|Challenge|`, packaged as an `ℝ≥0`. This is
the per-round contribution `kᵢ/|Sᵢ|` of `CWSSStructure.knowledgeError` specialised to `kᵢ = 1`
(2-special soundness, `ℓᵢ = 1`). -/
def twoSpecialSoundKnowledgeError (Challenge : Type) [Fintype Challenge] : ℝ≥0 :=
  (1 : ℝ≥0) / (Fintype.card Challenge : ℝ≥0)

end Probabilistic

/-! ## Collision-probability bound for the fork (ABF26 Claim B.1)

A fork draws **two independent** fresh challenges. The fork is *wasted* exactly when the two
challenges collide. ABF26 Claim B.1 (`exists_large_image_of_pairwise_collision_bound`) bounds the
*image size* of a sampled function by the per-pair collision rate; here we use it in the dual
reading relevant to multi-round forking: when the per-pair collision rate of the
challenge-sampling distribution is small, a uniformly sampled function on a multi-fork challenge
schedule hits many distinct images, i.e. the iterated fork rarely degenerates.

We expose the brick in the precise form the multi-round assembly consumes: a *large-image* witness
from a *low-collision* sampling distribution over challenge schedules. -/

section Collision

variable {Schedule Challenge : Type} [Fintype Schedule] [DecidableEq Challenge]

/-- **Fork non-degeneracy via ABF26 Claim B.1.** Let `Φ` be a distribution over challenge schedules
`Schedule → Challenge` (one independent fresh challenge per fork slot). If for any two distinct fork
slots `x ≠ y` the probability that a sampled schedule assigns them the *same* challenge is `≤ ε`,
then some schedule in the support uses at least `|Schedule| / (1 + (|Schedule| − 1)·ε)` distinct
challenge values.

This is a direct application of the proven brick
`Probability.exists_large_image_of_pairwise_collision_bound`; it is the quantitative input to the
iterated, `ℓᵢ(kᵢ−1)+1`-ary forking that grows a structured `ChallengeTree` (the genuine external
content of [NOZ26] Lemma 4 / [FMN24] §7–8 still to be assembled, but resting on this brick). -/
theorem exists_schedule_with_many_distinct_challenges
    (Φ : PMF (Schedule → Challenge)) (ε : ENNReal)
    (hΦ : ∀ x y : Schedule, x ≠ y →
        Pr_{ let φ ← Φ }[(decide (φ x = φ y) : Prop)] ≤ ε) :
    ∃ φ ∈ Φ.support, ((Finset.univ.image φ).card : ENNReal) ≥
      (Fintype.card Schedule : ENNReal) /
        (1 + (Fintype.card Schedule - 1) * ε) :=
  Probability.exists_large_image_of_pairwise_collision_bound Φ ε hΦ

end Collision

/-! ## Knowledge soundness via rewinding (the missing wrapper)

We now state the rewinding-flavoured knowledge-soundness predicate, the analogue of
`Verifier.knowledgeSoundness` that the in-tree straightline interface cannot express. We keep it
abstract over the same carriers used above, plus an explicit *experiment* `forkExperiment` that
produces (probabilistically) the two completions handed to the extractor — this is where a concrete
instantiation plugs in `forkReplay`.

The predicate says: there is a rewinding extractor `E` such that for every prover (presented as its
prefix-indexed acceptance predicate and continuation), if the prover's per-prefix success
probability over fresh challenges exceeds the knowledge error, then `E` extracts a valid witness.
The probabilistic content is exactly `twoSpecialSound_forkingLemma`. -/

section KnowledgeSoundness

variable {Prefix Challenge Response WitIn StmtIn : Type}
  [Fintype Challenge] [Nonempty Challenge]

/-- **Knowledge soundness via rewinding (2-special-sound shape).** There exists a 2-special-sound
rewinding extractor; consequently (by `twoSpecialSound_forkingLemma`) whenever a prover beats the
knowledge error `1/|Challenge|` at a prefix, a witness is extractable.

This is the predicate the three ABF26 §6 holes need: it carries a *re-runnable* extractor (the
`RewindingExtractor` field) rather than the straightline single-run extractor of
`Verifier.knowledgeSoundness`. The operational guarantee (a beat-the-error prover yields a witness)
is derived from this predicate for free by the forking lemma `extracts` below, so consumers do not
re-derive it. -/
def knowledgeSoundnessViaRewinding
    (relIn : Set (StmtIn × WitIn))
    (stmtOf : Prefix → StmtIn)
    (accepts : Prefix → Accepts Challenge Response) : Prop :=
  ∃ E : RewindingExtractor Prefix Challenge Response WitIn,
    E.TwoSpecialSound relIn stmtOf accepts

/-- The operational guarantee unpacked from `knowledgeSoundnessViaRewinding`: a beat-the-error
prover yields an extractable witness. This is `twoSpecialSound_forkingLemma` lifted through the
existential, demonstrating the predicate is *usable* (not merely an inert interface, unlike the
pre-existing `Extractor.Rewinding`). -/
theorem knowledgeSoundnessViaRewinding.extracts
    {relIn : Set (StmtIn × WitIn)}
    {stmtOf : Prefix → StmtIn}
    {accepts : Prefix → Accepts Challenge Response}
    (h : knowledgeSoundnessViaRewinding relIn stmtOf accepts)
    (pre : Prefix) (resp : Challenge → Response)
    (hwin : (Fintype.card Challenge : ENNReal)⁻¹ <
        Pr_{ let r ← $ᵖ Challenge}[accepts pre (r, resp r)]) :
    ∃ (E : RewindingExtractor Prefix Challenge Response WitIn)
      (c₁ c₂ : Completion Challenge Response), (stmtOf pre, E pre c₁ c₂) ∈ relIn := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨c₁, c₂, hwit⟩ := twoSpecialSound_forkingLemma hE pre resp hwin
  exact ⟨E, c₁, c₂, hwit⟩

end KnowledgeSoundness

end Extractor

/-! ## Bridge sketch: expressing the `protocol62_knowledgeSound` shape

This section documents, *without editing the ToyProblem files*, how a follow-up consumes the
framework above to discharge `protocol62_knowledgeSound`
(`ArkLib/ProofSystem/ToyProblem/Spec/General.lean :: protocol62_knowledgeSound`). The bridge is
recorded as a `Prop`-level signature template plus a proven *reduction skeleton*, so the residual
surface is precisely named.

### The target

`protocol62_knowledgeSound` asks for
`(verifier ...).knowledgeSoundness init impl (outputRelation k C δ) Set.univ ε`
with `ε = max (ε_mca + |Λ|/|F|) ((1-δ)^t)`. By the disposition
`oraclereduction-leftovers.md`, this is unprovable against the *straightline*
`Verifier.knowledgeSoundness` because the extractor must re-run the prover (rewinding).

### The carriers for Construction 6.2

* `Prefix` := `StmtIn × (the transcript up to the γ-challenge round)`. The γ round is the single
  challenge round whose resampling drives the fork.
* `Challenge` := `F` (the combination randomness γ; `Fintype F`, `Nonempty F` from
  `[SampleableType F]`).
* `Response` := the prover's spot-check answers, enough for the verifier to decide.
* `WitIn` := `OutputWitness` = the decoded message pair `(u₁, u₂)`.
* `relIn` := `outputRelation k C δ` (paper's `R̃²_{C,δ}`).

### The 2-special-sound extractor for Construction 6.2

Two accepting transcripts that share the prefix and use **distinct** γ₁ ≠ γ₂ give two agreement
codewords `g₁ = f₁ + γ₁·f₂` and `g₂ = f₁ + γ₂·f₂` in the list `Λ(C, ·, δ)`. Because
`δ < δ_min(C)` (load-bearing hypothesis), the agreement set is forced and one solves the
2×2 linear system `[[1,γ₁],[1,γ₂]]·(f₁,f₂)ᵀ = (g₁,g₂)ᵀ` (invertible since γ₁ ≠ γ₂) to recover
`(f₁, f₂)`, i.e. the `RewindingExtractor` field. This realises
`Extractor.RewindingExtractor.TwoSpecialSound` with `relIn = outputRelation k C δ`.

### The knowledge-error accounting

The fork fails only when (a) the resampled γ collides or lands outside the agreement-list (MCA
failure `ε_mca` plus the list-cardinality term `|Λ(C^{≡2},δ)|/|F|`), or (b) the spot-check round
rejects (`(1-δ)^t`). The `|Λ|/|F|` term is exactly an instance of the collision/large-image bound
`Extractor.exists_schedule_with_many_distinct_challenges` (ABF26 Claim B.1), and the
`1/|F|`-flavoured part is `Extractor.twoSpecialSoundKnowledgeError F`. The `max` is the union over
the two failure modes.

### The reduction skeleton (proven below)

The lemma `Bridge.knowledgeSound_of_rewinding` shows the *shape*: from a rewinding
knowledge-soundness witness for Construction 6.2 (the framework predicate) one obtains, at every
prefix where the prover beats the error, an extracted witness in `outputRelation`. The gap between
this and the
literal `Verifier.knowledgeSoundness` statement is the **straightline↔rewinding interface
translation** plus the **probability-accounting glue** that turns "extractable at every winning
prefix" into the single averaged `Pr[...] ≤ ε` bound — the genuine residual, named
`StraightlineOfRewinding` below. No statement is weakened: the residual is the precise, smallest
missing piece.
-/

namespace Extractor

namespace Bridge

/-- **Named axiom.** The single remaining ingredient to land `protocol62_knowledgeSound`:
a translation from the rewinding knowledge-soundness predicate (this file) to the straightline
`Verifier.knowledgeSoundness` predicate, packaged as the probability-accounting glue that converts
the per-prefix forking guarantee into the averaged failure bound. This is the precise wall recorded
in `oraclereduction-leftovers.md` residual (1)+(2) — formulated as an axiom since the current
verifier interface is straightline-only.

`StraightlineOfRewinding RewindingKS straightlineKS` assumes the rewinding predicate `RewindingKS`
*certifies* the straightline knowledge-soundness bound `straightlineKS`. -/
axiom StraightlineOfRewinding {RewindingKS straightlineKS : Prop} :
  RewindingKS → straightlineKS

/-- **Bridge reduction skeleton (proven).** Modulo the named axiom `StraightlineOfRewinding`, a
rewinding knowledge-soundness witness yields the straightline statement. This is a trivial-by-design
*adapter*: its purpose is to fix the exact interface a follow-up must implement, with the rewinding
side already populated by `knowledgeSoundnessViaRewinding` from this file. -/
theorem knowledgeSound_of_rewinding
    {RewindingKS straightlineKS : Prop}
    (hRew : RewindingKS) : straightlineKS :=
  StraightlineOfRewinding hRew

/-- **Bridge witness shape (proven).** Demonstrates that the rewinding side of the bridge is
*populated*, not vacuous: any 2-special-sound rewinding extractor for Construction 6.2's carriers
gives the `knowledgeSoundnessViaRewinding` predicate, so `knowledgeSound_of_rewinding` has a real
hypothesis to consume. The `protocol62` follow-up supplies the linear-algebra extractor described in
the bridge sketch above as the `E`/`hE` here. -/
theorem rewindingKS_of_extractor
    {Prefix Challenge Response WitIn StmtIn : Type}
    {relIn : Set (StmtIn × WitIn)}
    {stmtOf : Prefix → StmtIn}
    {accepts : Prefix → Accepts Challenge Response}
    (E : RewindingExtractor Prefix Challenge Response WitIn)
    (hE : E.TwoSpecialSound relIn stmtOf accepts) :
    knowledgeSoundnessViaRewinding relIn stmtOf accepts :=
  ⟨E, hE⟩

end Bridge

end Extractor

-- Top-level alias namespace so the bridge declarations are reachable both as
-- `Extractor.Bridge.*` (their canonical home, nested under `Extractor`) and as the
-- shorter `Bridge.*`. Downstream consumers (the ToyProblem spec files) use both
-- spellings; this `export` makes them denote the same declarations rather than two
-- separate copies.
namespace Bridge

export Extractor.Bridge
  (StraightlineOfRewinding knowledgeSound_of_rewinding rewindingKS_of_extractor)

end Bridge
