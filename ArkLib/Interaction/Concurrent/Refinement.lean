/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Observation

/-!
# Forward refinement for dynamic concurrent processes

This file introduces a first process-level refinement notion for the dynamic
concurrent core.

The central notion is `ForwardSimulation` between two `Process.System`s. A
simulation records:

* a relation between implementation and specification states;
* initialization and assumption compatibility;
* a step-matching rule from every implementation transcript to some matching
  specification transcript; and
* a safety-transfer rule from related specification states to implementation
  states.

The matching relation on step transcripts is parameterized by any chosen
`Observation.Process.TranscriptRel`, so the same simulation interface can be
instantiated with controller-path, event, or ticket preservation.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Refinement

/--
`ForwardSimulation impl spec matchStep` is a forward simulation from the
implementation system `impl` to the specification system `spec`.

The meaning is:

* every initial implementation state is related to some initial specification
  state;
* assumptions are preserved from implementation to specification;
* every implementation step transcript can be matched by some specification
  step transcript satisfying `matchStep`;
* related safe specification states imply safe implementation states.

This is intentionally phrased over the dynamic `Process.System` core rather
than any particular concurrent frontend.
-/
structure ForwardSimulation {Party : Type u}
    (impl spec : Process.System Party)
    (matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess :=
        Observation.Process.TranscriptRel.top) where
  stateRel : impl.Proc → spec.Proc → Prop
  init :
    ∀ pImpl, impl.init pImpl →
      ∃ pSpec, spec.init pSpec ∧ stateRel pImpl pSpec
  assumptions :
    ∀ {pImpl pSpec}, stateRel pImpl pSpec →
      impl.assumptions pImpl → spec.assumptions pSpec
  step :
    ∀ {pImpl pSpec}, stateRel pImpl pSpec →
      ∀ trImpl : (impl.step pImpl).spec.Transcript,
        ∃ trSpec : (spec.step pSpec).spec.Transcript,
          matchStep trImpl trSpec ∧
            stateRel ((impl.step pImpl).next trImpl) ((spec.step pSpec).next trSpec)
  safe :
    ∀ {pImpl pSpec}, stateRel pImpl pSpec →
      spec.safe pSpec → impl.safe pImpl

namespace ForwardSimulation

/--
Choose the matching specification transcript for one implementation transcript.
-/
noncomputable def matchTranscript {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    {pImpl pSpec : _}
    (hrel : sim.stateRel pImpl pSpec)
    (trImpl : (impl.step pImpl).spec.Transcript) :
    (spec.step pSpec).spec.Transcript :=
  Classical.choose (sim.step hrel trImpl)

/--
The chosen matching transcript satisfies `matchStep` and preserves the state
relation to the next residual states.
-/
theorem matchTranscript_spec {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    {pImpl pSpec : _}
    (hrel : sim.stateRel pImpl pSpec)
    (trImpl : (impl.step pImpl).spec.Transcript) :
    matchStep trImpl (sim.matchTranscript hrel trImpl) ∧
      sim.stateRel ((impl.step pImpl).next trImpl)
        ((spec.step pSpec).next (sim.matchTranscript hrel trImpl)) :=
  Classical.choose_spec (sim.step hrel trImpl)

/--
`matchedState sim run hrel n` is the specification-side state reached after
matching the first `n` steps of the implementation run `run`, starting from an
initial related specification state witnessed by `hrel`.
-/
noncomputable def matchedState {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    (n : Nat) → {qSpec : spec.Proc // sim.stateRel (run.state n) qSpec}
  | 0 => ⟨pSpec, by simpa [Process.Run.initial] using hrel⟩
  | n + 1 =>
      let prev := sim.matchedState run hrel n
      let trSpec := sim.matchTranscript prev.2 (run.transcript n)
      let hspec := sim.matchTranscript_spec prev.2 (run.transcript n)
      ⟨(spec.step prev.1).next trSpec, by
        dsimp [trSpec]
        rw [run.next_state n]
        exact hspec.2⟩

/--
The specification transcript chosen to match the `n`th implementation step of
the run `run`, relative to the initial related specification state witnessed by
`hrel`.
-/
noncomputable def matchedTranscript {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec)
    (n : Nat) :
    (spec.step (sim.matchedState run hrel n).1).spec.Transcript :=
  sim.matchTranscript (sim.matchedState run hrel n).2 (run.transcript n)

/--
`mapRun sim run hrel` is the specification run obtained by recursively matching
every step of the implementation run `run`, starting from an initial related
specification state witnessed by `hrel`.
-/
noncomputable def mapRun {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    Process.Run spec.toProcess where
  state n := (sim.matchedState run hrel n).1
  transcript n := sim.matchedTranscript run hrel n
  next_state n := by
    rfl

/--
At every step index `n`, the mapped specification run remains related to the
implementation run by `stateRel`.
-/
theorem stateRel_mapRun {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ∀ n, sim.stateRel (run.state n) ((sim.mapRun run hrel).state n)
  | n => (sim.matchedState run hrel n).2

/--
At every step index `n`, the mapped specification transcript matches the
implementation transcript by `matchStep`.
-/
theorem match_mapRun {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec) :
    ∀ n,
      matchStep (run.transcript n) ((sim.mapRun run hrel).transcript n)
  | n => (sim.matchTranscript_spec (sim.matchedState run hrel n).2 (run.transcript n)).1

/--
If every state along the mapped specification run is safe, then every state
along the implementation run is safe.
-/
theorem safe_of_mapRun {Party : Type u}
    {impl spec : Process.System Party}
    {matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess}
    (sim : ForwardSimulation impl spec matchStep)
    (run : Process.Run impl.toProcess)
    {pSpec : spec.Proc}
    (hrel : sim.stateRel run.initial pSpec)
    (hsafe :
      ∀ n, spec.safe ((sim.mapRun run hrel).state n)) :
    ∀ n, impl.safe (run.state n)
  | n => sim.safe (sim.stateRel_mapRun run hrel n) (hsafe n)

end ForwardSimulation

end Refinement
end Concurrent
end Interaction
