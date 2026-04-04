/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Fairness

/-!
# Safety and liveness predicates over concurrent runs

This file packages the basic temporal predicates that will sit on top of the
new run and fairness layers.

The focus here is intentionally modest:

* lift state predicates to run predicates;
* define always/eventually/infinitely-often state properties of runs;
* define admissibility and safety of runs for `Process.System`;
* define what it means for a system to satisfy a run property under a chosen
  fairness assumption.

This is a semantic layer, not yet a temporal-logic DSL.
-/

universe u v w

namespace Interaction
namespace Concurrent

namespace Process
namespace Run

/-- A run predicate for the process `process`. -/
abbrev Pred {Party : Type u} (process : Process Party) :=
  Process.Run process → Prop

/-- A state predicate for the process `process`. -/
abbrev StatePred {Party : Type u} (process : Process Party) :=
  process.Proc → Prop

/-- `AlwaysState P run` means that the state predicate `P` holds at every state
of the run `run`. -/
def AlwaysState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ∀ n, P (run.state n)

/-- `EventuallyState P run` means that `P` holds at some state of `run`. -/
def EventuallyState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ∃ n, P (run.state n)

/-- `InfinitelyOftenState P run` means that `P` holds at arbitrarily late
states of `run`. -/
def InfinitelyOftenState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P (run.state n)

/-- Monotonicity of `AlwaysState`. -/
theorem alwaysState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process}, AlwaysState P run → AlwaysState Q run := by
  intro run hP n
  exact himp _ (hP n)

/-- Monotonicity of `EventuallyState`. -/
theorem eventuallyState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process}, EventuallyState P run → EventuallyState Q run := by
  rintro run ⟨n, hP⟩
  exact ⟨n, himp _ hP⟩

/-- Monotonicity of `InfinitelyOftenState`. -/
theorem infinitelyOftenState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process},
      InfinitelyOftenState P run → InfinitelyOftenState Q run := by
  intro run hP N
  rcases hP N with ⟨n, hn, hPn⟩
  exact ⟨n, hn, himp _ hPn⟩

end Run

namespace System

/-- A run of `system` is admissible when the ambient assumptions hold at every
state along the run. -/
def Admissible {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  Process.Run.AlwaysState system.assumptions run

/-- A run of `system` is safe when the safety predicate holds at every state
along the run. -/
def Safe {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  Process.Run.AlwaysState system.safe run

/-- A run starts from an initial state when its first residual state satisfies
`system.init`. -/
def Initial {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  system.init run.initial

/--
`Satisfies system fairness property` means:
every initial admissible run of `system` that satisfies the fairness
assumption `fairness` also satisfies the run property `property`.
-/
def Satisfies {Party : Type u} (system : Process.System Party)
    (fairness property : Process.Run.Pred system.toProcess) : Prop :=
  ∀ run : Process.Run system.toProcess,
    Initial system run →
      Admissible system run →
        fairness run →
          property run

/--
If a run is safe and every safe state satisfies `P`, then `P` holds at every
state along the run.
-/
theorem alwaysState_of_safe {Party : Type u} (system : Process.System Party)
    {P : Process.Run.StatePred system.toProcess}
    (himp : ∀ p, system.safe p → P p) :
    ∀ {run : Process.Run system.toProcess},
      Safe system run → Process.Run.AlwaysState P run := by
  intro run hsafe n
  exact himp _ (hsafe n)

end System

end Process
end Concurrent
end Interaction
