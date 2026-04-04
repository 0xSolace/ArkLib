/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Run

/-!
# Observation equivalence for concurrent processes

This file packages the local observations induced by finite and infinite
executions of `Concurrent.Process`, and provides reusable transcript-matching
relations for later refinement and fairness layers.

The key idea is to erase a step's dependent local-observation types into a
uniform packed form:

* each visited node contributes one packed observation value;
* each process step contributes a list of such packed observations;
* each finite prefix contributes a list of per-step observation lists.

This packed representation is intentionally coarse enough to compare different
concrete transcripts that expose the same local information to a chosen party.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Observation

/--
`PackedObs` is a locally observed value packaged together with its observation
type, with the value lifted into a common comparison universe.

This is the simplest uniform carrier for local observations whose precise type
may vary from one node to the next.
-/
abbrev PackedObs := PSigma fun α : Type _ => ULift α

namespace Step
namespace Observed

/--
Forget the dependent indices of an observed sequential transcript and keep only
the concrete packed sequence of observations that was exposed locally.
-/
def toList {Party : Type u} [DecidableEq Party] {me : Party} :
    {spec : Interaction.Spec.{w}} →
      {semantics : Interaction.Spec.Decoration (StepContext Party) spec} →
      {tr : Interaction.Spec.Transcript spec} →
      Interaction.Concurrent.Step.Observed me semantics tr →
      List PackedObs
  | .done, _, _, .done => []
  | .node _ _, _, _, .step obs rest =>
      ⟨_, ⟨obs⟩⟩ :: toList rest

end Observed

/--
`obsList me step tr` is the packed sequence of local observations available to
the fixed party `me` while the sequential process step `step` executes along
the transcript `tr`.
-/
def obsList {Party : Type u} [DecidableEq Party] (me : Party)
    {P : Type v} (step : Interaction.Concurrent.Step Party P)
    (tr : Interaction.Spec.Transcript step.spec) : List PackedObs :=
  Observed.toList (Interaction.Concurrent.Step.observe me step tr)

end Step

namespace Process
namespace Trace

/--
The per-step packed local observations exposed along a finite complete process
trace.
-/
def observations {Party : Type u} [DecidableEq Party]
    {process : Process Party} (me : Party) :
    {p : process.Proc} → Process.Trace process p → List (List PackedObs)
  | _, .done _ => []
  | p, .step tr tail =>
      Step.obsList me (process.step p) tr :: observations me tail

end Trace

namespace Prefix

/--
The per-step packed local observations exposed along a finite process prefix.
-/
def observations {Party : Type u} [DecidableEq Party]
    {process : Process Party} (me : Party) :
    {p : process.Proc} → {n : Nat} → Process.Prefix process p n →
      List (List PackedObs)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      Step.obsList me (process.step p) tr :: observations me tail

/--
`Rel rel left right` states that the two finite prefixes `left` and `right`
match step-by-step according to the transcript relation `rel`.

The length index forces the two prefixes to have the same number of executed
steps.
-/
def Rel {Party : Type u}
    {left right : Process Party}
    (rel :
      {pL : left.Proc} → {pR : right.Proc} →
        (left.step pL).spec.Transcript →
        (right.step pR).spec.Transcript →
        Prop) :
    {pL : left.Proc} → {pR : right.Proc} → {n : Nat} →
      Process.Prefix left pL n → Process.Prefix right pR n → Prop
  | _, _, _, .nil, .nil => True
  | _, _, _, .step trL tailL, .step trR tailR =>
      rel trL trR ∧ Rel rel tailL tailR

end Prefix

/--
`TranscriptRel left right` is a cross-process relation on one complete process
step transcript of `left` and one complete process step transcript of `right`.

This is the basic matching interface used later by refinement.
-/
abbrev TranscriptRel {Party : Type u}
    (left right : Process Party) :=
  {pL : left.Proc} → {pR : right.Proc} →
    (left.step pL).spec.Transcript →
    (right.step pR).spec.Transcript →
    Prop

namespace TranscriptRel

/-- The permissive transcript relation. -/
def top {Party : Type u} {left right : Process Party} :
    TranscriptRel left right :=
  fun _ _ => True

/-- Conjunction of transcript relations. -/
def inter {Party : Type u} {left right : Process Party}
    (first second : TranscriptRel left right) :
    TranscriptRel left right :=
  fun trL trR => first trL trR ∧ second trL trR

/-- Match two transcripts by equality of their current controlling parties. -/
def byController {Party : Type u} {left right : Process Party} :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    (left.step pL).currentController? trL = (right.step pR).currentController? trR

/-- Match two transcripts by equality of their full controller paths. -/
def byPath {Party : Type u} {left right : Process Party} :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    (left.step pL).controllerPath trL = (right.step pR).controllerPath trR

/-- Match two transcripts by equality of stable external event labels. -/
def byEvent {Party : Type u} {left right : Process Party}
    {Event : Type w}
    (eventL : left.EventMap Event) (eventR : right.EventMap Event) :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    eventL pL trL = eventR pR trR

/-- Match two transcripts by equality of stable tickets. -/
def byTicket {Party : Type u} {left right : Process Party}
    {Ticket : Type w}
    (ticketL : left.Tickets Ticket) (ticketR : right.Tickets Ticket) :
    TranscriptRel left right :=
  fun {pL} {pR} trL trR =>
    ticketL pL trL = ticketR pR trR

end TranscriptRel

namespace Run

/--
The per-step packed local observations exposed along the first `n` steps of the
run `run`.
-/
def observationsUpTo {Party : Type u} [DecidableEq Party]
    {process : Process Party} (me : Party)
    (run : Process.Run process) (n : Nat) : List (List PackedObs) :=
  Process.Prefix.observations me (run.take n)

/--
`RelUpTo rel left right n` states that the first `n` executed steps of the
runs `left` and `right` match step-by-step according to `rel`.
-/
def RelUpTo {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right)
    (leftRun : Process.Run left) (rightRun : Process.Run right) (n : Nat) : Prop :=
  Process.Prefix.Rel rel (leftRun.take n) (rightRun.take n)

/--
`Rel rel left right` states that every finite prefix of the runs `left` and
`right` matches according to `rel`.
-/
def Rel {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right)
    (leftRun : Process.Run left) (rightRun : Process.Run right) : Prop :=
  ∀ n, RelUpTo rel leftRun rightRun n

end Run

end Process
end Observation
end Concurrent
end Interaction
