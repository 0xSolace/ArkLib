/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Bisimulation

/-!
# Common concurrent equivalence notions

This file packages the most useful bisimulation-based equivalence notions for
the current concurrent framework.

The emphasis is pragmatic rather than foundational:

* controller equivalence,
* controller-path equivalence,
* event-trace equivalence,
* ticket equivalence,
* and party-local observational equivalence.

Each notion is just a specialized `Refinement.Bisimulation`, together with the
obvious preservation lemmas exposed under a simpler name.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Equivalence

/-- Controller equivalence preserves the current controller chosen at each
executed step. -/
abbrev Controller {Party : Type u}
    (left right : Process.System Party) :=
  Refinement.Bisimulation left right
    Observation.Process.TranscriptRel.byController
    (Observation.Process.TranscriptRel.byController
      (left := right.toProcess) (right := left.toProcess))

/-- Controller-path equivalence preserves the full controller path of each
executed step. -/
abbrev ControllerPath {Party : Type u}
    (left right : Process.System Party) :=
  Refinement.Bisimulation left right
    Observation.Process.TranscriptRel.byPath
    (Observation.Process.TranscriptRel.byPath
      (left := right.toProcess) (right := left.toProcess))

/-- Trace equivalence preserves the stable external event labels attached to
complete step transcripts. -/
abbrev Trace {Party : Type u} {Event : Type w}
    (left right : Process.System Party)
    (eventLeft : left.toProcess.EventMap Event)
    (eventRight : right.toProcess.EventMap Event) :=
  Refinement.Bisimulation left right
    (Observation.Process.TranscriptRel.byEvent eventLeft eventRight)
    (Observation.Process.TranscriptRel.byEvent
      (left := right.toProcess) (right := left.toProcess) eventRight eventLeft)

/-- Ticket equivalence preserves the stable tickets attached to complete step
transcripts. -/
abbrev Ticket {Party : Type u} {Ticket : Type w}
    (left right : Process.System Party)
    (ticketLeft : left.toProcess.Tickets Ticket)
    (ticketRight : right.toProcess.Tickets Ticket) :=
  Refinement.Bisimulation left right
    (Observation.Process.TranscriptRel.byTicket ticketLeft ticketRight)
    (Observation.Process.TranscriptRel.byTicket
      (left := right.toProcess) (right := left.toProcess) ticketRight ticketLeft)

/-- Observational equivalence for one fixed party preserves that party's packed
local observations at every executed step. -/
abbrev Observation {Party : Type u} [DecidableEq Party]
    (me : Party)
    (left right : Process.System Party) :=
  Refinement.Bisimulation left right
    (Observation.Process.TranscriptRel.byObservation me)
    (Observation.Process.TranscriptRel.byObservation
      (left := right.toProcess) (right := left.toProcess) me)

namespace Controller

/-- Along the forward direction of a controller equivalence, the current
controller sequence of every finite run prefix is preserved. -/
theorem currentControllersUpTo_eq {Party : Type u}
    {left right : Process.System Party}
    (equiv : Controller left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    run.currentControllersUpTo n =
      (equiv.forth.mapRun run hrel).currentControllersUpTo n :=
  equiv.forth.currentControllersUpTo_mapRun run hrel n

end Controller

namespace ControllerPath

/-- Along the forward direction of a controller-path equivalence, the full
controller-path sequence of every finite run prefix is preserved. -/
theorem controllerPathsUpTo_eq {Party : Type u}
    {left right : Process.System Party}
    (equiv : ControllerPath left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    run.controllerPathsUpTo n =
      (equiv.forth.mapRun run hrel).controllerPathsUpTo n :=
  equiv.forth.controllerPathsUpTo_mapRun run hrel n

end ControllerPath

namespace Trace

/-- Along the forward direction of a trace equivalence, the stable event trace
of every finite run prefix is preserved. -/
theorem eventsUpTo_eq {Party : Type u} {Event : Type w}
    {left right : Process.System Party}
    {eventLeft : left.toProcess.EventMap Event}
    {eventRight : right.toProcess.EventMap Event}
    (equiv : Trace left right eventLeft eventRight)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    run.eventsUpTo eventLeft n =
      (equiv.forth.mapRun run hrel).eventsUpTo eventRight n :=
  equiv.forth.eventsUpTo_mapRun run hrel n

end Trace

namespace Ticket

/-- Along the forward direction of a ticket equivalence, the stable ticket
sequence of every finite run prefix is preserved. -/
theorem ticketsUpTo_eq {Party : Type u} {TicketTy : Type w}
    {left right : Process.System Party}
    {ticketLeft : left.toProcess.Tickets TicketTy}
    {ticketRight : right.toProcess.Tickets TicketTy}
    (equiv : Ticket left right ticketLeft ticketRight)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    run.ticketsUpTo ticketLeft n =
      (equiv.forth.mapRun run hrel).ticketsUpTo ticketRight n :=
  equiv.forth.ticketsUpTo_mapRun run hrel n

end Ticket

namespace Observation

/-- Along the forward direction of an observational equivalence, the packed
local observations of the chosen party are preserved on every finite run
prefix. -/
theorem observationsUpTo_eq {Party : Type u} [DecidableEq Party]
    (me : Party)
    {left right : Process.System Party}
    (equiv : Observation me left right)
    (run : Process.Run left.toProcess)
    {pRight : right.Proc}
    (hrel : equiv.forth.stateRel run.initial pRight) (n : Nat) :
    Observation.Process.Run.observationsUpTo me run n =
      Observation.Process.Run.observationsUpTo me (equiv.forth.mapRun run hrel) n :=
  equiv.forth.observationsUpTo_mapRun me run hrel n

end Observation

end Equivalence
end Concurrent
end Interaction
