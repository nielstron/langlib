module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Relation
import Mathlib.Tactic

@[expose]
public section

/-!
# Locally reversible graph-walking memory

This module isolates the part of the graph-walking-automaton model that is
relevant to a bounded tape.  A memory configuration has a finite observable
label and a finite family of partial moves.  Every move has a named opposite
which undoes it.  A deterministic finite control may inspect only its current
state and the current label before choosing its next state and one move.

The definitions do not assume that the vertex type is finite.  Finiteness is
needed only by traversal theorems for a particular bounded input graph.
-/

namespace GraphWalking

open Relation

universe uLabel uDirection uVertex uState

/-- A graph presented by locally observable, partially defined, invertible
memory operations.

`move_reverse` is the labelled-undirected-edge law: traversing direction `d`
from `source` to `target` is equivalent to traversing the opposite direction
from `target` back to `source`. -/
public structure MemoryGraph
    (Label : Type uLabel) (Direction : Type uDirection)
    (Vertex : Type uVertex) where
  observe : Vertex → Label
  opposite : Direction → Direction
  opposite_involutive : Function.Involutive opposite
  move : Direction → Vertex → Option Vertex
  move_reverse : ∀ direction source target,
    move direction source = some target ↔
      move (opposite direction) target = some source

namespace MemoryGraph

variable {Label : Type uLabel} {Direction : Type uDirection}
  {Vertex : Type uVertex} (graph : MemoryGraph Label Direction Vertex)

@[simp]
public theorem opposite_opposite (direction : Direction) :
    graph.opposite (graph.opposite direction) = direction :=
  graph.opposite_involutive direction

/-- A named memory move has at most one source for a fixed target.  This is a
consequence of the executable reverse move, rather than an extra global
injectivity promise. -/
public theorem move_leftUnique (direction : Direction) :
    Relator.LeftUnique (fun source target => graph.move direction source = some target) := by
  intro left right target hleft hright
  have hbackLeft : graph.move (graph.opposite direction) target = some left :=
    (graph.move_reverse direction left target).mp hleft
  have hbackRight : graph.move (graph.opposite direction) target = some right :=
    (graph.move_reverse direction right target).mp hright
  exact Option.some.inj (hbackLeft.symm.trans hbackRight)

/-- Reversing an opposite move gives the original move. -/
public theorem move_opposite_iff (direction : Direction) (source target : Vertex) :
    graph.move (graph.opposite direction) target = some source ↔
      graph.move direction source = some target := by
  simpa using (graph.move_reverse direction source target).symm

end MemoryGraph

/-- A deterministic finite-state controller for a locally presented memory
graph.  Acceptance is tested only when the transition is undefined; this is
recorded separately by `TerminalAcceptance`. -/
public structure Machine
    (Label : Type uLabel) (Direction : Type uDirection)
    (State : Type uState) where
  transition : State → Label → Option (State × Direction)
  accept : State → Label → Prop

/-- A controller state paired with the current memory vertex. -/
public abbrev Configuration (State : Type uState) (Vertex : Type uVertex) :=
  State × Vertex

namespace Machine

variable {Label : Type uLabel} {Direction : Type uDirection}
  {Vertex : Type uVertex} {State : Type uState}
  (machine : Machine Label Direction State)
  (graph : MemoryGraph Label Direction Vertex)

/-- The unique next configuration, if both the finite-control instruction and
the selected partial memory move are defined. -/
@[expose]
public def next (source : Configuration State Vertex) :
    Option (Configuration State Vertex) :=
  match machine.transition source.1 (graph.observe source.2) with
  | none => none
  | some (targetState, direction) =>
      (graph.move direction source.2).map fun targetVertex =>
        (targetState, targetVertex)

/-- The directed configuration relation of a deterministic graph walk. -/
@[expose]
public def Step (source target : Configuration State Vertex) : Prop :=
  machine.next graph source = some target

/-- Deterministic graph walking gives a functional configuration relation. -/
public theorem step_rightUnique : Relator.RightUnique (machine.Step graph) := by
  intro source left right hleft hright
  exact Option.some.inj (hleft.symm.trans hright)

/-- Acceptance at a configuration depends only on finite control and the
locally observed node label. -/
@[expose]
public def Accepting (configuration : Configuration State Vertex) : Prop :=
  machine.accept configuration.1 (graph.observe configuration.2)

/-- The usual graph-walking convention that accepting configurations have no
outgoing controller instruction. -/
@[expose]
public def TerminalAcceptance : Prop :=
  ∀ state label, machine.accept state label →
    machine.transition state label = none

/-- Under `TerminalAcceptance`, every accepting configuration is a terminal
vertex of the configuration graph. -/
public theorem no_step_of_accepting
    (hterminal : machine.TerminalAcceptance)
    {configuration : Configuration State Vertex}
    (haccept : machine.Accepting graph configuration) :
    ∀ target, ¬ machine.Step graph configuration target := by
  intro target hstep
  simp [Step, Machine.next, hterminal _ _ haccept] at hstep

/-- Direction determinacy: the destination control state remembers the
physical direction used to enter it.  This is the local information needed to
identify the predecessor memory vertex while backtracking. -/
public structure ArrivalDiscipline where
  incoming : State → Direction
  transition_incoming : ∀ {source label target direction},
    machine.transition source label = some (target, direction) →
      incoming target = direction

end Machine

/-! ## The standard direction-determinate state lift -/

/-- Remember the most recently used direction in finite control. -/
public abbrev DirectionLiftState
    (State : Type uState) (Direction : Type uDirection) := State × Direction

/-- The standard direction-determinate expansion of a deterministic walker.
The remembered direction is not consulted; it is overwritten by every move. -/
@[expose]
public def Machine.directionLift
    {Label : Type uLabel} {Direction : Type uDirection}
    {State : Type uState} (machine : Machine Label Direction State) :
    Machine Label Direction (DirectionLiftState State Direction) where
  transition state label :=
    (machine.transition state.1 label).map fun output =>
      ((output.1, output.2), output.2)
  accept state label := machine.accept state.1 label

/-- The direction lift is direction-determinate, with the remembered second
component as the incoming direction. -/
public def Machine.directionLiftArrival
    {Label : Type uLabel} {Direction : Type uDirection}
    {State : Type uState} (machine : Machine Label Direction State) :
    machine.directionLift.ArrivalDiscipline where
  incoming := Prod.snd
  transition_incoming := by
    intro source label target direction htransition
    simp only [Machine.directionLift, Option.map_eq_some_iff] at htransition
    obtain ⟨output, _, houtput⟩ := htransition
    cases houtput
    rfl

/-- Forget the incoming-direction register from a lifted configuration. -/
@[expose]
public def forgetDirection
    {State : Type uState} {Direction : Type uDirection}
    {Vertex : Type uVertex} :
    Configuration (DirectionLiftState State Direction) Vertex →
      Configuration State Vertex :=
  fun configuration => (configuration.1.1, configuration.2)

/-- Every lifted step projects to exactly one source-machine step. -/
public theorem Machine.step_forgetDirection
    {Label : Type uLabel} {Direction : Type uDirection}
    {Vertex : Type uVertex} {State : Type uState}
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    {source target : Configuration (DirectionLiftState State Direction) Vertex}
    (hstep : machine.directionLift.Step graph source target) :
    machine.Step graph (forgetDirection source) (forgetDirection target) := by
  rcases source with ⟨⟨sourceState, remembered⟩, sourceVertex⟩
  rcases target with ⟨⟨targetState, arrived⟩, targetVertex⟩
  cases htransition : machine.transition sourceState (graph.observe sourceVertex) with
  | none =>
      simp [Machine.Step, Machine.next, Machine.directionLift,
        htransition] at hstep
  | some output =>
      rcases output with ⟨outputState, direction⟩
      cases hmove : graph.move direction sourceVertex with
      | none =>
          simp [Machine.Step, Machine.next, Machine.directionLift,
            htransition, hmove] at hstep
      | some outputVertex =>
          simp [Machine.Step, Machine.next, Machine.directionLift,
            htransition, hmove] at hstep
          rcases hstep with ⟨⟨rfl, rfl⟩, rfl⟩
          simp [Machine.Step, Machine.next, forgetDirection, htransition, hmove]

/-- Every source step lifts from any remembered incoming direction. -/
public theorem Machine.exists_directionLift_step
    {Label : Type uLabel} {Direction : Type uDirection}
    {Vertex : Type uVertex} {State : Type uState}
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    {source target : Configuration State Vertex}
    (remembered : Direction)
    (hstep : machine.Step graph source target) :
    ∃ arrived : Direction,
      machine.directionLift.Step graph
        ((source.1, remembered), source.2)
        ((target.1, arrived), target.2) := by
  rcases source with ⟨sourceState, sourceVertex⟩
  rcases target with ⟨targetState, targetVertex⟩
  cases htransition : machine.transition sourceState (graph.observe sourceVertex) with
  | none =>
      simp [Machine.Step, Machine.next, htransition] at hstep
  | some output =>
      rcases output with ⟨outputState, direction⟩
      cases hmove : graph.move direction sourceVertex with
      | none =>
          simp [Machine.Step, Machine.next, htransition, hmove] at hstep
      | some outputVertex =>
          simp [Machine.Step, Machine.next, htransition, hmove] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          refine ⟨direction, ?_⟩
          simp [Machine.Step, Machine.next, Machine.directionLift,
            htransition, hmove]

/-- Projecting a lifted run gives a source-machine run. -/
public theorem Machine.reaches_forgetDirection
    {Label : Type uLabel} {Direction : Type uDirection}
    {Vertex : Type uVertex} {State : Type uState}
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    {source target : Configuration (DirectionLiftState State Direction) Vertex}
    (hreach : ReflTransGen (machine.directionLift.Step graph) source target) :
    ReflTransGen (machine.Step graph)
      (forgetDirection source) (forgetDirection target) := by
  exact hreach.lift forgetDirection
    (fun _ _ hstep => machine.step_forgetDirection graph hstep)

/-- Every source-machine run can be lifted from an arbitrary remembered
direction.  The final remembered direction is existential because it is the
direction of the last nonempty source step. -/
public theorem Machine.exists_directionLift_reaches
    {Label : Type uLabel} {Direction : Type uDirection}
    {Vertex : Type uVertex} {State : Type uState}
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    {source target : Configuration State Vertex}
    (remembered : Direction)
    (hreach : ReflTransGen (machine.Step graph) source target) :
    ∃ finish : Configuration (DirectionLiftState State Direction) Vertex,
      ReflTransGen (machine.directionLift.Step graph)
        ((source.1, remembered), source.2) finish ∧
      forgetDirection finish = target := by
  induction hreach with
  | refl =>
      exact ⟨((source.1, remembered), source.2), .refl, rfl⟩
  | @tail middle target _ hstep ih =>
      obtain ⟨liftedMiddle, hmiddle, hforgetMiddle⟩ := ih
      obtain ⟨arrived, hliftedStep⟩ :=
        machine.exists_directionLift_step graph liftedMiddle.1.2
          (hforgetMiddle ▸ hstep)
      let liftedTarget : Configuration (DirectionLiftState State Direction) Vertex :=
        ((target.1, arrived), target.2)
      refine ⟨liftedTarget, hmiddle.tail ?_, rfl⟩
      simpa [liftedTarget, forgetDirection] using hliftedStep

/-- Exact reachability equivalence for the direction lift. -/
public theorem Machine.exists_directionLift_reaches_iff
    {Label : Type uLabel} {Direction : Type uDirection}
    {Vertex : Type uVertex} {State : Type uState}
    (machine : Machine Label Direction State)
    (graph : MemoryGraph Label Direction Vertex)
    {source target : Configuration State Vertex}
    (remembered : Direction) :
    (∃ finish : Configuration (DirectionLiftState State Direction) Vertex,
      ReflTransGen (machine.directionLift.Step graph)
        ((source.1, remembered), source.2) finish ∧
      forgetDirection finish = target) ↔
      ReflTransGen (machine.Step graph) source target := by
  constructor
  · rintro ⟨finish, hreach, hfinish⟩
    simpa [hfinish] using machine.reaches_forgetDirection graph hreach
  · exact machine.exists_directionLift_reaches graph remembered

end GraphWalking

end
