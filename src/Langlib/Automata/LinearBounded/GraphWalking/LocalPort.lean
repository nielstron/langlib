module

public import Langlib.Automata.LinearBounded.GraphWalking.Definition
public import Langlib.Automata.LinearBounded.FunctionalGraphReversibleTraversal
import Mathlib.Tactic

@[expose]
public section

/-!
# Local finite-control ports for graph-walking computations

For a direction-determinate graph walker, every configuration is given the
same finite ring of ports:

* one distinguished anchor;
* one potential outgoing edge end;
* one potential incoming edge end for each source control state.

An actual computation edge pairs its source's outgoing port with the incoming
port named by its source state at the target.  A nonexistent candidate port is
a fixed stub.  Rotation uses only the finite `Slot State` type; in particular,
it never invokes `Fintype.equivFin` on the type of memory vertices or on the
type of configurations.

The pairing operation has radius one in the memory graph.  For an incoming
candidate it applies the opposite memory operation, inspects the neighbouring
label, and tests one finite-control transition.  Turning that bounded-radius
operation into individual raw LBA steps is deliberately left to the separate
boundary-safe microcompiler.
-/

namespace GraphWalking

open Classical Relation
open FunctionalGraphReversibleTraversal

universe uLabel uDirection uVertex uState

namespace LocalPort

/-- The uniform finite ring of potential edge ends at one configuration. -/
public inductive Slot (State : Type uState) where
  | anchor
  | outgoing
  | incoming (sourceState : State)
  deriving DecidableEq, Fintype

private instance slotNonempty {State : Type uState} : Nonempty (Slot State) :=
  ⟨.anchor⟩

/-- A local port stores its endpoint and only a finite-control slot. -/
public abbrev Port (State : Type uState) (Vertex : Type uVertex) :=
  Configuration State Vertex × Slot State

/-- The represented source configuration. -/
@[expose]
public def endpoint
    {State : Type uState} {Vertex : Type uVertex} :
    Port State Vertex → Configuration State Vertex :=
  Prod.fst

/-- The distinguished fixed slot at a configuration. -/
@[expose]
public def anchor
    {State : Type uState} {Vertex : Type uVertex}
    (configuration : Configuration State Vertex) : Port State Vertex :=
  (configuration, .anchor)

@[simp]
public theorem endpoint_anchor
    {State : Type uState} {Vertex : Type uVertex}
    (configuration : Configuration State Vertex) :
    endpoint (anchor configuration) = configuration := rfl

variable {Label : Type uLabel} {Direction : Type uDirection}
  {Vertex : Type uVertex} {State : Type uState}
  (machine : Machine Label Direction State)
  (graph : MemoryGraph Label Direction Vertex)
  (arrival : machine.ArrivalDiscipline)

/-- The only possible predecessor vertex of a target configuration for a
fixed source state.  Direction determinacy supplies the direction; the memory
graph supplies its executable inverse. -/
@[expose]
public def predecessorCandidate
    (target : Configuration State Vertex) (sourceState : State) :
    Option (Configuration State Vertex) :=
  (graph.move (graph.opposite (arrival.incoming target.1)) target.2).map
    fun sourceVertex => (sourceState, sourceVertex)

/-- Reversing the arrival direction of an actual source step reconstructs its
source configuration exactly. -/
public theorem predecessorCandidate_eq_some_of_step
    {source target : Configuration State Vertex}
    (hstep : machine.Step graph source target) :
    predecessorCandidate machine graph arrival target source.1 = some source := by
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
          have hincoming : arrival.incoming outputState = direction :=
            arrival.transition_incoming htransition
          simp only [predecessorCandidate, hincoming]
          rw [(graph.move_reverse direction sourceVertex outputVertex).mp hmove]
          rfl

/-- The state component of a predecessor candidate is the supplied candidate
state, independently of whether it is an actual computation predecessor. -/
public theorem fst_eq_of_predecessorCandidate_eq_some
    {target source : Configuration State Vertex} {sourceState : State}
    (hcandidate : predecessorCandidate machine graph arrival target sourceState = some source) :
    source.1 = sourceState := by
  unfold predecessorCandidate at hcandidate
  rcases hmove : graph.move
      (graph.opposite (arrival.incoming target.1)) target.2 with _ | sourceVertex
  · simp [hmove] at hcandidate
  · simp [hmove] at hcandidate
    exact congrArg Prod.fst hcandidate.symm

/-- The actual predecessor represented by an incoming slot, if it exists.

This operation uses exactly one opposite memory move and then compares one
finite-control transition with the expected target state and incoming
direction.  It does not enumerate vertices, edges, or configurations. -/
@[expose]
public def incomingSource [DecidableEq State] [DecidableEq Direction]
    (target : Configuration State Vertex) (sourceState : State) :
    Option (Configuration State Vertex) :=
  match predecessorCandidate machine graph arrival target sourceState with
  | none => none
  | some source =>
      if machine.transition source.1 (graph.observe source.2) =
          some (target.1, arrival.incoming target.1) then
        some source
      else
        none

/-- Every actual computation step is found by the one-move incoming-port
test. -/
public theorem incomingSource_eq_some_of_step
    [DecidableEq State] [DecidableEq Direction]
    {source target : Configuration State Vertex}
    (hstep : machine.Step graph source target) :
    incomingSource machine graph arrival target source.1 = some source := by
  have hcandidate := predecessorCandidate_eq_some_of_step
    machine graph arrival hstep
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
          have hincoming : arrival.incoming outputState = direction :=
            arrival.transition_incoming htransition
          simp [incomingSource, hcandidate, htransition, hincoming]

/-- Conversely, the local incoming-port test is sound for the source
configuration relation. -/
public theorem step_of_incomingSource_eq_some
    [DecidableEq State] [DecidableEq Direction]
    {source target : Configuration State Vertex} {sourceState : State}
    (hincoming : incomingSource machine graph arrival target sourceState = some source) :
    machine.Step graph source target := by
  rcases target with ⟨targetState, targetVertex⟩
  rcases source with ⟨sourceState', sourceVertex⟩
  cases hreverse : graph.move
      (graph.opposite (arrival.incoming targetState)) targetVertex with
  | none =>
      simp [incomingSource, predecessorCandidate, hreverse] at hincoming
  | some candidateVertex =>
      by_cases htransition :
          machine.transition sourceState (graph.observe candidateVertex) =
            some (targetState, arrival.incoming targetState)
      · simp [incomingSource, predecessorCandidate, hreverse, htransition] at hincoming
        rcases hincoming with ⟨rfl, rfl⟩
        have hforward : graph.move (arrival.incoming targetState) candidateVertex =
            some targetVertex :=
          (graph.move_opposite_iff (arrival.incoming targetState)
            candidateVertex targetVertex).mp (by simpa using hreverse)
        simp [Machine.Step, Machine.next, htransition, hforward]
      · simp [incomingSource, predecessorCandidate, hreverse, htransition] at hincoming

/-- The source-state index stored in an incoming slot agrees with the state of
the locally reconstructed source configuration. -/
public theorem fst_eq_of_incomingSource_eq_some
    [DecidableEq State] [DecidableEq Direction]
    {target source : Configuration State Vertex} {sourceState : State}
    (hincoming : incomingSource machine graph arrival target sourceState = some source) :
    source.1 = sourceState := by
  unfold incomingSource at hincoming
  cases hcandidate : predecessorCandidate machine graph arrival target sourceState with
  | none => simp [hcandidate] at hincoming
  | some candidate =>
      by_cases htransition :
          machine.transition candidate.1 (graph.observe candidate.2) =
            some (target.1, arrival.incoming target.1)
      · simp [hcandidate, htransition] at hincoming
        subst source
        exact fst_eq_of_predecessorCandidate_eq_some
          machine graph arrival hcandidate
      · simp [hcandidate, htransition] at hincoming

/-- Pair actual computation-edge ends and fix every nonexistent local port. -/
@[expose]
public def swapFun [DecidableEq State] [DecidableEq Direction] :
    Port State Vertex → Port State Vertex
  | (configuration, .anchor) => (configuration, .anchor)
  | (configuration, .outgoing) =>
      match machine.next graph configuration with
      | none => (configuration, .outgoing)
      | some target => (target, .incoming configuration.1)
  | (configuration, .incoming sourceState) =>
      match incomingSource machine graph arrival configuration sourceState with
      | none => (configuration, .incoming sourceState)
      | some source => (source, .outgoing)

/-- Local edge-end pairing is an involution on all raw ports, including ports
whose candidate source transition is absent. -/
public theorem swapFun_involutive
    [DecidableEq State] [DecidableEq Direction] :
    Function.Involutive (swapFun machine graph arrival) := by
  rintro ⟨configuration, slot⟩
  cases slot with
  | anchor => rfl
  | outgoing =>
      cases hnext : machine.next graph configuration with
      | none => simp [swapFun, hnext]
      | some target =>
          have hincoming := incomingSource_eq_some_of_step
            machine graph arrival hnext
          simp [swapFun, hnext, hincoming]
  | incoming sourceState =>
      cases hincoming : incomingSource machine graph arrival
          configuration sourceState with
      | none => simp [swapFun, hincoming]
      | some source =>
          have hstep := step_of_incomingSource_eq_some
            machine graph arrival hincoming
          have hsourceState : source.1 = sourceState :=
            fst_eq_of_incomingSource_eq_some
              machine graph arrival hincoming
          change machine.next graph source = some configuration at hstep
          simp [swapFun, hincoming, hstep, hsourceState]

/-- The local pairing as a total permutation. -/
@[expose]
public def swap [DecidableEq State] [DecidableEq Direction] :
    Equiv.Perm (Port State Vertex) where
  toFun := swapFun machine graph arrival
  invFun := swapFun machine graph arrival
  left_inv := swapFun_involutive machine graph arrival
  right_inv := swapFun_involutive machine graph arrival

@[simp]
public theorem swap_apply [DecidableEq State] [DecidableEq Direction]
    (port : Port State Vertex) :
    swap machine graph arrival port = swapFun machine graph arrival port := rfl

@[simp]
public theorem swap_involution [DecidableEq State] [DecidableEq Direction]
    (port : Port State Vertex) :
    swap machine graph arrival (swap machine graph arrival port) = port :=
  swapFun_involutive machine graph arrival port

/-! ## Uniform finite-control rotation -/

/-- Rotate only the finite slot register, leaving the represented memory
configuration untouched. -/
noncomputable def rotate [Fintype State] : Equiv.Perm (Port State Vertex) where
  toFun port := (port.1, cyclicPerm (Slot State) port.2)
  invFun port := (port.1, (cyclicPerm (Slot State))⁻¹ port.2)
  left_inv := by
    intro port
    apply Prod.ext
    · rfl
    · exact (cyclicPerm (Slot State)).symm_apply_apply port.2
  right_inv := by
    intro port
    apply Prod.ext
    · rfl
    · exact (cyclicPerm (Slot State)).apply_symm_apply port.2

@[simp]
public theorem endpoint_rotate [Fintype State] (port : Port State Vertex) :
    endpoint (rotate (State := State) (Vertex := Vertex) port) = endpoint port := rfl

/-- The local rotation reaches every slot at a fixed configuration.  Only the
finite state type is enumerated. -/
public theorem rotate_complete [Fintype State]
    (left right : Port State Vertex)
    (hsame : endpoint left = endpoint right) :
    ReflTransGen
      (PermutationReachability.PowerEdge
        (rotate (State := State) (Vertex := Vertex))) left right := by
  rcases left with ⟨leftConfiguration, leftSlot⟩
  rcases right with ⟨rightConfiguration, rightSlot⟩
  simp only [endpoint] at hsame
  subst rightConfiguration
  have hslots := cyclicPerm_reaches_everywhere leftSlot rightSlot
  exact hslots.lift (fun slot => (leftConfiguration, slot)) (by
    intro source target hstep
    change (leftConfiguration, cyclicPerm (Slot State) source) =
      (leftConfiguration, target)
    exact congrArg (fun slot => (leftConfiguration, slot)) hstep)

/-! ## A genuinely local port system -/

/-- Swapping a local port crosses at most one weak computation edge. -/
public theorem swap_sound
    [DecidableEq State] [DecidableEq Direction]
    (port : Port State Vertex) :
    ReflTransGen (WeakStep (machine.Step graph))
      (endpoint port) (endpoint (swap machine graph arrival port)) := by
  rcases port with ⟨configuration, slot⟩
  cases slot with
  | anchor => exact .refl
  | outgoing =>
      cases hnext : machine.next graph configuration with
      | none =>
          simpa [endpoint, swap, swapFun, hnext] using
            (ReflTransGen.refl : ReflTransGen (WeakStep (machine.Step graph))
              configuration configuration)
      | some target =>
          have hweak : WeakStep (machine.Step graph) configuration target :=
            Or.inl hnext
          simpa [endpoint, swap, swapFun, hnext] using
            (ReflTransGen.single hweak)
  | incoming sourceState =>
      cases hincoming : incomingSource machine graph arrival
          configuration sourceState with
      | none =>
          simpa [endpoint, swap, swapFun, hincoming] using
            (ReflTransGen.refl : ReflTransGen (WeakStep (machine.Step graph))
              configuration configuration)
      | some source =>
          have hstep := step_of_incomingSource_eq_some
            machine graph arrival hincoming
          have hweak : WeakStep (machine.Step graph) configuration source :=
            Or.inr hstep
          simpa [endpoint, swap, swapFun, hincoming] using
            (ReflTransGen.single hweak)

/-- Every actual computation edge is paired by its source outgoing slot. -/
public theorem edge_port
    [DecidableEq State] [DecidableEq Direction]
    {source target : Configuration State Vertex}
    (hstep : machine.Step graph source target) :
    ∃ port : Port State Vertex,
      endpoint port = source ∧
      endpoint (swap machine graph arrival port) = target := by
  refine ⟨(source, .outgoing), rfl, ?_⟩
  change machine.next graph source = some target at hstep
  simp [endpoint, swap, swapFun, hstep]

/-- The graph walk's computation relation has a port system whose operations
are uniform in the memory-graph size.  Finiteness of vertices is used only to
satisfy the semantic `PortSystem` interface. -/
noncomputable def ofMachine
    [Fintype State] [DecidableEq State] [DecidableEq Direction]
    [Fintype Vertex] [DecidableEq Vertex] :
    PortSystem (machine.Step graph) where
  Port := Port State Vertex
  portFintype := inferInstance
  portDecidableEq := inferInstance
  endpoint := endpoint
  anchor := anchor
  endpoint_anchor := endpoint_anchor
  rotate := rotate
  rotate_endpoint := endpoint_rotate
  rotate_complete := rotate_complete
  swap := swap machine graph arrival
  swap_involution := swap_involution machine graph arrival
  swap_sound := swap_sound machine graph arrival
  edge_port := edge_port machine graph arrival

/-- The single local Euler step is globally reversible on raw ports. -/
public theorem eulerEdge_biUnique
    [Fintype State] [DecidableEq State] [DecidableEq Direction]
    [Fintype Vertex] [DecidableEq Vertex] :
    Relator.BiUnique (ofMachine machine graph arrival).EulerEdge :=
  (ofMachine machine graph arrival).eulerEdge_biUnique

end LocalPort

end GraphWalking

end
