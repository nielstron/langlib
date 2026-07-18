module

public import Langlib.Automata.LinearBounded.GraphWalking.BoundedTapeController
public import Langlib.Automata.LinearBounded.GraphWalking.LocalPort
public import Langlib.Automata.LinearBounded.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Marked raw-LBA refinement of a local Euler port

This module contains only the finite alphabets, control states, and transition
table of the raw compiler.  Its proof modules are intentionally separate.

This construction keeps an immutable boundary component observable before a
physical head move.  Pre-move blocked-direction dispatch is essential here:
discovering an unavailable partial move only after invoking a clamped raw move
would create a two-predecessor landing which would have to be both terminal
(for the matching decomposition) and continuing (to implement a fixed port).

An incoming directional port is implemented asymmetrically.  It tags the
logical target, probes the candidate predecessor, and then either

* finishes at the predecessor in its outgoing port, or
* restores the failed candidate and returns to the original incoming port.

Every moving rule writes a constructor disjoint from the constructor accepted
by its landing state.  Parameters dropped from a landing state are retained
injectively in the written tag.  These are the two raw invariants used by the
later indegree-two and terminal-clamp proofs.
-/

namespace GraphWalking

open FunctionalGraphReversibleTraversal

universe uTerminal uWork uState

namespace MarkedEulerProbe

noncomputable section

local instance (priority := low) markedEulerProbeDefinitionPropDecidable
    (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev LogicalAlphabet (T : Type uTerminal) (Gamma : Type uWork) :=
  LBA.EndAlpha T Gamma

/-! ## Exact plain-cell codes and immutable boundary information -/

/-- Physical endpoint information retained by every packed cell.  `both` is
needed for width-zero raw tapes, even though a canonical endmarker input always
has at least two cells. -/
public inductive Boundary where
  | left
  | middle
  | right
  | both
  deriving DecidableEq, Repr, Fintype

/-- Whether a boundary code permits a genuine one-cell motion. -/
@[expose]
public def Boundary.allows : Boundary -> BoundedTapeMemory.Travel -> Bool
  | .left, .left => false
  | .left, .right => true
  | .middle, _ => true
  | .right, .left => true
  | .right, .right => false
  | .both, _ => false

/-- Exact representations of ordinary data cells.

The four raw constructors remember how a canonical endmarker/input symbol was
represented.  Consequently tagging and restoring a cell is injective even
when a raw symbol and a packed symbol have the same logical meaning. -/
public inductive PlainCode (T : Type uTerminal) (Gamma : Type uWork) where
  | blank
  | input (terminal : T)
  | leftMarker
  | rightMarker
  | packed (boundary : Boundary) (symbol : LogicalAlphabet T Gamma)
  deriving DecidableEq, Repr, Fintype

namespace PlainCode

/-- The immutable physical-boundary view of a plain code. -/
@[expose]
public def boundary : PlainCode T Gamma -> Boundary
  | .blank => .middle
  | .input _ => .middle
  | .leftMarker => .left
  | .rightMarker => .right
  | .packed boundary _ => boundary

/-- The logical source-machine symbol represented by a plain code. -/
@[expose]
public def logical : PlainCode T Gamma -> LogicalAlphabet T Gamma
  | .blank => Sum.inl none
  | .input terminal => Sum.inl (some (Sum.inl terminal))
  | .leftMarker => LBA.leftMark
  | .rightMarker => LBA.rightMark
  | .packed _ symbol => symbol

/-- Replace a possibly clamping direction by `stay` exactly when the immutable
boundary code says that the requested neighbour is absent. -/
@[expose]
public def normalizeDirection (code : PlainCode T Gamma) : DLBA.Dir -> DLBA.Dir
  | .stay => .stay
  | .left => if code.boundary.allows .left then .left else .stay
  | .right => if code.boundary.allows .right then .right else .stay

end PlainCode

/-! ## The marked deterministic controller and its direction lift -/

/-- Lift a deterministic endmarker transition table to exact plain codes.  A
logical write is canonicalized to `packed`, preserves the immutable boundary,
and an outward clamped instruction becomes a stationary instruction. -/
@[expose]
public def markedMachine
    (source : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    DLBA.Machine (PlainCode T Gamma) Q where
  transition state code :=
    (source.transition state code.logical).map fun output =>
      (output.1,
        .packed code.boundary output.2.1,
        code.normalizeDirection output.2.2)
  accept := source.accept
  initial := source.initial

/-- Finite control of the direction-determinate graph walker. -/
public abbrev LiftState (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) :=
  DirectionLiftState Q (BoundedTapeMemory.Direction (PlainCode T Gamma))

/-- The marked deterministic controller viewed as a direction-determinate
walker over the locally reversible bounded-tape memory operations. -/
@[expose]
public def walker
    (source : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    Machine (PlainCode T Gamma)
      (BoundedTapeMemory.Direction (PlainCode T Gamma))
      (LiftState T Gamma Q) :=
  (BoundedTapeController.machine (markedMachine source)).directionLift

/-! ## Saved local computation edges -/

/-- Constant-size finite data naming one candidate directed walker edge. -/
public structure Edge (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) where
  source : LiftState T Gamma Q
  target : LiftState T Gamma Q
  direction : BoundedTapeMemory.Direction (PlainCode T Gamma)
  deriving DecidableEq, Repr, Fintype

namespace Edge

/-- Symbol observed at the represented source configuration. -/
@[expose]
public def old (edge : Edge T Gamma Q) : PlainCode T Gamma :=
  match edge.direction with
  | .stationary old _ => old
  | .departure old _ _ => old
  | .arrival old _ _ => old

/-- Symbol left at the departure cell by the represented operation. -/
@[expose]
public def written (edge : Edge T Gamma Q) : PlainCode T Gamma :=
  match edge.direction with
  | .stationary _ written => written
  | .departure _ written _ => written
  | .arrival _ written _ => written

/-- The saved edge really is selected by the marked direction-lifted
controller at its named source. -/
@[expose]
public def Enabled
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) : Prop :=
  (walker machine).transition edge.source edge.old =
    some (edge.target, edge.direction)

/-- The edge named by an incoming port.  Direction determinacy stores the
candidate operation in the target state's second component. -/
@[expose]
public def ofIncoming
    (target source : LiftState T Gamma Q) : Edge T Gamma Q where
  source := source
  target := target
  direction := target.2

end Edge

/-! ## Raw alphabet -/

/-- Work constructors of the final canonical endmarker alphabet.  `packed` is
ordinary data; every other constructor is a private protocol tag. -/
public inductive WorkSymbol (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) where
  | packed (boundary : Boundary) (symbol : LogicalAlphabet T Gamma)
  | outgoingDeparture (edge : Edge T Gamma Q)
  | outgoingNeighbour (edge : Edge T Gamma Q) (saved : PlainCode T Gamma)
  | incomingTarget (edge : Edge T Gamma Q) (saved : PlainCode T Gamma)
  | incomingSource (edge : Edge T Gamma Q)
  | incomingInvalidSource (edge : Edge T Gamma Q) (saved : PlainCode T Gamma)
  | stationaryOutgoing (edge : Edge T Gamma Q)
  | stationaryIncoming (edge : Edge T Gamma Q)
  deriving DecidableEq, Repr, Fintype

/-- The raw compiler remains in the repository's canonical endmarker
presentation. -/
public abbrev Alphabet (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) := LBA.EndAlpha T (WorkSymbol T Gamma Q)

/-- Inject an exact plain-cell code into the raw alphabet. -/
@[expose]
public def encodePlain : PlainCode T Gamma -> Alphabet T Gamma Q
  | .blank => Sum.inl none
  | .input terminal => Sum.inl (some (Sum.inl terminal))
  | .leftMarker => Sum.inr false
  | .rightMarker => Sum.inr true
  | .packed boundary symbol =>
      Sum.inl (some (Sum.inr (.packed boundary symbol)))

/-- Inject a private work constructor. -/
@[expose]
public def encodeWork (work : WorkSymbol T Gamma Q) : Alphabet T Gamma Q :=
  Sum.inl (some (Sum.inr work))

/-- Decode exactly the ordinary-data subset of the raw alphabet. -/
@[expose]
public def decodePlain : Alphabet T Gamma Q -> Option (PlainCode T Gamma)
  | Sum.inl none => some .blank
  | Sum.inl (some (Sum.inl terminal)) => some (.input terminal)
  | Sum.inr false => some .leftMarker
  | Sum.inr true => some .rightMarker
  | Sum.inl (some (Sum.inr (.packed boundary symbol))) =>
      some (.packed boundary symbol)
  | Sum.inl (some (Sum.inr _)) => none

/-- Decode the work summand, including both packed data and protocol tags. -/
@[expose]
public def decodeWork : Alphabet T Gamma Q -> Option (WorkSymbol T Gamma Q)
  | Sum.inl (some (Sum.inr work)) => some work
  | _ => none

/-! ## Raw finite control -/

public abbrev Slot (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) := LocalPort.Slot (LiftState T Gamma Q)

/-- Protocol control without the explicit alternating phase bit. -/
public inductive CoreState (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) where
  | canonical (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
  | dispatch (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
  | outgoingAtNeighbour (edge : Edge T Gamma Q)
  | outgoingAtDeparture (edge : Edge T Gamma Q)
  | outgoingRestoreNeighbour (edge : Edge T Gamma Q)
  | outgoingValidateAtDeparture (edge : Edge T Gamma Q)
  | incomingInspect (edge : Edge T Gamma Q)
  | incomingValidAtTarget (edge : Edge T Gamma Q)
  | incomingValidFinish (edge : Edge T Gamma Q)
  | incomingInvalidAtTarget (edge : Edge T Gamma Q)
      (candidate : PlainCode T Gamma)
  | incomingInvalidAtSource (edge : Edge T Gamma Q)
      (candidate : PlainCode T Gamma)
  | incomingReturnAtTarget (edge : Edge T Gamma Q)
  | stationaryOutgoingPending (edge : Edge T Gamma Q)
  | stationaryIncomingPending (edge : Edge T Gamma Q)
  deriving DecidableEq, Fintype

/-- Every raw edge toggles this bit.  Keeping it explicit makes parity
independent of the four-, five-, and two-step protocol lengths. -/
public structure State (T : Type uTerminal) (Gamma : Type uWork)
    (Q : Type uState) where
  phase : Bool
  core : CoreState T Gamma Q
  deriving DecidableEq, Fintype

/-- Toggle phase while entering a new core state. -/
@[expose]
public def nextState (phase : Bool) (core : CoreState T Gamma Q) :
    State T Gamma Q :=
  ⟨!phase, core⟩

/-- The local finite slot rotation.  It enumerates only the fixed finite state
and slot types, never tape configurations. -/
noncomputable def rotateSlot [Fintype (LiftState T Gamma Q)]
    (slot : Slot T Gamma Q) : Slot T Gamma Q :=
  cyclicPerm (Slot T Gamma Q) slot

/-! ## The complete raw transition table -/

def oneOutput (phase : Bool) (core : CoreState T Gamma Q)
    (symbol : Alphabet T Gamma Q) (direction : DLBA.Dir) :
    Set (State T Gamma Q × Alphabet T Gamma Q × DLBA.Dir) :=
  {(nextState phase core, symbol, direction)}

/-- Raw transition table refining `swap o rotate`.

Only ordinary data are accepted by canonical/dispatch states.  Every protocol
state accepts one exact private tag family.  A fabricated tag or a clamped
landing therefore has no successor unless it matches the complete saved edge
and branch data. -/
@[expose]
public noncomputable def transition
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    State T Gamma Q -> Alphabet T Gamma Q ->
      Set (State T Gamma Q × Alphabet T Gamma Q × DLBA.Dir)
  | ⟨phase, .canonical endpoint slot⟩, symbol =>
      match decodePlain symbol with
      | none => ∅
      | some code =>
          oneOutput phase (.dispatch endpoint (rotateSlot slot))
            (encodePlain code) .stay

  | ⟨phase, .dispatch endpoint .anchor⟩, symbol =>
      match decodePlain symbol with
      | none => ∅
      | some code =>
          oneOutput phase (.canonical endpoint .anchor) (encodePlain code) .stay

  | ⟨phase, .dispatch endpoint .outgoing⟩, symbol =>
      match decodePlain symbol with
      | none => ∅
      | some code =>
          match (walker machine).transition endpoint code with
          | none =>
              oneOutput phase (.canonical endpoint .outgoing)
                (encodePlain code) .stay
          | some (target, direction) =>
              let edge : Edge T Gamma Q :=
                { source := endpoint, target := target, direction := direction }
              match direction with
              | .stationary _ _ =>
                  oneOutput phase (.stationaryOutgoingPending edge)
                    (encodeWork (.stationaryOutgoing edge)) .stay
              | .departure _ _ travel =>
                  if code.boundary.allows travel then
                    oneOutput phase (.outgoingAtNeighbour edge)
                      (encodeWork (.outgoingDeparture edge)) travel.toDir
                  else
                    oneOutput phase (.canonical endpoint .outgoing)
                      (encodePlain code) .stay
              | .arrival _ _ _ =>
                  oneOutput phase (.canonical endpoint .outgoing)
                    (encodePlain code) .stay

  | ⟨phase, .dispatch endpoint (.incoming source)⟩, symbol =>
      match decodePlain symbol with
      | none => ∅
      | some code =>
          let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
          match edge.direction with
          | .stationary _ written =>
              if code = written ∧ edge.Enabled machine then
                oneOutput phase (.stationaryIncomingPending edge)
                  (encodeWork (.stationaryIncoming edge)) .stay
              else
                oneOutput phase (.canonical endpoint (.incoming source))
                  (encodePlain code) .stay
          | .departure _ _ travel =>
              if code.boundary.allows travel.reverse then
                oneOutput phase (.incomingInspect edge)
                  (encodeWork (.incomingTarget edge code)) travel.reverse.toDir
              else
                oneOutput phase (.canonical endpoint (.incoming source))
                  (encodePlain code) .stay
          | .arrival _ _ _ =>
              oneOutput phase (.canonical endpoint (.incoming source))
                (encodePlain code) .stay

  | ⟨phase, .outgoingAtNeighbour edge⟩, symbol =>
      match edge.direction, decodePlain symbol with
      | .departure _ _ travel, some neighbour =>
          if neighbour.boundary.allows travel.reverse then
            oneOutput phase (.outgoingAtDeparture edge)
              (encodeWork (.outgoingNeighbour edge neighbour)) travel.reverse.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .outgoingAtDeparture edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure _ written travel, some (.outgoingDeparture observed) =>
          if observed = edge ∧ edge.Enabled machine then
            oneOutput phase (.outgoingRestoreNeighbour edge)
              (encodePlain written) travel.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .outgoingRestoreNeighbour edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure _ _ travel,
          some (.outgoingNeighbour observed neighbour) =>
          if observed = edge ∧ edge.Enabled machine ∧
              neighbour.boundary.allows travel.reverse = true then
            oneOutput phase (.outgoingValidateAtDeparture edge)
              (encodeWork (.incomingTarget edge neighbour)) travel.reverse.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .outgoingValidateAtDeparture edge⟩, symbol =>
      match edge.direction, decodePlain symbol with
      | .departure _ written travel, some candidate =>
          if candidate = written ∧ edge.Enabled machine ∧
              candidate.boundary.allows travel = true then
            oneOutput phase (.incomingReturnAtTarget edge)
              (encodePlain candidate) travel.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .incomingInspect edge⟩, symbol =>
      match edge.direction, decodePlain symbol with
      | .departure _ written travel, some candidate =>
          if candidate = written ∧ edge.Enabled machine ∧
              candidate.boundary.allows travel = true then
            oneOutput phase (.incomingValidAtTarget edge)
              (encodeWork (.incomingSource edge)) travel.toDir
          else
            oneOutput phase (.incomingInvalidAtTarget edge candidate)
              (encodeWork (.incomingInvalidSource edge candidate)) travel.toDir
      | _, _ => ∅

  | ⟨phase, .incomingValidAtTarget edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure _ _ travel, some (.incomingTarget observed neighbour) =>
          if observed = edge ∧ edge.Enabled machine then
            oneOutput phase (.incomingValidFinish edge)
              (encodePlain neighbour) travel.reverse.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .incomingValidFinish edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure old _ travel, some (.incomingSource observed) =>
          if observed = edge ∧ edge.Enabled machine ∧
              old.boundary.allows travel = true then
            oneOutput phase (.canonical edge.source .outgoing)
              (encodePlain edge.old) .stay
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .incomingInvalidAtTarget edge candidate⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure _ _ travel, some (.incomingTarget observed neighbour) =>
          if observed = edge then
            oneOutput phase (.incomingInvalidAtSource edge candidate)
              (encodeWork (.incomingTarget edge neighbour)) travel.reverse.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .incomingInvalidAtSource edge candidate⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure _ _ travel,
          some (.incomingInvalidSource observed saved) =>
          if observed = edge ∧ saved = candidate ∧
              edge = Edge.ofIncoming edge.target edge.source ∧
              ¬(candidate = edge.written ∧ edge.Enabled machine ∧
                candidate.boundary.allows travel = true) then
            oneOutput phase (.incomingReturnAtTarget edge)
              (encodePlain candidate) travel.toDir
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .incomingReturnAtTarget edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .departure _ _ travel,
          some (.incomingTarget observed neighbour) =>
          if observed = edge ∧
              edge = Edge.ofIncoming edge.target edge.source ∧
              neighbour.boundary.allows travel.reverse = true then
            oneOutput phase
              (.canonical edge.target (.incoming edge.source))
              (encodePlain neighbour) .stay
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .stationaryOutgoingPending edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .stationary _ written, some (.stationaryOutgoing observed) =>
          if observed = edge ∧ edge.Enabled machine then
            oneOutput phase
              (.canonical edge.target (.incoming edge.source))
              (encodePlain written) .stay
          else
            ∅
      | _, _ => ∅

  | ⟨phase, .stationaryIncomingPending edge⟩, symbol =>
      match edge.direction, decodeWork symbol with
      | .stationary old _, some (.stationaryIncoming observed) =>
          if observed = edge ∧ edge.Enabled machine then
            oneOutput phase (.canonical edge.source .outgoing)
              (encodePlain old) .stay
          else
            ∅
      | _, _ => ∅

/-- The raw LBA defined by the table above.  Only canonical port states inherit
source acceptance; every dispatch, protocol, and collision state is rejecting. -/
@[expose]
public noncomputable def rawMachine
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    LBA.Machine (Alphabet T Gamma Q) (State T Gamma Q) where
  transition := transition machine
  accept
    | ⟨_, .canonical endpoint _⟩ => machine.accept endpoint.1
    | _ => false
  initial :=
    { phase := false
      core := .canonical
        (machine.initial,
          .stationary (.leftMarker : PlainCode T Gamma) .leftMarker)
        .anchor }

end

end MarkedEulerProbe

end GraphWalking

end
