module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.Definition
public import Langlib.Automata.LinearBounded.Functional
import Mathlib.Tactic

@[expose]
public section

/-!
# Structural facts for the marked Euler probe

This file records the exact interface between ordinary packed cells and the
private protocol tags.  It also proves, directly from the complete raw
transition table, that the compiler is functional at every tape width and
that every raw edge toggles the explicit phase bit.
-/

namespace GraphWalking.MarkedEulerProbe

open LBA

universe uTerminal uWork uState

noncomputable section

local instance (priority := low) markedEulerProbeStructuralPropDecidable
    (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}

/-! ## Exact coding algebra -/

@[simp]
public theorem decodePlain_encodePlain (code : PlainCode T Gamma) :
    decodePlain (encodePlain (Q := Q) code) = some code := by
  cases code <;> rfl

@[simp]
public theorem decodeWork_encodeWork (work : WorkSymbol T Gamma Q) :
    decodeWork (encodeWork work) = some work := by
  rfl

public theorem encodePlain_injective :
    Function.Injective (encodePlain : PlainCode T Gamma → Alphabet T Gamma Q) := by
  intro left right heq
  have := congrArg decodePlain heq
  simpa using this

public theorem encodeWork_injective :
    Function.Injective (encodeWork : WorkSymbol T Gamma Q → Alphabet T Gamma Q) := by
  intro left right heq
  have := congrArg decodeWork heq
  simpa using this

public theorem eq_encodePlain_of_decodePlain_eq_some
    {symbol : Alphabet T Gamma Q} {code : PlainCode T Gamma}
    (hdecode : decodePlain symbol = some code) :
    symbol = encodePlain code := by
  cases symbol with
  | inl option =>
      cases option with
      | none =>
          simp only [decodePlain, Option.some.injEq] at hdecode
          subst code
          rfl
      | some value =>
          cases value with
          | inl terminal =>
              simp only [decodePlain, Option.some.injEq] at hdecode
              subst code
              rfl
          | inr work =>
              cases work <;>
                simp only [decodePlain] at hdecode
              next boundary logical =>
                simp only [Option.some.injEq] at hdecode
                subst code
                rfl
              all_goals contradiction
  | inr marker =>
      cases marker <;>
        simp only [decodePlain, Option.some.injEq] at hdecode <;>
        subst code <;> rfl

public theorem decodePlain_eq_some_iff
    (symbol : Alphabet T Gamma Q) (code : PlainCode T Gamma) :
    decodePlain symbol = some code ↔ symbol = encodePlain code := by
  constructor
  · exact eq_encodePlain_of_decodePlain_eq_some
  · rintro rfl
    simp

public theorem eq_encodeWork_of_decodeWork_eq_some
    {symbol : Alphabet T Gamma Q} {work : WorkSymbol T Gamma Q}
    (hdecode : decodeWork symbol = some work) :
    symbol = encodeWork work := by
  cases symbol with
  | inl option =>
      cases option with
      | none => simp [decodeWork] at hdecode
      | some value =>
          cases value with
          | inl terminal => simp [decodeWork] at hdecode
          | inr observed =>
              simp only [decodeWork, Option.some.injEq] at hdecode
              subst work
              rfl
  | inr marker => simp [decodeWork] at hdecode

public theorem decodeWork_eq_some_iff
    (symbol : Alphabet T Gamma Q) (work : WorkSymbol T Gamma Q) :
    decodeWork symbol = some work ↔ symbol = encodeWork work := by
  constructor
  · exact eq_encodeWork_of_decodeWork_eq_some
  · rintro rfl
    simp

@[simp]
public theorem decodePlain_encodeWork (work : WorkSymbol T Gamma Q) :
    decodePlain (encodeWork work) =
      match work with
      | .packed boundary symbol => some (.packed boundary symbol)
      | _ => none := by
  cases work <;> rfl

@[simp]
public theorem decodeWork_encodePlain (code : PlainCode T Gamma) :
    decodeWork (encodePlain (Q := Q) code) =
      match code with
      | .packed boundary symbol => some (.packed boundary symbol)
      | _ => none := by
  cases code <;> rfl

/-- Ordinary cells and work encodings overlap exactly on the intentionally
shared `packed` constructor.  All other work constructors are private tags. -/
public theorem encodePlain_eq_encodeWork_iff
    (code : PlainCode T Gamma) (work : WorkSymbol T Gamma Q) :
    encodePlain (Q := Q) code = encodeWork work ↔
      ∃ boundary symbol,
        code = .packed boundary symbol ∧ work = .packed boundary symbol := by
  constructor
  · intro heq
    cases code <;> cases work <;> simp_all [encodePlain, encodeWork]
  · rintro ⟨boundary, symbol, rfl, rfl⟩
    rfl

@[simp]
public theorem encodePlain_ne_outgoingDeparture
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q) :
    encodePlain (Q := Q) code ≠ encodeWork (.outgoingDeparture edge) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

@[simp]
public theorem encodePlain_ne_outgoingNeighbour
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q)
    (saved : PlainCode T Gamma) :
    encodePlain (Q := Q) code ≠ encodeWork (.outgoingNeighbour edge saved) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

@[simp]
public theorem encodePlain_ne_incomingTarget
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q)
    (saved : PlainCode T Gamma) :
    encodePlain (Q := Q) code ≠ encodeWork (.incomingTarget edge saved) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

@[simp]
public theorem encodePlain_ne_incomingSource
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q) :
    encodePlain (Q := Q) code ≠ encodeWork (.incomingSource edge) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

@[simp]
public theorem encodePlain_ne_incomingInvalidSource
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q)
    (saved : PlainCode T Gamma) :
    encodePlain (Q := Q) code ≠
      encodeWork (.incomingInvalidSource edge saved) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

@[simp]
public theorem encodePlain_ne_stationaryOutgoing
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q) :
    encodePlain (Q := Q) code ≠ encodeWork (.stationaryOutgoing edge) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

@[simp]
public theorem encodePlain_ne_stationaryIncoming
    (code : PlainCode T Gamma) (edge : Edge T Gamma Q) :
    encodePlain (Q := Q) code ≠ encodeWork (.stationaryIncoming edge) := by
  rw [ne_eq, encodePlain_eq_encodeWork_iff]
  simp

/-! ## Inverting enabled marked-controller edges -/

/-- Full finite-control inversion for an enabled saved edge.  It exposes the
source DLBA instruction before boundary normalization and both copies of the
selected reversible operation introduced by the direction lift. -/
public theorem Edge.enabled_iff_exists_source_transition
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) :
    edge.Enabled machine ↔
      ∃ target written direction,
        machine.transition edge.source.1 edge.old.logical =
            some (target, written, direction) ∧
        edge.target =
          (target, BoundedTapeController.operation edge.old
            (.packed edge.old.boundary written)
            (edge.old.normalizeDirection direction)) ∧
        edge.direction =
          BoundedTapeController.operation edge.old
            (.packed edge.old.boundary written)
            (edge.old.normalizeDirection direction) := by
  simp only [Edge.Enabled, walker, GraphWalking.Machine.directionLift,
    BoundedTapeController.machine, markedMachine,
    Option.map_eq_some_iff]
  aesop

/-- The direction lift stores the selected operation in the target state. -/
public theorem Edge.target_snd_eq_direction_of_enabled
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) (henabled : edge.Enabled machine) :
    edge.target.2 = edge.direction := by
  rcases (edge.enabled_iff_exists_source_transition machine).1 henabled with
    ⟨target, written, direction, htransition, htarget, hdirection⟩
  rw [htarget, hdirection]

/-- A forward marked controller selects only stationary or departure
operations; an arrival name can occur only while graph walking backwards. -/
public theorem Edge.direction_ne_arrival_of_enabled
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) (henabled : edge.Enabled machine)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel) :
    edge.direction ≠ .arrival old written travel := by
  rcases (edge.enabled_iff_exists_source_transition machine).1 henabled with
    ⟨target, new, direction, htransition, htarget, hdirection⟩
  rw [hdirection]
  cases direction <;>
    simp [BoundedTapeController.operation, PlainCode.normalizeDirection] <;>
    split <;> simp

/-- The old-symbol field of a stationary name is exactly `Edge.old`. -/
public theorem Edge.old_eq_of_direction_stationary
    (edge : Edge T Gamma Q) (old written : PlainCode T Gamma)
    (hdirection : edge.direction = .stationary old written) :
    old = edge.old := by
  rw [Edge.old, hdirection]

/-- The old-symbol field of a departure name is exactly `Edge.old`. -/
public theorem Edge.old_eq_of_direction_departure
    (edge : Edge T Gamma Q) (old written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (hdirection : edge.direction = .departure old written travel) :
    old = edge.old := by
  rw [Edge.old, hdirection]

/-- The old-symbol field of an arrival name is exactly `Edge.old`. -/
public theorem Edge.old_eq_of_direction_arrival
    (edge : Edge T Gamma Q) (old written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (hdirection : edge.direction = .arrival old written travel) :
    old = edge.old := by
  rw [Edge.old, hdirection]

/-- Boundary normalization can select an enabled departure only when the
immutable old-cell code permits that genuine travel. -/
public theorem Edge.old_boundary_allows_of_enabled_departure
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) (henabled : edge.Enabled machine)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (hdirection : edge.direction = .departure old written travel) :
    edge.old.boundary.allows travel = true := by
  rcases (edge.enabled_iff_exists_source_transition machine).1 henabled with
    ⟨target, new, direction, htransition, htarget, hedge⟩
  rw [hedge] at hdirection
  cases direction with
  | stay =>
      simp [PlainCode.normalizeDirection, BoundedTapeController.operation]
        at hdirection
  | left =>
      simp only [PlainCode.normalizeDirection] at hdirection
      split at hdirection
      next hallows =>
        simp only [BoundedTapeController.operation,
          BoundedTapeMemory.Direction.departure.injEq] at hdirection
        exact hdirection.2.2 ▸ hallows
      next blocked =>
        simp [BoundedTapeController.operation] at hdirection
  | right =>
      simp only [PlainCode.normalizeDirection] at hdirection
      split at hdirection
      next hallows =>
        simp only [BoundedTapeController.operation,
          BoundedTapeMemory.Direction.departure.injEq] at hdirection
        exact hdirection.2.2 ▸ hallows
      next blocked =>
        simp [BoundedTapeController.operation] at hdirection

/-- The written-symbol field of an enabled departure carries the same
immutable boundary code and therefore also permits the selected travel. -/
public theorem Edge.written_boundary_allows_of_enabled_departure
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) (henabled : edge.Enabled machine)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (hdirection : edge.direction = .departure old written travel) :
    edge.written.boundary.allows travel = true := by
  have holdAllows :=
    edge.old_boundary_allows_of_enabled_departure machine henabled
      old written travel hdirection
  rcases (edge.enabled_iff_exists_source_transition machine).1 henabled with
    ⟨target, new, sourceDirection, htransition, htarget, hedge⟩
  have hoperation : BoundedTapeController.operation edge.old
      (.packed edge.old.boundary new)
      (edge.old.normalizeDirection sourceDirection) =
      .departure old written travel := hedge.symm.trans hdirection
  cases hnormalized : edge.old.normalizeDirection sourceDirection with
  | stay =>
      simp [BoundedTapeController.operation, hnormalized] at hoperation
  | left =>
      simp only [hnormalized, BoundedTapeController.operation] at hoperation
      have hinj := BoundedTapeMemory.Direction.departure.inj hoperation
      rw [← hinj.2.2] at holdAllows
      rw [Edge.written, hdirection]
      rw [← hinj.2.1, ← hinj.2.2]
      change edge.old.boundary.allows .left = true
      exact holdAllows
  | right =>
      simp only [hnormalized, BoundedTapeController.operation] at hoperation
      have hinj := BoundedTapeMemory.Direction.departure.inj hoperation
      rw [← hinj.2.2] at holdAllows
      rw [Edge.written, hdirection]
      rw [← hinj.2.1, ← hinj.2.2]
      change edge.old.boundary.allows .right = true
      exact holdAllows

/-! ## Exhaustive local transition cases -/

/-- Constructor-level classification of every nonempty entry of the raw
transition table.  The indices expose the exact read symbol and exact output;
the constructor premises expose every semantic test performed by the table. -/
public inductive RawTransitionCase
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (phase : Bool) :
    CoreState T Gamma Q → Alphabet T Gamma Q →
      (State T Gamma Q × Alphabet T Gamma Q × DLBA.Dir) → Prop where
  | canonical (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
      (code : PlainCode T Gamma) :
      RawTransitionCase machine phase (.canonical endpoint slot)
        (encodePlain code)
        (nextState phase (.dispatch endpoint (rotateSlot slot)),
          encodePlain code, .stay)
  | dispatchAnchor (endpoint : LiftState T Gamma Q)
      (code : PlainCode T Gamma) :
      RawTransitionCase machine phase (.dispatch endpoint .anchor)
        (encodePlain code)
        (nextState phase (.canonical endpoint .anchor), encodePlain code, .stay)
  | dispatchOutgoingNone (endpoint : LiftState T Gamma Q)
      (code : PlainCode T Gamma)
      (htransition : (walker machine).transition endpoint code = none) :
      RawTransitionCase machine phase (.dispatch endpoint .outgoing)
        (encodePlain code)
        (nextState phase (.canonical endpoint .outgoing), encodePlain code, .stay)
  | dispatchOutgoingStationary (endpoint target : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (htransition : (walker machine).transition endpoint code =
        some (target, .stationary old written)) :
      RawTransitionCase machine phase (.dispatch endpoint .outgoing)
        (encodePlain code)
        (nextState phase (.stationaryOutgoingPending
            { source := endpoint, target := target,
              direction := .stationary old written }),
          encodeWork (.stationaryOutgoing
            { source := endpoint, target := target,
              direction := .stationary old written }), .stay)
  | dispatchOutgoingDeparture (endpoint target : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (htransition : (walker machine).transition endpoint code =
        some (target, .departure old written travel))
      (hallows : code.boundary.allows travel = true) :
      RawTransitionCase machine phase (.dispatch endpoint .outgoing)
        (encodePlain code)
        (nextState phase (.outgoingAtNeighbour
            { source := endpoint, target := target,
              direction := .departure old written travel }),
          encodeWork (.outgoingDeparture
            { source := endpoint, target := target,
              direction := .departure old written travel }), travel.toDir)
  | dispatchOutgoingBlocked (endpoint target : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (htransition : (walker machine).transition endpoint code =
        some (target, .departure old written travel))
      (hblocked : code.boundary.allows travel = false) :
      RawTransitionCase machine phase (.dispatch endpoint .outgoing)
        (encodePlain code)
        (nextState phase (.canonical endpoint .outgoing), encodePlain code, .stay)
  | dispatchOutgoingArrival (endpoint target : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (htransition : (walker machine).transition endpoint code =
        some (target, .arrival old written travel)) :
      RawTransitionCase machine phase (.dispatch endpoint .outgoing)
        (encodePlain code)
        (nextState phase (.canonical endpoint .outgoing), encodePlain code, .stay)
  | dispatchIncomingStationaryValid (endpoint source : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (hdirection : (Edge.ofIncoming endpoint source).direction =
        .stationary old written)
      (hcode : code = written)
      (henabled : (Edge.ofIncoming endpoint source).Enabled machine) :
      RawTransitionCase machine phase (.dispatch endpoint (.incoming source))
        (encodePlain code)
        (nextState phase (.stationaryIncomingPending
            (Edge.ofIncoming endpoint source)),
          encodeWork (.stationaryIncoming (Edge.ofIncoming endpoint source)), .stay)
  | dispatchIncomingStationaryInvalid (endpoint source : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (hdirection : (Edge.ofIncoming endpoint source).direction =
        .stationary old written)
      (hinvalid : ¬ (code = written ∧
        (Edge.ofIncoming endpoint source).Enabled machine)) :
      RawTransitionCase machine phase (.dispatch endpoint (.incoming source))
        (encodePlain code)
        (nextState phase (.canonical endpoint (.incoming source)),
          encodePlain code, .stay)
  | dispatchIncomingDeparture (endpoint source : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : (Edge.ofIncoming endpoint source).direction =
        .departure old written travel)
      (hallows : code.boundary.allows travel.reverse = true) :
      RawTransitionCase machine phase (.dispatch endpoint (.incoming source))
        (encodePlain code)
        (nextState phase (.incomingInspect (Edge.ofIncoming endpoint source)),
          encodeWork (.incomingTarget (Edge.ofIncoming endpoint source) code),
          travel.reverse.toDir)
  | dispatchIncomingBlocked (endpoint source : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : (Edge.ofIncoming endpoint source).direction =
        .departure old written travel)
      (hblocked : code.boundary.allows travel.reverse = false) :
      RawTransitionCase machine phase (.dispatch endpoint (.incoming source))
        (encodePlain code)
        (nextState phase (.canonical endpoint (.incoming source)),
          encodePlain code, .stay)
  | dispatchIncomingArrival (endpoint source : LiftState T Gamma Q)
      (code old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : (Edge.ofIncoming endpoint source).direction =
        .arrival old written travel) :
      RawTransitionCase machine phase (.dispatch endpoint (.incoming source))
        (encodePlain code)
        (nextState phase (.canonical endpoint (.incoming source)),
          encodePlain code, .stay)
  | outgoingAtNeighbour (edge : Edge T Gamma Q)
      (old written neighbour : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (hallows : neighbour.boundary.allows travel.reverse = true) :
      RawTransitionCase machine phase (.outgoingAtNeighbour edge)
        (encodePlain neighbour)
        (nextState phase (.outgoingAtDeparture edge),
          encodeWork (.outgoingNeighbour edge neighbour), travel.reverse.toDir)
  | outgoingAtDeparture (edge : Edge T Gamma Q)
      (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (henabled : edge.Enabled machine) :
      RawTransitionCase machine phase (.outgoingAtDeparture edge)
        (encodeWork (.outgoingDeparture edge))
        (nextState phase (.outgoingRestoreNeighbour edge),
          encodePlain written, travel.toDir)
  | outgoingRestoreNeighbour (edge : Edge T Gamma Q)
      (old written neighbour : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (henabled : edge.Enabled machine)
      (hallows : neighbour.boundary.allows travel.reverse = true) :
      RawTransitionCase machine phase (.outgoingRestoreNeighbour edge)
        (encodeWork (.outgoingNeighbour edge neighbour))
        (nextState phase (.outgoingValidateAtDeparture edge),
          encodeWork (.incomingTarget edge neighbour), travel.reverse.toDir)
  | outgoingValidateAtDeparture (edge : Edge T Gamma Q)
      (old written candidate : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (hvalid : candidate = written ∧ edge.Enabled machine ∧
        candidate.boundary.allows travel = true) :
      RawTransitionCase machine phase (.outgoingValidateAtDeparture edge)
        (encodePlain candidate)
        (nextState phase (.incomingReturnAtTarget edge), encodePlain candidate,
          travel.toDir)
  | incomingInspectValid (edge : Edge T Gamma Q)
      (old written candidate : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (hvalid : candidate = written ∧ edge.Enabled machine ∧
        candidate.boundary.allows travel = true) :
      RawTransitionCase machine phase (.incomingInspect edge)
        (encodePlain candidate)
        (nextState phase (.incomingValidAtTarget edge),
          encodeWork (.incomingSource edge), travel.toDir)
  | incomingInspectInvalid (edge : Edge T Gamma Q)
      (old written candidate : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (hinvalid : ¬ (candidate = written ∧ edge.Enabled machine ∧
        candidate.boundary.allows travel = true)) :
      RawTransitionCase machine phase (.incomingInspect edge)
        (encodePlain candidate)
        (nextState phase (.incomingInvalidAtTarget edge candidate),
          encodeWork (.incomingInvalidSource edge candidate), travel.toDir)
  | incomingValidAtTarget (edge : Edge T Gamma Q)
      (old written neighbour : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (henabled : edge.Enabled machine) :
      RawTransitionCase machine phase (.incomingValidAtTarget edge)
        (encodeWork (.incomingTarget edge neighbour))
        (nextState phase (.incomingValidFinish edge), encodePlain neighbour,
          travel.reverse.toDir)
  | incomingValidFinish (edge : Edge T Gamma Q)
      (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (henabled : edge.Enabled machine)
      (hallows : old.boundary.allows travel = true) :
      RawTransitionCase machine phase (.incomingValidFinish edge)
        (encodeWork (.incomingSource edge))
        (nextState phase (.canonical edge.source .outgoing),
          encodePlain edge.old, .stay)
  | incomingInvalidAtTarget (edge : Edge T Gamma Q)
      (candidate neighbour old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel) :
      RawTransitionCase machine phase (.incomingInvalidAtTarget edge candidate)
        (encodeWork (.incomingTarget edge neighbour))
        (nextState phase (.incomingInvalidAtSource edge candidate),
          encodeWork (.incomingTarget edge neighbour), travel.reverse.toDir)
  | incomingInvalidAtSource (edge : Edge T Gamma Q)
      (candidate old written : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (hwellformed : edge = Edge.ofIncoming edge.target edge.source)
      (hinvalid : ¬ (candidate = edge.written ∧ edge.Enabled machine ∧
        candidate.boundary.allows travel = true)) :
      RawTransitionCase machine phase (.incomingInvalidAtSource edge candidate)
        (encodeWork (.incomingInvalidSource edge candidate))
        (nextState phase (.incomingReturnAtTarget edge), encodePlain candidate,
          travel.toDir)
  | incomingReturnAtTarget (edge : Edge T Gamma Q)
      (old written neighbour : PlainCode T Gamma)
      (travel : BoundedTapeMemory.Travel)
      (hdirection : edge.direction = .departure old written travel)
      (hwellformed : edge = Edge.ofIncoming edge.target edge.source)
      (hallows : neighbour.boundary.allows travel.reverse = true) :
      RawTransitionCase machine phase (.incomingReturnAtTarget edge)
        (encodeWork (.incomingTarget edge neighbour))
        (nextState phase (.canonical edge.target (.incoming edge.source)),
          encodePlain neighbour, .stay)
  | stationaryOutgoingPending (edge : Edge T Gamma Q)
      (old written : PlainCode T Gamma)
      (hdirection : edge.direction = .stationary old written)
      (henabled : edge.Enabled machine) :
      RawTransitionCase machine phase (.stationaryOutgoingPending edge)
        (encodeWork (.stationaryOutgoing edge))
        (nextState phase (.canonical edge.target (.incoming edge.source)),
          encodePlain written, .stay)
  | stationaryIncomingPending (edge : Edge T Gamma Q)
      (old written : PlainCode T Gamma)
      (hdirection : edge.direction = .stationary old written)
      (henabled : edge.Enabled machine) :
      RawTransitionCase machine phase (.stationaryIncomingPending edge)
        (encodeWork (.stationaryIncoming edge))
        (nextState phase (.canonical edge.source .outgoing),
          encodePlain old, .stay)

/-- Exact inversion theorem for all 25 possible raw edge forms. -/
public theorem mem_transition_iff_rawTransitionCase
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (phase : Bool)
    (core : CoreState T Gamma Q) (symbol : Alphabet T Gamma Q)
    (output : State T Gamma Q × Alphabet T Gamma Q × DLBA.Dir) :
    output ∈ transition machine ⟨phase, core⟩ symbol ↔
      RawTransitionCase machine phase core symbol output := by
  constructor
  · intro hmem
    cases core with
    | canonical endpoint slot =>
        simp only [transition] at hmem
        cases hdecode : decodePlain symbol with
        | none => simp [hdecode] at hmem
        | some code =>
            simp only [hdecode] at hmem
            have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
            subst symbol
            simp only [oneOutput, Set.mem_singleton_iff] at hmem
            subst output
            exact .canonical endpoint slot code
    | dispatch endpoint slot =>
        cases slot with
        | anchor =>
            simp only [transition] at hmem
            cases hdecode : decodePlain symbol with
            | none => simp [hdecode] at hmem
            | some code =>
                simp only [hdecode] at hmem
                have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
                subst symbol
                simp only [oneOutput, Set.mem_singleton_iff] at hmem
                subst output
                exact .dispatchAnchor endpoint code
        | outgoing =>
            simp only [transition] at hmem
            cases hdecode : decodePlain symbol with
            | none => simp [hdecode] at hmem
            | some code =>
                simp only [hdecode] at hmem
                have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
                subst symbol
                cases hwalk : (walker machine).transition endpoint code with
                | none =>
                    simp only [hwalk, oneOutput, Set.mem_singleton_iff] at hmem
                    subst output
                    exact .dispatchOutgoingNone endpoint code hwalk
                | some result =>
                    rcases result with ⟨target, direction⟩
                    simp only [hwalk] at hmem
                    cases direction with
                    | stationary old written =>
                        simp only [oneOutput, Set.mem_singleton_iff] at hmem
                        subst output
                        exact .dispatchOutgoingStationary endpoint target code old written hwalk
                    | departure old written travel =>
                        cases hallows : code.boundary.allows travel <;>
                          simp only [hallows, Bool.false_eq_true, ↓reduceIte,
                            oneOutput, Set.mem_singleton_iff] at hmem
                        · subst output
                          exact .dispatchOutgoingBlocked endpoint target code old written
                            travel hwalk hallows
                        · subst output
                          exact .dispatchOutgoingDeparture endpoint target code old written
                            travel hwalk hallows
                    | arrival old written travel =>
                        simp only [oneOutput, Set.mem_singleton_iff] at hmem
                        subst output
                        exact .dispatchOutgoingArrival endpoint target code old written travel hwalk
        | incoming source =>
            simp only [transition] at hmem
            cases hdecode : decodePlain symbol with
            | none => simp [hdecode] at hmem
            | some code =>
                simp only [hdecode] at hmem
                have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
                subst symbol
                cases hdirection : (Edge.ofIncoming endpoint source).direction with
                | stationary old written =>
                    simp only [hdirection] at hmem
                    by_cases hvalid : code = written ∧
                        (Edge.ofIncoming endpoint source).Enabled machine
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      subst output
                      exact .dispatchIncomingStationaryValid endpoint source code old written
                        hdirection hvalid.1 hvalid.2
                    · rw [if_neg hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      subst output
                      exact .dispatchIncomingStationaryInvalid endpoint source code old written
                        hdirection hvalid
                | departure old written travel =>
                    simp only [hdirection] at hmem
                    cases hallows : code.boundary.allows travel.reverse <;>
                      simp only [hallows, Bool.false_eq_true,
                        ↓reduceIte, oneOutput, Set.mem_singleton_iff] at hmem
                    · subst output
                      exact .dispatchIncomingBlocked endpoint source code old written
                        travel hdirection hallows
                    · subst output
                      exact .dispatchIncomingDeparture endpoint source code old written
                        travel hdirection hallows
                | arrival old written travel =>
                    simp only [hdirection, oneOutput, Set.mem_singleton_iff] at hmem
                    subst output
                    exact .dispatchIncomingArrival endpoint source code old written travel
                      hdirection
    | outgoingAtNeighbour edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodePlain symbol with
            | none => simp [hdecode] at hmem
            | some neighbour =>
                simp only [hdecode] at hmem
                have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
                subst symbol
                cases hallows : neighbour.boundary.allows travel.reverse <;>
                  simp only [hallows, Bool.false_eq_true, ↓reduceIte,
                    oneOutput, Set.mem_singleton_iff] at hmem
                · contradiction
                · subst output
                  exact .outgoingAtNeighbour edge old written neighbour travel
                    hdirection hallows
    | outgoingAtDeparture edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | outgoingDeparture observed =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ edge.Enabled machine
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .outgoingAtDeparture edge old written travel hdirection hvalid.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | outgoingRestoreNeighbour edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | outgoingNeighbour observed neighbour =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ edge.Enabled machine ∧
                        neighbour.boundary.allows travel.reverse = true
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .outgoingRestoreNeighbour edge old written neighbour travel
                        hdirection hvalid.2.1 hvalid.2.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | outgoingValidateAtDeparture edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodePlain symbol with
            | none => simp [hdecode] at hmem
            | some candidate =>
                simp only [hdecode] at hmem
                have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
                subst symbol
                by_cases hvalid : candidate = written ∧ edge.Enabled machine ∧
                    candidate.boundary.allows travel = true
                · rw [if_pos hvalid] at hmem
                  simp only [oneOutput, Set.mem_singleton_iff] at hmem
                  subst output
                  exact .outgoingValidateAtDeparture edge old written candidate travel
                    hdirection hvalid
                · rw [if_neg hvalid] at hmem
                  exact hmem.elim
    | incomingInspect edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodePlain symbol with
            | none => simp [hdecode] at hmem
            | some candidate =>
                simp only [hdecode] at hmem
                have hsymbol := eq_encodePlain_of_decodePlain_eq_some hdecode
                subst symbol
                by_cases hvalid : candidate = written ∧ edge.Enabled machine ∧
                    candidate.boundary.allows travel = true
                · rw [if_pos hvalid] at hmem
                  simp only [oneOutput, Set.mem_singleton_iff] at hmem
                  subst output
                  exact .incomingInspectValid edge old written candidate travel
                    hdirection hvalid
                · rw [if_neg hvalid] at hmem
                  simp only [oneOutput, Set.mem_singleton_iff] at hmem
                  subst output
                  exact .incomingInspectInvalid edge old written candidate travel
                    hdirection hvalid
    | incomingValidAtTarget edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | incomingTarget observed neighbour =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ edge.Enabled machine
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .incomingValidAtTarget edge old written neighbour travel
                        hdirection hvalid.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | incomingValidFinish edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | incomingSource observed =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ edge.Enabled machine ∧
                        old.boundary.allows travel = true
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .incomingValidFinish edge old written travel hdirection
                        hvalid.2.1 hvalid.2.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | incomingInvalidAtTarget edge candidate =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | incomingTarget observed neighbour =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      subst observed
                      subst symbol
                      subst output
                      exact .incomingInvalidAtTarget edge candidate neighbour old written
                        travel hdirection
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | incomingInvalidAtSource edge candidate =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | incomingInvalidSource observed saved =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ saved = candidate ∧
                        edge = Edge.ofIncoming edge.target edge.source ∧
                        ¬ (candidate = edge.written ∧ edge.Enabled machine ∧
                          candidate.boundary.allows travel = true)
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      have hsaved := hvalid.2.1
                      subst observed
                      subst saved
                      subst symbol
                      subst output
                      exact .incomingInvalidAtSource edge candidate old written travel hdirection
                        hvalid.2.2.1 hvalid.2.2.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | incomingReturnAtTarget edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | stationary old written => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | departure old written travel =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | incomingTarget observed neighbour =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧
                        edge = Edge.ofIncoming edge.target edge.source ∧
                        neighbour.boundary.allows travel.reverse = true
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .incomingReturnAtTarget edge old written neighbour travel
                        hdirection hvalid.2.1 hvalid.2.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | stationaryOutgoingPending edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | departure old written travel => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | stationary old written =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | stationaryOutgoing observed =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ edge.Enabled machine
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .stationaryOutgoingPending edge old written hdirection hvalid.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
    | stationaryIncomingPending edge =>
        simp only [transition] at hmem
        cases hdirection : edge.direction with
        | departure old written travel => simp [hdirection] at hmem
        | arrival old written travel => simp [hdirection] at hmem
        | stationary old written =>
            simp only [hdirection] at hmem
            cases hdecode : decodeWork symbol with
            | none => simp [hdecode] at hmem
            | some work =>
                cases work with
                | stationaryIncoming observed =>
                    simp only [hdecode] at hmem
                    by_cases hvalid : observed = edge ∧ edge.Enabled machine
                    · rw [if_pos hvalid] at hmem
                      simp only [oneOutput, Set.mem_singleton_iff] at hmem
                      have hsymbol := eq_encodeWork_of_decodeWork_eq_some hdecode
                      have hobserved := hvalid.1
                      subst observed
                      subst symbol
                      subst output
                      exact .stationaryIncomingPending edge old written hdirection hvalid.2
                    · rw [if_neg hvalid] at hmem
                      exact hmem.elim
                | _ => simp [hdecode] at hmem
  · intro hcase
    cases hcase with
    | canonical endpoint slot code =>
        simp only [transition, decodePlain_encodePlain, oneOutput,
          Set.mem_singleton_iff]
    | dispatchAnchor endpoint code =>
        simp only [transition, decodePlain_encodePlain, oneOutput,
          Set.mem_singleton_iff]
    | dispatchOutgoingNone endpoint code htransition =>
        simp only [transition, decodePlain_encodePlain, htransition, oneOutput,
          Set.mem_singleton_iff]
    | dispatchOutgoingStationary endpoint target code old written htransition =>
        simp only [transition, decodePlain_encodePlain, htransition, oneOutput,
          Set.mem_singleton_iff]
    | dispatchOutgoingDeparture endpoint target code old written travel htransition hallows =>
        simp only [transition, decodePlain_encodePlain, htransition, hallows,
          ↓reduceIte, oneOutput, Set.mem_singleton_iff]
    | dispatchOutgoingBlocked endpoint target code old written travel htransition hblocked =>
        simp only [transition, decodePlain_encodePlain, htransition, hblocked,
          Bool.false_eq_true, ↓reduceIte, oneOutput, Set.mem_singleton_iff]
    | dispatchOutgoingArrival endpoint target code old written travel htransition =>
        simp only [transition, decodePlain_encodePlain, htransition, oneOutput,
          Set.mem_singleton_iff]
    | dispatchIncomingStationaryValid endpoint source code old written hdirection hcode henabled =>
        simp only [transition, decodePlain_encodePlain, hdirection]
        rw [if_pos ⟨hcode, henabled⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | dispatchIncomingStationaryInvalid endpoint source code old written hdirection hinvalid =>
        simp only [transition, decodePlain_encodePlain, hdirection]
        rw [if_neg hinvalid]
        simp only [oneOutput, Set.mem_singleton_iff]
    | dispatchIncomingDeparture endpoint source code old written travel hdirection hallows =>
        simp only [transition, decodePlain_encodePlain, hdirection, hallows,
          ↓reduceIte, oneOutput, Set.mem_singleton_iff]
    | dispatchIncomingBlocked endpoint source code old written travel hdirection hblocked =>
        simp only [transition, decodePlain_encodePlain, hdirection, hblocked,
          Bool.false_eq_true, ↓reduceIte, oneOutput, Set.mem_singleton_iff]
    | dispatchIncomingArrival endpoint source code old written travel hdirection =>
        simp only [transition, decodePlain_encodePlain, hdirection, oneOutput,
          Set.mem_singleton_iff]
    | outgoingAtNeighbour edge old written neighbour travel hdirection hallows =>
        simp only [transition, hdirection, decodePlain_encodePlain, hallows,
          ↓reduceIte, oneOutput, Set.mem_singleton_iff]
    | outgoingAtDeparture edge old written travel hdirection henabled =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, henabled⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | outgoingRestoreNeighbour edge old written neighbour travel hdirection henabled hallows =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, henabled, hallows⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | outgoingValidateAtDeparture edge old written candidate travel hdirection hvalid =>
        simp only [transition, hdirection, decodePlain_encodePlain]
        rw [if_pos hvalid]
        simp only [oneOutput, Set.mem_singleton_iff]
    | incomingInspectValid edge old written candidate travel hdirection hvalid =>
        simp only [transition, hdirection, decodePlain_encodePlain]
        rw [if_pos hvalid]
        simp only [oneOutput, Set.mem_singleton_iff]
    | incomingInspectInvalid edge old written candidate travel hdirection hinvalid =>
        simp only [transition, hdirection, decodePlain_encodePlain]
        rw [if_neg hinvalid]
        simp only [oneOutput, Set.mem_singleton_iff]
    | incomingValidAtTarget edge old written neighbour travel hdirection henabled =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, henabled⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | incomingValidFinish edge old written travel hdirection henabled hallows =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, henabled, hallows⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | incomingInvalidAtTarget edge candidate neighbour old written travel hdirection =>
        simp only [transition, hdirection, decodeWork_encodeWork, ↓reduceIte,
          oneOutput, Set.mem_singleton_iff]
    | incomingInvalidAtSource edge candidate old written travel hdirection
        hwellformed hinvalid =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, True.intro, hwellformed, hinvalid⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | incomingReturnAtTarget edge old written neighbour travel hdirection
        hwellformed hallows =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, hwellformed, hallows⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | stationaryOutgoingPending edge old written hdirection henabled =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, henabled⟩]
        simp only [oneOutput, Set.mem_singleton_iff]
    | stationaryIncomingPending edge old written hdirection henabled =>
        simp only [transition, hdirection, decodeWork_encodeWork]
        rw [if_pos ⟨True.intro, henabled⟩]
        simp only [oneOutput, Set.mem_singleton_iff]

/-! ## Pointwise determinism and phase -/

/-- The table has at most one output for every raw state/symbol pair.  This is
pointwise and therefore independent of the tape width or tape well-formedness. -/
public theorem transition_subsingleton
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (state : State T Gamma Q) (symbol : Alphabet T Gamma Q) :
    (transition machine state symbol).Subsingleton := by
  rcases state with ⟨phase, core⟩
  cases core <;>
    simp only [transition] <;>
    repeat' first | split
  all_goals first
    | exact Set.subsingleton_empty
    | (unfold oneOutput; exact Set.subsingleton_singleton)

/-- The compiled raw LBA is functional, uniformly over every tape width. -/
public theorem rawMachine_functional
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    (rawMachine machine).Functional := by
  intro state symbol
  exact transition_subsingleton machine state symbol

/-- Exact configuration-level form of the constructor inversion theorem. -/
public theorem step_iff_exists_rawTransitionCase
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) :
    LBA.Step (rawMachine machine) source target ↔
      ∃ written direction,
        RawTransitionCase machine source.state.phase source.state.core
          source.tape.read (target.state, written, direction) ∧
        target.tape = (source.tape.write written).moveHead direction := by
  constructor
  · rintro ⟨next, written, direction, hmem, rfl⟩
    refine ⟨written, direction, ?_, rfl⟩
    exact (mem_transition_iff_rawTransitionCase machine
      source.state.phase source.state.core source.tape.read
      (next, written, direction)).1 hmem
  · rcases source with ⟨⟨phase, core⟩, sourceTape⟩
    rcases target with ⟨targetState, targetTape⟩
    rintro ⟨written, direction, hcase, htape⟩
    change RawTransitionCase machine phase core sourceTape.read
      (targetState, written, direction) at hcase
    change targetTape = (sourceTape.write written).moveHead direction at htape
    subst targetTape
    refine ⟨targetState, written, direction, ?_, rfl⟩
    exact (mem_transition_iff_rawTransitionCase machine phase core
      sourceTape.read (targetState, written, direction)).2 hcase

/-- The complete fixed-width raw configuration relation is right-unique,
including widths zero and one and arbitrary malformed tapes. -/
public theorem rawMachine_step_rightUnique
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ} :
    Relator.RightUnique
      (@LBA.Step (Alphabet T Gamma Q) (State T Gamma Q) n
        (rawMachine machine)) := by
  intro source left right hleft hright
  rcases hleft with
    ⟨leftState, leftWritten, leftDirection, hleftMem, rfl⟩
  rcases hright with
    ⟨rightState, rightWritten, rightDirection, hrightMem, rfl⟩
  have heq : (leftState, leftWritten, leftDirection) =
      (rightState, rightWritten, rightDirection) :=
    transition_subsingleton machine source.state source.tape.read
      hleftMem hrightMem
  cases heq
  rfl

/-- Every member of the raw transition table has precisely the toggled phase. -/
public theorem phase_eq_not_of_mem_transition
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {state next : State T Gamma Q} {read written : Alphabet T Gamma Q}
    {direction : DLBA.Dir}
    (hmem : (next, written, direction) ∈ transition machine state read) :
    next.phase = !state.phase := by
  rcases state with ⟨phase, core⟩
  have hcase :=
    (mem_transition_iff_rawTransitionCase machine phase core read
      (next, written, direction)).1 hmem
  cases hcase <;> rfl

/-- Every raw configuration edge toggles the explicit phase bit, including
edges on malformed tapes and at widths zero and one. -/
public theorem phase_eq_not_of_step
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) source target) :
    target.state.phase = !source.state.phase := by
  rcases hstep with ⟨next, written, direction, hmem, rfl⟩
  exact phase_eq_not_of_mem_transition machine hmem

/-- In disequality form, every raw edge crosses the explicit bipartition. -/
public theorem phase_ne_of_step
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) source target) :
    source.state.phase ≠ target.state.phase := by
  rw [phase_eq_not_of_step machine hstep]
  cases source.state.phase <;> simp

end

end GraphWalking.MarkedEulerProbe

end
