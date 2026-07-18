module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.Structural
public import Langlib.Automata.LinearBounded.BoundaryShuttle.RawDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical-target predecessor uniqueness for the marked Euler probe

All protocol families finish with a stationary raw edge.  Although several
families can name the same canonical control state, their guards are mutually
exclusive, and enabled marked-controller edges are functional.  Consequently
an exact canonical raw configuration has at most one predecessor.  This is the
only cross-family part of the complete indegree analysis; moving protocol
targets are treated separately in `RawDegree`.
-/

namespace GraphWalking

open Classical

namespace MarkedEulerProbe

universe uTerminal uWork uState

variable {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}

set_option maxRecDepth 10000

/-! ## A local inverse for canonical landings -/

/-- Read the unique raw-table row which can produce a given canonical state
and visible plain symbol.  The definition is deliberately the inverse of the
five canonical-finishing table families, so its functionality packages all
cross-family guard exclusions in one place. -/
private noncomputable def canonicalPredecessor?
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
    (visible : Alphabet T Gamma Q) :
    Option (CoreState T Gamma Q × Alphabet T Gamma Q) :=
  match decodePlain visible with
  | none => none
  | some code =>
      match slot with
      | .anchor => some (.dispatch endpoint .anchor, encodePlain code)
      | .outgoing =>
          match (walker machine).transition endpoint code with
          | none => some (.dispatch endpoint .outgoing, encodePlain code)
          | some (target, direction) =>
              let edge : Edge T Gamma Q :=
                { source := endpoint, target := target, direction := direction }
              match direction with
              | .stationary _ _ =>
                  some (.stationaryIncomingPending edge,
                    encodeWork (.stationaryIncoming edge))
              | .departure _ _ travel =>
                  if code.boundary.allows travel then
                    some (.incomingValidFinish edge,
                      encodeWork (.incomingSource edge))
                  else
                    some (.dispatch endpoint .outgoing, encodePlain code)
              | .arrival _ _ _ =>
                  some (.dispatch endpoint .outgoing, encodePlain code)
      | .incoming source =>
          let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
          match edge.direction with
          | .stationary _ written =>
              if code = written ∧ edge.Enabled machine then
                some (.stationaryOutgoingPending edge,
                  encodeWork (.stationaryOutgoing edge))
              else
                some (.dispatch endpoint (.incoming source), encodePlain code)
          | .departure _ _ travel =>
              if code.boundary.allows travel.reverse then
                some (.incomingReturnAtTarget edge,
                  encodeWork (.incomingTarget edge code))
              else
                some (.dispatch endpoint (.incoming source), encodePlain code)
          | .arrival _ _ _ =>
              some (.dispatch endpoint (.incoming source), encodePlain code)

private theorem ofIncoming_target_source_eq_of_enabled
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (edge : Edge T Gamma Q) (henabled : edge.Enabled machine) :
    Edge.ofIncoming edge.target edge.source = edge := by
  have hdirection :=
    Edge.target_snd_eq_direction_of_enabled machine edge henabled
  rcases edge with ⟨source, target, direction⟩
  simp only [Edge.ofIncoming] at hdirection ⊢
  exact congrArg (fun savedDirection =>
    ({ source := source, target := target, direction := savedDirection } :
      Edge T Gamma Q)) hdirection

/-- Every raw table entry ending at a canonical local state is recovered by
the canonical inverse above. -/
private theorem canonicalPredecessor?_eq_some_of_rawTransitionCase
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {phase : Bool} {core : CoreState T Gamma Q}
    {read : Alphabet T Gamma Q}
    {output : State T Gamma Q × Alphabet T Gamma Q × DLBA.Dir}
    (hcase : RawTransitionCase machine phase core read output)
    {targetPhase : Bool} {endpoint : LiftState T Gamma Q}
    {slot : Slot T Gamma Q} {written : Alphabet T Gamma Q}
    (houtput : output =
      (⟨targetPhase, .canonical endpoint slot⟩, written, .stay)) :
    phase = !targetPhase ∧
      canonicalPredecessor? machine endpoint slot written = some (core, read) := by
  cases hcase <;> simp [nextState] at houtput
  case dispatchAnchor endpoint' code =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by simp [canonicalPredecessor?]⟩
  case dispatchOutgoingNone endpoint' code htransition =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by simp [canonicalPredecessor?, htransition]⟩
  case dispatchOutgoingBlocked endpoint' target code old saved travel
      htransition hblocked =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by
      simp [canonicalPredecessor?, htransition, hblocked]⟩
  case dispatchOutgoingArrival endpoint' target code old saved travel
      htransition =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by simp [canonicalPredecessor?, htransition]⟩
  case dispatchIncomingStationaryInvalid endpoint' source code old saved
      hdirection hinvalid =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by
      simp [canonicalPredecessor?, hdirection, hinvalid]⟩
  case dispatchIncomingBlocked endpoint' source code old saved travel
      hdirection hblocked =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by
      simp [canonicalPredecessor?, hdirection, hblocked]⟩
  case dispatchIncomingArrival endpoint' source code old saved travel
      hdirection =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint'
    subst slot
    subst written
    exact ⟨hphase, by simp [canonicalPredecessor?, hdirection]⟩
  case incomingValidFinish edge old saved travel hdirection henabled hallows =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint
    subst slot
    subst written
    have hold := Edge.old_eq_of_direction_departure edge old saved travel hdirection
    subst old
    have hedge :
        (⟨edge.source, edge.target, edge.direction⟩ : Edge T Gamma Q) = edge := by
      cases edge
      rfl
    exact ⟨hphase, by
      simp [Edge.Enabled] at henabled
      simp only [canonicalPredecessor?, decodePlain_encodePlain, henabled]
      simp only [hedge]
      rw [hdirection]
      simp [hallows]⟩
  case incomingReturnAtTarget edge old saved neighbour travel hdirection
      hwellformed hallows =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint
    subst slot
    subst written
    have hedge : Edge.ofIncoming edge.target edge.source = edge :=
      hwellformed.symm
    exact ⟨hphase, by
      simp [canonicalPredecessor?, hedge, hdirection, hallows]⟩
  case stationaryOutgoingPending edge old saved hdirection henabled =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint
    subst slot
    subst written
    have hedge := ofIncoming_target_source_eq_of_enabled machine edge henabled
    exact ⟨hphase, by
      simp [canonicalPredecessor?, hedge, hdirection, henabled]⟩
  case stationaryIncomingPending edge old saved hdirection henabled =>
    rcases houtput with ⟨⟨hphase, hendpoint, hslot⟩, hwritten⟩
    subst endpoint
    subst slot
    subst written
    have hold := Edge.old_eq_of_direction_stationary edge old saved hdirection
    subst old
    have hedge :
        (⟨edge.source, edge.target, edge.direction⟩ : Edge T Gamma Q) = edge := by
      cases edge
      rfl
    exact ⟨hphase, by
      simp [Edge.Enabled] at henabled
      simp only [canonicalPredecessor?, decodePlain_encodePlain, henabled]
      simp only [hedge]
      rw [hdirection]⟩

/-! ## Configuration-level uniqueness -/

private theorem moveHead_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) : tape.moveHead .stay = tape := by
  cases tape
  rfl

private theorem write_write_read {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (written : A) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem direction_eq_stay_of_canonical_rawTransitionCase
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {phase : Bool} {core : CoreState T Gamma Q}
    {read written : Alphabet T Gamma Q}
    {direction : DLBA.Dir} {targetPhase : Bool}
    {endpoint : LiftState T Gamma Q} {slot : Slot T Gamma Q}
    (hcase : RawTransitionCase machine phase core read
      (⟨targetPhase, .canonical endpoint slot⟩, written, direction)) :
    direction = .stay := by
  generalize houtput :
      ((⟨targetPhase, .canonical endpoint slot⟩ : State T Gamma Q),
        written, direction) = output at hcase
  cases hcase <;> simp [nextState] at houtput
  all_goals exact houtput.2.2

/-- Two raw edges ending in the same exact canonical configuration have the
same source, uniformly over all widths and malformed tapes. -/
public theorem predecessor_canonical_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : Nat}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {endpoint : LiftState T Gamma Q}
    {slot : Slot T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .canonical endpoint slot⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .canonical endpoint slot⟩, tape⟩) :
    left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
  rw [step_iff_exists_rawTransitionCase] at hleft hright
  rcases hleft with ⟨leftWritten, leftDirection, leftCase, leftTapeEq⟩
  rcases hright with ⟨rightWritten, rightDirection, rightCase, rightTapeEq⟩
  change RawTransitionCase machine leftPhase leftCore leftTape.read
    (⟨targetPhase, .canonical endpoint slot⟩, leftWritten, leftDirection) at leftCase
  change RawTransitionCase machine rightPhase rightCore rightTape.read
    (⟨targetPhase, .canonical endpoint slot⟩, rightWritten, rightDirection) at rightCase
  change tape = (leftTape.write leftWritten).moveHead leftDirection at leftTapeEq
  change tape = (rightTape.write rightWritten).moveHead rightDirection at rightTapeEq
  have hleftDirection : leftDirection = .stay :=
    direction_eq_stay_of_canonical_rawTransitionCase machine leftCase
  have hrightDirection : rightDirection = .stay :=
    direction_eq_stay_of_canonical_rawTransitionCase machine rightCase
  subst leftDirection
  subst rightDirection
  rw [moveHead_stay] at leftTapeEq rightTapeEq
  have hleftWritten : tape.read = leftWritten := by
    rw [leftTapeEq]
    simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
  have hrightWritten : tape.read = rightWritten := by
    rw [rightTapeEq]
    simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
  have hwritten : leftWritten = rightWritten :=
    hleftWritten.symm.trans hrightWritten
  have hleftInverse :=
    canonicalPredecessor?_eq_some_of_rawTransitionCase machine leftCase rfl
  have hrightInverse :=
    canonicalPredecessor?_eq_some_of_rawTransitionCase machine rightCase rfl
  rw [← hwritten] at hrightInverse
  have hphase : leftPhase = rightPhase :=
    hleftInverse.1.trans hrightInverse.1.symm
  have hlocal : (leftCore, leftTape.read) = (rightCore, rightTape.read) :=
    Option.some.inj (hleftInverse.2.symm.trans hrightInverse.2)
  have hcore : leftCore = rightCore := congrArg Prod.fst hlocal
  have hread : leftTape.read = rightTape.read := congrArg Prod.snd hlocal
  have hleftRestore : tape.write leftTape.read = leftTape := by
    rw [leftTapeEq]
    exact write_write_read leftTape leftWritten
  have hrightRestore : tape.write rightTape.read = rightTape := by
    rw [rightTapeEq]
    exact write_write_read rightTape rightWritten
  have htape : leftTape = rightTape := by
    calc
      leftTape = tape.write leftTape.read := hleftRestore.symm
      _ = tape.write rightTape.read := by rw [hread]
      _ = rightTape := hrightRestore
  cases hphase
  cases hcore
  cases htape
  rfl

/-- A canonical raw configuration has at most one predecessor, on every tape
width and without any tape well-formedness promise. -/
public theorem encard_predecessors_canonical_le_one
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : Nat}
    (targetPhase : Bool) (endpoint : LiftState T Gamma Q)
    (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .canonical endpoint slot⟩, tape⟩} ≤ 1 := by
  apply Set.encard_le_one_iff.mpr
  intro left right hleft hright
  exact predecessor_canonical_eq machine hleft hright

/-- The uniform degree-two form used by the complete raw indegree theorem. -/
public theorem encard_predecessors_canonical_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : Nat}
    (targetPhase : Bool) (endpoint : LiftState T Gamma Q)
    (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .canonical endpoint slot⟩, tape⟩} ≤ 2 := by
  exact (encard_predecessors_canonical_le_one machine targetPhase endpoint slot tape).trans
    (by norm_num)

end MarkedEulerProbe

end GraphWalking

end
