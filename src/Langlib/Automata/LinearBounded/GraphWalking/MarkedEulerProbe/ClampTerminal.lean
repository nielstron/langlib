module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.Structural
import Mathlib.Tactic

@[expose]
public section

/-!
# Clamped moving landings are terminal

Every genuinely moving protocol rule writes a constructor which its landing
state does not accept.  On a nonclamping move the head leaves that constructor
behind.  If the physical raw move clamps, however, the head remains over the
fresh constructor, so the landing has no outgoing transition.  The theorem
below checks all moving cases of the exhaustive structural inversion and is
uniform in the tape width and in malformed raw tapes.
-/

namespace GraphWalking.MarkedEulerProbe

open LBA

universe uTerminal uWork uState

noncomputable section

local instance (priority := low) markedEulerProbeClampTerminalPropDecidable
    (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}

/-- A write-and-move whose physical head does not change leaves the freshly
written symbol under the landing head. -/
public theorem read_write_moveHead_eq_written_of_head_eq
    {A : Type*} {n : ℕ} (tape : DLBA.BoundedTape A n)
    (written : A) (direction : DLBA.Dir)
    (hhead : ((tape.write written).moveHead direction).head = tape.head) :
    ((tape.write written).moveHead direction).read = written := by
  change Function.update tape.contents tape.head written
      ((tape.write written).moveHead direction).head = written
  rw [hhead, Function.update_self]

/-- Every moving table entry whose physical landing clamps is a terminal raw
configuration.  The premise names the actual local transition output, so it
distinguishes a clamped moving edge from the many legitimate stationary
protocol edges which also preserve the head. -/
public theorem no_step_of_clamped_moving_transition
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {state next : State T Gamma Q}
    {read written : Alphabet T Gamma Q} {direction : DLBA.Dir}
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n)
    (hmem : (next, written, direction) ∈ transition machine state read)
    (hmoving : direction ≠ .stay)
    (hclamp : ((tape.write written).moveHead direction).head = tape.head) :
    ∀ target, ¬ LBA.Step (rawMachine machine)
      ⟨next, (tape.write written).moveHead direction⟩ target := by
  have hlandingRead :
      ((tape.write written).moveHead direction).read = written :=
    read_write_moveHead_eq_written_of_head_eq tape written direction hclamp
  rcases state with ⟨phase, core⟩
  have hcase :=
    (mem_transition_iff_rawTransitionCase machine phase core read
      (next, written, direction)).1 hmem
  intro target hstep
  rcases hstep with
    ⟨targetState, targetWritten, targetDirection, hnext, htarget⟩
  change (targetState, targetWritten, targetDirection) ∈
    transition machine next
      ((tape.write written).moveHead direction).read at hnext
  rw [hlandingRead] at hnext
  cases hcase with
  | canonical => exact hmoving rfl
  | dispatchAnchor => exact hmoving rfl
  | dispatchOutgoingNone => exact hmoving rfl
  | dispatchOutgoingStationary => exact hmoving rfl
  | dispatchOutgoingDeparture =>
      simp only [nextState, transition, decodePlain_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | dispatchOutgoingBlocked => exact hmoving rfl
  | dispatchOutgoingArrival => exact hmoving rfl
  | dispatchIncomingStationaryValid => exact hmoving rfl
  | dispatchIncomingStationaryInvalid => exact hmoving rfl
  | dispatchIncomingDeparture endpoint source code old saved travel hdirection hallows =>
      simp only [nextState, transition, hdirection, decodePlain_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | dispatchIncomingBlocked => exact hmoving rfl
  | dispatchIncomingArrival => exact hmoving rfl
  | outgoingAtNeighbour edge old saved neighbour travel hdirection hallows =>
      simp only [nextState, transition, hdirection, decodeWork_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | outgoingAtDeparture edge old saved travel hdirection henabled =>
      cases saved <;>
        simp only [nextState, transition, hdirection, decodeWork_encodePlain,
          Set.mem_empty_iff_false] at hnext
  | outgoingRestoreNeighbour edge old saved neighbour travel hdirection henabled hallows =>
      simp only [nextState, transition, hdirection, decodePlain_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | outgoingValidateAtDeparture edge old saved candidate travel hdirection hvalid =>
      cases candidate <;>
        simp only [nextState, transition, hdirection, decodeWork_encodePlain,
          Set.mem_empty_iff_false] at hnext
  | incomingInspectValid edge old saved candidate travel hdirection hvalid =>
      simp only [nextState, transition, hdirection, decodeWork_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | incomingInspectInvalid edge old saved candidate travel hdirection hinvalid =>
      simp only [nextState, transition, hdirection, decodeWork_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | incomingValidAtTarget edge old saved neighbour travel hdirection henabled =>
      cases neighbour <;>
        simp only [nextState, transition, hdirection, decodeWork_encodePlain,
          Set.mem_empty_iff_false] at hnext
  | incomingValidFinish => exact hmoving rfl
  | incomingInvalidAtTarget edge candidate neighbour old saved travel hdirection =>
      simp only [nextState, transition, hdirection, decodeWork_encodeWork,
        Set.mem_empty_iff_false] at hnext
  | incomingInvalidAtSource edge candidate old saved travel hdirection
      hwellformed hinvalid =>
      cases candidate <;>
        simp only [nextState, transition, hdirection, decodeWork_encodePlain,
          Set.mem_empty_iff_false] at hnext
  | incomingReturnAtTarget => exact hmoving rfl
  | stationaryOutgoingPending => exact hmoving rfl
  | stationaryIncomingPending => exact hmoving rfl

end

end GraphWalking.MarkedEulerProbe

end
