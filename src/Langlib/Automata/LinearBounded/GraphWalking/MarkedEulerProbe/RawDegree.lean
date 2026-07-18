module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.CanonicalDegree
public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.ClampTerminal
public import Langlib.Automata.LinearBounded.BoundaryShuttle.RawDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# Complete-raw-graph degree analysis for the marked Euler probe

The raw transition table is deterministic without a well-formedness promise.
For moving protocol phases, the only possible predecessor heads are the
stationary clamped candidate and the genuine reverse-neighbour candidate.
The proofs in this file deliberately quantify over arbitrary raw tapes and
all widths, including zero.
-/

namespace GraphWalking

open Classical

namespace MarkedEulerProbe

universe uTerminal uWork uState

variable {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}

private theorem write_write_read {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (written : A) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem write_read {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) : tape.write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem moveHead_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) : tape.moveHead .stay = tape := by
  cases tape
  rfl

/-- Once the original head and scanned symbol agree, a common post-step tape
determines the entire predecessor tape.  The two steps may write different
symbols and request different directions; neither affects this restoration
argument. -/
private theorem tape_eq_of_write_move_eq_of_head_eq_of_read_eq
    {A : Type*} {n : ℕ}
    (left right target : DLBA.BoundedTape A n)
    (leftWritten rightWritten : A) (leftDirection rightDirection : DLBA.Dir)
    (hleft : (left.write leftWritten).moveHead leftDirection = target)
    (hright : (right.write rightWritten).moveHead rightDirection = target)
    (hhead : left.head = right.head) (hread : left.read = right.read) :
    left = right := by
  apply BoundedTapeMemory.eq_of_contents_head
  · funext position
    by_cases hposition : position = left.head
    · subst position
      change left.contents left.head = right.contents right.head at hread
      simpa [hhead] using hread
    · have hcontents := congrArg (fun tape => tape.contents position)
          (hleft.trans hright.symm)
      change Function.update left.contents left.head leftWritten position =
        Function.update right.contents right.head rightWritten position at hcontents
      have hpositionRight : position ≠ right.head := by
        rwa [← hhead]
      simpa [hposition, hpositionRight] using hcontents
  · exact hhead

/-- The symbol written at a common predecessor head is visible in the common
post-step contents, independently of the requested movement. -/
private theorem written_eq_of_write_move_eq_of_head_eq
    {A : Type*} {n : ℕ}
    (left right target : DLBA.BoundedTape A n)
    (leftWritten rightWritten : A) (leftDirection rightDirection : DLBA.Dir)
    (hleft : (left.write leftWritten).moveHead leftDirection = target)
    (hright : (right.write rightWritten).moveHead rightDirection = target)
    (hhead : left.head = right.head) : leftWritten = rightWritten := by
  have hcontents := congrArg (fun tape => tape.contents left.head)
    (hleft.trans hright.symm)
  change Function.update left.contents left.head leftWritten left.head =
    Function.update right.contents right.head rightWritten left.head at hcontents
  rw [hhead] at hcontents
  simpa using hcontents

/-- A predecessor family whose head has two possible values and which is
injective at each fixed head has extended cardinality at most two. -/
private theorem encard_predecessors_le_two_of_heads
    {C H : Type*} (relation : C → Prop) (head : C → H) (first second : H)
    (hheads : ∀ cfg, relation cfg → head cfg = first ∨ head cfg = second)
    (hfixed : ∀ left right, relation left → relation right →
      head left = head right → left = right) :
    Set.encard {cfg | relation cfg} ≤ 2 := by
  let firstSet : Set C := {cfg | relation cfg ∧ head cfg = first}
  let secondSet : Set C := {cfg | relation cfg ∧ head cfg = second}
  have hsubset : {cfg | relation cfg} ⊆ firstSet ∪ secondSet := by
    intro cfg hcfg
    rcases hheads cfg hcfg with hfirst | hsecond
    · exact Or.inl ⟨hcfg, hfirst⟩
    · exact Or.inr ⟨hcfg, hsecond⟩
  have hfirstCard : firstSet.encard ≤ 1 := Set.encard_le_one_iff.mpr (by
    intro left right hleft hright
    exact hfixed left right hleft.1 hright.1 (hleft.2.trans hright.2.symm))
  have hsecondCard : secondSet.encard ≤ 1 := Set.encard_le_one_iff.mpr (by
    intro left right hleft hright
    exact hfixed left right hleft.1 hright.1 (hleft.2.trans hright.2.symm))
  calc
    Set.encard {cfg | relation cfg} ≤ Set.encard (firstSet ∪ secondSet) :=
      Set.encard_le_encard hsubset
    _ ≤ firstSet.encard + secondSet.encard := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add hfirstCard hsecondCard
    _ = 2 := by norm_num

/-- Cardinal wrapper for the recurring moving-phase inversion shape: one
clamped candidate plus one reverse-neighbour candidate whose travel is fixed
by the saved direction record. -/
private theorem encard_relation_le_two_of_fixed_or_direction
    {C A : Type*} (relation : C → Prop)
    (edgeDirection : BoundedTapeMemory.Direction A)
    (first : C) (second : BoundedTapeMemory.Travel → C)
    (hinvert : ∀ cfg, relation cfg →
      cfg = first ∨ ∃ old written travel,
        edgeDirection = .departure old written travel ∧
          cfg = second travel) :
    Set.encard {cfg | relation cfg} ≤ 2 := by
  cases hdirection : edgeDirection with
  | stationary old written =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases hinvert left hleft with rfl | ⟨_, _, _, hleftDirection, _⟩
      · rcases hinvert right hright with rfl | ⟨_, _, _, hrightDirection, _⟩
        · rfl
        · rw [hdirection] at hrightDirection
          contradiction
      · rw [hdirection] at hleftDirection
        contradiction
  | arrival old written travel =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases hinvert left hleft with rfl | ⟨_, _, _, hleftDirection, _⟩
      · rcases hinvert right hright with rfl | ⟨_, _, _, hrightDirection, _⟩
        · rfl
        · rw [hdirection] at hrightDirection
          contradiction
      · rw [hdirection] at hleftDirection
        contradiction
  | departure old written travel =>
      calc
        Set.encard {cfg | relation cfg} ≤
            Set.encard ({first, second travel} : Set C) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases hinvert cfg hcfg with hfirst | ⟨leftOld, leftWritten,
              leftTravel, hleftDirection, hsecond⟩
          · exact Or.inl hfirst
          · rw [hdirection] at hleftDirection
            rcases hleftDirection with ⟨rfl, rfl, rfl⟩
            exact Or.inr hsecond
        _ ≤ 2 := by
          calc
            Set.encard ({first, second travel} : Set C) ≤
                Set.encard ({second travel} : Set C) + 1 :=
              Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl

/-- Cardinal wrapper for a target core which can only be entered by a saved
departure and whose predecessor head then has the usual two possibilities. -/
private theorem encard_relation_le_two_of_departure_heads
    {C A H : Type*} (relation : C → Prop)
    (edgeDirection : BoundedTapeMemory.Direction A) (head : C → H)
    (first : H) (second : BoundedTapeMemory.Travel → H)
    (hdeparture : ∀ cfg, relation cfg → ∃ old written travel,
      edgeDirection = .departure old written travel)
    (hheads : ∀ cfg, relation cfg → ∀ old written travel,
      edgeDirection = .departure old written travel →
        head cfg = first ∨ head cfg = second travel)
    (hfixed : ∀ left right, relation left → relation right →
      head left = head right → left = right) :
    Set.encard {cfg | relation cfg} ≤ 2 := by
  cases hdirection : edgeDirection with
  | stationary old written =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases hdeparture left hleft with
        ⟨leftOld, leftWritten, leftTravel, hleftDirection⟩
      rw [hdirection] at hleftDirection
      cases hleftDirection
  | arrival old written travel =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases hdeparture left hleft with
        ⟨leftOld, leftWritten, leftTravel, hleftDirection⟩
      rw [hdirection] at hleftDirection
      cases hleftDirection
  | departure old written travel =>
      exact encard_predecessors_le_two_of_heads relation head first
        (second travel)
        (fun cfg hcfg => hheads cfg hcfg old written travel hdirection)
        hfixed

/-- Every direction emitted by the marked controller stores the scanned code
as its old field.  This local copy keeps the complete-raw analysis independent
of the forward simulation development. -/
private theorem old_eq_of_walker_transition
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {endpoint target : LiftState T Gamma Q} {code : PlainCode T Gamma}
    {direction : BoundedTapeMemory.Direction (PlainCode T Gamma)}
    (htransition : (walker machine).transition endpoint code =
      some (target, direction)) :
    (Edge.mk endpoint target direction).old = code := by
  rcases endpoint with ⟨state, remembered⟩
  cases hsource : machine.transition state code.logical with
  | none =>
      simp [walker, Machine.directionLift, BoundedTapeController.machine,
        markedMachine, hsource] at htransition
  | some output =>
      rcases output with ⟨targetState, logicalWritten, sourceDirection⟩
      cases sourceDirection with
      | left =>
          cases hnormalize : code.normalizeDirection .left <;>
            simp [walker, Machine.directionLift, BoundedTapeController.machine,
              markedMachine, BoundedTapeController.operation, hsource,
              hnormalize] at htransition <;>
            rcases htransition with ⟨rfl, rfl⟩ <;> rfl
      | right =>
          cases hnormalize : code.normalizeDirection .right <;>
            simp [walker, Machine.directionLift, BoundedTapeController.machine,
              markedMachine, BoundedTapeController.operation, hsource,
              hnormalize] at htransition <;>
            rcases htransition with ⟨rfl, rfl⟩ <;> rfl
      | stay =>
          simp [walker, Machine.directionLift, BoundedTapeController.machine,
            markedMachine, BoundedTapeController.operation, hsource] at htransition
          rcases htransition with ⟨rfl, rfl⟩
          rfl

/-- Exactly the protocol cores entered by moving table rules. -/
private def MovingLanding : CoreState T Gamma Q → Prop
  | .canonical _ _ | .dispatch _ _
  | .stationaryOutgoingPending _ | .stationaryIncomingPending _ => False
  | _ => True

private def landingEdge : CoreState T Gamma Q → Option (Edge T Gamma Q)
  | .outgoingAtNeighbour edge | .outgoingAtDeparture edge
  | .outgoingRestoreNeighbour edge | .outgoingValidateAtDeparture edge
  | .incomingInspect edge | .incomingValidAtTarget edge
  | .incomingValidFinish edge | .incomingReturnAtTarget edge => some edge
  | .incomingInvalidAtTarget edge _
  | .incomingInvalidAtSource edge _ => some edge
  | _ => none

private theorem travel_toDir_ne_stay
    (travel : BoundedTapeMemory.Travel) : travel.toDir ≠ .stay := by
  cases travel <;> simp [BoundedTapeMemory.Travel.toDir]

/-- Every edge-carrying moving landing can only be entered for a saved
departure direction. -/
private theorem departure_of_step_to_moving_landing_edge
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {edge : Edge T Gamma Q}
    (hedge : landingEdge target.state.core = some edge)
    (hstep : LBA.Step (rawMachine machine) source target) :
    ∃ old written travel, edge.direction = .departure old written travel := by
  rcases source with ⟨⟨phase, core⟩, sourceTape⟩
  rcases hstep with ⟨nextState', writtenSymbol, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (nextState', writtenSymbol, direction) ∈
    transition machine ⟨phase, core⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  subst target
  cases hmem <;> simp only [nextState, landingEdge, Option.some.injEq] at hedge
  all_goals try contradiction
  all_goals subst edge
  all_goals first
    | exact ⟨_, _, _, by assumption⟩
    | exact ⟨_, _, _, rfl⟩

/-- A predecessor of a moving landing which shares its physical head with the
landing witnesses a clamp, hence the landing is terminal. -/
private theorem no_step_of_moving_landing_predecessor_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {source target : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hmovingLanding : MovingLanding target.state.core)
    (hstep : LBA.Step (rawMachine machine) source target)
    (hhead : source.tape.head = target.tape.head) :
    ∀ next, ¬ LBA.Step (rawMachine machine) target next := by
  rcases source with ⟨⟨phase, core⟩, sourceTape⟩
  rcases hstep with ⟨nextState', written, direction, hmem, htarget⟩
  have htransition := hmem
  generalize hread : sourceTape.read = read at hmem
  change (nextState', written, direction) ∈
    transition machine ⟨phase, core⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  subst target
  have hmoving : direction ≠ .stay := by
    cases hmem <;>
      simp only [nextState, MovingLanding] at hmovingLanding
    all_goals first
      | contradiction
      | assumption
      | exact travel_toDir_ne_stay _
  exact no_step_of_clamped_moving_transition machine sourceTape htransition hmoving
    hhead.symm

private theorem left_or_right_eq_first_of_two_head_choices
    {C H : Type*} {left right : C} {head : C → H} {first second : H}
    (hne : left ≠ right)
    (hfixed : head left = head right → left = right)
    (hleft : head left = first ∨ head left = second)
    (hright : head right = first ∨ head right = second) :
    head left = first ∨ head right = first := by
  rcases hleft with hleftFirst | hleftSecond
  · exact Or.inl hleftFirst
  · rcases hright with hrightFirst | hrightSecond
    · exact Or.inr hrightFirst
    · exact False.elim (hne (hfixed (hleftSecond.trans hrightSecond.symm)))

private theorem left_or_right_eq_first_of_two_configuration_choices
    {C : Type*} {left right first second : C} (hne : left ≠ right)
    (hleft : left = first ∨ left = second)
    (hright : right = first ∨ right = second) :
    left = first ∨ right = first := by
  rcases hleft with hleftFirst | hleftSecond
  · exact Or.inl hleftFirst
  · rcases hright with hrightFirst | hrightSecond
    · exact Or.inr hrightFirst
    · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))

private theorem no_step_of_two_predecessors_with_two_head_choices
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right target :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {secondHead : Fin (n + 1)}
    (hne : left ≠ right)
    (hleft : LBA.Step (rawMachine machine) left target)
    (hright : LBA.Step (rawMachine machine) right target)
    (hmovingLanding : MovingLanding target.state.core)
    (hleftHeads : left.tape.head = target.tape.head ∨
      left.tape.head = secondHead)
    (hrightHeads : right.tape.head = target.tape.head ∨
      right.tape.head = secondHead)
    (hfixed : left.tape.head = right.tape.head → left = right) :
    ∀ next, ¬ LBA.Step (rawMachine machine) target next := by
  rcases left_or_right_eq_first_of_two_head_choices
      (head := fun cfg : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n =>
        cfg.tape.head)
      (first := target.tape.head) (second := secondHead)
      hne hfixed hleftHeads hrightHeads with hleftClamp | hrightClamp
  · exact no_step_of_moving_landing_predecessor_head_eq machine
      hmovingLanding hleft hleftClamp
  · exact no_step_of_moving_landing_predecessor_head_eq machine
      hmovingLanding hright hrightClamp

private theorem no_step_of_two_predecessors_with_two_configuration_choices
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right first second target :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hne : left ≠ right)
    (hleft : LBA.Step (rawMachine machine) left target)
    (hright : LBA.Step (rawMachine machine) right target)
    (hmovingLanding : MovingLanding target.state.core)
    (hleftChoices : left = first ∨ left = second)
    (hrightChoices : right = first ∨ right = second)
    (hfirstHead : first.tape.head = target.tape.head) :
    ∀ next, ¬ LBA.Step (rawMachine machine) target next := by
  rcases left_or_right_eq_first_of_two_configuration_choices hne
      hleftChoices hrightChoices with hleftFirst | hrightFirst
  · subst left
    exact no_step_of_moving_landing_predecessor_head_eq machine
      hmovingLanding hleft hfirstHead
  · subst right
    exact no_step_of_moving_landing_predecessor_head_eq machine
      hmovingLanding hright hfirstHead

/-! ## Outdegree -/

/-- Functionality gives the complete raw graph outdegree at most one, hence
in particular at most two, at every width. -/
public theorem rawMachine_configurationOutdegreeAtMostTwo
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    (rawMachine machine).ConfigurationOutdegreeAtMostTwo := by
  intro n source
  apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
  intro left right hleft hright
  exact rawMachine_step_rightUnique machine hleft hright

/-! ## Moving-phase predecessor inversion -/

/-! ## Stationary protocol fibres -/

/-- Rotation is a permutation, so a dispatch configuration has one raw
predecessor even before any tape well-formedness assumption. -/
public theorem predecessor_dispatch_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {endpoint : LiftState T Gamma Q}
    {slot : Slot T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .dispatch endpoint slot⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .dispatch endpoint slot⟩, tape⟩) :
    left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases hleft with ⟨leftNext, leftOutput, leftDirection, hleftMem,
    hleftTarget⟩
  generalize hleftRead : leftTape.read = leftRead at hleftMem
  change (leftNext, leftOutput, leftDirection) ∈
    transition machine ⟨leftPhase, leftCore⟩ leftRead at hleftMem
  rw [mem_transition_iff_rawTransitionCase] at hleftMem
  cases hleftMem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) hleftTarget
    simp only [nextState] at hcore
    cases hcore
  next leftEndpoint leftSlot leftCode =>
    rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
    rcases hright with ⟨rightNext, rightOutput, rightDirection, hrightMem,
      hrightTarget⟩
    generalize hrightRead : rightTape.read = rightRead at hrightMem
    change (rightNext, rightOutput, rightDirection) ∈
      transition machine ⟨rightPhase, rightCore⟩ rightRead at hrightMem
    rw [mem_transition_iff_rawTransitionCase] at hrightMem
    cases hrightMem
    case canonical rightEndpoint rightSlot rightCode =>
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      have hinj := CoreState.dispatch.inj hcore
      have hendpoints : endpoint = rightEndpoint := hinj.1
      have hrotated : rotateSlot leftSlot = rotateSlot rightSlot := by
        exact hinj.2
      subst rightEndpoint
      have hslots : leftSlot = rightSlot := by
        exact (FunctionalGraphReversibleTraversal.cyclicPerm
          (Slot T Gamma Q)).injective hrotated
      subst rightSlot
      have hleftPhaseEq := congrArg (fun cfg => cfg.state.phase) hleftTarget
      have hrightPhaseEq := congrArg (fun cfg => cfg.state.phase) hrightTarget
      simp only [nextState] at hleftPhaseEq hrightPhaseEq
      have hphases : leftPhase = rightPhase := by
        simpa using hleftPhaseEq.symm.trans hrightPhaseEq
      subst rightPhase
      have hleftTapeEq := congrArg (fun cfg => cfg.tape) hleftTarget
      have hrightTapeEq := congrArg (fun cfg => cfg.tape) hrightTarget
      have hleftTape : leftTape = tape := by
        rw [moveHead_stay] at hleftTapeEq
        rw [← hleftRead, write_read] at hleftTapeEq
        exact hleftTapeEq.symm
      have hrightTape : rightTape = tape := by
        rw [moveHead_stay] at hrightTapeEq
        rw [← hrightRead, write_read] at hrightTapeEq
        exact hrightTapeEq.symm
      rw [hleftTape, hrightTape]
    all_goals
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      cases hcore

public theorem encard_predecessors_dispatch_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (endpoint : LiftState T Gamma Q)
    (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .dispatch endpoint slot⟩, tape⟩} ≤ 2 := by
  apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
  intro left right hleft hright
  exact predecessor_dispatch_eq machine hleft hright

/-- The stationary outgoing tag records the whole edge, while the edge's old
field recovers the overwritten dispatch symbol. -/
public theorem predecessor_stationaryOutgoingPending_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .stationaryOutgoingPending edge⟩, tape⟩) :
    predecessor =
      ⟨⟨!targetPhase, .dispatch edge.source .outgoing⟩,
        tape.write (encodePlain edge.old)⟩ := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next endpoint target code old written htransition =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    have hold : old = code := by
      simpa using old_eq_of_walker_transition machine htransition
    subst code
    rw [moveHead_stay] at htape
    change tape = sourceTape.write
      (encodeWork (.stationaryOutgoing
        { source := endpoint, target := target,
          direction := .stationary old written })) at htape
    have hsourceTape : sourceTape = tape.write (encodePlain old) := by
      rw [htape]
      rw [← hread]
      exact (write_write_read sourceTape
        (encodeWork (.stationaryOutgoing
          { source := endpoint, target := target,
            direction := .stationary old written }))).symm
    simpa [Edge.old] using hsourceTape

public theorem encard_predecessors_stationaryOutgoingPending_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .stationaryOutgoingPending edge⟩, tape⟩} ≤ 2 := by
  apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
  intro left right hleft hright
  rw [predecessor_stationaryOutgoingPending_eq machine hleft,
    predecessor_stationaryOutgoingPending_eq machine hright]

/-- The stationary incoming tag likewise has a unique dispatch predecessor. -/
public theorem predecessor_stationaryIncomingPending_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .stationaryIncomingPending edge⟩, tape⟩) :
    predecessor =
      ⟨⟨!targetPhase, .dispatch edge.target (.incoming edge.source)⟩,
        tape.write (encodePlain edge.written)⟩ := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next endpoint source code old written hdirection hcode henabled =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    subst code
    rw [moveHead_stay] at htape
    change tape = sourceTape.write
      (encodeWork (.stationaryIncoming
        (Edge.ofIncoming endpoint source))) at htape
    have hsourceTape : sourceTape = tape.write (encodePlain written) := by
      rw [htape]
      rw [← hread]
      exact (write_write_read sourceTape
        (encodeWork (.stationaryIncoming
          (Edge.ofIncoming endpoint source)))).symm
    have hedgeWritten : (Edge.ofIncoming endpoint source).written = written := by
      rw [Edge.written, hdirection]
    rw [hedgeWritten]
    simpa [Edge.ofIncoming] using hsourceTape

public theorem encard_predecessors_stationaryIncomingPending_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .stationaryIncomingPending edge⟩, tape⟩} ≤ 2 := by
  apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
  intro left right hleft hright
  rw [predecessor_stationaryIncomingPending_eq machine hleft,
    predecessor_stationaryIncomingPending_eq machine hright]

/-! ## Moving-phase predecessor inversion -/

/-- The first outgoing landing has the two inverse candidates of its saved
departure.  The marked-controller old-field invariant fixes the erased plain
symbol even on a malformed tape. -/
public theorem predecessor_outgoingAtNeighbour_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .outgoingAtNeighbour edge⟩, tape⟩) :
    predecessor =
        ⟨⟨!targetPhase, .dispatch edge.source .outgoing⟩,
          tape.write (encodePlain edge.old)⟩ ∨
      ∃ old written travel,
        edge.direction = .departure old written travel ∧
        predecessor =
          ⟨⟨!targetPhase, .dispatch edge.source .outgoing⟩,
            (tape.moveHead travel.reverse.toDir).write
              (encodePlain edge.old)⟩ := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next endpoint target code old written travel htransition hallows =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    have hold : old = code := by
      simpa using old_eq_of_walker_transition machine htransition
    subst code
    have hcandidates := LBA.tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (encodePlain old)
        (encodeWork (.outgoingDeparture
          { source := endpoint, target := target,
            direction := .departure old written travel }))
        travel.toDir hread htape.symm
    rcases hcandidates with hfirst | hsecond
    · exact Or.inl (by simpa [Edge.old] using hfirst)
    · exact Or.inr ⟨old, written, travel, rfl, by
        simpa [Edge.old] using hsecond⟩

public theorem encard_predecessors_outgoingAtNeighbour_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .outgoingAtNeighbour edge⟩, tape⟩} ≤ 2 := by
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .dispatch edge.source .outgoing⟩,
      tape.write (encodePlain edge.old)⟩
  let second (travel : BoundedTapeMemory.Travel) :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .dispatch edge.source .outgoing⟩,
      (tape.moveHead travel.reverse.toDir).write (encodePlain edge.old)⟩
  exact encard_relation_le_two_of_fixed_or_direction
    (fun predecessor => LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .outgoingAtNeighbour edge⟩, tape⟩)
    edge.direction first second (by
      intro predecessor hpredecessor
      exact predecessor_outgoingAtNeighbour_eq_or_eq machine hpredecessor)

/-- An incoming dispatch moves in the reverse saved direction, so an
`incomingInspect` predecessor head is either clamped at the landing head or
is the unique forward neighbour. -/
public theorem predecessor_incomingInspect_head_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {old written : PlainCode T Gamma} {travel : BoundedTapeMemory.Travel}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hdirection : edge.direction = .departure old written travel)
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingInspect edge⟩, tape⟩) :
    predecessor.tape.head = tape.head ∨
      predecessor.tape.head = (tape.moveHead travel.toDir).head := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next endpoint source code sourceOld sourceWritten sourceTravel
      hsourceDirection hallows =>
    have hparameters : sourceOld = old ∧ sourceWritten = written ∧
        sourceTravel = travel := by
      simpa using hsourceDirection.symm.trans hdirection
    rcases hparameters with ⟨rfl, rfl, rfl⟩
    have htape := congrArg (fun cfg => cfg.tape) htarget
    rcases LBA.moveHead_eq_implies_eq_or_reverseDirection
        (sourceTape.write (encodeWork
          (.incomingTarget (Edge.ofIncoming endpoint source) code)))
        tape sourceTravel.reverse.toDir htape.symm with hsame | hreverse
    · exact Or.inl (congrArg (fun source => source.head) hsame)
    · right
      have hhead := congrArg (fun source => source.head) hreverse
      cases sourceTravel <;> exact hhead

/-- At a fixed physical head the incoming-dispatch landing is injective: the
private tag in the common target recovers the erased plain candidate. -/
public theorem predecessor_incomingInspect_eq_of_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .incomingInspect edge⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .incomingInspect edge⟩, tape⟩)
    (hhead : left.tape.head = right.tape.head) : left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases hleft with ⟨leftNext, leftOutput, leftDirection, hleftMem,
    hleftTarget⟩
  generalize hleftRead : leftTape.read = leftRead at hleftMem
  change (leftNext, leftOutput, leftDirection) ∈
    transition machine ⟨leftPhase, leftCore⟩ leftRead at hleftMem
  rw [mem_transition_iff_rawTransitionCase] at hleftMem
  cases hleftMem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) hleftTarget
    simp only [nextState] at hcore
    cases hcore
  next endpoint source leftCode old written travel hleftDirection hallows =>
    rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
    rcases hright with ⟨rightNext, rightOutput, rightDirection, hrightMem,
      hrightTarget⟩
    generalize hrightRead : rightTape.read = rightRead at hrightMem
    change (rightNext, rightOutput, rightDirection) ∈
      transition machine ⟨rightPhase, rightCore⟩ rightRead at hrightMem
    rw [mem_transition_iff_rawTransitionCase] at hrightMem
    cases hrightMem
    all_goals
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      cases hcore
    next rightEndpoint rightSource rightCode rightOld rightWritten rightTravel
        hrightDirection hrightAllows =>
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hleftDirection.symm.trans hrightAllows
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hleftPhaseEq := congrArg (fun cfg => cfg.state.phase) hleftTarget
      have hrightPhaseEq := congrArg (fun cfg => cfg.state.phase) hrightTarget
      simp only [nextState] at hleftPhaseEq hrightPhaseEq
      have hphases : leftPhase = rightPhase := by
        simpa using hleftPhaseEq.symm.trans hrightPhaseEq
      subst rightPhase
      have hleftTapeEq := congrArg (fun cfg => cfg.tape) hleftTarget
      have hrightTapeEq := congrArg (fun cfg => cfg.tape) hrightTarget
      have hwritten := written_eq_of_write_move_eq_of_head_eq
        leftTape rightTape tape
          (encodeWork (.incomingTarget (Edge.ofIncoming endpoint source)
            leftCode))
          (encodeWork (.incomingTarget (Edge.ofIncoming endpoint source)
            rightCode))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead
      have hcodes : leftCode = rightCode := by
        simpa using encodeWork_injective hwritten
      subst rightCode
      have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape
          (encodeWork (.incomingTarget (Edge.ofIncoming endpoint source)
            leftCode))
          (encodeWork (.incomingTarget (Edge.ofIncoming endpoint source)
            leftCode))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead (by
            rw [hleftRead, hrightRead])
      rw [htapes]

public theorem encard_predecessors_incomingInspect_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .incomingInspect edge⟩, tape⟩} ≤ 2 := by
  cases hdirection : edge.direction with
  | stationary old written =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
      rcases hleft with ⟨next, output, direction, hmem, htarget⟩
      generalize hread : leftTape.read = read at hmem
      change (next, output, direction) ∈
        transition machine ⟨leftPhase, leftCore⟩ read at hmem
      rw [mem_transition_iff_rawTransitionCase] at hmem
      cases hmem
      all_goals
        have hcore := congrArg (fun cfg => cfg.state.core) htarget
        simp only [nextState] at hcore
        cases hcore
      next endpoint source code sourceOld sourceWritten travel
          hsourceDirection hallows =>
        rw [hdirection] at hsourceDirection
        cases hsourceDirection
  | arrival old written travel =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
      rcases hleft with ⟨next, output, direction, hmem, htarget⟩
      generalize hread : leftTape.read = read at hmem
      change (next, output, direction) ∈
        transition machine ⟨leftPhase, leftCore⟩ read at hmem
      rw [mem_transition_iff_rawTransitionCase] at hmem
      cases hmem
      all_goals
        have hcore := congrArg (fun cfg => cfg.state.core) htarget
        simp only [nextState] at hcore
        cases hcore
      next endpoint source code sourceOld sourceWritten sourceTravel
          hsourceDirection hallows =>
        rw [hdirection] at hsourceDirection
        cases hsourceDirection
  | departure old written travel =>
      exact encard_predecessors_le_two_of_heads
        (fun predecessor => LBA.Step (rawMachine machine) predecessor
          ⟨⟨targetPhase, .incomingInspect edge⟩, tape⟩)
        (fun predecessor => predecessor.tape.head) tape.head
          (tape.moveHead travel.toDir).head
        (fun predecessor hpredecessor =>
          predecessor_incomingInspect_head_eq_or_eq machine hdirection
            hpredecessor)
        (fun left right hleft hright hhead =>
          predecessor_incomingInspect_eq_of_head_eq machine hleft hright hhead)

/-- The return from an inspected neighbour has the same clamped/genuine
head dichotomy. -/
public theorem predecessor_outgoingAtDeparture_head_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {old written : PlainCode T Gamma} {travel : BoundedTapeMemory.Travel}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hdirection : edge.direction = .departure old written travel)
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .outgoingAtDeparture edge⟩, tape⟩) :
    predecessor.tape.head = tape.head ∨
      predecessor.tape.head = (tape.moveHead travel.toDir).head := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next edge' sourceOld sourceWritten neighbour sourceTravel
      hsourceDirection hallows =>
    have hparameters : sourceOld = old ∧ sourceWritten = written ∧
        sourceTravel = travel := by
      simpa using hallows.symm.trans hdirection
    rcases hparameters with ⟨rfl, rfl, rfl⟩
    have htape := congrArg (fun cfg => cfg.tape) htarget
    rcases LBA.moveHead_eq_implies_eq_or_reverseDirection
        (sourceTape.write (encodeWork (.outgoingNeighbour edge neighbour)))
        tape sourceTravel.reverse.toDir htape.symm with hsame | hreverse
    · exact Or.inl (congrArg (fun source => source.head) hsame)
    · right
      have hhead := congrArg (fun source => source.head) hreverse
      cases sourceTravel <;> exact hhead

public theorem predecessor_outgoingAtDeparture_eq_of_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .outgoingAtDeparture edge⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .outgoingAtDeparture edge⟩, tape⟩)
    (hhead : left.tape.head = right.tape.head) : left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases hleft with ⟨leftNext, leftOutput, leftDirection, hleftMem,
    hleftTarget⟩
  generalize hleftRead : leftTape.read = leftRead at hleftMem
  change (leftNext, leftOutput, leftDirection) ∈
    transition machine ⟨leftPhase, leftCore⟩ leftRead at hleftMem
  rw [mem_transition_iff_rawTransitionCase] at hleftMem
  cases hleftMem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) hleftTarget
    simp only [nextState] at hcore
    cases hcore
  next edge' old written leftNeighbour travel hleftDirection hleftAllows =>
    rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
    rcases hright with ⟨rightNext, rightOutput, rightDirection, hrightMem,
      hrightTarget⟩
    generalize hrightRead : rightTape.read = rightRead at hrightMem
    change (rightNext, rightOutput, rightDirection) ∈
      transition machine ⟨rightPhase, rightCore⟩ rightRead at hrightMem
    rw [mem_transition_iff_rawTransitionCase] at hrightMem
    cases hrightMem
    all_goals
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      cases hcore
    next edge'' rightOld rightWritten rightNeighbour rightTravel
        hrightDirection hrightAllows =>
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hleftAllows.symm.trans hrightAllows
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hleftPhaseEq := congrArg (fun cfg => cfg.state.phase) hleftTarget
      have hrightPhaseEq := congrArg (fun cfg => cfg.state.phase) hrightTarget
      simp only [nextState] at hleftPhaseEq hrightPhaseEq
      have hphases : leftPhase = rightPhase := by
        simpa using hleftPhaseEq.symm.trans hrightPhaseEq
      subst rightPhase
      have hleftTapeEq := congrArg (fun cfg => cfg.tape) hleftTarget
      have hrightTapeEq := congrArg (fun cfg => cfg.tape) hrightTarget
      have hwritten := written_eq_of_write_move_eq_of_head_eq
        leftTape rightTape tape
          (encodeWork (.outgoingNeighbour edge leftNeighbour))
          (encodeWork (.outgoingNeighbour edge rightNeighbour))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead
      have hneighbours : leftNeighbour = rightNeighbour := by
        simpa using encodeWork_injective hwritten
      subst rightNeighbour
      have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape
          (encodeWork (.outgoingNeighbour edge leftNeighbour))
          (encodeWork (.outgoingNeighbour edge leftNeighbour))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead (by
            rw [hleftRead, hrightRead])
      rw [htapes]

public theorem encard_predecessors_outgoingAtDeparture_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .outgoingAtDeparture edge⟩, tape⟩} ≤ 2 := by
  cases hdirection : edge.direction with
  | stationary old written =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
      rcases hleft with ⟨next, output, direction, hmem, htarget⟩
      generalize hread : leftTape.read = read at hmem
      change (next, output, direction) ∈
        transition machine ⟨leftPhase, leftCore⟩ read at hmem
      rw [mem_transition_iff_rawTransitionCase] at hmem
      cases hmem
      all_goals
        have hcore := congrArg (fun cfg => cfg.state.core) htarget
        simp only [nextState] at hcore
        cases hcore
      next edge' sourceOld sourceWritten neighbour travel
          hsourceDirection hallows =>
        rw [hdirection] at hallows
        cases hallows
  | arrival old written travel =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
      rcases hleft with ⟨next, output, direction, hmem, htarget⟩
      generalize hread : leftTape.read = read at hmem
      change (next, output, direction) ∈
        transition machine ⟨leftPhase, leftCore⟩ read at hmem
      rw [mem_transition_iff_rawTransitionCase] at hmem
      cases hmem
      all_goals
        have hcore := congrArg (fun cfg => cfg.state.core) htarget
        simp only [nextState] at hcore
        cases hcore
      next edge' sourceOld sourceWritten neighbour sourceTravel
          hsourceDirection hallows =>
        rw [hdirection] at hallows
        cases hallows
  | departure old written travel =>
      exact encard_predecessors_le_two_of_heads
        (fun predecessor => LBA.Step (rawMachine machine) predecessor
          ⟨⟨targetPhase, .outgoingAtDeparture edge⟩, tape⟩)
        (fun predecessor => predecessor.tape.head) tape.head
          (tape.moveHead travel.toDir).head
        (fun predecessor hpredecessor =>
          predecessor_outgoingAtDeparture_head_eq_or_eq machine hdirection
            hpredecessor)
        (fun left right hleft hright hhead =>
          predecessor_outgoingAtDeparture_eq_of_head_eq machine
            hleft hright hhead)

/-- An `outgoingRestoreNeighbour` landing has only the stationary clamped
inverse and the genuine reverse-neighbour inverse. -/
public theorem predecessor_outgoingRestoreNeighbour_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .outgoingRestoreNeighbour edge⟩, tape⟩) :
    predecessor =
        ⟨⟨!targetPhase, .outgoingAtDeparture edge⟩,
          tape.write (encodeWork (.outgoingDeparture edge))⟩ ∨
      ∃ old written travel,
        edge.direction = .departure old written travel ∧
        predecessor =
          ⟨⟨!targetPhase, .outgoingAtDeparture edge⟩,
            (tape.moveHead travel.reverse.toDir).write
              (encodeWork (.outgoingDeparture edge))⟩ := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next edge' old written travel hdirection henabled =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    have hcandidates := LBA.tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (encodeWork (.outgoingDeparture edge))
        (encodePlain written) travel.toDir hread htape.symm
    rcases hcandidates with hfirst | hsecond
    · exact Or.inl (by rw [hfirst])
    · exact Or.inr ⟨old, written, travel, hdirection, by
        rw [hsecond]
        cases travel <;> rfl⟩

/-- The `outgoingRestoreNeighbour` fibre has raw indegree at most two for
every width, including width zero. -/
public theorem encard_predecessors_outgoingRestoreNeighbour_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .outgoingRestoreNeighbour edge⟩, tape⟩} ≤ 2 := by
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .outgoingAtDeparture edge⟩,
      tape.write (encodeWork (.outgoingDeparture edge))⟩
  cases hdirection : edge.direction with
  | stationary old written =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases predecessor_outgoingRestoreNeighbour_eq_or_eq machine hleft with
        rfl | ⟨leftOld, leftWritten, leftTravel, hleftDirection, hleft⟩
      · rcases predecessor_outgoingRestoreNeighbour_eq_or_eq machine hright with
          rfl | ⟨rightOld, rightWritten, rightTravel, hrightDirection, hright⟩
        · rfl
        · rw [hdirection] at hrightDirection
          contradiction
      · rw [hdirection] at hleftDirection
        contradiction
  | arrival old written travel =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases predecessor_outgoingRestoreNeighbour_eq_or_eq machine hleft with
        rfl | ⟨leftOld, leftWritten, leftTravel, hleftDirection, hleft⟩
      · rcases predecessor_outgoingRestoreNeighbour_eq_or_eq machine hright with
          rfl | ⟨rightOld, rightWritten, rightTravel, hrightDirection, hright⟩
        · rfl
        · rw [hdirection] at hrightDirection
          contradiction
      · rw [hdirection] at hleftDirection
        contradiction
  | departure old written travel =>
      let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!targetPhase, .outgoingAtDeparture edge⟩,
          (tape.moveHead travel.reverse.toDir).write
            (encodeWork (.outgoingDeparture edge))⟩
      calc
        Set.encard {predecessor |
            LBA.Step (rawMachine machine) predecessor
              ⟨⟨targetPhase, .outgoingRestoreNeighbour edge⟩, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro predecessor hpredecessor
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          rcases predecessor_outgoingRestoreNeighbour_eq_or_eq machine
              hpredecessor with hfirst | ⟨leftOld, leftWritten, leftTravel,
                hleftDirection, hsecond⟩
          · exact Or.inl hfirst
          · rw [hdirection] at hleftDirection
            rcases hleftDirection with ⟨rfl, rfl, rfl⟩
            exact Or.inr hsecond
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl

/-- Complete head inversion for the validation landing. -/
public theorem predecessor_outgoingValidateAtDeparture_departure_and_heads
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .outgoingValidateAtDeparture edge⟩, tape⟩) :
    ∃ old written travel,
      edge.direction = .departure old written travel ∧
      (predecessor.tape.head = tape.head ∨
        predecessor.tape.head = (tape.moveHead travel.toDir).head) := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next instQ old written neighbour travel hfirstGuard hsecondGuard hthirdGuard =>
    have hdirection : edge.direction = .departure old written travel := by
      assumption
    refine ⟨old, written, travel, hdirection, ?_⟩
    have htape := congrArg (fun cfg => cfg.tape) htarget
    rcases LBA.moveHead_eq_implies_eq_or_reverseDirection
        (sourceTape.write (encodeWork (.incomingTarget edge neighbour)))
        tape travel.reverse.toDir htape.symm with hsame | hreverse
    · exact Or.inl (congrArg (fun source => source.head) hsame)
    · right
      have hhead := congrArg (fun source => source.head) hreverse
      cases travel <;> exact hhead

public theorem predecessor_outgoingValidateAtDeparture_eq_of_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .outgoingValidateAtDeparture edge⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .outgoingValidateAtDeparture edge⟩, tape⟩)
    (hhead : left.tape.head = right.tape.head) : left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases hleft with ⟨leftNext, leftOutput, leftDirection, hleftMem,
    hleftTarget⟩
  generalize hleftRead : leftTape.read = leftRead at hleftMem
  change (leftNext, leftOutput, leftDirection) ∈
    transition machine ⟨leftPhase, leftCore⟩ leftRead at hleftMem
  rw [mem_transition_iff_rawTransitionCase] at hleftMem
  cases hleftMem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) hleftTarget
    simp only [nextState] at hcore
    cases hcore
  next instQ old written leftNeighbour travel hleftGuard1 hleftGuard2
      hleftGuard3 =>
    have hleftDirection : edge.direction = .departure old written travel := by
      assumption
    rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
    rcases hright with ⟨rightNext, rightOutput, rightDirection, hrightMem,
      hrightTarget⟩
    generalize hrightRead : rightTape.read = rightRead at hrightMem
    change (rightNext, rightOutput, rightDirection) ∈
      transition machine ⟨rightPhase, rightCore⟩ rightRead at hrightMem
    rw [mem_transition_iff_rawTransitionCase] at hrightMem
    cases hrightMem
    all_goals
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      cases hcore
    next instQ' rightOld rightWritten rightNeighbour rightTravel
        hrightGuard1 hrightGuard2 hrightGuard3 =>
      have hrightDirection : edge.direction =
          .departure rightOld rightWritten rightTravel := by
        assumption
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hleftDirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hleftPhaseEq := congrArg (fun cfg => cfg.state.phase) hleftTarget
      have hrightPhaseEq := congrArg (fun cfg => cfg.state.phase) hrightTarget
      simp only [nextState] at hleftPhaseEq hrightPhaseEq
      have hphases : leftPhase = rightPhase := by
        simpa using hleftPhaseEq.symm.trans hrightPhaseEq
      subst rightPhase
      have hleftTapeEq := congrArg (fun cfg => cfg.tape) hleftTarget
      have hrightTapeEq := congrArg (fun cfg => cfg.tape) hrightTarget
      have hwritten := written_eq_of_write_move_eq_of_head_eq
        leftTape rightTape tape
          (encodeWork (.incomingTarget edge leftNeighbour))
          (encodeWork (.incomingTarget edge rightNeighbour))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead
      have hneighbours : leftNeighbour = rightNeighbour := by
        simpa using encodeWork_injective hwritten
      subst rightNeighbour
      have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape
          (encodeWork (.incomingTarget edge leftNeighbour))
          (encodeWork (.incomingTarget edge leftNeighbour))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead (by
            rw [hleftRead, hrightRead])
      rw [htapes]

public theorem encard_predecessors_outgoingValidateAtDeparture_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .outgoingValidateAtDeparture edge⟩, tape⟩} ≤ 2 := by
  exact encard_relation_le_two_of_departure_heads
    (fun predecessor => LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .outgoingValidateAtDeparture edge⟩, tape⟩)
    edge.direction (fun predecessor => predecessor.tape.head) tape.head
      (fun travel => (tape.moveHead travel.toDir).head)
    (fun predecessor hpredecessor => by
      rcases predecessor_outgoingValidateAtDeparture_departure_and_heads
          machine hpredecessor with ⟨old, written, travel, hdirection, _⟩
      exact ⟨old, written, travel, hdirection⟩)
    (fun predecessor hpredecessor old written travel hdirection => by
      rcases predecessor_outgoingValidateAtDeparture_departure_and_heads
          machine hpredecessor with
        ⟨sourceOld, sourceWritten, sourceTravel, hsourceDirection, hheads⟩
      have hparameters : sourceOld = old ∧ sourceWritten = written ∧
          sourceTravel = travel := by
        simpa using hsourceDirection.symm.trans hdirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      exact hheads)
    (fun left right hleft hright hhead =>
      predecessor_outgoingValidateAtDeparture_eq_of_head_eq machine
        hleft hright hhead)

/-- An `incomingValidAtTarget` landing has the same two inverse head
candidates.  Its saved edge fixes both the scanned predecessor symbol and the
tag written before moving. -/
public theorem predecessor_incomingValidAtTarget_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingValidAtTarget edge⟩, tape⟩) :
    predecessor =
        ⟨⟨!targetPhase, .incomingInspect edge⟩,
          tape.write (encodePlain edge.written)⟩ ∨
      ∃ old written travel,
        edge.direction = .departure old written travel ∧
        predecessor =
          ⟨⟨!targetPhase, .incomingInspect edge⟩,
            (tape.moveHead travel.reverse.toDir).write
              (encodePlain edge.written)⟩ := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next edge' old written candidate travel hdirection hvalid =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    have hcandidate : candidate = edge.written := by
      simpa [Edge.written, hdirection] using hvalid.1
    subst candidate
    have hcandidates := LBA.tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (encodePlain edge.written)
        (encodeWork (.incomingSource edge)) travel.toDir hread htape.symm
    rcases hcandidates with hfirst | hsecond
    · exact Or.inl (by rw [hfirst])
    · exact Or.inr ⟨old, written, travel, hdirection, by
        rw [hsecond]
        cases travel <;> rfl⟩

public theorem encard_predecessors_incomingValidAtTarget_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .incomingValidAtTarget edge⟩, tape⟩} ≤ 2 := by
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .incomingInspect edge⟩,
      tape.write (encodePlain edge.written)⟩
  let second (travel : BoundedTapeMemory.Travel) :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .incomingInspect edge⟩,
      (tape.moveHead travel.reverse.toDir).write
        (encodePlain edge.written)⟩
  exact encard_relation_le_two_of_fixed_or_direction
    (fun predecessor => LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingValidAtTarget edge⟩, tape⟩)
    edge.direction first second (by
      intro predecessor hpredecessor
      exact predecessor_incomingValidAtTarget_eq_or_eq machine hpredecessor)

/-- Complete head inversion for the valid branch's return to its source. -/
public theorem predecessor_incomingValidFinish_departure_and_heads
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingValidFinish edge⟩, tape⟩) :
    ∃ old written travel,
      edge.direction = .departure old written travel ∧
      (predecessor.tape.head = tape.head ∨
        predecessor.tape.head = (tape.moveHead travel.toDir).head) := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next instQ old written neighbour travel hguard1 hguard2 =>
    have hdirection : edge.direction = .departure old written travel := by
      assumption
    refine ⟨old, written, travel, hdirection, ?_⟩
    have htape := congrArg (fun cfg => cfg.tape) htarget
    rcases LBA.moveHead_eq_implies_eq_or_reverseDirection
        (sourceTape.write (encodePlain neighbour)) tape
        travel.reverse.toDir htape.symm with hsame | hreverse
    · exact Or.inl (congrArg (fun source => source.head) hsame)
    · right
      have hhead := congrArg (fun source => source.head) hreverse
      cases travel <;> exact hhead

public theorem predecessor_incomingValidFinish_eq_of_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .incomingValidFinish edge⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .incomingValidFinish edge⟩, tape⟩)
    (hhead : left.tape.head = right.tape.head) : left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases hleft with ⟨leftNext, leftOutput, leftDirection, hleftMem,
    hleftTarget⟩
  generalize hleftRead : leftTape.read = leftRead at hleftMem
  change (leftNext, leftOutput, leftDirection) ∈
    transition machine ⟨leftPhase, leftCore⟩ leftRead at hleftMem
  rw [mem_transition_iff_rawTransitionCase] at hleftMem
  cases hleftMem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) hleftTarget
    simp only [nextState] at hcore
    cases hcore
  next instQ old written leftNeighbour travel hleftGuard1 hleftGuard2 =>
    have hleftDirection : edge.direction = .departure old written travel := by
      assumption
    rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
    rcases hright with ⟨rightNext, rightOutput, rightDirection, hrightMem,
      hrightTarget⟩
    generalize hrightRead : rightTape.read = rightRead at hrightMem
    change (rightNext, rightOutput, rightDirection) ∈
      transition machine ⟨rightPhase, rightCore⟩ rightRead at hrightMem
    rw [mem_transition_iff_rawTransitionCase] at hrightMem
    cases hrightMem
    all_goals
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      cases hcore
    next instQ' rightOld rightWritten rightNeighbour rightTravel
        hrightGuard1 hrightGuard2 =>
      have hrightDirection : edge.direction =
          .departure rightOld rightWritten rightTravel := by
        assumption
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hleftDirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hleftPhaseEq := congrArg (fun cfg => cfg.state.phase) hleftTarget
      have hrightPhaseEq := congrArg (fun cfg => cfg.state.phase) hrightTarget
      simp only [nextState] at hleftPhaseEq hrightPhaseEq
      have hphases : leftPhase = rightPhase := by
        simpa using hleftPhaseEq.symm.trans hrightPhaseEq
      subst rightPhase
      have hleftTapeEq := congrArg (fun cfg => cfg.tape) hleftTarget
      have hrightTapeEq := congrArg (fun cfg => cfg.tape) hrightTarget
      have hwritten := written_eq_of_write_move_eq_of_head_eq
        leftTape rightTape tape (encodePlain leftNeighbour)
          (encodePlain rightNeighbour) travel.reverse.toDir
          travel.reverse.toDir hleftTapeEq.symm hrightTapeEq.symm hhead
      have hneighbours : leftNeighbour = rightNeighbour :=
        encodePlain_injective hwritten
      subst rightNeighbour
      have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape (encodePlain leftNeighbour)
          (encodePlain leftNeighbour) travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead (by
            rw [hleftRead, hrightRead])
      rw [htapes]

public theorem encard_predecessors_incomingValidFinish_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .incomingValidFinish edge⟩, tape⟩} ≤ 2 := by
  exact encard_relation_le_two_of_departure_heads
    (fun predecessor => LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingValidFinish edge⟩, tape⟩)
    edge.direction (fun predecessor => predecessor.tape.head) tape.head
      (fun travel => (tape.moveHead travel.toDir).head)
    (fun predecessor hpredecessor => by
      rcases predecessor_incomingValidFinish_departure_and_heads machine
          hpredecessor with ⟨old, written, travel, hdirection, _⟩
      exact ⟨old, written, travel, hdirection⟩)
    (fun predecessor hpredecessor old written travel hdirection => by
      rcases predecessor_incomingValidFinish_departure_and_heads machine
          hpredecessor with
        ⟨sourceOld, sourceWritten, sourceTravel, hsourceDirection, hheads⟩
      have hparameters : sourceOld = old ∧ sourceWritten = written ∧
          sourceTravel = travel := by
        simpa using hsourceDirection.symm.trans hdirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      exact hheads)
    (fun left right hleft hright hhead =>
      predecessor_incomingValidFinish_eq_of_head_eq machine
        hleft hright hhead)

/-- The invalid branch retains its candidate in both control and the written
tag, so its first moving landing also has exactly the standard two inverse
head candidates. -/
public theorem predecessor_incomingInvalidAtTarget_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {candidate : PlainCode T Gamma}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingInvalidAtTarget edge candidate⟩, tape⟩) :
    predecessor =
        ⟨⟨!targetPhase, .incomingInspect edge⟩,
          tape.write (encodePlain candidate)⟩ ∨
      ∃ old written travel,
        edge.direction = .departure old written travel ∧
        predecessor =
          ⟨⟨!targetPhase, .incomingInspect edge⟩,
            (tape.moveHead travel.reverse.toDir).write
              (encodePlain candidate)⟩ := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  case incomingInspectInvalid instGamma instQ old written travel hdirection hinvalid =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    have hcandidates := LBA.tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (encodePlain candidate)
        (encodeWork (.incomingInvalidSource edge candidate)) travel.toDir
          hread htape.symm
    rcases hcandidates with hfirst | hsecond
    · exact Or.inl (by rw [hfirst])
    · exact Or.inr ⟨old, written, travel, hdirection, by
        rw [hsecond]
        cases travel <;> rfl⟩

public theorem encard_predecessors_incomingInvalidAtTarget_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (candidate : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .incomingInvalidAtTarget edge candidate⟩, tape⟩} ≤ 2 := by
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .incomingInspect edge⟩,
      tape.write (encodePlain candidate)⟩
  let second (travel : BoundedTapeMemory.Travel) :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    ⟨⟨!targetPhase, .incomingInspect edge⟩,
      (tape.moveHead travel.reverse.toDir).write (encodePlain candidate)⟩
  exact encard_relation_le_two_of_fixed_or_direction
    (fun predecessor => LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingInvalidAtTarget edge candidate⟩, tape⟩)
    edge.direction first second (by
      intro predecessor hpredecessor
      exact predecessor_incomingInvalidAtTarget_eq_or_eq machine hpredecessor)

/-- Complete head inversion for the invalid branch's return to its source. -/
public theorem predecessor_incomingInvalidAtSource_departure_and_heads
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {candidate : PlainCode T Gamma}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingInvalidAtSource edge candidate⟩, tape⟩) :
    ∃ old written travel,
      edge.direction = .departure old written travel ∧
      (predecessor.tape.head = tape.head ∨
        predecessor.tape.head = (tape.moveHead travel.toDir).head) := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  next instGamma instQ neighbour old written travel hguard =>
    have hdirection : edge.direction = .departure old written travel := by
      assumption
    refine ⟨old, written, travel, hdirection, ?_⟩
    have htape := congrArg (fun cfg => cfg.tape) htarget
    rcases LBA.moveHead_eq_implies_eq_or_reverseDirection
        (sourceTape.write (encodeWork (.incomingTarget edge neighbour)))
        tape travel.reverse.toDir htape.symm with hsame | hreverse
    · exact Or.inl (congrArg (fun source => source.head) hsame)
    · right
      have hhead := congrArg (fun source => source.head) hreverse
      cases travel <;> exact hhead

public theorem predecessor_incomingInvalidAtSource_eq_of_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {candidate : PlainCode T Gamma}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .incomingInvalidAtSource edge candidate⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .incomingInvalidAtSource edge candidate⟩, tape⟩)
    (hhead : left.tape.head = right.tape.head) : left = right := by
  rcases left with ⟨⟨leftPhase, leftCore⟩, leftTape⟩
  rcases hleft with ⟨leftNext, leftOutput, leftDirection, hleftMem,
    hleftTarget⟩
  generalize hleftRead : leftTape.read = leftRead at hleftMem
  change (leftNext, leftOutput, leftDirection) ∈
    transition machine ⟨leftPhase, leftCore⟩ leftRead at hleftMem
  rw [mem_transition_iff_rawTransitionCase] at hleftMem
  cases hleftMem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) hleftTarget
    simp only [nextState] at hcore
    cases hcore
  next instGamma instQ leftNeighbour old written travel hleftGuard =>
    have hleftDirection : edge.direction = .departure old written travel := by
      assumption
    rcases right with ⟨⟨rightPhase, rightCore⟩, rightTape⟩
    rcases hright with ⟨rightNext, rightOutput, rightDirection, hrightMem,
      hrightTarget⟩
    generalize hrightRead : rightTape.read = rightRead at hrightMem
    change (rightNext, rightOutput, rightDirection) ∈
      transition machine ⟨rightPhase, rightCore⟩ rightRead at hrightMem
    rw [mem_transition_iff_rawTransitionCase] at hrightMem
    cases hrightMem
    all_goals
      have hcore := congrArg (fun cfg => cfg.state.core) hrightTarget
      simp only [nextState] at hcore
      cases hcore
    next instGamma' instQ' rightNeighbour rightOld rightWritten rightTravel
        hrightGuard =>
      have hrightDirection : edge.direction =
          .departure rightOld rightWritten rightTravel := by
        assumption
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hleftDirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hleftPhaseEq := congrArg (fun cfg => cfg.state.phase) hleftTarget
      have hrightPhaseEq := congrArg (fun cfg => cfg.state.phase) hrightTarget
      simp only [nextState] at hleftPhaseEq hrightPhaseEq
      have hphases : leftPhase = rightPhase := by
        simpa using hleftPhaseEq.symm.trans hrightPhaseEq
      subst rightPhase
      have hleftTapeEq := congrArg (fun cfg => cfg.tape) hleftTarget
      have hrightTapeEq := congrArg (fun cfg => cfg.tape) hrightTarget
      have hwritten := written_eq_of_write_move_eq_of_head_eq
        leftTape rightTape tape
          (encodeWork (.incomingTarget edge leftNeighbour))
          (encodeWork (.incomingTarget edge rightNeighbour))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead
      have hneighbours : leftNeighbour = rightNeighbour := by
        simpa using encodeWork_injective hwritten
      subst rightNeighbour
      have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape
          (encodeWork (.incomingTarget edge leftNeighbour))
          (encodeWork (.incomingTarget edge leftNeighbour))
          travel.reverse.toDir travel.reverse.toDir
          hleftTapeEq.symm hrightTapeEq.symm hhead (by
            rw [hleftRead, hrightRead])
      rw [htapes]

public theorem encard_predecessors_incomingInvalidAtSource_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (candidate : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .incomingInvalidAtSource edge candidate⟩, tape⟩} ≤ 2 := by
  exact encard_relation_le_two_of_departure_heads
    (fun predecessor => LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingInvalidAtSource edge candidate⟩, tape⟩)
    edge.direction (fun predecessor => predecessor.tape.head) tape.head
      (fun travel => (tape.moveHead travel.toDir).head)
    (fun predecessor hpredecessor => by
      rcases predecessor_incomingInvalidAtSource_departure_and_heads machine
          hpredecessor with ⟨old, written, travel, hdirection, _⟩
      exact ⟨old, written, travel, hdirection⟩)
    (fun predecessor hpredecessor old written travel hdirection => by
      rcases predecessor_incomingInvalidAtSource_departure_and_heads machine
          hpredecessor with
        ⟨sourceOld, sourceWritten, sourceTravel, hsourceDirection, hheads⟩
      have hparameters : sourceOld = old ∧ sourceWritten = written ∧
          sourceTravel = travel := by
        simpa using hsourceDirection.symm.trans hdirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      exact hheads)
    (fun left right hleft hright hhead =>
      predecessor_incomingInvalidAtSource_eq_of_head_eq machine
        hleft hright hhead)

/-! ## The shared return landing -/

/-- Exact two-family inversion for the shared return state.  Both families
write a plain candidate and move in the saved departure direction; their
validity predicates are complementary when the candidates agree. -/
public theorem predecessor_incomingReturnAtTarget_cases
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingReturnAtTarget edge⟩, tape⟩) :
    (∃ old written candidate travel sourceTape,
      edge.direction = .departure old written travel ∧
      (candidate = written ∧ edge.Enabled machine ∧
        candidate.boundary.allows travel = true) ∧
      predecessor =
        ⟨⟨!targetPhase, .outgoingValidateAtDeparture edge⟩, sourceTape⟩ ∧
      sourceTape.read = encodePlain candidate ∧
      tape = (sourceTape.write (encodePlain candidate)).moveHead travel.toDir) ∨
    (∃ candidate old written travel sourceTape,
      edge.direction = .departure old written travel ∧
      edge = Edge.ofIncoming edge.target edge.source ∧
      ¬(candidate = edge.written ∧ edge.Enabled machine ∧
        candidate.boundary.allows travel = true) ∧
      predecessor =
        ⟨⟨!targetPhase, .incomingInvalidAtSource edge candidate⟩, sourceTape⟩ ∧
      sourceTape.read = encodeWork (.incomingInvalidSource edge candidate) ∧
      tape = (sourceTape.write (encodePlain candidate)).moveHead travel.toDir) := by
  rcases predecessor with ⟨⟨sourcePhase, sourceCore⟩, sourceTape⟩
  rcases hstep with ⟨next, output, direction, hmem, htarget⟩
  generalize hread : sourceTape.read = read at hmem
  change (next, output, direction) ∈
    transition machine ⟨sourcePhase, sourceCore⟩ read at hmem
  rw [mem_transition_iff_rawTransitionCase] at hmem
  cases hmem
  all_goals
    have hcore := congrArg (fun cfg => cfg.state.core) htarget
    simp only [nextState] at hcore
    cases hcore
  case outgoingValidateAtDeparture edge' old written candidate travel
      hdirection hvalid =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    exact Or.inl ⟨old, written, candidate, travel, sourceTape,
      hdirection, hvalid, rfl, hread, htape⟩
  case incomingInvalidAtSource edge' candidate old written travel
      hdirection hwellformed hinvalid =>
    have hphase := congrArg (fun cfg => cfg.state.phase) htarget
    have htape := congrArg (fun cfg => cfg.tape) htarget
    simp only [nextState] at hphase
    have hsourcePhase : sourcePhase = !targetPhase := by
      simpa using (congrArg (fun phase => !phase) hphase).symm
    subst sourcePhase
    exact Or.inr ⟨candidate, old, written, travel, sourceTape,
      hdirection, hwellformed, hinvalid, rfl, hread, htape⟩

/-- At a fixed physical predecessor head, the two Return families are
jointly injective.  The cross-family cases are impossible because equality of
the post-step tape identifies the candidate, making the valid and invalid
guards contradictory. -/
public theorem predecessor_incomingReturnAtTarget_eq_of_head_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hleft : LBA.Step (rawMachine machine) left
      ⟨⟨targetPhase, .incomingReturnAtTarget edge⟩, tape⟩)
    (hright : LBA.Step (rawMachine machine) right
      ⟨⟨targetPhase, .incomingReturnAtTarget edge⟩, tape⟩)
    (hhead : left.tape.head = right.tape.head) : left = right := by
  rcases predecessor_incomingReturnAtTarget_cases machine hleft with
      ⟨leftOld, leftWritten, leftCandidate, leftTravel, leftTape,
        hleftDirection, hleftValid, rfl, hleftRead, hleftTape⟩ |
      ⟨leftCandidate, leftOld, leftWritten, leftTravel, leftTape,
        hleftDirection, hleftWellformed, hleftInvalid, rfl,
        hleftRead, hleftTape⟩
  · rcases predecessor_incomingReturnAtTarget_cases machine hright with
      ⟨rightOld, rightWritten, rightCandidate, rightTravel, rightTape,
        hrightDirection, hrightValid, rfl, hrightRead, hrightTape⟩ |
      ⟨rightCandidate, rightOld, rightWritten, rightTravel, rightTape,
        hrightDirection, hrightWellformed, hrightInvalid, rfl,
        hrightRead, hrightTape⟩
    · have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape (encodePlain leftCandidate)
          (encodePlain rightCandidate) leftTravel.toDir rightTravel.toDir
          hleftTape.symm hrightTape.symm hhead (by
            rw [hleftRead, hrightRead]
            have hwritten := written_eq_of_write_move_eq_of_head_eq
              leftTape rightTape tape (encodePlain leftCandidate)
                (encodePlain rightCandidate) leftTravel.toDir rightTravel.toDir
                hleftTape.symm hrightTape.symm hhead
            exact hwritten)
      rw [htapes]
    · have hparameters : leftOld = rightOld ∧
          leftWritten = rightWritten ∧ leftTravel = rightTravel := by
        simpa using hleftDirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hcandidates : leftCandidate = rightCandidate :=
        encodePlain_injective (written_eq_of_write_move_eq_of_head_eq
          leftTape rightTape tape (encodePlain leftCandidate)
            (encodePlain rightCandidate) leftTravel.toDir leftTravel.toDir
            hleftTape.symm hrightTape.symm hhead)
      subst rightCandidate
      have hcandidateWritten : leftCandidate = edge.written := by
        simpa [Edge.written, hleftDirection] using hleftValid.1
      exact False.elim (hrightInvalid
        ⟨hcandidateWritten, hleftValid.2.1, hleftValid.2.2⟩)
  · rcases predecessor_incomingReturnAtTarget_cases machine hright with
      ⟨rightOld, rightWritten, rightCandidate, rightTravel, rightTape,
        hrightDirection, hrightValid, rfl, hrightRead, hrightTape⟩ |
      ⟨rightCandidate, rightOld, rightWritten, rightTravel, rightTape,
        hrightDirection, hrightWellformed, hrightInvalid, rfl,
        hrightRead, hrightTape⟩
    · have hparameters : leftOld = rightOld ∧
          leftWritten = rightWritten ∧ leftTravel = rightTravel := by
        simpa using hleftDirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      have hcandidates : leftCandidate = rightCandidate :=
        encodePlain_injective (written_eq_of_write_move_eq_of_head_eq
          leftTape rightTape tape (encodePlain leftCandidate)
            (encodePlain rightCandidate) leftTravel.toDir leftTravel.toDir
            hleftTape.symm hrightTape.symm hhead)
      subst rightCandidate
      have hcandidateWritten : leftCandidate = edge.written := by
        simpa [Edge.written, hrightDirection] using hrightValid.1
      exact False.elim (hleftInvalid
        ⟨hcandidateWritten, hrightValid.2.1, hrightValid.2.2⟩)
    · have hcandidates : leftCandidate = rightCandidate :=
        encodePlain_injective (written_eq_of_write_move_eq_of_head_eq
          leftTape rightTape tape (encodePlain leftCandidate)
            (encodePlain rightCandidate) leftTravel.toDir rightTravel.toDir
            hleftTape.symm hrightTape.symm hhead)
      subst rightCandidate
      have htapes := tape_eq_of_write_move_eq_of_head_eq_of_read_eq
        leftTape rightTape tape (encodePlain leftCandidate)
          (encodePlain leftCandidate) leftTravel.toDir rightTravel.toDir
          hleftTape.symm hrightTape.symm hhead (by
            rw [hleftRead, hrightRead])
      rw [htapes]

/-- The source head of a Return predecessor is either the clamped target head
or the one reverse-neighbour head. -/
public theorem predecessor_incomingReturnAtTarget_head_eq_or_eq
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {predecessor : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    {targetPhase : Bool} {edge : Edge T Gamma Q}
    {old written : PlainCode T Gamma} {travel : BoundedTapeMemory.Travel}
    {tape : DLBA.BoundedTape (Alphabet T Gamma Q) n}
    (hdirection : edge.direction = .departure old written travel)
    (hstep : LBA.Step (rawMachine machine) predecessor
      ⟨⟨targetPhase, .incomingReturnAtTarget edge⟩, tape⟩) :
    predecessor.tape.head = tape.head ∨
      predecessor.tape.head = (tape.moveHead travel.reverse.toDir).head := by
  rcases predecessor_incomingReturnAtTarget_cases machine hstep with
      ⟨sourceOld, sourceWritten, candidate, sourceTravel, sourceTape,
        hsourceDirection, hvalid, rfl, hread, htape⟩ |
      ⟨candidate, sourceOld, sourceWritten, sourceTravel, sourceTape,
        hsourceDirection, hwellformed, hinvalid, rfl, hread, htape⟩
  all_goals
    have hparameters : sourceOld = old ∧ sourceWritten = written ∧
        sourceTravel = travel := by
      simpa using hsourceDirection.symm.trans hdirection
    rcases hparameters with ⟨rfl, rfl, rfl⟩
    rcases LBA.moveHead_eq_implies_eq_or_reverseDirection
        (sourceTape.write (encodePlain candidate)) tape sourceTravel.toDir
          htape.symm with hsame | hreverse
    · exact Or.inl (congrArg (fun source => source.head) hsame)
    · right
      have hhead := congrArg (fun source => source.head) hreverse
      cases sourceTravel <;> exact hhead

/-- The redesigned shared Return fibre has indegree at most two on every raw
tape and every width. -/
public theorem encard_predecessors_incomingReturnAtTarget_le_two
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    (targetPhase : Bool) (edge : Edge T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Set.encard {predecessor |
      LBA.Step (rawMachine machine) predecessor
        ⟨⟨targetPhase, .incomingReturnAtTarget edge⟩, tape⟩} ≤ 2 := by
  cases hdirection : edge.direction with
  | stationary old written =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases predecessor_incomingReturnAtTarget_cases machine hleft with
          ⟨_, _, _, _, _, hleftDirection, _⟩ |
          ⟨_, _, _, _, _, hleftDirection, _⟩
      all_goals rw [hdirection] at hleftDirection
      all_goals cases hleftDirection
  | arrival old written travel =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      rcases predecessor_incomingReturnAtTarget_cases machine hleft with
          ⟨_, _, _, _, _, hleftDirection, _⟩ |
          ⟨_, _, _, _, _, hleftDirection, _⟩
      all_goals rw [hdirection] at hleftDirection
      all_goals cases hleftDirection
  | departure old written travel =>
      exact encard_predecessors_le_two_of_heads
        (fun predecessor => LBA.Step (rawMachine machine) predecessor
          ⟨⟨targetPhase, .incomingReturnAtTarget edge⟩, tape⟩)
        (fun predecessor => predecessor.tape.head) tape.head
          (tape.moveHead travel.reverse.toDir).head
        (fun predecessor hpredecessor =>
          predecessor_incomingReturnAtTarget_head_eq_or_eq machine
            hdirection hpredecessor)
        (fun left right hleft hright hhead =>
          predecessor_incomingReturnAtTarget_eq_of_head_eq machine
            hleft hright hhead)

/-! ## Complete raw degree and collision terminality -/

/-- Every complete-raw configuration has at most two predecessors, uniformly
over all widths and without a tape well-formedness promise. -/
public theorem rawMachine_configurationIndegreeAtMostTwo
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    (rawMachine machine).ConfigurationIndegreeAtMostTwo := by
  intro n target
  rcases target with ⟨⟨phase, core⟩, tape⟩
  cases core with
  | canonical endpoint slot =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      exact predecessor_canonical_eq machine hleft hright
  | dispatch endpoint slot =>
      exact encard_predecessors_dispatch_le_two machine phase endpoint slot tape
  | outgoingAtNeighbour edge =>
      exact encard_predecessors_outgoingAtNeighbour_le_two
        machine phase edge tape
  | outgoingAtDeparture edge =>
      exact encard_predecessors_outgoingAtDeparture_le_two
        machine phase edge tape
  | outgoingRestoreNeighbour edge =>
      exact encard_predecessors_outgoingRestoreNeighbour_le_two
        machine phase edge tape
  | outgoingValidateAtDeparture edge =>
      exact encard_predecessors_outgoingValidateAtDeparture_le_two
        machine phase edge tape
  | incomingInspect edge =>
      exact encard_predecessors_incomingInspect_le_two machine phase edge tape
  | incomingValidAtTarget edge =>
      exact encard_predecessors_incomingValidAtTarget_le_two
        machine phase edge tape
  | incomingValidFinish edge =>
      exact encard_predecessors_incomingValidFinish_le_two
        machine phase edge tape
  | incomingInvalidAtTarget edge candidate =>
      exact encard_predecessors_incomingInvalidAtTarget_le_two
        machine phase edge candidate tape
  | incomingInvalidAtSource edge candidate =>
      exact encard_predecessors_incomingInvalidAtSource_le_two
        machine phase edge candidate tape
  | incomingReturnAtTarget edge =>
      exact encard_predecessors_incomingReturnAtTarget_le_two
        machine phase edge tape
  | stationaryOutgoingPending edge =>
      exact encard_predecessors_stationaryOutgoingPending_le_two
        machine phase edge tape
  | stationaryIncomingPending edge =>
      exact encard_predecessors_stationaryIncomingPending_le_two
        machine phase edge tape

/-- Any genuine raw double merge is caused by one of the two inverse physical
head candidates clamping.  The freshly written private tag then makes the
common target terminal. -/
public theorem sink_of_two_distinct_predecessors_rawMachine
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) {n : ℕ}
    {left right target :
      DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n}
    (hne : left ≠ right)
    (hleft : LBA.Step (rawMachine machine) left target)
    (hright : LBA.Step (rawMachine machine) right target) :
    ∀ next, ¬ LBA.Step (rawMachine machine) target next := by
  rcases target with ⟨⟨phase, core⟩, tape⟩
  cases core with
  | canonical endpoint slot =>
      exact False.elim (hne (predecessor_canonical_eq machine hleft hright))
  | dispatch endpoint slot =>
      exact False.elim (hne (predecessor_dispatch_eq machine hleft hright))
  | stationaryOutgoingPending edge =>
      exact False.elim (hne ((predecessor_stationaryOutgoingPending_eq
        machine hleft).trans
          (predecessor_stationaryOutgoingPending_eq machine hright).symm))
  | stationaryIncomingPending edge =>
      exact False.elim (hne ((predecessor_stationaryIncomingPending_eq
        machine hleft).trans
          (predecessor_stationaryIncomingPending_eq machine hright).symm))
  | incomingInspect edge =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      exact no_step_of_two_predecessors_with_two_head_choices machine
        hne hleft hright (by trivial)
        (predecessor_incomingInspect_head_eq_or_eq machine hdirection hleft)
        (predecessor_incomingInspect_head_eq_or_eq machine hdirection hright)
        (fun hhead => predecessor_incomingInspect_eq_of_head_eq machine
          hleft hright hhead)
  | outgoingAtDeparture edge =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      exact no_step_of_two_predecessors_with_two_head_choices machine
        hne hleft hright (by trivial)
        (predecessor_outgoingAtDeparture_head_eq_or_eq machine
          hdirection hleft)
        (predecessor_outgoingAtDeparture_head_eq_or_eq machine
          hdirection hright)
        (fun hhead => predecessor_outgoingAtDeparture_eq_of_head_eq machine
          hleft hright hhead)
  | outgoingValidateAtDeparture edge =>
      rcases predecessor_outgoingValidateAtDeparture_departure_and_heads
          machine hleft with
        ⟨old, written, travel, hdirection, hleftHeads⟩
      rcases predecessor_outgoingValidateAtDeparture_departure_and_heads
          machine hright with
        ⟨rightOld, rightWritten, rightTravel, hrightDirection,
          hrightHeads⟩
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hdirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      exact no_step_of_two_predecessors_with_two_head_choices machine
        hne hleft hright (by trivial) hleftHeads hrightHeads
        (fun hhead =>
          predecessor_outgoingValidateAtDeparture_eq_of_head_eq machine
            hleft hright hhead)
  | incomingValidFinish edge =>
      rcases predecessor_incomingValidFinish_departure_and_heads
          machine hleft with
        ⟨old, written, travel, hdirection, hleftHeads⟩
      rcases predecessor_incomingValidFinish_departure_and_heads
          machine hright with
        ⟨rightOld, rightWritten, rightTravel, hrightDirection,
          hrightHeads⟩
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hdirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      exact no_step_of_two_predecessors_with_two_head_choices machine
        hne hleft hright (by trivial) hleftHeads hrightHeads
        (fun hhead => predecessor_incomingValidFinish_eq_of_head_eq machine
          hleft hright hhead)
  | incomingInvalidAtSource edge candidate =>
      rcases predecessor_incomingInvalidAtSource_departure_and_heads
          machine hleft with
        ⟨old, written, travel, hdirection, hleftHeads⟩
      rcases predecessor_incomingInvalidAtSource_departure_and_heads
          machine hright with
        ⟨rightOld, rightWritten, rightTravel, hrightDirection,
          hrightHeads⟩
      have hparameters : old = rightOld ∧ written = rightWritten ∧
          travel = rightTravel := by
        simpa using hdirection.symm.trans hrightDirection
      rcases hparameters with ⟨rfl, rfl, rfl⟩
      exact no_step_of_two_predecessors_with_two_head_choices machine
        hne hleft hright (by trivial) hleftHeads hrightHeads
        (fun hhead =>
          predecessor_incomingInvalidAtSource_eq_of_head_eq machine
            hleft hright hhead)
  | incomingReturnAtTarget edge =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      exact no_step_of_two_predecessors_with_two_head_choices machine
        hne hleft hright (by trivial)
        (predecessor_incomingReturnAtTarget_head_eq_or_eq machine
          hdirection hleft)
        (predecessor_incomingReturnAtTarget_head_eq_or_eq machine
          hdirection hright)
        (fun hhead => predecessor_incomingReturnAtTarget_eq_of_head_eq machine
          hleft hright hhead)
  | outgoingAtNeighbour edge =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .dispatch edge.source .outgoing⟩,
          tape.write (encodePlain edge.old)⟩
      let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .dispatch edge.source .outgoing⟩,
          (tape.moveHead travel.reverse.toDir).write
            (encodePlain edge.old)⟩
      have specialize (predecessor)
          (hpredecessor : LBA.Step (rawMachine machine) predecessor
            ⟨⟨phase, .outgoingAtNeighbour edge⟩, tape⟩) :
          predecessor = first ∨ predecessor = second := by
        rcases predecessor_outgoingAtNeighbour_eq_or_eq machine hpredecessor with
          hfirst | ⟨sourceOld, sourceWritten, sourceTravel,
            hsourceDirection, hsecond⟩
        · exact Or.inl hfirst
        · have hparameters : old = sourceOld ∧ written = sourceWritten ∧
              travel = sourceTravel := by
            simpa using hdirection.symm.trans hsourceDirection
          rcases hparameters with ⟨rfl, rfl, rfl⟩
          exact Or.inr hsecond
      exact no_step_of_two_predecessors_with_two_configuration_choices machine
        hne hleft hright (by trivial) (specialize left hleft)
          (specialize right hright) rfl
  | outgoingRestoreNeighbour edge =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .outgoingAtDeparture edge⟩,
          tape.write (encodeWork (.outgoingDeparture edge))⟩
      let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .outgoingAtDeparture edge⟩,
          (tape.moveHead travel.reverse.toDir).write
            (encodeWork (.outgoingDeparture edge))⟩
      have specialize (predecessor)
          (hpredecessor : LBA.Step (rawMachine machine) predecessor
            ⟨⟨phase, .outgoingRestoreNeighbour edge⟩, tape⟩) :
          predecessor = first ∨ predecessor = second := by
        rcases predecessor_outgoingRestoreNeighbour_eq_or_eq machine
            hpredecessor with hfirst | ⟨sourceOld, sourceWritten,
              sourceTravel, hsourceDirection, hsecond⟩
        · exact Or.inl hfirst
        · have hparameters : old = sourceOld ∧ written = sourceWritten ∧
              travel = sourceTravel := by
            simpa using hdirection.symm.trans hsourceDirection
          rcases hparameters with ⟨rfl, rfl, rfl⟩
          exact Or.inr hsecond
      exact no_step_of_two_predecessors_with_two_configuration_choices machine
        hne hleft hright (by trivial) (specialize left hleft)
          (specialize right hright) rfl
  | incomingValidAtTarget edge =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .incomingInspect edge⟩,
          tape.write (encodePlain edge.written)⟩
      let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .incomingInspect edge⟩,
          (tape.moveHead travel.reverse.toDir).write
            (encodePlain edge.written)⟩
      have specialize (predecessor)
          (hpredecessor : LBA.Step (rawMachine machine) predecessor
            ⟨⟨phase, .incomingValidAtTarget edge⟩, tape⟩) :
          predecessor = first ∨ predecessor = second := by
        rcases predecessor_incomingValidAtTarget_eq_or_eq machine
            hpredecessor with hfirst | ⟨sourceOld, sourceWritten,
              sourceTravel, hsourceDirection, hsecond⟩
        · exact Or.inl hfirst
        · have hparameters : old = sourceOld ∧ written = sourceWritten ∧
              travel = sourceTravel := by
            simpa using hdirection.symm.trans hsourceDirection
          rcases hparameters with ⟨rfl, rfl, rfl⟩
          exact Or.inr hsecond
      exact no_step_of_two_predecessors_with_two_configuration_choices machine
        hne hleft hright (by trivial) (specialize left hleft)
          (specialize right hright) rfl
  | incomingInvalidAtTarget edge candidate =>
      rcases departure_of_step_to_moving_landing_edge machine rfl hleft with
        ⟨old, written, travel, hdirection⟩
      let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .incomingInspect edge⟩,
          tape.write (encodePlain candidate)⟩
      let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
        ⟨⟨!phase, .incomingInspect edge⟩,
          (tape.moveHead travel.reverse.toDir).write
            (encodePlain candidate)⟩
      have specialize (predecessor)
          (hpredecessor : LBA.Step (rawMachine machine) predecessor
            ⟨⟨phase, .incomingInvalidAtTarget edge candidate⟩, tape⟩) :
          predecessor = first ∨ predecessor = second := by
        rcases predecessor_incomingInvalidAtTarget_eq_or_eq machine
            hpredecessor with hfirst | ⟨sourceOld, sourceWritten,
              sourceTravel, hsourceDirection, hsecond⟩
        · exact Or.inl hfirst
        · have hparameters : old = sourceOld ∧ written = sourceWritten ∧
              travel = sourceTravel := by
            simpa using hdirection.symm.trans hsourceDirection
          rcases hparameters with ⟨rfl, rfl, rfl⟩
          exact Or.inr hsecond
      exact no_step_of_two_predecessors_with_two_configuration_choices machine
        hne hleft hright (by trivial) (specialize left hleft)
          (specialize right hright) rfl

end MarkedEulerProbe

end GraphWalking

end
