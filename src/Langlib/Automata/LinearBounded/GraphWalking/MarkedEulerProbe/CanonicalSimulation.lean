module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.Structural
public import Langlib.Automata.LinearBounded.GraphWalking.ArrivalProbe
public import Langlib.Automata.LinearBounded.BoundaryShuttle.Canonical
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical semantics of the marked Euler probe

This file relates the raw marked transition table to the local Euler port
permutation.  A plain tape carries an immutable code for its physical left
and right boundary.  Canonical raw configurations are obtained by injecting
every plain cell and by placing the represented local port in finite control;
the inverse map is partial because protocol tags deliberately do not decode
as plain cells.

The simulation lemmas below expose every constant-length protocol path.  The
phase bit is retained exactly at intermediate configurations and erased only
when stating the represented port.
-/

namespace GraphWalking

open Relation
open FunctionalGraphReversibleTraversal

universe uTerminal uWork uState

namespace MarkedEulerProbe

noncomputable section

local instance (priority := low) markedEulerProbeCanonicalSimulationPropDecidable
    (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-! ## Boundary-correct plain tapes -/

/-- The physical boundary class of a cell of an `(n+1)`-cell tape. -/
@[expose]
public def physicalBoundary {n : Nat} (position : Fin (n + 1)) : Boundary :=
  if n = 0 then .both
  else if position.val = 0 then .left
  else if position.val = n then .right
  else .middle

/-- Every plain cell remembers its actual physical boundary class. -/
@[expose]
public def WellBoundaryCoded {T : Type uTerminal} {Gamma : Type uWork}
    {n : Nat} (tape : DLBA.BoundedTape (PlainCode T Gamma) n) : Prop :=
  forall position, (tape.contents position).boundary = physicalBoundary position

public theorem physicalBoundary_allows_left_iff {n : Nat}
    (position : Fin (n + 1)) :
    (physicalBoundary position).allows .left = true ↔ 0 < position.val := by
  unfold physicalBoundary
  by_cases hn : n = 0
  · have hposition : position.val = 0 := by
      have := position.isLt
      omega
    simp [hn, hposition, Boundary.allows]
  · rw [if_neg hn]
    by_cases hzero : position.val = 0
    · simp [hzero, Boundary.allows]
    · rw [if_neg hzero]
      by_cases hlast : position.val = n
      · have hpositive : 0 < position.val := by omega
        have hnpositive : 0 < n := by omega
        simp [hlast, hnpositive, Boundary.allows]
      · have hpositive : 0 < position.val := by omega
        simp [hlast, hpositive, Boundary.allows]

public theorem physicalBoundary_allows_right_iff {n : Nat}
    (position : Fin (n + 1)) :
    (physicalBoundary position).allows .right = true ↔ position.val < n := by
  unfold physicalBoundary
  by_cases hn : n = 0
  · have hposition : position.val = 0 := by
      have := position.isLt
      omega
    simp [hn, hposition, Boundary.allows]
  · rw [if_neg hn]
    by_cases hzero : position.val = 0
    · have hpositive : 0 < n := by omega
      simp [hzero, hpositive, Boundary.allows]
    · rw [if_neg hzero]
      by_cases hlast : position.val = n
      · simp [hlast, Boundary.allows]
      · have hlt : position.val < n := by
          have := position.isLt
          omega
        simp [hlast, hlt, Boundary.allows]

/-- On a boundary-correct tape, the finite symbol test used by the raw table
is equivalent to existence of the corresponding partial memory move. -/
public theorem allows_iff_exists_nextHead
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) (travel : BoundedTapeMemory.Travel) :
    tape.read.boundary.allows travel = true ↔
      exists target, BoundedTapeMemory.nextHead travel tape.head = some target := by
  change (tape.contents tape.head).boundary.allows travel = true ↔ _
  rw [hwell tape.head]
  cases travel with
  | left =>
      rw [physicalBoundary_allows_left_iff]
      constructor
      · intro hpositive
        refine ⟨Fin.mk (tape.head.val - 1) (by omega), ?_⟩
        simp [BoundedTapeMemory.nextHead, hpositive]
      · rintro ⟨target, hnext⟩
        by_contra hnot
        have hzero : tape.head.val = 0 := by omega
        simp [BoundedTapeMemory.nextHead, hzero] at hnext
  | right =>
      rw [physicalBoundary_allows_right_iff]
      constructor
      · intro hinside
        refine ⟨Fin.mk (tape.head.val + 1) (by omega), ?_⟩
        simp [BoundedTapeMemory.nextHead, hinside]
      · rintro ⟨target, hnext⟩
        by_contra hnot
        have hlast : tape.head.val = n := by
          have := tape.head.isLt
          omega
        simp [BoundedTapeMemory.nextHead, hlast] at hnext

public theorem wellBoundaryCoded_moveHead
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) (direction : DLBA.Dir) :
    WellBoundaryCoded (tape.moveHead direction) := by
  intro position
  exact hwell position

public theorem movesInside_toDir_of_allows
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) (travel : BoundedTapeMemory.Travel)
    (hallows : tape.read.boundary.allows travel = true) :
    LBA.movesInside tape travel.toDir := by
  obtain ⟨target, hnext⟩ :=
    (allows_iff_exists_nextHead tape hwell travel).mp hallows
  cases travel with
  | left =>
      change 0 < tape.head.val
      by_contra hnot
      have hzero : tape.head.val = 0 := by omega
      simp [BoundedTapeMemory.nextHead, hzero] at hnext
  | right =>
      change tape.head.val < n
      by_contra hnot
      have hlast : tape.head.val = n := by
        have := tape.head.isLt
        omega
      simp [BoundedTapeMemory.nextHead, hlast] at hnext

@[simp]
public theorem reverseDirection_toDir
    (travel : BoundedTapeMemory.Travel) :
    LBA.reverseDirection travel.toDir = travel.reverse.toDir := by
  cases travel <;> rfl

/-- Pointwise injection of a plain tape into the raw endmarker alphabet. -/
@[expose]
public def encodeTape {T : Type uTerminal} {Gamma : Type uWork}
    {Q : Type uState} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n where
  contents := encodePlain ∘ tape.contents
  head := tape.head

/-- Partial pointwise decoding of a raw tape.  It succeeds exactly when every
cell is ordinary data rather than a private protocol tag. -/
@[expose]
public noncomputable def decodeTape {T : Type uTerminal} {Gamma : Type uWork}
    {Q : Type uState} {n : Nat}
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    Option (DLBA.BoundedTape (PlainCode T Gamma) n) :=
  if hplain : forall position, exists code,
      decodePlain (tape.contents position) = some code then
    some
      { contents := fun position => Classical.choose (hplain position)
        head := tape.head }
  else
    none

@[simp]
public theorem decodeTape_encodeTape
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    decodeTape (encodeTape (Q := Q) tape) = some tape := by
  classical
  unfold decodeTape
  simp only [encodeTape, Function.comp_apply, decodePlain_encodePlain]
  split
  next hplain =>
    apply congrArg some
    apply BoundedTapeMemory.eq_of_contents_head
    · funext position
      exact (Option.some.inj (Classical.choose_spec (hplain position))).symm
    · rfl
  next hplain =>
    exact (hplain (fun position => ⟨tape.contents position, rfl⟩)).elim

@[simp]
public theorem encodeTape_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    (encodeTape (Q := Q) tape).read = encodePlain tape.read := rfl

@[simp]
public theorem encodeTape_write
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (code : PlainCode T Gamma) :
    (encodeTape (Q := Q) tape).write (encodePlain code) =
      encodeTape (Q := Q) (tape.write code) := by
  classical
  apply BoundedTapeMemory.eq_of_contents_head
  · simp [encodeTape, DLBA.BoundedTape.write, Function.comp_update]
  · rfl

@[simp]
public theorem encodeTape_moveHead
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) (direction : DLBA.Dir) :
    (encodeTape (Q := Q) tape).moveHead direction =
      encodeTape (Q := Q) (tape.moveHead direction) := by
  rfl

/-! ## Canonical raw configurations and their partial inverse -/

/-- Encode one local port as a canonical raw-LBA configuration. -/
@[expose]
public def encodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) :
    DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
  { state :=
      { phase := phase
        core := .canonical port.1.1 port.2 }
    tape := encodeTape port.1.2 }

/-- Decode a canonical raw configuration to its phase and represented local
port.  Dispatch and protocol configurations decode to `none`. -/
@[expose]
public noncomputable def decodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) :
    Option (Bool × LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) :=
  match configuration.state.core with
  | .canonical endpoint slot =>
      (decodeTape configuration.tape).map fun tape =>
        (configuration.state.phase, ((endpoint, tape), slot))
  | _ => none

@[simp]
public theorem decodePortCfg_encodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)) :
    decodePortCfg (encodePortCfg phase port) = some (phase, port) := by
  simp [decodePortCfg, encodePortCfg]

/-! ## The canonical undoubled local port system -/

/-- Local ports of the marked direction-lifted controller at an arbitrary
bounded-tape width.  This is the semantic object refined by the raw protocol;
the explicit raw phase is intentionally absent from it. -/
@[expose]
public noncomputable def ports
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (n : Nat) :=
  LocalPort.ofMachine
    (walker machine)
    (BoundedTapeMemory.graph (PlainCode T Gamma) n)
    (BoundedTapeController.machine
      (markedMachine machine)).directionLiftArrival

/-! ## Canonical endmarker input, including the empty word -/

/-- The exact plain-code presentation of the bracketed input `left w right`. -/
@[expose]
public noncomputable def plainLoadEnd
    {T : Type uTerminal} {Gamma : Type uWork} (word : List T) :
    DLBA.BoundedTape (PlainCode T Gamma) (word.length + 1) where
  contents position :=
    if position.val = 0 then .leftMarker
    else if h : position.val - 1 < word.length then
      .input (word.get <| Fin.mk (position.val - 1) h)
    else
      .rightMarker
  head := Fin.mk 0 (Nat.succ_pos _)

/-- The bracketed plain input has the right boundary code at every cell.  For
the empty word this says that the two cells are respectively `left` and
`right`, not `both`. -/
public theorem plainLoadEnd_wellBoundaryCoded
    {T : Type uTerminal} {Gamma : Type uWork} (word : List T) :
    WellBoundaryCoded (plainLoadEnd (Gamma := Gamma) word) := by
  intro position
  have hn : word.length + 1 ≠ 0 := by omega
  unfold plainLoadEnd physicalBoundary
  rw [if_neg hn]
  by_cases hzero : position.val = 0
  · simp [hzero, PlainCode.boundary]
  · by_cases hinterior : position.val - 1 < word.length
    · have hlast : position.val ≠ word.length + 1 := by omega
      simp [hzero, hinterior, hlast, PlainCode.boundary]
    · have hlast : position.val = word.length + 1 := by
        have := position.isLt
        omega
      simp [hlast, PlainCode.boundary]

@[simp]
public theorem encodeTape_plainLoadEnd
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (word : List T) :
    encodeTape (Q := Q) (plainLoadEnd (Gamma := Gamma) word) =
      LBA.loadEnd (Γ := WorkSymbol T Gamma Q) word := by
  apply BoundedTapeMemory.eq_of_contents_head
  · funext position
    simp only [encodeTape, plainLoadEnd, Function.comp_apply, LBA.loadEnd]
    split
    · rfl
    · split
      · rfl
      · rfl
  · rfl

/-- Initial local port corresponding to the raw compiler's endmarker input. -/
@[expose]
public noncomputable def initialPort
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (word : List T) :
    LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) (word.length + 1)) :=
  (((machine.initial,
      .stationary (.leftMarker : PlainCode T Gamma) .leftMarker),
      plainLoadEnd (Gamma := Gamma) word),
    .anchor)

/-- Raw initialization is exactly canonical port encoding.  There is no
nonempty-word premise, so this theorem includes the genuine two-cell tape for
`epsilon`. -/
public theorem initCfgEnd_rawMachine_eq_encodePortCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (word : List T) :
    LBA.initCfgEnd (rawMachine machine) word =
      encodePortCfg false (initialPort machine word) := by
  unfold LBA.initCfgEnd encodePortCfg initialPort
  simp only [rawMachine]
  rw [encodeTape_plainLoadEnd]

/-- The empty word is covered explicitly: both presentations have the
canonical two-cell `left right` tape. -/
public theorem initCfgEnd_rawMachine_nil
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) :
    LBA.initCfgEnd (rawMachine machine) ([] : List T) =
      encodePortCfg false (initialPort machine []) :=
  initCfgEnd_rawMachine_eq_encodePortCfg machine []

/-! ## Raw-step helpers -/

/-- A raw configuration with an explicitly supplied protocol core and tape. -/
@[expose]
public def protocolCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (phase : Bool) (core : CoreState T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
  { state := { phase := phase, core := core }
    tape := tape }

/-- A raw configuration is strictly inside a protocol macro rather than at an
encoded local port.  This constructor test is the proper-prefix invariant used
by canonical-return reflection. -/
@[expose]
public def NoncanonicalCore
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n) : Prop :=
  match configuration.state.core with
  | .canonical _ _ => False
  | _ => True

@[simp]
public theorem noncanonicalCore_dispatch
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (phase : Bool) (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (Alphabet T Gamma Q) n) :
    NoncanonicalCore (protocolCfg phase (.dispatch endpoint slot) tape) := by
  simp [NoncanonicalCore, protocolCfg]

private theorem write_read_stay {A : Type*} {n : Nat}
    (tape : DLBA.BoundedTape A n) :
    (tape.write tape.read).moveHead .stay = tape := by
  cases tape with
  | mk contents head =>
      simp [DLBA.BoundedTape.write, DLBA.BoundedTape.read,
        DLBA.BoundedTape.moveHead]

private theorem moveHead_stay {A : Type*} {n : Nat}
    (tape : DLBA.BoundedTape A n) : tape.moveHead .stay = tape := by
  cases tape
  rfl

private theorem write_write {A : Type*} {n : Nat}
    (tape : DLBA.BoundedTape A n) (first second : A) :
    (tape.write first).write second = tape.write second := by
  classical
  cases tape with
  | mk contents head =>
      simp [DLBA.BoundedTape.write, Function.update_idem]

private theorem alternating_restore_read_first
    {Index Value : Type*} [DecidableEq Index]
    (base : Index → Value) (first second : Index)
    (hne : first ≠ second) (firstTag secondTag : Value) :
    Function.update
      (Function.update
        (Function.update
          (Function.update base first firstTag) second secondTag)
        first firstTag)
      second (base second) first = firstTag := by
  simp [Function.update, hne]

private theorem alternating_updates_restore
    {Index Value : Type*} [DecidableEq Index]
    (base : Index → Value) (first second : Index)
    (_hne : first ≠ second) (firstTag secondTag : Value) :
    Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update base first firstTag) second secondTag)
          first firstTag)
        second (base second))
      first (base first) = base := by
  funext position
  by_cases hfirst : position = first
  · subst position
    simp [Function.update]
  · by_cases hsecond : position = second
    · subst position
      simp [Function.update, hfirst]
    · simp [Function.update, hfirst, hsecond]

/-- Every operation emitted by the marked controller records the observed
plain code as its `old` field. -/
public theorem edge_old_eq_of_walker_transition
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
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

/-- The marked controller preserves the immutable boundary component in the
symbol saved as `written`. -/
public theorem edge_written_boundary_eq_of_walker_transition
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {endpoint target : LiftState T Gamma Q} {code : PlainCode T Gamma}
    {direction : BoundedTapeMemory.Direction (PlainCode T Gamma)}
    (htransition : (walker machine).transition endpoint code =
      some (target, direction)) :
    (Edge.mk endpoint target direction).written.boundary = code.boundary := by
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

/-- The forward marked walker never selects an arrival operation.  Arrival
names are used only by the local port system while traversing an edge in the
reverse direction. -/
public theorem walker_transition_ne_arrival
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (source target : LiftState T Gamma Q) (code old written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel) :
    (walker machine).transition source code ≠
      some (target, .arrival old written travel) := by
  intro htransition
  let edge : Edge T Gamma Q :=
    { source := source, target := target,
      direction := .arrival old written travel }
  have henabled : edge.Enabled machine := by
    unfold Edge.Enabled
    have hold : edge.old = code := by
      exact edge_old_eq_of_walker_transition machine htransition
    rw [hold]
    exact htransition
  exact (edge.direction_ne_arrival_of_enabled machine henabled
    old written travel) (by rfl)

/-- The first raw edge performs exactly the finite slot rotation and leaves
the encoded tape untouched. -/
public theorem step_rotate_to_dispatch
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q)
    (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    LBA.Step (rawMachine machine)
      (encodePortCfg phase (((endpoint, tape), slot)))
      (protocolCfg (!phase) (.dispatch endpoint (rotateSlot slot))
        (encodeTape tape)) := by
  refine ⟨nextState phase (.dispatch endpoint (rotateSlot slot)),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, encodePortCfg, oneOutput,
      encodeTape]
  · simp only [encodePortCfg, protocolCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

/-- The anchor is a fixed swap port, implemented by one stationary raw edge
after dispatch. -/
public theorem step_dispatch_anchor
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .anchor) (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .anchor))) := by
  refine ⟨nextState phase (.canonical endpoint .anchor),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

/-! ## Fixed swap ports -/

public theorem step_dispatch_outgoing_none
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (htransition : (walker machine).transition endpoint tape.read = none) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .outgoing))) := by
  change (walker machine).transition endpoint (tape.contents tape.head) = none at htransition
  refine ⟨nextState phase (.canonical endpoint .outgoing),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
      htransition]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

public theorem step_dispatch_outgoing_arrival
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .arrival old written travel)) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .outgoing))) := by
  change (walker machine).transition endpoint (tape.contents tape.head) =
    some (target, .arrival old written travel) at htransition
  refine ⟨nextState phase (.canonical endpoint .outgoing),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
      htransition]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

public theorem step_dispatch_outgoing_departure_blocked
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .departure old written travel))
    (hblocked : tape.read.boundary.allows travel = false) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .outgoing))) := by
  change (walker machine).transition endpoint (tape.contents tape.head) =
    some (target, .departure old written travel) at htransition
  change (tape.contents tape.head).boundary.allows travel = false at hblocked
  refine ⟨nextState phase (.canonical endpoint .outgoing),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
      htransition, hblocked]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

/-! ## Stationary computation-edge ports -/

/-- Exact two-edge witness for a stationary outgoing swap port. -/
public theorem exists_steps_dispatch_stationary_outgoing
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .stationary old written)) :
    ∃ middle : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n,
      LBA.Step (rawMachine machine)
        (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
        middle ∧
      LBA.Step (rawMachine machine) middle
        (encodePortCfg phase
          (((target, tape.write written), .incoming endpoint))) ∧
      NoncanonicalCore middle := by
  have hold : old = tape.read := by
    have h := edge_old_eq_of_walker_transition machine htransition
    simpa using h
  subst old
  change (walker machine).transition endpoint (tape.contents tape.head) =
    some (target, .stationary (tape.contents tape.head) written) at htransition
  let edge : Edge T Gamma Q :=
    { source := endpoint, target := target,
      direction := .stationary tape.read written }
  let middleTape :=
    (encodeTape (Q := Q) tape).write
      (encodeWork (.stationaryOutgoing edge))
  let middle : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.stationaryOutgoingPending edge) middleTape
  have hfirst : LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      middle := by
    refine ⟨nextState phase (.stationaryOutgoingPending edge),
      encodeWork (.stationaryOutgoing edge), .stay, ?_, ?_⟩
    · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
        htransition, edge]
    · simp [middle, middleTape, protocolCfg, nextState, moveHead_stay]
  have hsecond : LBA.Step (rawMachine machine) middle
      (encodePortCfg phase
        (((target, tape.write written), .incoming endpoint))) := by
    refine ⟨nextState (!phase) (.canonical target (.incoming endpoint)),
      encodePlain written, .stay, ?_, ?_⟩
    · simp [rawMachine, transition, middle, middleTape, protocolCfg,
        oneOutput, edge, Edge.Enabled, Edge.old, htransition,
        decodeWork, encodeWork,
        DLBA.BoundedTape.read, DLBA.BoundedTape.write]
    · simp only [middle, middleTape, protocolCfg, encodePortCfg, nextState,
        Bool.not_not]
      congr 1
      rw [moveHead_stay, write_write, encodeTape_write]
  exact ⟨middle, hfirst, hsecond, by simp [NoncanonicalCore, middle, protocolCfg]⟩

/-- Exact two-edge implementation of a stationary outgoing swap port. -/
public theorem reaches_dispatch_stationary_outgoing
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .stationary old written)) :
    LBA.Reaches (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg phase
        (((target, tape.write written), .incoming endpoint))) := by
  obtain ⟨middle, hfirst, hsecond, _⟩ :=
    exists_steps_dispatch_stationary_outgoing machine phase endpoint target
      old written tape htransition
  exact (ReflTransGen.single hfirst).tail hsecond

/-- A stationary incoming candidate which fails its exact symbol/edge test is
a fixed local port. -/
public theorem step_dispatch_stationary_incoming_fixed
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .stationary old written)
    (hinvalid : ¬(tape.read = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine)) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .incoming source))) := by
  change (tape.contents tape.head = written ∧
    (Edge.ofIncoming endpoint source).Enabled machine) → False at hinvalid
  refine ⟨nextState phase (.canonical endpoint (.incoming source)),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · by_cases hvalid : tape.contents tape.head = written ∧
        (Edge.ofIncoming endpoint source).Enabled machine
    · exact (hinvalid hvalid).elim
    · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
        hdirection, hvalid]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

/-- Exact two-edge witness for a valid stationary incoming port. -/
public theorem exists_steps_dispatch_stationary_incoming
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .stationary old written)
    (hread : tape.read = written)
    (henabled : (Edge.ofIncoming endpoint source).Enabled machine) :
    ∃ middle : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n,
      LBA.Step (rawMachine machine)
        (protocolCfg phase (.dispatch endpoint (.incoming source))
          (encodeTape tape)) middle ∧
      LBA.Step (rawMachine machine) middle
        (encodePortCfg phase (((source, tape.write old), .outgoing))) ∧
      NoncanonicalCore middle := by
  change endpoint.2 = .stationary old written at hdirection
  change tape.contents tape.head = written at hread
  unfold Edge.Enabled at henabled
  simp only [Edge.ofIncoming] at henabled
  rw [hdirection] at henabled
  have henabled' : (walker machine).transition source old =
      some (endpoint, .stationary old written) := by
    simpa only [Edge.old] using henabled
  let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
  let middleTape :=
    (encodeTape (Q := Q) tape).write
      (encodeWork (.stationaryIncoming edge))
  let middle : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.stationaryIncomingPending edge) middleTape
  have hfirst : LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape tape)) middle := by
    refine ⟨nextState phase (.stationaryIncomingPending edge),
      encodeWork (.stationaryIncoming edge), .stay, ?_, ?_⟩
    · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
        edge, hdirection, hread, henabled', Edge.Enabled, Edge.ofIncoming,
        Edge.old]
    · simp [middle, middleTape, protocolCfg, nextState, moveHead_stay]
  have hsecond : LBA.Step (rawMachine machine) middle
      (encodePortCfg phase (((source, tape.write old), .outgoing))) := by
    refine ⟨nextState (!phase) (.canonical source .outgoing),
      encodePlain old, .stay, ?_, ?_⟩
    · simp [rawMachine, transition, middle, middleTape, protocolCfg,
        oneOutput, edge, hdirection, henabled', Edge.Enabled, Edge.ofIncoming,
        Edge.old, decodeWork, encodeWork, DLBA.BoundedTape.read,
        DLBA.BoundedTape.write]
    · simp only [middle, middleTape, protocolCfg, encodePortCfg, nextState,
        Bool.not_not]
      congr 1
      rw [moveHead_stay, write_write, encodeTape_write]
  exact ⟨middle, hfirst, hsecond, by simp [NoncanonicalCore, middle, protocolCfg]⟩

/-- Exact two-edge implementation of a valid stationary incoming port. -/
public theorem reaches_dispatch_stationary_incoming
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .stationary old written)
    (hread : tape.read = written)
    (henabled : (Edge.ofIncoming endpoint source).Enabled machine) :
    LBA.Reaches (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape tape))
      (encodePortCfg phase (((source, tape.write old), .outgoing))) := by
  obtain ⟨middle, hfirst, hsecond, _⟩ :=
    exists_steps_dispatch_stationary_incoming machine phase endpoint source
      old written tape hdirection hread henabled
  exact (ReflTransGen.single hfirst).tail hsecond

public theorem step_dispatch_incoming_arrival
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .arrival old written travel) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .incoming source))) := by
  refine ⟨nextState phase (.canonical endpoint (.incoming source)),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
      hdirection]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

public theorem step_dispatch_incoming_departure_blocked
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hblocked : tape.read.boundary.allows travel.reverse = false) :
    LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape tape))
      (encodePortCfg (!phase) (((endpoint, tape), .incoming source))) := by
  change (tape.contents tape.head).boundary.allows travel.reverse = false at hblocked
  refine ⟨nextState phase (.canonical endpoint (.incoming source)),
    encodePlain tape.read, .stay, ?_, ?_⟩
  · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
      hdirection, hblocked]
  · simp only [protocolCfg, encodePortCfg, nextState]
    congr 1
    symm
    simpa only [encodeTape_read] using write_read_stay (encodeTape tape)

/-! ## Directional outgoing protocol -/

@[expose]
public def outgoingNeighbourCode
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) : PlainCode T Gamma :=
  (tape.moveHead travel.toDir).read

@[expose]
public def outgoingAfterDeparture
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((encodeTape tape).write (encodeWork (.outgoingDeparture edge))).moveHead
    travel.toDir

@[expose]
public def outgoingAfterNeighbour
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((outgoingAfterDeparture edge travel tape).write
    (encodeWork (.outgoingNeighbour edge (outgoingNeighbourCode travel tape))))
      |>.moveHead travel.reverse.toDir

@[expose]
public def outgoingAfterRestoreDeparture
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((outgoingAfterNeighbour edge travel tape).write (encodePlain written))
    |>.moveHead travel.toDir

/-- The authenticated return tag installed at the target cell before the
protocol exposes the target incoming port. -/
@[expose]
public def outgoingAfterReturnTag
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((outgoingAfterRestoreDeparture edge written travel tape).write
    (encodeWork (.incomingTarget edge (outgoingNeighbourCode travel tape))))
      |>.moveHead travel.reverse.toDir

/-- Tape after locally validating the restored departure cell and returning
to the authenticated target tag. -/
@[expose]
public def outgoingAfterValidatedDeparture
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((outgoingAfterReturnTag edge written travel tape).write
    (encodePlain written)) |>.moveHead travel.toDir

@[expose]
public def outgoingAfterFinish
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  (outgoingAfterRestoreDeparture edge written travel tape).write
    (encodePlain (outgoingNeighbourCode travel tape))

public theorem outgoingAfterDeparture_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    (outgoingAfterDeparture edge travel tape).read =
      encodePlain (outgoingNeighbourCode travel tape) := by
  classical
  change Function.update (encodePlain ∘ tape.contents) tape.head
      (encodeWork (.outgoingDeparture edge))
      (tape.moveHead travel.toDir).head =
    encodePlain (tape.contents (tape.moveHead travel.toDir).head)
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne tape travel.toDir hinside)]
  rfl

public theorem outgoingAfterNeighbour_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    (outgoingAfterNeighbour edge travel tape).read =
      encodeWork (.outgoingDeparture edge) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside)
  rw [reverseDirection_toDir] at hback
  change Function.update
      (Function.update (encodePlain ∘ tape.contents) tape.head
        (encodeWork (.outgoingDeparture edge)))
      (tape.moveHead travel.toDir).head
      (encodeWork (.outgoingNeighbour edge (outgoingNeighbourCode travel tape)))
      ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head = _
  rw [hback]
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne tape travel.toDir hinside).symm]
  simp

public theorem outgoingAfterRestoreDeparture_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    (outgoingAfterRestoreDeparture edge written travel tape).read =
      encodeWork (.outgoingNeighbour edge (outgoingNeighbourCode travel tape)) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside)
  rw [reverseDirection_toDir] at hback
  have hforward :
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).head = (tape.moveHead travel.toDir).head := by
    rw [← reverseDirection_toDir]
    rw [LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside]
  change Function.update
      (Function.update
        (Function.update (encodePlain ∘ tape.contents) tape.head
          (encodeWork (.outgoingDeparture edge)))
        (tape.moveHead travel.toDir).head
        (encodeWork (.outgoingNeighbour edge (outgoingNeighbourCode travel tape))))
      ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head
      (encodePlain written)
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).head = _
  rw [hback, hforward]
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne tape travel.toDir hinside)]
  simp

public theorem outgoingAfterReturnTag_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    (outgoingAfterReturnTag edge written travel tape).read =
      encodePlain written := by
  classical
  have hroundtrip :
      (tape.moveHead travel.toDir).moveHead travel.reverse.toDir = tape := by
    rw [← reverseDirection_toDir]
    exact LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside
  have hforwardTape :
      ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir = tape.moveHead travel.toDir := by
    rw [hroundtrip]
  have hreturnTape :
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir = tape := by
    rw [hforwardTape, hroundtrip]
  change Function.update
      (Function.update
        (Function.update
          (Function.update (encodePlain ∘ tape.contents) tape.head
            (encodeWork (.outgoingDeparture edge)))
          (tape.moveHead travel.toDir).head
          (encodeWork (.outgoingNeighbour edge
            (outgoingNeighbourCode travel tape))))
        ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head
        (encodePlain written))
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).head
      (encodeWork (.incomingTarget edge (outgoingNeighbourCode travel tape)))
      ((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir).head = _
  rw [congrArg DLBA.BoundedTape.head hroundtrip,
    congrArg DLBA.BoundedTape.head hforwardTape,
    congrArg DLBA.BoundedTape.head hreturnTape]
  have hne := LBA.movesInside_head_ne tape travel.toDir hinside
  simp [Function.update, hne.symm]

public theorem outgoingAfterValidatedDeparture_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    (outgoingAfterValidatedDeparture edge written travel tape).read =
      encodeWork (.incomingTarget edge (outgoingNeighbourCode travel tape)) := by
  classical
  have hroundtrip :
      (tape.moveHead travel.toDir).moveHead travel.reverse.toDir = tape := by
    rw [← reverseDirection_toDir]
    exact LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside
  have hforwardTape :
      ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir = tape.moveHead travel.toDir := by
    rw [hroundtrip]
  have hreturnTape :
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir = tape := by
    rw [hforwardTape, hroundtrip]
  have htargetTape :
      ((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir).moveHead travel.toDir =
          tape.moveHead travel.toDir := by
    rw [hreturnTape]
  change Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update (encodePlain ∘ tape.contents) tape.head
              (encodeWork (.outgoingDeparture edge)))
            (tape.moveHead travel.toDir).head
            (encodeWork (.outgoingNeighbour edge
              (outgoingNeighbourCode travel tape))))
          ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head
          (encodePlain written))
        (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
          travel.toDir).head
        (encodeWork (.incomingTarget edge (outgoingNeighbourCode travel tape))))
      ((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir).head
      (encodePlain written)
      (((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir).moveHead
          travel.toDir).head = _
  rw [congrArg DLBA.BoundedTape.head hroundtrip,
    congrArg DLBA.BoundedTape.head hforwardTape,
    congrArg DLBA.BoundedTape.head hreturnTape,
    congrArg DLBA.BoundedTape.head htargetTape]
  have hne := LBA.movesInside_head_ne tape travel.toDir hinside
  simp [Function.update, hne]

/-- Erasing the authenticated return tag gives the same final tape as the
direct algebraic finish operation below. -/
public theorem outgoingAfterReturnErase_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    (outgoingAfterValidatedDeparture edge written travel tape).write
        (encodePlain (outgoingNeighbourCode travel tape)) =
      outgoingAfterFinish edge written travel tape := by
  classical
  have hroundtrip :
      (tape.moveHead travel.toDir).moveHead travel.reverse.toDir = tape := by
    rw [← reverseDirection_toDir]
    exact LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside
  have hforwardTape :
      ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir = tape.moveHead travel.toDir := by
    rw [hroundtrip]
  have hreturnTape :
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir = tape := by
    rw [hforwardTape, hroundtrip]
  have htargetTape :
      ((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).moveHead travel.reverse.toDir).moveHead travel.toDir =
          tape.moveHead travel.toDir := by
    rw [hreturnTape]
  apply BoundedTapeMemory.eq_of_contents_head
  · change Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update
                (Function.update (encodePlain ∘ tape.contents) tape.head
                  (encodeWork (.outgoingDeparture edge)))
                (tape.moveHead travel.toDir).head
                (encodeWork (.outgoingNeighbour edge
                  (outgoingNeighbourCode travel tape))))
              ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head
              (encodePlain written))
            (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
              travel.toDir).head
            (encodeWork (.incomingTarget edge
              (outgoingNeighbourCode travel tape))))
          ((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
            travel.toDir).moveHead travel.reverse.toDir).head
          (encodePlain written))
        (((((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
          travel.toDir).moveHead travel.reverse.toDir).moveHead
            travel.toDir).head
        (encodePlain (outgoingNeighbourCode travel tape)) =
        Function.update
          (Function.update
            (Function.update
              (Function.update (encodePlain ∘ tape.contents) tape.head
                (encodeWork (.outgoingDeparture edge)))
              (tape.moveHead travel.toDir).head
              (encodeWork (.outgoingNeighbour edge
                (outgoingNeighbourCode travel tape))))
            ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head
            (encodePlain written))
          (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
            travel.toDir).head
          (encodePlain (outgoingNeighbourCode travel tape))
    rw [congrArg DLBA.BoundedTape.head hroundtrip,
      congrArg DLBA.BoundedTape.head hforwardTape,
      congrArg DLBA.BoundedTape.head hreturnTape,
      congrArg DLBA.BoundedTape.head htargetTape]
    have hne := LBA.movesInside_head_ne tape travel.toDir hinside
    funext position
    by_cases hdeparture : position = tape.head
    · subst position
      simp [Function.update]
    · by_cases htarget : position = (tape.moveHead travel.toDir).head
      · subst position
        simp [Function.update]
      · simp [Function.update, hdeparture, htarget]
  · exact (congrArg DLBA.BoundedTape.head htargetTape).trans
      (congrArg DLBA.BoundedTape.head hforwardTape).symm

public theorem outgoingAfterFinish_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (written : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside tape travel.toDir) :
    outgoingAfterFinish edge written travel tape =
      encodeTape ((tape.write written).moveHead travel.toDir) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside)
  rw [reverseDirection_toDir] at hback
  have hforward :
      (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
        travel.toDir).head = (tape.moveHead travel.toDir).head := by
    rw [← reverseDirection_toDir]
    rw [LBA.moveHead_reverseDirection_moveHead tape travel.toDir hinside]
  apply BoundedTapeMemory.eq_of_contents_head
  · change Function.update
        (Function.update
          (Function.update
            (Function.update (encodePlain ∘ tape.contents) tape.head
              (encodeWork (.outgoingDeparture edge)))
            (tape.moveHead travel.toDir).head
            (encodeWork (.outgoingNeighbour edge
              (outgoingNeighbourCode travel tape))))
          ((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).head
          (encodePlain written))
        (((tape.moveHead travel.toDir).moveHead travel.reverse.toDir).moveHead
          travel.toDir).head
        (encodePlain (outgoingNeighbourCode travel tape)) =
      encodePlain ∘ Function.update tape.contents tape.head written
    rw [hback, hforward]
    have hne := LBA.movesInside_head_ne tape travel.toDir hinside
    rw [Function.update_comm hne.symm, Function.update_idem]
    rw [Function.update_comm hne, Function.update_idem]
    rw [Function.comp_update]
    apply Function.update_eq_self_iff.mpr
    rw [Function.update_of_ne hne]
    rfl
  · exact hforward

public theorem neighbour_allows_reverse
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (hallows : tape.read.boundary.allows travel = true) :
    (outgoingNeighbourCode travel tape).boundary.allows travel.reverse = true := by
  obtain ⟨targetHead, hnext⟩ :=
    (allows_iff_exists_nextHead tape hwell travel).mp hallows
  let moved := tape.moveHead travel.toDir
  have hmovedHead : moved.head = targetHead :=
    BoundedTapeMemory.moveHead_eq_of_nextHead tape travel hnext
  have hmovedWell : WellBoundaryCoded moved :=
    wellBoundaryCoded_moveHead tape hwell travel.toDir
  apply (allows_iff_exists_nextHead moved hmovedWell travel.reverse).mpr
  refine ⟨tape.head, ?_⟩
  rw [hmovedHead]
  exact (BoundedTapeMemory.nextHead_reverse_iff travel tape.head targetHead).mp hnext

/-- Exact six-edge witness for a genuine outgoing departure port. -/
public theorem exists_steps_dispatch_departure_outgoing
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .departure old written travel))
    (hallows : tape.read.boundary.allows travel = true) :
    ∃ first second third fourth fifth :
        DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n,
      LBA.Step (rawMachine machine)
          (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
          first ∧
      LBA.Step (rawMachine machine) first second ∧
      LBA.Step (rawMachine machine) second third ∧
      LBA.Step (rawMachine machine) third fourth ∧
      LBA.Step (rawMachine machine) fourth fifth ∧
      LBA.Step (rawMachine machine) fifth
        (encodePortCfg phase
          (((target, (tape.write written).moveHead travel.toDir),
            .incoming endpoint))) ∧
      NoncanonicalCore first ∧ NoncanonicalCore second ∧
      NoncanonicalCore third ∧ NoncanonicalCore fourth ∧
      NoncanonicalCore fifth := by
  have hold : old = tape.read := by
    have h := edge_old_eq_of_walker_transition machine htransition
    simpa using h
  subst old
  change (walker machine).transition endpoint (tape.contents tape.head) =
    some (target, .departure (tape.contents tape.head) written travel) at htransition
  change (tape.contents tape.head).boundary.allows travel = true at hallows
  let edge : Edge T Gamma Q :=
    { source := endpoint, target := target,
      direction := .departure tape.read written travel }
  have hinside : LBA.movesInside tape travel.toDir :=
    movesInside_toDir_of_allows tape hwell travel hallows
  have hneighbour :
      (outgoingNeighbourCode travel tape).boundary.allows travel.reverse = true :=
    neighbour_allows_reverse travel tape hwell hallows
  have hwrittenBoundary : written.boundary = tape.read.boundary := by
    have hboundary :=
      edge_written_boundary_eq_of_walker_transition machine htransition
    simpa using hboundary
  have hwrittenAllows : written.boundary.allows travel = true := by
    rw [hwrittenBoundary]
    exact hallows
  have htargetDirection : target.2 =
      .departure tape.read written travel := by
    exact (BoundedTapeController.machine
      (markedMachine machine)).directionLiftArrival.transition_incoming htransition
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.outgoingAtNeighbour edge)
      (outgoingAfterDeparture edge travel tape)
  let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg phase (.outgoingAtDeparture edge)
      (outgoingAfterNeighbour edge travel tape)
  let third : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.outgoingRestoreNeighbour edge)
      (outgoingAfterRestoreDeparture edge written travel tape)
  let fourth : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg phase (.outgoingValidateAtDeparture edge)
      (outgoingAfterReturnTag edge written travel tape)
  let fifth : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.incomingReturnAtTarget edge)
      (outgoingAfterValidatedDeparture edge written travel tape)
  have hfirst : LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      first := by
    refine ⟨nextState phase (.outgoingAtNeighbour edge),
      encodeWork (.outgoingDeparture edge), travel.toDir, ?_, ?_⟩
    · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
        edge, htransition, hallows]
    · simp [first, outgoingAfterDeparture, protocolCfg, nextState]
  have hsecond : LBA.Step (rawMachine machine) first second := by
    refine ⟨nextState (!phase) (.outgoingAtDeparture edge),
      encodeWork (.outgoingNeighbour edge (outgoingNeighbourCode travel tape)),
      travel.reverse.toDir, ?_, ?_⟩
    · simp only [first, protocolCfg]
      rw [outgoingAfterDeparture_read edge travel tape hinside]
      simp [rawMachine, transition, oneOutput, edge,
        hneighbour]
    · simp [first, second, outgoingAfterNeighbour, protocolCfg, nextState]
  have hthird : LBA.Step (rawMachine machine) second third := by
    refine ⟨nextState phase (.outgoingRestoreNeighbour edge),
      encodePlain written, travel.toDir, ?_, ?_⟩
    · simp only [second, protocolCfg]
      rw [outgoingAfterNeighbour_read edge travel tape hinside]
      simp [rawMachine, transition, oneOutput, edge,
        Edge.Enabled, Edge.old, htransition, decodeWork, encodeWork]
    · simp [second, third, outgoingAfterRestoreDeparture, protocolCfg,
        nextState]
  have hfourth : LBA.Step (rawMachine machine) third fourth := by
    refine ⟨nextState (!phase) (.outgoingValidateAtDeparture edge),
      encodeWork (.incomingTarget edge (outgoingNeighbourCode travel tape)),
      travel.reverse.toDir, ?_, ?_⟩
    · simp only [third, protocolCfg]
      rw [outgoingAfterRestoreDeparture_read edge written travel tape hinside]
      simp [rawMachine, transition, oneOutput, edge,
        Edge.Enabled, Edge.old, htransition, hneighbour,
        decodeWork, encodeWork]
    · simp [third, fourth, outgoingAfterReturnTag, protocolCfg, nextState]
  have hfifth : LBA.Step (rawMachine machine) fourth fifth := by
    refine ⟨nextState phase (.incomingReturnAtTarget edge),
      encodePlain written, travel.toDir, ?_, ?_⟩
    · simp only [fourth, protocolCfg]
      rw [outgoingAfterReturnTag_read edge written travel tape hinside]
      simp [rawMachine, transition, oneOutput, edge, Edge.Enabled, Edge.old,
        htransition, hwrittenAllows]
    · simp [fourth, fifth, outgoingAfterValidatedDeparture, protocolCfg,
        nextState]
  have hsixth : LBA.Step (rawMachine machine) fifth
      (encodePortCfg phase
        (((target, (tape.write written).moveHead travel.toDir),
          .incoming endpoint))) := by
    refine ⟨nextState (!phase) (.canonical target (.incoming endpoint)),
      encodePlain (outgoingNeighbourCode travel tape), .stay, ?_, ?_⟩
    · simp only [fifth, protocolCfg]
      rw [outgoingAfterValidatedDeparture_read edge written travel tape hinside]
      simp [rawMachine, transition, oneOutput, edge, htargetDirection,
        hneighbour, Edge.ofIncoming, decodeWork, encodeWork]
    · simp only [fifth, protocolCfg, encodePortCfg, nextState, Bool.not_not]
      congr 1
      rw [moveHead_stay]
      rw [outgoingAfterReturnErase_eq edge written travel tape hinside]
      exact (outgoingAfterFinish_eq edge written travel tape hinside).symm
  exact ⟨first, second, third, fourth, fifth, hfirst, hsecond, hthird,
    hfourth, hfifth, hsixth,
    by simp [NoncanonicalCore, first, protocolCfg],
    by simp [NoncanonicalCore, second, protocolCfg],
    by simp [NoncanonicalCore, third, protocolCfg],
    by simp [NoncanonicalCore, fourth, protocolCfg],
    by simp [NoncanonicalCore, fifth, protocolCfg]⟩

/-- Exact six-edge implementation of a genuine outgoing departure port. -/
public theorem reaches_dispatch_departure_outgoing
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint target : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (htransition : (walker machine).transition endpoint tape.read =
      some (target, .departure old written travel))
    (hallows : tape.read.boundary.allows travel = true) :
    LBA.Reaches (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
      (encodePortCfg phase
        (((target, (tape.write written).moveHead travel.toDir),
          .incoming endpoint))) := by
  obtain ⟨first, second, third, fourth, fifth, hfirst, hsecond, hthird,
      hfourth, hfifth, hsixth, _, _, _, _, _⟩ :=
    exists_steps_dispatch_departure_outgoing machine phase endpoint target
      old written travel tape hwell htransition hallows
  exact (ReflTransGen.single hfirst).tail hsecond |>.tail hthird |>.tail hfourth
    |>.tail hfifth |>.tail hsixth

/-! ## Directional incoming probe tapes -/

@[expose]
public def incomingCandidateCode
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) : PlainCode T Gamma :=
  (target.moveHead travel.reverse.toDir).read

@[expose]
public def incomingAfterTargetTag
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((encodeTape target).write (encodeWork (.incomingTarget edge target.read)))
    |>.moveHead travel.reverse.toDir

@[expose]
public def incomingAfterValidInspect
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((incomingAfterTargetTag edge travel target).write
    (encodeWork (.incomingSource edge))) |>.moveHead travel.toDir

@[expose]
public def incomingAfterValidTargetRestore
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((incomingAfterValidInspect edge travel target).write
    (encodePlain target.read)) |>.moveHead travel.reverse.toDir

@[expose]
public def incomingAfterValidFinish
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (old : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  (incomingAfterValidTargetRestore edge travel target).write (encodePlain old)

@[expose]
public def incomingAfterInvalidInspect
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((incomingAfterTargetTag edge travel target).write
    (encodeWork (.incomingInvalidSource edge
      (incomingCandidateCode travel target)))) |>.moveHead travel.toDir

@[expose]
public def incomingAfterInvalidRetagTarget
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((incomingAfterInvalidInspect edge travel target).write
    (encodeWork (.incomingTarget edge target.read)))
      |>.moveHead travel.reverse.toDir

@[expose]
public def incomingAfterInvalidRestoreCandidate
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  ((incomingAfterInvalidRetagTarget edge travel target).write
    (encodePlain (incomingCandidateCode travel target)))
      |>.moveHead travel.toDir

@[expose]
public def incomingAfterInvalidFinish
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (Alphabet T Gamma Q) n :=
  (incomingAfterInvalidRestoreCandidate edge travel target).write
    (encodePlain target.read)

public theorem incomingAfterTargetTag_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    (incomingAfterTargetTag edge travel target).read =
      encodePlain (incomingCandidateCode travel target) := by
  classical
  change Function.update (encodePlain ∘ target.contents) target.head
      (encodeWork (.incomingTarget edge target.read))
      (target.moveHead travel.reverse.toDir).head =
    encodePlain (target.contents (target.moveHead travel.reverse.toDir).head)
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne target travel.reverse.toDir hinside)]
  rfl

public theorem incomingAfterValidInspect_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    (incomingAfterValidInspect edge travel target).read =
      encodeWork (.incomingTarget edge target.read) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  change Function.update
      (Function.update (encodePlain ∘ target.contents) target.head
        (encodeWork (.incomingTarget edge target.read)))
      (target.moveHead travel.reverse.toDir).head
      (encodeWork (.incomingSource edge))
      ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head = _
  rw [hback]
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne target travel.reverse.toDir hinside).symm]
  simp

public theorem incomingAfterValidTargetRestore_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    (incomingAfterValidTargetRestore edge travel target).read =
      encodeWork (.incomingSource edge) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  have hroundtrip :
      (target.moveHead travel.reverse.toDir).moveHead travel.toDir = target := by
    simpa only [reverseDirection_toDir,
      BoundedTapeMemory.Travel.reverse_reverse] using
      (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  have hforward :
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).head =
          (target.moveHead travel.reverse.toDir).head := by
    rw [hroundtrip]
  change Function.update
      (Function.update
        (Function.update (encodePlain ∘ target.contents) target.head
          (encodeWork (.incomingTarget edge target.read)))
        (target.moveHead travel.reverse.toDir).head
        (encodeWork (.incomingSource edge)))
      ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head
      (encodePlain target.read)
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).head = _
  rw [hback, hforward]
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne target travel.reverse.toDir hinside)]
  simp

public theorem incomingAfterValidFinish_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (old : PlainCode T Gamma)
    (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    incomingAfterValidFinish edge old travel target =
      encodeTape ((target.moveHead travel.reverse.toDir).write old) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  have hroundtrip :
      (target.moveHead travel.reverse.toDir).moveHead travel.toDir = target := by
    simpa only [reverseDirection_toDir,
      BoundedTapeMemory.Travel.reverse_reverse] using
      (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  have hcandidate :
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).head =
          (target.moveHead travel.reverse.toDir).head := by
    rw [hroundtrip]
  apply BoundedTapeMemory.eq_of_contents_head
  · change Function.update
        (Function.update
          (Function.update
            (Function.update (encodePlain ∘ target.contents) target.head
              (encodeWork (.incomingTarget edge target.read)))
            (target.moveHead travel.reverse.toDir).head
            (encodeWork (.incomingSource edge)))
          ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head
          (encodePlain target.read))
        (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
          travel.reverse.toDir).head
        (encodePlain old) =
      encodePlain ∘ Function.update target.contents
        (target.moveHead travel.reverse.toDir).head old
    rw [hback, hcandidate]
    have hne := LBA.movesInside_head_ne target travel.reverse.toDir hinside
    rw [Function.update_comm hne.symm, Function.update_idem]
    rw [Function.update_comm hne, Function.update_idem]
    rw [Function.comp_update]
    have hrestore : Function.update
        ((encodePlain (Q := Q)) ∘ target.contents) target.head
        (encodePlain (Q := Q) target.read) =
          (encodePlain (Q := Q)) ∘ target.contents := by
      apply Function.update_eq_self_iff.mpr
      rfl
    rw [hrestore]
  · exact hcandidate

public theorem incomingAfterInvalidInspect_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    (incomingAfterInvalidInspect edge travel target).read =
      encodeWork (.incomingTarget edge target.read) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  change Function.update
      (Function.update (encodePlain ∘ target.contents) target.head
        (encodeWork (.incomingTarget edge target.read)))
      (target.moveHead travel.reverse.toDir).head
      (encodeWork (.incomingInvalidSource edge
        (incomingCandidateCode travel target)))
      ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head = _
  rw [hback]
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne target travel.reverse.toDir hinside).symm]
  simp

public theorem incomingAfterInvalidRetagTarget_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    (incomingAfterInvalidRetagTarget edge travel target).read =
      encodeWork (.incomingInvalidSource edge
        (incomingCandidateCode travel target)) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  have hroundtrip :
      (target.moveHead travel.reverse.toDir).moveHead travel.toDir = target := by
    simpa only [reverseDirection_toDir,
      BoundedTapeMemory.Travel.reverse_reverse] using
      (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  have hcandidate :
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).head =
          (target.moveHead travel.reverse.toDir).head := by rw [hroundtrip]
  change Function.update
      (Function.update
        (Function.update (encodePlain ∘ target.contents) target.head
          (encodeWork (.incomingTarget edge target.read)))
        (target.moveHead travel.reverse.toDir).head
        (encodeWork (.incomingInvalidSource edge
          (incomingCandidateCode travel target))))
      ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head
      (encodeWork (.incomingTarget edge target.read))
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).head = _
  rw [hcandidate]
  rw [hback]
  rw [Function.update_of_ne
    (LBA.movesInside_head_ne target travel.reverse.toDir hinside)]
  simp

public theorem incomingAfterInvalidRestoreCandidate_read
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    (incomingAfterInvalidRestoreCandidate edge travel target).read =
      encodeWork (.incomingTarget edge target.read) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  have hroundtrip :
      (target.moveHead travel.reverse.toDir).moveHead travel.toDir = target := by
    simpa only [reverseDirection_toDir,
      BoundedTapeMemory.Travel.reverse_reverse] using
      (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  have hcandidateTape :
      ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
          travel.reverse.toDir = target.moveHead travel.reverse.toDir :=
    congrArg (fun tape => tape.moveHead travel.reverse.toDir) hroundtrip
  have htargetTape :
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
          travel.reverse.toDir).moveHead travel.toDir = target := by
    rw [hcandidateTape, hroundtrip]
  change Function.update
      (Function.update
        (Function.update
          (Function.update (encodePlain ∘ target.contents) target.head
            (encodeWork (.incomingTarget edge target.read)))
          (target.moveHead travel.reverse.toDir).head
          (encodeWork (.incomingInvalidSource edge
            (incomingCandidateCode travel target))))
        ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head
        (encodeWork (.incomingTarget edge target.read)))
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).head
      (encodePlain (incomingCandidateCode travel target))
      ((((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).moveHead travel.toDir).head = _
  rw [htargetTape, hcandidateTape, hroundtrip]
  have hne := LBA.movesInside_head_ne target travel.reverse.toDir hinside
  simpa [incomingCandidateCode, DLBA.BoundedTape.read] using
    (alternating_restore_read_first
      ((encodePlain (Q := Q)) ∘ target.contents)
      target.head (target.moveHead travel.reverse.toDir).head hne.symm
      (encodeWork (.incomingTarget edge target.read))
      (encodeWork (.incomingInvalidSource edge
        (incomingCandidateCode travel target))))

public theorem incomingAfterInvalidFinish_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (edge : Edge T Gamma Q) (travel : BoundedTapeMemory.Travel)
    (target : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hinside : LBA.movesInside target travel.reverse.toDir) :
    incomingAfterInvalidFinish edge travel target = encodeTape target := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  simp only [reverseDirection_toDir, BoundedTapeMemory.Travel.reverse_reverse] at hback
  have hroundtrip :
      (target.moveHead travel.reverse.toDir).moveHead travel.toDir = target := by
    simpa only [reverseDirection_toDir,
      BoundedTapeMemory.Travel.reverse_reverse] using
      (LBA.moveHead_reverseDirection_moveHead target travel.reverse.toDir hinside)
  have hcandidateTape :
      ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
          travel.reverse.toDir = target.moveHead travel.reverse.toDir :=
    congrArg (fun tape => tape.moveHead travel.reverse.toDir) hroundtrip
  have htargetTape :
      (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
          travel.reverse.toDir).moveHead travel.toDir = target := by
    rw [hcandidateTape, hroundtrip]
  apply BoundedTapeMemory.eq_of_contents_head
  · change Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update (encodePlain ∘ target.contents) target.head
                (encodeWork (.incomingTarget edge target.read)))
              (target.moveHead travel.reverse.toDir).head
              (encodeWork (.incomingInvalidSource edge
                (incomingCandidateCode travel target))))
            ((target.moveHead travel.reverse.toDir).moveHead travel.toDir).head
            (encodeWork (.incomingTarget edge target.read)))
          (((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
            travel.reverse.toDir).head
          (encodePlain (incomingCandidateCode travel target)))
        ((((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
          travel.reverse.toDir).moveHead travel.toDir).head
        (encodePlain target.read) = encodePlain ∘ target.contents
    rw [htargetTape, hcandidateTape, hroundtrip]
    have hne := LBA.movesInside_head_ne target travel.reverse.toDir hinside
    simpa [incomingCandidateCode, DLBA.BoundedTape.read] using
      (alternating_updates_restore
        ((encodePlain (Q := Q)) ∘ target.contents)
        target.head (target.moveHead travel.reverse.toDir).head hne.symm
        (encodeWork (.incomingTarget edge target.read))
        (encodeWork (.incomingInvalidSource edge
          (incomingCandidateCode travel target))))
  · change
      ((((target.moveHead travel.reverse.toDir).moveHead travel.toDir).moveHead
        travel.reverse.toDir).moveHead travel.toDir).head = target.head
    exact congrArg DLBA.BoundedTape.head htargetTape

/-! ## Directional incoming protocol paths -/

/-- Exact four-edge witness for a valid incoming probe. -/
public theorem exists_steps_dispatch_departure_incoming_valid
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (targetTape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded targetTape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : targetTape.read.boundary.allows travel.reverse = true)
    (hvalid : incomingCandidateCode travel targetTape = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true)
    (holdAllows : old.boundary.allows travel = true) :
    ∃ first second third :
        DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n,
      LBA.Step (rawMachine machine)
          (protocolCfg phase (.dispatch endpoint (.incoming source))
            (encodeTape targetTape)) first ∧
      LBA.Step (rawMachine machine) first second ∧
      LBA.Step (rawMachine machine) second third ∧
      LBA.Step (rawMachine machine) third
        (encodePortCfg phase
          (((source, (targetTape.moveHead travel.reverse.toDir).write old),
            .outgoing))) ∧
      NoncanonicalCore first ∧ NoncanonicalCore second ∧
      NoncanonicalCore third := by
  change endpoint.2 = .departure old written travel at hdirection
  change (targetTape.contents targetTape.head).boundary.allows
    travel.reverse = true at hallows
  have hwrittenAllows : written.boundary.allows travel = true := by
    rw [← hvalid.1]
    exact hvalid.2.2
  have hedgeEnabled : Edge.Enabled machine
      ({ source := source, target := endpoint, direction := .departure old written travel } :
        Edge T Gamma Q) := by
    simpa only [Edge.ofIncoming, hdirection] using hvalid.2.1
  let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
  have hinside : LBA.movesInside targetTape travel.reverse.toDir := by
    apply movesInside_toDir_of_allows targetTape
      (travel := travel.reverse)
    · exact hwell
    · simpa using hallows
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.incomingInspect edge)
      (incomingAfterTargetTag edge travel targetTape)
  let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg phase (.incomingValidAtTarget edge)
      (incomingAfterValidInspect edge travel targetTape)
  let third : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.incomingValidFinish edge)
      (incomingAfterValidTargetRestore edge travel targetTape)
  have hfirst : LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape targetTape)) first := by
    refine ⟨nextState phase (.incomingInspect edge),
      encodeWork (.incomingTarget edge targetTape.read),
      travel.reverse.toDir, ?_, ?_⟩
    · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
        edge, Edge.ofIncoming, hdirection, hallows]
    · simp [first, incomingAfterTargetTag, protocolCfg, nextState]
  have hsecond : LBA.Step (rawMachine machine) first second := by
    refine ⟨nextState (!phase) (.incomingValidAtTarget edge),
      encodeWork (.incomingSource edge), travel.toDir, ?_, ?_⟩
    · simp only [first, protocolCfg]
      rw [incomingAfterTargetTag_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, Edge.ofIncoming,
        hdirection, hvalid, hwrittenAllows, hedgeEnabled]
    · simp [first, second, incomingAfterValidInspect, protocolCfg, nextState]
  have hthird : LBA.Step (rawMachine machine) second third := by
    refine ⟨nextState phase (.incomingValidFinish edge),
      encodePlain targetTape.read, travel.reverse.toDir, ?_, ?_⟩
    · simp only [second, protocolCfg]
      rw [incomingAfterValidInspect_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, Edge.ofIncoming,
        hdirection, hedgeEnabled,
        decodeWork, encodeWork]
    · simp [second, third, incomingAfterValidTargetRestore, protocolCfg,
        nextState]
  have hfourth : LBA.Step (rawMachine machine) third
      (encodePortCfg phase
        (((source, (targetTape.moveHead travel.reverse.toDir).write old),
          .outgoing))) := by
    refine ⟨nextState (!phase) (.canonical source .outgoing),
      encodePlain old, .stay, ?_, ?_⟩
    · simp only [third, protocolCfg]
      rw [incomingAfterValidTargetRestore_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, hdirection,
        holdAllows, hedgeEnabled, Edge.old, Edge.ofIncoming, decodeWork,
        encodeWork]
    · simp only [third, protocolCfg, encodePortCfg, nextState, Bool.not_not]
      congr 1
      rw [moveHead_stay]
      exact (incomingAfterValidFinish_eq edge old travel targetTape hinside).symm
  exact ⟨first, second, third, hfirst, hsecond, hthird, hfourth,
    by simp [NoncanonicalCore, first, protocolCfg],
    by simp [NoncanonicalCore, second, protocolCfg],
    by simp [NoncanonicalCore, third, protocolCfg]⟩

/-- Exact four-edge valid incoming probe. -/
public theorem reaches_dispatch_departure_incoming_valid
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (targetTape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded targetTape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : targetTape.read.boundary.allows travel.reverse = true)
    (hvalid : incomingCandidateCode travel targetTape = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true)
    (holdAllows : old.boundary.allows travel = true) :
    LBA.Reaches (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape targetTape))
      (encodePortCfg phase
        (((source, (targetTape.moveHead travel.reverse.toDir).write old),
          .outgoing))) := by
  obtain ⟨first, second, third, hfirst, hsecond, hthird, hfourth,
      _, _, _⟩ :=
    exists_steps_dispatch_departure_incoming_valid machine phase endpoint source
      old written travel targetTape hwell hdirection hallows hvalid holdAllows
  exact (ReflTransGen.single hfirst).tail hsecond |>.tail hthird |>.tail hfourth

/-- Exact five-edge witness for a failed incoming probe.  The candidate and
target cells are both restored and the head returns to the original incoming
port. -/
public theorem exists_steps_dispatch_departure_incoming_invalid
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (targetTape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded targetTape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : targetTape.read.boundary.allows travel.reverse = true)
    (hinvalid : ¬(incomingCandidateCode travel targetTape = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true)) :
    ∃ first second third fourth :
        DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n,
      LBA.Step (rawMachine machine)
          (protocolCfg phase (.dispatch endpoint (.incoming source))
            (encodeTape targetTape)) first ∧
      LBA.Step (rawMachine machine) first second ∧
      LBA.Step (rawMachine machine) second third ∧
      LBA.Step (rawMachine machine) third fourth ∧
      LBA.Step (rawMachine machine) fourth
        (encodePortCfg (!phase)
          (((endpoint, targetTape), .incoming source))) ∧
      NoncanonicalCore first ∧ NoncanonicalCore second ∧
      NoncanonicalCore third ∧ NoncanonicalCore fourth := by
  change endpoint.2 = .departure old written travel at hdirection
  change (targetTape.contents targetTape.head).boundary.allows
    travel.reverse = true at hallows
  have hinvalidExplicit : ¬(incomingCandidateCode travel targetTape = written ∧
      Edge.Enabled machine
        ({ source := source, target := endpoint, direction := .departure old written travel } :
          Edge T Gamma Q) ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true) := by
    simpa only [Edge.ofIncoming, hdirection] using hinvalid
  let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
  have hinside : LBA.movesInside targetTape travel.reverse.toDir :=
    movesInside_toDir_of_allows targetTape hwell travel.reverse hallows
  let first : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase) (.incomingInspect edge)
      (incomingAfterTargetTag edge travel targetTape)
  let second : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg phase
      (.incomingInvalidAtTarget edge (incomingCandidateCode travel targetTape))
      (incomingAfterInvalidInspect edge travel targetTape)
  let third : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg (!phase)
      (.incomingInvalidAtSource edge (incomingCandidateCode travel targetTape))
      (incomingAfterInvalidRetagTarget edge travel targetTape)
  let fourth : DLBA.Cfg (Alphabet T Gamma Q) (State T Gamma Q) n :=
    protocolCfg phase
      (.incomingReturnAtTarget edge)
      (incomingAfterInvalidRestoreCandidate edge travel targetTape)
  have hfirst : LBA.Step (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape targetTape)) first := by
    refine ⟨nextState phase (.incomingInspect edge),
      encodeWork (.incomingTarget edge targetTape.read),
      travel.reverse.toDir, ?_, ?_⟩
    · simp [rawMachine, transition, protocolCfg, oneOutput, encodeTape,
        edge, Edge.ofIncoming, hdirection, hallows]
    · simp [first, incomingAfterTargetTag, protocolCfg, nextState]
  have hsecond : LBA.Step (rawMachine machine) first second := by
    refine ⟨nextState (!phase)
        (.incomingInvalidAtTarget edge (incomingCandidateCode travel targetTape)),
      encodeWork (.incomingInvalidSource edge
        (incomingCandidateCode travel targetTape)), travel.toDir, ?_, ?_⟩
    · simp only [first, protocolCfg]
      rw [incomingAfterTargetTag_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, Edge.ofIncoming,
        hdirection, hinvalidExplicit]
    · simp [first, second, incomingAfterInvalidInspect, protocolCfg, nextState]
  have hthird : LBA.Step (rawMachine machine) second third := by
    refine ⟨nextState phase
        (.incomingInvalidAtSource edge (incomingCandidateCode travel targetTape)),
      encodeWork (.incomingTarget edge targetTape.read),
      travel.reverse.toDir, ?_, ?_⟩
    · simp only [second, protocolCfg]
      rw [incomingAfterInvalidInspect_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, Edge.ofIncoming, hdirection,
        decodeWork, encodeWork]
    · simp [second, third, incomingAfterInvalidRetagTarget, protocolCfg,
        nextState]
  have hfourth : LBA.Step (rawMachine machine) third fourth := by
    refine ⟨nextState (!phase)
        (.incomingReturnAtTarget edge),
      encodePlain (incomingCandidateCode travel targetTape), travel.toDir,
      ?_, ?_⟩
    · simp only [third, protocolCfg]
      rw [incomingAfterInvalidRetagTarget_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, Edge.ofIncoming, hdirection,
        hinvalidExplicit, Edge.written, decodeWork, encodeWork]
    · simp [third, fourth, incomingAfterInvalidRestoreCandidate,
        protocolCfg, nextState]
  have hfifth : LBA.Step (rawMachine machine) fourth
      (encodePortCfg (!phase) (((endpoint, targetTape), .incoming source))) := by
    refine ⟨nextState phase (.canonical endpoint (.incoming source)),
      encodePlain targetTape.read, .stay, ?_, ?_⟩
    · simp only [fourth, protocolCfg]
      rw [incomingAfterInvalidRestoreCandidate_read edge travel targetTape hinside]
      simp [rawMachine, transition, oneOutput, edge, hdirection, hallows,
        Edge.ofIncoming, decodeWork, encodeWork]
    · simp only [fourth, protocolCfg, encodePortCfg, nextState]
      congr 1
      rw [moveHead_stay]
      exact (incomingAfterInvalidFinish_eq edge travel targetTape hinside).symm
  exact ⟨first, second, third, fourth, hfirst, hsecond, hthird, hfourth,
    hfifth,
    by simp [NoncanonicalCore, first, protocolCfg],
    by simp [NoncanonicalCore, second, protocolCfg],
    by simp [NoncanonicalCore, third, protocolCfg],
    by simp [NoncanonicalCore, fourth, protocolCfg]⟩

/-- Exact five-edge failed incoming probe.  The candidate and target cells are
both restored and the head returns to the original incoming port. -/
public theorem reaches_dispatch_departure_incoming_invalid
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (targetTape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded targetTape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : targetTape.read.boundary.allows travel.reverse = true)
    (hinvalid : ¬(incomingCandidateCode travel targetTape = written ∧
      (Edge.ofIncoming endpoint source).Enabled machine ∧
      (incomingCandidateCode travel targetTape).boundary.allows travel = true)) :
    LBA.Reaches (rawMachine machine)
      (protocolCfg phase (.dispatch endpoint (.incoming source))
        (encodeTape targetTape))
      (encodePortCfg (!phase) (((endpoint, targetTape), .incoming source))) := by
  obtain ⟨first, second, third, fourth, hfirst, hsecond, hthird, hfourth,
      hfifth, _, _, _, _⟩ :=
    exists_steps_dispatch_departure_incoming_invalid machine phase endpoint source
      old written travel targetTape hwell hdirection hallows hinvalid
  exact (ReflTransGen.single hfirst).tail hsecond |>.tail hthird |>.tail hfourth
    |>.tail hfifth

/-! ## Dispatch-level semantic assembly -/

/-- The semantic incoming-source test for a stationary remembered edge is
exactly the symbol-and-enabled test used by the raw dispatch table. -/
public theorem incomingSource_stationary_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .stationary old written) :
    LocalPort.incomingSource
        (walker machine) (BoundedTapeMemory.graph (PlainCode T Gamma) n)
        (BoundedTapeController.machine
          (markedMachine machine)).directionLiftArrival
        (endpoint, tape) source =
      if tape.read = written ∧
          (Edge.ofIncoming endpoint source).Enabled machine then
        some (source, tape.write old)
      else none := by
  change endpoint.2 = .stationary old written at hdirection
  by_cases hread : tape.contents tape.head = written <;>
    simp [LocalPort.incomingSource, LocalPort.predecessorCandidate,
      BoundedTapeMemory.graph, BoundedTapeMemory.Direction.opposite,
      BoundedTapeMemory.move, Machine.directionLiftArrival, hdirection,
      Edge.Enabled, Edge.ofIncoming, Edge.old, hread,
      DLBA.BoundedTape.write]

/-- A physically blocked reverse probe has no semantic incoming source. -/
public theorem incomingSource_departure_blocked_eq_none
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hblocked : tape.read.boundary.allows travel.reverse = false) :
    LocalPort.incomingSource
        (walker machine) (BoundedTapeMemory.graph (PlainCode T Gamma) n)
        (BoundedTapeController.machine
          (markedMachine machine)).directionLiftArrival
        (endpoint, tape) source = none := by
  change endpoint.2 = .departure old written travel at hdirection
  have hprevious : BoundedTapeMemory.previousHead travel tape.head = none := by
    unfold BoundedTapeMemory.previousHead
    cases hnext : BoundedTapeMemory.nextHead travel.reverse tape.head with
    | none => rfl
    | some candidateHead =>
        have hallows := (allows_iff_exists_nextHead tape hwell travel.reverse).2
          ⟨candidateHead, hnext⟩
        rw [hblocked] at hallows
        simp at hallows
  simp [LocalPort.incomingSource, LocalPort.predecessorCandidate,
    BoundedTapeMemory.graph, BoundedTapeMemory.Direction.opposite,
    BoundedTapeMemory.move, Machine.directionLiftArrival, hdirection,
    hprevious]

/-- With a genuine reverse neighbour, the semantic incoming-source test is
exactly the candidate-symbol and enabled-edge test used by the raw probe. -/
public theorem incomingSource_departure_allowed_eq
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .departure old written travel)
    (hallows : tape.read.boundary.allows travel.reverse = true) :
    LocalPort.incomingSource
        (walker machine) (BoundedTapeMemory.graph (PlainCode T Gamma) n)
        (BoundedTapeController.machine
          (markedMachine machine)).directionLiftArrival
        (endpoint, tape) source =
      if incomingCandidateCode travel tape = written ∧
          (Edge.ofIncoming endpoint source).Enabled machine then
        some (source, (tape.moveHead travel.reverse.toDir).write old)
      else none := by
  change endpoint.2 = .departure old written travel at hdirection
  obtain ⟨candidateHead, hprevious⟩ :=
    (allows_iff_exists_nextHead tape hwell travel.reverse).1 hallows
  have hmovedHead : (tape.moveHead travel.reverse.toDir).head = candidateHead :=
    BoundedTapeMemory.moveHead_eq_of_nextHead tape travel.reverse hprevious
  by_cases hcandidate : incomingCandidateCode travel tape = written
  · have hwritten : tape.contents candidateHead = written := by
      change tape.contents (tape.moveHead travel.reverse.toDir).head = written at hcandidate
      rw [hmovedHead] at hcandidate
      exact hcandidate
    have hmove : BoundedTapeMemory.move (.arrival old written travel) tape =
        some ((tape.moveHead travel.reverse.toDir).write old) := by
      simpa [BoundedTapeMemory.rawArrivalCandidate] using
        BoundedTapeMemory.move_arrival_eq_raw_probe_success
          old written travel tape hprevious hwritten
    simp [LocalPort.incomingSource, LocalPort.predecessorCandidate,
      BoundedTapeMemory.graph, BoundedTapeMemory.Direction.opposite,
      Machine.directionLiftArrival, hdirection, hmove, hcandidate,
      Edge.Enabled, Edge.ofIncoming, Edge.old, DLBA.BoundedTape.write]
  · have hne : tape.contents candidateHead ≠ written := by
      intro hwritten
      apply hcandidate
      change tape.contents (tape.moveHead travel.reverse.toDir).head = written
      rw [hmovedHead]
      exact hwritten
    have hmove : BoundedTapeMemory.move (.arrival old written travel) tape = none :=
      BoundedTapeMemory.move_arrival_eq_none_of_candidate_ne
        old written travel tape hprevious hne
    simp [LocalPort.incomingSource, LocalPort.predecessorCandidate,
      BoundedTapeMemory.graph, BoundedTapeMemory.Direction.opposite,
      Machine.directionLiftArrival, hdirection, hmove, hcandidate]

/-- A remembered arrival name cannot validate as an incoming source because
the forward marked walker never emits arrival operations. -/
public theorem incomingSource_arrival_eq_none
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (endpoint source : LiftState T Gamma Q)
    (old written : PlainCode T Gamma) (travel : BoundedTapeMemory.Travel)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hdirection : (Edge.ofIncoming endpoint source).direction =
      .arrival old written travel) :
    LocalPort.incomingSource
        (walker machine) (BoundedTapeMemory.graph (PlainCode T Gamma) n)
        (BoundedTapeController.machine
          (markedMachine machine)).directionLiftArrival
        (endpoint, tape) source = none := by
  change endpoint.2 = .arrival old written travel at hdirection
  unfold LocalPort.incomingSource
  cases hcandidate : LocalPort.predecessorCandidate
      (walker machine) (BoundedTapeMemory.graph (PlainCode T Gamma) n)
      (BoundedTapeController.machine
        (markedMachine machine)).directionLiftArrival
      (endpoint, tape) source with
  | none => simp
  | some candidate =>
      have hne : (walker machine).transition candidate.1
          ((BoundedTapeMemory.graph (PlainCode T Gamma) n).observe candidate.2) ≠
          some (endpoint,
            (BoundedTapeController.machine
              (markedMachine machine)).directionLiftArrival.incoming endpoint) := by
        simp only [BoundedTapeMemory.graph_observe,
          Machine.directionLiftArrival, hdirection]
        exact walker_transition_ne_arrival machine candidate.1 endpoint
          candidate.2.read old written travel
      have hne' : (walker machine).transition candidate.1
          (candidate.2.contents candidate.2.head) ≠
          some (endpoint, .arrival old written travel) := by
        simpa only [BoundedTapeMemory.graph_observe,
          Machine.directionLiftArrival, hdirection] using hne
      simp [Machine.directionLiftArrival, hdirection, hne']

/-- Every outgoing dispatch implements exactly the undoubled local-port swap,
with the final raw phase exposed existentially. -/
public theorem exists_phase_reaches_dispatch_outgoing_swap
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    ∃ finalPhase,
      LBA.Reaches (rawMachine machine)
        (protocolCfg phase (.dispatch endpoint .outgoing) (encodeTape tape))
        (encodePortCfg finalPhase
          ((ports machine n).swap (((endpoint, tape), .outgoing)))) := by
  cases htransition :
      (walker machine).transition endpoint (tape.contents tape.head) with
  | none =>
      refine ⟨!phase, ?_⟩
      have hstep := step_dispatch_outgoing_none machine phase endpoint tape htransition
      simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
        Machine.next, htransition] using (ReflTransGen.single hstep)
  | some output =>
      rcases output with ⟨target, direction⟩
      cases direction with
      | stationary old written =>
          have hpath := reaches_dispatch_stationary_outgoing machine phase
            endpoint target old written tape htransition
          refine ⟨phase, ?_⟩
          have hold : old = tape.read := by
            simpa using edge_old_eq_of_walker_transition machine htransition
          simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
            Machine.next, htransition, BoundedTapeMemory.graph,
            BoundedTapeMemory.move, DLBA.BoundedTape.read, hold] using hpath
      | departure old written travel =>
          have hold : old = tape.read := by
            simpa using edge_old_eq_of_walker_transition machine htransition
          subst old
          let edge : Edge T Gamma Q :=
            { source := endpoint, target := target,
              direction := .departure tape.read written travel }
          have henabled : edge.Enabled machine := by
            simp [Edge.Enabled, Edge.old, edge, htransition]
          have hallows : tape.read.boundary.allows travel = true := by
            simpa [edge, Edge.old] using
              edge.old_boundary_allows_of_enabled_departure machine henabled
                tape.read written travel (by rfl)
          obtain ⟨targetHead, hnext⟩ :=
            (allows_iff_exists_nextHead tape hwell travel).mp hallows
          have hmove :
              BoundedTapeMemory.move
                  (.departure tape.read written travel) tape =
                some ((tape.write written).moveHead travel.toDir) :=
            by
              simpa only [BoundedTapeMemory.graph_move] using
                BoundedTapeMemory.move_departure_eq_write_moveHead
                  tape written travel hnext
          change BoundedTapeMemory.move
              (.departure (tape.contents tape.head) written travel) tape =
            some ((tape.write written).moveHead travel.toDir) at hmove
          have hnextCfg :
              (walker machine).next
                  (BoundedTapeMemory.graph (PlainCode T Gamma) n)
                  (endpoint, tape) =
                some (target, (tape.write written).moveHead travel.toDir) := by
            simp [Machine.next, htransition, hmove]
          have hpath := reaches_dispatch_departure_outgoing machine phase
            endpoint target tape.read written travel tape hwell htransition hallows
          refine ⟨phase, ?_⟩
          simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
            hnextCfg] using hpath
      | arrival old written travel =>
          exact (walker_transition_ne_arrival machine endpoint target tape.read
            old written travel htransition).elim

/-- Every incoming dispatch implements exactly the undoubled local-port swap,
including failed probes, which restore the tape and return to the same port. -/
public theorem exists_phase_reaches_dispatch_incoming_swap
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint source : LiftState T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    ∃ finalPhase,
      LBA.Reaches (rawMachine machine)
        (protocolCfg phase (.dispatch endpoint (.incoming source))
          (encodeTape tape))
        (encodePortCfg finalPhase
          ((ports machine n).swap (((endpoint, tape), .incoming source)))) := by
  let edge : Edge T Gamma Q := Edge.ofIncoming endpoint source
  cases hdirection : edge.direction with
  | stationary old written =>
      have hsource := incomingSource_stationary_eq machine endpoint source
        old written tape (by simpa [edge] using hdirection)
      by_cases hvalid : tape.read = written ∧ edge.Enabled machine
      · rw [if_pos (by simpa [edge] using hvalid)] at hsource
        have hpath := reaches_dispatch_stationary_incoming machine phase
          endpoint source old written tape (by simpa [edge] using hdirection)
          hvalid.1 (by simpa [edge] using hvalid.2)
        refine ⟨phase, ?_⟩
        simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
          hsource] using hpath
      · rw [if_neg (by simpa [edge] using hvalid)] at hsource
        have hstep := step_dispatch_stationary_incoming_fixed machine phase
          endpoint source old written tape (by simpa [edge] using hdirection)
          (by simpa [edge] using hvalid)
        refine ⟨!phase, ?_⟩
        simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
          hsource] using (ReflTransGen.single hstep)
  | departure old written travel =>
      cases hallows : tape.read.boundary.allows travel.reverse with
      | false =>
          have hsource := incomingSource_departure_blocked_eq_none machine
            endpoint source old written travel tape hwell
              (by simpa [edge] using hdirection) hallows
          have hstep := step_dispatch_incoming_departure_blocked machine phase
            endpoint source old written travel tape
              (by simpa [edge] using hdirection) hallows
          refine ⟨!phase, ?_⟩
          simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
            hsource] using (ReflTransGen.single hstep)
      | true =>
          have hsource := incomingSource_departure_allowed_eq machine
            endpoint source old written travel tape hwell
              (by simpa [edge] using hdirection) hallows
          have hcandidateAllows :
              (incomingCandidateCode travel tape).boundary.allows travel = true := by
            have hreverse := neighbour_allows_reverse travel.reverse tape hwell hallows
            simpa [incomingCandidateCode, outgoingNeighbourCode] using hreverse
          by_cases hvalid :
              incomingCandidateCode travel tape = written ∧ edge.Enabled machine
          · rw [if_pos (by simpa [edge] using hvalid)] at hsource
            have holdAllows : old.boundary.allows travel = true := by
              have hold := edge.old_boundary_allows_of_enabled_departure
                machine hvalid.2 old written travel hdirection
              simpa [edge, Edge.old, hdirection] using hold
            have hpath := reaches_dispatch_departure_incoming_valid machine phase
              endpoint source old written travel tape hwell
              (by simpa [edge] using hdirection) hallows
              ⟨hvalid.1, by simpa [edge] using hvalid.2, hcandidateAllows⟩
              holdAllows
            refine ⟨phase, ?_⟩
            simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
              hsource] using hpath
          · rw [if_neg (by simpa [edge] using hvalid)] at hsource
            have hinvalid : ¬(incomingCandidateCode travel tape = written ∧
                (Edge.ofIncoming endpoint source).Enabled machine ∧
                (incomingCandidateCode travel tape).boundary.allows travel = true) := by
              intro hall
              apply hvalid
              exact ⟨hall.1, by simpa [edge] using hall.2.1⟩
            have hpath := reaches_dispatch_departure_incoming_invalid
              machine phase endpoint source old written travel tape hwell
              (by simpa [edge] using hdirection) hallows hinvalid
            refine ⟨!phase, ?_⟩
            simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
              hsource] using hpath
  | arrival old written travel =>
      have hsource := incomingSource_arrival_eq_none machine endpoint source
        old written travel tape (by simpa [edge] using hdirection)
      have hstep := step_dispatch_incoming_arrival machine phase endpoint source
        old written travel tape (by simpa [edge] using hdirection)
      refine ⟨!phase, ?_⟩
      simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun,
        hsource] using (ReflTransGen.single hstep)

/-- Every dispatch state reaches the exact semantic swap of its represented
undoubled local port. -/
public theorem exists_phase_reaches_dispatch_swap
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool) (endpoint : LiftState T Gamma Q) (slot : Slot T Gamma Q)
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    ∃ finalPhase,
      LBA.Reaches (rawMachine machine)
        (protocolCfg phase (.dispatch endpoint slot) (encodeTape tape))
        (encodePortCfg finalPhase
          ((ports machine n).swap (((endpoint, tape), slot)))) := by
  cases slot with
  | anchor =>
      refine ⟨!phase, ?_⟩
      have hstep := step_dispatch_anchor machine phase endpoint tape
      simpa [ports, LocalPort.ofMachine, LocalPort.swap, LocalPort.swapFun]
        using (ReflTransGen.single hstep)
  | outgoing =>
      exact exists_phase_reaches_dispatch_outgoing_swap
        machine phase endpoint tape hwell
  | incoming source =>
      exact exists_phase_reaches_dispatch_incoming_swap
        machine phase endpoint source tape hwell

/-! ## One complete undoubled Euler macro -/

/-- One undoubled local Euler edge is refined by a nonempty raw run.  The raw
phase is deliberately existential: protocol branches have different parity. -/
public theorem exists_phase_transGen_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2) :
    ∃ finalPhase,
      TransGen (LBA.Step (rawMachine machine))
        (encodePortCfg phase port)
        (encodePortCfg finalPhase ((ports machine n).euler port)) := by
  rcases port with ⟨⟨endpoint, tape⟩, slot⟩
  have hrotate := step_rotate_to_dispatch machine phase endpoint slot tape
  obtain ⟨finalPhase, hdispatch⟩ :=
    exists_phase_reaches_dispatch_swap machine (!phase) endpoint
      (rotateSlot slot) tape hwell
  refine ⟨finalPhase, ?_⟩
  simpa [PortSystem.euler, ports, LocalPort.ofMachine, LocalPort.rotate,
    rotateSlot] using (TransGen.head' hrotate hdispatch)

/-- Reflexive-transitive form of `exists_phase_transGen_euler`. -/
public theorem exists_phase_reaches_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (phase : Bool)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2) :
    ∃ finalPhase,
      LBA.Reaches (rawMachine machine)
        (encodePortCfg phase port)
        (encodePortCfg finalPhase ((ports machine n).euler port)) := by
  obtain ⟨finalPhase, hstrict⟩ :=
    exists_phase_transGen_euler machine phase port hwell
  exact ⟨finalPhase, hstrict.to_reflTransGen⟩

end

end MarkedEulerProbe

end GraphWalking

end
