module

public import Langlib.Automata.LinearBounded.GraphWalking.BoundedTapeMemory
import Mathlib.Tactic

@[expose]
public section

/-!
# A deterministic bounded-tape controller as a graph walker

This file translates an ordinary deterministic LBA transition table to the
locally reversible memory operations of `BoundedTapeMemory`.  A stationary
transition chooses a stationary rewrite; a left or right transition chooses a
departure operation whose symbol parameters are determined by the observed
cell and the transition table.

Every graph-walker step is an ordinary DLBA step.  Conversely, an ordinary
step is a graph-walker step when its enabled left/right motion genuinely stays
inside the tape.  At a physical boundary the graph operation is undefined,
whereas `DLBA.BoundedTape.moveHead` clamps.  Consequently this file does not
claim whole-machine or language equivalence for arbitrary raw clamped DLBAs.
-/

namespace GraphWalking

universe uAlphabet uState

namespace BoundedTapeController

open BoundedTapeMemory

/-- The explicitly reversible memory-operation name selected by one ordinary
write-and-move instruction. -/
@[expose]
public def operation {A : Type uAlphabet} (old written : A) :
    DLBA.Dir → BoundedTapeMemory.Direction A
  | .stay => .stationary old written
  | .left => .departure old written .left
  | .right => .departure old written .right

/-- The exact condition under which an ordinary bounded-tape direction does
not invoke physical clamping. -/
@[expose]
public def Nonclamping {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) : DLBA.Dir → Prop
  | .stay => True
  | .left => 0 < tape.head.val
  | .right => tape.head.val < n

/-- Nonclamping left motion has an explicit partial successor head. -/
public theorem nextHead_left_of_nonclamping {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (hinside : Nonclamping tape .left) :
    nextHead .left tape.head =
      some ⟨tape.head.val - 1, by
        have := tape.head.isLt
        omega⟩ := by
  change 0 < tape.head.val at hinside
  simp [nextHead, hinside]

/-- Nonclamping right motion has an explicit partial successor head. -/
public theorem nextHead_right_of_nonclamping {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (hinside : Nonclamping tape .right) :
    nextHead .right tape.head =
      some ⟨tape.head.val + 1, by
        change tape.head.val < n at hinside
        omega⟩ := by
  change tape.head.val < n at hinside
  simp [nextHead, hinside]

/-- Under the precise nonclamping premise, the selected reversible memory
operation has exactly the ordinary write-and-move result. -/
public theorem graph_move_operation_eq {A : Type uAlphabet} [DecidableEq A]
    {n : ℕ} (tape : DLBA.BoundedTape A n) (written : A)
    (direction : DLBA.Dir) (hinside : Nonclamping tape direction) :
    (BoundedTapeMemory.graph A n).move
        (operation tape.read written direction) tape =
      some ((tape.write written).moveHead direction) := by
  cases direction with
  | stay =>
      exact move_stationary_eq_write_moveHead tape written
  | left =>
      have hnext := nextHead_left_of_nonclamping tape hinside
      simpa [operation, Travel.toDir] using
        (move_departure_eq_write_moveHead tape written .left hnext)
  | right =>
      have hnext := nextHead_right_of_nonclamping tape hinside
      simpa [operation, Travel.toDir] using
        (move_departure_eq_write_moveHead tape written .right hnext)

/-- Conversely, success of the selected graph operation certifies both that
the motion did not clamp and that its target is the ordinary write-and-move
tape. -/
public theorem nonclamping_and_eq_of_graph_move_operation {A : Type uAlphabet}
    [DecidableEq A] {n : ℕ} (tape target : DLBA.BoundedTape A n)
    (written : A) (direction : DLBA.Dir)
    (hmove : (BoundedTapeMemory.graph A n).move
      (operation tape.read written direction) tape = some target) :
    Nonclamping tape direction ∧
      target = (tape.write written).moveHead direction := by
  cases direction with
  | stay =>
      have hspec := (move_stationary_eq_some_iff
        tape.read written tape target).mp (by simpa [operation] using hmove)
      refine ⟨trivial, ?_⟩
      simpa using hspec.2
  | left =>
      have hspec := (move_departure_eq_some_iff
        tape.read written .left tape target).mp (by simpa [operation] using hmove)
      rcases hspec with ⟨_, targetHead, hnext, rfl⟩
      have hinside : 0 < tape.head.val := by
        by_contra hnot
        have : tape.head.val = 0 := by omega
        simp [nextHead, this] at hnext
      refine ⟨hinside, ?_⟩
      apply Eq.symm
      apply BoundedTapeMemory.eq_of_contents_head
      · rfl
      · exact moveHead_eq_of_nextHead (tape.write written) .left hnext
  | right =>
      have hspec := (move_departure_eq_some_iff
        tape.read written .right tape target).mp (by simpa [operation] using hmove)
      rcases hspec with ⟨_, targetHead, hnext, rfl⟩
      have hinside : tape.head.val < n := by
        by_contra hnot
        have : tape.head.val = n := by
          have := tape.head.isLt
          omega
        simp [nextHead, this] at hnext
      refine ⟨hinside, ?_⟩
      apply Eq.symm
      apply BoundedTapeMemory.eq_of_contents_head
      · rfl
      · exact moveHead_eq_of_nextHead (tape.write written) .right hnext

/-- Translate the deterministic finite-control table.  Reverse/arrival names
belong to the memory graph and are used by local backtracking, but the forward
controller itself selects only stationary or departure names. -/
@[expose]
public def machine {A : Type uAlphabet} {State : Type uState}
    (source : DLBA.Machine A State) :
    GraphWalking.Machine A (BoundedTapeMemory.Direction A) State where
  transition state observed :=
    (source.transition state observed).map fun output =>
      (output.1, operation observed output.2.1 output.2.2)
  accept state _ := source.accept state = true

@[simp]
public theorem machine_accept {A : Type uAlphabet} {State : Type uState}
    (source : DLBA.Machine A State) (state : State) (observed : A) :
    (machine source).accept state observed ↔ source.accept state = true := by
  rfl

/-- The translation preserves terminal acceptance when it is an explicit
property of the source table.  In particular, `machine` does **not** silently
remove outgoing transitions from accepting source states: without this
hypothesis its accepting configurations need not be terminal. -/
public theorem machine_terminalAcceptance
    {A : Type uAlphabet} {State : Type uState}
    (source : DLBA.Machine A State)
    (hterminal : ∀ state observed, source.accept state = true →
      source.transition state observed = none) :
    (machine source).TerminalAcceptance := by
  intro state observed haccept
  have hnone := hterminal state observed haccept
  simp [machine, hnone]

/-- Forget the graph-walking presentation of a bounded-tape configuration. -/
@[expose]
public def toDLBACfg {A : Type uAlphabet} {State : Type uState} {n : ℕ} :
    GraphWalking.Configuration State (DLBA.BoundedTape A n) → DLBA.Cfg A State n
  | (state, tape) => ⟨state, tape⟩

/-- All enabled moves at one source configuration avoid clamping.  The
condition is vacuous for a halted configuration and automatic for `stay`. -/
@[expose]
public def TransitionNonclamping {A : Type uAlphabet} {State : Type uState}
    {n : ℕ} (source : DLBA.Machine A State) (state : State)
    (tape : DLBA.BoundedTape A n) : Prop :=
  ∀ targetState written direction,
    source.transition state tape.read = some (targetState, written, direction) →
      Nonclamping tape direction

/-- Every graph-walker step projects to exactly the corresponding ordinary
DLBA step; successful partial motion itself supplies the nonclamping fact. -/
public theorem step_sound {A : Type uAlphabet} [DecidableEq A]
    {State : Type uState} {n : ℕ} (source : DLBA.Machine A State)
    {state targetState : State} {tape targetTape : DLBA.BoundedTape A n}
    (hstep : (machine source).Step (BoundedTapeMemory.graph A n)
      (state, tape) (targetState, targetTape)) :
    DLBA.step source ⟨state, tape⟩ = some ⟨targetState, targetTape⟩ := by
  cases htransition : source.transition state tape.read with
  | none =>
      change source.transition state (tape.contents tape.head) = none at htransition
      simp [Machine.Step, Machine.next, machine, htransition] at hstep
  | some output =>
      rcases output with ⟨targetState', written, direction⟩
      change source.transition state (tape.contents tape.head) =
        some (targetState', written, direction) at htransition
      cases hmove : BoundedTapeMemory.move
          (operation (tape.contents tape.head) written direction) tape with
      | none =>
          simp [Machine.Step, Machine.next, machine, htransition, hmove] at hstep
      | some outputTape =>
          simp [Machine.Step, Machine.next, machine, htransition, hmove] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          have hgraphMove : (BoundedTapeMemory.graph A n).move
              (operation tape.read written direction) tape = some outputTape := hmove
          have hresult := (nonclamping_and_eq_of_graph_move_operation
            tape outputTape written direction hgraphMove).2
          simp [DLBA.step, htransition, hresult]

/-- Every finite graph-walker run projects to a finite run of the ordinary
deterministic step relation.  This is one-way: a clamped source transition can
exist even though the corresponding partial graph operation is absent. -/
public theorem reaches_sound {A : Type uAlphabet} [DecidableEq A]
    {State : Type uState} {n : ℕ} (source : DLBA.Machine A State)
    {start finish :
      GraphWalking.Configuration State (DLBA.BoundedTape A n)}
    (hreach : Relation.ReflTransGen
      ((machine source).Step (BoundedTapeMemory.graph A n)) start finish) :
    Relation.ReflTransGen
      (fun left right : DLBA.Cfg A State n =>
        DLBA.step source left = some right)
      (toDLBACfg start) (toDLBACfg finish) := by
  exact hreach.lift toDLBACfg (fun _ _ hstep => step_sound source hstep)

/-- Exact one-step correspondence at a source whose enabled instruction does
not clamp. -/
public theorem step_iff_dlba_step_of_transitionNonclamping
    {A : Type uAlphabet} [DecidableEq A] {State : Type uState} {n : ℕ}
    (source : DLBA.Machine A State) {state targetState : State}
    {tape targetTape : DLBA.BoundedTape A n}
    (hinside : TransitionNonclamping source state tape) :
    (machine source).Step (BoundedTapeMemory.graph A n)
        (state, tape) (targetState, targetTape) ↔
      DLBA.step source ⟨state, tape⟩ = some ⟨targetState, targetTape⟩ := by
  constructor
  · exact step_sound source
  · intro hstep
    cases htransition : source.transition state tape.read with
    | none =>
        change source.transition state (tape.contents tape.head) = none at htransition
        simp [DLBA.step, htransition] at hstep
    | some output =>
        rcases output with ⟨targetState', written, direction⟩
        change source.transition state (tape.contents tape.head) =
          some (targetState', written, direction) at htransition
        have hnonclamping := hinside targetState' written direction htransition
        have hmove := graph_move_operation_eq tape written direction hnonclamping
        change BoundedTapeMemory.move
          (operation (tape.contents tape.head) written direction) tape =
            some ((tape.write written).moveHead direction) at hmove
        simp [DLBA.step, htransition] at hstep
        rcases hstep with ⟨rfl, rfl⟩
        simp [Machine.Step, Machine.next, machine, htransition, hmove]

/-- A convenient direct forward rule for one known ordinary transition. -/
public theorem step_of_transition
    {A : Type uAlphabet} [DecidableEq A] {State : Type uState} {n : ℕ}
    (source : DLBA.Machine A State) {state targetState : State}
    (tape : DLBA.BoundedTape A n) {written : A} {direction : DLBA.Dir}
    (htransition : source.transition state tape.read =
      some (targetState, written, direction))
    (hinside : Nonclamping tape direction) :
    (machine source).Step (BoundedTapeMemory.graph A n)
      (state, tape)
      (targetState, (tape.write written).moveHead direction) := by
  have hmove := graph_move_operation_eq tape written direction hinside
  change source.transition state (tape.contents tape.head) =
    some (targetState, written, direction) at htransition
  change BoundedTapeMemory.move
    (operation (tape.contents tape.head) written direction) tape =
      some ((tape.write written).moveHead direction) at hmove
  simp [Machine.Step, Machine.next, machine, htransition, hmove]

end BoundedTapeController

end GraphWalking
