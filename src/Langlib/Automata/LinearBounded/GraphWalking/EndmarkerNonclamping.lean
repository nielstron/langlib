module

public import Langlib.Automata.LinearBounded.GraphWalking.BoundedTapeController
public import Langlib.Automata.LinearBounded.Unambiguous
import Mathlib.Tactic

@[expose]
public section

/-!
# Endmarker guards eliminate clamping on canonical runs

`DLBA.BoundedTape A n` has `n + 1` cells, indexed from `0` through `n`.
For the canonical endmarker tape `LBA.loadEnd w`, the parameter is
`n = |w| + 1`; hence even the empty input has the two distinct cells `0` and
`1`.

This file isolates the elementary normal-form bridge needed by the bounded
tape graph-walking controller.  A syntactic endmarker guard preserves both
markers and points boundary moves inward.  Starting from `loadEnd`, every
reachable configuration therefore still has intact markers, and every
enabled deterministic transition is nonclamping.

The final section applies the bridge to the existing pipeline
`LBA.simMachine (DLBA.toLBA' M) b`, converted back to a terminalized DLBA by
`LBA.Machine.toDLBA`.  This is only a canonical-run/controller result; it does
not assert a new language-class inclusion.
-/

namespace LBA

variable {T Gamma State : Type*}

/-- Both endpoint cells of a bounded tape contain their canonical markers.

For a one-cell raw tape (`n = 0`) this proposition is deliberately
inconsistent: the single cell cannot simultaneously be the two distinct
markers.  Canonical tapes have parameter `|w| + 1`, and therefore at least two
cells. -/
@[expose]
public def EndmarkersIntact {n : Nat}
    (tape : DLBA.BoundedTape (EndAlpha T Gamma) n) : Prop :=
  tape.contents (0 : Fin (n + 1)) = leftMark ∧
    tape.contents (Fin.last n) = rightMark

/-- The canonical bracketed tape has intact, distinct endpoint cells. -/
public theorem endmarkersIntact_loadEnd (word : List T) :
    EndmarkersIntact (loadEnd (Γ := Gamma) word) := by
  constructor
  · simp [loadEnd]
  · simp [loadEnd, Fin.last]

/-- Updating the head cell preserves intact endpoints provided an update at
an endpoint writes that endpoint's marker back.  Head motion is irrelevant to
the contents. -/
public theorem EndmarkersIntact.write_moveHead
    {n : Nat} {tape : DLBA.BoundedTape (EndAlpha T Gamma) n}
    (hintact : EndmarkersIntact tape) (written : EndAlpha T Gamma)
    (direction : DLBA.Dir)
    (hleft : tape.head = (0 : Fin (n + 1)) → written = leftMark)
    (hright : tape.head = Fin.last n → written = rightMark) :
    EndmarkersIntact ((tape.write written).moveHead direction) := by
  constructor
  · by_cases hhead : tape.head = (0 : Fin (n + 1))
    · simp [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hhead,
        hleft hhead]
    · simp [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
        Function.update_of_ne (Ne.symm hhead), hintact.1]
  · by_cases hhead : tape.head = Fin.last n
    · simp [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, hhead,
        hright hhead]
    · simp [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
        Function.update_of_ne (Ne.symm hhead), hintact.2]

/-- An LBA table is endmarker guarded when an instruction reading `leftMark`
preserves it and does not move left, and an instruction reading `rightMark`
preserves it and does not move right. -/
@[expose]
public def Machine.EndmarkerGuarded
    (machine : Machine (EndAlpha T Gamma) State) : Prop :=
  (∀ state target written direction,
      (target, written, direction) ∈ machine.transition state leftMark →
        written = leftMark ∧ direction ≠ DLBA.Dir.left) ∧
    (∀ state target written direction,
      (target, written, direction) ∈ machine.transition state rightMark →
        written = rightMark ∧ direction ≠ DLBA.Dir.right)

/-- The relational analogue of the controller's deterministic
`TransitionNonclamping` predicate. -/
@[expose]
public def Machine.TransitionNonclamping
    {n : Nat} (machine : Machine (EndAlpha T Gamma) State)
    (state : State) (tape : DLBA.BoundedTape (EndAlpha T Gamma) n) : Prop :=
  ∀ target written direction,
    (target, written, direction) ∈ machine.transition state tape.read →
      GraphWalking.BoundedTapeController.Nonclamping tape direction

/-- Intact markers and the syntactic guard rule out clamped LBA moves. -/
public theorem Machine.transitionNonclamping_of_endmarkersIntact
    {n : Nat} (machine : Machine (EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded) (state : State)
    (tape : DLBA.BoundedTape (EndAlpha T Gamma) n)
    (hintact : EndmarkersIntact tape) :
    machine.TransitionNonclamping state tape := by
  intro target written direction htransition
  cases direction with
  | stay => trivial
  | left =>
      change 0 < tape.head.val
      by_contra hnot
      have hval : tape.head.val = 0 := by omega
      have hzero : tape.head = (0 : Fin (n + 1)) := Fin.ext hval
      have hread : tape.read = leftMark := by
        simp [DLBA.BoundedTape.read, hzero, hintact.1]
      exact (hguard.1 state target written .left (hread ▸ htransition)).2 rfl
  | right =>
      change tape.head.val < n
      by_contra hnot
      have hval : tape.head.val = n := by
        have := tape.head.isLt
        omega
      have hlast : tape.head = Fin.last n := Fin.ext (by
        simpa [Fin.last] using hval)
      have hread : tape.read = rightMark := by
        simp [DLBA.BoundedTape.read, hlast, hintact.2]
      exact (hguard.2 state target written .right (hread ▸ htransition)).2 rfl

/-- One guarded LBA step preserves the endpoint markers. -/
public theorem Machine.endmarkersIntact_of_step
    {n : Nat} (machine : Machine (EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded)
    {source target : DLBA.Cfg (EndAlpha T Gamma) State n}
    (hintact : EndmarkersIntact source.tape)
    (hstep : Step machine source target) :
    EndmarkersIntact target.tape := by
  rcases hstep with ⟨targetState, written, direction, htransition, rfl⟩
  apply hintact.write_moveHead written direction
  · intro hhead
    have hread : source.tape.read = leftMark := by
      simp [DLBA.BoundedTape.read, hhead, hintact.1]
    exact (hguard.1 source.state targetState written direction
      (hread ▸ htransition)).1
  · intro hhead
    have hread : source.tape.read = rightMark := by
      simp [DLBA.BoundedTape.read, hhead, hintact.2]
    exact (hguard.2 source.state targetState written direction
      (hread ▸ htransition)).1

/-- Intactness is an invariant of every finite guarded LBA run. -/
public theorem Machine.endmarkersIntact_of_reaches
    {n : Nat} (machine : Machine (EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded)
    {source target : DLBA.Cfg (EndAlpha T Gamma) State n}
    (hintact : EndmarkersIntact source.tape)
    (hreaches : Reaches machine source target) :
    EndmarkersIntact target.tape := by
  induction hreaches with
  | refl => exact hintact
  | tail _ lastStep ih =>
      exact machine.endmarkersIntact_of_step hguard ih lastStep

/-- The existing bouncing endmarker simulator preserves markers and always
points inward at an endpoint, independently of its simulated transition
table. -/
public theorem simMachine_endmarkerGuarded
    (machine : Machine (Option (T ⊕ Gamma)) State) (acceptEmpty : Bool) :
    (simMachine machine acceptEmpty).EndmarkerGuarded := by
  constructor
  · intro state target written direction htransition
    cases state with
    | start =>
        simp [simMachine, simTransition] at htransition
        rcases htransition with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, by decide⟩
    | entry => simp [simMachine, simTransition] at htransition
    | run state =>
        simp [simMachine, simTransition] at htransition
        rcases htransition with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, by decide⟩
    | acc => simp [simMachine, simTransition] at htransition
    | rej => simp [simMachine, simTransition] at htransition
  · intro state target written direction htransition
    cases state with
    | start => simp [simMachine, simTransition] at htransition
    | entry =>
        by_cases hb : acceptEmpty = true
        · simp [simMachine, simTransition, hb] at htransition
          rcases htransition with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, by decide⟩
        · have hbfalse : acceptEmpty = false := Bool.eq_false_of_not_eq_true hb
          simp [simMachine, simTransition, hbfalse] at htransition
          rcases htransition with ⟨rfl, rfl, rfl⟩
          exact ⟨rfl, by decide⟩
    | run state =>
        simp [simMachine, simTransition] at htransition
        rcases htransition with ⟨rfl, rfl, rfl⟩
        exact ⟨rfl, by decide⟩
    | acc => simp [simMachine, simTransition] at htransition
    | rej => simp [simMachine, simTransition] at htransition

end LBA

namespace DLBA

variable {T Gamma State : Type*}

/-- Deterministic form of the syntactic endmarker guard. -/
@[expose]
public def Machine.EndmarkerGuarded
    (machine : Machine (LBA.EndAlpha T Gamma) State) : Prop :=
  (∀ state target written direction,
      machine.transition state LBA.leftMark =
          some (target, written, direction) →
        written = LBA.leftMark ∧ direction ≠ Dir.left) ∧
    (∀ state target written direction,
      machine.transition state LBA.rightMark =
          some (target, written, direction) →
        written = LBA.rightMark ∧ direction ≠ Dir.right)

/-- Intact markers and a deterministic guard imply exactly the controller's
`TransitionNonclamping` premise. -/
public theorem Machine.transitionNonclamping_of_endmarkersIntact
    {n : Nat} (machine : Machine (LBA.EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded) (state : State)
    (tape : BoundedTape (LBA.EndAlpha T Gamma) n)
    (hintact : LBA.EndmarkersIntact tape) :
    GraphWalking.BoundedTapeController.TransitionNonclamping machine state tape := by
  intro target written direction htransition
  cases direction with
  | stay => trivial
  | left =>
      change 0 < tape.head.val
      by_contra hnot
      have hval : tape.head.val = 0 := by omega
      have hzero : tape.head = (0 : Fin (n + 1)) := Fin.ext hval
      have hread : tape.read = LBA.leftMark := by
        simp [BoundedTape.read, hzero, hintact.1]
      exact (hguard.1 state target written .left (hread ▸ htransition)).2 rfl
  | right =>
      change tape.head.val < n
      by_contra hnot
      have hval : tape.head.val = n := by
        have := tape.head.isLt
        omega
      have hlast : tape.head = Fin.last n := Fin.ext (by
        simpa [Fin.last] using hval)
      have hread : tape.read = LBA.rightMark := by
        simp [BoundedTape.read, hlast, hintact.2]
      exact (hguard.2 state target written .right (hread ▸ htransition)).2 rfl

/-- One guarded deterministic step preserves both endpoint markers. -/
public theorem Machine.endmarkersIntact_of_step
    {n : Nat} (machine : Machine (LBA.EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded)
    {source target : Cfg (LBA.EndAlpha T Gamma) State n}
    (hintact : LBA.EndmarkersIntact source.tape)
    (hstep : step machine source = some target) :
    LBA.EndmarkersIntact target.tape := by
  cases htransition : machine.transition source.state source.tape.read with
  | none =>
      unfold step at hstep
      rw [htransition] at hstep
      simp at hstep
  | some output =>
      rcases output with ⟨targetState, written, direction⟩
      unfold step at hstep
      rw [htransition] at hstep
      simp only [Option.some.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      apply hintact.write_moveHead written direction
      · intro hhead
        have hread : source.tape.read = LBA.leftMark := by
          simp [BoundedTape.read, hhead, hintact.1]
        exact (hguard.1 source.state targetState written direction
          (hread ▸ htransition)).1
      · intro hhead
        have hread : source.tape.read = LBA.rightMark := by
          simp [BoundedTape.read, hhead, hintact.2]
        exact (hguard.2 source.state targetState written direction
          (hread ▸ htransition)).1

/-- Intactness is invariant under deterministic step reachability. -/
public theorem Machine.endmarkersIntact_of_reflTransGen_step
    {n : Nat} (machine : Machine (LBA.EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded)
    {source target : Cfg (LBA.EndAlpha T Gamma) State n}
    (hintact : LBA.EndmarkersIntact source.tape)
    (hreaches : Relation.ReflTransGen
      (fun left right => step machine left = some right) source target) :
    LBA.EndmarkersIntact target.tape := by
  induction hreaches with
  | refl => exact hintact
  | tail _ lastStep ih =>
      exact machine.endmarkersIntact_of_step hguard ih lastStep

/-- Every configuration deterministically reachable from a canonical input
has a nonclamping enabled transition (if it has any transition at all). -/
public theorem Machine.transitionNonclamping_of_reachable_loadEnd
    (machine : Machine (LBA.EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded) (word : List T)
    {target : Cfg (LBA.EndAlpha T Gamma) State (word.length + 1)}
    (hreaches : Relation.ReflTransGen
      (fun left right => step machine left = some right)
      ⟨machine.initial, LBA.loadEnd (Γ := Gamma) word⟩ target) :
    GraphWalking.BoundedTapeController.TransitionNonclamping
      machine target.state target.tape := by
  apply machine.transitionNonclamping_of_endmarkersIntact hguard
  exact machine.endmarkersIntact_of_reflTransGen_step hguard
    (LBA.endmarkersIntact_loadEnd (Gamma := Gamma) word) hreaches

/-- A chosen transition of `M.toDLBA` always came from the source LBA table. -/
private theorem toDLBA_transition_some_mem
    (machine : LBA.Machine (LBA.EndAlpha T Gamma) State)
    {state target : State} {observed written : LBA.EndAlpha T Gamma}
    {direction : Dir}
    (htransition : machine.toDLBA.transition state observed =
      some (target, written, direction)) :
    (target, written, direction) ∈ machine.transition state observed := by
  simp only [LBA.Machine.toDLBA] at htransition
  split at htransition
  · simp at htransition
  · split at htransition
    · next hexists =>
        have hchosen := Classical.choose_spec hexists
        have heq : Classical.choose hexists = (target, written, direction) :=
          Option.some.inj htransition
        rw [← heq]
        exact hchosen
    · simp at htransition

/-- The functional-LBA-to-DLBA conversion preserves syntactic endmarker
guards.  Functionality is not needed for this local fact: the selected move is
always a member of the guarded source set. -/
public theorem endmarkerGuarded_toDLBA
    (machine : LBA.Machine (LBA.EndAlpha T Gamma) State)
    (hguard : machine.EndmarkerGuarded) :
    machine.toDLBA.EndmarkerGuarded := by
  constructor
  · intro state target written direction htransition
    exact hguard.1 state target written direction
      (toDLBA_transition_some_mem machine htransition)
  · intro state target written direction htransition
    exact hguard.2 state target written direction
      (toDLBA_transition_some_mem machine htransition)

/-- `LBA.Machine.toDLBA` terminalizes acceptance by construction. -/
public theorem toDLBA_terminalAcceptance
    (machine : LBA.Machine (LBA.EndAlpha T Gamma) State) :
    ∀ state observed, machine.toDLBA.accept state = true →
      machine.toDLBA.transition state observed = none := by
  classical
  intro state observed haccept
  change machine.accept state = true at haccept
  change (if machine.accept state = true then none else
    if h : ∃ move, move ∈ machine.transition state observed then
      some (Classical.choose h) else none) = none
  rw [if_pos haccept]

end DLBA

namespace GraphWalking
namespace EndmarkerNonclamping

variable {T Gamma State : Type*}

/-- The deterministic, terminalized endmarker machine produced by the
existing DLBA-to-LBA and bouncing-endmarker pipeline. -/
@[expose]
public noncomputable def deterministicSimMachine
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    DLBA.Machine (LBA.EndAlpha T Gamma) (LBA.SimState (Option State)) :=
  (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty).toDLBA

/-- The intermediate endmarker LBA is functional, using the existing two
functionality theorems rather than reproving transition uniqueness. -/
public theorem simMachine_toLBA_functional
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty).Functional :=
  LBA.Machine.simMachine_functional (DLBA.toLBA' machine)
    (DLBA.toLBA'_functional machine) acceptEmpty

/-- Converting the functional endmarker simulator to a DLBA preserves
acceptance from every bounded configuration.  This is the existing generic
functional-conversion theorem specialized to the pipeline. -/
public theorem deterministicSimMachine_accepts_iff
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) {n : Nat}
    (configuration : DLBA.Cfg (LBA.EndAlpha T Gamma)
      (LBA.SimState (Option State)) n) :
    DLBA.Accepts (deterministicSimMachine machine acceptEmpty) configuration ↔
      LBA.Accepts (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty)
        configuration := by
  exact LBA.Machine.accepts_toDLBA_iff
    (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty)
    (simMachine_toLBA_functional machine acceptEmpty) configuration

/-- The terminalized deterministic simulator is syntactically guarded. -/
public theorem deterministicSimMachine_endmarkerGuarded
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    (deterministicSimMachine machine acceptEmpty).EndmarkerGuarded := by
  exact DLBA.endmarkerGuarded_toDLBA
    (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty)
    (LBA.simMachine_endmarkerGuarded (DLBA.toLBA' machine) acceptEmpty)

/-- Accepting states of the deterministic simulator have no outgoing
controller transition. -/
public theorem deterministicSimMachine_terminalAcceptance
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    ∀ state observed,
      (deterministicSimMachine machine acceptEmpty).accept state = true →
      (deterministicSimMachine machine acceptEmpty).transition state observed = none := by
  exact DLBA.toDLBA_terminalAcceptance
    (LBA.simMachine (DLBA.toLBA' machine) acceptEmpty)

/-- The bounded-tape graph-walking controller of the deterministic simulator
has terminal acceptance. -/
public theorem controller_deterministicSimMachine_terminalAcceptance
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) :
    (BoundedTapeController.machine
      (deterministicSimMachine machine acceptEmpty)).TerminalAcceptance := by
  apply BoundedTapeController.machine_terminalAcceptance
  exact deterministicSimMachine_terminalAcceptance machine acceptEmpty

/-- Every transition enabled at a canonical-reachable simulator
configuration avoids physical clamping. -/
public theorem deterministicSimMachine_transitionNonclamping_of_reachable
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T)
    {target : DLBA.Cfg (LBA.EndAlpha T Gamma) (LBA.SimState (Option State))
      (word.length + 1)}
    (hreaches : Relation.ReflTransGen
      (fun left right =>
        DLBA.step (deterministicSimMachine machine acceptEmpty) left = some right)
      ⟨(deterministicSimMachine machine acceptEmpty).initial,
        LBA.loadEnd (Γ := Gamma) word⟩ target) :
    BoundedTapeController.TransitionNonclamping
      (deterministicSimMachine machine acceptEmpty) target.state target.tape := by
  exact DLBA.Machine.transitionNonclamping_of_reachable_loadEnd
    (deterministicSimMachine machine acceptEmpty)
    (deterministicSimMachine_endmarkerGuarded machine acceptEmpty) word hreaches

/-- Consequently, at every canonical-reachable source, one controller step is
equivalent to the corresponding deterministic bounded-tape step. -/
public theorem controller_step_iff_dlba_step_of_reachable
    [DecidableEq (Option (T ⊕ Gamma))]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) State)
    (acceptEmpty : Bool) (word : List T)
    {source : DLBA.Cfg (LBA.EndAlpha T Gamma) (LBA.SimState (Option State))
      (word.length + 1)}
    (hreaches : Relation.ReflTransGen
      (fun left right =>
        DLBA.step (deterministicSimMachine machine acceptEmpty) left = some right)
      ⟨(deterministicSimMachine machine acceptEmpty).initial,
        LBA.loadEnd (Γ := Gamma) word⟩ source)
    {targetState : LBA.SimState (Option State)}
    {targetTape : DLBA.BoundedTape (LBA.EndAlpha T Gamma) (word.length + 1)} :
    (BoundedTapeController.machine
      (deterministicSimMachine machine acceptEmpty)).Step
        (BoundedTapeMemory.graph (LBA.EndAlpha T Gamma) (word.length + 1))
        (source.state, source.tape) (targetState, targetTape) ↔
      DLBA.step (deterministicSimMachine machine acceptEmpty) source =
        some ⟨targetState, targetTape⟩ := by
  apply BoundedTapeController.step_iff_dlba_step_of_transitionNonclamping
  exact deterministicSimMachine_transitionNonclamping_of_reachable
    machine acceptEmpty word hreaches

end EndmarkerNonclamping
end GraphWalking
