module

public import Langlib.Automata.FiniteState.Equivalence.Determinization
public import Langlib.Automata.LinearBounded.CrossingSequence
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic

@[expose]
public section

/-!
# Finite crossing profiles and one-cell LBA histories

A crossing profile is a control-state sequence of length at most a fixed constant.  Adjacent tape
cells share one profile for their common boundary.  `CellRun` describes the complete local history
of one cell: it remembers the current symbol while the global head is elsewhere, validates writes
and stationary moves while the head is present, and consumes the appropriate profile entry on
each exit or re-entry.

Physical clamping is part of the verifier.  A left move stays local exactly on the first cell; a
right move stays local exactly on the last cell.  Acceptance may occur at any cell.  The Boolean
index of `CellRun` marks whether that cell contains the unique terminal accepting event.

`profileNFA` scans cell symbols from left to right, guessing one bounded profile per internal
boundary and checking adjacent local histories.  Its one-symbol delay is necessary because a
cell is known to be the physical right endpoint only when no later symbol remains.
-/

namespace LBA.BoundedCrossing

universe u v

variable {Gamma : Type u} {State : Type v}

/-- A control-state sequence of length at most `bound`, represented by its finite length and a
vector of that length. -/
abbrev Profile (State : Type v) (bound : Nat) :=
  Σ length : Fin (bound + 1), List.Vector State length.val

namespace Profile

/-- Forget the finite length witness and expose a profile as an ordinary list. -/
def list {bound : Nat} (profile : Profile State bound) : List State :=
  profile.2.1

@[simp] theorem length_list {bound : Nat} (profile : Profile State bound) :
    profile.list.length = profile.1.val := profile.2.2

/-- Package a list whose length meets the profile bound. -/
def ofList {bound : Nat} (states : List State)
    (hlength : states.length ≤ bound) : Profile State bound :=
  ⟨⟨states.length, by omega⟩, ⟨states, rfl⟩⟩

@[simp] theorem list_ofList {bound : Nat} (states : List State)
    (hlength : states.length ≤ bound) :
    (ofList states hlength).list = states := rfl

end Profile

/-- The side of a cell on which the global tape head currently lies while it is outside. -/
inductive Side
  | left
  | right
deriving DecidableEq, Fintype

/-- Local phase of one cell: either the head is present with a control state, or it is outside
on a specified side.  The cell's current symbol is retained in every phase. -/
inductive Phase (Gamma : Type u) (State : Type v)
  | active (state : State) (symbol : Gamma)
  | outside (side : Side) (symbol : Gamma)

/-- A direction is executed without leaving this cell, including the physically clamped endpoint
directions. -/
def DirectionStaysLocal (atLeft atRight : Bool) : DLBA.Dir → Prop
  | .stay => True
  | .left => atLeft = true
  | .right => atRight = true

/-- A direction genuinely exits this cell across its left boundary. -/
def DirectionExitsLeft (atLeft : Bool) : DLBA.Dir → Prop
  | .left => atLeft = false
  | _ => False

/-- A direction genuinely exits this cell across its right boundary. -/
def DirectionExitsRight (atRight : Bool) : DLBA.Dir → Prop
  | .right => atRight = false
  | _ => False

/-- A finite local history for one physical cell.

The two lists are the as-yet-unconsumed chronological crossing profiles on the left and right
boundaries.  Exiting records the target state of the machine transition; entering consumes that
same state in the neighboring cell. -/
inductive CellRun (M : LBA.Machine Gamma State) (atLeft atRight : Bool) :
    Phase Gamma State → List State → List State → Bool → Type (max u v)
  | terminal {state symbol}
      (haccept : M.accept state = true) :
      CellRun M atLeft atRight (.active state symbol) [] [] true
  | idleLeft (symbol) :
      CellRun M atLeft atRight (.outside .left symbol) [] [] false
  | idleRight (symbol) :
      CellRun M atLeft atRight (.outside .right symbol) [] [] false
  | stationary {state symbol nextState written direction left right terminal}
      (henabled :
        (nextState, written, direction) ∈ M.transition state symbol)
      (hstays : DirectionStaysLocal atLeft atRight direction)
      (rest : CellRun M atLeft atRight
        (.active nextState written) left right terminal) :
      CellRun M atLeft atRight
        (.active state symbol) left right terminal
  | exitLeft {state symbol nextState written direction left right terminal}
      (henabled :
        (nextState, written, direction) ∈ M.transition state symbol)
      (hexits : DirectionExitsLeft atLeft direction)
      (rest : CellRun M atLeft atRight
        (.outside .left written) left right terminal) :
      CellRun M atLeft atRight
        (.active state symbol) (nextState :: left) right terminal
  | exitRight {state symbol nextState written direction left right terminal}
      (henabled :
        (nextState, written, direction) ∈ M.transition state symbol)
      (hexits : DirectionExitsRight atRight direction)
      (rest : CellRun M atLeft atRight
        (.outside .right written) left right terminal) :
      CellRun M atLeft atRight
        (.active state symbol) left (nextState :: right) terminal
  | enterLeft {state symbol left right terminal}
      (rest : CellRun M atLeft atRight
        (.active state symbol) left right terminal) :
      CellRun M atLeft atRight
        (.outside .left symbol) (state :: left) right terminal
  | enterRight {state symbol left right terminal}
      (rest : CellRun M atLeft atRight
        (.active state symbol) left right terminal) :
      CellRun M atLeft atRight
        (.outside .right symbol) left (state :: right) terminal

namespace CellRun

/-- Number of local constructors in a cell history.  This supplies a decreasing measure for
synchronized reconstruction of the global run. -/
def size {M : LBA.Machine Gamma State} {atLeft atRight : Bool} :
    {phase : Phase Gamma State} → {left right : List State} →
      {terminal : Bool} → CellRun M atLeft atRight phase left right terminal → Nat
  | _, _, _, _, .terminal _ => 1
  | _, _, _, _, .idleLeft _ => 1
  | _, _, _, _, .idleRight _ => 1
  | _, _, _, _, .stationary _ _ rest => rest.size + 1
  | _, _, _, _, .exitLeft _ _ rest => rest.size + 1
  | _, _, _, _, .exitRight _ _ rest => rest.size + 1
  | _, _, _, _, .enterLeft rest => rest.size + 1
  | _, _, _, _, .enterRight rest => rest.size + 1

end CellRun

/-- One initial cell symbol admits a local history with the supplied boundary profiles and
terminal-event bit.  The first cell starts active in the machine's initial state; every other
cell starts with the global head somewhere to its left. -/
def CellCompatible (M : LBA.Machine Gamma State)
    (atLeft atRight : Bool) (initialSymbol : Gamma)
    (left right : List State) (terminal : Bool) : Prop :=
  Nonempty <| CellRun M atLeft atRight
    (if atLeft then
      .active M.initial initialSymbol
    else
      .outside .left initialSymbol)
    left right terminal

/-- Delayed spatial scan states for `profileNFA`. -/
inductive ScanState (Gamma : Type u) (State : Type v) (bound : Nat)
  | before
  | first (symbol : Gamma)
  | pending (symbol : Gamma) (left : Profile State bound)
      (seenTerminal : Bool)
deriving DecidableEq, Fintype

/-- NFA that guesses bounded boundary profiles and validates one complete local history per
physical tape cell.

The language correctness theorem is proved separately by relating NFA paths to spatial
certificates and synchronizing those certificates with global machine traces. -/
def profileNFA (M : LBA.Machine Gamma State) (bound : Nat) :
    NFA Gamma (ScanState Gamma State bound) where
  start := {.before}
  step
    | .before, new => {.first new}
    | .first old, new =>
        {next | ∃ (right : Profile State bound) (terminal : Bool),
          CellCompatible M true false old [] right.list terminal ∧
          next = .pending new right terminal}
    | .pending old left seen, new =>
        {next | ∃ (right : Profile State bound) (terminal : Bool),
          CellCompatible M false false old left.list right.list terminal ∧
          ¬ (seen = true ∧ terminal = true) ∧
          next = .pending new right (seen || terminal)}
  accept := {state |
    match state with
    | .before => False
    | .first symbol =>
        CellCompatible M true true symbol [] [] true
    | .pending symbol left seen =>
        ∃ terminal : Bool,
          CellCompatible M false true symbol left.list [] terminal ∧
          ¬ (seen = true ∧ terminal = true) ∧
          (seen || terminal) = true}

end LBA.BoundedCrossing

end
