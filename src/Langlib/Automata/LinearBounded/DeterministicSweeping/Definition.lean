module

public import Langlib.Automata.DeterministicLinearBounded.Inclusion.LinearBounded
public import Langlib.Automata.LinearBounded.Sweeping

@[expose]
public section

/-!
# A deterministic sweeping simulation alphabet and machine

This file gives the foundational machine construction used to simulate a deterministic
linearly bounded automaton by a deterministic machine whose physical head sweeps between the
two ends of the same bounded tape.  The input initially consists only of raw symbols
`some (.inl i)`.  An initialization sweep replaces them by work cells, records both physical
endpoints, and installs the simulated head on the leftmost cell.

The construction is deliberately stated only at machine level.  Its sweeping invariant and
language-simulation theorem belong in subsequent modules.  In particular, this definition does
**not** assert that nondeterministic and deterministic LBAs recognize the same languages, and it
must not be read as an `LBA = DLBA` claim.

The target alphabet is exactly `Option (I ⊕ Cell Γ Q)`.  The outer `Option` and the raw-input
summand make the initialization protocol explicit; neither carries an oracle, a time bound, nor
an externally decided language bit.  The one-cell tape is handled by the same transitions as
all other widths: the initial right move is clamped, so `initSweep` re-reads that converted cell
and marks it as both endpoints.
-/

namespace DLBA

namespace DeterministicSweeping

universe u v w

/-- The simulated-head annotation stored in a converted work cell.

`needLeft q` records a delayed source-machine left move.  A rightward sweep leaves this request
behind; the following leftward sweep resolves it without making an interior physical turn. -/
public inductive Tag (Q : Type w) where
  | plain
  | head (state : Q)
  | needLeft (state : Q)
  deriving DecidableEq, Fintype

/-- A converted target-tape cell.

The Boolean endpoint fields are installed by initialization.  Exactly one well-formed cell has
`left = true` and exactly one has `right = true`; on a one-cell tape both fields are true. -/
public structure Cell (Γ : Type v) (Q : Type w) where
  left : Bool
  right : Bool
  symbol : Γ
  tag : Tag Q
  deriving DecidableEq, Fintype

/-- Control phases of the deterministic sweeping simulator. -/
public inductive Phase (Q : Type w) where
  | initFirst
  | initSweep
  | initBack
  | scanRight
  | query (state : Q)
  | putRight (state : Q)
  | scanLeft
  | putLeft (state : Q)
  deriving DecidableEq, Fintype

/-- The target alphabet: raw input symbols or converted simulator cells, with an outer blank. -/
public abbrev Alphabet (I : Type u) (Γ : Type v) (Q : Type w) : Type _ :=
  Option (I ⊕ Cell Γ Q)

/-- Canonical embedding of a raw input symbol into the target alphabet. -/
@[simp]
public def inputEmbed (input : I) : Alphabet I Γ Q :=
  some (.inl input)

/-- Embed a converted work cell into the target alphabet. -/
@[simp]
public def workSymbol (cell : Cell Γ Q) : Alphabet I Γ Q :=
  some (.inr cell)

/-- Replace the simulated-head tag while preserving endpoints and the source symbol. -/
@[simp]
public def Cell.withTag (cell : Cell Γ Q) (tag : Tag Q) : Cell Γ Q :=
  { cell with tag }

/-- Replace the source symbol and simulated-head tag in one operation. -/
@[simp]
public def Cell.writeTagged (cell : Cell Γ Q) (symbol : Γ) (tag : Tag Q) : Cell Γ Q :=
  { cell with symbol, tag }

/-- Continue a rightward pass, reversing immediately when the current cell is the right end. -/
public def continueRight (cell : Cell Γ Q) :
    Phase Q × Alphabet I Γ Q × DLBA.Dir :=
  if cell.right then
    (.scanLeft, workSymbol cell, .left)
  else
    (.scanRight, workSymbol cell, .right)

/-- Continue a leftward pass, changing phase without leaving the left endpoint.

The stationary phase change is essential when the simulated head is itself on the leftmost
cell: the following `scanRight` transition can then observe it rather than skipping it. -/
public def continueLeft (cell : Cell Γ Q) :
    Phase Q × Alphabet I Γ Q × DLBA.Dir :=
  if cell.left then
    (.scanRight, workSymbol cell, .stay)
  else
    (.scanLeft, workSymbol cell, .left)

/-- The deterministic transition function of the sweeping simulator.

Only `scanRight` executes a source step.  A source left move from an interior cell is delayed
with `needLeft`; at the physical right endpoint it is instead performed immediately through
`putLeft`, because a leftward scan would otherwise have already passed the request cell.  A
source left move at the physical left endpoint is clamped, including the width-one case. -/
public def transition (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    Phase Q → Alphabet I Γ Q →
      Option (Phase Q × Alphabet I Γ Q × DLBA.Dir)
  | .initFirst, some (.inl input) =>
      some (.initSweep,
        workSymbol ⟨true, false, embed input, .head M.initial⟩, .right)
  | .initFirst, _ => none
  | .initSweep, some (.inl input) =>
      some (.initSweep,
        workSymbol ⟨false, false, embed input, .plain⟩, .right)
  | .initSweep, some (.inr cell) =>
      some (.initBack, workSymbol { cell with right := true }, .left)
  | .initSweep, _ => none
  | .initBack, some (.inr cell) =>
      if cell.left then
        some (.scanRight, workSymbol cell, .stay)
      else
        some (.initBack, workSymbol cell, .left)
  | .initBack, _ => none
  | .scanRight, some (.inr cell) =>
      match cell.tag with
      | .head state => some (.query state, workSymbol cell, .stay)
      | .plain | .needLeft _ => some (continueRight cell)
  | .scanRight, _ => none
  | .query state, some (.inr cell) =>
      match M.transition state cell.symbol with
      | none => none
      | some (next, symbol, .stay) =>
          some (continueRight (cell.writeTagged symbol (.head next)))
      | some (next, symbol, .right) =>
          if cell.right then
            some (continueRight (cell.writeTagged symbol (.head next)))
          else
            some (.putRight next,
              workSymbol (cell.writeTagged symbol .plain), .right)
      | some (next, symbol, .left) =>
          if cell.left then
            some (continueRight (cell.writeTagged symbol (.head next)))
          else if cell.right then
            some (.putLeft next,
              workSymbol (cell.writeTagged symbol .plain), .left)
          else
            some (continueRight (cell.writeTagged symbol (.needLeft next)))
  | .query _, _ => none
  | .putRight state, some (.inr cell) =>
      some (continueRight (cell.withTag (.head state)))
  | .putRight _, _ => none
  | .scanLeft, some (.inr cell) =>
      match cell.tag with
      | .needLeft state =>
          some (.putLeft state, workSymbol (cell.withTag .plain), .left)
      | .plain | .head _ => some (continueLeft cell)
  | .scanLeft, _ => none
  | .putLeft state, some (.inr cell) =>
      some (continueLeft (cell.withTag (.head state)))
  | .putLeft _, _ => none

/-- The deterministic sweeping simulator as a `DLBA.Machine`.

Acceptance is visible only in a `query q` state.  If the source transition at that state and
symbol is `none`, the target halts there, reproducing the source DLBA's halt-and-test convention.
-/
public def machine (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    DLBA.Machine (Alphabet I Γ Q) (Phase Q) where
  transition := transition M embed
  accept
    | .query state => M.accept state
    | _ => false
  initial := .initFirst

@[simp]
public theorem machine_transition (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).transition = transition M embed := rfl

@[simp]
public theorem machine_initial (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).initial = .initFirst := rfl

@[simp]
public theorem machine_accept_query (M : DLBA.Machine Γ Q) (embed : I → Γ) (state : Q) :
    (machine M embed).accept (.query state) = M.accept state := rfl

@[simp]
public theorem machine_accept_initFirst (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).accept .initFirst = false := rfl

@[simp]
public theorem machine_accept_initSweep (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).accept .initSweep = false := rfl

@[simp]
public theorem machine_accept_initBack (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).accept .initBack = false := rfl

@[simp]
public theorem machine_accept_scanRight (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).accept .scanRight = false := rfl

@[simp]
public theorem machine_accept_putRight (M : DLBA.Machine Γ Q) (embed : I → Γ) (state : Q) :
    (machine M embed).accept (.putRight state) = false := rfl

@[simp]
public theorem machine_accept_scanLeft (M : DLBA.Machine Γ Q) (embed : I → Γ) :
    (machine M embed).accept .scanLeft = false := rfl

@[simp]
public theorem machine_accept_putLeft (M : DLBA.Machine Γ Q) (embed : I → Γ) (state : Q) :
    (machine M embed).accept (.putLeft state) = false := rfl

end DeterministicSweeping

namespace Machine

/-- A deterministic machine is sweeping through `embed` when its standard deterministic-to-LBA
view has only sweeping traces from canonical nonempty inputs.

This is a semantic restriction on one deterministic machine.  It does not identify the LBA and
DLBA language classes. -/
public def SweepingViaEmbed {I : Type u} {Γ : Type v} {Q : Type w}
    [DecidableEq Γ] (M : DLBA.Machine Γ Q) (embed : I → Γ) : Prop :=
  (DLBA.toLBA' M).SweepingViaEmbed embed

end Machine

end DLBA
