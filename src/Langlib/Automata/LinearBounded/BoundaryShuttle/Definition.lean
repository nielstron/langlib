module

public import Langlib.Automata.LinearBounded.Functional
public import Langlib.Automata.LinearBounded.BoundedDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# A boundary-safe four-step shuttle for directional LBA moves

This file defines the local microprogram needed to execute a directional transition without
allowing a clamped landing to continue.  A source move

`(q, old) -> (target, written, direction)`

is expanded as follows (the neighbouring symbol is `neighbour`):

1. write the departure tag `K(move)` and move in `direction`;
2. write the disjoint neighbour tag `L(move, neighbour)` and move back;
3. restore `written` at the departure cell and move in `direction` again;
4. restore `neighbour` and enter `target` without moving.

On a genuine non-clamped move these four steps restore both cells and exactly implement the
source transition.  If any of the first three directional moves clamps, its landing state reads
the symbol it has just written, but that landing state has no transition on that constructor.
Thus every such boundary collision is terminal.

The construction deliberately retains the complete source instruction in both tags and in all
protocol states.  Forgetting that instruction in the fourth step still needs a source normal
form: `DirectionalTargetInjective` says that a target control state names at most one enabled
directional instruction.  This is stronger than injectivity of the ordinary local transition
function and is the precise state-splitting obligation left to a surrounding reversible
compiler.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Complete data of one source-machine instruction. -/
public structure ShuttleMove (Γ Λ : Type*) where
  source : Λ
  old : Γ
  target : Λ
  written : Γ
  direction : DLBA.Dir
  deriving DecidableEq, Fintype

/-- The instruction represented by a shuttle tag is genuinely enabled by `M`. -/
@[expose]
public def Machine.ShuttleEnabled (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) : Prop :=
  (move.target, move.written, move.direction) ∈
    M.transition move.source move.old

/-- Only left- and right-moving source instructions are handled by this microcompiler.  Stay
moves can first be eliminated or split by a separate stationary normal form. -/
@[expose]
public def ShuttleMove.Directional (move : ShuttleMove Γ Λ) : Prop :=
  move.direction ≠ .stay

/-- Enabled directional instructions. -/
@[expose]
public def Machine.ShuttleDirectionalEnabled
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) : Prop :=
  M.ShuttleEnabled move ∧ move.Directional

/-- Reverse a physical head direction. -/
@[expose]
public def reverseDirection : DLBA.Dir → DLBA.Dir
  | .left => .right
  | .right => .left
  | .stay => .stay

@[simp]
public theorem reverseDirection_reverseDirection (direction : DLBA.Dir) :
    reverseDirection (reverseDirection direction) = direction := by
  cases direction <;> rfl

@[simp]
public theorem reverseDirection_eq_stay_iff {direction : DLBA.Dir} :
    reverseDirection direction = .stay ↔ direction = .stay := by
  cases direction <;> simp [reverseDirection]

/-- Tape alphabet of the shuttle compiler.  `plain` is the semantic source alphabet; `departure`
and `neighbour` are disjoint protocol alphabets. -/
public inductive ShuttleAlphabet (Γ Λ : Type*) where
  | plain (symbol : Γ)
  | departure (move : ShuttleMove Γ Λ)
  | neighbour (move : ShuttleMove Γ Λ) (symbol : Γ)
  deriving DecidableEq, Fintype

/-- Control phases of the four-step shuttle. -/
public inductive ShuttleState (Γ Λ : Type*) where
  | normal (state : Λ)
  | atNeighbour (move : ShuttleMove Γ Λ)
  | atDeparture (move : ShuttleMove Γ Λ) (neighbour : Γ)
  | restoreNeighbour (move : ShuttleMove Γ Λ) (neighbour : Γ)
  deriving DecidableEq, Fintype

/-- The raw transition relation of the shuttle compiler.

Every protocol phase rechecks that its saved instruction is enabled.  Consequently arbitrary
raw states carrying a fabricated instruction are sinks rather than extra computations. -/
@[expose]
public def shuttleTransition (M : Machine Γ Λ) :
    ShuttleState Γ Λ → ShuttleAlphabet Γ Λ →
      Set (ShuttleState Γ Λ × ShuttleAlphabet Γ Λ × DLBA.Dir)
  | .normal state, .plain old =>
      {output | ∃ move : ShuttleMove Γ Λ,
        M.ShuttleDirectionalEnabled move ∧
        move.source = state ∧ move.old = old ∧
        output = (.atNeighbour move, .departure move, move.direction)}
  | .atNeighbour move, .plain neighbour =>
      {output | M.ShuttleDirectionalEnabled move ∧
        output = (.atDeparture move neighbour, .neighbour move neighbour,
          reverseDirection move.direction)}
  | .atDeparture move neighbour, .departure observed =>
      {output | observed = move ∧ M.ShuttleDirectionalEnabled move ∧
        output = (.restoreNeighbour move neighbour, .plain move.written,
          move.direction)}
  | .restoreNeighbour move neighbour, .neighbour observed observedNeighbour =>
      {output | observed = move ∧ observedNeighbour = neighbour ∧
        M.ShuttleDirectionalEnabled move ∧
        output = (.normal move.target, .plain neighbour, .stay)}
  | _, _ => ∅

/-- Compile all directional instructions of `M` into boundary-safe four-step shuttles. -/
@[expose]
public def Machine.boundaryShuttle (M : Machine Γ Λ) :
    Machine (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) where
  transition := shuttleTransition M
  accept
    | .normal state => M.accept state
    | _ => false
  initial := .normal M.initial

/-- Embed a source tape by tagging every cell as ordinary data. -/
@[expose]
public def shuttleTape {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n :=
  ⟨ShuttleAlphabet.plain ∘ tape.contents, tape.head⟩

/-- Embed a source configuration in the semantic (`normal`) phase. -/
@[expose]
public def shuttleCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
  ⟨.normal cfg.state, shuttleTape cfg.tape⟩

@[simp]
public theorem shuttleTape_read {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (shuttleTape (Λ := Λ) tape).read = .plain tape.read := rfl

@[simp]
public theorem boundaryShuttle_accept_normal
    (M : Machine Γ Λ) (state : Λ) :
    M.boundaryShuttle.accept (.normal state) = M.accept state := rfl

@[simp]
public theorem boundaryShuttle_accept_atNeighbour
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) :
    M.boundaryShuttle.accept (.atNeighbour move) = false := rfl

@[simp]
public theorem boundaryShuttle_accept_atDeparture
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) (symbol : Γ) :
    M.boundaryShuttle.accept (.atDeparture move symbol) = false := rfl

@[simp]
public theorem boundaryShuttle_accept_restoreNeighbour
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) (symbol : Γ) :
    M.boundaryShuttle.accept (.restoreNeighbour move symbol) = false := rfl

/-! ## Exact local hypotheses -/

/-- Each semantic source row selects at most one directional instruction.  Ordinary
`Machine.Functional` implies this property. -/
@[expose]
public def Machine.DirectionalFunctional (M : Machine Γ Λ) : Prop :=
  ∀ move₁ move₂ : ShuttleMove Γ Λ,
    M.ShuttleDirectionalEnabled move₁ →
    M.ShuttleDirectionalEnabled move₂ →
    move₁.source = move₂.source → move₁.old = move₂.old →
    move₁ = move₂

/-- The target control state uniquely names its incoming directional instruction.

This condition is intentionally stated on full instructions, including source state and old
symbol.  It is the exact hypothesis that bounds predecessors of the final tag-forgetting step;
plain injectivity of `(source, old) ↦ (target, written, direction)` is not by itself enough on
malformed raw tapes. -/
@[expose]
public def Machine.DirectionalTargetInjective (M : Machine Γ Λ) : Prop :=
  ∀ move₁ move₂ : ShuttleMove Γ Λ,
    M.ShuttleDirectionalEnabled move₁ →
    M.ShuttleDirectionalEnabled move₂ →
    move₁.target = move₂.target →
    move₁ = move₂

/-- A functional source transition table selects at most one saved shuttle instruction from a
given semantic state and scanned symbol. -/
public theorem Machine.directionalFunctional_of_functional
    (M : Machine Γ Λ) (hfunctional : M.Functional) :
    M.DirectionalFunctional := by
  intro move₁ move₂ h₁ h₂ hsource hold
  have hlocal :
      (move₁.target, move₁.written, move₁.direction) =
        (move₂.target, move₂.written, move₂.direction) := by
    apply hfunctional move₁.source move₁.old h₁.1
    simpa only [hsource, hold] using h₂.1
  cases move₁
  cases move₂
  simp_all

/-- Under row functionality, every raw shuttle configuration has at most one successor. -/
public theorem Machine.boundaryShuttle_functional
    (M : Machine Γ Λ) (hfunctional : M.DirectionalFunctional) :
    M.boundaryShuttle.Functional := by
  intro state symbol left hleft right hright
  cases state <;> cases symbol <;>
    simp only [Machine.boundaryShuttle, shuttleTransition] at hleft hright
  · obtain ⟨leftMove, hleftEnabled, hleftSource, hleftOld, rfl⟩ := hleft
    obtain ⟨rightMove, hrightEnabled, hrightSource, hrightOld, rfl⟩ := hright
    have hmove : leftMove = rightMove :=
      hfunctional leftMove rightMove hleftEnabled hrightEnabled
        (hleftSource.trans hrightSource.symm) (hleftOld.trans hrightOld.symm)
    subst rightMove
    rfl
  all_goals simp_all

end LBA

