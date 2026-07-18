module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# A two-step tagged compiler for stationary LBA moves

This is the stationary counterpart of `Machine.boundaryShuttle`.  An enabled source
instruction

`(source, old) -> (target, written, stay)`

is expanded into two stationary microsteps:

1. replace `old` by a private tag carrying the complete instruction, and enter a private
   pending state carrying the same instruction;
2. recheck the tag and the source transition table, replace it by `written`, and enter the
   ordinary target state.

Because neither microstep moves the head, there is no boundary case and no clamped inverse-head
ambiguity.  The exact reverse-determinism condition is correspondingly weaker than the one for
the directional shuttle: among enabled stay instructions, `(target, written)` must determine the
complete instruction.  The written symbol is observable in the final raw configuration, so it
does not need to be encoded in the target control state.

This construction is deliberately standalone.  It does not yet combine its alphabet and state
types with `boundaryShuttle`; the cross-kind condition needed for such a sum is recorded below as
`Machine.ShuttleTargetKindDisjoint`.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- A saved shuttle instruction is stationary. -/
@[expose]
public def ShuttleMove.Stationary (move : ShuttleMove Γ Λ) : Prop :=
  move.direction = .stay

/-- Enabled stationary source instructions. -/
@[expose]
public def Machine.ShuttleStationaryEnabled
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) : Prop :=
  M.ShuttleEnabled move ∧ move.Stationary

/-- Tape alphabet for the stationary compiler.  The saved constructor is a private protocol
symbol and retains the complete source instruction. -/
public inductive StationaryShuttleAlphabet (Γ Λ : Type*) where
  | plain (symbol : Γ)
  | saved (move : ShuttleMove Γ Λ)
  deriving DecidableEq, Fintype

/-- Control states for the stationary compiler. -/
public inductive StationaryShuttleState (Γ Λ : Type*) where
  | normal (state : Λ)
  | pending (move : ShuttleMove Γ Λ)
  deriving DecidableEq, Fintype

/-- The raw two-step stationary protocol.  A fabricated pending state is a sink unless its saved
instruction is genuinely enabled and the scanned tag agrees with it. -/
@[expose]
public def stationaryShuttleTransition (M : Machine Γ Λ) :
    StationaryShuttleState Γ Λ → StationaryShuttleAlphabet Γ Λ →
      Set (StationaryShuttleState Γ Λ × StationaryShuttleAlphabet Γ Λ × DLBA.Dir)
  | .normal state, .plain old =>
      {output | ∃ move : ShuttleMove Γ Λ,
        M.ShuttleStationaryEnabled move ∧
        move.source = state ∧ move.old = old ∧
        output = (.pending move, .saved move, .stay)}
  | .pending move, .saved observed =>
      {output | observed = move ∧ M.ShuttleStationaryEnabled move ∧
        output = (.normal move.target, .plain move.written, .stay)}
  | _, _ => ∅

/-- Compile all enabled stay instructions of `M` into private two-step protocols. -/
@[expose]
public def Machine.stationaryShuttle (M : Machine Γ Λ) :
    Machine (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) where
  transition := stationaryShuttleTransition M
  accept
    | .normal state => M.accept state
    | .pending _ => false
  initial := .normal M.initial

/-- Embed a source tape by making every cell ordinary data. -/
@[expose]
public def stationaryShuttleTape {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n :=
  ⟨StationaryShuttleAlphabet.plain ∘ tape.contents, tape.head⟩

/-- Embed a source configuration in the normal phase. -/
@[expose]
public def stationaryShuttleCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n :=
  ⟨.normal cfg.state, stationaryShuttleTape cfg.tape⟩

@[simp]
public theorem stationaryShuttleTape_read {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (stationaryShuttleTape (Λ := Λ) tape).read = .plain tape.read := rfl

@[simp]
public theorem stationaryShuttle_accept_normal
    (M : Machine Γ Λ) (state : Λ) :
    M.stationaryShuttle.accept (.normal state) = M.accept state := rfl

@[simp]
public theorem stationaryShuttle_accept_pending
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) :
    M.stationaryShuttle.accept (.pending move) = false := rfl

/-! ## Exact local hypotheses -/

/-- Each semantic source row selects at most one enabled stationary instruction. -/
@[expose]
public def Machine.StationaryFunctional (M : Machine Γ Λ) : Prop :=
  ∀ move₁ move₂ : ShuttleMove Γ Λ,
    M.ShuttleStationaryEnabled move₁ →
    M.ShuttleStationaryEnabled move₂ →
    move₁.source = move₂.source → move₁.old = move₂.old →
    move₁ = move₂

/-- The weakest local backward-injectivity condition needed by the standalone stationary
compiler: the target state together with the symbol visible after the final write identifies the
complete enabled stay instruction. -/
@[expose]
public def Machine.StationaryTargetWrittenInjective (M : Machine Γ Λ) : Prop :=
  ∀ move₁ move₂ : ShuttleMove Γ Λ,
    M.ShuttleStationaryEnabled move₁ →
    M.ShuttleStationaryEnabled move₂ →
    move₁.target = move₂.target → move₁.written = move₂.written →
    move₁ = move₂

/-- Ordinary local functionality implies stationary row functionality. -/
public theorem Machine.stationaryFunctional_of_functional
    (M : Machine Γ Λ) (hfunctional : M.Functional) :
    M.StationaryFunctional := by
  intro move₁ move₂ h₁ h₂ hsource hold
  have hlocal :
      (move₁.target, move₁.written, move₁.direction) =
        (move₂.target, move₂.written, move₂.direction) := by
    apply hfunctional move₁.source move₁.old h₁.1
    simpa only [hsource, hold] using h₂.1
  cases move₁
  cases move₂
  simp_all

/-- Under row functionality, every raw stationary-shuttle state/symbol pair has at most one
local successor instruction. -/
public theorem Machine.stationaryShuttle_functional
    (M : Machine Γ Λ) (hfunctional : M.StationaryFunctional) :
    M.stationaryShuttle.Functional := by
  intro state symbol left hleft right hright
  cases state <;> cases symbol <;>
    simp only [Machine.stationaryShuttle, stationaryShuttleTransition] at hleft hright
  · obtain ⟨leftMove, hleftEnabled, hleftSource, hleftOld, rfl⟩ := hleft
    obtain ⟨rightMove, hrightEnabled, hrightSource, hrightOld, rfl⟩ := hright
    have hmove : leftMove = rightMove :=
      hfunctional leftMove rightMove hleftEnabled hrightEnabled
        (hleftSource.trans hrightSource.symm) (hleftOld.trans hrightOld.symm)
    subst rightMove
    rfl
  all_goals simp_all

/-! ## The extra condition required by a combined directional/stationary compiler -/

/-- No target control state receives both an enabled directional instruction and an enabled
stationary instruction.

This source normal form is needed when the two standalone shuttles are combined with shared
`normal` states.  A directional final edge restores an arbitrary neighbouring plain symbol,
whereas a stationary final edge writes its saved `written` symbol.  On malformed raw tapes those
symbols can coincide.  If both instructions also share their target state, the two final edges
can merge into the same normal configuration, which may immediately continue.  Written-symbol
disjointness cannot prevent this because the directional landing symbol is arbitrary; separating
the *target-state kinds* (or retaining a kind tag through a later reversible join) does.
-/
@[expose]
public def Machine.ShuttleTargetKindDisjoint (M : Machine Γ Λ) : Prop :=
  ∀ directional stationary : ShuttleMove Γ Λ,
    M.ShuttleDirectionalEnabled directional →
    M.ShuttleStationaryEnabled stationary →
    directional.target ≠ stationary.target

end LBA
