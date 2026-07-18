module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.StationaryDefinition
import Mathlib.Tactic

@[expose]
public section

/-!
# One boundary shuttle for directional and stationary moves

This module combines the four-step directional protocol and the two-step stationary protocol.
The two protocols share precisely the semantic `plain` tape constructor and `normal` control
states; every tag and intermediate state remains kind-specific.  Thus every enabled source
instruction is represented, while malformed raw tapes cannot confuse protocol phases.

The construction is still only a local compiler.  Directional instructions that point out of a
bounded tape deliberately halt after a clamped tagged move.  Consequently the positive canonical
simulation theorems do not by themselves give whole-language equivalence or run reflection.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Unified tape alphabet.  All four protocol tags are pairwise disjoint. -/
public inductive CombinedShuttleAlphabet (Γ Λ : Type*) where
  | plain (symbol : Γ)
  | directionalDeparture (move : ShuttleMove Γ Λ)
  | directionalNeighbour (move : ShuttleMove Γ Λ) (symbol : Γ)
  | stationarySaved (move : ShuttleMove Γ Λ)
  deriving DecidableEq, Fintype

/-- Unified control states with one shared semantic phase. -/
public inductive CombinedShuttleState (Γ Λ : Type*) where
  | normal (state : Λ)
  | directionalAtNeighbour (move : ShuttleMove Γ Λ)
  | directionalAtDeparture (move : ShuttleMove Γ Λ) (neighbour : Γ)
  | directionalRestoreNeighbour (move : ShuttleMove Γ Λ) (neighbour : Γ)
  | stationaryPending (move : ShuttleMove Γ Λ)
  deriving DecidableEq, Fintype

/-- Raw transition table of the combined compiler.

The first clause is the only shared clause.  Its two disjuncts partition enabled instructions by
direction.  Every intermediate clause rechecks the saved source instruction, so fabricated
protocol states are sinks. -/
@[expose]
public def combinedShuttleTransition (M : Machine Γ Λ) :
    CombinedShuttleState Γ Λ → CombinedShuttleAlphabet Γ Λ →
      Set (CombinedShuttleState Γ Λ × CombinedShuttleAlphabet Γ Λ × DLBA.Dir)
  | .normal state, .plain old =>
      {output |
        (∃ move : ShuttleMove Γ Λ,
          M.ShuttleDirectionalEnabled move ∧ move.source = state ∧ move.old = old ∧
          output = (.directionalAtNeighbour move,
            .directionalDeparture move, move.direction)) ∨
        (∃ move : ShuttleMove Γ Λ,
          M.ShuttleStationaryEnabled move ∧ move.source = state ∧ move.old = old ∧
          output = (.stationaryPending move, .stationarySaved move, .stay))}
  | .directionalAtNeighbour move, .plain neighbour =>
      {output | M.ShuttleDirectionalEnabled move ∧
        output = (.directionalAtDeparture move neighbour,
          .directionalNeighbour move neighbour, reverseDirection move.direction)}
  | .directionalAtDeparture move neighbour, .directionalDeparture observed =>
      {output | observed = move ∧ M.ShuttleDirectionalEnabled move ∧
        output = (.directionalRestoreNeighbour move neighbour,
          .plain move.written, move.direction)}
  | .directionalRestoreNeighbour move neighbour,
      .directionalNeighbour observed observedNeighbour =>
      {output | observed = move ∧ observedNeighbour = neighbour ∧
        M.ShuttleDirectionalEnabled move ∧
        output = (.normal move.target, .plain neighbour, .stay)}
  | .stationaryPending move, .stationarySaved observed =>
      {output | observed = move ∧ M.ShuttleStationaryEnabled move ∧
        output = (.normal move.target, .plain move.written, .stay)}
  | _, _ => ∅

/-- Compile all enabled source instructions, choosing the protocol from their direction. -/
@[expose]
public def Machine.combinedBoundaryShuttle (M : Machine Γ Λ) :
    Machine (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) where
  transition := combinedShuttleTransition M
  accept
    | .normal state => M.accept state
    | _ => false
  initial := .normal M.initial

/-- Plain embedding of a source tape. -/
@[expose]
public def combinedShuttleTape {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n :=
  ⟨CombinedShuttleAlphabet.plain ∘ tape.contents, tape.head⟩

/-- Plain/normal embedding of a source configuration. -/
@[expose]
public def combinedShuttleCfg {n : ℕ} (cfg : DLBA.Cfg Γ Λ n) :
    DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n :=
  ⟨.normal cfg.state, combinedShuttleTape cfg.tape⟩

@[simp]
public theorem combinedShuttleTape_read {n : ℕ} (tape : DLBA.BoundedTape Γ n) :
    (combinedShuttleTape (Λ := Λ) tape).read = .plain tape.read := rfl

@[simp]
public theorem combinedBoundaryShuttle_accept_normal
    (M : Machine Γ Λ) (state : Λ) :
    M.combinedBoundaryShuttle.accept (.normal state) = M.accept state := rfl

@[simp]
public theorem combinedBoundaryShuttle_accept_directionalAtNeighbour
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) :
    M.combinedBoundaryShuttle.accept (.directionalAtNeighbour move) = false := rfl

@[simp]
public theorem combinedBoundaryShuttle_accept_directionalAtDeparture
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) (symbol : Γ) :
    M.combinedBoundaryShuttle.accept (.directionalAtDeparture move symbol) = false := rfl

@[simp]
public theorem combinedBoundaryShuttle_accept_directionalRestoreNeighbour
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) (symbol : Γ) :
    M.combinedBoundaryShuttle.accept (.directionalRestoreNeighbour move symbol) = false := rfl

@[simp]
public theorem combinedBoundaryShuttle_accept_stationaryPending
    (M : Machine Γ Λ) (move : ShuttleMove Γ Λ) :
    M.combinedBoundaryShuttle.accept (.stationaryPending move) = false := rfl

/-- Functionality of the source transition table gives functionality of the entire raw combined
microprogram, including the directional/stationary choice at a shared normal state. -/
public theorem Machine.combinedBoundaryShuttle_functional
    (M : Machine Γ Λ) (hfunctional : M.Functional) :
    M.combinedBoundaryShuttle.Functional := by
  intro state symbol left hleft right hright
  cases state <;> cases symbol <;>
    simp only [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at hleft hright
  · rcases hleft with
      ⟨leftMove, hleftEnabled, hleftSource, hleftOld, rfl⟩ |
      ⟨leftMove, hleftEnabled, hleftSource, hleftOld, rfl⟩
    · rcases hright with
      ⟨rightMove, hrightEnabled, hrightSource, hrightOld, rfl⟩ |
      ⟨rightMove, hrightEnabled, hrightSource, hrightOld, rfl⟩
      · have hlocal :
            (leftMove.target, leftMove.written, leftMove.direction) =
              (rightMove.target, rightMove.written, rightMove.direction) := by
          apply hfunctional leftMove.source leftMove.old hleftEnabled.1
          rw [hleftSource, hleftOld, ← hrightSource, ← hrightOld]
          exact hrightEnabled.1
        have hmove : leftMove = rightMove := by
          cases leftMove
          cases rightMove
          simp_all
        subst rightMove
        rfl
      · have hlocal :
            (leftMove.target, leftMove.written, leftMove.direction) =
              (rightMove.target, rightMove.written, rightMove.direction) := by
          apply hfunctional leftMove.source leftMove.old hleftEnabled.1
          rw [hleftSource, hleftOld, ← hrightSource, ← hrightOld]
          exact hrightEnabled.1
        have hmove : leftMove = rightMove := by
          cases leftMove
          cases rightMove
          simp_all
        subst rightMove
        exact False.elim (hleftEnabled.2 hrightEnabled.2)
    · rcases hright with
      ⟨rightMove, hrightEnabled, hrightSource, hrightOld, rfl⟩ |
      ⟨rightMove, hrightEnabled, hrightSource, hrightOld, rfl⟩
      · have hlocal :
            (leftMove.target, leftMove.written, leftMove.direction) =
              (rightMove.target, rightMove.written, rightMove.direction) := by
          apply hfunctional leftMove.source leftMove.old hleftEnabled.1
          rw [hleftSource, hleftOld, ← hrightSource, ← hrightOld]
          exact hrightEnabled.1
        have hmove : leftMove = rightMove := by
          cases leftMove
          cases rightMove
          simp_all
        subst rightMove
        exact False.elim (hrightEnabled.2 hleftEnabled.2)
      · have hlocal :
            (leftMove.target, leftMove.written, leftMove.direction) =
              (rightMove.target, rightMove.written, rightMove.direction) := by
          apply hfunctional leftMove.source leftMove.old hleftEnabled.1
          rw [hleftSource, hleftOld, ← hrightSource, ← hrightOld]
          exact hrightEnabled.1
        have hmove : leftMove = rightMove := by
          cases leftMove
          cases rightMove
          simp_all
        subst rightMove
        rfl
  all_goals simp_all

end LBA
