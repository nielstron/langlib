module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.StationaryDefinition
import Mathlib.Tactic

@[expose]
public section

/-!
# Raw edge inversion for the stationary shuttle

There are exactly two kinds of raw edge, even on malformed tapes: a normal/plain source writes
its private saved-instruction tag, or a pending state reading exactly that tag restores ordinary
data.  Both edges are stationary and flip the syntactic phase.
-/

namespace LBA

variable {Γ Λ : Type*}

@[simp]
public theorem stationary_moveHead_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) :
    tape.moveHead .stay = tape := by
  cases tape
  rfl

/-- Complete phase-explicit characterization of every stationary-shuttle edge, for every tape
width and every raw tape. -/
public theorem Machine.step_stationaryShuttle_iff
    (M : Machine Γ Λ) {n : ℕ}
    (source target :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n) :
    Step M.stationaryShuttle source target ↔
      (∃ (move : ShuttleMove Γ Λ)
          (tape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n),
        M.ShuttleStationaryEnabled move ∧
        tape.read = .plain move.old ∧
        source = ⟨.normal move.source, tape⟩ ∧
        target = ⟨.pending move, tape.write (.saved move)⟩) ∨
      (∃ (move : ShuttleMove Γ Λ)
          (tape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n),
        M.ShuttleStationaryEnabled move ∧
        tape.read = .saved move ∧
        source = ⟨.pending move, tape⟩ ∧
        target = ⟨.normal move.target, tape.write (.plain move.written)⟩) := by
  constructor
  · rintro ⟨next, written, direction, henabled, rfl⟩
    rcases source with ⟨state, tape⟩
    cases state with
    | normal state =>
        cases hread : tape.read with
        | plain old =>
            rw [hread] at henabled
            change ∃ move : ShuttleMove Γ Λ,
              M.ShuttleStationaryEnabled move ∧ move.source = state ∧
                move.old = old ∧
                (next, written, direction) =
                  (.pending move, .saved move, .stay) at henabled
            obtain ⟨move, hmove, hsource, hold, hout⟩ := henabled
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            subst state
            subst old
            exact Or.inl ⟨move, tape, hmove, hread, rfl, by simp⟩
        | saved observed =>
            rw [hread] at henabled
            simp [Machine.stationaryShuttle, stationaryShuttleTransition] at henabled
    | pending move =>
        cases hread : tape.read with
        | plain symbol =>
            rw [hread] at henabled
            simp [Machine.stationaryShuttle, stationaryShuttleTransition] at henabled
        | saved observed =>
            rw [hread] at henabled
            change observed = move ∧ M.ShuttleStationaryEnabled move ∧
              (next, written, direction) =
                (.normal move.target, .plain move.written, .stay) at henabled
            obtain ⟨hobserved, hmove, hout⟩ := henabled
            subst observed
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr ⟨move, tape, hmove, hread, rfl, by simp⟩
  · rintro (⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, tape, hmove, hread, rfl, rfl⟩)
    · refine ⟨.pending move, .saved move, .stay, ?_, by simp⟩
      rw [hread]
      exact ⟨move, hmove, rfl, rfl, rfl⟩
    · refine ⟨.normal move.target, .plain move.written, .stay, ?_, by simp⟩
      rw [hread]
      exact ⟨rfl, hmove, rfl⟩

/-- The first, tag-writing edge. -/
public theorem Machine.step_stationaryShuttle_save
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = .plain move.old) :
    Step M.stationaryShuttle
      ⟨.normal move.source, tape⟩
      ⟨.pending move, tape.write (.saved move)⟩ := by
  rw [M.step_stationaryShuttle_iff]
  exact Or.inl ⟨move, tape, henabled, hread, rfl, rfl⟩

/-- The second, tag-erasing edge. -/
public theorem Machine.step_stationaryShuttle_finish
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (StationaryShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = .saved move) :
    Step M.stationaryShuttle
      ⟨.pending move, tape⟩
      ⟨.normal move.target, tape.write (.plain move.written)⟩ := by
  rw [M.step_stationaryShuttle_iff]
  exact Or.inr ⟨move, tape, henabled, hread, rfl, rfl⟩

/-- Syntactic side of the stationary-shuttle graph. -/
@[expose]
public def stationaryShuttleParity : StationaryShuttleState Γ Λ → Bool
  | .normal _ => false
  | .pending _ => true

/-- Every raw stationary-shuttle edge crosses the syntactic bipartition. -/
public theorem Machine.stationaryShuttleParity_ne_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target :
      DLBA.Cfg (StationaryShuttleAlphabet Γ Λ) (StationaryShuttleState Γ Λ) n}
    (hstep : Step M.stationaryShuttle source target) :
    stationaryShuttleParity source.state ≠ stationaryShuttleParity target.state := by
  rw [M.step_stationaryShuttle_iff source target] at hstep
  rcases hstep with
      ⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, tape, hmove, hread, rfl, rfl⟩ <;>
    simp [stationaryShuttleParity]

end LBA
