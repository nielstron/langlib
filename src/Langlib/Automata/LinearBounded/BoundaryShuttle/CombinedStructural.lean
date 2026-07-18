module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedDefinition
import Mathlib.Tactic

@[expose]
public section

/-!
# Exact raw edges of the combined shuttle

The six disjuncts below classify every edge at every tape width, including widths zero and one
and tapes containing arbitrary malformed tags.  The classification also proves that the shared
normal phase introduces no hidden seventh edge kind.
-/

namespace LBA

variable {Γ Λ : Type*}

@[simp]
public theorem combined_moveHead_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) : tape.moveHead .stay = tape := by
  cases tape
  rfl

/-- Syntactic bipartition shared by the four-edge and two-edge protocols. -/
@[expose]
public def combinedShuttleParity : CombinedShuttleState Γ Λ → Bool
  | .normal _ => false
  | .directionalAtNeighbour _ => true
  | .directionalAtDeparture _ _ => false
  | .directionalRestoreNeighbour _ _ => true
  | .stationaryPending _ => true

/-- Complete six-case inversion theorem for the combined raw step relation. -/
public theorem Machine.step_combinedBoundaryShuttle_iff
    (M : Machine Γ Λ) {n : ℕ}
    (source target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n) :
    Step M.combinedBoundaryShuttle source target ↔
      (∃ (move : ShuttleMove Γ Λ)
          (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .plain move.old ∧
        source = ⟨.normal move.source, tape⟩ ∧
        target = ⟨.directionalAtNeighbour move,
          (tape.write (.directionalDeparture move)).moveHead move.direction⟩) ∨
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .plain neighbour ∧
        source = ⟨.directionalAtNeighbour move, tape⟩ ∧
        target = ⟨.directionalAtDeparture move neighbour,
          (tape.write (.directionalNeighbour move neighbour)).moveHead
            (reverseDirection move.direction)⟩) ∨
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .directionalDeparture move ∧
        source = ⟨.directionalAtDeparture move neighbour, tape⟩ ∧
        target = ⟨.directionalRestoreNeighbour move neighbour,
          (tape.write (.plain move.written)).moveHead move.direction⟩) ∨
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .directionalNeighbour move neighbour ∧
        source = ⟨.directionalRestoreNeighbour move neighbour, tape⟩ ∧
        target = ⟨.normal move.target, tape.write (.plain neighbour)⟩) ∨
      (∃ (move : ShuttleMove Γ Λ)
          (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleStationaryEnabled move ∧
        tape.read = .plain move.old ∧
        source = ⟨.normal move.source, tape⟩ ∧
        target = ⟨.stationaryPending move,
          tape.write (.stationarySaved move)⟩) ∨
      (∃ (move : ShuttleMove Γ Λ)
          (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n),
        M.ShuttleStationaryEnabled move ∧
        tape.read = .stationarySaved move ∧
        source = ⟨.stationaryPending move, tape⟩ ∧
        target = ⟨.normal move.target, tape.write (.plain move.written)⟩) := by
  constructor
  · rintro ⟨next, written, direction, henabled, rfl⟩
    rcases source with ⟨state, tape⟩
    cases state with
    | normal state =>
        cases hread : tape.read with
        | plain old =>
            rw [hread] at henabled
            change
              (∃ move : ShuttleMove Γ Λ,
                M.ShuttleDirectionalEnabled move ∧ move.source = state ∧
                  move.old = old ∧
                  (next, written, direction) =
                    (.directionalAtNeighbour move,
                      .directionalDeparture move, move.direction)) ∨
              (∃ move : ShuttleMove Γ Λ,
                M.ShuttleStationaryEnabled move ∧ move.source = state ∧
                  move.old = old ∧
                  (next, written, direction) =
                    (.stationaryPending move, .stationarySaved move, .stay)) at henabled
            rcases henabled with
                ⟨move, hmove, hsource, hold, hout⟩ |
                ⟨move, hmove, hsource, hold, hout⟩
            · simp only [Prod.mk.injEq] at hout
              rcases hout with ⟨rfl, rfl, rfl⟩
              subst state
              subst old
              exact Or.inl ⟨move, tape, hmove, hread, rfl, rfl⟩
            · simp only [Prod.mk.injEq] at hout
              rcases hout with ⟨rfl, rfl, rfl⟩
              subst state
              subst old
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨move, tape, hmove, hread, rfl, by simp⟩))))
        | directionalDeparture observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalNeighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | stationarySaved observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
    | directionalAtNeighbour move =>
        cases hread : tape.read with
        | plain neighbour =>
            rw [hread] at henabled
            change M.ShuttleDirectionalEnabled move ∧
              (next, written, direction) =
                (.directionalAtDeparture move neighbour,
                  .directionalNeighbour move neighbour,
                  reverseDirection move.direction) at henabled
            obtain ⟨hmove, hout⟩ := henabled
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr (Or.inl ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩)
        | directionalDeparture observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalNeighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | stationarySaved observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
    | directionalAtDeparture move neighbour =>
        cases hread : tape.read with
        | plain symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalDeparture observed =>
            rw [hread] at henabled
            change observed = move ∧ M.ShuttleDirectionalEnabled move ∧
              (next, written, direction) =
                (.directionalRestoreNeighbour move neighbour,
                  .plain move.written, move.direction) at henabled
            obtain ⟨hobserved, hmove, hout⟩ := henabled
            subst observed
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr (Or.inr (Or.inl
              ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩))
        | directionalNeighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | stationarySaved observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
    | directionalRestoreNeighbour move neighbour =>
        cases hread : tape.read with
        | plain symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalDeparture observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalNeighbour observed observedNeighbour =>
            rw [hread] at henabled
            change observed = move ∧ observedNeighbour = neighbour ∧
              M.ShuttleDirectionalEnabled move ∧
              (next, written, direction) =
                (.normal move.target, .plain neighbour, .stay) at henabled
            obtain ⟨hobserved, hobservedNeighbour, hmove, hout⟩ := henabled
            subst observed
            subst observedNeighbour
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨move, neighbour, tape, hmove, hread, rfl, by simp⟩)))
        | stationarySaved observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
    | stationaryPending move =>
        cases hread : tape.read with
        | plain symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalDeparture observed =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | directionalNeighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled
        | stationarySaved observed =>
            rw [hread] at henabled
            change observed = move ∧ M.ShuttleStationaryEnabled move ∧
              (next, written, direction) =
                (.normal move.target, .plain move.written, .stay) at henabled
            obtain ⟨hobserved, hmove, hout⟩ := henabled
            subst observed
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨move, tape, hmove, hread, rfl, by simp⟩))))
  · rintro (⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, tape, hmove, hread, rfl, rfl⟩)
    · refine ⟨.directionalAtNeighbour move, .directionalDeparture move,
        move.direction, ?_, rfl⟩
      rw [hread]
      exact Or.inl ⟨move, hmove, rfl, rfl, rfl⟩
    · refine ⟨.directionalAtDeparture move neighbour,
        .directionalNeighbour move neighbour, reverseDirection move.direction,
        ?_, rfl⟩
      rw [hread]
      exact ⟨hmove, rfl⟩
    · refine ⟨.directionalRestoreNeighbour move neighbour, .plain move.written,
        move.direction, ?_, rfl⟩
      rw [hread]
      exact ⟨rfl, hmove, rfl⟩
    · refine ⟨.normal move.target, .plain neighbour, .stay, ?_, by simp⟩
      rw [hread]
      exact ⟨rfl, rfl, hmove, rfl⟩
    · refine ⟨.stationaryPending move, .stationarySaved move, .stay, ?_, by simp⟩
      rw [hread]
      exact Or.inr ⟨move, hmove, rfl, rfl, rfl⟩
    · refine ⟨.normal move.target, .plain move.written, .stay, ?_, by simp⟩
      rw [hread]
      exact ⟨rfl, hmove, rfl⟩

/-- Every raw edge flips syntactic parity, including every malformed-tape edge. -/
public theorem Machine.combinedShuttleParity_ne_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle source target) :
    combinedShuttleParity source.state ≠ combinedShuttleParity target.state := by
  rw [M.step_combinedBoundaryShuttle_iff source target] at hstep
  rcases hstep with
      ⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, tape, hmove, hread, rfl, rfl⟩ <;>
    simp [combinedShuttleParity]

/-! Named constructors for all six raw edge kinds. -/

public theorem Machine.step_combinedShuttle_directionalStart
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .plain move.old) :
    Step M.combinedBoundaryShuttle
      ⟨.normal move.source, tape⟩
      ⟨.directionalAtNeighbour move,
        (tape.write (.directionalDeparture move)).moveHead move.direction⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff]
  exact Or.inl ⟨move, tape, henabled, hread, rfl, rfl⟩

public theorem Machine.step_combinedShuttle_directionalTagNeighbour
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (neighbour : Γ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .plain neighbour) :
    Step M.combinedBoundaryShuttle
      ⟨.directionalAtNeighbour move, tape⟩
      ⟨.directionalAtDeparture move neighbour,
        (tape.write (.directionalNeighbour move neighbour)).moveHead
          (reverseDirection move.direction)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff]
  exact Or.inr (Or.inl ⟨move, neighbour, tape, henabled, hread, rfl, rfl⟩)

public theorem Machine.step_combinedShuttle_directionalRestoreDeparture
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (neighbour : Γ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .directionalDeparture move) :
    Step M.combinedBoundaryShuttle
      ⟨.directionalAtDeparture move neighbour, tape⟩
      ⟨.directionalRestoreNeighbour move neighbour,
        (tape.write (.plain move.written)).moveHead move.direction⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff]
  exact Or.inr (Or.inr (Or.inl
    ⟨move, neighbour, tape, henabled, hread, rfl, rfl⟩))

public theorem Machine.step_combinedShuttle_directionalFinish
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (neighbour : Γ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .directionalNeighbour move neighbour) :
    Step M.combinedBoundaryShuttle
      ⟨.directionalRestoreNeighbour move neighbour, tape⟩
      ⟨.normal move.target, tape.write (.plain neighbour)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inl
    ⟨move, neighbour, tape, henabled, hread, rfl, rfl⟩)))

public theorem Machine.step_combinedShuttle_stationarySave
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = .plain move.old) :
    Step M.combinedBoundaryShuttle
      ⟨.normal move.source, tape⟩
      ⟨.stationaryPending move, tape.write (.stationarySaved move)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨move, tape, henabled, hread, rfl, rfl⟩))))

public theorem Machine.step_combinedShuttle_stationaryFinish
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleStationaryEnabled move)
    (hread : tape.read = .stationarySaved move) :
    Step M.combinedBoundaryShuttle
      ⟨.stationaryPending move, tape⟩
      ⟨.normal move.target, tape.write (.plain move.written)⟩ := by
  rw [M.step_combinedBoundaryShuttle_iff]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨move, tape, henabled, hread, rfl, rfl⟩))))

/-- Every enabled source instruction has a first compiled edge.  This includes outward-pointing
directional instructions: their first edge exists, while the subsequent clamped tagged landing
is deliberately terminal. -/
public theorem Machine.step_combinedShuttle_start_of_enabled
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleEnabled move)
    (hread : tape.read = .plain move.old) :
    (move.direction = .stay ∧
      Step M.combinedBoundaryShuttle
        ⟨.normal move.source, tape⟩
        ⟨.stationaryPending move, tape.write (.stationarySaved move)⟩) ∨
    (move.direction ≠ .stay ∧
      Step M.combinedBoundaryShuttle
        ⟨.normal move.source, tape⟩
        ⟨.directionalAtNeighbour move,
          (tape.write (.directionalDeparture move)).moveHead move.direction⟩) := by
  by_cases hstay : move.direction = .stay
  · exact Or.inl ⟨hstay,
      M.step_combinedShuttle_stationarySave move tape ⟨henabled, hstay⟩ hread⟩
  · exact Or.inr ⟨hstay,
      M.step_combinedShuttle_directionalStart move tape ⟨henabled, hstay⟩ hread⟩

end LBA
