module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# Raw graph structure of the boundary shuttle

This file gives an exact four-case inversion theorem for every raw configuration edge.  It also
records the syntactic bipartition of the protocol graph.  The phase parity flips on every edge,
including malformed raw-tape edges; a complete semantic shuttle has four edges and hence returns
to the original parity.
-/

namespace LBA

variable {Γ Λ : Type*}

/-- Syntactic side of the shuttle configuration graph. -/
@[expose]
public def shuttleParity : ShuttleState Γ Λ → Bool
  | .normal _ => false
  | .atNeighbour _ => true
  | .atDeparture _ _ => false
  | .restoreNeighbour _ _ => true

/-- Complete phase-explicit characterization of every low-level edge, over every tape width and
every raw tape. -/
public theorem Machine.step_boundaryShuttle_iff
    (M : Machine Γ Λ) {n : ℕ}
    (source target : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n) :
    Step M.boundaryShuttle source target ↔
      (∃ (move : ShuttleMove Γ Λ)
          (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .plain move.old ∧
        source = ⟨.normal move.source, tape⟩ ∧
        target = ⟨.atNeighbour move,
          (tape.write (.departure move)).moveHead move.direction⟩) ∨
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .plain neighbour ∧
        source = ⟨.atNeighbour move, tape⟩ ∧
        target = ⟨.atDeparture move neighbour,
          (tape.write (.neighbour move neighbour)).moveHead
            (reverseDirection move.direction)⟩) ∨
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .departure move ∧
        source = ⟨.atDeparture move neighbour, tape⟩ ∧
        target = ⟨.restoreNeighbour move neighbour,
          (tape.write (.plain move.written)).moveHead move.direction⟩) ∨
      (∃ (move : ShuttleMove Γ Λ) (neighbour : Γ)
          (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n),
        M.ShuttleDirectionalEnabled move ∧
        tape.read = .neighbour move neighbour ∧
        source = ⟨.restoreNeighbour move neighbour, tape⟩ ∧
        target = ⟨.normal move.target,
          (tape.write (.plain neighbour)).moveHead .stay⟩) := by
  constructor
  · rintro ⟨next, written, direction, henabled, rfl⟩
    rcases source with ⟨state, tape⟩
    cases state with
    | normal state =>
        cases hread : tape.read with
        | plain old =>
            rw [hread] at henabled
            change ∃ move : ShuttleMove Γ Λ,
              M.ShuttleDirectionalEnabled move ∧ move.source = state ∧
                move.old = old ∧
                (next, written, direction) =
                  (.atNeighbour move, .departure move, move.direction) at henabled
            obtain ⟨move, hmove, hsource, hold, hout⟩ := henabled
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            subst state
            subst old
            exact Or.inl ⟨move, tape, hmove, hread, rfl, rfl⟩
        | departure observed =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
        | neighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
    | atNeighbour move =>
        cases hread : tape.read with
        | plain neighbour =>
            rw [hread] at henabled
            change M.ShuttleDirectionalEnabled move ∧
              (next, written, direction) =
                (.atDeparture move neighbour, .neighbour move neighbour,
                  reverseDirection move.direction) at henabled
            obtain ⟨hmove, hout⟩ := henabled
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr (Or.inl ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩)
        | departure observed =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
        | neighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
    | atDeparture move neighbour =>
        cases hread : tape.read with
        | plain symbol =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
        | departure observed =>
            rw [hread] at henabled
            change observed = move ∧ M.ShuttleDirectionalEnabled move ∧
              (next, written, direction) =
                (.restoreNeighbour move neighbour, .plain move.written,
                  move.direction) at henabled
            obtain ⟨hobserved, hmove, hout⟩ := henabled
            subst observed
            simp only [Prod.mk.injEq] at hout
            rcases hout with ⟨rfl, rfl, rfl⟩
            exact Or.inr (Or.inr (Or.inl
              ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩))
        | neighbour observed symbol =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
    | restoreNeighbour move neighbour =>
        cases hread : tape.read with
        | plain symbol =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
        | departure observed =>
            rw [hread] at henabled
            simp [Machine.boundaryShuttle, shuttleTransition] at henabled
        | neighbour observed observedNeighbour =>
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
            exact Or.inr (Or.inr (Or.inr
              ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩))
  · rintro (⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩)
    · refine ⟨.atNeighbour move, .departure move, move.direction, ?_, rfl⟩
      rw [hread]
      exact ⟨move, hmove, rfl, rfl, rfl⟩
    · refine ⟨.atDeparture move neighbour, .neighbour move neighbour,
        reverseDirection move.direction, ?_, rfl⟩
      rw [hread]
      exact ⟨hmove, rfl⟩
    · refine ⟨.restoreNeighbour move neighbour, .plain move.written,
        move.direction, ?_, rfl⟩
      rw [hread]
      exact ⟨rfl, hmove, rfl⟩
    · refine ⟨.normal move.target, .plain neighbour, .stay, ?_, rfl⟩
      rw [hread]
      exact ⟨rfl, rfl, hmove, rfl⟩

/-- Every low-level shuttle edge crosses the syntactic bipartition. -/
public theorem Machine.shuttleParity_ne_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    (hstep : Step M.boundaryShuttle source target) :
    shuttleParity source.state ≠ shuttleParity target.state := by
  rw [M.step_boundaryShuttle_iff source target] at hstep
  rcases hstep with
      ⟨move, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ |
      ⟨move, neighbour, tape, hmove, hread, rfl, rfl⟩ <;>
    simp [shuttleParity]

/-- Boolean equation form of the parity-flip invariant. -/
public theorem Machine.shuttleParity_eq_not_of_step
    (M : Machine Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    (hstep : Step M.boundaryShuttle source target) :
    shuttleParity target.state = !shuttleParity source.state := by
  have hne := M.shuttleParity_ne_of_step hstep
  revert hne
  cases hsource : shuttleParity source.state <;>
    cases htarget : shuttleParity target.state <;> simp

/-- The first protocol edge. -/
public theorem Machine.step_boundaryShuttle_start
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .plain move.old) :
    Step M.boundaryShuttle
      ⟨.normal move.source, tape⟩
      ⟨.atNeighbour move,
        (tape.write (.departure move)).moveHead move.direction⟩ := by
  rw [M.step_boundaryShuttle_iff]
  exact Or.inl ⟨move, tape, henabled, hread, rfl, rfl⟩

/-- The second protocol edge. -/
public theorem Machine.step_boundaryShuttle_tagNeighbour
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (neighbour : Γ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .plain neighbour) :
    Step M.boundaryShuttle
      ⟨.atNeighbour move, tape⟩
      ⟨.atDeparture move neighbour,
        (tape.write (.neighbour move neighbour)).moveHead
          (reverseDirection move.direction)⟩ := by
  rw [M.step_boundaryShuttle_iff]
  exact Or.inr (Or.inl ⟨move, neighbour, tape, henabled, hread, rfl, rfl⟩)

/-- The third protocol edge. -/
public theorem Machine.step_boundaryShuttle_restoreDeparture
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (neighbour : Γ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .departure move) :
    Step M.boundaryShuttle
      ⟨.atDeparture move neighbour, tape⟩
      ⟨.restoreNeighbour move neighbour,
        (tape.write (.plain move.written)).moveHead move.direction⟩ := by
  rw [M.step_boundaryShuttle_iff]
  exact Or.inr (Or.inr (Or.inl
    ⟨move, neighbour, tape, henabled, hread, rfl, rfl⟩))

/-- The fourth protocol edge. -/
public theorem Machine.step_boundaryShuttle_finish
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (neighbour : Γ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = .neighbour move neighbour) :
    Step M.boundaryShuttle
      ⟨.restoreNeighbour move neighbour, tape⟩
      ⟨.normal move.target,
        (tape.write (.plain neighbour)).moveHead .stay⟩ := by
  rw [M.step_boundaryShuttle_iff]
  exact Or.inr (Or.inr (Or.inr
    ⟨move, neighbour, tape, henabled, hread, rfl, rfl⟩))

end LBA
