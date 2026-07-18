module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.RawDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# Double-predecessor landings are terminal

At each of the three directional protocol landings, the two possible predecessors are the
stationary boundary source and its adjacent source.  If both occur, the boundary source wrote at
the target head.  The target therefore reads the just-written tag.  Its next protocol phase only
accepts a disjoint symbol constructor, so it is a sink.

The final, stationary landing cannot have two predecessors under `DirectionalTargetInjective`.
Thus every raw vertex with two distinct predecessors is terminal.  This is exactly the local
merge condition needed by a two-matching decomposition; no global acyclicity premise is used.
-/

namespace LBA

variable {Γ Λ : Type*}

private theorem target_read_eq_written_of_write_move_eq_of_head_eq
    {A : Type*} {n : ℕ} (source target : DLBA.BoundedTape A n)
    (written : A) (direction : DLBA.Dir)
    (hmove : (source.write written).moveHead direction = target)
    (hhead : source.head = target.head) :
    target.read = written := by
  rw [← hmove]
  change Function.update source.contents source.head written
      ((source.write written).moveHead direction).head = written
  have hmovedHead : ((source.write written).moveHead direction).head = source.head := by
    rw [hmove]
    exact hhead.symm
  rw [hmovedHead, Function.update_self]

/-- A neighbour-phase state reading a departure tag has no successor. -/
public theorem Machine.no_step_boundaryShuttle_atNeighbour_departure
    (M : Machine Γ Λ) {n : ℕ} (move observed : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (hread : tape.read = .departure observed) :
    ∀ target, ¬ Step M.boundaryShuttle ⟨.atNeighbour move, tape⟩ target := by
  intro target
  rintro ⟨next, written, direction, henabled, rfl⟩
  rw [hread] at henabled
  simp [Machine.boundaryShuttle, shuttleTransition] at henabled

/-- A departure-phase state reading a neighbour tag has no successor. -/
public theorem Machine.no_step_boundaryShuttle_atDeparture_neighbour
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (saved : Γ)
    (observed : ShuttleMove Γ Λ) (symbol : Γ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (hread : tape.read = .neighbour observed symbol) :
    ∀ target, ¬ Step M.boundaryShuttle ⟨.atDeparture move saved, tape⟩ target := by
  intro target
  rintro ⟨next, written, direction, henabled, rfl⟩
  rw [hread] at henabled
  simp [Machine.boundaryShuttle, shuttleTransition] at henabled

/-- A restore-neighbour state reading plain data has no successor. -/
public theorem Machine.no_step_boundaryShuttle_restoreNeighbour_plain
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (saved symbol : Γ)
    (tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n)
    (hread : tape.read = .plain symbol) :
    ∀ target, ¬ Step M.boundaryShuttle
      ⟨.restoreNeighbour move saved, tape⟩ target := by
  intro target
  rintro ⟨next, written, direction, henabled, rfl⟩
  rw [hread] at henabled
  simp [Machine.boundaryShuttle, shuttleTransition] at henabled

/-! ## A boundary-headed predecessor exposes the just-written tag -/

private theorem Machine.read_departure_of_step_atNeighbour_of_head_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ}
    {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hstep : Step M.boundaryShuttle predecessor ⟨.atNeighbour move, tape⟩)
    (hhead : predecessor.tape.head = tape.head) :
    tape.read = .departure move := by
  rw [M.step_boundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩
  · simp only [DLBA.Cfg.mk.injEq, ShuttleState.atNeighbour.injEq] at htarget
    rcases htarget with ⟨hmove, htape⟩
    subst sourceMove
    rw [hsource] at hhead
    exact target_read_eq_written_of_write_move_eq_of_head_eq
      sourceTape tape (.departure move) move.direction htape.symm hhead
  all_goals simp at htarget

private theorem Machine.read_neighbour_of_step_atDeparture_of_head_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hstep : Step M.boundaryShuttle predecessor
      ⟨.atDeparture move neighbour, tape⟩)
    (hhead : predecessor.tape.head = tape.head) :
    tape.read = .neighbour move neighbour := by
  rw [M.step_boundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq, ShuttleState.atDeparture.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hneighbour⟩
    subst sourceMove
    subst sourceNeighbour
    rw [hsource] at hhead
    exact target_read_eq_written_of_write_move_eq_of_head_eq
      sourceTape tape (.neighbour move neighbour)
        (reverseDirection move.direction) htape.symm hhead
  all_goals simp at htarget

private theorem Machine.read_plain_of_step_restoreNeighbour_of_head_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hstep : Step M.boundaryShuttle predecessor
      ⟨.restoreNeighbour move neighbour, tape⟩)
    (hhead : predecessor.tape.head = tape.head) :
    tape.read = .plain move.written := by
  rw [M.step_boundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq, ShuttleState.restoreNeighbour.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hneighbour⟩
    subst sourceMove
    subst sourceNeighbour
    rw [hsource] at hhead
    exact target_read_eq_written_of_write_move_eq_of_head_eq
      sourceTape tape (.plain move.written) move.direction htape.symm hhead
  all_goals simp at htarget

/-- Every raw shuttle vertex with two distinct predecessors is a sink. -/
public theorem Machine.sink_of_two_distinct_predecessors_boundaryShuttle
    (M : Machine Γ Λ) (htargetInjective : M.DirectionalTargetInjective)
    {n : ℕ}
    {left right target :
      DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    (hne : left ≠ right)
    (hleft : Step M.boundaryShuttle left target)
    (hright : Step M.boundaryShuttle right target) :
    ∀ next, ¬ Step M.boundaryShuttle target next := by
  rcases target with ⟨state, tape⟩
  cases state with
  | normal state =>
      exact False.elim (hne
        (M.predecessor_boundaryShuttle_normal_eq htargetInjective hleft hright))
  | atNeighbour move =>
      rcases M.predecessor_boundaryShuttle_atNeighbour_eq_or_eq hleft with
        hleftFirst | hleftSecond
      · rcases M.predecessor_boundaryShuttle_atNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · exact False.elim (hne (hleftFirst.trans hrightFirst.symm))
        · have hhead : left.tape.head = tape.head := by rw [hleftFirst]; rfl
          exact M.no_step_boundaryShuttle_atNeighbour_departure move move tape
            (M.read_departure_of_step_atNeighbour_of_head_eq hleft hhead)
      · rcases M.predecessor_boundaryShuttle_atNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · have hhead : right.tape.head = tape.head := by rw [hrightFirst]; rfl
          exact M.no_step_boundaryShuttle_atNeighbour_departure move move tape
            (M.read_departure_of_step_atNeighbour_of_head_eq hright hhead)
        · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))
  | atDeparture move neighbour =>
      rcases M.predecessor_boundaryShuttle_atDeparture_eq_or_eq hleft with
        hleftFirst | hleftSecond
      · rcases M.predecessor_boundaryShuttle_atDeparture_eq_or_eq hright with
          hrightFirst | hrightSecond
        · exact False.elim (hne (hleftFirst.trans hrightFirst.symm))
        · have hhead : left.tape.head = tape.head := by rw [hleftFirst]; rfl
          exact M.no_step_boundaryShuttle_atDeparture_neighbour
            move neighbour move neighbour tape
            (M.read_neighbour_of_step_atDeparture_of_head_eq hleft hhead)
      · rcases M.predecessor_boundaryShuttle_atDeparture_eq_or_eq hright with
          hrightFirst | hrightSecond
        · have hhead : right.tape.head = tape.head := by rw [hrightFirst]; rfl
          exact M.no_step_boundaryShuttle_atDeparture_neighbour
            move neighbour move neighbour tape
            (M.read_neighbour_of_step_atDeparture_of_head_eq hright hhead)
        · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))
  | restoreNeighbour move neighbour =>
      rcases M.predecessor_boundaryShuttle_restoreNeighbour_eq_or_eq hleft with
        hleftFirst | hleftSecond
      · rcases M.predecessor_boundaryShuttle_restoreNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · exact False.elim (hne (hleftFirst.trans hrightFirst.symm))
        · have hhead : left.tape.head = tape.head := by rw [hleftFirst]; rfl
          exact M.no_step_boundaryShuttle_restoreNeighbour_plain
            move neighbour move.written tape
            (M.read_plain_of_step_restoreNeighbour_of_head_eq hleft hhead)
      · rcases M.predecessor_boundaryShuttle_restoreNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · have hhead : right.tape.head = tape.head := by rw [hrightFirst]; rfl
          exact M.no_step_boundaryShuttle_restoreNeighbour_plain
            move neighbour move.written tape
            (M.read_plain_of_step_restoreNeighbour_of_head_eq hright hhead)
        · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))

end LBA
