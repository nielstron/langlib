module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.CombinedRawDegree
import Mathlib.Tactic

@[expose]
public section

/-!
# Every genuine double merge of the combined shuttle is terminal

Only the three moving protocol landings can have two distinct predecessors.  When both inverse
head candidates really occur, one predecessor is boundary-clamped and leaves the freshly written
tag under the landing head.  That tag belongs to a constructor disjoint from the one expected by
the next phase, so the landing is a sink.  Normal and stationary-pending landings have unique
predecessors under the combined normal-form hypotheses.
-/

namespace LBA

variable {Γ Λ : Type*}

private theorem combined_target_read_eq_written_of_write_move_eq_of_head_eq
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

public theorem Machine.no_step_combinedShuttle_directionalAtNeighbour_departure
    (M : Machine Γ Λ) {n : ℕ} (move observed : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (hread : tape.read = .directionalDeparture observed) :
    ∀ target, ¬ Step M.combinedBoundaryShuttle
      ⟨.directionalAtNeighbour move, tape⟩ target := by
  intro target
  rintro ⟨next, written, direction, henabled, rfl⟩
  rw [hread] at henabled
  simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled

public theorem Machine.no_step_combinedShuttle_directionalAtDeparture_neighbour
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (saved : Γ)
    (observed : ShuttleMove Γ Λ) (symbol : Γ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (hread : tape.read = .directionalNeighbour observed symbol) :
    ∀ target, ¬ Step M.combinedBoundaryShuttle
      ⟨.directionalAtDeparture move saved, tape⟩ target := by
  intro target
  rintro ⟨next, written, direction, henabled, rfl⟩
  rw [hread] at henabled
  simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled

public theorem Machine.no_step_combinedShuttle_directionalRestoreNeighbour_plain
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ) (saved symbol : Γ)
    (tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n)
    (hread : tape.read = .plain symbol) :
    ∀ target, ¬ Step M.combinedBoundaryShuttle
      ⟨.directionalRestoreNeighbour move saved, tape⟩ target := by
  intro target
  rintro ⟨next, written, direction, henabled, rfl⟩
  rw [hread] at henabled
  simp [Machine.combinedBoundaryShuttle, combinedShuttleTransition] at henabled

private theorem Machine.read_directionalDeparture_of_step_atNeighbour_of_head_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle predecessor
      ⟨.directionalAtNeighbour move, tape⟩)
    (hhead : predecessor.tape.head = tape.head) :
    tape.read = .directionalDeparture move := by
  rw [M.step_combinedBoundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩
  · simp only [DLBA.Cfg.mk.injEq,
      CombinedShuttleState.directionalAtNeighbour.injEq] at htarget
    rcases htarget with ⟨hmove, htape⟩
    subst sourceMove
    rw [hsource] at hhead
    exact combined_target_read_eq_written_of_write_move_eq_of_head_eq
      sourceTape tape (.directionalDeparture move) move.direction htape.symm hhead
  all_goals simp at htarget

private theorem Machine.read_directionalNeighbour_of_step_atDeparture_of_head_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle predecessor
      ⟨.directionalAtDeparture move neighbour, tape⟩)
    (hhead : predecessor.tape.head = tape.head) :
    tape.read = .directionalNeighbour move neighbour := by
  rw [M.step_combinedBoundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq,
      CombinedShuttleState.directionalAtDeparture.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hneighbour⟩
    subst sourceMove
    subst sourceNeighbour
    rw [hsource] at hhead
    exact combined_target_read_eq_written_of_write_move_eq_of_head_eq
      sourceTape tape (.directionalNeighbour move neighbour)
        (reverseDirection move.direction) htape.symm hhead
  all_goals simp at htarget

private theorem Machine.read_plain_of_step_directionalRestoreNeighbour_of_head_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (CombinedShuttleAlphabet Γ Λ) n}
    (hstep : Step M.combinedBoundaryShuttle predecessor
      ⟨.directionalRestoreNeighbour move neighbour, tape⟩)
    (hhead : predecessor.tape.head = tape.head) :
    tape.read = .plain move.written := by
  rw [M.step_combinedBoundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq,
      CombinedShuttleState.directionalRestoreNeighbour.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hneighbour⟩
    subst sourceMove
    subst sourceNeighbour
    rw [hsource] at hhead
    exact combined_target_read_eq_written_of_write_move_eq_of_head_eq
      sourceTape tape (.plain move.written) move.direction htape.symm hhead
  all_goals simp at htarget

/-- Every raw combined-shuttle vertex with two distinct predecessors is a sink. -/
public theorem Machine.sink_of_two_distinct_predecessors_combinedBoundaryShuttle
    (M : Machine Γ Λ)
    (hdirectional : M.DirectionalTargetInjective)
    (hstationary : M.StationaryTargetWrittenInjective)
    (hkind : M.ShuttleTargetKindDisjoint)
    {n : ℕ}
    {left right target :
      DLBA.Cfg (CombinedShuttleAlphabet Γ Λ) (CombinedShuttleState Γ Λ) n}
    (hne : left ≠ right)
    (hleft : Step M.combinedBoundaryShuttle left target)
    (hright : Step M.combinedBoundaryShuttle right target) :
    ∀ next, ¬ Step M.combinedBoundaryShuttle target next := by
  rcases target with ⟨state, tape⟩
  cases state with
  | normal state =>
      exact False.elim (hne (M.predecessor_combinedShuttle_normal_eq
        hdirectional hstationary hkind hleft hright))
  | stationaryPending move =>
      exact False.elim (hne
        (M.predecessor_combinedShuttle_stationaryPending_eq hleft hright))
  | directionalAtNeighbour move =>
      rcases M.predecessor_combinedShuttle_directionalAtNeighbour_eq_or_eq hleft with
        hleftFirst | hleftSecond
      · rcases M.predecessor_combinedShuttle_directionalAtNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · exact False.elim (hne (hleftFirst.trans hrightFirst.symm))
        · have hhead : left.tape.head = tape.head := by rw [hleftFirst]; rfl
          exact M.no_step_combinedShuttle_directionalAtNeighbour_departure
            move move tape
            (M.read_directionalDeparture_of_step_atNeighbour_of_head_eq hleft hhead)
      · rcases M.predecessor_combinedShuttle_directionalAtNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · have hhead : right.tape.head = tape.head := by rw [hrightFirst]; rfl
          exact M.no_step_combinedShuttle_directionalAtNeighbour_departure
            move move tape
            (M.read_directionalDeparture_of_step_atNeighbour_of_head_eq hright hhead)
        · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))
  | directionalAtDeparture move neighbour =>
      rcases M.predecessor_combinedShuttle_directionalAtDeparture_eq_or_eq hleft with
        hleftFirst | hleftSecond
      · rcases M.predecessor_combinedShuttle_directionalAtDeparture_eq_or_eq hright with
          hrightFirst | hrightSecond
        · exact False.elim (hne (hleftFirst.trans hrightFirst.symm))
        · have hhead : left.tape.head = tape.head := by rw [hleftFirst]; rfl
          exact M.no_step_combinedShuttle_directionalAtDeparture_neighbour
            move neighbour move neighbour tape
            (M.read_directionalNeighbour_of_step_atDeparture_of_head_eq hleft hhead)
      · rcases M.predecessor_combinedShuttle_directionalAtDeparture_eq_or_eq hright with
          hrightFirst | hrightSecond
        · have hhead : right.tape.head = tape.head := by rw [hrightFirst]; rfl
          exact M.no_step_combinedShuttle_directionalAtDeparture_neighbour
            move neighbour move neighbour tape
            (M.read_directionalNeighbour_of_step_atDeparture_of_head_eq hright hhead)
        · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))
  | directionalRestoreNeighbour move neighbour =>
      rcases
          M.predecessor_combinedShuttle_directionalRestoreNeighbour_eq_or_eq hleft with
        hleftFirst | hleftSecond
      · rcases
          M.predecessor_combinedShuttle_directionalRestoreNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · exact False.elim (hne (hleftFirst.trans hrightFirst.symm))
        · have hhead : left.tape.head = tape.head := by rw [hleftFirst]; rfl
          exact M.no_step_combinedShuttle_directionalRestoreNeighbour_plain
            move neighbour move.written tape
            (M.read_plain_of_step_directionalRestoreNeighbour_of_head_eq hleft hhead)
      · rcases
          M.predecessor_combinedShuttle_directionalRestoreNeighbour_eq_or_eq hright with
          hrightFirst | hrightSecond
        · have hhead : right.tape.head = tape.head := by rw [hrightFirst]; rfl
          exact M.no_step_combinedShuttle_directionalRestoreNeighbour_plain
            move neighbour move.written tape
            (M.read_plain_of_step_directionalRestoreNeighbour_of_head_eq hright hhead)
        · exact False.elim (hne (hleftSecond.trans hrightSecond.symm))

end LBA
