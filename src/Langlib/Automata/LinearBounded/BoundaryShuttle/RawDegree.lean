module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.Canonical
import Mathlib.Tactic

@[expose]
public section

/-!
# Complete raw-graph degree bounds for the boundary shuttle

The three tagged landing phases inherit exactly the two possible inverse head positions of a
clamped move.  The final stationary tag-erasing edge has a unique predecessor under
`DirectionalTargetInjective`.  These statements range over all tape widths and all raw tapes.
-/

namespace LBA

open Classical

variable {Γ Λ : Type*}

private theorem write_write_read {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (written : A) :
    (tape.write written).write tape.read = tape := by
  cases tape
  simp [DLBA.BoundedTape.write, Function.update_eq_self]

private theorem moveHead_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) : tape.moveHead .stay = tape := by
  cases tape
  rfl

/-- A clamped movement has only the stationary and opposite-neighbour inverse candidates. -/
public theorem moveHead_eq_implies_eq_or_reverseDirection
    {A : Type*} {n : ℕ} (source target : DLBA.BoundedTape A n)
    (direction : DLBA.Dir) (hmove : source.moveHead direction = target) :
    source = target ∨ source = target.moveHead (reverseDirection direction) := by
  subst target
  cases direction with
  | stay => exact Or.inl rfl
  | left =>
      by_cases hpos : 0 < source.head.val
      · right
        cases source with
        | mk contents head =>
            have hpos' : 0 < head.val := by simpa using hpos
            have hlt : head.val - 1 < n := by
              have := head.isLt
              omega
            simp only [DLBA.BoundedTape.moveHead, hpos, reverseDirection,
              hlt, dite_true]
            congr 1
            apply Fin.ext
            simp
            exact (Nat.sub_add_cancel hpos').symm
      · left
        simp [DLBA.BoundedTape.moveHead, hpos]
  | right =>
      by_cases hlt : source.head.val < n
      · right
        cases source with
        | mk contents head =>
            have hpos : 0 < head.val + 1 := by omega
            simp [DLBA.BoundedTape.moveHead, hlt, reverseDirection, hpos]
      · left
        simp [DLBA.BoundedTape.moveHead, hlt]

/-- Restoring the scanned symbol to either inverse post-write candidate lists every predecessor
tape of a write-and-move operation. -/
public theorem tape_eq_write_target_or_reverse_of_write_move_eq
    {A : Type*} {n : ℕ} (source target : DLBA.BoundedTape A n)
    (old written : A) (direction : DLBA.Dir)
    (hread : source.read = old)
    (hmove : (source.write written).moveHead direction = target) :
    source = target.write old ∨
      source = (target.moveHead (reverseDirection direction)).write old := by
  have hrestore : (source.write written).write old = source := by
    rw [← hread]
    exact write_write_read source written
  rcases moveHead_eq_implies_eq_or_reverseDirection
      (source.write written) target direction hmove with hsame | hopposite
  · left
    rw [← hsame]
    exact hrestore.symm
  · right
    rw [← hopposite]
    exact hrestore.symm

/-! ## Phase-specific predecessor inversion -/

/-- An `atNeighbour` landing has at most the two inverse clamped departures. -/
public theorem Machine.predecessor_boundaryShuttle_atNeighbour_eq_or_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ}
    {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hstep : Step M.boundaryShuttle predecessor ⟨.atNeighbour move, tape⟩) :
    predecessor =
        ⟨.normal move.source, tape.write (.plain move.old)⟩ ∨
      predecessor =
        ⟨.normal move.source,
          (tape.moveHead (reverseDirection move.direction)).write
            (.plain move.old)⟩ := by
  rw [M.step_boundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, neighbour, sourceTape, henabled, hread, hsource, htarget⟩
  · simp only [DLBA.Cfg.mk.injEq, ShuttleState.atNeighbour.injEq] at htarget
    rcases htarget with ⟨hmove, htape⟩
    subst sourceMove
    have hcandidates := tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (.plain move.old) (.departure move) move.direction
      hread htape.symm
    rcases hcandidates with htapeSource | htapeSource
    · left
      rw [hsource, htapeSource]
    · right
      rw [hsource, htapeSource]
  all_goals simp at htarget

/-- An `atDeparture` landing has at most the two inverse return-move predecessors. -/
public theorem Machine.predecessor_boundaryShuttle_atDeparture_eq_or_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hstep : Step M.boundaryShuttle predecessor
      ⟨.atDeparture move neighbour, tape⟩) :
    predecessor =
        ⟨.atNeighbour move, tape.write (.plain neighbour)⟩ ∨
      predecessor =
        ⟨.atNeighbour move,
          (tape.moveHead move.direction).write (.plain neighbour)⟩ := by
  rw [M.step_boundaryShuttle_iff] at hstep
  rcases hstep with
      ⟨sourceMove, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩ |
      ⟨sourceMove, sourceNeighbour, sourceTape, henabled, hread, hsource, htarget⟩
  · simp at htarget
  · simp only [DLBA.Cfg.mk.injEq, ShuttleState.atDeparture.injEq] at htarget
    rcases htarget with ⟨hstate, htape⟩
    rcases hstate with ⟨hmove, hsourceNeighbour⟩
    subst sourceMove
    subst sourceNeighbour
    have hcandidates := tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (.plain neighbour) (.neighbour move neighbour)
        (reverseDirection move.direction) hread htape.symm
    rw [reverseDirection_reverseDirection] at hcandidates
    rcases hcandidates with htapeSource | htapeSource
    · left
      rw [hsource, htapeSource]
    · right
      rw [hsource, htapeSource]
  all_goals simp at htarget

/-- A `restoreNeighbour` landing has at most the two inverse second departures. -/
public theorem Machine.predecessor_boundaryShuttle_restoreNeighbour_eq_or_eq
    (M : Machine Γ Λ) {n : ℕ}
    {predecessor : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {move : ShuttleMove Γ Λ} {neighbour : Γ}
    {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hstep : Step M.boundaryShuttle predecessor
      ⟨.restoreNeighbour move neighbour, tape⟩) :
    predecessor =
        ⟨.atDeparture move neighbour, tape.write (.departure move)⟩ ∨
      predecessor =
        ⟨.atDeparture move neighbour,
          (tape.moveHead (reverseDirection move.direction)).write
            (.departure move)⟩ := by
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
    rcases hstate with ⟨hmove, hsourceNeighbour⟩
    subst sourceMove
    subst sourceNeighbour
    have hcandidates := tape_eq_write_target_or_reverse_of_write_move_eq
      sourceTape tape (.departure move) (.plain move.written) move.direction
      hread htape.symm
    rcases hcandidates with htapeSource | htapeSource
    · left
      rw [hsource, htapeSource]
    · right
      rw [hsource, htapeSource]
  all_goals simp at htarget

/-- Under target-state instruction uniqueness, a normal landing has at most one predecessor. -/
public theorem Machine.predecessor_boundaryShuttle_normal_eq
    (M : Machine Γ Λ) (htargetInjective : M.DirectionalTargetInjective)
    {n : ℕ}
    {left right : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n}
    {target : Λ} {tape : DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n}
    (hleft : Step M.boundaryShuttle left ⟨.normal target, tape⟩)
    (hright : Step M.boundaryShuttle right ⟨.normal target, tape⟩) :
    left = right := by
  rw [M.step_boundaryShuttle_iff] at hleft hright
  rcases hleft with
      ⟨leftMove, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩ |
      ⟨leftMove, leftNeighbour, leftTape, hleftEnabled, hleftRead, hleftSource, hleftTarget⟩
  all_goals try simp at hleftTarget
  rcases hright with
      ⟨rightMove, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩ |
      ⟨rightMove, rightNeighbour, rightTape, hrightEnabled, hrightRead, hrightSource, hrightTarget⟩
  all_goals try simp at hrightTarget
  rcases hleftTarget with ⟨hleftTargetState, hleftTargetTape⟩
  rcases hrightTarget with ⟨hrightTargetState, hrightTargetTape⟩
  rw [moveHead_stay] at hleftTargetTape hrightTargetTape
  have hmove : leftMove = rightMove := htargetInjective leftMove rightMove
    hleftEnabled hrightEnabled
    (hleftTargetState.symm.trans hrightTargetState)
  subst rightMove
  have hneighbour : leftNeighbour = rightNeighbour := by
    have hreadLeft : tape.read = .plain leftNeighbour := by
      rw [hleftTargetTape]
      simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
    have hreadRight : tape.read = .plain rightNeighbour := by
      rw [hrightTargetTape]
      simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]
    rw [hreadLeft] at hreadRight
    exact ShuttleAlphabet.plain.inj hreadRight
  subst rightNeighbour
  have hleftTape :
      leftTape = tape.write (.neighbour leftMove leftNeighbour) := by
    rw [hleftTargetTape]
    rw [← hleftRead]
    exact (write_write_read leftTape (.plain leftNeighbour)).symm
  have hrightTape :
      rightTape = tape.write (.neighbour leftMove leftNeighbour) := by
    rw [hrightTargetTape]
    rw [← hrightRead]
    exact (write_write_read rightTape (.plain leftNeighbour)).symm
  rw [hleftSource, hrightSource, hleftTape, hrightTape]

/-! ## Cardinal degree bounds -/

/-- All raw shuttle configurations have at most two predecessors. -/
public theorem Machine.boundaryShuttle_configurationIndegreeAtMostTwo
    (M : Machine Γ Λ) (htargetInjective : M.DirectionalTargetInjective) :
    M.boundaryShuttle.ConfigurationIndegreeAtMostTwo := by
  intro n target
  rcases target with ⟨state, tape⟩
  cases state with
  | normal target =>
      apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
      intro left right hleft hright
      exact M.predecessor_boundaryShuttle_normal_eq htargetInjective hleft hright
  | atNeighbour move =>
      let first : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
        ⟨.normal move.source, tape.write (.plain move.old)⟩
      let second : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
        ⟨.normal move.source,
          (tape.moveHead (reverseDirection move.direction)).write (.plain move.old)⟩
      calc
        Set.encard {cfg | Step M.boundaryShuttle cfg ⟨.atNeighbour move, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_boundaryShuttle_atNeighbour_eq_or_eq hcfg
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl
  | atDeparture move neighbour =>
      let first : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
        ⟨.atNeighbour move, tape.write (.plain neighbour)⟩
      let second : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
        ⟨.atNeighbour move, (tape.moveHead move.direction).write (.plain neighbour)⟩
      calc
        Set.encard {cfg | Step M.boundaryShuttle cfg
            ⟨.atDeparture move neighbour, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_boundaryShuttle_atDeparture_eq_or_eq hcfg
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl
  | restoreNeighbour move neighbour =>
      let first : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
        ⟨.atDeparture move neighbour, tape.write (.departure move)⟩
      let second : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
        ⟨.atDeparture move neighbour,
          (tape.moveHead (reverseDirection move.direction)).write (.departure move)⟩
      calc
        Set.encard {cfg | Step M.boundaryShuttle cfg
            ⟨.restoreNeighbour move neighbour, tape⟩} ≤
            Set.encard ({first, second} : Set _) := by
          apply Set.encard_le_encard
          intro cfg hcfg
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          exact M.predecessor_boundaryShuttle_restoreNeighbour_eq_or_eq hcfg
        _ ≤ 2 := by
          calc
            Set.encard ({first, second} : Set _) ≤
                Set.encard ({second} : Set _) + 1 := Set.encard_insert_le _ _
            _ = 2 := by rw [Set.encard_singleton]; rfl

/-- Functionality gives the sharper raw outdegree bound one, hence certainly two. -/
public theorem Machine.boundaryShuttle_configurationOutdegreeAtMostTwo
    (M : Machine Γ Λ) (hfunctional : M.DirectionalFunctional) :
    M.boundaryShuttle.ConfigurationOutdegreeAtMostTwo := by
  have hlocal := M.boundaryShuttle_functional hfunctional
  intro n source
  apply le_trans (Set.encard_le_one_iff.mpr ?_) (by norm_num)
  intro left right hleft hright
  rcases hleft with ⟨leftTarget, leftWritten, leftDirection, leftEnabled, rfl⟩
  rcases hright with ⟨rightTarget, rightWritten, rightDirection, rightEnabled, rfl⟩
  have hmove := hlocal source.state source.tape.read leftEnabled rightEnabled
  simp only [Prod.mk.injEq] at hmove
  rcases hmove with ⟨rfl, rfl, rfl⟩
  rfl

/-- Combined complete raw directed-degree bound. -/
public theorem Machine.boundaryShuttle_configurationDegreeAtMostTwo
    (M : Machine Γ Λ) (hfunctional : M.DirectionalFunctional)
    (htargetInjective : M.DirectionalTargetInjective) :
    M.boundaryShuttle.ConfigurationDegreeAtMostTwo :=
  ⟨M.boundaryShuttle_configurationOutdegreeAtMostTwo hfunctional,
    M.boundaryShuttle_configurationIndegreeAtMostTwo htargetInjective⟩

end LBA
