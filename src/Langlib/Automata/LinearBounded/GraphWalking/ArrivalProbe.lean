module

public import Langlib.Automata.LinearBounded.GraphWalking.BoundedTapeMemory
import Mathlib.Tactic

@[expose]
public section

/-!
# Decomposing an arrival operation into raw head moves

The inverse of a directional bounded-tape operation is deliberately
out-of-sync: starting at the arrival cell, it first moves to the candidate
departure cell and only then checks the symbol which the forward operation
would have written there.

This file isolates the tape algebra of that probe.  Away from a boundary, a
valid probe restores the old symbol and finishes at the predecessor, while an
invalid probe can return to the original target without changing the tape.
At a boundary the first raw clamped move is the identity.  The latter fact is
the reason a raw compiler must dispatch an observably blocked direction
before moving; it cannot discover the boundary by executing the clamped move.
-/

namespace GraphWalking
namespace BoundedTapeMemory

universe u

variable {A : Type u} {n : ℕ}

/-- The physical first step of an arrival probe.  It uses the reverse of the
original departure direction and therefore agrees with the partial
`previousHead` operation exactly when that operation is defined. -/
@[expose]
public def rawArrivalCandidate (travel : Travel)
    (target : DLBA.BoundedTape A n) : DLBA.BoundedTape A n :=
  target.moveHead travel.reverse.toDir

/-- A successful partial predecessor-head calculation identifies the raw
candidate tape exactly. -/
public theorem rawArrivalCandidate_eq_atHead
    (travel : Travel) (target : DLBA.BoundedTape A n)
    {departureHead : Fin (n + 1)}
    (hprevious : previousHead travel target.head = some departureHead) :
    rawArrivalCandidate travel target = atHead target departureHead := by
  apply eq_of_contents_head
  · rfl
  · exact moveHead_eq_of_nextHead target travel.reverse hprevious

/-- After a genuine reverse move, the corresponding forward raw move returns
to the original target tape without changing any cell. -/
public theorem rawArrivalCandidate_moveHead_forward
    (travel : Travel) (target : DLBA.BoundedTape A n)
    {departureHead : Fin (n + 1)}
    (hprevious : previousHead travel target.head = some departureHead) :
    (rawArrivalCandidate travel target).moveHead travel.toDir = target := by
  have hcandidate := rawArrivalCandidate_eq_atHead travel target hprevious
  rw [hcandidate]
  apply eq_of_contents_head
  · rfl
  · exact moveHead_eq_of_nextHead (atHead target departureHead) travel
      ((nextHead_reverse_iff travel departureHead target.head).mpr hprevious)

/-- If the candidate cell contains the expected written symbol, the two raw
actions "move backwards; restore old" give exactly the successful atomic
arrival operation. -/
public theorem move_arrival_eq_raw_probe_success
    [DecidableEq A]
    (old written : A) (travel : Travel)
    (target : DLBA.BoundedTape A n) {departureHead : Fin (n + 1)}
    (hprevious : previousHead travel target.head = some departureHead)
    (hwritten : target.contents departureHead = written) :
    move (.arrival old written travel) target =
      some ((rawArrivalCandidate travel target).write old) := by
  rw [move_arrival_eq_some_iff]
  refine ⟨departureHead, hprevious, hwritten, ?_⟩
  rw [rawArrivalCandidate_eq_atHead travel target hprevious]
  apply eq_of_contents_head
  · classical
    simp [atHead, DLBA.BoundedTape.write]
  · rfl

/-- If the candidate symbol fails the finite transition test, the atomic
arrival operation is undefined. -/
public theorem move_arrival_eq_none_of_candidate_ne
    [DecidableEq A]
    (old written : A) (travel : Travel)
    (target : DLBA.BoundedTape A n) {departureHead : Fin (n + 1)}
    (hprevious : previousHead travel target.head = some departureHead)
    (hne : target.contents departureHead ≠ written) :
    move (.arrival old written travel) target = none := by
  simp [move, hprevious, hne]

/-- The failed-probe round trip is exact: move to the candidate, perform no
write, and move forward again. -/
public theorem rawArrivalProbe_invalid_returns
    (written : A) (travel : Travel)
    (target : DLBA.BoundedTape A n) {departureHead : Fin (n + 1)}
    (hprevious : previousHead travel target.head = some departureHead)
    (_hne : target.contents departureHead ≠ written) :
    (rawArrivalCandidate travel target).moveHead travel.toDir = target :=
  rawArrivalCandidate_moveHead_forward travel target hprevious

/-- At a physical boundary, the partial arrival operation is undefined. -/
public theorem move_arrival_eq_none_of_previousHead_eq_none
    [DecidableEq A]
    (old written : A) (travel : Travel)
    (target : DLBA.BoundedTape A n)
    (hprevious : previousHead travel target.head = none) :
    move (.arrival old written travel) target = none := by
  simp [move, hprevious]

/-- The dangerous clamping equation: when the partial predecessor head does
not exist, executing the corresponding *raw* reverse move leaves the entire
tape unchanged.  Hence a raw transition cannot distinguish this case after
the move has happened. -/
public theorem rawArrivalCandidate_eq_self_of_previousHead_eq_none
    (travel : Travel) (target : DLBA.BoundedTape A n)
    (hprevious : previousHead travel target.head = none) :
    rawArrivalCandidate travel target = target := by
  apply eq_of_contents_head
  · rfl
  · cases travel with
    | left =>
        have hlast : target.head.val = n := by
          simpa [previousHead] using
            (nextHead_right_eq_none_iff target.head).mp hprevious
        simp [rawArrivalCandidate, Travel.reverse, Travel.toDir,
          DLBA.BoundedTape.moveHead, hlast]
    | right =>
        have hzero : target.head.val = 0 := by
          simpa [previousHead] using
            (nextHead_left_eq_none_iff target.head).mp hprevious
        simp [rawArrivalCandidate, Travel.reverse, Travel.toDir,
          DLBA.BoundedTape.moveHead, hzero]

end BoundedTapeMemory
end GraphWalking

end
