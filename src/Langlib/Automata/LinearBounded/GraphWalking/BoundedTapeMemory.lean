module

public import Langlib.Automata.LinearBounded.GraphWalking.Definition
public import Langlib.Automata.DeterministicLinearBounded.Definition
import Mathlib.Tactic

@[expose]
public section

/-!
# A locally reversible bounded-tape memory graph

`DLBA.BoundedTape.moveHead` deliberately clamps at the two ends of the tape.
Clamping is not invertible: at an end cell, staying put and trying to cross the
boundary have the same physical result.  This module therefore gives the same
bounded tape a different family of *partial* named operations.  A left or
right operation is undefined at the relevant boundary.

There are three kinds of names.

* `stationary old new` rewrites the cell under the head; its opposite swaps
  `old` and `new`.
* `departure old written travel` checks `old`, writes `written`, and moves one
  genuine cell in `travel`.
* `arrival old written travel` is the named reverse of that departure.  From
  the neighbouring cell it first finds the previous head position, checks the
  saved `written` symbol there, restores `old`, and moves the head back there.

Thus the reverse operation is executable using one bounded-radius memory
operation.  No operation in the memory graph uses physical boundary
clamping.  This is the concrete memory interface needed by the local-port
graph-walking construction; compiling one such partial operation into raw
clamped LBA steps remains a separate microcompilation problem.
-/

namespace GraphWalking

universe u

namespace BoundedTapeMemory

/-- The two genuinely moving directions. -/
public inductive Travel where
  | left
  | right
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Reverse a genuine one-cell travel. -/
@[expose]
public def Travel.reverse : Travel → Travel
  | .left => .right
  | .right => .left

@[simp]
public theorem Travel.reverse_reverse (travel : Travel) :
    travel.reverse.reverse = travel := by
  cases travel <;> rfl

/-- View a genuine travel as an ordinary bounded-tape direction. -/
@[expose]
public def Travel.toDir : Travel → DLBA.Dir
  | .left => .left
  | .right => .right

@[simp]
public theorem Travel.reverse_toDir (travel : Travel) :
    travel.reverse.toDir =
      match travel.toDir with
      | .left => .right
      | .right => .left
      | .stay => .stay := by
  cases travel <;> rfl

/-- The partial, nonclamping successor of a head position. -/
@[expose]
public def nextHead {n : ℕ} (travel : Travel) (head : Fin (n + 1)) :
    Option (Fin (n + 1)) :=
  match travel with
  | .left =>
      if h : 0 < head.val then
        some ⟨head.val - 1, by omega⟩
      else
        none
  | .right =>
      if h : head.val < n then
        some ⟨head.val + 1, by omega⟩
      else
        none

/-- The partial predecessor is just a successor in the reverse direction. -/
@[expose]
public def previousHead {n : ℕ} (travel : Travel) (head : Fin (n + 1)) :
    Option (Fin (n + 1)) :=
  nextHead travel.reverse head

@[simp]
public theorem nextHead_left_eq_none_iff {n : ℕ} (head : Fin (n + 1)) :
    nextHead .left head = none ↔ head.val = 0 := by
  simp [nextHead]

@[simp]
public theorem nextHead_right_eq_none_iff {n : ℕ} (head : Fin (n + 1)) :
    nextHead .right head = none ↔ head.val = n := by
  simp [nextHead]
  omega

/-- A nonclamping head step is exactly undone by the reverse head step. -/
public theorem nextHead_reverse_iff {n : ℕ} (travel : Travel)
    (source target : Fin (n + 1)) :
    nextHead travel source = some target ↔
      nextHead travel.reverse target = some source := by
  cases travel with
  | left =>
      constructor
      · intro h
        by_cases hsource : 0 < source.val
        · simp only [nextHead, hsource, dite_true] at h
          have htarget : target = ⟨source.val - 1, by omega⟩ :=
            (Option.some.inj h).symm
          subst target
          have hinside : source.val - 1 < n := by
            have := source.isLt
            omega
          simp only [Travel.reverse, nextHead, hinside, dite_true]
          apply congrArg some
          apply Fin.ext
          simp
          omega
        · simp [nextHead, hsource] at h
      · intro h
        by_cases htarget : target.val < n
        · simp only [Travel.reverse, nextHead, htarget, dite_true] at h
          have hsource : source = ⟨target.val + 1, by omega⟩ :=
            (Option.some.inj h).symm
          subst source
          have hinside : 0 < target.val + 1 := by omega
          simp only [nextHead, hinside, dite_true]
          apply congrArg some
          apply Fin.ext
          simp
        · simp [Travel.reverse, nextHead, htarget] at h
  | right =>
      constructor
      · intro h
        by_cases hsource : source.val < n
        · simp only [nextHead, hsource, dite_true] at h
          have htarget : target = ⟨source.val + 1, by omega⟩ :=
            (Option.some.inj h).symm
          subst target
          have hinside : 0 < source.val + 1 := by omega
          simp only [Travel.reverse, nextHead, hinside, dite_true]
          apply congrArg some
          apply Fin.ext
          simp
        · simp [nextHead, hsource] at h
      · intro h
        by_cases htarget : 0 < target.val
        · simp only [Travel.reverse, nextHead, htarget, dite_true] at h
          have hsource : source = ⟨target.val - 1, by omega⟩ :=
            (Option.some.inj h).symm
          subst source
          have hinside : target.val - 1 < n := by
            have := target.isLt
            omega
          simp only [nextHead, hinside, dite_true]
          apply congrArg some
          apply Fin.ext
          simp
          omega
        · simp [Travel.reverse, nextHead, htarget] at h

/-- A successful partial head step agrees with the ordinary clamped operation;
the success hypothesis is exactly what rules out clamping. -/
public theorem moveHead_eq_of_nextHead {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (travel : Travel)
    {target : Fin (n + 1)}
    (hnext : nextHead travel tape.head = some target) :
    (tape.moveHead travel.toDir).head = target := by
  rcases tape with ⟨contents, head⟩
  cases travel with
  | left =>
      simp only [nextHead] at hnext
      split at hnext
      next hinside =>
        simp only [DLBA.BoundedTape.moveHead, Travel.toDir, hinside, dite_true]
        exact Option.some.inj hnext
      next houtside => simp at hnext
  | right =>
      simp only [nextHead] at hnext
      split at hnext
      next hinside =>
        simp only [DLBA.BoundedTape.moveHead, Travel.toDir, hinside, dite_true]
        exact Option.some.inj hnext
      next houtside => simp at hnext

/-- Give a bounded tape a specified head without changing its contents. -/
@[expose]
public def atHead {A : Type*} {n : ℕ} (tape : DLBA.BoundedTape A n)
    (head : Fin (n + 1)) : DLBA.BoundedTape A n :=
  { tape with head := head }

@[simp]
public theorem atHead_contents {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (head : Fin (n + 1)) :
    (atHead tape head).contents = tape.contents := rfl

@[simp]
public theorem atHead_head {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (head : Fin (n + 1)) :
    (atHead tape head).head = head := rfl

/-- Move to a genuine neighbouring cell, returning `none` at a boundary. -/
@[expose]
public def movePartial {A : Type*} {n : ℕ} (travel : Travel)
    (tape : DLBA.BoundedTape A n) : Option (DLBA.BoundedTape A n) :=
  (nextHead travel tape.head).map (atHead tape)

public theorem movePartial_eq_some_iff {A : Type*} {n : ℕ}
    (travel : Travel) (source target : DLBA.BoundedTape A n) :
    movePartial travel source = some target ↔
      ∃ head, nextHead travel source.head = some head ∧
        target = atHead source head := by
  simp [movePartial, Option.map_eq_some_iff]
  aesop

/-- Named reversible operations on a bounded tape. -/
public inductive Direction (A : Type u) where
  | stationary (old new : A)
  | departure (old written : A) (travel : Travel)
  | arrival (old written : A) (travel : Travel)
  deriving DecidableEq, Repr

/-- A sum-of-products code used only to inherit finite enumeration. -/
public abbrev DirectionCode (A : Type u) :=
  (A × A) ⊕ (A × A × Travel) ⊕ (A × A × Travel)

public def directionEquiv {A : Type u} : Direction A ≃ DirectionCode A where
  toFun
    | .stationary old new => .inl (old, new)
    | .departure old written travel => .inr (.inl (old, written, travel))
    | .arrival old written travel => .inr (.inr (old, written, travel))
  invFun
    | .inl (old, new) => .stationary old new
    | .inr (.inl (old, written, travel)) => .departure old written travel
    | .inr (.inr (old, written, travel)) => .arrival old written travel
  left_inv := by intro direction; cases direction <;> rfl
  right_inv := by
    intro code
    rcases code with pair | code
    · rcases pair with ⟨old, new⟩
      rfl
    · rcases code with triple | triple <;>
        rcases triple with ⟨old, written, travel⟩ <;> rfl

/-- There are finitely many operation names when the tape alphabet is finite. -/
public noncomputable instance Direction.instFintype {A : Type u} [Fintype A] :
    Fintype (Direction A) :=
  Fintype.ofEquiv (DirectionCode A) directionEquiv.symm

/-- The explicitly named inverse operation. -/
@[expose]
public def Direction.opposite {A : Type u} : Direction A → Direction A
  | .stationary old new => .stationary new old
  | .departure old written travel => .arrival old written travel
  | .arrival old written travel => .departure old written travel

@[simp]
public theorem Direction.opposite_opposite {A : Type u} (direction : Direction A) :
    direction.opposite.opposite = direction := by
  cases direction <;> rfl

/-- Execute a named memory operation.  Equality tests are only on the locally
read cell (or the one adjacent cell used by an arrival operation). -/
@[expose]
public def move {A : Type u} [DecidableEq A] {n : ℕ}
    (direction : Direction A) (tape : DLBA.BoundedTape A n) :
    Option (DLBA.BoundedTape A n) :=
  match direction with
  | .stationary old new =>
      if tape.read = old then some (tape.write new) else none
  | .departure old written travel =>
      if tape.read = old then movePartial travel (tape.write written) else none
  | .arrival old written travel =>
      match previousHead travel tape.head with
      | none => none
      | some departureHead =>
          if tape.contents departureHead = written then
            some (atHead { tape with
              contents := Function.update tape.contents departureHead old }
              departureHead)
          else
            none

public theorem eq_of_contents_head {A : Type*} {n : ℕ}
    {left right : DLBA.BoundedTape A n}
    (hcontents : left.contents = right.contents)
    (hhead : left.head = right.head) : left = right := by
  cases left
  cases right
  simp_all

@[simp]
public theorem read_write {A : Type*} [DecidableEq A] {n : ℕ}
    (tape : DLBA.BoundedTape A n) (symbol : A) :
    (tape.write symbol).read = symbol := by
  simp [DLBA.BoundedTape.read, DLBA.BoundedTape.write]

/-- Exact local specification of a stationary rewrite. -/
public theorem move_stationary_eq_some_iff {A : Type u} [DecidableEq A] {n : ℕ}
    (old new : A) (source target : DLBA.BoundedTape A n) :
    move (.stationary old new) source = some target ↔
      source.read = old ∧ target = source.write new := by
  simp [move, eq_comm]

/-- Exact local specification of a departure operation. -/
public theorem move_departure_eq_some_iff {A : Type u} [DecidableEq A] {n : ℕ}
    (old written : A) (travel : Travel)
    (source target : DLBA.BoundedTape A n) :
    move (.departure old written travel) source = some target ↔
      source.read = old ∧
        ∃ targetHead, nextHead travel source.head = some targetHead ∧
          target = atHead (source.write written) targetHead := by
  by_cases hread : source.contents source.head = old
  · constructor
    · intro hmove
      refine ⟨(by exact hread), ?_⟩
      have := (movePartial_eq_some_iff travel (source.write written) target).mp
        (by simpa [move, hread] using hmove)
      simpa [eq_comm, DLBA.BoundedTape.write] using this
    · rintro ⟨_, targetHead, hnext, rfl⟩
      have hpartial : movePartial travel (source.write written) =
          some (atHead (source.write written) targetHead) :=
        (movePartial_eq_some_iff travel _ _).mpr ⟨targetHead, hnext, rfl⟩
      simpa [move, hread] using hpartial
  · constructor
    · intro hmove
      simp [move, hread] at hmove
    · rintro ⟨hread', _⟩
      exact (hread (by exact hread')).elim

/-- Exact local specification of the reverse arrival operation. -/
public theorem move_arrival_eq_some_iff {A : Type u} [DecidableEq A] {n : ℕ}
    (old written : A) (travel : Travel)
    (source target : DLBA.BoundedTape A n) :
    move (.arrival old written travel) source = some target ↔
      ∃ departureHead,
        previousHead travel source.head = some departureHead ∧
        source.contents departureHead = written ∧
        target = atHead { source with
          contents := Function.update source.contents departureHead old }
          departureHead := by
  cases hprevious : previousHead travel source.head with
  | none =>
      constructor
      · intro hmove
        simp [move, hprevious] at hmove
      · rintro ⟨departureHead, h, _⟩
        simp at h
  | some departureHead =>
      by_cases hwritten : source.contents departureHead = written
      · constructor
        · intro hmove
          refine ⟨departureHead, rfl, hwritten, ?_⟩
          simpa [move, hprevious, hwritten] using hmove.symm
        · rintro ⟨candidate, hcandidate, _, rfl⟩
          have : candidate = departureHead := (Option.some.inj hcandidate).symm
          subst candidate
          simp [move, hprevious, hwritten]
      · constructor
        · intro hmove
          simp [move, hprevious, hwritten] at hmove
        · rintro ⟨candidate, hcandidate, hsymbol, _⟩
          have : candidate = departureHead := (Option.some.inj hcandidate).symm
          subst candidate
          exact (hwritten hsymbol).elim

/-- Stationary rewrites are exactly reversible by swapping their two symbol
parameters. -/
public theorem move_stationary_reverse {A : Type u} [DecidableEq A] {n : ℕ}
    (old new : A) (source target : DLBA.BoundedTape A n) :
    move (.stationary old new) source = some target ↔
      move (.stationary new old) target = some source := by
  rw [move_stationary_eq_some_iff, move_stationary_eq_some_iff]
  constructor
  · rintro ⟨hread, rfl⟩
    constructor
    · exact read_write source new
    · apply eq_of_contents_head
      · classical
        simp [DLBA.BoundedTape.write]
        simpa [DLBA.BoundedTape.read] using hread
      · rfl
  · rintro ⟨hread, rfl⟩
    constructor
    · exact read_write target old
    · apply eq_of_contents_head
      · classical
        simp [DLBA.BoundedTape.write]
        simpa [DLBA.BoundedTape.read] using hread
      · rfl

/-- A successful departure is exactly reversible by its named arrival. -/
public theorem move_departure_reverse {A : Type u} [DecidableEq A] {n : ℕ}
    (old written : A) (travel : Travel)
    (source target : DLBA.BoundedTape A n) :
    move (.departure old written travel) source = some target ↔
      move (.arrival old written travel) target = some source := by
  rw [move_departure_eq_some_iff, move_arrival_eq_some_iff]
  constructor
  · rintro ⟨hread, targetHead, hnext, rfl⟩
    refine ⟨source.head, ?_, ?_, ?_⟩
    · exact (nextHead_reverse_iff travel source.head targetHead).mp hnext
    · simp [atHead, DLBA.BoundedTape.write]
    · apply eq_of_contents_head
      · classical
        simp [atHead, DLBA.BoundedTape.write]
        simpa [DLBA.BoundedTape.read] using hread
      · rfl
  · rintro ⟨departureHead, hprevious, hwritten, rfl⟩
    refine ⟨?_, target.head, ?_, ?_⟩
    · simp [atHead, DLBA.BoundedTape.read]
    · exact (nextHead_reverse_iff travel departureHead target.head).mpr hprevious
    · apply eq_of_contents_head
      · classical
        simp [atHead, DLBA.BoundedTape.write]
        simpa using hwritten
      · rfl

/-- The concrete locally reversible memory graph on an `(n+1)`-cell bounded
tape.  It requires decidable symbol equality but no finiteness assumption. -/
@[expose]
public def graph (A : Type u) [DecidableEq A] (n : ℕ) :
    MemoryGraph A (Direction A) (DLBA.BoundedTape A n) where
  observe := DLBA.BoundedTape.read
  opposite := Direction.opposite
  opposite_involutive := Direction.opposite_opposite
  move := move
  move_reverse := by
    intro direction source target
    cases direction with
    | stationary old new => exact move_stationary_reverse old new source target
    | departure old written travel =>
        exact move_departure_reverse old written travel source target
    | arrival old written travel =>
        simpa using (move_departure_reverse old written travel target source).symm

@[simp]
public theorem graph_observe {A : Type u} [DecidableEq A] {n : ℕ}
    (tape : DLBA.BoundedTape A n) :
    (graph A n).observe tape = tape.read := rfl

@[simp]
public theorem graph_opposite {A : Type u} [DecidableEq A] {n : ℕ}
    (direction : Direction A) :
    (graph A n).opposite direction = direction.opposite := rfl

@[simp]
public theorem graph_move {A : Type u} [DecidableEq A] {n : ℕ}
    (direction : Direction A) (tape : DLBA.BoundedTape A n) :
    (graph A n).move direction tape = move direction tape := rfl

/-- A successful departure has exactly the ordinary write-and-move result.
Unlike the ordinary operation, the memory operation is simply undefined when
the requested move would clamp. -/
public theorem move_departure_eq_write_moveHead {A : Type u} [DecidableEq A]
    {n : ℕ} (tape : DLBA.BoundedTape A n) (written : A) (travel : Travel)
    {targetHead : Fin (n + 1)}
    (hnext : nextHead travel tape.head = some targetHead) :
    (graph A n).move (.departure tape.read written travel) tape =
      some ((tape.write written).moveHead travel.toDir) := by
  rw [graph_move, move_departure_eq_some_iff]
  refine ⟨rfl, targetHead, hnext, ?_⟩
  apply eq_of_contents_head
  · rfl
  · exact moveHead_eq_of_nextHead (tape.write written) travel hnext

/-- A stationary named operation always gives the ordinary write-and-stay
result when its old-symbol parameter is the observed symbol. -/
public theorem move_stationary_eq_write_moveHead {A : Type u} [DecidableEq A]
    {n : ℕ} (tape : DLBA.BoundedTape A n) (written : A) :
    (graph A n).move (.stationary tape.read written) tape =
      some ((tape.write written).moveHead .stay) := by
  rw [graph_move, move_stationary_eq_some_iff]
  refine ⟨rfl, ?_⟩
  rfl

/-- The inverse/locality equation in the form used by local incoming-port
reconstruction. -/
public theorem move_arrival_iff_departure {A : Type u} [DecidableEq A]
    {n : ℕ} (old written : A) (travel : Travel)
    (source target : DLBA.BoundedTape A n) :
    (graph A n).move (.arrival old written travel) target = some source ↔
      (graph A n).move (.departure old written travel) source = some target := by
  exact (graph A n).move_opposite_iff
    (.departure old written travel) source target

end BoundedTapeMemory

end GraphWalking
