module

public import Langlib.Automata.LinearBounded.BoundaryShuttle.Structural
import Mathlib.Tactic

@[expose]
public section

/-!
# Canonical four-step semantics of the boundary shuttle

The raw compiler is allowed to halt on a clamped protocol move.  This file proves the positive
half: when the source directional move is strictly inside the bounded tape, the four protocol
edges exist and return to the plain embedding of exactly the source successor configuration.
-/

namespace LBA

open Relation

variable {Γ Λ : Type*}

/-- A direction genuinely changes the head on this tape, rather than clamping. -/
@[expose]
public def movesInside {n : ℕ} (tape : DLBA.BoundedTape Γ n) : DLBA.Dir → Prop
  | .left => 0 < tape.head.val
  | .right => tape.head.val < n
  | .stay => False

public theorem movesInside_directional {n : ℕ} {tape : DLBA.BoundedTape Γ n}
    {direction : DLBA.Dir} (hinside : movesInside tape direction) :
    direction ≠ .stay := by
  cases direction <;> simp_all [movesInside]

/-- A genuine inside move changes the head position. -/
public theorem movesInside_head_ne {n : ℕ} (tape : DLBA.BoundedTape Γ n)
    (direction : DLBA.Dir) (hinside : movesInside tape direction) :
    (tape.moveHead direction).head ≠ tape.head := by
  rcases tape with ⟨contents, head⟩
  cases direction with
  | stay => simp [movesInside] at hinside
  | left =>
      simp only [movesInside] at hinside
      simp only [DLBA.BoundedTape.moveHead, hinside, dite_true]
      intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
  | right =>
      simp only [movesInside] at hinside
      simp only [DLBA.BoundedTape.moveHead, hinside, dite_true]
      intro heq
      have := congrArg Fin.val heq
      simp at this

/-- Reversing a genuine inside move returns to the original tape. -/
public theorem moveHead_reverseDirection_moveHead {n : ℕ}
    (tape : DLBA.BoundedTape Γ n) (direction : DLBA.Dir)
    (hinside : movesInside tape direction) :
    (tape.moveHead direction).moveHead (reverseDirection direction) = tape := by
  rcases tape with ⟨contents, head⟩
  cases direction with
  | stay => simp [movesInside] at hinside
  | left =>
      simp only [movesInside] at hinside
      have hright : head.val - 1 < n := by
        have := head.isLt
        omega
      simp only [DLBA.BoundedTape.moveHead, hinside, reverseDirection,
        hright, dite_true]
      congr 1
      apply Fin.ext
      simp
      omega
  | right =>
      simp only [movesInside] at hinside
      have hpositive : 0 < head.val + 1 := by omega
      simp only [DLBA.BoundedTape.moveHead, hinside, reverseDirection,
        hpositive, dite_true]
      congr 1

private theorem boundedTape_ext {A : Type*} {n : ℕ}
    {left right : DLBA.BoundedTape A n}
    (hcontents : left.contents = right.contents)
    (hhead : left.head = right.head) : left = right := by
  cases left
  cases right
  simp_all

/-- Tape after the first (departure-tagging) edge. -/
@[expose]
public def shuttleAfterDeparture {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n :=
  ((shuttleTape (Λ := Λ) tape).write (.departure move)).moveHead move.direction

/-- The untouched source symbol at the genuine neighbouring cell. -/
@[expose]
public def shuttleNeighbourSymbol {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) : Γ :=
  (tape.moveHead move.direction).read

/-- Tape after tagging the neighbour and returning to the departure cell. -/
@[expose]
public def shuttleAfterNeighbour {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n :=
  ((shuttleAfterDeparture move tape).write
      (.neighbour move (shuttleNeighbourSymbol move tape))).moveHead
    (reverseDirection move.direction)

/-- Tape after restoring the departure cell and moving to the neighbour again. -/
@[expose]
public def shuttleAfterRestoreDeparture {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n :=
  ((shuttleAfterNeighbour move tape).write (.plain move.written)).moveHead
    move.direction

/-- Tape after the fourth edge restores the neighbour. -/
@[expose]
public def shuttleAfterFinish {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n) :
    DLBA.BoundedTape (ShuttleAlphabet Γ Λ) n :=
  ((shuttleAfterRestoreDeparture move tape).write
      (.plain (shuttleNeighbourSymbol move tape))).moveHead .stay

/-- A genuine first move lands on the untouched, plain neighbour. -/
public theorem shuttleAfterDeparture_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    (shuttleAfterDeparture move tape).read =
      .plain (shuttleNeighbourSymbol move tape) := by
  classical
  change Function.update (ShuttleAlphabet.plain ∘ tape.contents) tape.head
      (.departure move) (tape.moveHead move.direction).head =
    .plain (tape.contents (tape.moveHead move.direction).head)
  rw [Function.update_of_ne
    (movesInside_head_ne tape move.direction hinside)]
  rfl

/-- The second edge returns to and reads the saved departure tag. -/
public theorem shuttleAfterNeighbour_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    (shuttleAfterNeighbour move tape).read = .departure move := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (moveHead_reverseDirection_moveHead tape move.direction hinside)
  change Function.update
      (Function.update (ShuttleAlphabet.plain ∘ tape.contents) tape.head
        (.departure move))
      (tape.moveHead move.direction).head
      (.neighbour move (shuttleNeighbourSymbol move tape))
      ((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).head = .departure move
  rw [hback]
  rw [Function.update_of_ne
    (movesInside_head_ne tape move.direction hinside).symm]
  simp

/-- The third edge lands on and reads the saved neighbour tag. -/
public theorem shuttleAfterRestoreDeparture_read
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    (shuttleAfterRestoreDeparture move tape).read =
      .neighbour move (shuttleNeighbourSymbol move tape) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (moveHead_reverseDirection_moveHead tape move.direction hinside)
  have hforward :
      (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
          (tape.moveHead move.direction).head := by
    rw [moveHead_reverseDirection_moveHead tape move.direction hinside]
  change Function.update
      (Function.update
        (Function.update (ShuttleAlphabet.plain ∘ tape.contents) tape.head
          (.departure move))
        (tape.moveHead move.direction).head
        (.neighbour move (shuttleNeighbourSymbol move tape)))
      ((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).head
      (.plain move.written)
      (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
          .neighbour move (shuttleNeighbourSymbol move tape)
  rw [hback, hforward]
  rw [Function.update_of_ne
    (movesInside_head_ne tape move.direction hinside)]
  simp

/-- After four genuine edges the tape is exactly the plain embedding of the source transition's
written-and-moved tape. -/
public theorem shuttleAfterFinish_eq
    {n : ℕ} (move : ShuttleMove Γ Λ) (tape : DLBA.BoundedTape Γ n)
    (hinside : movesInside tape move.direction) :
    shuttleAfterFinish move tape =
      shuttleTape (Λ := Λ) ((tape.write move.written).moveHead move.direction) := by
  classical
  have hback := congrArg DLBA.BoundedTape.head
    (moveHead_reverseDirection_moveHead tape move.direction hinside)
  have hforward :
      (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
          (tape.moveHead move.direction).head := by
    rw [moveHead_reverseDirection_moveHead tape move.direction hinside]
  apply boundedTape_ext
  · change Function.update
        (Function.update
          (Function.update
            (Function.update (ShuttleAlphabet.plain ∘ tape.contents) tape.head
              (.departure move))
            (tape.moveHead move.direction).head
            (.neighbour move (shuttleNeighbourSymbol move tape)))
          ((tape.moveHead move.direction).moveHead
            (reverseDirection move.direction)).head
          (.plain move.written))
        (((tape.moveHead move.direction).moveHead
          (reverseDirection move.direction)).moveHead move.direction).head
        (.plain (shuttleNeighbourSymbol move tape)) =
      ShuttleAlphabet.plain ∘
        Function.update tape.contents tape.head move.written
    rw [hback, hforward]
    have hne := movesInside_head_ne tape move.direction hinside
    rw [Function.update_comm hne.symm]
    rw [Function.update_idem]
    rw [Function.update_comm hne]
    rw [Function.update_idem]
    rw [Function.comp_update]
    change Function.update
      (Function.update (ShuttleAlphabet.plain ∘ tape.contents) tape.head
        (.plain move.written))
      (tape.moveHead move.direction).head
      (.plain ((tape.moveHead move.direction).read)) = _
    apply Function.update_eq_self_iff.mpr
    rw [Function.update_of_ne hne]
    rfl
  · change (((tape.moveHead move.direction).moveHead
        (reverseDirection move.direction)).moveHead move.direction).head =
      (tape.moveHead move.direction).head
    exact hforward

/-- One enabled, non-clamped source instruction expands to exactly four shuttle edges. -/
public theorem Machine.reaches_boundaryShuttle_of_move
    (M : Machine Γ Λ) {n : ℕ} (move : ShuttleMove Γ Λ)
    (tape : DLBA.BoundedTape Γ n)
    (henabled : M.ShuttleDirectionalEnabled move)
    (hread : tape.read = move.old)
    (hinside : movesInside tape move.direction) :
    Reaches M.boundaryShuttle
      (shuttleCfg (Λ := Λ) ⟨move.source, tape⟩)
      (shuttleCfg (Λ := Λ)
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩) := by
  let first : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
    ⟨.atNeighbour move, shuttleAfterDeparture move tape⟩
  let second : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
    ⟨.atDeparture move (shuttleNeighbourSymbol move tape),
      shuttleAfterNeighbour move tape⟩
  let third : DLBA.Cfg (ShuttleAlphabet Γ Λ) (ShuttleState Γ Λ) n :=
    ⟨.restoreNeighbour move (shuttleNeighbourSymbol move tape),
      shuttleAfterRestoreDeparture move tape⟩
  have h₁ : Step M.boundaryShuttle
      (shuttleCfg (Λ := Λ) ⟨move.source, tape⟩) first := by
    apply M.step_boundaryShuttle_start move (shuttleTape (Λ := Λ) tape) henabled
    change ShuttleAlphabet.plain tape.read = .plain move.old
    rw [hread]
  have h₂ : Step M.boundaryShuttle first second := by
    apply M.step_boundaryShuttle_tagNeighbour move
      (shuttleNeighbourSymbol move tape) (shuttleAfterDeparture move tape) henabled
    exact shuttleAfterDeparture_read move tape hinside
  have h₃ : Step M.boundaryShuttle second third := by
    apply M.step_boundaryShuttle_restoreDeparture move
      (shuttleNeighbourSymbol move tape) (shuttleAfterNeighbour move tape) henabled
    exact shuttleAfterNeighbour_read move tape hinside
  have h₄ : Step M.boundaryShuttle third
      (shuttleCfg (Λ := Λ)
        ⟨move.target, (tape.write move.written).moveHead move.direction⟩) := by
    have hfinish := M.step_boundaryShuttle_finish move
      (shuttleNeighbourSymbol move tape) (shuttleAfterRestoreDeparture move tape)
      henabled (shuttleAfterRestoreDeparture_read move tape hinside)
    simpa only [third, shuttleCfg, shuttleAfterFinish] using
      (shuttleAfterFinish_eq move tape hinside ▸ hfinish)
  exact (ReflTransGen.single h₁).tail h₂ |>.tail h₃ |>.tail h₄

/-- Configuration-facing form: every non-clamped directional source step is simulated by four
compiled steps. -/
public theorem Machine.reaches_boundaryShuttle_of_step
    (M : Machine Γ Λ) {n : ℕ} {source target : DLBA.Cfg Γ Λ n}
    (hstep : Step M source target)
    (hinside : ∃ next written direction,
      (next, written, direction) ∈ M.transition source.state source.tape.read ∧
      target = ⟨next, (source.tape.write written).moveHead direction⟩ ∧
      movesInside source.tape direction) :
    Reaches M.boundaryShuttle (shuttleCfg source) (shuttleCfg target) := by
  obtain ⟨next, written, direction, henabled, rfl, hinterior⟩ := hinside
  let move : ShuttleMove Γ Λ :=
    { source := source.state
      old := source.tape.read
      target := next
      written := written
      direction := direction }
  exact M.reaches_boundaryShuttle_of_move move source.tape
    ⟨henabled, movesInside_directional hinterior⟩ rfl hinterior

end LBA
