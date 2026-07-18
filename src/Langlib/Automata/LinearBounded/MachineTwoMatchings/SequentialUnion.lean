module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.BranchFunctional
import Mathlib.Tactic

@[expose]
public section

/-!
# Sequentially running the pinned branches of a two-matching LBA

`Machine.pinFirst` turns every possible first transition triple into a functional branch.
This file supplies the operational finite-union machine on the canonical endmarker tape.  Every
physical cell carries both a mutable simulated symbol and an immutable copy of the canonical
input symbol.  When one pinned branch halts without accepting, a deterministic pair of sweeps
restores the mutable track and starts the next branch.

The construction deliberately stays in the endmarker LBA model.  A separate deterministic
endmarker-to-flag compiler can fold the two logical endmarker cells into the marker-free tape
used by the class-level `is_DLBA` definition.

The trial index ranges over `Fintype.equivFin` for the fixed finite move type.  Neither the index
nor the transition selector depends on the input length or consults the two matching layers.
-/

namespace LBA.MachineTwoMatchings

open Classical Relation

variable {T Γ Λ : Type*}

/-- Whether a packed cell occupies the left endpoint, an interior position, or the right
endpoint of the physical endmarker tape.  The tag is immutable during simulation. -/
public inductive Boundary where
  | left
  | middle
  | right
deriving Fintype, DecidableEq

/-- A mutable simulated symbol together with its immutable canonical-input backup. -/
public structure BackupCell (T Γ : Type*) where
  original : EndAlpha T Γ
  current : EndAlpha T Γ
  boundary : Boundary
deriving Fintype, DecidableEq

/-- The enlarged endmarker alphabet.  Packed cells live in the work-symbol summand; the ordinary
input and endmarker constructors remain available for the canonical initial tape. -/
public abbrev BackupAlpha (T Γ : Type*) : Type _ :=
  EndAlpha T (BackupCell T Γ)

/-- Store a backup cell in the work-symbol summand of the enlarged alphabet. -/
@[expose]
public def pack (cell : BackupCell T Γ) : BackupAlpha T Γ :=
  Sum.inl (some (Sum.inr cell))

/-- Recognize a packed work cell. -/
@[expose]
public def unpack : BackupAlpha T Γ → Option (BackupCell T Γ)
  | Sum.inl (some (Sum.inr cell)) => some cell
  | _ => none

@[simp]
public theorem unpack_pack (cell : BackupCell T Γ) : unpack (pack cell) = some cell := rfl

/-- Restore the mutable track of one packed cell. -/
@[expose]
public def BackupCell.restore (cell : BackupCell T Γ) : BackupCell T Γ :=
  { cell with current := cell.original }

@[simp]
public theorem BackupCell.restore_original (cell : BackupCell T Γ) :
    cell.restore.original = cell.original := rfl

@[simp]
public theorem BackupCell.restore_current (cell : BackupCell T Γ) :
    cell.restore.current = cell.original := rfl

@[simp]
public theorem BackupCell.restore_boundary (cell : BackupCell T Γ) :
    cell.restore.boundary = cell.boundary := rfl

/-- All possible transition triples of the source machine. -/
public abbrev Move (Γ Λ : Type*) := Λ × Γ × DLBA.Dir

/-- One extra index denotes that all finite trials have been exhausted. -/
public abbrev TrialIndex (Γ Λ : Type*) [Fintype Γ] [Fintype Λ] :=
  Fin (Fintype.card (Move Γ Λ) + 1)

/-- The move assigned to a nonterminal trial index. -/
@[expose]
public noncomputable def moveAt?
    [Fintype Γ] [Fintype Λ] (index : TrialIndex Γ Λ) : Option (Move Γ Λ) :=
  if h : index.val < Fintype.card (Move Γ Λ) then
    some ((Fintype.equivFin (Move Γ Λ)).symm ⟨index.val, h⟩)
  else none

/-- Advance past a nonterminal trial. -/
@[expose]
public def nextIndex
    [Fintype Γ] [Fintype Λ]
    (index : TrialIndex Γ Λ)
    (h : index.val < Fintype.card (Move Γ Λ)) : TrialIndex Γ Λ :=
  ⟨index.val + 1, by omega⟩

/-- Every move occurs at its `equivFin` index. -/
public theorem moveAt?_equivFin
    [Fintype Γ] [Fintype Λ] (move : Move Γ Λ) :
    moveAt? (⟨(Fintype.equivFin (Move Γ Λ) move).val, by
      have := (Fintype.equivFin (Move Γ Λ) move).isLt
      omega⟩ : TrialIndex Γ Λ) = some move := by
  simp only [moveAt?]
  split
  · next h => simp
  · next h =>
      exact False.elim (h (Fintype.equivFin (Move Γ Λ) move).isLt)

/-- Finite control for initialization, branch simulation, and reset sweeps. -/
public inductive SequentialState
    (T Γ Λ : Type*) [Fintype (EndAlpha T Γ)] [Fintype Λ] where
  | initializeLeft
  | initializeRight
  | rewind (next : TrialIndex (EndAlpha T Γ) Λ)
  | run (next : TrialIndex (EndAlpha T Γ) Λ)
      (first : Move (EndAlpha T Γ) Λ) (state : FirstMoveState Λ)
  | resetLeft (next : TrialIndex (EndAlpha T Γ) Λ)
  | restoreRight (next : TrialIndex (EndAlpha T Γ) Λ)
deriving Fintype, DecidableEq

variable [Fintype T] [Fintype Γ] [Fintype Λ]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ]

/-- The canonical source symbol represented by an unprocessed target-alphabet symbol. -/
def rawSourceSymbol : BackupAlpha T Γ → Option (EndAlpha T Γ)
  | Sum.inr false => some leftMark
  | Sum.inr true => some rightMark
  | Sum.inl (some (Sum.inl input)) => some (Sum.inl (some (Sum.inl input)))
  | _ => none

/-- Pack a raw canonical input cell, assigning the supplied immutable boundary tag. -/
def initializeCell (symbol : BackupAlpha T Γ) (boundary : Boundary) :
    Option (BackupAlpha T Γ) :=
  (rawSourceSymbol symbol).map fun source =>
    pack { original := source, current := source, boundary := boundary }

/-- Map one transition triple of a pinned machine to the packed sequential machine. -/
def mappedPinnedMove
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (cell : BackupCell T Γ)
    (move : Move (EndAlpha T Γ) (FirstMoveState Λ)) :
    SequentialState T Γ Λ × BackupAlpha T Γ × DLBA.Dir :=
  (.run next first move.1,
    pack { cell with current := move.2.1 }, move.2.2)

/-- The deterministic sequential-union transition table.

On a malformed raw tape the machine simply halts nonaccepting.  All simulation and reset cases
only operate on packed cells. -/
@[expose]
public noncomputable def sequentialTransition
    (M : Machine (EndAlpha T Γ) Λ) :
    SequentialState T Γ Λ → BackupAlpha T Γ →
      Set (SequentialState T Γ Λ × BackupAlpha T Γ × DLBA.Dir)
  | .initializeLeft, symbol =>
      if symbol = (leftMark : BackupAlpha T Γ) then
        {(.initializeRight,
          pack { original := leftMark, current := leftMark, boundary := .left },
          .right)}
      else ∅
  | .initializeRight, symbol =>
      if symbol = (rightMark : BackupAlpha T Γ) then
        {(.rewind 0,
          pack { original := rightMark, current := rightMark, boundary := .right },
          .left)}
      else
        match initializeCell symbol .middle with
        | some packed => {(.initializeRight, packed, .right)}
        | none => ∅
  | .rewind next, symbol =>
      match unpack symbol with
      | none => ∅
      | some cell =>
          if cell.boundary = .left then
            match hmove : moveAt? next with
            | none => ∅
            | some first =>
                let hlt : next.val < Fintype.card (Move (EndAlpha T Γ) Λ) := by
                  simp only [moveAt?] at hmove
                  split at hmove
                  · assumption
                  · simp at hmove
                {(.run (nextIndex next hlt) first .boot, symbol, .stay)}
          else {(.rewind next, symbol, .left)}
  | .run next first state, symbol =>
      match unpack symbol with
      | none => ∅
      | some cell =>
          if (M.pinFirst first).accept state = true then ∅
          else
            match hmove : (M.pinFirst first).selectedMove state cell.current with
            | some move => {mappedPinnedMove next first cell move}
            | none => {(.resetLeft next, symbol, .stay)}
  | .resetLeft next, symbol =>
      match unpack symbol with
      | none => ∅
      | some cell =>
          if cell.boundary = .left then
            {(.restoreRight next, pack cell.restore, .right)}
          else {(.resetLeft next, symbol, .left)}
  | .restoreRight next, symbol =>
      match unpack symbol with
      | none => ∅
      | some cell =>
          if cell.boundary = .right then
            {(.rewind next, pack cell.restore, .left)}
          else {(.restoreRight next, pack cell.restore, .right)}

/-- A functional endmarker LBA that tries every pinned first move in a fixed finite order. -/
@[expose]
public noncomputable def sequentialUnion
    (M : Machine (EndAlpha T Γ) Λ) :
    Machine (BackupAlpha T Γ) (SequentialState T Γ Λ) where
  transition := sequentialTransition M
  accept
    | .run _ first state => (M.pinFirst first).accept state
    | _ => false
  initial := .initializeLeft

/-! ## Exact packed simulation of one pinned trial -/

/-- Immutable endpoint tag determined by a physical tape position. -/
@[expose]
public def boundaryAt (n : ℕ) (index : Fin (n + 1)) : Boundary :=
  if index.val = 0 then .left else if index.val = n then .right else .middle

@[simp]
public theorem boundaryAt_eq_left_iff {n : ℕ} {index : Fin (n + 1)} :
    boundaryAt n index = .left ↔ index.val = 0 := by
  constructor
  · intro h
    by_cases hzero : index.val = 0
    · exact hzero
    · exfalso
      by_cases hlast : index.val = n
      · have hnzero : n = 0 := by
          simpa [boundaryAt, hzero, hlast] using h
        exact hzero (hlast.trans hnzero)
      · simp [boundaryAt, hzero, hlast] at h
  · intro hzero
    simp [boundaryAt, hzero]

public theorem boundaryAt_eq_right_iff {n : ℕ} (hn : 0 < n)
    {index : Fin (n + 1)} :
    boundaryAt n index = .right ↔ index.val = n := by
  constructor
  · intro h
    by_cases hzero : index.val = 0
    · simp [boundaryAt, hzero] at h
    · by_cases hlast : index.val = n
      · exact hlast
      · simp [boundaryAt, hzero, hlast] at h
  · intro hlast
    have hzero : index.val ≠ 0 := by omega
    unfold boundaryAt
    rw [if_neg hzero, if_pos hlast]

/-- Pack an arbitrary mutable tape while retaining a fixed immutable symbol at every cell. -/
@[expose]
public def packedTape {n : ℕ}
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n) :
    DLBA.BoundedTape (BackupAlpha T Γ) n :=
  ⟨fun index => pack {
      original := original index
      current := current.contents index
      boundary := boundaryAt n index },
    current.head⟩

/-- Embed a pinned-machine configuration into a running sequential trial. -/
@[expose]
public def packedRunCfg {n : ℕ}
    (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (cfg : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n) :
    DLBA.Cfg (BackupAlpha T Γ) (SequentialState T Γ Λ) n :=
  ⟨.run next first cfg.state, packedTape original cfg.tape⟩

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
@[simp]
public theorem unpack_packedTape_read {n : ℕ}
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n) :
    unpack (packedTape original current).read = some {
      original := original current.head
      current := current.read
      boundary := boundaryAt n current.head } := rfl

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
/-- Updating the mutable field of the packed head and making the same bounded head move exactly
commutes with packing. -/
public theorem packedTape_write_move {n : ℕ}
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (written : EndAlpha T Γ) (direction : DLBA.Dir) :
    ((packedTape original current).write
      (pack {
        original := original current.head
        current := written
        boundary := boundaryAt n current.head })).moveHead direction =
      packedTape original ((current.write written).moveHead direction) := by
  rcases current with ⟨contents, head⟩
  rw [DLBA.BoundedTape.mk.injEq]
  constructor
  · funext index
    simp only [packedTape, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      Function.update_apply]
    split <;> simp_all
  · simp [packedTape, DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]

omit [Fintype T] [Fintype Γ] [DecidableEq T] [DecidableEq Γ] in
/-- Packing commutes with a head move that does not change tape contents. -/
public theorem packedTape_move {n : ℕ}
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (direction : DLBA.Dir) :
    (packedTape original current).moveHead direction =
      packedTape original (current.moveHead direction) := by
  rcases current with ⟨contents, head⟩
  rw [DLBA.BoundedTape.mk.injEq]
  constructor
  · rfl
  · simp [packedTape, DLBA.BoundedTape.moveHead]

omit [DecidableEq Λ] in
/-- A nonaccepting pinned step is simulated by exactly one running step of the sequential
machine, with the immutable track unchanged. -/
public theorem step_sequentialUnion_run_of_step_pinFirst
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    {source target : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n}
    (hnonaccept : (M.pinFirst first).accept source.state ≠ true)
    (hstep : Step (M.pinFirst first) source target) :
    Step (sequentialUnion M) (packedRunCfg original next first source)
      (packedRunCfg original next first target) := by
  rcases source with ⟨state, tape⟩
  rcases hstep with ⟨targetState, written, direction, henabled, rfl⟩
  obtain ⟨selected, hselected⟩ :=
    (M.pinFirst first).exists_selectedMove_of_mem henabled
  have hselectedEq : selected = (targetState, written, direction) :=
    (M.pinFirst_functional first) state tape.read
      ((M.pinFirst first).selectedMove_mem hselected) henabled
  subst selected
  refine ⟨.run next first targetState,
    pack {
      original := original tape.head
      current := written
      boundary := boundaryAt n tape.head },
    direction, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, packedRunCfg,
      unpack_packedTape_read]
    rw [if_neg hnonaccept, hselected]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl, (packedTape_write_move original tape written direction).symm⟩

omit [DecidableEq Λ] in
/-- A pinned run either encounters an accepting state (where the sequential machine stops the
trial) or is mirrored completely on the mutable track. -/
public theorem accepts_or_reaches_sequentialUnion_run_of_reaches_pinFirst
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    {source target : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n}
    (hreach : Reaches (M.pinFirst first) source target) :
    Accepts (sequentialUnion M) (packedRunCfg original next first source) ∨
      Reaches (sequentialUnion M) (packedRunCfg original next first source)
        (packedRunCfg original next first target) := by
  induction hreach with
  | refl => exact Or.inr .refl
  | @tail middle target hreach hstep ih =>
      rcases ih with haccept | hpacked
      · exact Or.inl haccept
      · by_cases hmiddle : (M.pinFirst first).accept middle.state = true
        · exact Or.inl ⟨packedRunCfg original next first middle, hpacked, hmiddle⟩
        · exact Or.inr (hpacked.tail
            (step_sequentialUnion_run_of_step_pinFirst M original next first
              hmiddle hstep))

omit [DecidableEq Λ] in
/-- Acceptance by one pinned branch lifts to acceptance by the running phase of the sequential
machine. -/
public theorem accepts_sequentialUnion_run_of_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (source : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n)
    (haccept : Accepts (M.pinFirst first) source) :
    Accepts (sequentialUnion M) (packedRunCfg original next first source) := by
  obtain ⟨target, hreach, hfinal⟩ := haccept
  rcases accepts_or_reaches_sequentialUnion_run_of_reaches_pinFirst
      M original next first hreach with haccept | hpacked
  · exact haccept
  · exact ⟨packedRunCfg original next first target, hpacked, hfinal⟩

omit [DecidableEq Λ] in
/-- If the pinned branch does not accept, an entire pinned run is mirrored without taking the
sequential machine's accepting early exit. -/
public theorem reaches_sequentialUnion_run_of_reaches_pinFirst_of_not_accepts
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    {source target : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n}
    (hreject : ¬ Accepts (M.pinFirst first) source)
    (hreach : Reaches (M.pinFirst first) source target) :
    Reaches (sequentialUnion M) (packedRunCfg original next first source)
      (packedRunCfg original next first target) := by
  induction hreach with
  | refl => exact .refl
  | @tail middle target hreach hstep ih =>
      have hnonaccept : (M.pinFirst first).accept middle.state ≠ true := by
        intro hfinal
        exact hreject ⟨middle, hreach, hfinal⟩
      exact ih.tail
        (step_sequentialUnion_run_of_step_pinFirst M original next first
          hnonaccept hstep)

/-- Writing back the symbol currently under the head and staying put leaves a bounded tape
unchanged. -/
public theorem write_read_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) :
    (tape.write tape.read).moveHead .stay = tape := by
  rcases tape with ⟨contents, head⟩
  rw [DLBA.BoundedTape.mk.injEq]
  constructor
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      Function.update_eq_self]
  · rfl

/-- Writing the symbol already under the head before an arbitrary head move has no effect on
the tape contents. -/
public theorem write_read_move {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) (direction : DLBA.Dir) :
    (tape.write tape.read).moveHead direction = tape.moveHead direction := by
  have hwrite : tape.write tape.read = tape := by
    rcases tape with ⟨contents, head⟩
    rw [DLBA.BoundedTape.mk.injEq]
    constructor
    · simp [DLBA.BoundedTape.write, Function.update_eq_self]
    · rfl
  rw [hwrite]

omit [DecidableEq Λ] in
/-- A nonaccepting pinned sink makes the running phase enter the left-reset sweep without
changing the packed tape. -/
public theorem step_sequentialUnion_resetLeft_of_pinFirst_sink
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (target : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n)
    (hreject : (M.pinFirst first).accept target.state = false)
    (hsink : ∀ successor, ¬ Step (M.pinFirst first) target successor) :
    Step (sequentialUnion M) (packedRunCfg original next first target)
      ⟨.resetLeft next, packedTape original target.tape⟩ := by
  have hselected :
      (M.pinFirst first).selectedMove target.state target.tape.read = none := by
    cases hmove : (M.pinFirst first).selectedMove target.state target.tape.read with
    | none => rfl
    | some move =>
        exact False.elim (hsink
          ⟨move.1, (target.tape.write move.2.1).moveHead move.2.2⟩
          ⟨move.1, move.2.1, move.2.2,
            (M.pinFirst first).selectedMove_mem hmove, rfl⟩)
  refine ⟨.resetLeft next, (packedTape original target.tape).read, .stay, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, packedRunCfg,
      unpack_packedTape_read]
    rw [if_neg (show (M.pinFirst first).accept target.state ≠ true by simp [hreject]),
      hselected]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl, (write_read_stay (packedTape original target.tape)).symm⟩

omit [DecidableEq Λ] in
/-- Every failed acyclic pinned trial reaches the reset phase. -/
public theorem exists_reaches_resetLeft_of_not_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (source : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n)
    (hreject : ¬ Accepts (M.pinFirst first) source) :
    ∃ target : DLBA.Cfg (EndAlpha T Γ) (FirstMoveState Λ) n,
      Reaches (sequentialUnion M) (packedRunCfg original next first source)
        ⟨.resetLeft next, packedTape original target.tape⟩ := by
  obtain ⟨target, hreach, hfinal, hsink⟩ :=
    M.exists_reachable_rejecting_sink_pinFirst hacyclic first source hreject
  refine ⟨target,
    (reaches_sequentialUnion_run_of_reaches_pinFirst_of_not_accepts
      M original next first hreject hreach).tail ?_⟩
  exact step_sequentialUnion_resetLeft_of_pinFirst_sink
    M original next first target hfinal hsink

/-! ## Local reset-sweep semantics -/

omit [DecidableEq Λ] in
/-- Before the left endpoint is reached, the reset phase moves left without changing either
track. -/
public theorem step_sequentialUnion_resetLeft_of_not_left
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hleft : boundaryAt n current.head ≠ .left) :
    Step (sequentialUnion M)
      ⟨.resetLeft next, packedTape original current⟩
      ⟨.resetLeft next, packedTape original (current.moveHead .left)⟩ := by
  refine ⟨.resetLeft next, (packedTape original current).read, .left, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, unpack_packedTape_read]
    rw [if_neg hleft]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl, (packedTape_move original current .left).symm.trans
      (write_read_move (packedTape original current) .left).symm⟩

omit [DecidableEq Λ] in
/-- At the left endpoint, reset restores that cell and starts the rightward restoration sweep. -/
public theorem step_sequentialUnion_resetLeft_of_left
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hleft : boundaryAt n current.head = .left) :
    Step (sequentialUnion M)
      ⟨.resetLeft next, packedTape original current⟩
      ⟨.restoreRight next,
        packedTape original ((current.write (original current.head)).moveHead .right)⟩ := by
  refine ⟨.restoreRight next,
    pack {
      original := original current.head
      current := original current.head
      boundary := boundaryAt n current.head }, .right, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, unpack_packedTape_read]
    rw [if_pos hleft]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl,
      (packedTape_write_move original current (original current.head) .right).symm⟩

omit [DecidableEq Λ] in
/-- At a non-right cell, the rightward sweep restores that cell and advances. -/
public theorem step_sequentialUnion_restoreRight_of_not_right
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hright : boundaryAt n current.head ≠ .right) :
    Step (sequentialUnion M)
      ⟨.restoreRight next, packedTape original current⟩
      ⟨.restoreRight next,
        packedTape original ((current.write (original current.head)).moveHead .right)⟩ := by
  refine ⟨.restoreRight next,
    pack {
      original := original current.head
      current := original current.head
      boundary := boundaryAt n current.head }, .right, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, unpack_packedTape_read]
    rw [if_neg hright]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl,
      (packedTape_write_move original current (original current.head) .right).symm⟩

omit [DecidableEq Λ] in
/-- At the right endpoint, the sweep restores the final cell and switches to the ordinary
leftward rewind. -/
public theorem step_sequentialUnion_restoreRight_of_right
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hright : boundaryAt n current.head = .right) :
    Step (sequentialUnion M)
      ⟨.restoreRight next, packedTape original current⟩
      ⟨.rewind next,
        packedTape original ((current.write (original current.head)).moveHead .left)⟩ := by
  refine ⟨.rewind next,
    pack {
      original := original current.head
      current := original current.head
      boundary := boundaryAt n current.head }, .left, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, unpack_packedTape_read]
    rw [if_pos hright]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl,
      (packedTape_write_move original current (original current.head) .left).symm⟩

omit [DecidableEq Λ] in
/-- Repeated left-reset steps reach the uniquely tagged left endpoint without changing mutable
contents. -/
public theorem exists_reaches_sequentialUnion_resetLeft_boundary
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n) :
    ∃ leftTape : DLBA.BoundedTape (EndAlpha T Γ) n,
      leftTape.contents = current.contents ∧
      leftTape.head.val = 0 ∧
      Reaches (sequentialUnion M)
        ⟨.resetLeft next, packedTape original current⟩
        ⟨.resetLeft next, packedTape original leftTape⟩ := by
  generalize hvalue : current.head.val = value
  induction value using Nat.strong_induction_on generalizing current with
  | h value ih =>
      by_cases hzero : value = 0
      · exact ⟨current, rfl, by omega, .refl⟩
      · let moved := current.moveHead DLBA.Dir.left
        have hpositive : 0 < current.head.val := by omega
        have hmovedVal : moved.head.val = current.head.val - 1 := by
          simp [moved, DLBA.BoundedTape.moveHead, hpositive]
        have hlt : moved.head.val < value := by omega
        obtain ⟨leftTape, hcontents, hhead, hreach⟩ :=
          ih moved.head.val hlt moved rfl
        refine ⟨leftTape, ?_, hhead,
          ReflTransGen.head
            (step_sequentialUnion_resetLeft_of_not_left
              M original next current ?_) hreach⟩
        · exact hcontents
        · intro hboundary
          have hheadzero := boundaryAt_eq_left_iff.mp hboundary
          omega

omit [DecidableEq Λ] in
/-- With the strict left-to-right prefix invariant, the restoration sweep reaches the right
endpoint, restores every mutable symbol, and changes to rewind mode.  The positive-width
hypothesis is essential: at width zero the sole cell carries the left tag, not a right tag. -/
public theorem exists_reaches_sequentialUnion_restoreRight_rewind
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hprefix : ∀ index, index.val < current.head.val →
      current.contents index = original index) :
    ∃ restored : DLBA.BoundedTape (EndAlpha T Γ) n,
      restored.contents = original ∧
      Reaches (sequentialUnion M)
        ⟨.restoreRight next, packedTape original current⟩
        ⟨.rewind next, packedTape original restored⟩ := by
  generalize hdistance : n - current.head.val = distance
  induction distance using Nat.strong_induction_on generalizing current with
  | h distance ih =>
      by_cases hatRight : current.head.val = n
      · let restored :=
          (current.write (original current.head)).moveHead DLBA.Dir.left
        have hcontents : restored.contents = original := by
          funext index
          simp only [restored, DLBA.BoundedTape.moveHead,
            DLBA.BoundedTape.write, Function.update_apply]
          by_cases heq : index = current.head
          · simp [heq]
          · rw [if_neg heq]
            apply hprefix
            have hindex := index.isLt
            have hneVal : index.val ≠ current.head.val := by
              intro hval
              exact heq (Fin.ext hval)
            omega
        refine ⟨restored, hcontents,
          ReflTransGen.single
            (step_sequentialUnion_restoreRight_of_right
              M original next current ?_)⟩
        exact (boundaryAt_eq_right_iff hn).2 hatRight
      · have hbeforeRight : current.head.val < n := by
          have := current.head.isLt
          omega
        let moved :=
          (current.write (original current.head)).moveHead DLBA.Dir.right
        have hmovedHead : moved.head.val = current.head.val + 1 := by
          simp only [moved, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
          rw [dif_pos hbeforeRight]
        have hprefixMoved : ∀ index, index.val < moved.head.val →
            moved.contents index = original index := by
          intro index hindex
          simp only [moved, DLBA.BoundedTape.moveHead,
            DLBA.BoundedTape.write, Function.update_apply]
          by_cases heq : index = current.head
          · simp [heq]
          · rw [if_neg heq]
            apply hprefix
            have hneVal : index.val ≠ current.head.val := by
              intro hval
              exact heq (Fin.ext hval)
            omega
        have hcloser : n - moved.head.val < distance := by omega
        obtain ⟨restored, hcontents, hreach⟩ :=
          ih (n - moved.head.val) hcloser moved hprefixMoved rfl
        refine ⟨restored, hcontents,
          ReflTransGen.head
            (step_sequentialUnion_restoreRight_of_not_right
              M original next current ?_) hreach⟩
        intro hboundary
        exact hatRight ((boundaryAt_eq_right_iff hn).1 hboundary)

omit [DecidableEq Λ] in
/-- A complete reset cycle first finds the left endpoint, then restores every mutable cell,
and finally enters rewind mode with the original tape contents. -/
public theorem exists_reaches_sequentialUnion_resetLeft_rewind
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n) :
    ∃ restored : DLBA.BoundedTape (EndAlpha T Γ) n,
      restored.contents = original ∧
      Reaches (sequentialUnion M)
        ⟨.resetLeft next, packedTape original current⟩
        ⟨.rewind next, packedTape original restored⟩ := by
  obtain ⟨leftTape, _, hleftHead, hreachLeft⟩ :=
    exists_reaches_sequentialUnion_resetLeft_boundary
      M original next current
  have hleftBoundary : boundaryAt n leftTape.head = .left :=
    boundaryAt_eq_left_iff.mpr hleftHead
  let begun :=
    (leftTape.write (original leftTape.head)).moveHead DLBA.Dir.right
  have hbeforeRight : leftTape.head.val < n := by omega
  have hbegunHead : begun.head.val = 1 := by
    simp only [begun, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write]
    rw [dif_pos hbeforeRight]
    simp [hleftHead]
  have hprefixBegun : ∀ index, index.val < begun.head.val →
      begun.contents index = original index := by
    intro index hindex
    have hindexZero : index.val = 0 := by omega
    have heq : index = leftTape.head := Fin.ext (by omega)
    simp [begun, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, heq]
  obtain ⟨restored, hcontents, hreachRestore⟩ :=
    exists_reaches_sequentialUnion_restoreRight_rewind
      M hn original next begun hprefixBegun
  refine ⟨restored, hcontents, hreachLeft.trans ?_⟩
  exact ReflTransGen.head
    (step_sequentialUnion_resetLeft_of_left
      M original next leftTape hleftBoundary)
    hreachRestore

/-! ## Rewind and trial launch semantics -/

omit [DecidableEq Λ] in
/-- Before the left endpoint is reached, rewind moves left without changing the packed tape
contents. -/
public theorem step_sequentialUnion_rewind_of_not_left
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hleft : boundaryAt n current.head ≠ .left) :
    Step (sequentialUnion M)
      ⟨.rewind next, packedTape original current⟩
      ⟨.rewind next, packedTape original (current.moveHead .left)⟩ := by
  refine ⟨.rewind next, (packedTape original current).read, .left, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, unpack_packedTape_read]
    rw [if_neg hleft]
    rfl
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl, (packedTape_move original current .left).symm.trans
      (write_read_move (packedTape original current) .left).symm⟩

omit [DecidableEq Λ] in
/-- At the left endpoint, a nonterminal trial index launches its pinned machine in the boot
state. -/
public theorem step_sequentialUnion_rewind_launch
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hleft : boundaryAt n current.head = .left)
    (hmove : moveAt? next = some first) :
    ∃ hlt : next.val < Fintype.card (Move (EndAlpha T Γ) Λ),
      Step (sequentialUnion M)
        ⟨.rewind next, packedTape original current⟩
        (packedRunCfg original (nextIndex next hlt) first
          ⟨.boot, current⟩) := by
  have hlt : next.val < Fintype.card (Move (EndAlpha T Γ) Λ) := by
    simp only [moveAt?] at hmove
    split at hmove
    · assumption
    · simp at hmove
  have hfirst :
      (Fintype.equivFin (Move (EndAlpha T Γ) Λ)).symm ⟨next.val, hlt⟩ = first := by
    simp only [moveAt?, dif_pos hlt] at hmove
    exact Option.some.inj hmove
  refine ⟨hlt, .run (nextIndex next hlt) first .boot,
    (packedTape original current).read, .stay, ?_, ?_⟩
  · simp only [sequentialUnion, sequentialTransition, unpack_packedTape_read]
    rw [if_pos hleft]
    subst first
    simp only [moveAt?]
    split
    · next hnone =>
      rw [dif_pos hlt] at hnone
      simp at hnone
    · next chosen hchosen =>
      rw [dif_pos hlt] at hchosen
      have hchosenEq := Option.some.inj hchosen.symm
      subst chosen
      simp
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl, (write_read_stay (packedTape original current)).symm⟩

omit [DecidableEq Λ] in
/-- A rewind sweep reaches the left endpoint without changing mutable contents. -/
public theorem exists_reaches_sequentialUnion_rewind_boundary
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n) :
    ∃ leftTape : DLBA.BoundedTape (EndAlpha T Γ) n,
      leftTape.contents = current.contents ∧
      leftTape.head.val = 0 ∧
      Reaches (sequentialUnion M)
        ⟨.rewind next, packedTape original current⟩
        ⟨.rewind next, packedTape original leftTape⟩ := by
  generalize hvalue : current.head.val = value
  induction value using Nat.strong_induction_on generalizing current with
  | h value ih =>
      by_cases hzero : value = 0
      · exact ⟨current, rfl, by omega, .refl⟩
      · let moved := current.moveHead DLBA.Dir.left
        have hpositive : 0 < current.head.val := by omega
        have hmovedVal : moved.head.val = current.head.val - 1 := by
          simp [moved, DLBA.BoundedTape.moveHead, hpositive]
        have hlt : moved.head.val < value := by omega
        obtain ⟨leftTape, hcontents, hhead, hreach⟩ :=
          ih moved.head.val hlt moved rfl
        refine ⟨leftTape, hcontents, hhead,
          ReflTransGen.head
            (step_sequentialUnion_rewind_of_not_left
              M original next current ?_) hreach⟩
        intro hboundary
        have hheadzero := boundaryAt_eq_left_iff.mp hboundary
        omega

omit [DecidableEq Λ] in
/-- For a nonterminal index, rewind deterministically reaches the boot configuration of the
corresponding pinned trial. -/
public theorem exists_reaches_sequentialUnion_rewind_launch
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hmove : moveAt? next = some first) :
    ∃ (leftTape : DLBA.BoundedTape (EndAlpha T Γ) n)
      (hlt : next.val < Fintype.card (Move (EndAlpha T Γ) Λ)),
      leftTape.contents = current.contents ∧
      leftTape.head.val = 0 ∧
      Reaches (sequentialUnion M)
        ⟨.rewind next, packedTape original current⟩
        (packedRunCfg original (nextIndex next hlt) first
          ⟨.boot, leftTape⟩) := by
  obtain ⟨leftTape, hcontents, hhead, hreach⟩ :=
    exists_reaches_sequentialUnion_rewind_boundary
      M original next current
  have hleft : boundaryAt n leftTape.head = .left :=
    boundaryAt_eq_left_iff.mpr hhead
  obtain ⟨hlt, hstep⟩ :=
    step_sequentialUnion_rewind_launch
      M original next first leftTape hleft hmove
  exact ⟨leftTape, hlt, hcontents, hhead, hreach.tail hstep⟩

/-- The bounded tape with prescribed contents and its head at the left endpoint. -/
@[expose]
public def leftBoundedTape {A : Type*} {n : ℕ}
    (contents : Fin (n + 1) → A) : DLBA.BoundedTape A n :=
  ⟨contents, ⟨0, Nat.succ_pos _⟩⟩

/-- Contents equality and a zero head characterize `leftBoundedTape`. -/
public theorem eq_leftBoundedTape_of_contents_of_head_zero
    {A : Type*} {n : ℕ} (current : DLBA.BoundedTape A n)
    (contents : Fin (n + 1) → A)
    (hcontents : current.contents = contents)
    (hhead : current.head.val = 0) :
    current = leftBoundedTape contents := by
  rcases current with ⟨currentContents, head⟩
  rw [DLBA.BoundedTape.mk.injEq]
  exact ⟨hcontents, Fin.ext hhead⟩

omit [DecidableEq Λ] in
/-- If the trial selected at the current index accepts the restored left-headed tape, then the
sequential machine accepts from any rewind configuration whose mutable contents are restored. -/
public theorem accepts_sequentialUnion_rewind_of_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original)
    (hmove : moveAt? next = some first)
    (haccept : Accepts (M.pinFirst first)
      (M.pinFirstBootCfg (leftBoundedTape original))) :
    Accepts (sequentialUnion M)
      ⟨.rewind next, packedTape original current⟩ := by
  obtain ⟨leftTape, hlt, hleftContents, hleftHead, hlaunch⟩ :=
    exists_reaches_sequentialUnion_rewind_launch
      M original next first current hmove
  have hleftEq : leftTape = leftBoundedTape original :=
    eq_leftBoundedTape_of_contents_of_head_zero leftTape original
      (hleftContents.trans hcontents) hleftHead
  subst leftTape
  obtain ⟨target, hrun, hfinal⟩ :=
    accepts_sequentialUnion_run_of_accepts_pinFirst
      M original (nextIndex next hlt) first
        (M.pinFirstBootCfg (leftBoundedTape original)) haccept
  exact ⟨target, hlaunch.trans hrun, hfinal⟩

omit [DecidableEq Λ] in
/-- A rejected acyclic trial advances the scheduler to the next index with the mutable tape
fully restored. -/
public theorem exists_reaches_sequentialUnion_next_of_not_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (next : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original)
    (hmove : moveAt? next = some first)
    (hreject : ¬ Accepts (M.pinFirst first)
      (M.pinFirstBootCfg (leftBoundedTape original))) :
    ∃ (advanced : TrialIndex (EndAlpha T Γ) Λ)
      (restored : DLBA.BoundedTape (EndAlpha T Γ) n),
      advanced.val = next.val + 1 ∧
      restored.contents = original ∧
      Reaches (sequentialUnion M)
        ⟨.rewind next, packedTape original current⟩
        ⟨.rewind advanced, packedTape original restored⟩ := by
  obtain ⟨leftTape, hlt, hleftContents, hleftHead, hlaunch⟩ :=
    exists_reaches_sequentialUnion_rewind_launch
      M original next first current hmove
  have hleftEq : leftTape = leftBoundedTape original :=
    eq_leftBoundedTape_of_contents_of_head_zero leftTape original
      (hleftContents.trans hcontents) hleftHead
  subst leftTape
  obtain ⟨_, hreset⟩ :=
    exists_reaches_resetLeft_of_not_accepts_pinFirst
      M hacyclic original (nextIndex next hlt) first
        (M.pinFirstBootCfg (leftBoundedTape original)) hreject
  obtain ⟨restored, hrestored, hrestore⟩ :=
    exists_reaches_sequentialUnion_resetLeft_rewind
      M hn original (nextIndex next hlt) _
  exact ⟨nextIndex next hlt, restored, rfl, hrestored,
    hlaunch.trans (hreset.trans hrestore)⟩

omit [DecidableEq Λ] in
/-- If some trial at or after the current index accepts, then the scheduler accepts.  Earlier
trials need not be known rejecting in advance: the proof follows the first one that accepts and
uses acyclicity to reset every one that does not. -/
public theorem accepts_sequentialUnion_rewind_of_later_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (target : TrialIndex (EndAlpha T Γ) Λ)
    (first : Move (EndAlpha T Γ) Λ)
    (htarget : moveAt? target = some first)
    (haccept : Accepts (M.pinFirst first)
      (M.pinFirstBootCfg (leftBoundedTape original)))
    (index : TrialIndex (EndAlpha T Γ) Λ)
    (hle : index.val ≤ target.val)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original) :
    Accepts (sequentialUnion M)
      ⟨.rewind index, packedTape original current⟩ := by
  have htargetLt : target.val < Fintype.card (Move (EndAlpha T Γ) Λ) := by
    simp only [moveAt?] at htarget
    split at htarget
    · assumption
    · simp at htarget
  generalize hdistance : target.val - index.val = distance
  induction distance using Nat.strong_induction_on generalizing index current with
  | h distance ih =>
      by_cases heq : index.val = target.val
      · have hindex : index = target := Fin.ext heq
        subst index
        exact accepts_sequentialUnion_rewind_of_accepts_pinFirst
          M original target first current hcontents htarget haccept
      · have hindexLt : index.val < target.val := by omega
        have hcurrentLt : index.val < Fintype.card (Move (EndAlpha T Γ) Λ) := by
          omega
        let currentFirst : Move (EndAlpha T Γ) Λ :=
          (Fintype.equivFin (Move (EndAlpha T Γ) Λ)).symm
            ⟨index.val, hcurrentLt⟩
        have hcurrentMove : moveAt? index = some currentFirst := by
          simp only [moveAt?]
          rw [dif_pos hcurrentLt]
        by_cases hcurrentAccept : Accepts (M.pinFirst currentFirst)
            (M.pinFirstBootCfg (leftBoundedTape original))
        · exact accepts_sequentialUnion_rewind_of_accepts_pinFirst
            M original index currentFirst current hcontents
              hcurrentMove hcurrentAccept
        · obtain ⟨advanced, restored, hadvanced, hrestored, hreach⟩ :=
            exists_reaches_sequentialUnion_next_of_not_accepts_pinFirst
              M hacyclic hn original index currentFirst current hcontents
                hcurrentMove hcurrentAccept
          have hadvancedLe : advanced.val ≤ target.val := by omega
          have hcloser : target.val - advanced.val < distance := by omega
          obtain ⟨acceptCfg, hacceptReach, hfinal⟩ :=
            ih (target.val - advanced.val) hcloser advanced hadvancedLe
              restored hrestored rfl
          exact ⟨acceptCfg, hreach.trans hacceptReach, hfinal⟩

omit [DecidableEq Λ] in
/-- Starting from trial zero, every accepting pinned branch is eventually tried. -/
public theorem accepts_sequentialUnion_rewind_zero_of_exists_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original)
    (haccept : ∃ first : Move (EndAlpha T Γ) Λ,
      Accepts (M.pinFirst first)
        (M.pinFirstBootCfg (leftBoundedTape original))) :
    Accepts (sequentialUnion M)
      ⟨.rewind 0, packedTape original current⟩ := by
  obtain ⟨first, hfirst⟩ := haccept
  let target : TrialIndex (EndAlpha T Γ) Λ :=
    ⟨(Fintype.equivFin (Move (EndAlpha T Γ) Λ) first).val, by
      have hlt := (Fintype.equivFin (Move (EndAlpha T Γ) Λ) first).isLt
      omega⟩
  have htarget : moveAt? target = some first := by
    exact moveAt?_equivFin first
  exact accepts_sequentialUnion_rewind_of_later_pinFirst
    M hacyclic hn original target first htarget hfirst 0 (by simp)
      current hcontents

/-- The extra scheduler index after every actual move has been tried. -/
@[expose]
public def terminalTrialIndex : TrialIndex (EndAlpha T Γ) Λ :=
  ⟨Fintype.card (Move (EndAlpha T Γ) Λ), Nat.lt_succ_self _⟩

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ] in
@[simp]
public theorem terminalTrialIndex_val :
    (terminalTrialIndex : TrialIndex (EndAlpha T Γ) Λ).val =
      Fintype.card (Move (EndAlpha T Γ) Λ) := rfl

omit [DecidableEq T] [DecidableEq Γ] [DecidableEq Λ] in
/-- The terminal scheduler index has no assigned move. -/
public theorem moveAt?_terminalTrialIndex :
    moveAt? (terminalTrialIndex : TrialIndex (EndAlpha T Γ) Λ) = none := by
  simp [moveAt?, terminalTrialIndex]

omit [DecidableEq Λ] in
/-- If every pinned branch rejects, repeated reset macros exhaust all trials and leave the head
at the left endpoint of a restored tape. -/
public theorem exists_reaches_sequentialUnion_terminal_of_forall_not_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (index : TrialIndex (EndAlpha T Γ) Λ)
    (hle : index.val ≤ Fintype.card (Move (EndAlpha T Γ) Λ))
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original)
    (hreject : ∀ first : Move (EndAlpha T Γ) Λ,
      ¬ Accepts (M.pinFirst first)
        (M.pinFirstBootCfg (leftBoundedTape original))) :
    ∃ stopped : DLBA.BoundedTape (EndAlpha T Γ) n,
      stopped.contents = original ∧
      stopped.head.val = 0 ∧
      Reaches (sequentialUnion M)
        ⟨.rewind index, packedTape original current⟩
        ⟨.rewind terminalTrialIndex, packedTape original stopped⟩ := by
  generalize hdistance :
    Fintype.card (Move (EndAlpha T Γ) Λ) - index.val = distance
  induction distance using Nat.strong_induction_on generalizing index current with
  | h distance ih =>
      by_cases hterminal :
          index.val = Fintype.card (Move (EndAlpha T Γ) Λ)
      · have hindex : index = terminalTrialIndex := Fin.ext hterminal
        subst index
        obtain ⟨stopped, hstoppedContents, hstoppedHead, hrewind⟩ :=
          exists_reaches_sequentialUnion_rewind_boundary
            M original terminalTrialIndex current
        exact ⟨stopped, hstoppedContents.trans hcontents, hstoppedHead, hrewind⟩
      · have hindexLt :
            index.val < Fintype.card (Move (EndAlpha T Γ) Λ) := by omega
        let first : Move (EndAlpha T Γ) Λ :=
          (Fintype.equivFin (Move (EndAlpha T Γ) Λ)).symm
            ⟨index.val, hindexLt⟩
        have hmove : moveAt? index = some first := by
          simp only [moveAt?]
          rw [dif_pos hindexLt]
        obtain ⟨advanced, restored, hadvanced, hrestored, hadvanceReach⟩ :=
          exists_reaches_sequentialUnion_next_of_not_accepts_pinFirst
            M hacyclic hn original index first current hcontents hmove (hreject first)
        have hadvancedLe :
            advanced.val ≤ Fintype.card (Move (EndAlpha T Γ) Λ) := by omega
        have hcloser :
            Fintype.card (Move (EndAlpha T Γ) Λ) - advanced.val < distance := by
          omega
        obtain ⟨stopped, hstoppedContents, hstoppedHead, hterminalReach⟩ :=
          ih (Fintype.card (Move (EndAlpha T Γ) Λ) - advanced.val)
            hcloser advanced hadvancedLe restored hrestored rfl
        exact ⟨stopped, hstoppedContents, hstoppedHead,
          hadvanceReach.trans hterminalReach⟩

omit [DecidableEq Λ] in
/-- Trial zero reaches the rejecting terminal checkpoint whenever all pinned branches reject. -/
public theorem exists_reaches_sequentialUnion_terminal_zero_of_forall_not_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original)
    (hreject : ∀ first : Move (EndAlpha T Γ) Λ,
      ¬ Accepts (M.pinFirst first)
        (M.pinFirstBootCfg (leftBoundedTape original))) :
    ∃ stopped : DLBA.BoundedTape (EndAlpha T Γ) n,
      stopped.contents = original ∧
      stopped.head.val = 0 ∧
      Reaches (sequentialUnion M)
        ⟨.rewind 0, packedTape original current⟩
        ⟨.rewind terminalTrialIndex, packedTape original stopped⟩ := by
  exact exists_reaches_sequentialUnion_terminal_of_forall_not_accepts_pinFirst
    M hacyclic hn original 0 (by simp) current hcontents hreject

omit [DecidableEq Λ] in
/-- The sequential union machine is locally functional.  Administrative sweeps have a single
move, and a running trial uses `selectedMove` on the already functional pinned machine. -/
public theorem sequentialUnion_functional
    (M : Machine (EndAlpha T Γ) Λ) :
    (sequentialUnion M).Functional := by
  classical
  intro state symbol
  cases state <;>
    simp only [sequentialUnion, sequentialTransition]
  all_goals repeat' split
  all_goals simp

/-- Local transition functionality induces right-uniqueness of the configuration step
relation, including at clamped tape boundaries. -/
public theorem step_rightUnique_of_functional
    {A Q : Type*} (M : Machine A Q) (hfunctional : M.Functional) {n : ℕ} :
    Relator.RightUnique (@Step A Q n M) := by
  intro source left right hleft hright
  rcases hleft with ⟨leftState, leftWrite, leftDir, hleftEnabled, rfl⟩
  rcases hright with ⟨rightState, rightWrite, rightDir, hrightEnabled, rfl⟩
  have hmove : (leftState, leftWrite, leftDir) =
      (rightState, rightWrite, rightDir) :=
    hfunctional source.state source.tape.read hleftEnabled hrightEnabled
  cases hmove
  rfl

/-- A path starting at a configuration with no outgoing edge is necessarily reflexive. -/
public theorem reaches_eq_of_sink
    {A Q : Type*} (M : Machine A Q) {n : ℕ}
    {source target : DLBA.Cfg A Q n}
    (hsink : ∀ next, ¬ Step M source next)
    (hreach : Reaches M source target) :
    source = target := by
  rcases ReflTransGen.cases_head hreach with heq | ⟨middle, hstep, _⟩
  · exact heq
  · exact (hsink middle hstep).elim

omit [DecidableEq Λ] in
/-- An accepting sequential configuration is a sink: the running transition checks acceptance
before consulting the selected pinned move. -/
public theorem sequentialUnion_sink_of_accepting
    (M : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    (cfg : DLBA.Cfg (BackupAlpha T Γ) (SequentialState T Γ Λ) n)
    (haccept : (sequentialUnion M).accept cfg.state = true) :
    ∀ next, ¬ Step (sequentialUnion M) cfg next := by
  rcases cfg with ⟨state, tape⟩
  cases state with
  | initializeLeft => simp [sequentialUnion] at haccept
  | initializeRight => simp [sequentialUnion] at haccept
  | rewind next => simp [sequentialUnion] at haccept
  | resetLeft next => simp [sequentialUnion] at haccept
  | restoreRight next => simp [sequentialUnion] at haccept
  | run next first pinState =>
      intro target hstep
      rcases hstep with ⟨targetState, written, direction, henabled, _⟩
      simp only [sequentialUnion] at haccept
      simp only [sequentialUnion, sequentialTransition] at henabled
      cases hcell : unpack tape.read with
      | none =>
          rw [hcell] at henabled
          simp at henabled
      | some cell =>
          rw [hcell] at henabled
          change (targetState, written, direction) ∈
            (if (M.pinFirst first).accept pinState = true then ∅ else _) at henabled
          rw [if_pos haccept] at henabled
          simp at henabled

omit [DecidableEq Λ] in
/-- At the exhausted index and the left endpoint, rewind has no outgoing step. -/
public theorem sequentialUnion_terminal_sink
    (M : Machine (EndAlpha T Γ) Λ)
    {n : ℕ} (original : Fin (n + 1) → EndAlpha T Γ)
    (stopped : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hhead : stopped.head.val = 0) :
    ∀ target, ¬ Step (sequentialUnion M)
      ⟨.rewind terminalTrialIndex, packedTape original stopped⟩ target := by
  intro target hstep
  rcases hstep with ⟨targetState, written, direction, henabled, _⟩
  have hleft : boundaryAt n stopped.head = .left :=
    boundaryAt_eq_left_iff.mpr hhead
  simp only [sequentialUnion, sequentialTransition,
    unpack_packedTape_read] at henabled
  rw [if_pos hleft] at henabled
  split at henabled
  · simp at henabled
  · next first hmove =>
    rw [moveAt?_terminalTrialIndex] at hmove
    simp at hmove

omit [DecidableEq Λ] in
/-- On every restored positive-width tape, the sequential scheduler accepts exactly when one of
the finitely many pinned machines accepts.  The reverse direction uses acyclicity only to ensure
that each rejected functional trial reaches its reset macro. -/
public theorem accepts_sequentialUnion_rewind_zero_iff_exists_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (hacyclic : M.ConfigurationAcyclic)
    {n : ℕ} (hn : 0 < n)
    (original : Fin (n + 1) → EndAlpha T Γ)
    (current : DLBA.BoundedTape (EndAlpha T Γ) n)
    (hcontents : current.contents = original) :
    Accepts (sequentialUnion M)
        ⟨.rewind 0, packedTape original current⟩ ↔
      ∃ first : Move (EndAlpha T Γ) Λ,
        Accepts (M.pinFirst first)
          (M.pinFirstBootCfg (leftBoundedTape original)) := by
  constructor
  · intro hsequential
    by_contra hnone
    have hreject : ∀ first : Move (EndAlpha T Γ) Λ,
        ¬ Accepts (M.pinFirst first)
          (M.pinFirstBootCfg (leftBoundedTape original)) := by
      simpa only [not_exists] using hnone
    obtain ⟨stopped, _, hstoppedHead, hterminal⟩ :=
      exists_reaches_sequentialUnion_terminal_zero_of_forall_not_accepts_pinFirst
        M hacyclic hn original current hcontents hreject
    obtain ⟨acceptCfg, hacceptReach, hfinal⟩ := hsequential
    have hrightUnique :
        Relator.RightUnique (@Step _ _ n (sequentialUnion M)) :=
      step_rightUnique_of_functional (n := n) (sequentialUnion M)
        (sequentialUnion_functional M)
    rcases ReflTransGen.total_of_right_unique
        hrightUnique hterminal hacceptReach with
      hterminalAccept | hacceptTerminal
    · have heq := reaches_eq_of_sink (sequentialUnion M)
          (sequentialUnion_terminal_sink M original stopped hstoppedHead)
          hterminalAccept
      rw [← heq] at hfinal
      simp [sequentialUnion] at hfinal
    · have heq := reaches_eq_of_sink (sequentialUnion M)
          (sequentialUnion_sink_of_accepting M acceptCfg hfinal)
          hacceptTerminal
      rw [heq] at hfinal
      simp [sequentialUnion] at hfinal
  · exact accepts_sequentialUnion_rewind_zero_of_exists_accepts_pinFirst
      M hacyclic hn original current hcontents

end LBA.MachineTwoMatchings

end
