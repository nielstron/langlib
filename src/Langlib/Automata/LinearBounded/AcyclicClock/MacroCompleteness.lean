module

public import Langlib.Automata.LinearBounded.AcyclicClock.ReadyEncoding
import Mathlib.Tactic

@[expose]
public section

/-!
# Operational completeness of one clocked source macro

This file gives exact sweep invariants for the concrete compiler in `Construction`.

The completed checkpoint is not completely transient-free: the final `findMark` sweep leaves
`scan = true` precisely on cells strictly left of the simulated head.  That trail is a necessary
one-shot guard against physical-head clamping and is erased by the normalization sweep of the
next macro.  Accordingly, the end-to-end theorem targets `checkpointCfg`, while `readyCfg` is the
clean representation accepted as the first macro's input.
-/

open Classical Relation

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

private theorem cfg_eq {A Q : Type*} {n : ℕ}
    {s s' : Q} {contents contents' : Fin (n + 1) → A}
    {head head' : Fin (n + 1)}
    (hs : s = s') (hc : contents = contents') (hh : head = head') :
    (⟨s, ⟨contents, head⟩⟩ : DLBA.Cfg A Q n) =
      ⟨s', ⟨contents', head'⟩⟩ := by
  subst s'
  subst contents'
  subst head'
  rfl

/-! ## Source write, move, and mark installation -/

/-- The intermediate tape after the source transition has been written and the physical head has
moved, but before the new simulated-head mark is installed. -/
private def unmarkedCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape digits index with mark := false }

private def unmarkedTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (unmarkedCell tape digits index), tape.head⟩

private theorem ready_write_move_eq_unmarkedTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (written : SourceAlpha T Γ) (direction : DLBA.Dir) :
    ((readyTape tape digits).write
        (workSymbol
          { (readyCell tape digits tape.head).clearTransient with
            src := written
            mark := false })).moveHead direction =
      unmarkedTape ((tape.write written).moveHead direction) digits := by
  cases tape with
  | mk contents head =>
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write, readyTape,
        unmarkedTape]
      congr 1
      funext index
      rw [Function.update_apply]
      by_cases hindex : index = head
      · subst index
        simp [unmarkedCell, readyCell, WorkCell.clearTransient]
      · simp [hindex, unmarkedCell, readyCell]

private theorem step_mark_unmarked
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    LBA.Step (machine M)
      ⟨.mark source, unmarkedTape tape digits⟩
      ⟨.seek source, readyTape tape digits⟩ := by
  let cell := unmarkedCell tape digits tape.head
  refine ⟨.seek source,
    workSymbol { cell.clearTransient with mark := true }, .stay, ?_, ?_⟩
  · change
      (.seek source, workSymbol { cell.clearTransient with mark := true }, .stay) ∈
        transition M (.mark source) (workSymbol cell)
    rw [transition_mark_work]
    simp
  · apply (cfg_eq rfl
      (show
        Function.update (unmarkedTape tape digits).contents
            (unmarkedTape tape digits).head
            (workSymbol { cell.clearTransient with mark := true }) =
          (readyTape tape digits).contents by
        funext index
        rw [Function.update_apply]
        by_cases hindex : index = tape.head
        · subst index
          simp [cell, unmarkedCell, readyCell, unmarkedTape, readyTape,
            WorkCell.clearTransient]
        · simp [hindex, unmarkedCell, readyCell, unmarkedTape, readyTape])
      rfl).symm

/-- Every source-machine step is simulated through the exact write/move/mark prefix of the target
macro.  At the endpoint the source successor and the original clock row are represented cleanly,
and the target is ready to begin its guarded left sweep. -/
public theorem reaches_seek_of_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (hstep : LBA.Step M cfg cfg') :
    LBA.Reaches (machine M)
      (readyCfg cfg digits)
      ⟨.seek cfg'.state, readyTape cfg'.tape digits⟩ := by
  rcases hstep with ⟨target, written, direction, hmove, rfl⟩
  have hready :=
    step_ready_half_of_source_move M cfg.state (readyTape cfg.tape digits)
      (readyCell cfg.tape digits cfg.tape.head) rfl
      (by simp [readyCell]) hmove
  rw [ready_write_move_eq_unmarkedTape] at hready
  exact (ReflTransGen.single hready).tail
    (step_mark_unmarked M target ((cfg.tape.write written).moveHead direction) digits)

/-- Clear both harmless Ready-trail tracks at one physical cell. -/
public def ReadyTrails.clearAt
    {n : ℕ} (trails : ReadyTrails n) (cleared : Fin (n + 1)) :
    ReadyTrails n where
  post index := if index = cleared then false else trails.post index
  scan index := if index = cleared then false else trails.scan index

/-- Exact target tape immediately after `ready` has written one source move and physically moved,
but before the new simulated-head mark is installed. -/
public def afterReadyTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (written : SourceAlpha T Γ) (direction : DLBA.Dir) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ((checkpointTape tape digits trails).write
      (workSymbol
        { (checkpointCell tape digits trails tape.head).clearTransient with
          src := written
          mark := false })).moveHead direction

/-- Exact `.mark` configuration produced by the first target step of a source macro. -/
public def afterReadyCfg
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (target : Λ) (written : SourceAlpha T Γ) (direction : DLBA.Dir) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  ⟨.mark target, afterReadyTape cfg.tape digits trails written direction⟩

private def unmarkedCheckpointCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { checkpointCell tape digits trails index with mark := false }

private def unmarkedCheckpointTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (unmarkedCheckpointCell tape digits trails index), tape.head⟩

private theorem checkpoint_write_move_eq_unmarkedTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (written : SourceAlpha T Γ) (direction : DLBA.Dir) :
    ((checkpointTape tape digits trails).write
        (workSymbol
          { (checkpointCell tape digits trails tape.head).clearTransient with
            src := written
            mark := false })).moveHead direction =
      unmarkedCheckpointTape ((tape.write written).moveHead direction) digits
        (trails.clearAt tape.head) := by
  cases tape with
  | mk contents head =>
      simp only [DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
        checkpointTape, unmarkedCheckpointTape]
      congr 1
      funext index
      rw [Function.update_apply]
      by_cases hindex : index = head
      · subst index
        rw [if_pos rfl]
        apply congrArg workSymbol
        simp [unmarkedCheckpointCell, checkpointCell, ReadyTrails.clearAt,
          readyCell, WorkCell.clearTransient]
      · rw [if_neg hindex]
        apply congrArg workSymbol
        simp [unmarkedCheckpointCell, checkpointCell, ReadyTrails.clearAt,
          readyCell, hindex]

private theorem step_mark_unmarked_checkpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    LBA.Step (machine M)
      ⟨.mark source, unmarkedCheckpointTape tape digits trails⟩
      ⟨.seek source, checkpointTape tape digits (trails.clearAt tape.head)⟩ := by
  let cell := unmarkedCheckpointCell tape digits trails tape.head
  refine ⟨.seek source,
    workSymbol { cell.clearTransient with mark := true }, .stay, ?_, ?_⟩
  · change
      (.seek source, workSymbol { cell.clearTransient with mark := true }, .stay) ∈
        transition M (.mark source) (workSymbol cell)
    rw [transition_mark_work]
    simp
  · apply (cfg_eq rfl ?_ rfl).symm
    change
      Function.update (unmarkedCheckpointTape tape digits trails).contents
          (unmarkedCheckpointTape tape digits trails).head
          (workSymbol { cell.clearTransient with mark := true }) =
        (checkpointTape tape digits (trails.clearAt tape.head)).contents
    funext index
    rw [Function.update_apply]
    by_cases hindex : index = tape.head
    · subst index
      rw [if_pos (by simp [unmarkedCheckpointTape])]
      apply congrArg workSymbol
      simp [cell, unmarkedCheckpointCell, checkpointCell,
        ReadyTrails.clearAt, readyCell, WorkCell.clearTransient]
    · rw [if_neg (by simpa [unmarkedCheckpointTape] using hindex)]
      apply congrArg workSymbol
      simp [unmarkedCheckpointCell, checkpointCell, ReadyTrails.clearAt,
        readyCell, hindex]

/-- The write/move/mark prefix works from every operational checkpoint, independently of the
harmless `post` and `scan` trails.  It clears those trails at the old and new simulated-head cells
and preserves them elsewhere until normalization. -/
public theorem reaches_seek_checkpoint_of_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (hstep : LBA.Step M cfg cfg') :
    LBA.Reaches (machine M)
      (checkpointCfg cfg digits trails)
      ⟨.seek cfg'.state,
        checkpointTape cfg'.tape digits
          ((trails.clearAt cfg.tape.head).clearAt cfg'.tape.head)⟩ := by
  rcases hstep with ⟨target, written, direction, hmove, rfl⟩
  have hready :=
    step_ready_half_of_source_move M cfg.state
      (checkpointTape cfg.tape digits trails)
      (checkpointCell cfg.tape digits trails cfg.tape.head) rfl
      (by simp) hmove
  rw [checkpoint_write_move_eq_unmarkedTape] at hready
  exact (ReflTransGen.single hready).tail
    (step_mark_unmarked_checkpoint M target
      ((cfg.tape.write written).moveHead direction) digits
      (trails.clearAt cfg.tape.head))

/-! ## Guarded seek sweep -/

private theorem transition_seek_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.seek source) (workSymbol cell) =
      if cell.left then
        {(.cleanR source, workSymbol cell, .stay)}
      else if cell.seek then ∅
      else
        {(.seek source, workSymbol { cell with seek := true }, .left)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

/-- At a leftward seek position `current`, precisely the already crossed interval strictly to its
right and at most the original simulated head carries the seek guard. -/
private def seekCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { checkpointCell tape digits trails index with
    seek := decide (current.val < index.val ∧ index.val ≤ tape.head.val) }

private def seekTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current : Fin (n + 1)) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (seekCell tape digits trails current index), current⟩

private theorem seekTape_at_source_head
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    seekTape tape digits trails tape.head =
      checkpointTape tape digits trails := by
  cases tape with
  | mk contents head =>
      simp only [seekTape, checkpointTape]
      congr 1
      funext index
      apply congrArg workSymbol
      have hfalse : ¬(head.val < index.val ∧ index.val ≤ head.val) := by omega
      unfold seekCell
      rw [show decide (head.val < index.val ∧ index.val ≤ head.val) = false by
        exact (Bool.decide_false_iff _).2 hfalse]
      rfl

private theorem seek_update_left
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current : Fin (n + 1)) (hpos : 0 < current.val)
    (hle : current.val ≤ tape.head.val) :
    Function.update (seekTape tape digits trails current).contents current
        (workSymbol
          { seekCell tape digits trails current current with seek := true }) =
      (seekTape tape digits trails
        ⟨current.val - 1, by omega⟩).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = current
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [seekCell, checkpointCell, hpos, hle]
  · rw [if_neg heq]
    have hval : index.val ≠ current.val := fun h => heq (Fin.ext h)
    change
      workSymbol (seekCell tape digits trails current index) =
        workSymbol
          (seekCell tape digits trails
            ⟨current.val - 1, by omega⟩ index)
    apply congrArg workSymbol
    unfold seekCell
    exact congrArg
      (fun flag =>
        { checkpointCell tape digits trails index with seek := flag })
      (Bool.decide_congr
        (p := current.val < index.val ∧ index.val ≤ tape.head.val)
        (q := current.val - 1 < index.val ∧ index.val ≤ tape.head.val) (by
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨by omega, h₂⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨by omega, h₂⟩))

private theorem seek_step_left
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current : Fin (n + 1)) (hpos : 0 < current.val)
    (hle : current.val ≤ tape.head.val) :
    LBA.Step (machine M)
      ⟨.seek source, seekTape tape digits trails current⟩
      ⟨.seek source,
        seekTape tape digits trails ⟨current.val - 1, by omega⟩⟩ := by
  let cell := seekCell tape digits trails current current
  refine ⟨.seek source, workSymbol { cell with seek := true }, .left, ?_, ?_⟩
  · change
      (.seek source, workSymbol { cell with seek := true }, .left) ∈
        transition M (.seek source) (workSymbol cell)
    rw [transition_seek_work, if_neg, if_neg]
    · simp
    · simp [cell, seekCell, checkpointCell]
    · simp [cell, seekCell, checkpointCell, readyCell, hpos.ne']
  · symm
    apply cfg_eq rfl
    · exact seek_update_left tape digits trails current hpos hle
    · apply Fin.ext
      simp [seekTape, DLBA.BoundedTape.write, hpos]

private theorem seek_step_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    LBA.Step (machine M)
      ⟨.seek source, seekTape tape digits trails ⟨0, by omega⟩⟩
      ⟨.cleanR source, seekTape tape digits trails ⟨0, by omega⟩⟩ := by
  let zero : Fin (n + 1) := ⟨0, by omega⟩
  let cell := seekCell tape digits trails zero zero
  refine ⟨.cleanR source, workSymbol cell, .stay, ?_, ?_⟩
  · change
      (.cleanR source, workSymbol cell, .stay) ∈
        transition M (.seek source) (workSymbol cell)
    rw [transition_seek_work, if_pos]
    · simp
    · simp [cell, seekCell, checkpointCell, readyCell, zero]
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead, seekTape,
      zero, cell, Function.update_eq_self]

private theorem seek_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    ∀ current : Fin (n + 1), current.val ≤ tape.head.val →
      LBA.Reaches (machine M)
        ⟨.seek source, seekTape tape digits trails current⟩
        ⟨.cleanR source, seekTape tape digits trails ⟨0, by omega⟩⟩ := by
  suffices H :
      ∀ value, ∀ current : Fin (n + 1), current.val = value →
        current.val ≤ tape.head.val →
        LBA.Reaches (machine M)
          ⟨.seek source, seekTape tape digits trails current⟩
          ⟨.cleanR source, seekTape tape digits trails ⟨0, by omega⟩⟩ from
    fun current hle => H current.val current rfl hle
  intro value
  induction value with
  | zero =>
      intro current hvalue hle
      have hcurrent : current = ⟨0, by omega⟩ := Fin.ext hvalue
      rw [hcurrent]
      exact .single (seek_step_zero M source tape digits trails)
  | succ value ih =>
      intro current hvalue hle
      have hpos : 0 < current.val := by omega
      let previous : Fin (n + 1) := ⟨current.val - 1, by omega⟩
      have hprevious : previous.val = value := by
        simp [previous]
        omega
      exact ReflTransGen.head
        (seek_step_left M source tape digits trails current hpos hle)
        (ih previous hprevious (by simp [previous]; omega))

/-! ## Rightward and leftward normalization sweeps -/

private def normalizedCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  (readyCell tape digits index).normalizedRight

/-- During `cleanR`, cells strictly left of `current` have been normalized; cells at or right of
it still carry the seek trail. -/
private def cleanRCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  if index.val < current.val then normalizedCell tape digits index
  else seekCell tape digits trails ⟨0, by omega⟩ index

private def cleanRTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current : Fin (n + 1)) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (cleanRCell tape digits trails current index), current⟩

private def normalizedTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (normalizedCell tape digits index), Fin.last n⟩

private theorem cleanRTape_zero_eq_seekTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    cleanRTape tape digits trails ⟨0, by omega⟩ =
      seekTape tape digits trails ⟨0, by omega⟩ := by
  rfl

private theorem cleanR_update_right
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current : Fin (n + 1)) (hlt : current.val < n) :
    Function.update (cleanRTape tape digits trails current).contents current
        (workSymbol
          (cleanRCell tape digits trails current current).normalizedRight) =
      (cleanRTape tape digits trails
        ⟨current.val + 1, by omega⟩).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = current
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [cleanRCell, normalizedCell, seekCell, checkpointCell, readyCell,
      WorkCell.normalizedRight, WorkCell.clearTransient]
  · rw [if_neg heq]
    have hval : index.val ≠ current.val := fun h => heq (Fin.ext h)
    change
      workSymbol (cleanRCell tape digits trails current index) =
        workSymbol
          (cleanRCell tape digits trails
            ⟨current.val + 1, by omega⟩ index)
    apply congrArg workSymbol
    simp only [cleanRCell]
    by_cases hbefore : index.val < current.val
    · rw [if_pos hbefore, if_pos (by omega)]
    · rw [if_neg hbefore]
      rw [if_neg (by omega)]

private theorem cleanR_step_right
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (current : Fin (n + 1)) (hlt : current.val < n) :
    LBA.Step (machine M)
      ⟨.cleanR source, cleanRTape tape digits trails current⟩
      ⟨.cleanR source,
        cleanRTape tape digits trails ⟨current.val + 1, by omega⟩⟩ := by
  let cell := cleanRCell tape digits trails current current
  refine ⟨.cleanR source, workSymbol cell.normalizedRight, .right, ?_, ?_⟩
  · change
      (.cleanR source, workSymbol cell.normalizedRight, .right) ∈
        transition M (.cleanR source) (workSymbol cell)
    rw [transition_cleanR_work, if_neg, if_neg]
    · simp
    · simp [cell, cleanRCell, seekCell, checkpointCell, readyCell, hlt.ne]
    · simp [cell, cleanRCell, seekCell, checkpointCell, readyCell]
  · symm
    apply cfg_eq rfl
    · exact cleanR_update_right tape digits trails current hlt
    · apply Fin.ext
      simp [cleanRTape, DLBA.BoundedTape.write, hlt]

private theorem cleanR_update_last
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    Function.update
        (cleanRTape tape digits trails (Fin.last n)).contents (Fin.last n)
        (workSymbol
          (cleanRCell tape digits trails
            (Fin.last n) (Fin.last n)).normalizedRight) =
      (normalizedTape tape digits).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = Fin.last n
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [cleanRCell, normalizedCell, seekCell, checkpointCell, readyCell,
      WorkCell.normalizedRight, WorkCell.clearTransient]
  · rw [if_neg heq]
    have hlt : index.val < n := by
      have hle : index.val ≤ n := by omega
      have hne : index.val ≠ n := by
        intro h
        exact heq (Fin.ext (by simpa using h))
      omega
    change
      workSymbol (cleanRCell tape digits trails (Fin.last n) index) =
        workSymbol (normalizedCell tape digits index)
    simp [cleanRCell, hlt]

private theorem cleanR_step_last
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    LBA.Step (machine M)
      ⟨.cleanR source, cleanRTape tape digits trails (Fin.last n)⟩
      ⟨.cleanL source, normalizedTape tape digits⟩ := by
  let last := Fin.last n
  let cell := cleanRCell tape digits trails last last
  refine ⟨.cleanL source, workSymbol cell.normalizedRight, .stay, ?_, ?_⟩
  · change
      (.cleanL source, workSymbol cell.normalizedRight, .stay) ∈
        transition M (.cleanR source) (workSymbol cell)
    rw [transition_cleanR_work, if_neg, if_pos]
    · simp
    · simp [cell, cleanRCell, seekCell, checkpointCell, readyCell, last]
    · simp [cell, cleanRCell, seekCell, checkpointCell, readyCell]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    exact (cfg_eq rfl (cleanR_update_last tape digits trails) rfl).symm

private theorem cleanR_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    ∀ current : Fin (n + 1),
      LBA.Reaches (machine M)
        ⟨.cleanR source, cleanRTape tape digits trails current⟩
        ⟨.cleanL source, normalizedTape tape digits⟩ := by
  suffices H :
      ∀ distance, ∀ current : Fin (n + 1),
        n - current.val = distance →
        LBA.Reaches (machine M)
          ⟨.cleanR source, cleanRTape tape digits trails current⟩
          ⟨.cleanL source, normalizedTape tape digits⟩ from
    fun current => H (n - current.val) current rfl
  intro distance
  induction distance with
  | zero =>
      intro current hdistance
      have hlast : current = Fin.last n := by
        apply Fin.ext
        simp
        have := current.isLt
        omega
      subst current
      exact .single (cleanR_step_last M source tape digits trails)
  | succ distance ih =>
      intro current hdistance
      have hlt : current.val < n := by
        have := current.isLt
        omega
      let next : Fin (n + 1) := ⟨current.val + 1, by omega⟩
      exact ReflTransGen.head
        (cleanR_step_right M source tape digits trails current hlt)
        (ih next (by simp [next]; omega))

private def cleanLCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape digits index with
    norm := decide (index.val ≤ current.val) }

private def cleanLTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (cleanLCell tape digits current index), current⟩

private theorem cleanLTape_last_eq_normalizedTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    cleanLTape tape digits (Fin.last n) = normalizedTape tape digits := by
  simp only [cleanLTape, normalizedTape]
  congr 1
  funext index
  apply congrArg workSymbol
  have hle : index.val ≤ n := by
    have := index.isLt
    omega
  simp [cleanLCell, normalizedCell, WorkCell.normalizedRight,
    WorkCell.clearTransient, readyCell, hle]

private theorem cleanL_update_left
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hpos : 0 < current.val) :
    Function.update (cleanLTape tape digits current).contents current
        (workSymbol (cleanLCell tape digits current current).clearTransient) =
      (cleanLTape tape digits ⟨current.val - 1, by omega⟩).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = current
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [cleanLCell, readyCell, WorkCell.clearTransient, hpos]
  · rw [if_neg heq]
    have hval : index.val ≠ current.val := fun h => heq (Fin.ext h)
    change
      workSymbol (cleanLCell tape digits current index) =
        workSymbol
          (cleanLCell tape digits ⟨current.val - 1, by omega⟩ index)
    apply congrArg workSymbol
    unfold cleanLCell
    exact congrArg
      (fun flag => { readyCell tape digits index with norm := flag })
      (Bool.decide_congr
        (p := index.val ≤ current.val)
        (q := index.val ≤ current.val - 1) (by
        constructor <;> intro h
        · omega
        · omega))

private theorem cleanL_step_left
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hpos : 0 < current.val) :
    LBA.Step (machine M)
      ⟨.cleanL source, cleanLTape tape digits current⟩
      ⟨.cleanL source,
        cleanLTape tape digits ⟨current.val - 1, by omega⟩⟩ := by
  let cell := cleanLCell tape digits current current
  refine ⟨.cleanL source, workSymbol cell.clearTransient, .left, ?_, ?_⟩
  · change
      (.cleanL source, workSymbol cell.clearTransient, .left) ∈
        transition M (.cleanL source) (workSymbol cell)
    rw [transition_cleanL_work, if_neg, if_pos]
    · simp
    · simp [cell, cleanLCell]
    · simp [cell, cleanLCell, readyCell, hpos.ne']
  · symm
    apply cfg_eq rfl
    · exact cleanL_update_left tape digits current hpos
    · apply Fin.ext
      simp [cleanLTape, DLBA.BoundedTape.write, hpos]

public def leftHeadReadyTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨(readyTape tape digits).contents, ⟨0, by omega⟩⟩

private theorem cleanL_step_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    LBA.Step (machine M)
      ⟨.cleanL source, cleanLTape tape digits ⟨0, by omega⟩⟩
      ⟨.carry source, leftHeadReadyTape tape digits⟩ := by
  let zero : Fin (n + 1) := ⟨0, by omega⟩
  let cell := cleanLCell tape digits zero zero
  refine ⟨.carry source, workSymbol cell.clearTransient, .stay, ?_, ?_⟩
  · change
      (.carry source, workSymbol cell.clearTransient, .stay) ∈
        transition M (.cleanL source) (workSymbol cell)
    rw [transition_cleanL_work, if_pos, if_pos]
    · simp
    · simp [cell, cleanLCell]
    · simp [cell, cleanLCell, readyCell, zero]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    apply (cfg_eq rfl ?_ rfl).symm
    funext index
    rw [Function.update_apply]
    by_cases heq : index = zero
    · subst index
      rw [if_pos (by simp [cleanLTape, zero])]
      simp [cell, cleanLCell, readyCell, readyTape,
        WorkCell.clearTransient, zero]
    · rw [if_neg (by simpa [cleanLTape] using heq)]
      have hval : index.val ≠ 0 := by
        intro h
        exact heq (Fin.ext (by simpa [zero] using h))
      change
        workSymbol (cleanLCell tape digits zero index) =
          workSymbol (readyCell tape digits index)
      apply congrArg workSymbol
      unfold cleanLCell
      rw [show decide (index.val ≤ zero.val) = false by
        simp [zero, hval]]
      rfl

private theorem cleanL_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    ∀ current : Fin (n + 1),
      LBA.Reaches (machine M)
        ⟨.cleanL source, cleanLTape tape digits current⟩
        ⟨.carry source, leftHeadReadyTape tape digits⟩ := by
  suffices H :
      ∀ value, ∀ current : Fin (n + 1), current.val = value →
        LBA.Reaches (machine M)
          ⟨.cleanL source, cleanLTape tape digits current⟩
          ⟨.carry source, leftHeadReadyTape tape digits⟩ from
    fun current => H current.val current rfl
  intro value
  induction value with
  | zero =>
      intro current hvalue
      have hcurrent : current = ⟨0, by omega⟩ := Fin.ext hvalue
      rw [hcurrent]
      exact .single (cleanL_step_zero M source tape digits)
  | succ value ih =>
      intro current hvalue
      have hpos : 0 < current.val := by omega
      let previous : Fin (n + 1) := ⟨current.val - 1, by omega⟩
      have hprevious : previous.val = value := by
        simp [previous]
        omega
      exact ReflTransGen.head
        (cleanL_step_left M source tape digits current hpos)
        (ih previous hprevious)

/-- The complete seek/normalization prefix is total for arbitrary harmless Ready trails.  It
preserves all source data and clock digits, erases both trail tracks, and positions the physical
head at the least-significant digit. -/
public theorem reaches_carry_of_seek_checkpoint
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    LBA.Reaches (machine M)
      ⟨.seek source, checkpointTape tape digits trails⟩
      ⟨.carry source, leftHeadReadyTape tape digits⟩ := by
  rw [← seekTape_at_source_head tape digits trails]
  exact
    (seek_sweep M source tape digits trails tape.head (Nat.le_refl _)).trans
      ((cleanR_sweep M source tape digits trails ⟨0, by omega⟩).trans
        ((show normalizedTape tape digits =
              cleanLTape tape digits (Fin.last n) by
            symm
            exact cleanLTape_last_eq_normalizedTape tape digits) ▸
          cleanL_sweep M source tape digits (Fin.last n)))

/-- Every source step reaches the clean carry-entry configuration from every operational Ready
checkpoint.  This is the complete write/move/mark/seek/normalize prefix of one source macro. -/
public theorem reaches_carry_checkpoint_of_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (hstep : LBA.Step M cfg cfg') :
    LBA.Reaches (machine M)
      (checkpointCfg cfg digits trails)
      ⟨.carry cfg'.state, leftHeadReadyTape cfg'.tape digits⟩ := by
  exact (reaches_seek_checkpoint_of_step M digits trails hstep).trans
    (reaches_carry_of_seek_checkpoint M cfg'.state cfg'.tape digits
      ((trails.clearAt cfg.tape.head).clearAt cfg'.tape.head))

/-! ## Nonoverflowing clock carry -/

/-- Clock digits after a carry stops at `stop`: lower digits are zero, `stop` contains its local
successor, and higher digits are unchanged. -/
public def incrementedDigitsAt
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    ClockDigit T Γ Λ :=
  if index.val < stop.val then clockZero M
  else if index = stop then next
  else digits index

/-- Canonical fixed-width increment for the compiler's clock row.  The source initial state
supplies the nonempty-state witness needed by the generic digit codec. -/
public def incrementClockRow
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (row : List (ClockDigit T Γ Λ)) :
    List (ClockDigit T Γ Λ) × Bool :=
  letI : Nonempty Λ := ⟨M.initial⟩
  (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).increment row

/-- The pointwise row produced by a first nonmaximal digit is exactly canonical fixed-width
increment, with no overflow. -/
public theorem increment_of_first_next
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    ∀ {n : ℕ} (digits : Fin (n + 1) → ClockDigit T Γ Λ)
      (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ),
      (∀ index : Fin (n + 1), index.val < stop.val →
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits index) = none) →
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits stop) =
        some next →
      incrementClockRow M (List.ofFn digits) =
        (List.ofFn (incrementedDigitsAt M digits stop next), false) := by
  letI : Nonempty Λ := ⟨M.initial⟩
  intro n
  induction n with
  | zero =>
      intro digits stop next hbefore hnext
      have hstop : stop = ⟨0, by omega⟩ := Fin.eq_zero stop
      rw [hstop] at hnext ⊢
      have hnext0 :
          (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits 0) =
            some next := by
        simpa using hnext
      rw [List.ofFn_succ]
      simp [incrementClockRow, RowNumeral.DigitCodec.increment, hnext0,
        incrementedDigitsAt]
  | succ n ih =>
      intro digits stop next hbefore hnext
      rw [List.ofFn_succ]
      by_cases hzero : stop.val = 0
      · have hstop : stop = ⟨0, by omega⟩ := Fin.ext hzero
        rw [hstop] at hnext ⊢
        have hnext0 :
            (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits 0) =
              some next := by
          simpa using hnext
        simp [incrementClockRow, RowNumeral.DigitCodec.increment, hnext0,
          incrementedDigitsAt]
      · let tailDigits : Fin (n + 1) → ClockDigit T Γ Λ :=
          fun index => digits index.succ
        let tailStop : Fin (n + 1) :=
          ⟨stop.val - 1, by
            have := stop.isLt
            omega⟩
        have hhead :
            (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next
                (digits 0) = none := by
          apply hbefore 0
          exact Nat.pos_of_ne_zero hzero
        have hbeforeTail :
            ∀ index : Fin (n + 1), index.val < tailStop.val →
              (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next
                  (tailDigits index) = none := by
          intro index hlt
          apply hbefore index.succ
          simp [tailStop] at hlt ⊢
          omega
        have hnextTail :
            (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next
                (tailDigits tailStop) = some next := by
          have hsucc : tailStop.succ = stop := by
            apply Fin.ext
            simp [tailStop]
            omega
          change
            (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next
                (digits tailStop.succ) = some next
          rw [hsucc]
          exact hnext
        have htail :=
          ih tailDigits tailStop next hbeforeTail hnextTail
        have htailRaw :
            (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).increment
                (List.ofFn tailDigits) =
              (List.ofFn
                (incrementedDigitsAt M tailDigits tailStop next), false) := by
          simpa [incrementClockRow] using htail
        unfold incrementClockRow
        rw [RowNumeral.DigitCodec.increment, hhead]
        change
          ((clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zero ::
              ((clockCodec (T := T) (Γ := Γ) (Λ := Λ)).increment
                (List.ofFn tailDigits)).1,
            ((clockCodec (T := T) (Γ := Γ) (Λ := Λ)).increment
              (List.ofFn tailDigits)).2) =
          (List.ofFn (incrementedDigitsAt M digits stop next), false)
        rw [htailRaw]
        apply Prod.ext
        · rw [← List.ofFn_cons]
          apply List.ofFn_inj.2
          funext index
          refine Fin.cases ?_ (fun tailIndex => ?_) index
          · have hpos : 0 < stop.val := Nat.pos_of_ne_zero hzero
            simp [incrementedDigitsAt, hpos, clockZero]
          · change
              incrementedDigitsAt M tailDigits tailStop next tailIndex =
                incrementedDigitsAt M digits stop next tailIndex.succ
            simp only [incrementedDigitsAt]
            change
              (if tailIndex.val < tailStop.val then clockZero M
                else if tailIndex = tailStop then next
                else digits tailIndex.succ) =
              (if tailIndex.val + 1 < stop.val then clockZero M
                else if tailIndex.succ = stop then next
                else digits tailIndex.succ)
            by_cases hlt : tailIndex.val + 1 < stop.val
            · have hltTail : tailIndex.val < tailStop.val := by
                simp [tailStop]
                omega
              rw [if_pos hltTail, if_pos hlt]
            · have hnotTail : ¬tailIndex.val < tailStop.val := by
                simp [tailStop]
                omega
              rw [if_neg hnotTail, if_neg hlt]
              by_cases heq : tailIndex.val + 1 = stop.val
              · have heqTail : tailIndex = tailStop := by
                  apply Fin.ext
                  simp [tailStop]
                  omega
                rw [if_pos heqTail, if_pos (Fin.ext heq)]
              · have hneTail : tailIndex ≠ tailStop := by
                  intro h
                  have := congrArg Fin.val h
                  simp [tailStop] at this
                  omega
                have hneSucc : tailIndex.succ ≠ stop := by
                  intro h
                  apply heq
                  simpa using congrArg Fin.val h
                rw [if_neg hneTail, if_neg hneSucc]
        · rfl

/-- Every nonoverflowing fixed-width row has a unique operational carry stop: the first digit
with a local successor.  The theorem only needs existence; `hbefore` records its minimality. -/
public theorem exists_first_next_of_not_overflow
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    ∀ {n : ℕ} (digits : Fin (n + 1) → ClockDigit T Γ Λ),
      (incrementClockRow M (List.ofFn digits)).2 = false →
      ∃ (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ),
        (∀ index : Fin (n + 1), index.val < stop.val →
          (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next
            (digits index) = none) ∧
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next
            (digits stop) = some next := by
  letI : Nonempty Λ := ⟨M.initial⟩
  intro n
  induction n with
  | zero =>
      intro digits hno
      have hrow :
          List.ofFn digits = [digits 0] := by
        rw [List.ofFn_succ]
        rfl
      rw [hrow] at hno
      cases hnext :
          (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits 0) with
      | none =>
          simp [incrementClockRow, RowNumeral.DigitCodec.increment, hnext] at hno
      | some next =>
          refine ⟨0, next, ?_, hnext⟩
          intro index hlt
          simp at hlt
  | succ n ih =>
      intro digits hno
      let tailDigits : Fin (n + 1) → ClockDigit T Γ Λ :=
        fun index => digits index.succ
      have hrow :
          List.ofFn digits = digits 0 :: List.ofFn tailDigits := by
        rw [List.ofFn_succ]
      rw [hrow] at hno
      cases hnext :
          (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits 0) with
      | some next =>
          refine ⟨0, next, ?_, hnext⟩
          intro index hlt
          simp at hlt
      | none =>
          have htail :
              (incrementClockRow M (List.ofFn tailDigits)).2 = false := by
            simpa [incrementClockRow, RowNumeral.DigitCodec.increment, hnext]
              using hno
          rcases ih tailDigits htail with
            ⟨tailStop, next, hbeforeTail, hnextTail⟩
          refine ⟨tailStop.succ, next, ?_, ?_⟩
          · intro index hlt
            by_cases hzeroIndex : index.val = 0
            · have hindex : index = 0 := Fin.ext hzeroIndex
              subst index
              exact hnext
            · let tailIndex : Fin (n + 1) :=
                ⟨index.val - 1, by
                  have := index.isLt
                  omega⟩
              have hsucc : tailIndex.succ = index := by
                apply Fin.ext
                simp [tailIndex]
                omega
              have htailLt : tailIndex.val < tailStop.val := by
                have hindexLe : index.val ≤ tailStop.val := by
                  simpa using hlt
                simp [tailIndex]
                omega
              have ht := hbeforeTail tailIndex htailLt
              simpa [tailDigits, hsucc] using ht
          · exact hnextTail

private def carryCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  if index.val < current.val then
    { readyCell tape digits index with digit := clockZero M, carry := true }
  else
    readyCell tape digits index

private def carryTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (carryCell M tape digits current index), current⟩

private theorem carryTape_zero_eq_leftHeadReadyTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    carryTape M tape digits ⟨0, by omega⟩ =
      leftHeadReadyTape tape digits := by
  rfl

private theorem carry_update_max
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hlt : current.val < n) :
    Function.update (carryTape M tape digits current).contents current
        (workSymbol
          { carryCell M tape digits current current with
            digit := clockZero M
            carry := true }) =
      (carryTape M tape digits ⟨current.val + 1, by omega⟩).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = current
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [carryCell]
  · rw [if_neg heq]
    have hval : index.val ≠ current.val := fun h => heq (Fin.ext h)
    change
      workSymbol (carryCell M tape digits current index) =
        workSymbol
          (carryCell M tape digits ⟨current.val + 1, by omega⟩ index)
    apply congrArg workSymbol
    simp only [carryCell]
    by_cases hbefore : index.val < current.val
    · rw [if_pos hbefore, if_pos (by omega)]
    · rw [if_neg hbefore, if_neg (by omega)]

private theorem carry_step_max
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hlt : current.val < n)
    (hmax :
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits current) = none) :
    LBA.Step (machine M)
      ⟨.carry source, carryTape M tape digits current⟩
      ⟨.carryCheck source,
        carryTape M tape digits ⟨current.val + 1, by omega⟩⟩ := by
  let cell := carryCell M tape digits current current
  refine ⟨.carryCheck source,
    workSymbol { cell with digit := clockZero M, carry := true },
    .right, ?_, ?_⟩
  · change
      (.carryCheck source,
          workSymbol { cell with digit := clockZero M, carry := true },
          .right) ∈
        transition M (.carry source) (workSymbol cell)
    rw [transition_carry_max_notRight M source cell]
    · simp
    · simp [cell, carryCell, readyCell]
    · simpa [cell, carryCell] using hmax
    · simp [cell, carryCell, readyCell, hlt.ne]
  · symm
    apply cfg_eq rfl
    · exact carry_update_max M tape digits current hlt
    · apply Fin.ext
      simp [carryTape, DLBA.BoundedTape.write, hlt]

private theorem carryCheck_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) :
    LBA.Step (machine M)
      ⟨.carryCheck source, carryTape M tape digits current⟩
      ⟨.carry source, carryTape M tape digits current⟩ := by
  let cell := carryCell M tape digits current current
  refine ⟨.carry source, workSymbol cell, .stay, ?_, ?_⟩
  · change
      (.carry source, workSymbol cell, .stay) ∈
        transition M (.carryCheck source) (workSymbol cell)
    rw [transition_carryCheck_work, if_neg]
    · simp
    · simp [cell, carryCell, readyCell]
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      carryTape, cell, Function.update_eq_self]

private theorem reaches_carry_next_of_max
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hlt : current.val < n)
    (hmax :
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits current) = none) :
    LBA.Reaches (machine M)
      ⟨.carry source, carryTape M tape digits current⟩
      ⟨.carry source,
        carryTape M tape digits ⟨current.val + 1, by omega⟩⟩ := by
  exact ReflTransGen.head (carry_step_max M source tape digits current hlt hmax)
    (.single (carryCheck_step M source tape digits
      ⟨current.val + 1, by omega⟩))

public def returnStartCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape (incrementedDigitsAt M digits stop next) index with
    carry := decide (index.val < stop.val) }

public def returnStartTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (returnStartCell M tape digits stop next index), stop⟩

private theorem carry_update_stop
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    Function.update (carryTape M tape digits stop).contents stop
        (workSymbol
          { carryCell M tape digits stop stop with digit := next }) =
      (returnStartTape M tape digits stop next).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = stop
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [carryCell, returnStartCell, incrementedDigitsAt, readyCell]
  · rw [if_neg heq]
    apply congrArg workSymbol
    have hval : index.val ≠ stop.val := fun h => heq (Fin.ext h)
    by_cases hlt : index.val < stop.val
    · simp [carryCell, returnStartCell, incrementedDigitsAt, readyCell, hlt]
    · simp [carryCell, returnStartCell, incrementedDigitsAt, readyCell, hlt, heq]

private theorem carry_step_stop
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (hnext :
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits stop) =
        some next) :
    LBA.Step (machine M)
      ⟨.carry source, carryTape M tape digits stop⟩
      ⟨.returnL source, returnStartTape M tape digits stop next⟩ := by
  let cell := carryCell M tape digits stop stop
  refine ⟨.returnL source, workSymbol { cell with digit := next }, .stay, ?_, ?_⟩
  · change
      (.returnL source, workSymbol { cell with digit := next }, .stay) ∈
        transition M (.carry source) (workSymbol cell)
    rw [transition_carry_of_next M source cell next]
    · simp
    · simp [cell, carryCell, readyCell]
    · simpa [cell, carryCell] using hnext
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    exact (cfg_eq rfl (carry_update_stop M tape digits stop next) rfl).symm

/-- A carry with a specified first nonmaximal digit reaches the exact incremented row and enters
the guarded return sweep. -/
public theorem reaches_returnL_of_first_next
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (hbefore :
      ∀ index : Fin (n + 1), index.val < stop.val →
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits index) = none)
    (hnext :
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits stop) =
        some next) :
    LBA.Reaches (machine M)
      ⟨.carry source, leftHeadReadyTape tape digits⟩
      ⟨.returnL source, returnStartTape M tape digits stop next⟩ := by
  rw [← carryTape_zero_eq_leftHeadReadyTape M tape digits]
  let zero : Fin (n + 1) := ⟨0, by omega⟩
  suffices H :
      ∀ distance, ∀ current : Fin (n + 1),
        current.val ≤ stop.val →
        stop.val - current.val = distance →
        LBA.Reaches (machine M)
          ⟨.carry source, carryTape M tape digits current⟩
          ⟨.returnL source, returnStartTape M tape digits stop next⟩ from
    H stop.val zero (by simp [zero]) (by simp [zero])
  intro distance
  induction distance with
  | zero =>
      intro current hle hdistance
      have hcurrent : current = stop := by
        apply Fin.ext
        omega
      subst current
      exact .single (carry_step_stop M source tape digits stop next hnext)
  | succ distance ih =>
      intro current hle hdistance
      have hltStop : current.val < stop.val := by omega
      have hlt : current.val < n := by
        have := stop.isLt
        omega
      let following : Fin (n + 1) := ⟨current.val + 1, by omega⟩
      exact
        (reaches_carry_next_of_max M source tape digits current hlt
          (hbefore current hltStop)).trans
        (ih following (by simp [following]; omega)
          (by simp [following]; omega))

/-! ## Return to the left boundary and recovery of the simulated head -/

private def returnCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape (incrementedDigitsAt M digits stop next) index with
    carry := decide (index.val ≤ current.val ∧ index.val < stop.val)
    post := decide (current.val < index.val ∧ index.val ≤ stop.val) }

private def returnTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current : Fin (n + 1)) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (returnCell M tape digits stop next current index), current⟩

private theorem returnTape_stop_eq_start
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    returnTape M tape digits stop next stop =
      returnStartTape M tape digits stop next := by
  simp only [returnTape, returnStartTape]
  congr 1
  funext index
  apply congrArg workSymbol
  simp [returnCell, returnStartCell, readyCell]
  omega

private theorem return_update_left
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hpos : 0 < current.val)
    (hle : current.val ≤ stop.val) :
    Function.update (returnTape M tape digits stop next current).contents current
        (workSymbol (returnCell M tape digits stop next current current).posted) =
      (returnTape M tape digits stop next
        ⟨current.val - 1, by omega⟩).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = current
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [returnCell, WorkCell.posted, hpos, hle]
  · rw [if_neg heq]
    have hval : index.val ≠ current.val := fun h => heq (Fin.ext h)
    change
      workSymbol (returnCell M tape digits stop next current index) =
        workSymbol
          (returnCell M tape digits stop next
            ⟨current.val - 1, by omega⟩ index)
    apply congrArg workSymbol
    have hcarry :
        decide (index.val ≤ current.val ∧ index.val < stop.val) =
          decide (index.val ≤ current.val - 1 ∧ index.val < stop.val) :=
      Bool.decide_congr (by
        constructor <;> rintro ⟨h₁, h₂⟩ <;>
          exact ⟨by omega, h₂⟩)
    have hpost :
        decide (current.val < index.val ∧ index.val ≤ stop.val) =
          decide (current.val - 1 < index.val ∧ index.val ≤ stop.val) :=
      Bool.decide_congr (by
        constructor <;> rintro ⟨h₁, h₂⟩ <;>
          exact ⟨by omega, h₂⟩)
    simp only [returnCell]
    rw [hcarry, hpost]

private theorem return_step_left
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hpos : 0 < current.val)
    (hle : current.val ≤ stop.val) :
    LBA.Step (machine M)
      ⟨.returnL source, returnTape M tape digits stop next current⟩
      ⟨.returnL source,
        returnTape M tape digits stop next
          ⟨current.val - 1, by omega⟩⟩ := by
  let cell := returnCell M tape digits stop next current current
  refine ⟨.returnL source, workSymbol cell.posted, .left, ?_, ?_⟩
  · change
      (.returnL source, workSymbol cell.posted, .left) ∈
        transition M (.returnL source) (workSymbol cell)
    rw [transition_returnL_work, if_neg, if_neg]
    · simp
    · simp [cell, returnCell]
    · simp [cell, returnCell, readyCell, hpos.ne']
  · symm
    apply cfg_eq rfl
    · exact return_update_left M tape digits stop next current hpos hle
    · apply Fin.ext
      simp [returnTape, DLBA.BoundedTape.write, hpos]

private def findStartCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape (incrementedDigitsAt M digits stop next) index with
    post := decide (0 < index.val ∧ index.val ≤ stop.val) }

private def findStartTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (findStartCell M tape digits stop next index),
    ⟨0, by omega⟩⟩

private theorem return_finish_update
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    Function.update
        (returnTape M tape digits stop next ⟨0, by omega⟩).contents
        ⟨0, by omega⟩
        (workSymbol
          (returnCell M tape digits stop next
            ⟨0, by omega⟩ ⟨0, by omega⟩).clearTransient) =
      (findStartTape M tape digits stop next).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = ⟨0, by omega⟩
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [returnCell, findStartCell, readyCell, WorkCell.clearTransient]
  · rw [if_neg heq]
    apply congrArg workSymbol
    have hpos : 0 < index.val := by
      have hne : index.val ≠ 0 := by
        intro h
        exact heq (Fin.ext (by simpa using h))
      omega
    have hcarry :
        decide (index.val ≤ 0 ∧ index.val < stop.val) = false := by
      have hn : ¬(index.val ≤ 0 ∧ index.val < stop.val) := by
        rintro ⟨hle, _⟩
        omega
      exact (Bool.decide_false_iff _).2 hn
    simp only [returnCell, findStartCell]
    rw [hcarry]
    rfl

private theorem return_step_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    LBA.Step (machine M)
      ⟨.returnL source,
        returnTape M tape digits stop next ⟨0, by omega⟩⟩
      ⟨.findMark source, findStartTape M tape digits stop next⟩ := by
  let zero : Fin (n + 1) := ⟨0, by omega⟩
  let cell := returnCell M tape digits stop next zero zero
  refine ⟨.findMark source, workSymbol cell.clearTransient, .stay, ?_, ?_⟩
  · change
      (.findMark source, workSymbol cell.clearTransient, .stay) ∈
        transition M (.returnL source) (workSymbol cell)
    rw [transition_returnL_work, if_pos]
    · simp
    · simp [cell, returnCell, readyCell, zero]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    exact (cfg_eq rfl (return_finish_update M tape digits stop next) rfl).symm

private theorem return_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    ∀ current : Fin (n + 1), current.val ≤ stop.val →
      LBA.Reaches (machine M)
        ⟨.returnL source, returnTape M tape digits stop next current⟩
        ⟨.findMark source, findStartTape M tape digits stop next⟩ := by
  suffices H :
      ∀ value, ∀ current : Fin (n + 1), current.val = value →
        current.val ≤ stop.val →
        LBA.Reaches (machine M)
          ⟨.returnL source, returnTape M tape digits stop next current⟩
          ⟨.findMark source, findStartTape M tape digits stop next⟩ from
    fun current hle => H current.val current rfl hle
  intro value
  induction value with
  | zero =>
      intro current hvalue hle
      have hcurrent : current = ⟨0, by omega⟩ := Fin.ext hvalue
      rw [hcurrent]
      exact .single (return_step_zero M source tape digits stop next)
  | succ value ih =>
      intro current hvalue hle
      have hpos : 0 < current.val := by omega
      let previous : Fin (n + 1) := ⟨current.val - 1, by omega⟩
      have hprevious : previous.val = value := by
        simp [previous]
        omega
      exact ReflTransGen.head
        (return_step_left M source tape digits stop next current hpos hle)
        (ih previous hprevious (by simp [previous]; omega))

public def completedTrails
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (stop : Fin (n + 1)) :
    ReadyTrails n where
  post index := decide (tape.head.val < index.val ∧ index.val ≤ stop.val)
  scan index := decide (index.val < tape.head.val)

private def findCell
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape (incrementedDigitsAt M digits stop next) index with
    post := decide
      (current.val ≤ index.val ∧ 0 < index.val ∧ index.val ≤ stop.val)
    scan := decide (index.val < current.val) }

private def findTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current : Fin (n + 1)) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n :=
  ⟨fun index => workSymbol (findCell M tape digits stop next current index), current⟩

private theorem findTape_zero_eq_start
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    findTape M tape digits stop next ⟨0, by omega⟩ =
      findStartTape M tape digits stop next := by
  simp only [findTape, findStartTape]
  congr 1
  funext index
  apply congrArg workSymbol
  simp [findCell, findStartCell, readyCell]

private theorem find_update_right
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hlt : current.val < tape.head.val) :
    Function.update (findTape M tape digits stop next current).contents current
        (workSymbol (findCell M tape digits stop next current current).scanned) =
      (findTape M tape digits stop next
        ⟨current.val + 1, by
          have := tape.head.isLt
          omega⟩).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = current
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [findCell, WorkCell.scanned]
  · rw [if_neg heq]
    have hval : index.val ≠ current.val := fun h => heq (Fin.ext h)
    change
      workSymbol (findCell M tape digits stop next current index) =
        workSymbol
          (findCell M tape digits stop next
            ⟨current.val + 1, by
              have := tape.head.isLt
              omega⟩ index)
    apply congrArg workSymbol
    have hpost :
        decide
            (current.val ≤ index.val ∧ 0 < index.val ∧
              index.val ≤ stop.val) =
          decide
            (current.val + 1 ≤ index.val ∧ 0 < index.val ∧
              index.val ≤ stop.val) :=
      Bool.decide_congr (by
        constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;>
          exact ⟨by omega, h₂, h₃⟩)
    have hscan :
        decide (index.val < current.val) =
          decide (index.val < current.val + 1) :=
      Bool.decide_congr (by omega)
    simp only [findCell]
    rw [hpost, hscan]

private theorem find_step_right
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (current : Fin (n + 1)) (hlt : current.val < tape.head.val) :
    LBA.Step (machine M)
      ⟨.findMark source, findTape M tape digits stop next current⟩
      ⟨.findMark source,
        findTape M tape digits stop next
          ⟨current.val + 1, by
            have := tape.head.isLt
            omega⟩⟩ := by
  let cell := findCell M tape digits stop next current current
  refine ⟨.findMark source, workSymbol cell.scanned, .right, ?_, ?_⟩
  · change
      (.findMark source, workSymbol cell.scanned, .right) ∈
        transition M (.findMark source) (workSymbol cell)
    rw [transition_findMark_work, if_neg, if_neg, if_neg]
    · simp
    · simp [cell, findCell]
    · simp [cell, findCell, readyCell]
      have := tape.head.isLt
      omega
    · intro hmark
      have heq : current = tape.head := by
        simpa [cell, findCell, readyCell] using hmark
      have hval := congrArg Fin.val heq
      omega
  · symm
    apply cfg_eq rfl
    · exact find_update_right M tape digits stop next current hlt
    · apply Fin.ext
      have hcurrent : current.val < n := by
        have := tape.head.isLt
        omega
      simp [findTape, DLBA.BoundedTape.write, hcurrent]

private theorem find_finish_update
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    Function.update
        (findTape M tape digits stop next tape.head).contents tape.head
        (workSymbol
          (findCell M tape digits stop next tape.head tape.head).clearTransient) =
      (checkpointTape tape (incrementedDigitsAt M digits stop next)
        (completedTrails tape stop)).contents := by
  funext index
  rw [Function.update_apply]
  by_cases heq : index = tape.head
  · subst index
    rw [if_pos rfl]
    apply congrArg workSymbol
    simp [findCell, checkpointCell, completedTrails, readyCell,
      WorkCell.clearTransient]
  · rw [if_neg heq]
    apply congrArg workSymbol
    have hval : index.val ≠ tape.head.val := fun h => heq (Fin.ext h)
    have hpost :
        decide
            (tape.head.val ≤ index.val ∧ 0 < index.val ∧
              index.val ≤ stop.val) =
          decide (tape.head.val < index.val ∧ index.val ≤ stop.val) :=
      Bool.decide_congr (by
        constructor
        · rintro ⟨h₁, h₂, h₃⟩
          exact ⟨by omega, h₃⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨by omega, by omega, h₂⟩)
    simp only [findCell, checkpointCell, completedTrails]
    rw [hpost]

private theorem find_step_mark
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    LBA.Step (machine M)
      ⟨.findMark source, findTape M tape digits stop next tape.head⟩
      ⟨.ready source,
        checkpointTape tape (incrementedDigitsAt M digits stop next)
          (completedTrails tape stop)⟩ := by
  let cell := findCell M tape digits stop next tape.head tape.head
  refine ⟨.ready source, workSymbol cell.clearTransient, .stay, ?_, ?_⟩
  · change
      (.ready source, workSymbol cell.clearTransient, .stay) ∈
        transition M (.findMark source) (workSymbol cell)
    rw [transition_findMark_work, if_pos]
    · simp
    · simp [cell, findCell, readyCell]
  · simp only [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead]
    exact (cfg_eq rfl (find_finish_update M tape digits stop next) rfl).symm

private theorem find_sweep
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ) :
    ∀ current : Fin (n + 1), current.val ≤ tape.head.val →
      LBA.Reaches (machine M)
        ⟨.findMark source, findTape M tape digits stop next current⟩
        ⟨.ready source,
          checkpointTape tape (incrementedDigitsAt M digits stop next)
            (completedTrails tape stop)⟩ := by
  suffices H :
      ∀ distance, ∀ current : Fin (n + 1),
        current.val ≤ tape.head.val →
        tape.head.val - current.val = distance →
        LBA.Reaches (machine M)
          ⟨.findMark source, findTape M tape digits stop next current⟩
          ⟨.ready source,
            checkpointTape tape (incrementedDigitsAt M digits stop next)
              (completedTrails tape stop)⟩ from
    fun current hle => H (tape.head.val - current.val) current hle rfl
  intro distance
  induction distance with
  | zero =>
      intro current hle hdistance
      have hcurrent : current = tape.head := by
        apply Fin.ext
        omega
      subst current
      exact .single (find_step_mark M source tape digits stop next)
  | succ distance ih =>
      intro current hle hdistance
      have hlt : current.val < tape.head.val := by omega
      let following : Fin (n + 1) :=
        ⟨current.val + 1, by
          have := tape.head.isLt
          omega⟩
      exact ReflTransGen.head
        (find_step_right M source tape digits stop next current hlt)
        (ih following (by simp [following]; omega)
          (by simp [following]; omega))

/-- Given the first nonmaximal digit, the entire carry/return/find suffix reaches the exact
operational Ready checkpoint with the locally incremented clock row. -/
public theorem reaches_checkpoint_of_first_next
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (stop : Fin (n + 1)) (next : ClockDigit T Γ Λ)
    (hbefore :
      ∀ index : Fin (n + 1), index.val < stop.val →
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits index) = none)
    (hnext :
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next (digits stop) =
        some next) :
    LBA.Reaches (machine M)
      ⟨.carry source, leftHeadReadyTape tape digits⟩
      (checkpointCfg
        (⟨source, tape⟩ : DLBA.Cfg (SourceAlpha T Γ) Λ n)
        (incrementedDigitsAt M digits stop next)
        (completedTrails tape stop)) := by
  exact (reaches_returnL_of_first_next M source tape digits stop next hbefore hnext).trans
    (((show returnStartTape M tape digits stop next =
          returnTape M tape digits stop next stop by
        symm
        exact returnTape_stop_eq_start M tape digits stop next) ▸
      return_sweep M source tape digits stop next stop (Nat.le_refl _)).trans
    (((show findStartTape M tape digits stop next =
          findTape M tape digits stop next ⟨0, by omega⟩ by
        symm
        exact findTape_zero_eq_start M tape digits stop next) ▸
      find_sweep M source tape digits stop next ⟨0, by omega⟩ (by simp))))

/-- Once the nondeterministic Ready transition has selected a source move, the remaining protocol
is deterministic.  Under nonoverflow it reaches the exact incremented successor checkpoint from
the concrete `.mark` configuration produced by that first step. -/
public theorem reaches_incremented_checkpoint_afterReady
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (target : Λ) (written : SourceAlpha T Γ) (direction : DLBA.Dir)
    (hno : (incrementClockRow M (List.ofFn digits)).2 = false) :
    ∃ (digits' : Fin (n + 1) → ClockDigit T Γ Λ)
      (trails' : ReadyTrails n),
      List.ofFn digits' = (incrementClockRow M (List.ofFn digits)).1 ∧
      LBA.Reaches (machine M)
        (afterReadyCfg cfg digits trails target written direction)
        (checkpointCfg
          (⟨target, (cfg.tape.write written).moveHead direction⟩ :
            DLBA.Cfg (SourceAlpha T Γ) Λ n)
          digits' trails') := by
  rcases exists_first_next_of_not_overflow M digits hno with
    ⟨stop, next, hbefore, hnext⟩
  let successorTape := (cfg.tape.write written).moveHead direction
  let digits' := incrementedDigitsAt M digits stop next
  let trails' := completedTrails successorTape stop
  refine ⟨digits', trails', ?_, ?_⟩
  · have hinc :=
      increment_of_first_next M digits stop next hbefore hnext
    exact (congrArg Prod.fst hinc).symm
  · have hmark :=
      step_mark_unmarked_checkpoint M target successorTape digits
        (trails.clearAt cfg.tape.head)
    have hnormalize :=
      reaches_carry_of_seek_checkpoint M target successorTape digits
        ((trails.clearAt cfg.tape.head).clearAt successorTape.head)
    have hfinish :=
      reaches_checkpoint_of_first_next M target successorTape digits stop next
        hbefore hnext
    rw [afterReadyCfg, afterReadyTape,
      checkpoint_write_move_eq_unmarkedTape]
    exact (ReflTransGen.single hmark).trans (hnormalize.trans hfinish)

/-- Core macro completeness.  From any operational Ready checkpoint, every source step whose
clock row has a nonoverflowing successor reaches a Ready checkpoint for the source successor.
The output digit function reconstructs exactly the first component of `DigitCodec.increment`. -/
public theorem reaches_incremented_checkpoint_of_step
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (hstep : LBA.Step M cfg cfg')
    (hno : (incrementClockRow M (List.ofFn digits)).2 = false) :
    ∃ (digits' : Fin (n + 1) → ClockDigit T Γ Λ)
      (trails' : ReadyTrails n),
      List.ofFn digits' = (incrementClockRow M (List.ofFn digits)).1 ∧
      LBA.Reaches (machine M)
        (checkpointCfg cfg digits trails)
        (checkpointCfg cfg' digits' trails') := by
  rcases exists_first_next_of_not_overflow M digits hno with
    ⟨stop, next, hbefore, hnext⟩
  let digits' := incrementedDigitsAt M digits stop next
  let trails' := completedTrails cfg'.tape stop
  refine ⟨digits', trails', ?_, ?_⟩
  · have hinc :=
      increment_of_first_next M digits stop next hbefore hnext
    exact (congrArg Prod.fst hinc).symm
  · exact (reaches_carry_checkpoint_of_step M digits trails hstep).trans
      (reaches_checkpoint_of_first_next M cfg'.state cfg'.tape digits stop next
        hbefore hnext)

/-- The clean representation requested for a first macro is the clear-trail instance of the
general checkpoint theorem. -/
public theorem reaches_incremented_checkpoint_of_step_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg cfg' : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (hstep : LBA.Step M cfg cfg')
    (hno : (incrementClockRow M (List.ofFn digits)).2 = false) :
    ∃ (digits' : Fin (n + 1) → ClockDigit T Γ Λ)
      (trails' : ReadyTrails n),
      List.ofFn digits' = (incrementClockRow M (List.ofFn digits)).1 ∧
      LBA.Reaches (machine M)
        (readyCfg cfg digits)
        (checkpointCfg cfg' digits' trails') := by
  rw [← checkpointCfg_clear cfg digits]
  exact reaches_incremented_checkpoint_of_step M digits (ReadyTrails.clear n)
    hstep hno

/-- Clean Ready is the all-false-trail special case of the general normalization theorem. -/
public theorem reaches_carry_of_seek_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    LBA.Reaches (machine M)
      ⟨.seek source, readyTape tape digits⟩
      ⟨.carry source, leftHeadReadyTape tape digits⟩ := by
  rw [← checkpointTape_clear tape digits]
  exact reaches_carry_of_seek_checkpoint M source tape digits (ReadyTrails.clear n)

end LBA.AcyclicClock

end
