module

public import Langlib.Automata.LinearBounded.AcyclicClock.Canonical
import Mathlib.Tactic

@[expose]
public section

/-!
# Ready checkpoint encodings for the operational clock compiler

`Canonical` describes the clean zero-clock configuration produced by initialization.  A completed
simulated macrostep may retain two harmless guard trails: `findMark` leaves `scan` bits to the left
of the simulated head, and `returnL` may leave `post` bits to its right.  The next normalization
sweep clears both tracks.

This file therefore distinguishes:

* `readyCell`/`readyTape`/`readyCfg`, the completely clean auxiliary representation used directly
  by canonical initialization; and
* `checkpointCell`/`checkpointTape`/`checkpointCfg`, parameterized by the two unconstrained
  `ReadyTrails` tracks, the actual representation invariant at operational `ready` checkpoints.

The clean representation is the special case `ReadyTrails.clear`.

The projection is total on malformed target tapes: an unconverted symbol contributes the zero
digit.  This totality is used by the global acyclicity proof, whose rank is defined on every
target configuration rather than only on canonical runs.
-/

open Classical

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}
variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- A clean work cell representing one source-tape cell and one arbitrary clock digit. -/
public def readyCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ where
  src := tape.contents index
  digit := digits index
  left := decide (index.val = 0)
  right := decide (index.val = n)
  mark := decide (index = tape.head)
  init := false
  seek := false
  norm := false
  carry := false
  post := false
  scan := false

/-- A clean target work tape carrying an arbitrary same-width clock row. -/
public def readyTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n where
  contents index := workSymbol (readyCell tape digits index)
  head := tape.head

/-- A source configuration represented at a completed target-machine checkpoint. -/
public def readyCfg
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  ⟨.ready cfg.state, readyTape cfg.tape digits⟩

/-- The two harmless transient tracks permitted at a Ready checkpoint.  They are deliberately
unconstrained: their exact shapes depend on both the simulated-head position and the clock carry
stop.  The next `cleanR`/`cleanL` normalization clears them before they can affect another carry. -/
public structure ReadyTrails (n : ℕ) where
  post : Fin (n + 1) → Bool
  scan : Fin (n + 1) → Bool

/-- Completely clear Ready trails, used by canonical initialization. -/
public def ReadyTrails.clear (n : ℕ) : ReadyTrails n where
  post := fun _ => false
  scan := fun _ => false

/-- The actual operational Ready cell.  Source data, clock digits, boundaries, the unique mark,
and all guards needed to start the next macro are canonical; only `post` and `scan` are supplied
by the checkpoint trail parameter. -/
public def checkpointCell
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    WorkCell T Γ Λ :=
  { readyCell tape digits index with
    post := trails.post index
    scan := trails.scan index }

/-- A complete target tape at an operational Ready checkpoint. -/
public def checkpointTape
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    DLBA.BoundedTape (TapeAlpha T Γ Λ) n where
  contents index := workSymbol (checkpointCell tape digits trails index)
  head := tape.head

/-- The actual target representation invariant between completed source-step macros. -/
public def checkpointCfg
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n :=
  ⟨.ready cfg.state, checkpointTape cfg.tape digits trails⟩

/-- A target configuration represents a source configuration and clock row at a Ready checkpoint
when it has some (irrelevant) pair of `post`/`scan` trails. -/
public def RepresentsCheckpoint
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n) : Prop :=
  ∃ trails : ReadyTrails n, target = checkpointCfg cfg digits trails

@[simp]
public theorem readyCell_src
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    (readyCell tape digits index).src = tape.contents index := rfl

@[simp]
public theorem readyCell_digit
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    (readyCell tape digits index).digit = digits index := rfl

@[simp]
public theorem readyCell_left_iff
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    (readyCell tape digits index).left = true ↔ index.val = 0 := by
  simp [readyCell]

@[simp]
public theorem readyCell_right_iff
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    (readyCell tape digits index).right = true ↔ index.val = n := by
  simp [readyCell]

@[simp]
public theorem readyCell_mark_iff
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    (readyCell tape digits index).mark = true ↔ index = tape.head := by
  simp [readyCell]

@[simp]
public theorem readyCell_clearTransient
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    (readyCell tape digits index).clearTransient =
      readyCell tape digits index := rfl

@[simp]
public theorem asWork_readyTape_contents
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    asWork ((readyTape tape digits).contents index) =
      some (readyCell tape digits index) := rfl

@[simp]
public theorem readyTape_head
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    (readyTape tape digits).head = tape.head := rfl

@[simp]
public theorem readyTape_read
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    (readyTape tape digits).read =
      workSymbol (readyCell tape digits tape.head) := rfl

@[simp]
public theorem readyCfg_state
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    (readyCfg cfg digits).state = .ready cfg.state := rfl

@[simp]
public theorem readyCfg_tape
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    (readyCfg cfg digits).tape = readyTape cfg.tape digits := rfl

@[simp]
public theorem checkpointCell_src
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).src = tape.contents index := rfl

@[simp]
public theorem checkpointCell_digit
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).digit = digits index := rfl

@[simp]
public theorem checkpointCell_left_iff
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).left = true ↔ index.val = 0 :=
  readyCell_left_iff tape digits index

@[simp]
public theorem checkpointCell_right_iff
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).right = true ↔ index.val = n :=
  readyCell_right_iff tape digits index

@[simp]
public theorem checkpointCell_mark_iff
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).mark = true ↔ index = tape.head :=
  readyCell_mark_iff tape digits index

@[simp]
public theorem checkpointCell_post
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).post = trails.post index := rfl

@[simp]
public theorem checkpointCell_scan
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).scan = trails.scan index := rfl

@[simp]
public theorem checkpointCell_init
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).init = false := rfl

@[simp]
public theorem checkpointCell_seek
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).seek = false := rfl

@[simp]
public theorem checkpointCell_norm
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).norm = false := rfl

@[simp]
public theorem checkpointCell_carry
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).carry = false := rfl

@[simp]
public theorem checkpointCell_clearTransient
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    (checkpointCell tape digits trails index).clearTransient =
      readyCell tape digits index := by
  rfl

@[simp]
public theorem asWork_checkpointTape_contents
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    asWork ((checkpointTape tape digits trails).contents index) =
      some (checkpointCell tape digits trails index) := rfl

@[simp]
public theorem projectedSourceSymbol_checkpointTape_contents
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n)
    (index : Fin (n + 1)) :
    projectedSourceSymbol ((checkpointTape tape digits trails).contents index) =
      some (tape.contents index) := rfl

@[simp]
public theorem checkpointTape_head
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    (checkpointTape tape digits trails).head = tape.head := rfl

@[simp]
public theorem checkpointTape_read
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    (checkpointTape tape digits trails).read =
      workSymbol (checkpointCell tape digits trails tape.head) := rfl

@[simp]
public theorem checkpointCfg_state
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    (checkpointCfg cfg digits trails).state = .ready cfg.state := rfl

@[simp]
public theorem checkpointCfg_tape
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    (checkpointCfg cfg digits trails).tape =
      checkpointTape cfg.tape digits trails := rfl

@[simp]
public theorem machine_accept_checkpointCfg
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    (machine M).accept (checkpointCfg cfg digits trails).state =
      M.accept cfg.state := rfl

public theorem representsCheckpoint_checkpointCfg
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    RepresentsCheckpoint cfg digits (checkpointCfg cfg digits trails) :=
  ⟨trails, rfl⟩

public theorem representsCheckpoint_readyCfg
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    RepresentsCheckpoint cfg digits (readyCfg cfg digits) := by
  exact ⟨ReadyTrails.clear n, rfl⟩

public theorem RepresentsCheckpoint.state_eq
    {n : ℕ} {cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    {digits : Fin (n + 1) → ClockDigit T Γ Λ}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hrep : RepresentsCheckpoint cfg digits target) :
    target.state = .ready cfg.state := by
  rcases hrep with ⟨trails, rfl⟩
  rfl

public theorem RepresentsCheckpoint.accept_eq
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    {digits : Fin (n + 1) → ClockDigit T Γ Λ}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hrep : RepresentsCheckpoint cfg digits target) :
    (machine M).accept target.state = M.accept cfg.state := by
  rw [hrep.state_eq]
  rfl

/-! ## Relation to canonical initialization -/

@[simp]
public theorem canonicalCell_eq_readyCell_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (index : Fin (n + 1)) :
    canonicalCell M tape index =
      readyCell tape (fun _ => clockZero M) index := rfl

@[simp]
public theorem canonicalTape_eq_readyTape_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n) :
    canonicalTape M tape =
      readyTape tape (fun _ => clockZero M) := rfl

@[simp]
public theorem canonicalCfg_eq_readyCfg_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    canonicalCfg M cfg =
      readyCfg cfg (fun _ => clockZero M) := rfl

/-- Supplying clear trails recovers the completely clean Ready cell. -/
@[simp]
public theorem checkpointCell_clear
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (index : Fin (n + 1)) :
    checkpointCell tape digits (ReadyTrails.clear n) index =
      readyCell tape digits index := rfl

/-- Supplying clear trails recovers the completely clean Ready tape. -/
@[simp]
public theorem checkpointTape_clear
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    checkpointTape tape digits (ReadyTrails.clear n) =
      readyTape tape digits := rfl

/-- Supplying clear trails recovers the completely clean Ready configuration. -/
@[simp]
public theorem checkpointCfg_clear
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    checkpointCfg cfg digits (ReadyTrails.clear n) =
      readyCfg cfg digits := rfl

/-- Canonical initialization is the clear-trail, zero-clock operational checkpoint. -/
public theorem canonicalCfg_eq_checkpointCfg_clear_zero
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    canonicalCfg M cfg =
      checkpointCfg cfg (fun _ => clockZero M) (ReadyTrails.clear n) := by
  rw [checkpointCfg_clear]
  exact canonicalCfg_eq_readyCfg_zero M cfg

/-- Every canonical zero-clock encoding is a valid operational checkpoint representation. -/
public theorem representsCheckpoint_canonicalCfg
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n) :
    RepresentsCheckpoint cfg (fun _ => clockZero M) (canonicalCfg M cfg) := by
  refine ⟨ReadyTrails.clear n, ?_⟩
  exact canonicalCfg_eq_checkpointCfg_clear_zero M cfg

/-! ## Exact information content -/

/-- The general Ready tape encoding jointly preserves the source tape and the complete clock row. -/
public theorem readyTape_pair_injective {n : ℕ} :
    Function.Injective
      (fun data :
          DLBA.BoundedTape (SourceAlpha T Γ) n ×
            (Fin (n + 1) → ClockDigit T Γ Λ) =>
        readyTape data.1 data.2) := by
  rintro ⟨leftTape, leftDigits⟩ ⟨rightTape, rightDigits⟩ heq
  have hhead : leftTape.head = rightTape.head :=
    congrArg
      (fun tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n => tape.head) heq
  have hcells :
      ∀ index,
        readyCell leftTape leftDigits index =
          readyCell rightTape rightDigits index := by
    intro index
    have hsymbol :=
      congrFun (congrArg DLBA.BoundedTape.contents heq) index
    change
      workSymbol (readyCell leftTape leftDigits index) =
        workSymbol (readyCell rightTape rightDigits index) at hsymbol
    simpa [workSymbol] using hsymbol
  have hcontents : leftTape.contents = rightTape.contents := by
    funext index
    exact congrArg WorkCell.src (hcells index)
  have hdigits : leftDigits = rightDigits := by
    funext index
    exact congrArg WorkCell.digit (hcells index)
  have htapes : leftTape = rightTape := by
    cases leftTape
    cases rightTape
    simp_all
  simp_all

/-- The general Ready configuration encoding jointly preserves the source configuration and clock
row. -/
public theorem readyCfg_pair_injective {n : ℕ} :
    Function.Injective
      (fun data :
          DLBA.Cfg (SourceAlpha T Γ) Λ n ×
            (Fin (n + 1) → ClockDigit T Γ Λ) =>
        readyCfg data.1 data.2) := by
  rintro ⟨leftCfg, leftDigits⟩ ⟨rightCfg, rightDigits⟩ heq
  have hstate : leftCfg.state = rightCfg.state := by
    have := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simpa [readyCfg] using this
  have htapeData :
      (leftCfg.tape, leftDigits) = (rightCfg.tape, rightDigits) := by
    apply readyTape_pair_injective
    exact congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.tape) heq
  cases leftCfg
  cases rightCfg
  simp_all

/-- At fixed Ready trails, the operational checkpoint tape jointly preserves the source tape and
complete clock row. -/
public theorem checkpointTape_pair_injective {n : ℕ} (trails : ReadyTrails n) :
    Function.Injective
      (fun data :
          DLBA.BoundedTape (SourceAlpha T Γ) n ×
            (Fin (n + 1) → ClockDigit T Γ Λ) =>
        checkpointTape data.1 data.2 trails) := by
  rintro ⟨leftTape, leftDigits⟩ ⟨rightTape, rightDigits⟩ heq
  have hhead : leftTape.head = rightTape.head :=
    congrArg
      (fun tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n => tape.head) heq
  have hcells :
      ∀ index,
        checkpointCell leftTape leftDigits trails index =
          checkpointCell rightTape rightDigits trails index := by
    intro index
    have hsymbol :=
      congrFun (congrArg DLBA.BoundedTape.contents heq) index
    change
      workSymbol (checkpointCell leftTape leftDigits trails index) =
        workSymbol (checkpointCell rightTape rightDigits trails index) at hsymbol
    simpa [workSymbol] using hsymbol
  have hcontents : leftTape.contents = rightTape.contents := by
    funext index
    exact congrArg WorkCell.src (hcells index)
  have hdigits : leftDigits = rightDigits := by
    funext index
    exact congrArg WorkCell.digit (hcells index)
  have htapes : leftTape = rightTape := by
    cases leftTape
    cases rightTape
    simp_all
  simp_all

/-- At fixed Ready trails, the operational checkpoint configuration jointly preserves the source
configuration and clock row. -/
public theorem checkpointCfg_pair_injective {n : ℕ} (trails : ReadyTrails n) :
    Function.Injective
      (fun data :
          DLBA.Cfg (SourceAlpha T Γ) Λ n ×
            (Fin (n + 1) → ClockDigit T Γ Λ) =>
        checkpointCfg data.1 data.2 trails) := by
  rintro ⟨leftCfg, leftDigits⟩ ⟨rightCfg, rightDigits⟩ heq
  have hstate : leftCfg.state = rightCfg.state := by
    have := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simpa [checkpointCfg] using this
  have htapeData :
      (leftCfg.tape, leftDigits) = (rightCfg.tape, rightDigits) := by
    apply checkpointTape_pair_injective trails
    exact congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.tape) heq
  cases leftCfg
  cases rightCfg
  simp_all

/-- The irrelevant Ready trails do not make the represented source configuration or clock row
ambiguous. -/
public theorem representsCheckpoint_source_clock_unique
    {n : ℕ}
    {leftCfg rightCfg : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    {leftDigits rightDigits : Fin (n + 1) → ClockDigit T Γ Λ}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hleft : RepresentsCheckpoint leftCfg leftDigits target)
    (hright : RepresentsCheckpoint rightCfg rightDigits target) :
    leftCfg = rightCfg ∧ leftDigits = rightDigits := by
  rcases hleft with ⟨leftTrails, rfl⟩
  rcases hright with ⟨rightTrails, heq⟩
  have hstate : leftCfg.state = rightCfg.state := by
    have := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.state) heq
    simpa [checkpointCfg] using this
  have hhead : leftCfg.tape.head = rightCfg.tape.head := by
    have := congrArg
      (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n => cfg.tape.head) heq
    simpa [checkpointCfg, checkpointTape] using this
  have hcells :
      ∀ index,
        checkpointCell leftCfg.tape leftDigits leftTrails index =
          checkpointCell rightCfg.tape rightDigits rightTrails index := by
    intro index
    have hsymbol :=
      congrFun
        (congrArg
          (fun cfg : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n =>
            cfg.tape.contents) heq)
        index
    change
      workSymbol
          (checkpointCell leftCfg.tape leftDigits leftTrails index) =
        workSymbol
          (checkpointCell rightCfg.tape rightDigits rightTrails index) at hsymbol
    simpa [workSymbol] using hsymbol
  have hcontents : leftCfg.tape.contents = rightCfg.tape.contents := by
    funext index
    exact congrArg WorkCell.src (hcells index)
  have hdigits : leftDigits = rightDigits := by
    funext index
    exact congrArg WorkCell.digit (hcells index)
  have htapes : leftCfg.tape = rightCfg.tape := by
    cases hleftTape : leftCfg.tape with
    | mk leftContents leftHead =>
        cases hrightTape : rightCfg.tape with
        | mk rightContents rightHead =>
            rw [hleftTape] at hcontents hhead
            rw [hrightTape] at hcontents hhead
            rw [DLBA.BoundedTape.mk.injEq]
            exact ⟨hcontents, hhead⟩
  constructor
  · cases leftCfg
    cases rightCfg
    simp_all
  · exact hdigits

/-! ## A total numeric clock rank -/

/-- Project a clock digit from a converted target symbol. -/
public def projectedClockDigit
    (symbol : TapeAlpha T Γ Λ) : Option (ClockDigit T Γ Λ) :=
  (asWork symbol).map WorkCell.digit

@[simp]
public theorem projectedClockDigit_workSymbol
    (cell : WorkCell T Γ Λ) :
    projectedClockDigit (workSymbol cell) = some cell.digit := rfl

/-- Read every physical clock digit from left to right.  Unconverted symbols contribute zero, so
the row is total even on malformed target configurations. -/
public def clockRowOfTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    List (ClockDigit T Γ Λ) :=
  List.ofFn fun index =>
    (projectedClockDigit (tape.contents index)).getD (clockZero M)

/-- Numeric least-significant-digit-first value of the complete physical clock track. -/
public def clockValue
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) : ℕ :=
  (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
    (clockRowOfTape M tape)

@[simp]
public theorem length_clockRowOfTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    (clockRowOfTape M tape).length = n + 1 := by
  simp [clockRowOfTape]

@[simp]
public theorem clockRowOfTape_readyTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    clockRowOfTape M (readyTape tape digits) = List.ofFn digits := by
  simp [clockRowOfTape, readyTape, projectedClockDigit]

@[simp]
public theorem clockRowOfTape_checkpointTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    clockRowOfTape M (checkpointTape tape digits trails) = List.ofFn digits := by
  simp [clockRowOfTape, checkpointTape, projectedClockDigit]

@[simp]
public theorem clockValue_readyTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ) :
    clockValue M (readyTape tape digits) =
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
        (List.ofFn digits) := by
  simp [clockValue]

@[simp]
public theorem clockValue_checkpointTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n)
    (digits : Fin (n + 1) → ClockDigit T Γ Λ)
    (trails : ReadyTrails n) :
    clockValue M (checkpointTape tape digits trails) =
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
        (List.ofFn digits) := by
  simp [clockValue]

public theorem RepresentsCheckpoint.clockValue_eq
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} {cfg : DLBA.Cfg (SourceAlpha T Γ) Λ n}
    {digits : Fin (n + 1) → ClockDigit T Γ Λ}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State Λ) n}
    (hrep : RepresentsCheckpoint cfg digits target) :
    clockValue M target.tape =
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
        (List.ofFn digits) := by
  rcases hrep with ⟨trails, rfl⟩
  exact clockValue_checkpointTape M cfg.tape digits trails

@[simp]
public theorem clockValue_canonicalTape
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (SourceAlpha T Γ) n) :
    clockValue M (canonicalTape M tape) = 0 := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rw [canonicalTape_eq_readyTape_zero, clockValue_readyTape]
  change
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value
      (List.ofFn fun _ : Fin (n + 1) =>
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zero) = 0
  have hrow :
      (List.ofFn fun _ : Fin (n + 1) =>
        (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zero) =
      (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zeroRow (n + 1) := by
    simp only [List.ofFn_const, RowNumeral.DigitCodec.zeroRow]
  rw [hrow]
  exact
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value_zeroRow (n + 1)

/-- The total clock rank always lies below the concrete same-width clock capacity. -/
public theorem clockValue_lt_capacity
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    clockValue M tape <
      LBA.StrictClockLayering.clockCapacity
        (Γ := SourceAlpha T Γ) (Λ := Λ) n := by
  have hvalue :=
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).value_lt_pow_length
      (clockRowOfTape M tape)
  simpa [clockValue, LBA.StrictClockLayering.clockCapacity,
    clockCodec_radix] using hvalue

end LBA.AcyclicClock

end
