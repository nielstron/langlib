module

public import Langlib.Automata.LinearBounded.StrictClockLayering
import Mathlib.Tactic

@[expose]
public section

/-!
# Operational acyclic LBA clock compiler

This file defines the concrete one-tape LBA macro machine used by the later globally acyclic
presentation theorem.  The transition table and local equations live here; global acyclicity and
exact language preservation are proved in `AcyclicityReduction` and `MacroSoundness`.

The source machine uses the canonical endmarker alphabet.  The target machine uses the same input
alphabet and stores one source symbol, one finite clock digit, immutable boundary bits, the
simulated-head mark, and six one-shot sweep bits in each work symbol.

The phase protocol is:

* convert the canonical input to work symbols and return to the simulated head;
* perform one genuine source transition in `ready`/`mark`;
* make a guarded left sweep;
* normalize all one-shot bits by a right sweep followed by a left sweep;
* increment the least-significant-digit-first clock without wrapping;
* return left and scan back to the unique simulated-head mark.

Every sweep that could otherwise be clamped on a malformed tape changes a one-shot bit before
moving.  Re-reading the same physical cell therefore cannot continue in the same sweep phase: it
either halts or, for the intentional initialization endpoint, advances to the return phase.  This
is the local mechanism used by the later global potential proof.  The present file only supplies
the machine, exact transition equations, and local acceptance/clock facts.
-/

open Classical

namespace LBA.AcyclicClock

variable {T Γ Λ : Type*}

/-- Tape alphabet of the source endmarker machine. -/
public abbrev SourceAlpha (T Γ : Type*) :=
  LBA.EndAlpha T Γ

public instance SourceAlpha.instNonempty : Nonempty (SourceAlpha T Γ) :=
  ⟨.inr false⟩

section

variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- A clock digit.  Its cardinality is exactly
`2 * |SourceAlpha T Γ| * |Λ|`, up to commutativity of multiplication. -/
public abbrev ClockDigit (T Γ Λ : Type*) [Fintype T] [Fintype Γ] [Fintype Λ] :=
  LBA.StrictClockLayering.ClockDigit
    (Γ := SourceAlpha T Γ) (Λ := Λ)

/-- Canonical finite numbering of clock digits. -/
public def clockCodec :
    RowNumeral.DigitCodec (ClockDigit T Γ Λ) :=
  LBA.StrictClockLayering.clockCodec (SourceAlpha T Γ) Λ

@[simp]
public theorem clockCodec_radix :
    (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).radix =
      LBA.StrictClockLayering.clockRadix
        (Γ := SourceAlpha T Γ) (Λ := Λ) :=
  LBA.StrictClockLayering.clockCodec_radix

/-- The zero clock digit, using the source machine's initial state as the required inhabitant. -/
public def clockZero
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    ClockDigit T Γ Λ :=
  letI : Nonempty Λ := ⟨M.initial⟩
  (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).zero

/-- One target work cell.

The boundary bits are installed once during canonical initialization.  The other Boolean fields
are one-shot guards: a sweep may change such a bit before moving, and the same phase refuses to
move again from the changed value.
-/
public structure WorkCell (T Γ Λ : Type*)
    [Fintype T] [Fintype Γ] [Fintype Λ] where
  src : SourceAlpha T Γ
  digit : ClockDigit T Γ Λ
  left : Bool
  right : Bool
  mark : Bool
  init : Bool
  seek : Bool
  norm : Bool
  carry : Bool
  post : Bool
  scan : Bool
  deriving DecidableEq

public noncomputable instance WorkCell.instFintype :
    Fintype (WorkCell T Γ Λ) :=
  Fintype.ofInjective
    (fun cell =>
      (cell.src, cell.digit, cell.left, cell.right, cell.mark, cell.init,
        cell.seek, cell.norm, cell.carry, cell.post, cell.scan))
    (by
      intro left right h
      cases left
      cases right
      simp_all)

/-- The target is again a canonical endmarker LBA, now with `WorkCell` as its work alphabet. -/
public abbrev TapeAlpha (T Γ Λ : Type*)
    [Fintype T] [Fintype Γ] [Fintype Λ] :=
  LBA.EndAlpha T (WorkCell T Γ Λ)

/-- Control phases of the operational clock macro. -/
public inductive State (Λ : Type*) where
  | initFirst
  | initSweep
  | initBack
  | ready (source : Λ)
  | mark (source : Λ)
  | seek (source : Λ)
  | cleanR (source : Λ)
  | cleanL (source : Λ)
  | carry (source : Λ)
  | carryCheck (source : Λ)
  | returnL (source : Λ)
  | findMark (source : Λ)
  deriving DecidableEq, Fintype

/-- Embed one work cell into the target endmarker alphabet. -/
public def workSymbol (cell : WorkCell T Γ Λ) : TapeAlpha T Γ Λ :=
  .inl (some (.inr cell))

/-- View a target symbol as an already converted work cell. -/
public def asWork : TapeAlpha T Γ Λ → Option (WorkCell T Γ Λ)
  | .inl (some (.inr cell)) => some cell
  | _ => none

/-- View an unconverted target symbol as the corresponding source symbol. -/
public def asRawSource : TapeAlpha T Γ Λ → Option (SourceAlpha T Γ)
  | .inr boundary => some (.inr boundary)
  | .inl none => some (.inl none)
  | .inl (some (.inl input)) => some (.inl (some (.inl input)))
  | .inl (some (.inr _)) => none

@[simp]
public theorem asWork_workSymbol (cell : WorkCell T Γ Λ) :
    asWork (workSymbol cell) = some cell := rfl

@[simp]
public theorem asRawSource_workSymbol (cell : WorkCell T Γ Λ) :
    asRawSource (workSymbol cell) = none := rfl

/-- Clear every one-shot field while preserving source data, the clock, boundaries, and mark. -/
public def WorkCell.clearTransient (cell : WorkCell T Γ Λ) : WorkCell T Γ Λ :=
  { cell with
    init := false
    seek := false
    norm := false
    carry := false
    post := false
    scan := false }

/-- The cell written by the left-to-right normalization sweep. -/
public def WorkCell.normalizedRight (cell : WorkCell T Γ Λ) : WorkCell T Γ Λ :=
  { cell.clearTransient with norm := true }

/-- The cell written while returning left after clock increment. -/
public def WorkCell.posted (cell : WorkCell T Γ Λ) : WorkCell T Γ Λ :=
  { cell with carry := false, post := true }

/-- The cell written while scanning right for the simulated-head mark. -/
public def WorkCell.scanned (cell : WorkCell T Γ Λ) : WorkCell T Γ Λ :=
  { cell with post := false, scan := true }

/-- A freshly converted work cell. -/
public def freshCell (zero : ClockDigit T Γ Λ)
    (src : SourceAlpha T Γ) (left mark : Bool) :
    WorkCell T Γ Λ where
  src := src
  digit := zero
  left := left
  right := false
  mark := mark
  init := true
  seek := false
  norm := false
  carry := false
  post := false
  scan := false

/-- The source-step half of the macro.  The old mark is cleared before the physical target head is
reached.  Physical boundary clamping therefore implements source-head clamping without a separate
case split. -/
public def sourceChoice
    (cell : WorkCell T Γ Λ)
    (move : Λ × SourceAlpha T Γ × DLBA.Dir) :
    State Λ × TapeAlpha T Γ Λ × DLBA.Dir :=
  let written : WorkCell T Γ Λ :=
    { cell.clearTransient with src := move.2.1, mark := false }
  (.mark move.1, workSymbol written, move.2.2)

/-- Transition relation of the operational clock compiler. -/
public noncomputable def transition
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    State Λ → TapeAlpha T Γ Λ →
      Set (State Λ × TapeAlpha T Γ Λ × DLBA.Dir) :=
  letI : Nonempty Λ := ⟨M.initial⟩
  let zero := clockZero M
  fun state symbol =>
    match state, symbol with
    | .initFirst, .inr false =>
        {(.initSweep,
          workSymbol (freshCell zero (LBA.leftMark (T := T) (Γ := Γ)) true true),
          .right)}
    | .initFirst, _ => ∅

    | .initSweep, .inl (some (.inr cell)) =>
        if cell.init then
          {(.initBack, workSymbol { cell with right := true }, .stay)}
        else ∅
    | .initSweep, .inr boundary =>
        {(.initSweep, workSymbol (freshCell zero (.inr boundary) false false), .right)}
    | .initSweep, .inl none =>
        {(.initSweep, workSymbol (freshCell zero (.inl none) false false), .right)}
    | .initSweep, .inl (some (.inl input)) =>
        {(.initSweep,
          workSymbol (freshCell zero (.inl (some (.inl input))) false false), .right)}

    | .initBack, .inl (some (.inr cell)) =>
        if cell.left then
          if cell.init then
            {(.ready M.initial, workSymbol cell.clearTransient, .stay)}
          else ∅
        else if cell.init then
          {(.initBack, workSymbol { cell with init := false }, .left)}
        else ∅
    | .initBack, _ => ∅

    | .ready source, .inl (some (.inr cell)) =>
        if cell.mark then
          sourceChoice cell '' M.transition source cell.src
        else ∅
    | .ready _, _ => ∅

    | .mark source, .inl (some (.inr cell)) =>
        {(.seek source,
          workSymbol { cell.clearTransient with mark := true }, .stay)}
    | .mark _, _ => ∅

    | .seek source, .inl (some (.inr cell)) =>
        if cell.left then
          {(.cleanR source, workSymbol cell, .stay)}
        else if cell.seek then ∅
        else
          {(.seek source, workSymbol { cell with seek := true }, .left)}
    | .seek _, _ => ∅

    | .cleanR source, .inl (some (.inr cell)) =>
        if cell.norm then ∅
        else if cell.right then
          {(.cleanL source, workSymbol cell.normalizedRight, .stay)}
        else
          {(.cleanR source, workSymbol cell.normalizedRight, .right)}
    | .cleanR _, _ => ∅

    | .cleanL source, .inl (some (.inr cell)) =>
        if cell.left then
          if cell.norm then
            {(.carry source, workSymbol cell.clearTransient, .stay)}
          else ∅
        else if cell.norm then
          {(.cleanL source, workSymbol cell.clearTransient, .left)}
        else ∅
    | .cleanL _, _ => ∅

    | .carry source, .inl (some (.inr cell)) =>
        if cell.carry then ∅
        else
          match (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next cell.digit with
          | some next =>
              {(.returnL source, workSymbol { cell with digit := next }, .stay)}
          | none =>
              if cell.right then ∅
              else
                {(.carryCheck source,
                  workSymbol { cell with digit := zero, carry := true }, .right)}
    | .carry _, _ => ∅

    | .carryCheck source, .inl (some (.inr cell)) =>
        if cell.carry then ∅
        else {(.carry source, workSymbol cell, .stay)}
    | .carryCheck _, _ => ∅

    | .returnL source, .inl (some (.inr cell)) =>
        if cell.left then
          {(.findMark source, workSymbol cell.clearTransient, .stay)}
        else if cell.post then ∅
        else
          {(.returnL source, workSymbol cell.posted, .left)}
    | .returnL _, _ => ∅

    | .findMark source, .inl (some (.inr cell)) =>
        if cell.mark then
          {(.ready source, workSymbol cell.clearTransient, .stay)}
        else if cell.right then ∅
        else if cell.scan then ∅
        else
          {(.findMark source, workSymbol cell.scanned, .right)}
    | .findMark _, _ => ∅

/-- The concrete target machine.  Only `ready` source states can accept. -/
public noncomputable def machine
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    LBA.Machine (TapeAlpha T Γ Λ) (State Λ) where
  transition := transition M
  accept
    | .ready source => M.accept source
    | _ => false
  initial := .initFirst

/-! ## Exact local transition equations -/

@[simp]
public theorem transition_initFirst_leftMark
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    transition M .initFirst (LBA.leftMark (T := T) (Γ := WorkCell T Γ Λ)) =
      {(.initSweep,
        workSymbol
          (freshCell
            (clockZero M)
            (LBA.leftMark (T := T) (Γ := Γ)) true true),
        .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_initFirst_notLeft
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (symbol : TapeAlpha T Γ Λ)
    (h : symbol ≠ LBA.leftMark (T := T) (Γ := WorkCell T Γ Λ)) :
    transition M .initFirst symbol = ∅ := by
  rcases symbol with (_ | boundary)
  · rfl
  · cases boundary <;> simp_all [transition]

@[simp]
public theorem transition_initSweep_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (cell : WorkCell T Γ Λ) :
    transition M .initSweep (workSymbol cell) =
      if cell.init then
        {(.initBack, workSymbol { cell with right := true }, .stay)}
      else ∅ := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_initSweep_boundary
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (boundary : Bool) :
    transition M .initSweep (.inr boundary) =
      {(.initSweep,
        workSymbol (freshCell (clockZero M) (.inr boundary) false false),
        .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_initSweep_input
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (input : T) :
    transition M .initSweep (.inl (some (.inl input))) =
      {(.initSweep,
        workSymbol
          (freshCell (clockZero M) (.inl (some (.inl input))) false false),
        .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_initBack_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (cell : WorkCell T Γ Λ) :
    transition M .initBack (workSymbol cell) =
      if cell.left then
        if cell.init then
          {(.ready M.initial, workSymbol cell.clearTransient, .stay)}
        else ∅
      else if cell.init then
        {(.initBack, workSymbol { cell with init := false }, .left)}
      else ∅ := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_ready_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.ready source) (workSymbol cell) =
      if cell.mark then
        sourceChoice cell '' M.transition source cell.src
      else ∅ := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_mark_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.mark source) (workSymbol cell) =
      {(.seek source,
        workSymbol { cell.clearTransient with mark := true }, .stay)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_cleanR_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.cleanR source) (workSymbol cell) =
      if cell.norm then ∅
      else if cell.right then
        {(.cleanL source, workSymbol cell.normalizedRight, .stay)}
      else
        {(.cleanR source, workSymbol cell.normalizedRight, .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_cleanL_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.cleanL source) (workSymbol cell) =
      if cell.left then
        if cell.norm then
          {(.carry source, workSymbol cell.clearTransient, .stay)}
        else ∅
      else if cell.norm then
        {(.cleanL source, workSymbol cell.clearTransient, .left)}
      else ∅ := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_carryCheck_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.carryCheck source) (workSymbol cell) =
      if cell.carry then ∅
      else {(.carry source, workSymbol cell, .stay)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_returnL_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.returnL source) (workSymbol cell) =
      if cell.left then
        {(.findMark source, workSymbol cell.clearTransient, .stay)}
      else if cell.post then ∅
      else
        {(.returnL source, workSymbol cell.posted, .left)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_findMark_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.findMark source) (workSymbol cell) =
      if cell.mark then
        {(.ready source, workSymbol cell.clearTransient, .stay)}
      else if cell.right then ∅
      else if cell.scan then ∅
      else
        {(.findMark source, workSymbol cell.scanned, .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

@[simp]
public theorem transition_carry_work
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) :
    transition M (.carry source) (workSymbol cell) =
      if cell.carry then ∅
      else
        match (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next cell.digit with
        | some next =>
            {(.returnL source, workSymbol { cell with digit := next }, .stay)}
        | none =>
            if cell.right then ∅
            else
              {(.carryCheck source,
                workSymbol
                  { cell with
                    digit := clockZero M
                    carry := true },
                .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rfl

/-- A nonmaximal clock digit is incremented locally and enters the guarded return sweep. -/
public theorem transition_carry_of_next
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ) (next : ClockDigit T Γ Λ)
    (hcarry : cell.carry = false)
    (hnext : (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next cell.digit =
      some next) :
    transition M (.carry source) (workSymbol cell) =
      {(.returnL source, workSymbol { cell with digit := next }, .stay)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rw [transition_carry_work, if_neg (by simpa using hcarry), hnext]

/-- The maximum digit at the installed right boundary has no successor: the clock never wraps. -/
public theorem transition_carry_max_right
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ)
    (hcarry : cell.carry = false)
    (hmax : (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next cell.digit = none)
    (hright : cell.right = true) :
    transition M (.carry source) (workSymbol cell) = ∅ := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rw [transition_carry_work, if_neg (by simpa using hcarry), hmax,
    if_pos (by simpa using hright)]

/-- A maximal non-right digit is reset to zero, marked once, and moves right to a guard check. -/
public theorem transition_carry_max_notRight
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ)
    (hcarry : cell.carry = false)
    (hmax : (clockCodec (T := T) (Γ := Γ) (Λ := Λ)).next cell.digit = none)
    (hright : cell.right = false) :
    transition M (.carry source) (workSymbol cell) =
      {(.carryCheck source,
        workSymbol
          { cell with
            digit := clockZero M
            carry := true },
        .right)} := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rw [transition_carry_work, if_neg (by simpa using hcarry), hmax,
    if_neg (by simpa using hright)]

/-- Exact acceptance shape: intermediate protocol states never accept. -/
public theorem machine_accept_eq_true_iff
    (M : LBA.Machine (SourceAlpha T Γ) Λ) (state : State Λ) :
    (machine M).accept state = true ↔
      ∃ source, state = .ready source ∧ M.accept source = true := by
  cases state <;> simp [machine]

/-- Every enabled source move is offered by `ready` on a marked work cell. -/
public theorem sourceChoice_mem_transition_ready
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    (source : Λ) (cell : WorkCell T Γ Λ)
    (hmark : cell.mark = true)
    {move : Λ × SourceAlpha T Γ × DLBA.Dir}
    (hmove : move ∈ M.transition source cell.src) :
    sourceChoice cell move ∈
      transition M (.ready source) (workSymbol cell) := by
  letI : Nonempty Λ := ⟨M.initial⟩
  rw [transition_ready_work, if_pos (by simpa using hmark)]
  exact ⟨move, hmove, rfl⟩

/-- The write-and-physical-move half-step offered by `ready`.

The target ends in `.mark`; installing the new simulated-head mark and completing the clock macro
are separate later phases.
-/
public theorem step_ready_half_of_source_move
    (M : LBA.Machine (SourceAlpha T Γ) Λ)
    {n : ℕ} (source : Λ)
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (cell : WorkCell T Γ Λ)
    (hread : tape.read = workSymbol cell)
    (hmark : cell.mark = true)
    {move : Λ × SourceAlpha T Γ × DLBA.Dir}
    (hmove : move ∈ M.transition source cell.src) :
    LBA.Step (machine M)
      ⟨.ready source, tape⟩
      ⟨.mark move.1,
        (tape.write (workSymbol
          { cell.clearTransient with src := move.2.1, mark := false })).moveHead move.2.2⟩ := by
  refine ⟨.mark move.1,
    workSymbol { cell.clearTransient with src := move.2.1, mark := false },
    move.2.2, ?_, rfl⟩
  change
    (.mark move.1,
      workSymbol { cell.clearTransient with src := move.2.1, mark := false },
      move.2.2) ∈ transition M (.ready source) tape.read
  rw [hread]
  exact sourceChoice_mem_transition_ready M source cell hmark hmove

/-- The target machine starts in the canonical conversion phase. -/
@[simp]
public theorem machine_initial
    (M : LBA.Machine (SourceAlpha T Γ) Λ) :
    (machine M).initial = .initFirst := rfl

end

end LBA.AcyclicClock

end
