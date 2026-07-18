module

public import Langlib.Automata.LinearBounded.BoundedCrossingEncodedMembership
public import Langlib.Automata.LinearBounded.BoundedCrossingRegularCharacterization
public import Langlib.Automata.LinearBounded.BoundedCrossingTransport
public import Langlib.Automata.LinearBounded.SimpleTraceCrossingBound
public import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

@[expose]
public section

/-!
# One numeric code for all finite LBA signatures and crossing caps

The fixed-signature checker in `BoundedCrossingEncodedMembership` chooses its finite work and
state types before the program is constructed.  This file begins the genuinely uniform version:
the work-alphabet cardinality, state cardinality, and crossing cap are runtime fields of one raw
code.

The code contains only local finite machine data.  A transition entry records a source state,
the scanned symbol, a target state, the written symbol, and a direction.  The queried word is a
separate runtime input; the code has no word-dependent field or semantic membership oracle.

Work symbols and states use natural-number indices.  Out-of-range transition entries and
accepting indices are ignored.  For a positive state count, the raw initial index is normalized
modulo that count.  A zero state count denotes the empty language: this is the honest total
extension because an `LBA.Machine _ State` cannot exist when `State` is empty (it contains an
`initial : State`).  A zero work-symbol count is fully supported.
-/

namespace LBA.BoundedCrossing.VaryingEncodedMembership

universe u v

variable {Terminal : Type u}

/-- Numeric presentation of the three head directions. -/
def directionEquivFin : DLBA.Dir ≃ Fin 3 where
  toFun
    | .left => 0
    | .right => 1
    | .stay => 2
  invFun direction :=
    if direction.val = 0 then .left
    else if direction.val = 1 then .right
    else .stay
  left_inv direction := by cases direction <;> rfl
  right_inv direction := by
    apply Fin.ext
    fin_cases direction <;> rfl

noncomputable instance : Primcodable DLBA.Dir :=
  Primcodable.ofEquiv (Fin 3) directionEquivFin

/-- A runtime tape symbol.  Natural work indices are validated against the code's work count. -/
abbrev RawSymbol (Terminal : Type u) := LBA.EndAlpha Terminal Nat

/-- A local transition-table row, stored definitionally as ordinary primitive-codable data.
Keeping the representation as a product avoids a transported `Primcodable` instance and makes
the uniform evaluator's structural computability proof normalize predictably. -/
abbrev TransitionEntry (Terminal : Type u) :=
  Nat × RawSymbol Terminal × Nat × RawSymbol Terminal × DLBA.Dir

namespace TransitionEntry

def source (entry : TransitionEntry Terminal) : Nat := entry.1
def scanned (entry : TransitionEntry Terminal) : RawSymbol Terminal := entry.2.1
def target (entry : TransitionEntry Terminal) : Nat := entry.2.2.1
def written (entry : TransitionEntry Terminal) : RawSymbol Terminal := entry.2.2.2.1
def direction (entry : TransitionEntry Terminal) : DLBA.Dir := entry.2.2.2.2

end TransitionEntry

/-- Decidable equality assembled explicitly from the inside out.

The five-way product exceeds Lean's default instance-search depth when it is left entirely to
synthesis, even though every component has decidable equality. -/
instance (priority := high) instDecidableEqTransitionEntry [DecidableEq Terminal] :
    DecidableEq (TransitionEntry Terminal) := by
  letI : DecidableEq (RawSymbol Terminal × DLBA.Dir) := instDecidableEqProd
  letI : DecidableEq (Nat × (RawSymbol Terminal × DLBA.Dir)) := instDecidableEqProd
  letI : DecidableEq
      (RawSymbol Terminal × (Nat × (RawSymbol Terminal × DLBA.Dir))) :=
    instDecidableEqProd
  exact instDecidableEqProd

instance (priority := high) instBEqTransitionEntry [DecidableEq Terminal] :
    BEq (TransitionEntry Terminal) := instBEqOfDecidableEq

instance (priority := high) instLawfulBEqTransitionEntry [DecidableEq Terminal] :
    LawfulBEq (TransitionEntry Terminal) := instLawfulBEq

/--
One raw code for all finite work/state cardinalities and all crossing caps.

The fields, in order, are work count, state count, initial-state index, crossing cap, accepting
indices, and local transition entries.  The nested-product representation deliberately inherits
its `Primcodable` instance without a bespoke serialization layer.
-/
abbrev Code (Terminal : Type u) :=
  Nat × Nat × Nat × Nat × List Nat × List (TransitionEntry Terminal)

namespace Code

def workCount (code : Code Terminal) : Nat := code.1
def stateCount (code : Code Terminal) : Nat := code.2.1
def initialIndex (code : Code Terminal) : Nat := code.2.2.1
def crossingCap (code : Code Terminal) : Nat := code.2.2.2.1
def accepting (code : Code Terminal) : List Nat := code.2.2.2.2.1
def transitions (code : Code Terminal) : List (TransitionEntry Terminal) :=
  code.2.2.2.2.2

end Code

/-! ## Runtime validity and conversion to exact finite types -/

/-- The only runtime-dependent tape-symbol validity condition is the work-symbol bound. -/
def SymbolValid (workCount : Nat) : RawSymbol Terminal → Prop
  | .inl (some (.inr work)) => work < workCount
  | _ => True

instance (workCount : Nat) : DecidablePred (SymbolValid (Terminal := Terminal) workCount) :=
  fun symbol => by
    unfold SymbolValid
    split <;> infer_instance

/-- Encode an exactly bounded work symbol as its raw natural index. -/
def encodeSymbol {workCount : Nat} :
    LBA.EndAlpha Terminal (Fin workCount) → RawSymbol Terminal
  | .inl none => .inl none
  | .inl (some (.inl terminal)) => .inl (some (.inl terminal))
  | .inl (some (.inr work)) => .inl (some (.inr work.val))
  | .inr marker => .inr marker

theorem symbolValid_encodeSymbol {workCount : Nat}
    (symbol : LBA.EndAlpha Terminal (Fin workCount)) :
    SymbolValid workCount (encodeSymbol symbol) := by
  rcases symbol with (none | (terminal | work)) | marker <;>
    simp [encodeSymbol, SymbolValid]

/-- Decode a raw symbol after proving its work index is in range. -/
def decodeSymbol {workCount : Nat} (symbol : RawSymbol Terminal)
    (valid : SymbolValid workCount symbol) :
    LBA.EndAlpha Terminal (Fin workCount) :=
  match symbol with
  | .inl none => .inl none
  | .inl (some (.inl terminal)) => .inl (some (.inl terminal))
  | .inl (some (.inr work)) => .inl (some (.inr ⟨work, valid⟩))
  | .inr marker => .inr marker

@[simp] theorem decodeSymbol_encodeSymbol {workCount : Nat}
    (symbol : LBA.EndAlpha Terminal (Fin workCount)) :
    decodeSymbol (encodeSymbol symbol) (symbolValid_encodeSymbol symbol) = symbol := by
  rcases symbol with (none | (terminal | work)) | marker <;> rfl

@[simp] theorem encodeSymbol_decodeSymbol {workCount : Nat}
    (symbol : RawSymbol Terminal) (valid : SymbolValid workCount symbol) :
    encodeSymbol (decodeSymbol symbol valid) = symbol := by
  rcases symbol with (none | (terminal | work)) | marker <;> rfl

theorem decodeSymbol_eq_of_eq_encodeSymbol {workCount : Nat}
    (raw : RawSymbol Terminal) (valid : SymbolValid workCount raw)
    (symbol : LBA.EndAlpha Terminal (Fin workCount))
    (heq : raw = encodeSymbol symbol) :
    decodeSymbol raw valid = symbol := by
  subst raw
  exact decodeSymbol_encodeSymbol symbol

/-- Decode one valid raw transition row to the exact runtime finite signature. -/
def decodeEntry (code : Code Terminal) (entry : TransitionEntry Terminal)
    (sourceValid : entry.source < code.stateCount)
    (scannedValid : SymbolValid code.workCount entry.scanned)
    (targetValid : entry.target < code.stateCount)
    (writtenValid : SymbolValid code.workCount entry.written) :
    Fin code.stateCount × LBA.EndAlpha Terminal (Fin code.workCount) ×
      Fin code.stateCount × LBA.EndAlpha Terminal (Fin code.workCount) × DLBA.Dir :=
  (⟨entry.source, sourceValid⟩, decodeSymbol entry.scanned scannedValid,
    ⟨entry.target, targetValid⟩, decodeSymbol entry.written writtenValid, entry.direction)

/-- The machine denoted by a positive-state-count code.  Invalid local rows are ignored. -/
def toMachine (code : Code Terminal) (stateCountPositive : 0 < code.stateCount) :
    LBA.Machine (LBA.EndAlpha Terminal (Fin code.workCount)) (Fin code.stateCount) where
  initial := ⟨code.initialIndex % code.stateCount, Nat.mod_lt _ stateCountPositive⟩
  accept state := decide (state.val ∈ code.accepting)
  transition state symbol := {move |
    ∃ entry ∈ code.transitions,
      ∃ (sourceValid : entry.source < code.stateCount)
        (scannedValid : SymbolValid code.workCount entry.scanned)
        (targetValid : entry.target < code.stateCount)
        (writtenValid : SymbolValid code.workCount entry.written),
        decodeEntry code entry sourceValid scannedValid targetValid writtenValid =
          (state, symbol, move.1, move.2.1, move.2.2)}

@[simp] theorem toMachine_initial_val (code : Code Terminal)
    (stateCountPositive : 0 < code.stateCount) :
    (toMachine code stateCountPositive).initial.val =
      code.initialIndex % code.stateCount := rfl

@[simp] theorem toMachine_accept (code : Code Terminal)
    (stateCountPositive : 0 < code.stateCount) (state : Fin code.stateCount) :
    (toMachine code stateCountPositive).accept state = true ↔
      state.val ∈ code.accepting := by
  simp [toMachine]

/-! ## Total raw semantics -/

/-- The bounded-crossing language denoted by every raw code; zero states denotes `∅`. -/
noncomputable def languageOf (code : Code Terminal) : Language Terminal :=
  if stateCountPositive : 0 < code.stateCount then
    LanguageWithBound (toMachine code stateCountPositive) code.crossingCap
  else
    fun _ => False

@[simp] theorem languageOf_of_stateCount_eq_zero (code : Code Terminal)
    (hzero : code.stateCount = 0) : languageOf code = (fun _ => False) := by
  simp [languageOf, hzero]

theorem languageOf_of_stateCount_pos (code : Code Terminal)
    (hpos : 0 < code.stateCount) :
    languageOf code = LanguageWithBound (toMachine code hpos) code.crossingCap := by
  simp only [languageOf, dif_pos hpos]

/-! ## Explicit numeric search space -/

/-- All lists of one exact length over a supplied alphabet. -/
def listsOfLength {α : Type v} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | length + 1 =>
      (listsOfLength alphabet length).flatMap fun tail =>
        alphabet.map fun head => head :: tail

/-- All lists of length at most `bound`.  This includes `[[]]` even for an empty alphabet. -/
def listsUpToLength {α : Type v} (alphabet : List α) (bound : Nat) : List (List α) :=
  (List.range (bound + 1)).flatMap (listsOfLength alphabet)

/-- A safe simple-trace search budget on a canonical endmarker input.

There are `|word| + 1` physical boundaries.  The tape alphabet has
`|Terminal| + workCount + 3` symbols (blank, inputs, work symbols, and two markers). -/
def traceBudget [Fintype Terminal] (code : Code Terminal) (word : List Terminal) : Nat :=
  (code.stateCount * (Fintype.card Terminal + code.workCount + 3)) *
    ((word.length + 1) * code.crossingCap + 1)

theorem mem_listsOfLength {α : Type v} (alphabet : List α) (length : Nat)
    (items : List α) :
    items ∈ listsOfLength alphabet length ↔
      items.length = length ∧ ∀ item ∈ items, item ∈ alphabet := by
  induction length generalizing items with
  | zero =>
      simp only [listsOfLength, List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨rfl, by simp⟩
      · rintro ⟨hlength, -⟩
        exact List.length_eq_zero_iff.mp hlength
  | succ length ih =>
      simp only [listsOfLength, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨tail, htail, head, hhead, rfl⟩
        obtain ⟨hlength, hmem⟩ := (ih tail).mp htail
        exact ⟨by simp [hlength], fun item hitem => by
          rcases List.mem_cons.mp hitem with rfl | hitem
          · exact hhead
          · exact hmem item hitem⟩
      · rintro ⟨hlength, hmem⟩
        cases items with
        | nil => simp at hlength
        | cons head tail =>
            refine ⟨tail, (ih tail).mpr ⟨by simpa using hlength,
              fun item hitem => hmem item (by simp [hitem])⟩,
              head, hmem head (by simp), rfl⟩

theorem mem_listsUpToLength {α : Type v} (alphabet : List α) (bound : Nat)
    (items : List α) :
    items ∈ listsUpToLength alphabet bound ↔
      items.length ≤ bound ∧ ∀ item ∈ items, item ∈ alphabet := by
  simp only [listsUpToLength, List.mem_flatMap, mem_listsOfLength]
  constructor
  · rintro ⟨length, hlength, hitemsLength, hitems⟩
    exact ⟨by have := List.mem_range.mp hlength; omega, hitems⟩
  · rintro ⟨hlength, hitems⟩
    exact ⟨items.length, List.mem_range.mpr (by omega), rfl, hitems⟩

/-! ## Schedule replay with a latest-write-wins override log -/

/-- Endpoint-clamped movement on raw natural head indices.  `last` is the final cell index. -/
def moveHeadIndex (last head : Nat) : DLBA.Dir → Nat
  | .stay => head
  | .left => if 0 < head then head - 1 else head
  | .right => if head < last then head + 1 else head

/-- A newest-first write override: physical cell index and its current raw symbol. -/
abbrev Override (Terminal : Type u) := Nat × RawSymbol Terminal

/-- Runtime replay state: control state, head, newest-first writes, and newest-first head history.
The head history always includes the initial head, so its adjacent pairs correspond one-for-one
to executed machine steps. -/
abbrev ExecState (Terminal : Type u) :=
  Nat × Nat × List (Override Terminal) × List Nat

/-- Shared packed domain for the local replay predicates. -/
abbrev EntryInput (Terminal : Type u) :=
  Code Terminal × List Terminal × ExecState Terminal × TransitionEntry Terminal

namespace ExecState

def state (exec : ExecState Terminal) : Nat := exec.1
def head (exec : ExecState Terminal) : Nat := exec.2.1
def overrides (exec : ExecState Terminal) : List (Override Terminal) := exec.2.2.1
def headsRev (exec : ExecState Terminal) : List Nat := exec.2.2.2

end ExecState

/-- Search a newest-first override log. -/
def lookupOverride [DecidableEq Terminal]
    (index : Nat) : List (Override Terminal) → Option (RawSymbol Terminal)
  | [] => none
  | (writtenIndex, symbol) :: rest =>
      if writtenIndex = index then some symbol else lookupOverride index rest

/-- Read one physical cell through an override log, falling back to the canonical initial tape. -/
def readCell [DecidableEq Terminal] (word : List Terminal)
    (overrides : List (Override Terminal)) (index : Nat) : Option (RawSymbol Terminal) :=
  (lookupOverride index overrides).orElse fun _ =>
    (LBA.endWord (Work := Nat) word)[index]?

/-- Read the current raw symbol: newest write wins, then the canonical initial tape. -/
def readCurrent [DecidableEq Terminal] (word : List Terminal)
    (exec : ExecState Terminal) : Option (RawSymbol Terminal) :=
  readCell word exec.overrides exec.head

/-- Boolean runtime work-symbol validity. -/
def workIndex? : RawSymbol Terminal → Option Nat
  | .inl (some (.inr work)) => some work
  | _ => none

def symbolValidBool (workCount : Nat) (symbol : RawSymbol Terminal) : Bool :=
  match workIndex? symbol with
  | none => true
  | some work => decide (work < workCount)

theorem symbolValidBool_eq_true_iff (workCount : Nat) (symbol : RawSymbol Terminal) :
    symbolValidBool workCount symbol = true ↔ SymbolValid workCount symbol := by
  rcases symbol with (none | (terminal | work)) | marker <;>
    simp [symbolValidBool, workIndex?, SymbolValid]

/-- Initial raw replay state.  It is total at state count zero; membership rejects that case. -/
def initialExec (code : Code Terminal) : ExecState Terminal :=
  (code.initialIndex % code.stateCount, 0, [], [0])

/-- Executable local enabling condition for a chosen row. -/
def entryEnabledBool [DecidableEq Terminal] (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal) (entry : TransitionEntry Terminal) : Bool :=
  entry.source = exec.state && entry.target < code.stateCount &&
      symbolValidBool code.workCount entry.scanned &&
      symbolValidBool code.workCount entry.written &&
      readCurrent word exec = some entry.scanned

/-- Execute one chosen local row.  A successful step conses the write at the old head before
moving, exactly matching `BoundedTape.write` followed by `moveHead`. -/
def applyEntry? [DecidableEq Terminal] (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal) (entry : TransitionEntry Terminal) :
    Option (ExecState Terminal) :=
  bif entryEnabledBool code word exec entry then
    let nextHead := moveHeadIndex (word.length + 1) exec.head entry.direction
    some (entry.target, nextHead,
      (exec.head, entry.written) :: exec.overrides, nextHead :: exec.headsRev)
  else
    none

/-- Deterministically replay a schedule from an arbitrary current raw execution state. -/
def replayFrom [DecidableEq Terminal] (code : Code Terminal) (word : List Terminal) :
    ExecState Terminal → List (TransitionEntry Terminal) → Option (ExecState Terminal)
  | exec, [] => some exec
  | exec, entry :: rest =>
      (applyEntry? code word exec entry).bind fun next => replayFrom code word next rest

def replayFoldStep? [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (current : Option (ExecState Terminal)) (entry : TransitionEntry Terminal) :
    Option (ExecState Terminal) :=
  current.bind fun exec => applyEntry? code word exec entry

/-- Deterministically replay a schedule of chosen transition-table rows from the canonical
initial state. -/
def replaySchedule [DecidableEq Terminal] (code : Code Terminal) (word : List Terminal)
    (schedule : List (TransitionEntry Terminal)) : Option (ExecState Terminal) :=
  schedule.foldl (replayFoldStep? code word) (some (initialExec code))

@[simp] theorem replayFrom_nil [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (exec : ExecState Terminal) :
    replayFrom code word exec [] = some exec := rfl

@[simp] theorem replayFrom_cons [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (exec : ExecState Terminal)
    (entry : TransitionEntry Terminal) (rest : List (TransitionEntry Terminal)) :
    replayFrom code word exec (entry :: rest) =
      (applyEntry? code word exec entry).bind fun next => replayFrom code word next rest := rfl

private theorem replayFoldStep?_none [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (schedule : List (TransitionEntry Terminal)) :
    schedule.foldl (replayFoldStep? code word) none = none := by
  induction schedule with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons, replayFoldStep?, Option.bind_none]
      exact ih

private theorem replayFrom_eq_foldl [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal) (schedule : List (TransitionEntry Terminal)) :
    replayFrom code word exec schedule =
      schedule.foldl (replayFoldStep? code word) (some exec) := by
  induction schedule generalizing exec with
  | nil => rfl
  | cons entry rest ih =>
      simp only [replayFrom_cons, List.foldl_cons, replayFoldStep?, Option.bind_some]
      cases hstep : applyEntry? code word exec entry with
      | none =>
          simp only [Option.bind_none]
          exact (replayFoldStep?_none code word rest).symm
      | some next =>
          simp only [Option.bind_some]
          exact ih next

theorem replaySchedule_eq_replayFrom [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (schedule : List (TransitionEntry Terminal)) :
    replaySchedule code word schedule =
      replayFrom code word (initialExec code) schedule := by
  rw [replaySchedule, replayFrom_eq_foldl]

/-- Raw boundary-crossing predicate on a pair of head indices. -/
def headsCrossBoundaryBool (boundary source target : Nat) : Bool :=
  (decide (source ≤ boundary) && decide (boundary < target)) ||
    (decide (boundary < source) && decide (target ≤ boundary))

/-- Count crossings in one chronological list of head positions. -/
def crossingCountHeads (boundary : Nat) : List Nat → Nat
  | [] => 0
  | [_] => 0
  | source :: target :: rest =>
      (if headsCrossBoundaryBool boundary source target then 1 else 0) +
        crossingCountHeads boundary (target :: rest)

/-- Count crossings from the newest-first runtime head history by reversing it chronologically. -/
def crossingCountHeadsRev (boundary : Nat) (headsRev : List Nat) : Nat :=
  crossingCountHeads boundary headsRev.reverse

/-- Verify final acceptance and the crossing cap for a successfully replayed schedule. -/
def successfulExecAcceptsBool (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal) : Bool :=
  decide (exec.state ∈ code.accepting) &&
    (List.range (word.length + 1)).all fun boundary =>
      decide (crossingCountHeadsRev boundary exec.headsRev ≤ code.crossingCap)

/-- Verify one candidate transition-entry schedule. -/
def scheduleAcceptsBool [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (schedule : List (TransitionEntry Terminal)) : Bool :=
  decide (0 < code.stateCount) &&
    schedule.all (fun entry => decide (entry ∈ code.transitions)) &&
    match replaySchedule code word schedule with
    | none => false
    | some exec => successfulExecAcceptsBool code word exec

/-- Candidate schedules of every length at most the quantitative simple-trace budget.  This
contains the empty schedule even when the transition table is empty. -/
def candidateSchedules [Fintype Terminal]
    (code : Code Terminal) (word : List Terminal) :
    List (List (TransitionEntry Terminal)) :=
  listsUpToLength code.transitions (traceBudget code word)

/-- The genuine varying-code-and-word membership evaluator. -/
def membershipBool [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) : Bool :=
  (candidateSchedules code word).any (scheduleAcceptsBool code word)

/-! ## Exact local replay semantics -/

/-- Propositional form of the local checks performed before one chosen row is executed. -/
def EntryEnabled [DecidableEq Terminal] (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal) (entry : TransitionEntry Terminal) : Prop :=
  entry.source = exec.state ∧ entry.target < code.stateCount ∧
    SymbolValid code.workCount entry.scanned ∧
    SymbolValid code.workCount entry.written ∧
    readCurrent word exec = some entry.scanned

theorem entryEnabledBool_eq_true_iff [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal) (entry : TransitionEntry Terminal) :
    entryEnabledBool code word exec entry = true ↔
      EntryEnabled code word exec entry := by
  simp only [entryEnabledBool, EntryEnabled, Bool.and_eq_true, decide_eq_true_eq,
    symbolValidBool_eq_true_iff]
  tauto

theorem applyEntry?_eq_some_iff [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (exec next : ExecState Terminal) (entry : TransitionEntry Terminal) :
    applyEntry? code word exec entry = some next ↔
      EntryEnabled code word exec entry ∧
        next =
          let nextHead := moveHeadIndex (word.length + 1) exec.head entry.direction
          (entry.target, nextHead, (exec.head, entry.written) :: exec.overrides,
            nextHead :: exec.headsRev) := by
  cases henabled : entryEnabledBool code word exec entry with
  | false =>
      have hnot : ¬ EntryEnabled code word exec entry := by
        intro h
        have htrue :=
          (entryEnabledBool_eq_true_iff code word exec entry).2 h
        simp only [henabled, Bool.false_eq_true] at htrue
      simp [applyEntry?, henabled, hnot]
  | true =>
      have hyes : EntryEnabled code word exec entry :=
        (entryEnabledBool_eq_true_iff code word exec entry).1 henabled
      simp [applyEntry?, henabled, hyes, eq_comm]

/-- A replay state represents a semantic configuration when state/head indices agree, every
latest-write-wins cell read agrees after symbol decoding, and the head history starts at the
current head. -/
def Represents [DecidableEq Terminal] (code : Code Terminal) (word : List Terminal)
    (exec : ExecState Terminal)
    (cfg : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
      (Fin code.stateCount) (word.length + 1)) : Prop :=
  exec.state = cfg.state.val ∧ exec.head = cfg.tape.head.val ∧
    (∀ index : Fin (word.length + 2),
      readCell word exec.overrides index.val =
        some (encodeSymbol (cfg.tape.contents index))) ∧
    exec.headsRev.head? = some exec.head

@[simp] theorem moveHeadIndex_eq_moveHead_val {Gamma : Type v} {n : Nat}
    (tape : DLBA.BoundedTape Gamma n) (direction : DLBA.Dir) :
    moveHeadIndex n tape.head.val direction = (tape.moveHead direction).head.val := by
  cases direction with
  | stay => rfl
  | left =>
      simp only [moveHeadIndex, DLBA.BoundedTape.moveHead]
      split <;> rfl
  | right =>
      simp only [moveHeadIndex, DLBA.BoundedTape.moveHead]
      split <;> rfl

theorem encodeSymbol_endWord [DecidableEq Terminal] (workCount : Nat)
    (word : List Terminal) :
    (LBA.endWord (Work := Fin workCount) word).map encodeSymbol =
      LBA.endWord (Work := Nat) word := by
  simp [LBA.endWord, LBA.inputCell, encodeSymbol]

theorem readCell_nil_eq_initial [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (index : Fin (word.length + 2)) :
    readCell word [] index.val =
      some (encodeSymbol ((LBA.loadEnd (Γ := Fin code.workCount) word).contents index)) := by
  have htyped := LBA.ofFn_loadEnd_contents (Work := Fin code.workCount) word
  have hmapped := congrArg (List.map (encodeSymbol (Terminal := Terminal))) htyped
  rw [encodeSymbol_endWord] at hmapped
  have hindexRaw : index.val < (LBA.endWord (Work := Nat) word).length := by
    simp only [LBA.length_endWord]
    exact index.isLt
  have hindexTyped : index.val <
      (List.ofFn (LBA.loadEnd (Γ := Fin code.workCount) word).contents).length := by
    simp only [List.length_ofFn]
    exact index.isLt
  unfold readCell lookupOverride
  simp only [Option.orElse_none, List.getElem?_eq_getElem hindexRaw]
  have hget := congrArg (fun tape => tape[index.val]?) hmapped
  simp only [List.getElem?_eq_getElem hindexRaw, List.getElem?_map,
    List.getElem?_eq_getElem hindexTyped, List.getElem_ofFn] at hget
  simpa using hget.symm

theorem represents_initialExec [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount) :
    Represents code word (initialExec code) (LBA.initCfgEnd (toMachine code hpos) word) := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  intro index
  exact readCell_nil_eq_initial code word index

/-- One successful raw row replay is one genuine semantic LBA step and preserves the complete
latest-write-wins representation invariant. -/
theorem step_and_represents_of_applyEntry? [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount)
    (exec next : ExecState Terminal)
    (cfg : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
      (Fin code.stateCount) (word.length + 1))
    (entry : TransitionEntry Terminal)
    (hrep : Represents code word exec cfg)
    (hmem : entry ∈ code.transitions)
    (happly : applyEntry? code word exec entry = some next) :
    ∃ nextCfg : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
        (Fin code.stateCount) (word.length + 1),
      LBA.Step (toMachine code hpos) cfg nextCfg ∧
        Represents code word next nextCfg ∧
        ∃ (targetValid : entry.target < code.stateCount)
          (writtenValid : SymbolValid code.workCount entry.written),
          nextCfg = ⟨⟨entry.target, targetValid⟩,
            (cfg.tape.write (decodeSymbol entry.written writtenValid)).moveHead
              entry.direction⟩ := by
  obtain ⟨henabled, rfl⟩ :=
    (applyEntry?_eq_some_iff code word exec _ entry).mp happly
  rcases henabled with ⟨hsource, htarget, hscannedValid, hwrittenValid, hread⟩
  have hreadRep := hrep.2.2.1 cfg.tape.head
  have hreadAtHead : readCurrent word exec =
      some (encodeSymbol cfg.tape.read) := by
    unfold readCurrent
    rw [hrep.2.1]
    exact hreadRep
  have hscanned : entry.scanned = encodeSymbol cfg.tape.read := by
    rw [hreadAtHead] at hread
    exact Option.some.inj hread.symm
  let nextState : Fin code.stateCount := ⟨entry.target, htarget⟩
  let written : LBA.EndAlpha Terminal (Fin code.workCount) :=
    decodeSymbol entry.written hwrittenValid
  let nextCfg : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
      (Fin code.stateCount) (word.length + 1) :=
    ⟨nextState, (cfg.tape.write written).moveHead entry.direction⟩
  have henabledSemantic :
      (nextState, written, entry.direction) ∈
        (toMachine code hpos).transition cfg.state cfg.tape.read := by
    have hsourceValid : entry.source < code.stateCount := by
      rw [hsource, hrep.1]
      exact cfg.state.isLt
    have hdecodeScanned : decodeSymbol entry.scanned hscannedValid = cfg.tape.read := by
      exact decodeSymbol_eq_of_eq_encodeSymbol entry.scanned hscannedValid _ hscanned
    refine ⟨entry, hmem, hsourceValid, hscannedValid, htarget, hwrittenValid, ?_⟩
    unfold decodeEntry
    apply Prod.ext
    · exact Fin.ext (by simpa [hrep.1] using hsource)
    · apply Prod.ext
      · exact hdecodeScanned
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · rfl
  refine ⟨nextCfg, ⟨nextState, written, entry.direction, henabledSemantic, rfl⟩, ?_,
    htarget, hwrittenValid, rfl⟩
  refine ⟨rfl, ?_, ?_, rfl⟩
  · change moveHeadIndex (word.length + 1) exec.head entry.direction =
      ((cfg.tape.write written).moveHead entry.direction).head.val
    rw [hrep.2.1]
    exact moveHeadIndex_eq_moveHead_val (cfg.tape.write written) entry.direction
  · intro index
    have hold := hrep.2.2.1 index
    change readCell word ((exec.head, entry.written) :: exec.overrides) index.val =
      some (encodeSymbol (nextCfg.tape.contents index))
    simp only [readCell, lookupOverride]
    by_cases hindex : exec.head = index.val
    · rw [if_pos hindex]
      simp only [Option.orElse_some]
      have hfin : cfg.tape.head = index := by
        apply Fin.ext
        rw [← hrep.2.1]
        exact hindex
      subst index
      simp [nextCfg, written, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
        Function.update_self, encodeSymbol_decodeSymbol]
    · rw [if_neg hindex]
      change readCell word exec.overrides index.val =
        some (encodeSymbol (nextCfg.tape.contents index))
      have hfin : cfg.tape.head ≠ index := by
        intro heq
        apply hindex
        rw [hrep.2.1, heq]
      have hcontents : nextCfg.tape.contents index = cfg.tape.contents index := by
        simp [nextCfg, DLBA.BoundedTape.moveHead, DLBA.BoundedTape.write,
          Function.update_of_ne hfin.symm]
      rw [hcontents]
      exact hold

/-- Conversely, every semantic step chooses one stored raw row whose replay reaches a state
representing exactly the semantic target. -/
theorem exists_applyEntry?_of_step [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount)
    (exec : ExecState Terminal)
    (source target : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
      (Fin code.stateCount) (word.length + 1))
    (hrep : Represents code word exec source)
    (hstep : LBA.Step (toMachine code hpos) source target) :
    ∃ entry ∈ code.transitions, ∃ next : ExecState Terminal,
      applyEntry? code word exec entry = some next ∧
        Represents code word next target := by
  rcases hstep with ⟨targetState, written, direction, henabled, rfl⟩
  rcases henabled with
    ⟨entry, hmem, hsourceValid, hscannedValid, htargetValid, hwrittenValid, hdecode⟩
  have hsourceFin : (⟨entry.source, hsourceValid⟩ : Fin code.stateCount) = source.state :=
    congrArg (fun packed => packed.1) hdecode
  have hscannedDecoded : decodeSymbol entry.scanned hscannedValid = source.tape.read :=
    congrArg (fun packed => packed.2.1) hdecode
  have htargetFin : (⟨entry.target, htargetValid⟩ : Fin code.stateCount) = targetState :=
    congrArg (fun packed => packed.2.2.1) hdecode
  have hwrittenDecoded : decodeSymbol entry.written hwrittenValid = written :=
    congrArg (fun packed => packed.2.2.2.1) hdecode
  have hdirection : entry.direction = direction :=
    congrArg (fun packed => packed.2.2.2.2) hdecode
  have hsource : entry.source = exec.state := by
    rw [hrep.1]
    exact congrArg Fin.val hsourceFin
  have hscanned : entry.scanned = encodeSymbol source.tape.read := by
    calc
      entry.scanned = encodeSymbol (decodeSymbol entry.scanned hscannedValid) :=
        (encodeSymbol_decodeSymbol entry.scanned hscannedValid).symm
      _ = encodeSymbol source.tape.read := congrArg encodeSymbol hscannedDecoded
  have hreadRep := hrep.2.2.1 source.tape.head
  have hread : readCurrent word exec = some entry.scanned := by
    unfold readCurrent
    rw [hrep.2.1, hscanned]
    exact hreadRep
  let nextHead := moveHeadIndex (word.length + 1) exec.head entry.direction
  let next : ExecState Terminal :=
    (entry.target, nextHead, (exec.head, entry.written) :: exec.overrides,
      nextHead :: exec.headsRev)
  have happly : applyEntry? code word exec entry = some next := by
    apply (applyEntry?_eq_some_iff code word exec next entry).mpr
    exact ⟨⟨hsource, htargetValid, hscannedValid, hwrittenValid, hread⟩, rfl⟩
  obtain ⟨nextCfg, -, hnextRep, targetValid, writtenValid, hnextCfg⟩ :=
    step_and_represents_of_applyEntry? code word hpos exec next source entry
      hrep hmem happly
  have hnextTarget : nextCfg =
      ⟨targetState, (source.tape.write written).moveHead direction⟩ := by
    rw [hnextCfg]
    congr 1
    have hwritten : decodeSymbol entry.written writtenValid = written :=
      (decodeSymbol_eq_of_eq_encodeSymbol entry.written writtenValid
        (decodeSymbol entry.written hwrittenValid)
        (encodeSymbol_decodeSymbol entry.written hwrittenValid).symm).trans hwrittenDecoded
    rw [hwritten, hdirection]
  refine ⟨entry, hmem, next, happly, ?_⟩
  rwa [← hnextTarget]

/-- Chronological head positions visited by a concrete typed trace, including both endpoints. -/
def traceHeads {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State n}
    (trace : LBA.StepTrace M source target) : List Nat :=
  trace.vertices.map fun cfg => cfg.tape.head.val

/-- Soundness of replay from an arbitrary represented configuration.  The final newest-first
head log is exactly the reverse chronological trace-head list followed by the old log tail. -/
theorem replayFrom_sound [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount)
    (schedule : List (TransitionEntry Terminal))
    (exec final : ExecState Terminal)
    (cfg : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
      (Fin code.stateCount) (word.length + 1))
    (hrep : Represents code word exec cfg)
    (hall : ∀ entry ∈ schedule, entry ∈ code.transitions)
    (hreplay : replayFrom code word exec schedule = some final) :
    ∃ target : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
        (Fin code.stateCount) (word.length + 1),
      ∃ trace : LBA.StepTrace (toMachine code hpos) cfg target,
        Represents code word final target ∧
          final.headsRev = (traceHeads trace).reverse ++ exec.headsRev.tail := by
  induction schedule generalizing exec cfg with
  | nil =>
      simp only [replayFrom_nil, Option.some.injEq] at hreplay
      subst final
      refine ⟨cfg, .refl cfg, hrep, ?_⟩
      obtain ⟨tail, hheads⟩ := List.head?_eq_some_iff.mp hrep.2.2.2
      rw [hheads]
      simp [traceHeads, hrep.2.1]
  | cons entry rest ih =>
      simp only [replayFrom_cons] at hreplay
      cases happly : applyEntry? code word exec entry with
      | none => simp [happly] at hreplay
      | some next =>
          rw [happly] at hreplay
          simp only [Option.bind_some] at hreplay
          have hentry : entry ∈ code.transitions := hall entry (by simp)
          obtain ⟨nextCfg, hstep, hnextRep, -, -, -⟩ :=
            step_and_represents_of_applyEntry? code word hpos exec next cfg entry
              hrep hentry happly
          obtain ⟨target, restTrace, hfinalRep, hhistory⟩ :=
            ih next nextCfg hnextRep
              (fun later hlater => hall later (List.mem_cons_of_mem entry hlater)) hreplay
          refine ⟨target, .head hstep restTrace, hfinalRep, ?_⟩
          obtain ⟨henabled, hnext⟩ :=
            (applyEntry?_eq_some_iff code word exec next entry).mp happly
          subst next
          obtain ⟨oldTail, holdHeads⟩ := List.head?_eq_some_iff.mp hrep.2.2.2
          have hexecHeads : exec.headsRev = cfg.tape.head.val :: exec.headsRev.tail := by
            calc
              exec.headsRev = exec.head :: oldTail := holdHeads
              _ = cfg.tape.head.val :: oldTail := by rw [hrep.2.1]
              _ = cfg.tape.head.val :: exec.headsRev.tail := by simp [holdHeads]
          rw [hhistory]
          simp only [ExecState.headsRev, List.tail_cons, traceHeads,
            LBA.StepTrace.vertices_head, List.map_cons, List.reverse_cons,
            List.append_assoc]
          apply congrArg (fun suffix =>
            (List.map (fun cfg => cfg.tape.head.val) restTrace.vertices).reverse ++ suffix)
          simpa only [List.singleton_append] using hexecHeads

/-- The numeric head comparison is definitionally the typed boundary-crossing predicate. -/
theorem headsCrossBoundaryBool_eq_true_iff {Gamma State : Type*} {n : Nat}
    (boundary : Fin n) (source target : DLBA.Cfg Gamma State n) :
    headsCrossBoundaryBool boundary.val source.tape.head.val target.tape.head.val = true ↔
      LBA.StepTrace.CrossesBoundary boundary source target := by
  simp [headsCrossBoundaryBool, LBA.StepTrace.CrossesBoundary,
    LBA.StepTrace.CrossesRight, LBA.StepTrace.CrossesLeft,
    LBA.StepTrace.HeadAtOrLeft, LBA.StepTrace.HeadRight]

private theorem crossingCountHeads_source_cons_traceHeads
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source next target : DLBA.Cfg Gamma State n}
    (boundary : Fin n) (rest : LBA.StepTrace M next target) :
    crossingCountHeads boundary.val (source.tape.head.val :: traceHeads rest) =
      (if LBA.StepTrace.CrossesBoundary boundary source next then 1 else 0) +
        crossingCountHeads boundary.val (traceHeads rest) := by
  cases rest with
  | refl =>
      simp only [traceHeads, LBA.StepTrace.vertices_refl, List.map_singleton,
        crossingCountHeads]
      rw [if_congr (headsCrossBoundaryBool_eq_true_iff boundary source next) rfl rfl]
  | @head next middle target hstep rest =>
      simp only [traceHeads, LBA.StepTrace.vertices_head, List.map_cons,
        crossingCountHeads]
      rw [if_congr (headsCrossBoundaryBool_eq_true_iff boundary source next) rfl rfl]

/-- Counting crossings from the typed trace's chronological head list gives the library's exact
`StepTrace.crossingCount`. -/
theorem crossingCountHeads_traceHeads {Gamma State : Type*} {n : Nat}
    {M : LBA.Machine Gamma State} {source target : DLBA.Cfg Gamma State n}
    (boundary : Fin n) (trace : LBA.StepTrace M source target) :
    crossingCountHeads boundary.val (traceHeads trace) = trace.crossingCount boundary := by
  induction trace with
  | refl => simp [traceHeads, crossingCountHeads, LBA.StepTrace.crossingCount]
  | @head source next target hstep rest ih =>
      simp only [traceHeads, LBA.StepTrace.vertices_head, List.map_cons,
        LBA.StepTrace.crossingCount]
      change crossingCountHeads boundary.val (source.tape.head.val :: traceHeads rest) = _
      rw [crossingCountHeads_source_cons_traceHeads boundary rest, ih]

/-- On a replay from the canonical initial state, the raw final crossing counter is literally the
typed trace crossing counter. -/
theorem crossingCountHeadsRev_of_replayFrom_initial
    [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount)
    (schedule : List (TransitionEntry Terminal)) (final : ExecState Terminal)
    (hall : ∀ entry ∈ schedule, entry ∈ code.transitions)
    (hreplay : replaySchedule code word schedule = some final) :
    ∃ target : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
        (Fin code.stateCount) (word.length + 1),
      ∃ trace : LBA.StepTrace (toMachine code hpos)
          (LBA.initCfgEnd (toMachine code hpos) word) target,
        Represents code word final target ∧
          ∀ boundary : Fin (word.length + 1),
            crossingCountHeadsRev boundary.val final.headsRev =
              trace.crossingCount boundary := by
  rw [replaySchedule_eq_replayFrom] at hreplay
  obtain ⟨target, trace, hrep, hheads⟩ :=
    replayFrom_sound code word hpos schedule (initialExec code) final
      (LBA.initCfgEnd (toMachine code hpos) word)
      (represents_initialExec code word hpos) hall hreplay
  refine ⟨target, trace, hrep, ?_⟩
  intro boundary
  have hinitialTail : (initialExec code : ExecState Terminal).headsRev.tail = [] := rfl
  rw [hheads, hinitialTail, List.append_nil, crossingCountHeadsRev, List.reverse_reverse]
  exact crossingCountHeads_traceHeads boundary trace

/-- Every concrete typed trace compiles to a schedule of exactly the same length, using only
stored rows, and replaying that schedule preserves the exact target and head history. -/
theorem exists_schedule_of_stepTrace [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) (hpos : 0 < code.stateCount)
    (exec : ExecState Terminal)
    (source target : DLBA.Cfg (LBA.EndAlpha Terminal (Fin code.workCount))
      (Fin code.stateCount) (word.length + 1))
    (hrep : Represents code word exec source)
    (trace : LBA.StepTrace (toMachine code hpos) source target) :
    ∃ schedule : List (TransitionEntry Terminal), ∃ final : ExecState Terminal,
      schedule.length = trace.length ∧
        (∀ entry ∈ schedule, entry ∈ code.transitions) ∧
        replayFrom code word exec schedule = some final ∧
        Represents code word final target ∧
        final.headsRev = (traceHeads trace).reverse ++ exec.headsRev.tail := by
  induction trace generalizing exec with
  | refl =>
      refine ⟨[], exec, rfl, by simp, rfl, hrep, ?_⟩
      obtain ⟨tail, hheads⟩ := List.head?_eq_some_iff.mp hrep.2.2.2
      rw [hheads]
      simp [traceHeads, hrep.2.1]
  | @head source next target hstep rest ih =>
      obtain ⟨entry, hentry, nextExec, happly, hnextRep⟩ :=
        exists_applyEntry?_of_step code word hpos exec source next hrep hstep
      obtain ⟨schedule, final, hlength, hall, hreplay, hfinalRep, hhistory⟩ :=
        ih nextExec hnextRep
      refine ⟨entry :: schedule, final, ?_, ?_, ?_, hfinalRep, ?_⟩
      · simp [hlength, LBA.StepTrace.length]
      · intro chosen hchosen
        rcases List.mem_cons.mp hchosen with rfl | hchosen
        · exact hentry
        · exact hall chosen hchosen
      · simp only [replayFrom_cons, happly, Option.bind_some]
        exact hreplay
      · obtain ⟨henabled, hnext⟩ :=
          (applyEntry?_eq_some_iff code word exec nextExec entry).mp happly
        subst nextExec
        obtain ⟨oldTail, holdHeads⟩ := List.head?_eq_some_iff.mp hrep.2.2.2
        have hexecHeads : exec.headsRev = source.tape.head.val :: exec.headsRev.tail := by
          calc
            exec.headsRev = exec.head :: oldTail := holdHeads
            _ = source.tape.head.val :: oldTail := by rw [hrep.2.1]
            _ = source.tape.head.val :: exec.headsRev.tail := by simp [holdHeads]
        rw [hhistory]
        simp only [ExecState.headsRev, List.tail_cons, traceHeads,
          LBA.StepTrace.vertices_head, List.map_cons, List.reverse_cons,
          List.append_assoc]
        apply congrArg (fun suffix =>
          (List.map (fun cfg => cfg.tape.head.val) rest.vertices).reverse ++ suffix)
        simpa only [List.singleton_append] using hexecHeads

theorem successfulExecAcceptsBool_eq_true_iff
    (code : Code Terminal) (word : List Terminal) (exec : ExecState Terminal) :
    successfulExecAcceptsBool code word exec = true ↔
      exec.state ∈ code.accepting ∧
        ∀ boundary < word.length + 1,
          crossingCountHeadsRev boundary exec.headsRev ≤ code.crossingCap := by
  simp only [successfulExecAcceptsBool, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true]
  constructor
  · rintro ⟨haccept, hcaps⟩
    exact ⟨haccept, fun boundary hboundary =>
      hcaps boundary (List.mem_range.mpr hboundary)⟩
  · rintro ⟨haccept, hcaps⟩
    exact ⟨haccept, fun boundary hboundary =>
      hcaps boundary (List.mem_range.mp hboundary)⟩

theorem scheduleAcceptsBool_eq_true_iff [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (schedule : List (TransitionEntry Terminal)) :
    scheduleAcceptsBool code word schedule = true ↔
      0 < code.stateCount ∧
        (∀ entry ∈ schedule, entry ∈ code.transitions) ∧
        ∃ final : ExecState Terminal,
          replaySchedule code word schedule = some final ∧
            final.state ∈ code.accepting ∧
            ∀ boundary < word.length + 1,
              crossingCountHeadsRev boundary final.headsRev ≤ code.crossingCap := by
  cases hreplay : replaySchedule code word schedule with
  | none => simp [scheduleAcceptsBool, hreplay]
  | some final =>
      simp only [scheduleAcceptsBool, hreplay, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, successfulExecAcceptsBool_eq_true_iff]
      constructor
      · rintro ⟨⟨hpos, hall⟩, haccept, hcaps⟩
        exact ⟨hpos, hall, final, rfl, haccept, hcaps⟩
      · rintro ⟨hpos, hall, witness, hwitness, haccept, hcaps⟩
        have hwitnessEq : witness = final := (Option.some.inj hwitness).symm
        subst witness
        exact ⟨⟨hpos, hall⟩, haccept, hcaps⟩

theorem membershipBool_eq_true_iff_exists_schedule
    [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) :
    membershipBool code word = true ↔
      ∃ schedule : List (TransitionEntry Terminal),
        schedule.length ≤ traceBudget code word ∧
          (∀ entry ∈ schedule, entry ∈ code.transitions) ∧
          scheduleAcceptsBool code word schedule = true := by
  rw [membershipBool, List.any_eq_true]
  constructor
  · rintro ⟨schedule, hschedule, haccept⟩
    obtain ⟨hlength, hall⟩ :=
      (mem_listsUpToLength code.transitions (traceBudget code word) schedule).mp hschedule
    exact ⟨schedule, hlength, hall, haccept⟩
  · rintro ⟨schedule, hlength, hall, haccept⟩
    exact ⟨schedule,
      (mem_listsUpToLength code.transitions (traceBudget code word) schedule).mpr
        ⟨hlength, hall⟩,
      haccept⟩

@[simp] theorem card_endAlpha_fin [Fintype Terminal] (workCount : Nat) :
    Fintype.card (LBA.EndAlpha Terminal (Fin workCount)) =
      Fintype.card Terminal + workCount + 3 := by
  simp [LBA.EndAlpha]

/-- Soundness of the numeric schedule search against the semantic fixed-cap LBA language. -/
theorem acceptsWithBound_of_membershipBool_eq_true
    [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (haccept : membershipBool code word = true) :
    ∃ hpos : 0 < code.stateCount,
      AcceptsWithBound (toMachine code hpos)
        (LBA.initCfgEnd (toMachine code hpos) word) code.crossingCap := by
  obtain ⟨schedule, -, hall, hschedule⟩ :=
    (membershipBool_eq_true_iff_exists_schedule code word).mp haccept
  obtain ⟨hpos, hall', final, hreplay, hfinal, hcaps⟩ :=
    (scheduleAcceptsBool_eq_true_iff code word schedule).mp hschedule
  obtain ⟨target, trace, hrep, hcrossEq⟩ :=
    crossingCountHeadsRev_of_replayFrom_initial code word hpos schedule final hall' hreplay
  refine ⟨hpos, target, trace, ?_, ?_⟩
  · rw [toMachine_accept]
    rwa [← hrep.1]
  · intro boundary
    rw [← hcrossEq boundary]
    exact hcaps boundary.val boundary.isLt

/-- Completeness of the numeric schedule search.  The only fuel fact used is the existing sharp
simple-trace inequality with canonical boundary parameter `n = |word| + 1`. -/
theorem membershipBool_eq_true_of_acceptsWithBound
    [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal)
    (hpos : 0 < code.stateCount)
    (haccept : AcceptsWithBound (toMachine code hpos)
      (LBA.initCfgEnd (toMachine code hpos) word) code.crossingCap) :
    membershipBool code word = true := by
  obtain ⟨target, trace, hfinal, hsimple, hcaps, hlength⟩ :=
    exists_simple_acceptingTrace_of_acceptsWithBound haccept
  have hbudget : trace.length + 1 ≤ traceBudget code word := by
    simpa only [traceBudget, Fintype.card_fin, card_endAlpha_fin] using hlength
  obtain ⟨schedule, final, hscheduleLength, hall, hreplay, hfinalRep, hhistory⟩ :=
    exists_schedule_of_stepTrace code word hpos (initialExec code)
      (LBA.initCfgEnd (toMachine code hpos) word)
      target (represents_initialExec code word hpos) trace
  apply (membershipBool_eq_true_iff_exists_schedule code word).mpr
  refine ⟨schedule, by omega, hall, ?_⟩
  apply (scheduleAcceptsBool_eq_true_iff code word schedule).mpr
  have hreplaySchedule : replaySchedule code word schedule = some final := by
    rw [replaySchedule_eq_replayFrom]
    exact hreplay
  refine ⟨hpos, hall, final, hreplaySchedule, ?_, ?_⟩
  · rw [hfinalRep.1]
    exact (toMachine_accept code hpos target.state).mp hfinal
  · intro boundary hboundary
    let typedBoundary : Fin (word.length + 1) := ⟨boundary, hboundary⟩
    have hinitialTail : (initialExec code : ExecState Terminal).headsRev.tail = [] := rfl
    have hrawEq : crossingCountHeadsRev boundary final.headsRev =
        trace.crossingCount typedBoundary := by
      rw [hhistory, hinitialTail, List.append_nil, crossingCountHeadsRev,
        List.reverse_reverse]
      exact crossingCountHeads_traceHeads typedBoundary trace
    rw [hrawEq]
    exact hcaps typedBoundary

/-- Exact correctness of one genuinely varying code-and-word evaluator. -/
public theorem membershipBool_eq_true_iff
    [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) (word : List Terminal) :
    membershipBool code word = true ↔ word ∈ languageOf code := by
  by_cases hpos : 0 < code.stateCount
  · rw [languageOf_of_stateCount_pos code hpos]
    exact ⟨fun haccept => (acceptsWithBound_of_membershipBool_eq_true code word haccept).2,
      membershipBool_eq_true_of_acceptsWithBound code word hpos⟩
  · have hzero : code.stateCount = 0 := Nat.eq_zero_of_not_pos hpos
    rw [languageOf_of_stateCount_eq_zero code hzero]
    change membershipBool code word = true ↔ False
    constructor
    · intro haccept
      obtain ⟨hpositive, -⟩ := acceptsWithBound_of_membershipBool_eq_true code word haccept
      exact hpos hpositive
    · intro hfalse
      exact False.elim hfalse

/-! ## Joint primitive recursiveness in the varying code and the word -/

private theorem list_all_primrec
    {Input : Type u} {Element : Type v} [Primcodable Input] [Primcodable Element]
    {items : Input → List Element} {test : Input → Element → Bool}
    (hitems : Primrec items) (htest : Primrec₂ test) :
    Primrec fun input => (items input).all (test input) := by
  have hstep : Primrec₂ fun (input : Input) (state : Element × Bool) =>
      test input state.1 && state.2 := by
    apply Primrec₂.mk
    exact Primrec.and.comp
      (htest.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hitems (Primrec.const true) hstep).of_eq
  intro input
  induction items input with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem list_any_primrec
    {Input : Type u} {Element : Type v} [Primcodable Input] [Primcodable Element]
    {items : Input → List Element} {test : Input → Element → Bool}
    (hitems : Primrec items) (htest : Primrec₂ test) :
    Primrec fun input => (items input).any (test input) := by
  have hstep : Primrec₂ fun (input : Input) (state : Element × Bool) =>
      test input state.1 || state.2 := by
    apply Primrec₂.mk
    exact Primrec.or.comp
      (htest.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hitems (Primrec.const false) hstep).of_eq
  intro input
  induction items input with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem listsOfLength_eq_natRec {Element : Type v}
    (alphabet : List Element) (length : Nat) :
    listsOfLength alphabet length =
      Nat.rec [[]]
        (fun _ shorter => shorter.flatMap fun tail =>
          alphabet.map fun head => head :: tail)
        length := by
  induction length with
  | zero => rfl
  | succ length ih => simp only [listsOfLength, ih]

private theorem listsOfLength_primrec
    {Input : Type u} {Element : Type v} [Primcodable Input] [Primcodable Element]
    {alphabet : Input → List Element} {length : Input → Nat}
    (halphabet : Primrec alphabet) (hlength : Primrec length) :
    Primrec fun input => listsOfLength (alphabet input) (length input) := by
  have hstep : Primrec₂ fun (input : Input)
      (state : Nat × List (List Element)) =>
      state.2.flatMap fun tail =>
        (alphabet input).map fun head => head :: tail := by
    apply Primrec₂.mk
    let StepInput := Input × (Nat × List (List Element))
    have htails : Primrec fun p : StepInput => p.2.2 :=
      Primrec.snd.comp Primrec.snd
    have hmapped : Primrec₂ fun (p : StepInput) (tail : List Element) =>
        (alphabet p.1).map fun head => head :: tail := by
      apply Primrec₂.mk
      apply Primrec.list_map (halphabet.comp (Primrec.fst.comp Primrec.fst))
      apply Primrec₂.mk
      exact Primrec.list_cons.comp Primrec.snd
        (Primrec.snd.comp Primrec.fst)
    exact Primrec.list_flatMap htails hmapped
  apply (Primrec.nat_rec' hlength (Primrec.const [[]]) hstep).of_eq
  intro input
  exact (listsOfLength_eq_natRec (alphabet input) (length input)).symm

theorem listsUpToLength_primrec
    {Input : Type u} {Element : Type v} [Primcodable Input] [Primcodable Element]
    {alphabet : Input → List Element} {bound : Input → Nat}
    (halphabet : Primrec alphabet) (hbound : Primrec bound) :
    Primrec fun input => listsUpToLength (alphabet input) (bound input) := by
  have hlengths : Primrec fun input => List.range (bound input + 1) :=
    Primrec.list_range.comp (Primrec.succ.comp hbound)
  have hbody : Primrec₂ fun (input : Input) (length : Nat) =>
      listsOfLength (alphabet input) length := by
    apply Primrec₂.mk
    exact listsOfLength_primrec
      (halphabet.comp Primrec.fst) Primrec.snd
  exact Primrec.list_flatMap hlengths hbody

theorem code_workCount_primrec [Primcodable Terminal] :
    Primrec (Code.workCount : Code Terminal → Nat) := Primrec.fst

theorem code_stateCount_primrec [Primcodable Terminal] :
    Primrec (Code.stateCount : Code Terminal → Nat) :=
  Primrec.fst.comp Primrec.snd

theorem code_initialIndex_primrec [Primcodable Terminal] :
    Primrec (Code.initialIndex : Code Terminal → Nat) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

theorem code_crossingCap_primrec [Primcodable Terminal] :
    Primrec (Code.crossingCap : Code Terminal → Nat) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem code_accepting_primrec [Primcodable Terminal] :
    Primrec (Code.accepting : Code Terminal → List Nat) :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem code_transitions_primrec [Primcodable Terminal] :
    Primrec (Code.transitions : Code Terminal → List (TransitionEntry Terminal)) :=
  Primrec.snd.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem transitionEntry_source_primrec [Primcodable Terminal] :
    Primrec (TransitionEntry.source : TransitionEntry Terminal → Nat) :=
  Primrec.fst

private theorem transitionEntry_scanned_primrec [Primcodable Terminal] :
    Primrec (TransitionEntry.scanned : TransitionEntry Terminal → RawSymbol Terminal) :=
  Primrec.fst.comp Primrec.snd

private theorem transitionEntry_target_primrec [Primcodable Terminal] :
    Primrec (TransitionEntry.target : TransitionEntry Terminal → Nat) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem transitionEntry_written_primrec [Primcodable Terminal] :
    Primrec (TransitionEntry.written : TransitionEntry Terminal → RawSymbol Terminal) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem transitionEntry_direction_primrec [Primcodable Terminal] :
    Primrec (TransitionEntry.direction : TransitionEntry Terminal → DLBA.Dir) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem execState_state_primrec [Primcodable Terminal] :
    Primrec (ExecState.state : ExecState Terminal → Nat) := Primrec.fst

private theorem execState_head_primrec [Primcodable Terminal] :
    Primrec (ExecState.head : ExecState Terminal → Nat) :=
  Primrec.fst.comp Primrec.snd

private theorem execState_overrides_primrec [Primcodable Terminal] :
    Primrec (ExecState.overrides : ExecState Terminal → List (Override Terminal)) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem execState_headsRev_primrec [Primcodable Terminal] :
    Primrec (ExecState.headsRev : ExecState Terminal → List Nat) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

private theorem list_mem_primrec {Element : Type v}
    [Primcodable Element] [DecidableEq Element] :
    Primrec₂ fun (items : List Element) (value : Element) =>
      decide (value ∈ items) := by
  apply Primrec₂.mk
  have htest : Primrec₂ fun (input : List Element × Element)
      (candidate : Element) => decide (candidate = input.2) := by
    apply Primrec₂.mk
    exact Primrec.eq.decide.comp Primrec.snd
      (Primrec.snd.comp Primrec.fst)
  have hany : Primrec fun input : List Element × Element =>
      input.1.any fun candidate => decide (candidate = input.2) :=
    list_any_primrec Primrec.fst htest
  apply hany.of_eq
  rintro ⟨items, value⟩
  induction items with
  | nil => simp
  | cons head tail ih =>
      have ih' : (tail.any fun candidate => decide (value = candidate)) =
          decide (value ∈ tail) := by
        simpa [eq_comm] using ih
      simp [ih', eq_comm]

/-- Keep conjunction assembly opaque in callers whose input code is a deeply nested product.
Without this polymorphic boundary, unification repeatedly normalizes the concrete product coding
while checking each `Primrec.and.comp`. -/
private theorem primrec_and5 {Input : Type u} [Primcodable Input]
    {a b c d e : Input → Bool}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hd : Primrec d) (he : Primrec e) :
    Primrec fun input =>
      a input && b input && c input && d input && e input :=
  Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp (Primrec.and.comp ha hb) hc) hd) he

private theorem primrec_and3 {Input : Type u} [Primcodable Input]
    {a b c : Input → Bool}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
  Primrec fun input => a input && b input && c input :=
  Primrec.and.comp (Primrec.and.comp ha hb) hc

private def optionResultBool
    {Input : Type u} {Element : Type v}
    (option : Input → Option Element) (someCase : Input → Element → Bool)
    (input : Input) : Bool :=
  match option input with
  | none => false
  | some element => someCase input element

private theorem primrec_optionBool
    {Input : Type u} {Element : Type v}
    [Primcodable Input] [Primcodable Element]
    (option : Input → Option Element) (someCase : Input → Element → Bool)
    (hoption : Primrec option) (hsome : Primrec₂ someCase) :
    Primrec (optionResultBool option someCase) := by
  have hmapped : Primrec fun input => (option input).map (someCase input) :=
    @Primrec.option_map Input Element Bool inferInstance inferInstance inferInstance
      option someCase hoption hsome
  have hdefault : Primrec fun input =>
      ((option input).map (someCase input)).getD false :=
    @Primrec₂.comp Input (Option Bool) Bool Bool
      inferInstance inferInstance inferInstance inferInstance
      Option.getD
      (fun input => (option input).map (someCase input))
      (fun _ => false)
      Primrec.option_getD hmapped (Primrec.const false)
  apply hdefault.of_eq
  intro input
  unfold optionResultBool
  cases option input <;> rfl

private theorem endWord_primrec
    [Fintype Terminal] [Primcodable Terminal] :
    Primrec (LBA.endWord (Work := Nat) : List Terminal → List (RawSymbol Terminal)) := by
  have hinputCell : Primrec
      (LBA.inputCell : Terminal → RawSymbol Terminal) :=
    Primrec.dom_finite _
  have hmapped : Primrec fun word : List Terminal =>
      word.map (LBA.inputCell : Terminal → RawSymbol Terminal) := by
    apply Primrec.list_map Primrec.id
    apply Primrec₂.mk
    exact hinputCell.comp Primrec.snd
  apply (Primrec.list_append.comp
    (Primrec.list_cons.comp (Primrec.const (LBA.leftMark : RawSymbol Terminal)) hmapped)
    (Primrec.const [LBA.rightMark])).of_eq
  intro word
  rfl

private theorem workIndex?_primrec [Primcodable Terminal] :
    Primrec (workIndex? : RawSymbol Terminal → Option Nat) := by
  have hwork : Primrec fun symbol : Terminal ⊕ Nat =>
      match symbol with
      | .inl _ => none
      | .inr work => some work := by
    apply (Primrec.sumCasesOn Primrec.id
      (Primrec.const none).to₂
      (Primrec.option_some.comp Primrec.snd).to₂).of_eq
    intro symbol
    cases symbol <;> rfl
  have hinterior : Primrec fun symbol : Option (Terminal ⊕ Nat) =>
      match symbol with
      | none => none
      | some symbol =>
          match symbol with
          | .inl _ => none
          | .inr work => some work := by
    apply (Primrec.option_casesOn Primrec.id (Primrec.const none)
      (hwork.comp Primrec.snd).to₂).of_eq
    intro symbol
    cases symbol <;> rfl
  apply (Primrec.sumCasesOn Primrec.id
    (hinterior.comp Primrec.snd).to₂
    (Primrec.const none).to₂).of_eq
  intro symbol
  rcases symbol with (none | (terminal | work)) | marker <;> rfl

private theorem symbolValidBool_primrec [Primcodable Terminal] :
    Primrec₂ (symbolValidBool : Nat → RawSymbol Terminal → Bool) := by
  apply Primrec₂.mk
  let Input := Nat × RawSymbol Terminal
  have hindex : Primrec fun input : Input => workIndex? input.2 :=
    workIndex?_primrec.comp Primrec.snd
  have hsome : Primrec₂ fun (input : Input) (work : Nat) =>
      decide (work < input.1) := by
    apply Primrec₂.mk
    exact Primrec.nat_lt.decide.comp Primrec.snd
      (Primrec.fst.comp Primrec.fst)
  apply (Primrec.option_casesOn hindex (Primrec.const true) hsome).of_eq
  intro input
  cases hindex : workIndex? input.2 <;> simp [symbolValidBool, hindex]

theorem initialExec_primrec [Primcodable Terminal] :
    Primrec (initialExec : Code Terminal → ExecState Terminal) := by
  exact Primrec.pair
    (Primrec.nat_mod.comp code_initialIndex_primrec code_stateCount_primrec)
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.const []) (Primrec.const [0])))

private theorem lookupOverride_primrec
    [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec₂ (lookupOverride : Nat → List (Override Terminal) →
      Option (RawSymbol Terminal)) := by
  apply Primrec₂.mk
  let Input := Nat × List (Override Terminal)
  have hstep : Primrec₂ fun (input : Input)
      (state : Override Terminal × List (Override Terminal) ×
        Option (RawSymbol Terminal)) =>
      if state.1.1 = input.1 then some state.1.2 else state.2.2 := by
    apply Primrec₂.mk
    apply Primrec.ite
    · exact Primrec.eq.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp Primrec.fst)
    · exact Primrec.option_some.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    · exact Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_rec Primrec.snd (Primrec.const none) hstep).of_eq
  intro input
  induction input.2 with
  | nil => rfl
  | cons override rest ih =>
      rcases override with ⟨writtenIndex, symbol⟩
      simp [lookupOverride, ih]

private theorem readCell_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : List Terminal × List (Override Terminal) × Nat =>
      readCell input.1 input.2.1 input.2.2 := by
  have hoverride : Primrec fun input :
      List Terminal × List (Override Terminal) × Nat =>
      lookupOverride input.2.2 input.2.1 :=
    lookupOverride_primrec.comp
      (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd)
  have hinitial : Primrec fun input :
      List Terminal × List (Override Terminal) × Nat =>
      (LBA.endWord (Work := Nat) input.1)[input.2.2]? :=
    Primrec.list_getElem?.comp
      (endWord_primrec.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.option_orElse.comp hoverride hinitial).of_eq fun input => by
    simp only [readCell, Option.orElse_eq_orElse]

private theorem readCurrent_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec₂ (readCurrent : List Terminal → ExecState Terminal →
      Option (RawSymbol Terminal)) := by
  apply Primrec₂.mk
  exact readCell_primrec.comp
    (Primrec.pair Primrec.fst
      (Primrec.pair
        (execState_overrides_primrec.comp Primrec.snd)
        (execState_head_primrec.comp Primrec.snd)))

private theorem moveHeadIndex_primrec :
    Primrec fun input : Nat × Nat × DLBA.Dir =>
      moveHeadIndex input.1 input.2.1 input.2.2 := by
  have hlast : Primrec fun input : Nat × Nat × DLBA.Dir => input.1 :=
    Primrec.fst
  have hhead : Primrec fun input : Nat × Nat × DLBA.Dir => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hdirection : Primrec fun input : Nat × Nat × DLBA.Dir => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hstay : Primrec fun input : Nat × Nat × DLBA.Dir =>
      decide (input.2.2 = DLBA.Dir.stay) :=
    Primrec.eq.decide.comp hdirection (Primrec.const DLBA.Dir.stay)
  have hleftDirection : Primrec fun input : Nat × Nat × DLBA.Dir =>
      decide (input.2.2 = DLBA.Dir.left) :=
    Primrec.eq.decide.comp hdirection (Primrec.const DLBA.Dir.left)
  have hleft : Primrec fun input : Nat × Nat × DLBA.Dir =>
      if 0 < input.2.1 then input.2.1 - 1 else input.2.1 :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) hhead)
      (Primrec.nat_sub.comp hhead (Primrec.const 1)) hhead
  have hright : Primrec fun input : Nat × Nat × DLBA.Dir =>
      if input.2.1 < input.1 then input.2.1 + 1 else input.2.1 :=
    Primrec.ite (Primrec.nat_lt.comp hhead hlast)
      (Primrec.succ.comp hhead) hhead
  have hresult : Primrec fun input : Nat × Nat × DLBA.Dir =>
      bif decide (input.2.2 = DLBA.Dir.stay) then input.2.1
      else bif decide (input.2.2 = DLBA.Dir.left) then
        (if 0 < input.2.1 then input.2.1 - 1 else input.2.1)
      else (if input.2.1 < input.1 then input.2.1 + 1 else input.2.1) :=
    Primrec.cond hstay hhead (Primrec.cond hleftDirection hleft hright)
  apply hresult.of_eq
  intro input
  cases input.2.2 <;> simp [moveHeadIndex]

set_option maxHeartbeats 1000000 in
private theorem entryEnabledBool_packed_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : EntryInput Terminal =>
      entryEnabledBool input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  let Input := EntryInput Terminal
  have hcode : Primrec fun input : Input => input.1 := Primrec.fst
  have hword : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hexec : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hentry : Primrec fun input : Input => input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsource : Primrec fun input : Input => input.2.2.2.source :=
    transitionEntry_source_primrec.comp hentry
  have htarget : Primrec fun input : Input => input.2.2.2.target :=
    transitionEntry_target_primrec.comp hentry
  have hscanned : Primrec fun input : Input => input.2.2.2.scanned :=
    transitionEntry_scanned_primrec.comp hentry
  have hwritten : Primrec fun input : Input => input.2.2.2.written :=
    transitionEntry_written_primrec.comp hentry
  have hstate : Primrec fun input : Input => input.2.2.1.state :=
    execState_state_primrec.comp hexec
  have hstateCount : Primrec fun input : Input => input.1.stateCount :=
    code_stateCount_primrec.comp hcode
  have hworkCount : Primrec fun input : Input => input.1.workCount :=
    code_workCount_primrec.comp hcode
  have hread : Primrec fun input : Input =>
      readCurrent input.2.1 input.2.2.1 :=
    readCurrent_primrec.comp hword hexec
  have hsourceMatches : Primrec fun input : Input =>
      decide (input.2.2.2.source = input.2.2.1.state) :=
    Primrec.eq.decide.comp hsource hstate
  have htargetValid : Primrec fun input : Input =>
      decide (input.2.2.2.target < input.1.stateCount) :=
    Primrec.nat_lt.decide.comp htarget hstateCount
  have hscannedValid : Primrec fun input : Input =>
      symbolValidBool input.1.workCount input.2.2.2.scanned :=
    symbolValidBool_primrec.comp hworkCount hscanned
  have hwrittenValid : Primrec fun input : Input =>
      symbolValidBool input.1.workCount input.2.2.2.written :=
    symbolValidBool_primrec.comp hworkCount hwritten
  have hreadMatches : Primrec fun input : Input =>
      decide (readCurrent input.2.1 input.2.2.1 = some input.2.2.2.scanned) :=
    Primrec.eq.decide.comp hread (Primrec.option_some.comp hscanned)
  have hcombined := primrec_and5
    (a := fun input : Input =>
      decide (input.2.2.2.source = input.2.2.1.state))
    (b := fun input : Input =>
      decide (input.2.2.2.target < input.1.stateCount))
    (c := fun input : Input =>
      symbolValidBool input.1.workCount input.2.2.2.scanned)
    (d := fun input : Input =>
      symbolValidBool input.1.workCount input.2.2.2.written)
    (e := fun input : Input =>
      decide (readCurrent input.2.1 input.2.2.1 = some input.2.2.2.scanned))
    hsourceMatches htargetValid hscannedValid hwrittenValid hreadMatches
  unfold entryEnabledBool
  exact hcombined

set_option maxHeartbeats 1000000 in
theorem applyEntry?_packed_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : EntryInput Terminal =>
      applyEntry? input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  let Input := EntryInput Terminal
  have hword : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hexec : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hentry : Primrec fun input : Input => input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hhead : Primrec fun input : Input => input.2.2.1.head :=
    execState_head_primrec.comp hexec
  let nextHead : Input → Nat := fun input =>
      moveHeadIndex (input.2.1.length + 1) input.2.2.1.head
        input.2.2.2.direction
  have hlast : Primrec fun input : Input => input.2.1.length + 1 :=
    Primrec.succ.comp (Primrec.list_length.comp hword)
  have hdirection : Primrec fun input : Input => input.2.2.2.direction :=
    transitionEntry_direction_primrec.comp hentry
  have hheadDirection : Primrec fun input : Input =>
      (input.2.2.1.head, input.2.2.2.direction) := by
    apply Primrec.pair
    · exact hhead
    · exact hdirection
  have hmoveInput : Primrec fun input : Input =>
      (input.2.1.length + 1, input.2.2.1.head, input.2.2.2.direction) := by
    apply Primrec.pair
    · exact hlast
    · exact hheadDirection
  have hnextHead : Primrec nextHead := by
    unfold nextHead
    exact @Primrec.comp Input (Nat × Nat × DLBA.Dir) Nat
      inferInstance inferInstance inferInstance
      (fun input => moveHeadIndex input.1 input.2.1 input.2.2)
      (fun input : Input =>
        (input.2.1.length + 1, input.2.2.1.head, input.2.2.2.direction))
      moveHeadIndex_primrec hmoveInput
  have htarget : Primrec fun input : Input => input.2.2.2.target :=
    transitionEntry_target_primrec.comp hentry
  have hwritten : Primrec fun input : Input => input.2.2.2.written :=
    transitionEntry_written_primrec.comp hentry
  have hoverrides : Primrec fun input : Input => input.2.2.1.overrides :=
    execState_overrides_primrec.comp hexec
  have hheadsRev : Primrec fun input : Input => input.2.2.1.headsRev :=
    execState_headsRev_primrec.comp hexec
  have hnext : Primrec fun input : Input =>
      ((input.2.2.2.target, nextHead input,
        ((input.2.2.1.head, input.2.2.2.written) :: input.2.2.1.overrides),
        (nextHead input :: input.2.2.1.headsRev)) : ExecState Terminal) := by
    apply Primrec.pair
    · exact htarget
    apply Primrec.pair
    · exact hnextHead
    apply Primrec.pair
    · apply Primrec.list_cons.comp
      · apply Primrec.pair
        · exact hhead
        · exact hwritten
      · exact hoverrides
    · apply Primrec.list_cons.comp
      · exact hnextHead
      · exact hheadsRev
  unfold applyEntry?
  apply Primrec.cond
  · exact entryEnabledBool_packed_primrec
  · exact Primrec.option_some.comp hnext
  · exact Primrec.const none

set_option maxHeartbeats 1000000 in
private theorem replayFoldStep?_packed_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal ×
        Option (ExecState Terminal) × TransitionEntry Terminal =>
      replayFoldStep? input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  let Input := Code Terminal × List Terminal ×
    Option (ExecState Terminal) × TransitionEntry Terminal
  have hcurrent : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hsome : Primrec₂ fun (input : Input) (exec : ExecState Terminal) =>
      applyEntry? input.1 input.2.1 exec input.2.2.2 := by
    apply Primrec₂.mk
    let PackedInput := Input × ExecState Terminal
    have hpack : Primrec fun p : PackedInput =>
        ((p.1.1, p.1.2.1, p.2, p.1.2.2.2) : EntryInput Terminal) := by
      apply Primrec.pair
      · exact Primrec.fst.comp Primrec.fst
      apply Primrec.pair
      · exact Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      apply Primrec.pair
      · exact Primrec.snd
      · exact Primrec.snd.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact @Primrec.comp PackedInput (EntryInput Terminal)
      (Option (ExecState Terminal)) inferInstance inferInstance inferInstance
      (fun input => applyEntry? input.1 input.2.1 input.2.2.1 input.2.2.2)
      (fun p => (p.1.1, p.1.2.1, p.2, p.1.2.2.2))
      applyEntry?_packed_primrec hpack
  unfold replayFoldStep?
  apply Primrec.option_bind
  · exact hcurrent
  · exact hsome

set_option maxHeartbeats 1000000 in
theorem replaySchedule_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal ×
        List (TransitionEntry Terminal) =>
      replaySchedule input.1 input.2.1 input.2.2 := by
  let Input := Code Terminal × List Terminal ×
    List (TransitionEntry Terminal)
  have hcode : Primrec fun input : Input => input.1 := Primrec.fst
  have hword : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hschedule : Primrec fun input : Input => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hinitial : Primrec fun input : Input =>
      some (initialExec input.1 : ExecState Terminal) :=
    Primrec.option_some.comp (initialExec_primrec.comp hcode)
  have hstep : Primrec₂ fun (input : Input)
      (state : Option (ExecState Terminal) × TransitionEntry Terminal) =>
      replayFoldStep? input.1 input.2.1 state.1 state.2 := by
    apply Primrec₂.mk
    let PackedInput := Input ×
      (Option (ExecState Terminal) × TransitionEntry Terminal)
    let ReplayInput := Code Terminal × List Terminal ×
      Option (ExecState Terminal) × TransitionEntry Terminal
    have hpack : Primrec fun p : PackedInput =>
        ((p.1.1, p.1.2.1, p.2.1, p.2.2) : ReplayInput) := by
      apply Primrec.pair
      · exact Primrec.fst.comp Primrec.fst
      apply Primrec.pair
      · exact Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      apply Primrec.pair
      · exact Primrec.fst.comp Primrec.snd
      · exact Primrec.snd.comp Primrec.snd
    exact @Primrec.comp PackedInput ReplayInput (Option (ExecState Terminal))
      inferInstance inferInstance inferInstance
      (fun input => replayFoldStep? input.1 input.2.1 input.2.2.1 input.2.2.2)
      (fun p => (p.1.1, p.1.2.1, p.2.1, p.2.2))
      replayFoldStep?_packed_primrec hpack
  have hfold : Primrec fun input : Input =>
      input.2.2.foldl (replayFoldStep? input.1 input.2.1)
        (some (initialExec input.1 : ExecState Terminal)) :=
    @Primrec.list_foldl Input (TransitionEntry Terminal)
      (Option (ExecState Terminal)) inferInstance inferInstance inferInstance
      (fun input => input.2.2)
      (fun input => some (initialExec input.1 : ExecState Terminal))
      (fun input state => replayFoldStep? input.1 input.2.1 state.1 state.2)
      hschedule hinitial hstep
  exact hfold

private theorem headsCrossBoundaryBool_primrec :
    Primrec fun input : Nat × Nat × Nat =>
      headsCrossBoundaryBool input.1 input.2.1 input.2.2 := by
  have hboundary : Primrec fun input : Nat × Nat × Nat => input.1 :=
    Primrec.fst
  have hsource : Primrec fun input : Nat × Nat × Nat => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have htarget : Primrec fun input : Nat × Nat × Nat => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  unfold headsCrossBoundaryBool
  exact Primrec.or.comp
    (Primrec.and.comp
      (Primrec.nat_le.decide.comp hsource hboundary)
      (Primrec.nat_lt.decide.comp hboundary htarget))
    (Primrec.and.comp
      (Primrec.nat_lt.decide.comp hboundary hsource)
      (Primrec.nat_le.decide.comp htarget hboundary))

private def crossingFoldStep (boundary : Nat)
    (state : Option Nat × Nat) (target : Nat) : Option Nat × Nat :=
  match state.1 with
  | none => (some target, state.2)
  | some source =>
      (some target, state.2 + if headsCrossBoundaryBool boundary source target then 1 else 0)

private theorem crossingFoldStep_packed_primrec :
    Primrec fun input : Nat × (Option Nat × Nat) × Nat =>
      crossingFoldStep input.1 input.2.1 input.2.2 := by
  let Input := Nat × (Option Nat × Nat) × Nat
  have hprevious : Primrec fun input : Input => input.2.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hcount : Primrec fun input : Input => input.2.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have htarget : Primrec fun input : Input => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hnone : Primrec fun input : Input => (some input.2.2, input.2.1.2) := by
    apply Primrec.pair
    · apply Primrec.option_some.comp
      exact htarget
    · exact hcount
  have hsome : Primrec₂ fun (input : Input) (source : Nat) =>
      (some input.2.2, input.2.1.2 +
        bif headsCrossBoundaryBool input.1 source input.2.2 then 1 else 0) := by
    apply Primrec₂.mk
    let SomeInput := Input × Nat
    have hboundary : Primrec fun p : SomeInput => p.1.1 :=
      Primrec.fst.comp Primrec.fst
    have hsource : Primrec fun p : SomeInput => p.2 :=
      Primrec.snd
    have hsomeTarget : Primrec fun p : SomeInput => p.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hsomeCount : Primrec fun p : SomeInput => p.1.2.1.2 :=
      Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    have hcrossInput : Primrec fun p : SomeInput =>
        (p.1.1, p.2, p.1.2.2) := by
      apply Primrec.pair
      · exact hboundary
      apply Primrec.pair
      · exact hsource
      · exact hsomeTarget
    have hcross : Primrec fun p : SomeInput =>
        headsCrossBoundaryBool p.1.1 p.2 p.1.2.2 :=
      @Primrec.comp SomeInput (Nat × Nat × Nat) Bool
        inferInstance inferInstance inferInstance
        (fun input => headsCrossBoundaryBool input.1 input.2.1 input.2.2)
        (fun p => (p.1.1, p.2, p.1.2.2))
        headsCrossBoundaryBool_primrec hcrossInput
    have hincrement : Primrec fun p : SomeInput =>
        bif headsCrossBoundaryBool p.1.1 p.2 p.1.2.2 then 1 else 0 :=
      @Primrec.cond SomeInput Nat inferInstance inferInstance
        (fun p => headsCrossBoundaryBool p.1.1 p.2 p.1.2.2)
        (fun _ => 1) (fun _ => 0)
        hcross (Primrec.const 1) (Primrec.const 0)
    apply Primrec.pair
    · apply Primrec.option_some.comp
      exact hsomeTarget
    · apply Primrec.nat_add.comp
      · exact hsomeCount
      · exact hincrement
  exact (Primrec.option_casesOn hprevious hnone hsome).of_eq fun input => by
    cases hpreviousValue : input.2.1.1 with
    | none => simp [crossingFoldStep, hpreviousValue]
    | some source =>
        cases hcross : headsCrossBoundaryBool input.1 source input.2.2 <;>
          simp [crossingFoldStep, hpreviousValue, hcross]

private theorem crossingFold_from_some (boundary source count : Nat)
    (heads : List Nat) :
    (heads.foldl (crossingFoldStep boundary) (some source, count)).2 =
      count + crossingCountHeads boundary (source :: heads) := by
  induction heads generalizing source count with
  | nil => simp [crossingCountHeads]
  | cons target rest ih =>
      simp only [List.foldl_cons, crossingFoldStep]
      rw [ih]
      simp only [crossingCountHeads]
      omega

private theorem crossingCountHeads_eq_fold (boundary : Nat) (heads : List Nat) :
    crossingCountHeads boundary heads =
      (heads.foldl (crossingFoldStep boundary) (none, 0)).2 := by
  cases heads with
  | nil => rfl
  | cons source rest =>
      simp only [List.foldl_cons, crossingFoldStep]
      rw [crossingFold_from_some]
      simp

private theorem crossingCountHeads_primrec :
    Primrec₂ (crossingCountHeads : Nat → List Nat → Nat) := by
  apply Primrec₂.mk
  let Input := Nat × List Nat
  have hstep : Primrec₂ fun (input : Input)
      (state : (Option Nat × Nat) × Nat) =>
      crossingFoldStep input.1 state.1 state.2 := by
    apply Primrec₂.mk
    exact crossingFoldStep_packed_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have hfold : Primrec fun input : Input =>
      input.2.foldl (crossingFoldStep input.1) (none, 0) :=
    Primrec.list_foldl Primrec.snd (Primrec.const (none, 0)) hstep
  exact (Primrec.snd.comp hfold).of_eq fun input =>
    (crossingCountHeads_eq_fold input.1 input.2).symm

theorem crossingCountHeadsRev_primrec :
    Primrec₂ (crossingCountHeadsRev : Nat → List Nat → Nat) := by
  apply Primrec₂.mk
  exact crossingCountHeads_primrec.comp Primrec.fst
    (Primrec.list_reverse.comp Primrec.snd)

theorem traceBudget_primrec
    [Fintype Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal =>
      traceBudget input.1 input.2 := by
  have hstates : Primrec fun input : Code Terminal × List Terminal =>
      input.1.stateCount := code_stateCount_primrec.comp Primrec.fst
  have hwork : Primrec fun input : Code Terminal × List Terminal =>
      input.1.workCount := code_workCount_primrec.comp Primrec.fst
  have hcap : Primrec fun input : Code Terminal × List Terminal =>
      input.1.crossingCap := code_crossingCap_primrec.comp Primrec.fst
  have hlength : Primrec fun input : Code Terminal × List Terminal =>
      input.2.length := Primrec.list_length.comp Primrec.snd
  unfold traceBudget
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp hstates
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.const (Fintype.card Terminal)) hwork)
        (Primrec.const 3)))
    (Primrec.succ.comp
      (Primrec.nat_mul.comp (Primrec.succ.comp hlength) hcap))

set_option maxHeartbeats 1000000 in
theorem successfulExecAcceptsBool_packed_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal × ExecState Terminal =>
      successfulExecAcceptsBool input.1 input.2.1 input.2.2 := by
  let Input := Code Terminal × List Terminal × ExecState Terminal
  have hcode : Primrec fun input : Input => input.1 := Primrec.fst
  have hword : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hexec : Primrec fun input : Input => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have haccept : Primrec fun input : Input =>
      decide (input.2.2.state ∈ input.1.accepting) :=
    list_mem_primrec.comp
      (code_accepting_primrec.comp hcode)
      (execState_state_primrec.comp hexec)
  have hboundaries : Primrec fun input : Input =>
      List.range (input.2.1.length + 1) :=
    Primrec.list_range.comp
      (Primrec.succ.comp (Primrec.list_length.comp hword))
  have hboundaryTest : Primrec₂ fun (input : Input) (boundary : Nat) =>
      decide (crossingCountHeadsRev boundary input.2.2.headsRev ≤
        input.1.crossingCap) := by
    apply Primrec₂.mk
    have hcross : Primrec fun p : Input × Nat =>
        crossingCountHeadsRev p.2 p.1.2.2.headsRev :=
      crossingCountHeadsRev_primrec.comp Primrec.snd
        (execState_headsRev_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    exact Primrec.nat_le.decide.comp hcross
      (code_crossingCap_primrec.comp
        (Primrec.fst.comp Primrec.fst))
  have hall : Primrec fun input : Input =>
      (List.range (input.2.1.length + 1)).all fun boundary =>
        decide (crossingCountHeadsRev boundary input.2.2.headsRev ≤
          input.1.crossingCap) :=
    list_all_primrec hboundaries hboundaryTest
  unfold successfulExecAcceptsBool
  exact Primrec.and.comp haccept hall

set_option maxHeartbeats 1000000 in
theorem scheduleAcceptsBool_packed_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal ×
        List (TransitionEntry Terminal) =>
      scheduleAcceptsBool input.1 input.2.1 input.2.2 := by
  let Input := Code Terminal × List Terminal ×
    List (TransitionEntry Terminal)
  let positiveFn : Input → Bool := fun input =>
    decide (0 < input.1.stateCount)
  let allFn : Input → Bool := fun input =>
    input.2.2.all fun entry => decide (entry ∈ input.1.transitions)
  let replayFn : Input → Option (ExecState Terminal) := fun input =>
    replaySchedule input.1 input.2.1 input.2.2
  let successFn : Input → ExecState Terminal → Bool := fun input exec =>
    successfulExecAcceptsBool input.1 input.2.1 exec
  have hcode : Primrec fun input : Input => input.1 := Primrec.fst
  have hschedule : Primrec fun input : Input => input.2.2 :=
    Primrec.snd.comp Primrec.snd
  have hpositive : Primrec positiveFn :=
    Primrec.nat_lt.decide.comp (Primrec.const 0)
      (code_stateCount_primrec.comp hcode)
  have hentryTest : Primrec₂ fun (input : Input)
      (entry : TransitionEntry Terminal) =>
      decide (entry ∈ input.1.transitions) := by
    apply Primrec₂.mk
    exact list_mem_primrec.comp
      (code_transitions_primrec.comp
        (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hall : Primrec allFn :=
    list_all_primrec hschedule hentryTest
  have hreplay : Primrec replayFn :=
    replaySchedule_primrec
  have hsome : Primrec₂ successFn := by
    apply Primrec₂.mk
    let PackedInput := Input × ExecState Terminal
    let SuccessInput := Code Terminal × List Terminal × ExecState Terminal
    have hpack : Primrec fun p : PackedInput =>
        ((p.1.1, p.1.2.1, p.2) : SuccessInput) := by
      apply Primrec.pair
      · exact Primrec.fst.comp Primrec.fst
      apply Primrec.pair
      · exact Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
      · exact Primrec.snd
    exact @Primrec.comp PackedInput SuccessInput Bool
      inferInstance inferInstance inferInstance
      (fun input => successfulExecAcceptsBool input.1 input.2.1 input.2.2)
      (fun p => (p.1.1, p.1.2.1, p.2))
      successfulExecAcceptsBool_packed_primrec hpack
  have hresult := primrec_optionBool
    (Input := Input) (Element := ExecState Terminal)
    replayFn successFn hreplay hsome
  have hcombined := @primrec_and3 Input inferInstance
    positiveFn allFn
    (optionResultBool replayFn successFn)
    hpositive hall hresult
  exact @Primrec.of_eq Input Bool inferInstance inferInstance
    (fun input => positiveFn input && allFn input &&
      optionResultBool replayFn successFn input)
    (fun input => scheduleAcceptsBool input.1 input.2.1 input.2.2)
    hcombined (fun input => by
      cases hreplayValue : replaySchedule input.1 input.2.1 input.2.2 <;>
        simp [positiveFn, allFn, replayFn, successFn, optionResultBool,
          scheduleAcceptsBool, hreplayValue])

theorem candidateSchedules_primrec
    [Fintype Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal =>
      candidateSchedules input.1 input.2 := by
  have halphabet : Primrec fun input : Code Terminal × List Terminal =>
      input.1.transitions :=
    code_transitions_primrec.comp Primrec.fst
  have hbudget : Primrec fun input : Code Terminal × List Terminal =>
      traceBudget input.1 input.2 :=
    traceBudget_primrec
  unfold candidateSchedules
  exact listsUpToLength_primrec halphabet hbudget

set_option maxHeartbeats 1000000 in
public theorem membershipBool_primrec
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Primrec fun input : Code Terminal × List Terminal =>
      membershipBool input.1 input.2 := by
  let Input := Code Terminal × List Terminal
  let candidatesFn : Input → List (List (TransitionEntry Terminal)) := fun input =>
    candidateSchedules input.1 input.2
  let testFn : Input → List (TransitionEntry Terminal) → Bool := fun input schedule =>
    scheduleAcceptsBool input.1 input.2 schedule
  have hcandidates : Primrec candidatesFn := candidateSchedules_primrec
  have htest : Primrec₂ testFn := by
    apply Primrec₂.mk
    let PackedInput := Input × List (TransitionEntry Terminal)
    let ScheduleInput := Code Terminal × List Terminal ×
      List (TransitionEntry Terminal)
    have hpack : Primrec fun input : PackedInput =>
        ((input.1.1, input.1.2, input.2) : ScheduleInput) := by
      apply Primrec.pair
      · exact Primrec.fst.comp Primrec.fst
      apply Primrec.pair
      · exact Primrec.snd.comp Primrec.fst
      · exact Primrec.snd
    exact @Primrec.comp PackedInput ScheduleInput Bool
      inferInstance inferInstance inferInstance
      (fun input => scheduleAcceptsBool input.1 input.2.1 input.2.2)
      (fun input => (input.1.1, input.1.2, input.2))
      scheduleAcceptsBool_packed_primrec hpack
  have hany := list_any_primrec
    (Input := Input) (Element := List (TransitionEntry Terminal))
    (items := candidatesFn) (test := testFn) hcandidates htest
  exact @Primrec.of_eq Input Bool inferInstance inferInstance
    (fun input => (candidatesFn input).any (testFn input))
    (fun input => membershipBool input.1 input.2)
    hany (fun input => by rfl)

/-- The varying-signature checker is computable jointly in the entire numeric machine code,
runtime crossing cap, and unbounded query word. -/
public theorem membershipBool_computable
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    Computable fun input : Code Terminal × List Terminal =>
      membershipBool input.1 input.2 :=
  membershipBool_primrec.to_comp

/-- Exact joint decidability of the semantics denoted by a varying numeric code. -/
public theorem membership_computablePred
    [Fintype Terminal] [DecidableEq Terminal] [Primcodable Terminal] :
    ComputablePred fun input : Code Terminal × List Terminal =>
      input.2 ∈ languageOf input.1 := by
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun input => membershipBool input.1 input.2,
    membershipBool_computable, ?_⟩
  funext input
  apply propext
  exact (membershipBool_eq_true_iff input.1 input.2).symm

/-- In particular, every varying numeric code has uniformly semidecidable membership, with the
code itself (not an oracle hidden inside its encoding) supplied to the single machine. -/
public theorem languageOf_membershipSemiDecidable
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    [Primcodable Terminal] :
    MembershipSemiDecidable (languageOf (Terminal := Terminal)) :=
  membership_computablePred.to_re

/-! ## Noncomputable adequacy compiler -/

/-- A typed local row for a machine whose two finite signatures have already been normalized to
canonical `Fin` types. -/
abbrev FinTypedEntry (Terminal : Type u) (workCount stateCount : Nat) :=
  Fin stateCount × LBA.EndAlpha Terminal (Fin workCount) ×
    Fin stateCount × LBA.EndAlpha Terminal (Fin workCount) × DLBA.Dir

/-- Erase the dependent finite bounds from a typed local row. -/
def encodeFinTypedEntry {workCount stateCount : Nat} :
    FinTypedEntry Terminal workCount stateCount → TransitionEntry Terminal
  | (source, scanned, target, written, direction) =>
      ⟨source.val, encodeSymbol scanned, target.val, encodeSymbol written, direction⟩

private theorem encodeSymbol_injective {workCount : Nat} :
    Function.Injective
      (encodeSymbol : LBA.EndAlpha Terminal (Fin workCount) → RawSymbol Terminal) := by
  intro left right heq
  rcases left with (none | (terminal | work)) | marker
  all_goals
    rcases right with (none | (terminal' | work')) | marker'
    all_goals simp_all [encodeSymbol]
  exact Fin.ext heq

@[simp] theorem encodeSymbol_inj {workCount : Nat}
    {left right : LBA.EndAlpha Terminal (Fin workCount)} :
    encodeSymbol left = encodeSymbol right ↔ left = right :=
  encodeSymbol_injective.eq_iff

private theorem encodeFinTypedEntry_injective {workCount stateCount : Nat} :
    Function.Injective
      (encodeFinTypedEntry : FinTypedEntry Terminal workCount stateCount →
        TransitionEntry Terminal) := by
  rintro ⟨source, scanned, target, written, direction⟩
    ⟨source', scanned', target', written', direction'⟩ heq
  have hsource : source.val = source'.val :=
    congrArg TransitionEntry.source heq
  have hscanned : encodeSymbol scanned = encodeSymbol scanned' :=
    congrArg TransitionEntry.scanned heq
  have htarget : target.val = target'.val :=
    congrArg TransitionEntry.target heq
  have hwritten : encodeSymbol written = encodeSymbol written' :=
    congrArg TransitionEntry.written heq
  have hdirection : direction = direction' :=
    congrArg TransitionEntry.direction heq
  have hsource' : source = source' := Fin.ext hsource
  have htarget' : target = target' := Fin.ext htarget
  have hscanned' : scanned = scanned' := encodeSymbol_injective hscanned
  have hwritten' : written = written' := encodeSymbol_injective hwritten
  subst source'
  subst scanned'
  subst target'
  subst written'
  subst direction'
  rfl

/-- Compile a semantic LBA whose work and state signatures are already canonical `Fin` types to
one raw numeric code.  This function is deliberately noncomputable: classical enumeration is
used only in the adequacy proof to cover an arbitrary finite semantic transition relation.  It
is not used by `membershipBool`. -/
noncomputable def codeOfFinMachine [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) : Code Terminal := by
  classical
  exact
    (workCount, stateCount, M.initial.val, bound,
      (Finset.univ.filter fun state => M.accept state = true).toList.map Fin.val,
      (Finset.univ.filter fun entry : FinTypedEntry Terminal workCount stateCount =>
        (entry.2.2.1, entry.2.2.2.1, entry.2.2.2.2) ∈
          M.transition entry.1 entry.2.1).toList.map encodeFinTypedEntry)

@[simp] theorem codeOfFinMachine_workCount [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    (codeOfFinMachine M bound).workCount = workCount := by
  simp [codeOfFinMachine, Code.workCount]

@[simp] theorem codeOfFinMachine_stateCount [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    (codeOfFinMachine M bound).stateCount = stateCount := by
  simp [codeOfFinMachine, Code.stateCount]

@[simp] theorem codeOfFinMachine_initialIndex [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    (codeOfFinMachine M bound).initialIndex = M.initial.val := by
  simp [codeOfFinMachine, Code.initialIndex]

@[simp] theorem codeOfFinMachine_crossingCap [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    (codeOfFinMachine M bound).crossingCap = bound := by
  simp [codeOfFinMachine, Code.crossingCap]

theorem codeOfFinMachine_stateCount_pos [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    0 < (codeOfFinMachine M bound).stateCount := by
  rw [codeOfFinMachine_stateCount]
  exact Nat.zero_lt_of_lt M.initial.isLt

@[simp] theorem mem_codeOfFinMachine_accepting_iff
    [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) (state : Fin stateCount) :
    state.val ∈ (codeOfFinMachine M bound).accepting ↔
      M.accept state = true := by
  classical
  simp only [codeOfFinMachine, Code.accepting, List.mem_map,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨candidate, haccept, hval⟩
    have hstate : candidate = state := Fin.ext hval
    simpa [hstate] using haccept
  · intro haccept
    exact ⟨state, haccept, rfl⟩

@[simp] theorem encodeFinTypedEntry_mem_codeOfFinMachine_transitions_iff
    [Fintype Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) (entry : FinTypedEntry Terminal workCount stateCount) :
    encodeFinTypedEntry entry ∈ (codeOfFinMachine M bound).transitions ↔
      (entry.2.2.1, entry.2.2.2.1, entry.2.2.2.2) ∈
        M.transition entry.1 entry.2.1 := by
  classical
  simp only [codeOfFinMachine, Code.transitions, List.mem_map,
    Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨candidate, henabled, hencode⟩
    have hentry : candidate = entry := encodeFinTypedEntry_injective hencode
    simpa [hentry] using henabled
  · intro henabled
    exact ⟨entry, henabled, rfl⟩

theorem mem_toMachine_codeOfFinMachine_transition_iff
    [Fintype Terminal] [DecidableEq Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) (source target : Fin stateCount)
    (scanned written : LBA.EndAlpha Terminal (Fin workCount))
    (direction : DLBA.Dir) :
    (target, written, direction) ∈
        (toMachine (codeOfFinMachine M bound)
          (codeOfFinMachine_stateCount_pos M bound)).transition source scanned ↔
      (target, written, direction) ∈ M.transition source scanned := by
  classical
  simp only [toMachine]
  constructor
  · rintro ⟨entry, hentry, sourceValid, scannedValid, targetValid,
      writtenValid, hdecode⟩
    simp only [codeOfFinMachine, Code.transitions, List.mem_map,
      Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hentry
    obtain ⟨candidate, henabled, hencode⟩ := hentry
    subst entry
    rcases candidate with ⟨candidateSource, candidateScanned, candidateTarget,
      candidateWritten, candidateDirection⟩
    simp only [encodeFinTypedEntry, decodeEntry, TransitionEntry.source,
      TransitionEntry.scanned, TransitionEntry.target, TransitionEntry.written,
      TransitionEntry.direction, decodeSymbol_encodeSymbol, Prod.mk.injEq] at hdecode
    obtain ⟨hsource, hscanned, htarget, hwritten, hdirection⟩ := hdecode
    subst source
    subst scanned
    subst target
    subst written
    subst direction
    exact henabled
  · intro henabled
    let typedEntry : FinTypedEntry Terminal workCount stateCount :=
      (source, scanned, target, written, direction)
    let entry : TransitionEntry Terminal := encodeFinTypedEntry typedEntry
    have hentry : entry ∈ (codeOfFinMachine M bound).transitions :=
      (encodeFinTypedEntry_mem_codeOfFinMachine_transitions_iff M bound typedEntry).2
        henabled
    have hsource : entry.source < (codeOfFinMachine M bound).stateCount := by
      change source.val < stateCount
      exact source.isLt
    have hscanned : SymbolValid (codeOfFinMachine M bound).workCount entry.scanned := by
      change SymbolValid workCount (encodeSymbol scanned)
      exact symbolValid_encodeSymbol scanned
    have htarget : entry.target < (codeOfFinMachine M bound).stateCount := by
      change target.val < stateCount
      exact target.isLt
    have hwritten : SymbolValid (codeOfFinMachine M bound).workCount entry.written := by
      change SymbolValid workCount (encodeSymbol written)
      exact symbolValid_encodeSymbol written
    refine ⟨entry, hentry, hsource, hscanned, htarget, hwritten, ?_⟩
    simp [entry, typedEntry, decodeEntry, encodeFinTypedEntry,
      TransitionEntry.source, TransitionEntry.scanned, TransitionEntry.target,
      TransitionEntry.written, TransitionEntry.direction]

private theorem machine_eq_of_fields {Gamma State : Type*}
    {left right : LBA.Machine Gamma State}
    (htransition : left.transition = right.transition)
    (haccept : left.accept = right.accept)
    (hinitial : left.initial = right.initial) :
    left = right := by
  cases left with
  | mk leftTransition leftAccept leftInitial =>
      cases right with
      | mk rightTransition rightAccept rightInitial =>
          cases htransition
          cases haccept
          cases hinitial
          rfl

/-- The adequacy compiler is exact at the machine level, not merely language equivalent. -/
theorem toMachine_codeOfFinMachine
    [Fintype Terminal] [DecidableEq Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    toMachine (codeOfFinMachine M bound)
      (codeOfFinMachine_stateCount_pos M bound) = M := by
  apply machine_eq_of_fields
  · funext source scanned
    ext move
    rcases move with ⟨target, written, direction⟩
    exact mem_toMachine_codeOfFinMachine_transition_iff
      M bound source target scanned written direction
  · funext state
    apply Bool.eq_iff_iff.mpr
    rw [toMachine_accept]
    exact mem_codeOfFinMachine_accepting_iff M bound state
  · apply Fin.ext
    change M.initial.val % stateCount = M.initial.val
    exact Nat.mod_eq_of_lt M.initial.isLt

/-- Every normalized finite semantic machine is covered by a raw code at an arbitrary supplied
crossing cap.  This theorem is the reusable adequacy factor for both bounded and unrestricted
finite-signature presentation results. -/
public theorem languageOf_codeOfFinMachine
    [Fintype Terminal] [DecidableEq Terminal]
    {workCount stateCount : Nat}
    (M : LBA.Machine (LBA.EndAlpha Terminal (Fin workCount)) (Fin stateCount))
    (bound : Nat) :
    languageOf (codeOfFinMachine M bound) = LanguageWithBound M bound := by
  rw [languageOf_of_stateCount_pos _ (codeOfFinMachine_stateCount_pos M bound),
    codeOfFinMachine_crossingCap, toMachine_codeOfFinMachine]

/-- Compile an arbitrary pair of finite work/state types by first applying the noncomputable
canonical `Fin` transport.  No lower cardinality hypothesis is imposed: an empty work alphabet
is supported, while an empty state type is automatically impossible for a supplied `Machine`
because it contains an initial state. -/
noncomputable def codeOfFiniteMachine [Fintype Terminal]
    {Work State : Type*} [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    Code Terminal :=
  codeOfFinMachine M.finSignatureTransport bound

/-- Exact coverage of arbitrary finite signatures and an arbitrary cap. -/
public theorem languageOf_codeOfFiniteMachine
    [Fintype Terminal] [DecidableEq Terminal]
    {Work State : Type*} [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State) (bound : Nat) :
    languageOf (codeOfFiniteMachine M bound) = LanguageWithBound M bound := by
  calc
    languageOf (codeOfFiniteMachine M bound) =
        LanguageWithBound M.finSignatureTransport bound :=
      languageOf_codeOfFinMachine M.finSignatureTransport bound
    _ = LanguageWithBound M bound :=
      languageWithBound_finSignatureTransport M bound

/-! ## Independent semantic varying-cap class -/

section ClassLevel

variable {Terminal : Type}

/-- Independent semantic class obtained by allowing both finite signatures and the crossing cap
to vary.  It is stated through the existing semantic slice predicate, not as the raw-code range. -/
public def is_VaryingBoundedCrossingSlice (language : Language Terminal) : Prop :=
  ∃ bound, is_BoundedCrossingSlice bound language

/-- The independently stated varying-signature/cap slice class. -/
public def VaryingBoundedCrossingSlice : Set (Language Terminal) :=
  setOf is_VaryingBoundedCrossingSlice

/-- The independently stated varying-cap class is exactly the DFA class. -/
public theorem is_VaryingBoundedCrossingSlice_iff_is_DFA
    [Fintype Terminal] (language : Language Terminal) :
    is_VaryingBoundedCrossingSlice language ↔ is_DFA language := by
  constructor
  · rintro ⟨bound, hslice⟩
    exact is_DFA_of_is_BoundedCrossingSlice hslice
  · intro hdfa
    exact ⟨1, is_BoundedCrossingSlice_of_is_DFA (by omega) hdfa⟩

public theorem VaryingBoundedCrossingSlice_eq_DFA [Fintype Terminal] :
    (VaryingBoundedCrossingSlice (Terminal := Terminal) : Set (Language Terminal)) =
      DFA.Class := by
  ext language
  exact is_VaryingBoundedCrossingSlice_iff_is_DFA language

private theorem empty_language_is_DFA :
    is_DFA (fun _ : List Terminal => False) := by
  let emptyDFA : DFA Terminal Unit :=
    { step := fun _ _ => ()
      start := ()
      accept := fun _ => False }
  refine ⟨Unit, inferInstance, emptyDFA, ?_⟩
  funext word
  apply propext
  change False ↔ False
  exact Iff.rfl

/-- Every raw code denotes a regular language, including the total zero-state encoding of the
empty language. -/
public theorem is_DFA_languageOf [Fintype Terminal] [DecidableEq Terminal]
    (code : Code Terminal) : is_DFA (languageOf code) := by
  by_cases hpos : 0 < code.stateCount
  · rw [languageOf_of_stateCount_pos code hpos]
    exact is_DFA_languageWithBound (toMachine code hpos) code.crossingCap
  · have hzero : code.stateCount = 0 := Nat.eq_zero_of_not_pos hpos
    rw [languageOf_of_stateCount_eq_zero code hzero]
    exact empty_language_is_DFA

/-- Every DFA language is denoted by a raw code.  The completeness witness uses cap one and the
semantic fixed-cap converse, then the reusable arbitrary-signature compiler above. -/
public theorem exists_code_languageOf_eq_of_is_DFA
    [Fintype Terminal] [DecidableEq Terminal]
    {language : Language Terminal} (hlanguage : is_DFA language) :
    ∃ code : Code Terminal, languageOf code = language := by
  obtain ⟨Work, State, hWork, hState, M, hM⟩ :=
    is_BoundedCrossingSlice_of_is_DFA (bound := 1) (by omega) hlanguage
  letI : Fintype Work := hWork
  letI : Fintype State := hState
  refine ⟨codeOfFiniteMachine M 1, ?_⟩
  exact (languageOf_codeOfFiniteMachine M 1).trans hM

/-- The genuinely numeric varying-signature encoding characterizes exactly the named DFA
language class. -/
public theorem languageOf_characterizes_DFA
    [Fintype Terminal] [DecidableEq Terminal] :
    Characterizes DFA.Class (languageOf (Terminal := Terminal)) := by
  intro language
  constructor
  · exact exists_code_languageOf_eq_of_is_DFA
  · rintro ⟨code, rfl⟩
    exact is_DFA_languageOf code

/-- Direct NFA-named characterization of the same raw semantics. -/
public theorem languageOf_characterizes_NFA
    [Fintype Terminal] [DecidableEq Terminal] :
    Characterizes NFA.Class (languageOf (Terminal := Terminal)) := by
  rw [NFA_eq_DFA]
  exact languageOf_characterizes_DFA

/-- Direct Mathlib-regular characterization of the same raw semantics. -/
public theorem languageOf_characterizes_isRegular
    [Fintype Terminal] [DecidableEq Terminal] :
    Characterizes ({language : Language Terminal | language.IsRegular} :
      Set (Language Terminal)) (languageOf (Terminal := Terminal)) := by
  have hclass :
      ({language : Language Terminal | language.IsRegular} : Set (Language Terminal)) =
        DFA.Class := by
    ext language
    exact Language.isRegular_iff
  rw [hclass]
  exact languageOf_characterizes_DFA

/-- Equivalent characterization through the independent semantic varying-slice class. -/
public theorem languageOf_characterizes_varyingBoundedCrossingSlice
    [Fintype Terminal] [DecidableEq Terminal] :
    Characterizes (VaryingBoundedCrossingSlice (Terminal := Terminal))
      (languageOf (Terminal := Terminal)) := by
  rw [VaryingBoundedCrossingSlice_eq_DFA]
  exact languageOf_characterizes_DFA

/-- Headline effective-presentation theorem: one raw numeric code type, with runtime finite
signature sizes and runtime crossing cap, is an adequate effective presentation of precisely
the DFA/regular language class, and membership is uniformly decidable in `(code, word)`. -/
public theorem varyingBoundedCrossing_computableMembership
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    [Primcodable Terminal] :
    ComputableMembership DFA.Class
      (languageOf (Terminal := Terminal)) := by
  refine ⟨languageOf_characterizes_DFA.onTrue,
    languageOf_membershipSemiDecidable, ?_⟩
  exact ComputablePredOnPromise.ofComputablePred membership_computablePred

/-- NFA-named form of the same exact effective presentation result. -/
public theorem varyingBoundedCrossing_computableMembership_NFA
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    [Primcodable Terminal] :
    ComputableMembership NFA.Class
      (languageOf (Terminal := Terminal)) := by
  rw [NFA_eq_DFA]
  exact varyingBoundedCrossing_computableMembership

/-- Mathlib-regular named form of the exact effective presentation result. -/
public theorem varyingBoundedCrossing_computableMembership_isRegular
    {Terminal : Type} [Fintype Terminal] [DecidableEq Terminal]
    [Primcodable Terminal] :
    ComputableMembership
      ({language : Language Terminal | language.IsRegular} : Set (Language Terminal))
      (languageOf (Terminal := Terminal)) := by
  have hclass :
      ({language : Language Terminal | language.IsRegular} : Set (Language Terminal)) =
        DFA.Class := by
    ext language
    exact Language.isRegular_iff
  rw [hclass]
  exact varyingBoundedCrossing_computableMembership

end ClassLevel

end LBA.BoundedCrossing.VaryingEncodedMembership

end
