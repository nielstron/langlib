module

public import Langlib.Automata.LinearBounded.BoundedCrossingLanguage
import Mathlib.Tactic

@[expose]
public section

/-!
# Physical head turns bound tape-boundary crossings

This file measures reversals of the *physical* tape head along a concrete `LBA.StepTrace`.
Stationary transitions and moves clamped at an endpoint contribute no movement direction.  After
those steps have been erased, a head turn is a change between consecutive left/right directions.

For every physical boundary, its crossing count is at most the number of head turns plus one.
The sharper statement below gives zero when the trace has no genuine movement.  Consequently, a
weak existential promise selecting an accepting trace with at most `r` head turns for every
accepted canonical input implies the existing uniform crossing promise with cap `r + 1`.  The
bounded-crossing profile construction then makes the language finite-state, and hence also gives
a deterministic linearly bounded presentation.

All trace-level results include one-cell tapes (`n = 0`) and use no finiteness, nonemptiness, or
cardinality-lower-bound assumption.
-/

namespace LBA.HeadTurns

universe u

/-! ## Reusable change counting on lists -/

/-- Count changes in `values`, also comparing its first entry with `previous`.

For example, `changeCountFrom a [a, b, b, a] = 2`. -/
def changeCountFrom {Alpha : Type u} [DecidableEq Alpha]
    (previous : Alpha) : List Alpha → Nat
  | [] => 0
  | value :: values =>
      (if previous = value then 0 else 1) + changeCountFrom value values

/-- Count changes between consecutive entries of a list. -/
def changeCount {Alpha : Type u} [DecidableEq Alpha] : List Alpha → Nat
  | [] => 0
  | value :: values => changeCountFrom value values

@[simp] theorem changeCountFrom_nil {Alpha : Type u} [DecidableEq Alpha]
    (previous : Alpha) :
    changeCountFrom previous [] = 0 := rfl

@[simp] theorem changeCountFrom_cons {Alpha : Type u} [DecidableEq Alpha]
    (previous value : Alpha) (values : List Alpha) :
    changeCountFrom previous (value :: values) =
      (if previous = value then 0 else 1) + changeCountFrom value values := rfl

@[simp] theorem changeCount_nil {Alpha : Type u} [DecidableEq Alpha] :
    changeCount ([] : List Alpha) = 0 := rfl

@[simp] theorem changeCount_cons {Alpha : Type u} [DecidableEq Alpha]
    (value : Alpha) (values : List Alpha) :
    changeCount (value :: values) = changeCountFrom value values := rfl

/-- Supplying an arbitrary direction before a list adds at most one change. -/
theorem changeCountFrom_le_changeCount_add_one
    {Alpha : Type u} [DecidableEq Alpha]
    (previous : Alpha) (values : List Alpha) :
    changeCountFrom previous values ≤ changeCount values + 1 := by
  cases values with
  | nil => simp
  | cons value values =>
      simp only [changeCountFrom_cons, changeCount_cons]
      split <;> omega

@[simp] theorem changeCountFrom_replicate_same
    {Alpha : Type u} [DecidableEq Alpha]
    (value : Alpha) (count : Nat) :
    changeCountFrom value (List.replicate count value) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, changeCountFrom_cons, if_pos rfl, Nat.zero_add, ih]

@[simp] theorem changeCount_replicate
    {Alpha : Type u} [DecidableEq Alpha]
    (value : Alpha) (count : Nat) :
    changeCount (List.replicate count value) = 0 := by
  cases count with
  | zero => rfl
  | succ count =>
      rw [List.replicate_succ, changeCount_cons, changeCountFrom_replicate_same]

/-! ## Physical movement and turns of an LBA trace -/

/-- A genuine direction of physical head movement.  There is deliberately no stationary case. -/
inductive Direction where
  | left
  | right
  deriving DecidableEq, Repr

/-- Compare two configurations' actual head positions.

This returns `none` exactly when the head did not move.  Thus a transition requesting an outward
move at a clamped endpoint is treated just like an explicit stationary transition. -/
def physicalDirection {Gamma State : Type*} {n : Nat}
    (old new : DLBA.Cfg Gamma State n) : Option Direction :=
  if new.tape.head.val < old.tape.head.val then some .left
  else if old.tape.head.val < new.tape.head.val then some .right
  else none

/-- Chronological list of genuine physical head movements of a concrete trace. -/
def movementDirections {Gamma State : Type*} {n : Nat}
    {M : LBA.Machine Gamma State} :
    {source target : DLBA.Cfg Gamma State n} →
      LBA.StepTrace M source target → List Direction
  | _, _, .refl _ => []
  | source, _, .head (next := next) _ rest =>
      (physicalDirection source next).toList ++ movementDirections rest

/-- The number of physical head reversals in a trace, ignoring all stationary/clamped steps. -/
def headTurnCount {Gamma State : Type*} {n : Nat}
    {M : LBA.Machine Gamma State} {source target : DLBA.Cfg Gamma State n}
    (trace : LBA.StepTrace M source target) : Nat :=
  changeCount (movementDirections trace)

@[simp] theorem movementDirections_refl
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    (cfg : DLBA.Cfg Gamma State n) :
    movementDirections (.refl cfg : LBA.StepTrace M cfg cfg) = [] := rfl

@[simp] theorem movementDirections_single
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State n}
    (step : LBA.Step M source target) :
    movementDirections (LBA.StepTrace.single step) =
      (physicalDirection source target).toList := by
  simp [LBA.StepTrace.single, movementDirections]

/-- Physical movement directions concatenate along concatenated traces. -/
@[simp] theorem movementDirections_append
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source middle target : DLBA.Cfg Gamma State n}
    (first : LBA.StepTrace M source middle)
    (second : LBA.StepTrace M middle target) :
    movementDirections (LBA.StepTrace.append first second) =
      movementDirections first ++ movementDirections second := by
  induction first with
  | refl => rfl
  | head step rest ih =>
      simp only [LBA.StepTrace.append, movementDirections, ih, List.append_assoc]

@[simp] theorem headTurnCount_refl
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    (cfg : DLBA.Cfg Gamma State n) :
    headTurnCount (.refl cfg : LBA.StepTrace M cfg cfg) = 0 := rfl

/-! ## One boundary -/

/-- Which side of a physical boundary contains the head. -/
private def boundarySide {Gamma State : Type*} {n : Nat}
    (boundary : Fin n) (cfg : DLBA.Cfg Gamma State n) : Direction :=
  if cfg.tape.head.val ≤ boundary.val then .left else .right

/-- The zero-one discrete distance between two directions. -/
private def mismatch (leftDirection rightDirection : Direction) : Nat :=
  if leftDirection = rightDirection then 0 else 1

private theorem physicalDirection_eq_none_iff
    {Gamma State : Type*} {n : Nat}
    (old new : DLBA.Cfg Gamma State n) :
    physicalDirection old new = none ↔
      old.tape.head.val = new.tape.head.val := by
  simp only [physicalDirection]
  split_ifs <;> simp_all <;> omega

private theorem not_crossesBoundary_of_physicalDirection_eq_none
    {Gamma State : Type*} {n : Nat}
    (boundary : Fin n) (old new : DLBA.Cfg Gamma State n)
    (hstationary : physicalDirection old new = none) :
    ¬ LBA.StepTrace.CrossesBoundary boundary old new := by
  have hhead := (physicalDirection_eq_none_iff old new).mp hstationary
  simp only [LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
    LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
    LBA.StepTrace.HeadRight]
  omega

private theorem boundarySide_eq_of_physicalDirection_eq_none
    {Gamma State : Type*} {n : Nat}
    (boundary : Fin n) (old new : DLBA.Cfg Gamma State n)
    (hstationary : physicalDirection old new = none) :
    boundarySide boundary old = boundarySide boundary new := by
  have hhead := (physicalDirection_eq_none_iff old new).mp hstationary
  simp [boundarySide, hhead]

private theorem lt_of_physicalDirection_eq_some_left
    {Gamma State : Type*} {n : Nat}
    (old new : DLBA.Cfg Gamma State n)
    (hdirection : physicalDirection old new = some .left) :
    new.tape.head.val < old.tape.head.val := by
  simp only [physicalDirection] at hdirection
  split_ifs at hdirection <;> simp_all

private theorem lt_of_physicalDirection_eq_some_right
    {Gamma State : Type*} {n : Nat}
    (old new : DLBA.Cfg Gamma State n)
    (hdirection : physicalDirection old new = some .right) :
    old.tape.head.val < new.tape.head.val := by
  simp only [physicalDirection] at hdirection
  split_ifs at hdirection <;> simp_all

/-- Local accounting inequality for one genuine movement.

The two mismatch terms on the right are the available direction-change credit before the move
and the side credit at its source.  If the move crosses the boundary, its new physical direction
is the new side, while the two source and target sides differ.  If it does not cross, the usual
triangle inequality for the two-point direction type supplies the bound. -/
private theorem crossingIndicator_add_mismatch_le
    {Gamma State : Type*} {n : Nat}
    (boundary : Fin n) (old new : DLBA.Cfg Gamma State n)
    (previous direction : Direction)
    (hdirection : physicalDirection old new = some direction) :
    (if LBA.StepTrace.CrossesBoundary boundary old new then 1 else 0) +
        mismatch direction (boundarySide boundary new) ≤
      mismatch previous direction +
        mismatch previous (boundarySide boundary old) := by
  rcases direction with _ | _
  · have hmove := lt_of_physicalDirection_eq_some_left old new hdirection
    rcases previous with _ | _ <;>
      simp [boundarySide, mismatch,
        LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
        LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
        LBA.StepTrace.HeadRight] <;>
      split_ifs <;> simp_all <;> omega
  · have hmove := lt_of_physicalDirection_eq_some_right old new hdirection
    rcases previous with _ | _ <;>
      simp [boundarySide, mismatch,
        LBA.StepTrace.CrossesBoundary, LBA.StepTrace.CrossesRight,
        LBA.StepTrace.CrossesLeft, LBA.StepTrace.HeadAtOrLeft,
        LBA.StepTrace.HeadRight] <;>
      split_ifs <;> simp_all <;> omega

/-- Strong crossing invariant with an arbitrary direction immediately preceding the trace.

The final mismatch is a one-bit potential recording whether that preceding direction agrees
with the side containing the trace's source head. -/
private theorem crossingCount_le_changeCountFrom_add_mismatch
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State n}
    (boundary : Fin n) (previous : Direction)
    (trace : LBA.StepTrace M source target) :
    trace.crossingCount boundary ≤
      changeCountFrom previous (movementDirections trace) +
        mismatch previous (boundarySide boundary source) := by
  induction trace generalizing previous with
  | refl => simp [mismatch]
  | @head source next target step rest ih =>
      simp only [LBA.StepTrace.crossingCount, movementDirections]
      cases hdirection : physicalDirection source next with
      | none =>
          have hnotCross :=
            not_crossesBoundary_of_physicalDirection_eq_none
              boundary source next hdirection
          have hside :=
            boundarySide_eq_of_physicalDirection_eq_none
              boundary source next hdirection
          simp only [if_neg hnotCross]
          simpa [hside] using ih previous
      | some direction =>
          have hlocal := crossingIndicator_add_mismatch_le
            boundary source next previous direction hdirection
          have hrest := ih direction
          change
            (if LBA.StepTrace.CrossesBoundary boundary source next then 1 else 0) +
                rest.crossingCount boundary ≤
              changeCountFrom previous
                  (direction :: movementDirections rest) +
                mismatch previous (boundarySide boundary source)
          rw [changeCountFrom_cons]
          rw [show (if previous = direction then 0 else 1) =
            mismatch previous direction from rfl]
          have hsum := Nat.add_le_add_left hrest
            (if LBA.StepTrace.CrossesBoundary boundary source next then 1 else 0)
          omega

/-- Refined trace-level bound: a trace without genuine physical movement crosses no boundary;
otherwise every crossing is charged to its initial movement run or to a head turn. -/
theorem crossingCount_le_headTurnCount_add_indicator
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State n}
    (boundary : Fin n) (trace : LBA.StepTrace M source target) :
    trace.crossingCount boundary ≤
      headTurnCount trace + if movementDirections trace = [] then 0 else 1 := by
  have hstrong := crossingCount_le_changeCountFrom_add_mismatch
    boundary (boundarySide boundary source) trace
  by_cases hnil : movementDirections trace = []
  · simpa [headTurnCount, hnil, mismatch] using hstrong
  · obtain ⟨direction, directions, hdirections⟩ :=
      List.exists_cons_of_ne_nil hnil
    have hturn : headTurnCount trace =
        changeCount (direction :: directions) := by
      rw [headTurnCount, hdirections]
    calc
      trace.crossingCount boundary ≤
          changeCountFrom (boundarySide boundary source)
            (direction :: directions) := by
        simpa [hdirections, mismatch] using hstrong
      _ ≤ changeCount (direction :: directions) + 1 :=
        changeCountFrom_le_changeCount_add_one
          (boundarySide boundary source) (direction :: directions)
      _ = headTurnCount trace +
          (if movementDirections trace = [] then 0 else 1) := by
        rw [hturn, if_neg hnil]

/-- Every boundary is crossed at most once more than the number of physical head reversals. -/
theorem crossingCount_le_headTurnCount_add_one
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State n}
    (boundary : Fin n) (trace : LBA.StepTrace M source target) :
    trace.crossingCount boundary ≤ headTurnCount trace + 1 := by
  exact (crossingCount_le_headTurnCount_add_indicator boundary trace).trans (by
    by_cases hmovement : movementDirections trace = [] <;> simp [hmovement])

/-- If no physical move occurs, no physical boundary is crossed. -/
theorem crossingCount_eq_zero_of_movementDirections_eq_nil
    {Gamma State : Type*} {n : Nat} {M : LBA.Machine Gamma State}
    {source target : DLBA.Cfg Gamma State n}
    (boundary : Fin n) (trace : LBA.StepTrace M source target)
    (hmovement : movementDirections trace = []) :
    trace.crossingCount boundary = 0 := by
  have hbound := crossingCount_le_headTurnCount_add_indicator boundary trace
  simpa [headTurnCount, hmovement] using hbound

end LBA.HeadTurns

namespace LBA.BoundedCrossing

universe u v w

variable {Terminal : Type u} {Work : Type v} {State : Type w}

/-- A selected accepting trace with a bounded number of physical head reversals. -/
def AcceptsWithHeadTurnBound
    (M : LBA.Machine Gamma State) (source : DLBA.Cfg Gamma State n)
    (bound : Nat) : Prop :=
  ∃ target : DLBA.Cfg Gamma State n,
    ∃ trace : LBA.StepTrace M source target,
      M.accept target.state = true ∧ LBA.HeadTurns.headTurnCount trace ≤ bound

/-- Increasing the physical head-turn cap preserves a selected accepting witness. -/
theorem AcceptsWithHeadTurnBound.mono
    {M : LBA.Machine Gamma State} {source : DLBA.Cfg Gamma State n}
    {smaller larger : Nat}
    (haccept : AcceptsWithHeadTurnBound M source smaller)
    (hbound : smaller ≤ larger) :
    AcceptsWithHeadTurnBound M source larger := by
  obtain ⟨target, trace, hfinal, hturns⟩ := haccept
  exact ⟨target, trace, hfinal, hturns.trans hbound⟩

/-- Weak whole-language promise: every accepted canonical input has *some* accepting trace with
at most `bound` physical head reversals.  Other accepting traces and all rejecting traces are
unrestricted. -/
def HasUniformAcceptingHeadTurnBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    (bound : Nat) : Prop :=
  ∀ input : List Terminal,
    LBA.Accepts M (LBA.initCfgEnd M input) →
      AcceptsWithHeadTurnBound M (LBA.initCfgEnd M input) bound

/-- Increasing the cap preserves the weak whole-language head-turn promise. -/
theorem HasUniformAcceptingHeadTurnBound.mono
    {M : LBA.Machine (LBA.EndAlpha Terminal Work) State}
    {smaller larger : Nat}
    (hpromise : HasUniformAcceptingHeadTurnBound M smaller)
    (hbound : smaller ≤ larger) :
    HasUniformAcceptingHeadTurnBound M larger := by
  intro input haccept
  exact (hpromise input haccept).mono hbound

/-- A uniform selected-accepting head-turn cap gives a uniform crossing cap one larger. -/
theorem hasUniformAcceptingBound_of_hasUniformAcceptingHeadTurnBound
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {bound : Nat} (hbound : HasUniformAcceptingHeadTurnBound M bound) :
    HasUniformAcceptingBound M (bound + 1) := by
  intro input haccept
  obtain ⟨target, trace, hfinal, hturns⟩ := hbound input haccept
  refine ⟨target, trace, hfinal, ?_⟩
  intro boundary
  exact (LBA.HeadTurns.crossingCount_le_headTurnCount_add_one boundary trace).trans
    (Nat.add_le_add_right hturns 1)

/-- NFA form of bounded-head-turn regularity. -/
theorem is_NFA_languageEnd_of_hasUniformAcceptingHeadTurnBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {bound : Nat} (hbound : HasUniformAcceptingHeadTurnBound M bound) :
    is_NFA (LBA.LanguageEnd M) :=
  is_NFA_languageEnd_of_hasUniformAcceptingBound M (bound + 1)
    (hasUniformAcceptingBound_of_hasUniformAcceptingHeadTurnBound M hbound)

/-- DFA form of bounded-head-turn regularity. -/
theorem is_DFA_languageEnd_of_hasUniformAcceptingHeadTurnBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {bound : Nat} (hbound : HasUniformAcceptingHeadTurnBound M bound) :
    is_DFA (LBA.LanguageEnd M) :=
  is_DFA_languageEnd_of_hasUniformAcceptingBound M (bound + 1)
    (hasUniformAcceptingBound_of_hasUniformAcceptingHeadTurnBound M hbound)

/-- Mathlib's regular-language form of bounded-head-turn regularity. -/
theorem isRegular_languageEnd_of_hasUniformAcceptingHeadTurnBound
    {Terminal Work State : Type}
    [Fintype Terminal] [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {bound : Nat} (hbound : HasUniformAcceptingHeadTurnBound M bound) :
    (LBA.LanguageEnd M).IsRegular := by
  rw [Language.isRegular_iff]
  exact is_DFA_languageEnd_of_hasUniformAcceptingHeadTurnBound M hbound

/-- Deterministic-LBA form of bounded-head-turn regularity. -/
theorem is_DLBA_languageEnd_of_hasUniformAcceptingHeadTurnBound
    {Terminal Work State : Type}
    [Fintype Terminal] [DecidableEq Terminal]
    [Fintype Work] [Fintype State]
    (M : LBA.Machine (LBA.EndAlpha Terminal Work) State)
    {bound : Nat} (hbound : HasUniformAcceptingHeadTurnBound M bound) :
    is_DLBA (LBA.LanguageEnd M) :=
  is_DLBA_languageEnd_of_hasUniformAcceptingBound M (bound + 1)
    (hasUniformAcceptingBound_of_hasUniformAcceptingHeadTurnBound M hbound)

end LBA.BoundedCrossing

/-! ## The explicit one-way DFA scanner makes no head turn -/

namespace DFA

open LBA.HeadTurns

universe u v w

variable {T : Type u} {Q : Type v} {Work : Type w}

private theorem physicalDirection_initial_endmarkerScanCfg
    (D : DFA T Q) (word : List T) :
    physicalDirection
      (LBA.initCfgEnd (endmarkerLBA (Work := Work) D) word)
      (endmarkerScanCfg (Work := Work) D word 0 (Nat.zero_le _)) =
        some .right := by
  simp [physicalDirection, LBA.initCfgEnd, LBA.loadEnd, endmarkerScanCfg]

private theorem physicalDirection_endmarkerScanCfg_succ
    (D : DFA T Q) (word : List T) (index : Nat)
    (hindex : index < word.length) :
    physicalDirection
      (endmarkerScanCfg (Work := Work) D word index hindex.le)
      (endmarkerScanCfg (Work := Work) D word (index + 1) hindex) =
        some .right := by
  simp [physicalDirection, endmarkerScanCfg]

private theorem physicalDirection_endmarkerScanCfg_halt
    (D : DFA T Q) (word : List T) :
    physicalDirection
      (endmarkerScanCfg (Work := Work) D word word.length le_rfl)
      (endmarkerHaltCfg (Work := Work) D word) = none := by
  simp [physicalDirection, endmarkerScanCfg, endmarkerHaltCfg]

/-- The input-cell segment of the DFA scanner consists of exactly `index` rightward physical
movements. -/
theorem movementDirections_endmarkerScanTrace
    (D : DFA T Q) (word : List T) (index : Nat)
    (hindex : index ≤ word.length) :
    movementDirections (endmarkerScanTrace (Work := Work) D word index hindex) =
      List.replicate index .right := by
  induction index with
  | zero => rfl
  | succ index ih =>
      have hlt : index < word.length := by omega
      rw [endmarkerScanTrace, movementDirections_append, ih (by omega),
        movementDirections_single,
        physicalDirection_endmarkerScanCfg_succ (Work := Work) D word index hlt]
      simpa using (List.replicate_succ' (n := index)
        (a := Direction.right)).symm

/-- The complete DFA scanner moves only right; its final halting step is physically stationary. -/
theorem movementDirections_endmarkerTrace (D : DFA T Q) (word : List T) :
    movementDirections (endmarkerTrace (Work := Work) D word) =
      List.replicate (word.length + 1) .right := by
  rw [endmarkerTrace, movementDirections_append, movementDirections_single,
    physicalDirection_initial_endmarkerScanCfg,
    movementDirections_append, movementDirections_endmarkerScanTrace,
    movementDirections_single, physicalDirection_endmarkerScanCfg_halt]
  simp [List.replicate_succ]

/-- The existing explicit one-way DFA scanner has exactly zero physical head reversals. -/
@[simp] theorem headTurnCount_endmarkerTrace (D : DFA T Q) (word : List T) :
    headTurnCount (endmarkerTrace (Work := Work) D word) = 0 := by
  rw [headTurnCount, movementDirections_endmarkerTrace, changeCount_replicate]

/-- The explicit one-way DFA scanner supplies a selected-accepting head-turn promise with cap
zero. -/
theorem endmarkerLBA_hasUniformAcceptingHeadTurnBound_zero (D : DFA T Q) :
    LBA.BoundedCrossing.HasUniformAcceptingHeadTurnBound
      (endmarkerLBA (Work := Work) D) 0 := by
  intro word haccept
  have hdfa : word ∈ D.accepts :=
    (endmarkerLBA_accepts_iff (Work := Work) D word).mp haccept
  refine ⟨endmarkerHaltCfg (Work := Work) D word,
    endmarkerTrace (Work := Work) D word, ?_, ?_⟩
  · have hfinal : D.eval word ∈ D.accept := (DFA.mem_accepts D).mp hdfa
    simpa [endmarkerLBA, endmarkerHaltCfg] using hfinal
  · simp

end DFA

/-! ## Exact finite-state characterization at every fixed head-turn cap -/

open LBA.BoundedCrossing

variable {T : Type}

/-- Languages recognized by a finite-signature LBA having the advertised uniform cap on one
selected accepting trace per accepted canonical input.

This definition itself has no ambient typeclass assumptions: finiteness of the work alphabet
and state type is carried by the presentation witness. -/
def is_HeadTurnBoundedLBA (bound : Nat) (language : Language T) : Prop :=
  ∃ (Work State : Type) (_ : Fintype Work) (_ : Fintype State)
    (M : LBA.Machine (LBA.EndAlpha T Work) State),
    HasUniformAcceptingHeadTurnBound M bound ∧
      LBA.LanguageEnd M = language

/-- The language class presented by finite LBAs with uniform selected-accepting head-turn cap
`bound`. -/
def HeadTurnBoundedLBA (bound : Nat) : Set (Language T) :=
  setOf (is_HeadTurnBoundedLBA bound)

/-- Every finite LBA presentation with a uniform selected-accepting head-turn cap is
DFA-recognizable. -/
theorem is_DFA_of_is_HeadTurnBoundedLBA
    [Fintype T] {bound : Nat} {language : Language T}
    (hlanguage : is_HeadTurnBoundedLBA bound language) :
    is_DFA language := by
  obtain ⟨Work, State, hWork, hState, M, hbound, hM⟩ := hlanguage
  letI : Fintype Work := hWork
  letI : Fintype State := hState
  rw [← hM]
  exact is_DFA_languageEnd_of_hasUniformAcceptingHeadTurnBound M hbound

/-- Every DFA language has a finite LBA presentation at every head-turn cap.  The witness is the
explicit one-way scanner, whose selected accepting trace has zero turns. -/
theorem is_HeadTurnBoundedLBA_of_is_DFA
    (bound : Nat) {language : Language T} (hlanguage : is_DFA language) :
    is_HeadTurnBoundedLBA bound language := by
  classical
  obtain ⟨State, hState, D, hD⟩ := hlanguage
  letI : Fintype State := hState
  let M := DFA.endmarkerLBA (Work := Unit) D
  refine ⟨Unit, DFA.EndmarkerLBAState State, inferInstance, inferInstance,
    M, ?_, ?_⟩
  · exact (DFA.endmarkerLBA_hasUniformAcceptingHeadTurnBound_zero
      (Work := Unit) D).mono (Nat.zero_le bound)
  · exact (DFA.languageEnd_endmarkerLBA_eq D).trans hD

/-- For every natural cap, finite uniformly head-turn-bounded LBA presentations are exactly DFA
presentations.  No positivity assumption on the cap is needed. -/
theorem is_HeadTurnBoundedLBA_iff_is_DFA
    [Fintype T] (bound : Nat) (language : Language T) :
    is_HeadTurnBoundedLBA bound language ↔ is_DFA language :=
  ⟨is_DFA_of_is_HeadTurnBoundedLBA,
    is_HeadTurnBoundedLBA_of_is_DFA bound⟩

/-- Set equality with the DFA class at every fixed head-turn cap. -/
theorem HeadTurnBoundedLBA_eq_DFA [Fintype T] (bound : Nat) :
    (HeadTurnBoundedLBA bound : Set (Language T)) = DFA.Class := by
  ext language
  exact is_HeadTurnBoundedLBA_iff_is_DFA bound language

/-- NFA form of the exact characterization. -/
theorem is_HeadTurnBoundedLBA_iff_is_NFA
    [Fintype T] (bound : Nat) (language : Language T) :
    is_HeadTurnBoundedLBA bound language ↔ is_NFA language :=
  (is_HeadTurnBoundedLBA_iff_is_DFA bound language).trans
    is_NFA_iff_is_DFA.symm

/-- Set equality with the NFA class at every fixed head-turn cap. -/
theorem HeadTurnBoundedLBA_eq_NFA [Fintype T] (bound : Nat) :
    (HeadTurnBoundedLBA bound : Set (Language T)) = NFA.Class := by
  rw [HeadTurnBoundedLBA_eq_DFA, ← NFA_eq_DFA]

/-- Mathlib-regular form of the exact characterization. -/
theorem is_HeadTurnBoundedLBA_iff_isRegular
    [Fintype T] (bound : Nat) (language : Language T) :
    is_HeadTurnBoundedLBA bound language ↔ language.IsRegular := by
  rw [is_HeadTurnBoundedLBA_iff_is_DFA]
  exact Language.isRegular_iff.symm

/-- Set equality with Mathlib's regular-language predicate at every fixed head-turn cap. -/
theorem HeadTurnBoundedLBA_eq_isRegular [Fintype T] (bound : Nat) :
    (HeadTurnBoundedLBA bound : Set (Language T)) =
      {language | language.IsRegular} := by
  ext language
  exact is_HeadTurnBoundedLBA_iff_isRegular bound language

/-- A finite uniformly head-turn-bounded LBA presentation gives a deterministic-LBA
presentation whenever the ambient alphabet carries the instances required by `is_DLBA`. -/
theorem is_DLBA_of_is_HeadTurnBoundedLBA
    [Fintype T] [DecidableEq T]
    {bound : Nat} {language : Language T}
    (hlanguage : is_HeadTurnBoundedLBA bound language) :
    is_DLBA language := by
  obtain ⟨Work, State, hWork, hState, M, hbound, hM⟩ := hlanguage
  letI : Fintype Work := hWork
  letI : Fintype State := hState
  rw [← hM]
  exact is_DLBA_languageEnd_of_hasUniformAcceptingHeadTurnBound M hbound

/-- Direct class inclusion into deterministic linearly bounded languages. -/
theorem HeadTurnBoundedLBA_subset_DLBA
    [Fintype T] [DecidableEq T] (bound : Nat) :
    (HeadTurnBoundedLBA bound : Set (Language T)) ⊆ DLBA := by
  intro language hlanguage
  exact is_DLBA_of_is_HeadTurnBoundedLBA hlanguage

end
