module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.CanonicalSimulation
public import Langlib.Automata.LinearBounded.GraphWalking.BoundedEulerBridge
public import Langlib.Automata.LinearBounded.GraphWalking.ReversibleCore
import Mathlib.Tactic

@[expose]
public section

/-!
# Semantic correctness of the boundary-marked deterministic machine

The raw Euler probe operates on `PlainCode` cells so that it can inspect the
physical boundary before attempting a partial memory move.  This module
forgets that immutable boundary annotation and relates `markedMachine` back
to its source deterministic endmarker machine.

The relation is stated for every bounded-tape width.  In particular, the
one-cell raw width uses the `both` boundary code, while canonical endmarker
inputs have at least two cells and are handled without a nonempty-word
exception.
-/

namespace GraphWalking

open Relation

universe uTerminal uWork uState

namespace MarkedEulerProbe

noncomputable section

/-! ## Forgetting the immutable boundary annotation -/

/-- Pointwise logical projection of a plain-code tape. -/
@[expose]
public def logicalTape
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    DLBA.BoundedTape (LogicalAlphabet T Gamma) n where
  contents position := (tape.contents position).logical
  head := tape.head

@[simp]
public theorem logicalTape_read
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n) :
    (logicalTape tape).read = tape.read.logical := rfl

@[simp]
public theorem logicalTape_moveHead
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (direction : DLBA.Dir) :
    logicalTape (tape.moveHead direction) =
      (logicalTape tape).moveHead direction := by
  rfl

/-- Writing a packed logical symbol and then forgetting the annotation is
exactly an ordinary logical write. -/
@[simp]
public theorem logicalTape_write_packed
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (written : LogicalAlphabet T Gamma) :
    logicalTape (tape.write (.packed tape.read.boundary written)) =
      (logicalTape tape).write written := by
  apply BoundedTapeMemory.eq_of_contents_head
  · funext position
    by_cases hposition : position = tape.head
    · subst position
      simp [logicalTape, DLBA.BoundedTape.write, PlainCode.logical]
    · simp [logicalTape, DLBA.BoundedTape.write, hposition]
  · rfl

/-- Packing a write preserves the exact physical-boundary annotation. -/
public theorem wellBoundaryCoded_write_packed
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (written : LogicalAlphabet T Gamma) :
    WellBoundaryCoded (tape.write (.packed tape.read.boundary written)) := by
  intro position
  by_cases hposition : position = tape.head
  · subst position
    simpa [DLBA.BoundedTape.write, PlainCode.boundary] using hwell tape.head
  · simpa [DLBA.BoundedTape.write, PlainCode.boundary, hposition] using
      hwell position

/-- On a correctly annotated tape, replacing an outward clamped instruction
by `stay` has exactly the same physical effect as the original direction. -/
public theorem moveHead_normalizeDirection_eq
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) (direction : DLBA.Dir) :
    tape.moveHead (tape.read.normalizeDirection direction) =
      tape.moveHead direction := by
  cases direction with
  | stay => rfl
  | left =>
      have hboundary : tape.read.boundary = physicalBoundary tape.head :=
        hwell tape.head
      by_cases hinside : 0 < tape.head.val
      · have hallows : tape.read.boundary.allows .left = true := by
          rw [hboundary, physicalBoundary_allows_left_iff]
          exact hinside
        have hnormalize : tape.read.normalizeDirection .left = .left := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.left = true
            then DLBA.Dir.left else DLBA.Dir.stay) = DLBA.Dir.left
          change (tape.contents tape.head).boundary.allows
            BoundedTapeMemory.Travel.left = true at hallows
          simp [hallows]
        rw [hnormalize]
      · have hnotAllows : tape.read.boundary.allows .left = false := by
          apply Bool.eq_false_of_not_eq_true
          rw [hboundary, physicalBoundary_allows_left_iff]
          exact hinside
        have hzero : tape.head.val = 0 := by omega
        have hnormalize : tape.read.normalizeDirection .left = .stay := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.left = true
            then DLBA.Dir.left else DLBA.Dir.stay) = DLBA.Dir.stay
          change (tape.contents tape.head).boundary.allows
            BoundedTapeMemory.Travel.left = false at hnotAllows
          simp [hnotAllows]
        rw [hnormalize]
        simp [DLBA.BoundedTape.moveHead, hzero]
  | right =>
      have hboundary : tape.read.boundary = physicalBoundary tape.head :=
        hwell tape.head
      by_cases hinside : tape.head.val < n
      · have hallows : tape.read.boundary.allows .right = true := by
          rw [hboundary, physicalBoundary_allows_right_iff]
          exact hinside
        have hnormalize : tape.read.normalizeDirection .right = .right := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.right = true
            then DLBA.Dir.right else DLBA.Dir.stay) = DLBA.Dir.right
          change (tape.contents tape.head).boundary.allows
            BoundedTapeMemory.Travel.right = true at hallows
          simp [hallows]
        rw [hnormalize]
      · have hnotAllows : tape.read.boundary.allows .right = false := by
          apply Bool.eq_false_of_not_eq_true
          rw [hboundary, physicalBoundary_allows_right_iff]
          exact hinside
        have hlast : tape.head.val = n := by
          have := tape.head.isLt
          omega
        have hnormalize : tape.read.normalizeDirection .right = .stay := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.right = true
            then DLBA.Dir.right else DLBA.Dir.stay) = DLBA.Dir.stay
          change (tape.contents tape.head).boundary.allows
            BoundedTapeMemory.Travel.right = false at hnotAllows
          simp [hnotAllows]
        rw [hnormalize]
        simp [DLBA.BoundedTape.moveHead, hlast]

/-- The packed write retains precisely the boundary information consulted by
direction normalization. -/
public theorem normalizeDirection_read_write_packed
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (written : LogicalAlphabet T Gamma) (direction : DLBA.Dir) :
    ((tape.write (.packed tape.read.boundary written)).read).normalizeDirection
        direction =
      tape.read.normalizeDirection direction := by
  cases direction <;>
    simp [PlainCode.normalizeDirection, DLBA.BoundedTape.read,
      DLBA.BoundedTape.write, PlainCode.boundary]

/-- A marked write-and-move projects to exactly the source machine's clamped
write-and-move operation. -/
public theorem logicalTape_write_move_normalize
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape)
    (written : LogicalAlphabet T Gamma) (direction : DLBA.Dir) :
    logicalTape
        ((tape.write (.packed tape.read.boundary written)).moveHead
          (tape.read.normalizeDirection direction)) =
      ((logicalTape tape).write written).moveHead direction := by
  let updated := tape.write (.packed tape.read.boundary written)
  have hwellUpdated : WellBoundaryCoded updated :=
    wellBoundaryCoded_write_packed tape hwell written
  have hnormalize : updated.read.normalizeDirection direction =
      tape.read.normalizeDirection direction :=
    normalizeDirection_read_write_packed tape written direction
  have hmove : updated.moveHead (tape.read.normalizeDirection direction) =
      updated.moveHead direction := by
    rw [← hnormalize]
    exact moveHead_normalizeDirection_eq updated hwellUpdated direction
  rw [hmove, logicalTape_moveHead, logicalTape_write_packed]

/-! ## Exact deterministic-step projection -/

/-- Forget the boundary annotation in a deterministic configuration. -/
@[expose]
public def logicalCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (PlainCode T Gamma) Q n) :
    DLBA.Cfg (LogicalAlphabet T Gamma) Q n where
  state := configuration.state
  tape := logicalTape configuration.tape

@[simp]
public theorem logicalCfg_state
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (PlainCode T Gamma) Q n) :
    (logicalCfg configuration).state = configuration.state := rfl

@[simp]
public theorem logicalCfg_tape
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (configuration : DLBA.Cfg (PlainCode T Gamma) Q n) :
    (logicalCfg configuration).tape = logicalTape configuration.tape := rfl

/-- On every boundary-correct tape, the marked deterministic step projects
exactly—including halting—to the source deterministic step. -/
public theorem optionMap_logicalCfg_step_markedMachine
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (configuration : DLBA.Cfg (PlainCode T Gamma) Q n)
    (hwell : WellBoundaryCoded configuration.tape) :
    Option.map logicalCfg (DLBA.step (markedMachine machine) configuration) =
      DLBA.step machine (logicalCfg configuration) := by
  rcases configuration with ⟨state, tape⟩
  cases htransition : machine.transition state tape.read.logical with
  | none =>
      change machine.transition state (tape.contents tape.head).logical = none at htransition
      simp [DLBA.step, markedMachine, logicalCfg, logicalTape, htransition]
  | some output =>
      rcases output with ⟨target, written, direction⟩
      simp only [DLBA.step, markedMachine, logicalCfg, logicalTape_read,
        htransition, Option.map_some]
      apply congrArg some
      congr 1
      exact logicalTape_write_move_normalize tape hwell written direction

/-- A marked deterministic step preserves boundary correctness. -/
public theorem wellBoundaryCoded_of_step_markedMachine
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : DLBA.Cfg (PlainCode T Gamma) Q n}
    (hwell : WellBoundaryCoded source.tape)
    (hstep : DLBA.step (markedMachine machine) source = some target) :
    WellBoundaryCoded target.tape := by
  rcases source with ⟨state, tape⟩
  cases htransition : machine.transition state tape.read.logical with
  | none =>
      change machine.transition state (tape.contents tape.head).logical = none at htransition
      simp [DLBA.step, markedMachine, htransition] at hstep
  | some output =>
      rcases output with ⟨targetState, written, direction⟩
      have htransition' : machine.transition state
          (tape.contents tape.head).logical =
          some (targetState, written, direction) := htransition
      simp [DLBA.step, markedMachine, htransition'] at hstep
      subst target
      apply wellBoundaryCoded_moveHead
      exact wellBoundaryCoded_write_packed tape hwell written

/-- Boundary correctness also reflects across a marked deterministic step.

This reverse form is needed by the local-port swap: an incoming port crosses
one controller edge against its computational orientation.  The marked write
stores exactly the old cell's immutable boundary code, so the write-and-move
operation cannot repair an incorrectly coded source boundary. -/
public theorem wellBoundaryCoded_source_of_step_markedMachine
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : DLBA.Cfg (PlainCode T Gamma) Q n}
    (hwell : WellBoundaryCoded target.tape)
    (hstep : DLBA.step (markedMachine machine) source = some target) :
    WellBoundaryCoded source.tape := by
  rcases source with ⟨state, tape⟩
  cases htransition : machine.transition state tape.read.logical with
  | none =>
      change machine.transition state
          (tape.contents tape.head).logical = none at htransition
      simp [DLBA.step, markedMachine, htransition] at hstep
  | some output =>
      rcases output with ⟨targetState, written, direction⟩
      have htransition' : machine.transition state
          (tape.contents tape.head).logical =
          some (targetState, written, direction) := htransition
      simp [DLBA.step, markedMachine, htransition'] at hstep
      subst target
      intro position
      have htarget := hwell position
      change
        (((tape.write (.packed tape.read.boundary written)).moveHead
          (tape.read.normalizeDirection direction)).contents position).boundary =
            physicalBoundary position at htarget
      have hcontents :
          ((tape.write (.packed tape.read.boundary written)).moveHead
            (tape.read.normalizeDirection direction)).contents =
          (tape.write (.packed tape.read.boundary written)).contents := by
        cases tape.read.normalizeDirection direction <;> rfl
      rw [hcontents] at htarget
      by_cases hposition : position = tape.head
      · subst position
        simpa [DLBA.BoundedTape.write, PlainCode.boundary] using htarget
      · simpa [DLBA.BoundedTape.write, hposition] using htarget

/-- Every marked step projects to the exact source step. -/
public theorem step_logicalCfg_of_step_markedMachine
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : DLBA.Cfg (PlainCode T Gamma) Q n}
    (hwell : WellBoundaryCoded source.tape)
    (hstep : DLBA.step (markedMachine machine) source = some target) :
    DLBA.step machine (logicalCfg source) = some (logicalCfg target) := by
  rw [← optionMap_logicalCfg_step_markedMachine machine source hwell, hstep]
  rfl

/-- Conversely, a source step from a represented configuration has a unique
marked successor representing its target. -/
public theorem exists_step_markedMachine_of_step_logicalCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (source : DLBA.Cfg (PlainCode T Gamma) Q n)
    (hwell : WellBoundaryCoded source.tape)
    {target : DLBA.Cfg (LogicalAlphabet T Gamma) Q n}
    (hstep : DLBA.step machine (logicalCfg source) = some target) :
    exists markedTarget,
      DLBA.step (markedMachine machine) source = some markedTarget ∧
      logicalCfg markedTarget = target ∧
      WellBoundaryCoded markedTarget.tape := by
  have hmap := optionMap_logicalCfg_step_markedMachine machine source hwell
  rw [hstep] at hmap
  cases hmarked : DLBA.step (markedMachine machine) source with
  | none =>
      rw [hmarked] at hmap
      simp at hmap
  | some markedTarget =>
      rw [hmarked] at hmap
      have hlogical : logicalCfg markedTarget = target := by
        exact Option.some.inj hmap
      exact ⟨markedTarget, rfl, hlogical,
        wellBoundaryCoded_of_step_markedMachine machine hwell hmarked⟩

/-! ## Whole-run representation -/

/-- Every marked run from a boundary-correct tape projects to a source run,
and its final tape remains boundary-correct. -/
public theorem reaches_logicalCfg_of_reaches_markedMachine
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : DLBA.Cfg (PlainCode T Gamma) Q n}
    (hwell : WellBoundaryCoded source.tape)
    (hreaches : ReflTransGen
      (fun left right => DLBA.step (markedMachine machine) left = some right)
      source target) :
    ReflTransGen (fun left right => DLBA.step machine left = some right)
        (logicalCfg source) (logicalCfg target) ∧
      WellBoundaryCoded target.tape := by
  induction hreaches with
  | refl => exact ⟨.refl, hwell⟩
  | @tail middle target hprefix hlast ih =>
      exact ⟨ih.1.tail
          (step_logicalCfg_of_step_markedMachine machine ih.2 hlast),
        wellBoundaryCoded_of_step_markedMachine machine ih.2 hlast⟩

/-- Every source run lifts from any represented boundary-correct
configuration.  The marked endpoint is existential because logical
projection intentionally forgets the concrete plain-code constructor. -/
public theorem exists_reaches_markedMachine_of_reaches_logicalCfg
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (source : DLBA.Cfg (PlainCode T Gamma) Q n)
    (hwell : WellBoundaryCoded source.tape)
    {target : DLBA.Cfg (LogicalAlphabet T Gamma) Q n}
    (hreaches : ReflTransGen
      (fun left right => DLBA.step machine left = some right)
      (logicalCfg source) target) :
    exists markedTarget,
      ReflTransGen
        (fun left right => DLBA.step (markedMachine machine) left = some right)
        source markedTarget ∧
      logicalCfg markedTarget = target ∧
      WellBoundaryCoded markedTarget.tape := by
  generalize hstart : logicalCfg source = logicalStart at hreaches
  induction hreaches generalizing source with
  | refl =>
      exact ⟨source, .refl, hstart, hwell⟩
  | @tail middle target hprefix hlast ih =>
      obtain ⟨markedMiddle, hmarkedPrefix, hlogicalMiddle, hwellMiddle⟩ :=
        ih source hwell hstart
      have hlast' : DLBA.step machine (logicalCfg markedMiddle) = some target := by
        simpa [hlogicalMiddle] using hlast
      obtain ⟨markedTarget, hmarkedLast, hlogicalTarget, hwellTarget⟩ :=
        exists_step_markedMachine_of_step_logicalCfg
          machine markedMiddle hwellMiddle hlast'
      exact ⟨markedTarget, hmarkedPrefix.tail hmarkedLast,
        hlogicalTarget, hwellTarget⟩

/-! ## Terminal acceptance and canonical input -/

/-- Terminal acceptance of the logical source is inherited by the marked
machine. -/
public theorem markedMachine_terminalAcceptance
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hterminal : forall state observed, machine.accept state = true ->
      machine.transition state observed = none) :
    forall state observed, (markedMachine machine).accept state = true ->
      (markedMachine machine).transition state observed = none := by
  intro state observed haccept
  have hnone := hterminal state observed.logical haccept
  simp [markedMachine, hnone]

/-- For a terminal-accepting source, a represented boundary-correct
configuration is accepted by the marked machine exactly when its logical
projection is accepted by the source. -/
public theorem accepts_markedMachine_iff
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hterminal : forall state observed, machine.accept state = true ->
      machine.transition state observed = none)
    (source : DLBA.Cfg (PlainCode T Gamma) Q n)
    (hwell : WellBoundaryCoded source.tape) :
    DLBA.Accepts (markedMachine machine) source <->
      DLBA.Accepts machine (logicalCfg source) := by
  rw [BoundedEulerBridge.dlbaAccepts_iff_exists_reaches_accepting_of_terminal
      (markedMachine machine) (markedMachine_terminalAcceptance machine hterminal)
      source,
    BoundedEulerBridge.dlbaAccepts_iff_exists_reaches_accepting_of_terminal
      machine hterminal (logicalCfg source)]
  constructor
  · rintro ⟨target, hreaches, haccept⟩
    have hprojected :=
      reaches_logicalCfg_of_reaches_markedMachine machine hwell hreaches
    exact ⟨logicalCfg target, hprojected.1, haccept⟩
  · rintro ⟨target, hreaches, haccept⟩
    obtain ⟨markedTarget, hmarked, hlogical, _hwellTarget⟩ :=
      exists_reaches_markedMachine_of_reaches_logicalCfg
        machine source hwell hreaches
    refine ⟨markedTarget, hmarked, ?_⟩
    simpa [← hlogical] using haccept

/-- Logical projection of the exact plain-code input is the repository's
canonical endmarker input, including `epsilon`. -/
@[simp]
public theorem logicalTape_plainLoadEnd
    {T : Type uTerminal} {Gamma : Type uWork} (word : List T) :
    logicalTape (plainLoadEnd (Gamma := Gamma) word) =
      LBA.loadEnd (Γ := Gamma) word := by
  apply BoundedTapeMemory.eq_of_contents_head
  · funext position
    simp only [logicalTape, plainLoadEnd, LBA.loadEnd]
    split
    · rfl
    · split
      · rfl
      · rfl
  · rfl

/-- Initial marked acceptance is exactly initial source acceptance on the
same bracketed word. -/
public theorem accepts_markedMachine_plainLoadEnd_iff
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hterminal : forall state observed, machine.accept state = true ->
      machine.transition state observed = none)
    (word : List T) :
    DLBA.Accepts (markedMachine machine)
        ⟨machine.initial, plainLoadEnd (Gamma := Gamma) word⟩ <->
      DLBA.Accepts machine
        ⟨machine.initial, LBA.loadEnd (Γ := Gamma) word⟩ := by
  simpa [logicalCfg] using
    (accepts_markedMachine_iff machine hterminal
      (⟨machine.initial, plainLoadEnd (Gamma := Gamma) word⟩ :
        DLBA.Cfg (PlainCode T Gamma) Q (word.length + 1))
      (plainLoadEnd_wellBoundaryCoded word))

/-! ## The marked machine and its partial bounded-tape controller -/

/-- Direction normalization always produces an instruction executable by the
partial bounded-tape memory graph. -/
public theorem nonclamping_normalizeDirection
    {T : Type uTerminal} {Gamma : Type uWork} {n : Nat}
    (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) (direction : DLBA.Dir) :
    BoundedTapeController.Nonclamping tape
      (tape.read.normalizeDirection direction) := by
  cases direction with
  | stay => trivial
  | left =>
      by_cases hallows : tape.read.boundary.allows
          BoundedTapeMemory.Travel.left = true
      · have hnormalize : tape.read.normalizeDirection .left = .left := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.left = true
            then DLBA.Dir.left else DLBA.Dir.stay) = DLBA.Dir.left
          change (tape.contents tape.head).boundary.allows
            BoundedTapeMemory.Travel.left = true at hallows
          simp [hallows]
        rw [hnormalize]
        change 0 < tape.head.val
        rw [← physicalBoundary_allows_left_iff tape.head]
        rw [← hwell tape.head]
        exact hallows
      · have hnormalize : tape.read.normalizeDirection .left = .stay := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.left = true
            then DLBA.Dir.left else DLBA.Dir.stay) = DLBA.Dir.stay
          have hfalse : (tape.contents tape.head).boundary.allows
              BoundedTapeMemory.Travel.left = false := by
            apply Bool.eq_false_of_not_eq_true
            exact hallows
          simp [hfalse]
        rw [hnormalize]
        trivial
  | right =>
      by_cases hallows : tape.read.boundary.allows
          BoundedTapeMemory.Travel.right = true
      · have hnormalize : tape.read.normalizeDirection .right = .right := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.right = true
            then DLBA.Dir.right else DLBA.Dir.stay) = DLBA.Dir.right
          change (tape.contents tape.head).boundary.allows
            BoundedTapeMemory.Travel.right = true at hallows
          simp [hallows]
        rw [hnormalize]
        change tape.head.val < n
        rw [← physicalBoundary_allows_right_iff tape.head]
        rw [← hwell tape.head]
        exact hallows
      · have hnormalize : tape.read.normalizeDirection .right = .stay := by
          change (if tape.read.boundary.allows BoundedTapeMemory.Travel.right = true
            then DLBA.Dir.right else DLBA.Dir.stay) = DLBA.Dir.stay
          have hfalse : (tape.contents tape.head).boundary.allows
              BoundedTapeMemory.Travel.right = false := by
            apply Bool.eq_false_of_not_eq_true
            exact hallows
          simp [hfalse]
        rw [hnormalize]
        trivial

/-- Every instruction emitted by the marked machine is nonclamping on a
boundary-correct tape.  This is why no endmarker-guard premise is needed at
this representation layer. -/
public theorem markedMachine_transitionNonclamping
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (state : Q) (tape : DLBA.BoundedTape (PlainCode T Gamma) n)
    (hwell : WellBoundaryCoded tape) :
    BoundedTapeController.TransitionNonclamping
      (markedMachine machine) state tape := by
  intro target written direction htransition
  cases hsource : machine.transition state tape.read.logical with
  | none =>
      have hsource' : machine.transition state
          (tape.contents tape.head).logical = none := hsource
      simp [markedMachine, hsource'] at htransition
  | some output =>
      rcases output with ⟨sourceTarget, sourceWritten, sourceDirection⟩
      have hsource' : machine.transition state
          (tape.contents tape.head).logical =
          some (sourceTarget, sourceWritten, sourceDirection) := hsource
      change Option.map
          (fun output =>
            (output.1, .packed tape.read.boundary output.2.1,
              tape.read.normalizeDirection output.2.2))
          (machine.transition state tape.read.logical) =
        some (target, written, direction) at htransition
      rw [hsource] at htransition
      have houtput := Option.some.inj htransition
      have hdirection :
          tape.read.normalizeDirection sourceDirection = direction :=
        congrArg (fun output => output.2.2) houtput
      rw [← hdirection]
      exact nonclamping_normalizeDirection tape hwell sourceDirection

/-- On a boundary-correct tape, one partial-memory controller edge is exactly
one marked deterministic step. -/
public theorem controller_step_iff_marked_step
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {state targetState : Q}
    {tape targetTape : DLBA.BoundedTape (PlainCode T Gamma) n}
    (hwell : WellBoundaryCoded tape) :
    (BoundedTapeController.machine (markedMachine machine)).Step
        (BoundedTapeMemory.graph (PlainCode T Gamma) n)
        (state, tape) (targetState, targetTape) <->
      DLBA.step (markedMachine machine) ⟨state, tape⟩ =
        some ⟨targetState, targetTape⟩ := by
  apply BoundedTapeController.step_iff_dlba_step_of_transitionNonclamping
  exact markedMachine_transitionNonclamping machine state tape hwell

/-- Controller reachability and marked deterministic reachability coincide
from every boundary-correct start, and the invariant remains true at the
endpoint. -/
public theorem controller_reaches_iff_marked_reaches
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : DLBA.Cfg (PlainCode T Gamma) Q n}
    (hwell : WellBoundaryCoded source.tape) :
    ReflTransGen
        ((BoundedTapeController.machine (markedMachine machine)).Step
          (BoundedTapeMemory.graph (PlainCode T Gamma) n))
        (source.state, source.tape) (target.state, target.tape) <->
      ReflTransGen
        (fun left right => DLBA.step (markedMachine machine) left = some right)
        source target := by
  constructor
  · intro hcontroller
    exact BoundedTapeController.reaches_sound (markedMachine machine) hcontroller
  · intro hmarked
    induction hmarked with
    | refl => exact .refl
    | @tail middle target hprefix hlast ih =>
        have hwellMiddle :=
          (reaches_logicalCfg_of_reaches_markedMachine
            machine hwell hprefix).2
        exact ih.tail ((controller_step_iff_marked_step
          machine hwellMiddle).2 hlast)

/-- Terminal marked acceptance is equivalent to accepting reachability in
the partial bounded-tape controller. -/
public theorem accepts_markedMachine_iff_controller_reaches_accepting
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hterminal : forall state observed, machine.accept state = true ->
      machine.transition state observed = none)
    (source : DLBA.Cfg (PlainCode T Gamma) Q n)
    (hwell : WellBoundaryCoded source.tape) :
    DLBA.Accepts (markedMachine machine) source <->
      exists accept,
        (BoundedTapeController.machine (markedMachine machine)).Accepting
          (BoundedTapeMemory.graph (PlainCode T Gamma) n) accept ∧
        ReflTransGen
          ((BoundedTapeController.machine (markedMachine machine)).Step
            (BoundedTapeMemory.graph (PlainCode T Gamma) n))
          (source.state, source.tape) accept := by
  rw [BoundedEulerBridge.dlbaAccepts_iff_exists_reaches_accepting_of_terminal
    (markedMachine machine) (markedMachine_terminalAcceptance machine hterminal)
    source]
  constructor
  · rintro ⟨target, hreaches, haccept⟩
    exact ⟨(target.state, target.tape), haccept,
      (controller_reaches_iff_marked_reaches machine hwell).2 hreaches⟩
  · rintro ⟨⟨targetState, targetTape⟩, haccept, hreaches⟩
    exact ⟨⟨targetState, targetTape⟩,
      (controller_reaches_iff_marked_reaches machine hwell).1 hreaches,
      haccept⟩

/-! ## The undoubled local Euler criterion used by the raw compiler -/

/-- Local port system of the marked direction-determinate controller at an
arbitrary tape width. -/
@[expose]
public noncomputable def markedPorts
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q) (n : Nat) :=
  LocalPort.ofMachine
    (walker machine)
    (BoundedTapeMemory.graph (PlainCode T Gamma) n)
    (BoundedTapeController.machine
      (markedMachine machine)).directionLiftArrival

private theorem wellBoundaryCoded_of_walker_weakReaches
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [DecidableEq T] [DecidableEq Gamma]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    {source target : GraphWalking.Configuration (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n)}
    (hwell : WellBoundaryCoded source.2)
    (hreaches : ReflTransGen
      (FunctionalGraphReversibleTraversal.WeakStep
        ((walker machine).Step
          (BoundedTapeMemory.graph (PlainCode T Gamma) n)))
      source target) :
    WellBoundaryCoded target.2 := by
  induction hreaches with
  | refl => exact hwell
  | @tail middle target _ hlast ih =>
      have hwellMiddle := ih
      rcases hlast with hforward | hbackward
      · have hcontroller :=
          (BoundedTapeController.machine (markedMachine machine)).step_forgetDirection
            (BoundedTapeMemory.graph (PlainCode T Gamma) n) hforward
        have hmarked := BoundedTapeController.step_sound
          (markedMachine machine) hcontroller
        exact wellBoundaryCoded_of_step_markedMachine
          machine hwellMiddle hmarked
      · have hcontroller :=
          (BoundedTapeController.machine (markedMachine machine)).step_forgetDirection
            (BoundedTapeMemory.graph (PlainCode T Gamma) n) hbackward
        have hmarked := BoundedTapeController.step_sound
          (markedMachine machine) hcontroller
        exact wellBoundaryCoded_source_of_step_markedMachine
          machine hwellMiddle hmarked

/-- One undoubled local-Euler operation preserves the immutable physical
boundary annotation.  The proof handles both outgoing (forward) and incoming
(backward) swaps, rather than assuming that every Euler edge follows the
controller's computational orientation. -/
public theorem wellBoundaryCoded_euler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState} {n : Nat}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (port : LocalPort.Port (LiftState T Gamma Q)
      (DLBA.BoundedTape (PlainCode T Gamma) n))
    (hwell : WellBoundaryCoded port.1.2) :
    WellBoundaryCoded (((markedPorts machine n).euler port).1.2) := by
  let rotated := (markedPorts machine n).rotate port
  have hendpoint := (markedPorts machine n).rotate_endpoint port
  have hrotatedWell : WellBoundaryCoded rotated.1.2 := by
    change rotated.1 = port.1 at hendpoint
    rw [hendpoint]
    exact hwell
  have hweak := (markedPorts machine n).swap_sound rotated
  have hswappedWell := wellBoundaryCoded_of_walker_weakReaches
    machine hrotatedWell hweak
  simpa [FunctionalGraphReversibleTraversal.PortSystem.euler, rotated] using
    hswappedWell

/-- Initial remembered operation of the marked direction lift. -/
@[expose]
public def markedInitialDirection
    (T : Type uTerminal) (Gamma : Type uWork) :
    BoundedTapeMemory.Direction (PlainCode T Gamma) :=
  .stationary .leftMarker .leftMarker

/-- For every finite source machine with terminal acceptance, acceptance on
the canonical bracketed word is exactly accepting reachability in the
undoubled marked local-Euler orbit.  The raw compiler's microstep phase is
deliberately absent from this statement: macro paths have mixed parity. -/
public theorem sourceAccepts_iff_markedEuler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (LogicalAlphabet T Gamma) Q)
    (hterminal : forall state observed, machine.accept state = true ->
      machine.transition state observed = none)
    (word : List T) :
    DLBA.Accepts machine
        ⟨machine.initial, LBA.loadEnd (Γ := Gamma) word⟩ <->
      exists finish,
        ReflTransGen (markedPorts machine (word.length + 1)).EulerEdge
          (initialPort machine word) finish ∧
        (BoundedTapeController.machine (markedMachine machine)).Accepting
          (BoundedTapeMemory.graph (PlainCode T Gamma) (word.length + 1))
          (forgetDirection
            ((markedPorts machine (word.length + 1)).endpoint finish)) := by
  rw [← accepts_markedMachine_plainLoadEnd_iff machine hterminal word]
  rw [accepts_markedMachine_iff_controller_reaches_accepting
    machine hterminal
      (⟨machine.initial, plainLoadEnd (Gamma := Gamma) word⟩ :
        DLBA.Cfg (PlainCode T Gamma) Q (word.length + 1))
      (plainLoadEnd_wellBoundaryCoded word)]
  let base := BoundedTapeController.machine (markedMachine machine)
  let graph := BoundedTapeMemory.graph
    (PlainCode T Gamma) (word.length + 1)
  have hbaseTerminal : base.TerminalAcceptance := by
    apply BoundedTapeController.machine_terminalAcceptance
    exact markedMachine_terminalAcceptance machine hterminal
  have heuler := directionLift_localEuler_accepting_iff
    base graph (markedInitialDirection T Gamma) hbaseTerminal
    (machine.initial, plainLoadEnd (Gamma := Gamma) word)
  simpa [base, graph, markedPorts, walker, initialPort,
    markedInitialDirection, LocalPort.anchor] using heuler.symm

/-! ## Marker-free deterministic source presentation -/

/-- The existing endmarker simulator is an exact acceptance presentation of
the marker-free deterministic language, stated without passing through the
Euler criterion in the conclusion. -/
public theorem sourceLanguage_iff_deterministicSimMachineAccepts
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) Q)
    (acceptEmpty : Bool) (word : List T) :
    DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
        acceptEmpty word <->
      DLBA.Accepts
        (EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty)
        (BoundedEulerBridge.simulatorStart machine acceptEmpty word) := by
  exact (BoundedEulerBridge.sourceLanguage_iff_phaseDoubledLocalEuler
    machine acceptEmpty word false).trans
      (BoundedEulerBridge.simulatorAccepts_iff_phaseDoubledLocalEuler
        machine acceptEmpty word false).symm

/-- Complete semantic criterion for the marked compiler before raw
microstep refinement: marker-free source membership is equivalent to an
accepting port on the undoubled local Euler orbit of the boundary-marked
endmarker simulator. -/
public theorem sourceLanguage_iff_markedSimulatorEuler
    {T : Type uTerminal} {Gamma : Type uWork} {Q : Type uState}
    [Fintype T] [Fintype Gamma] [Fintype Q]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq Q]
    (machine : DLBA.Machine (Option (T ⊕ Gamma)) Q)
    (acceptEmpty : Bool) (word : List T) :
    DLBA.LanguageRecognized machine (fun input => some (Sum.inl input))
        acceptEmpty word <->
      let simulator :=
        EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
      exists finish,
        ReflTransGen (markedPorts simulator (word.length + 1)).EulerEdge
          (initialPort simulator word) finish ∧
        (BoundedTapeController.machine (markedMachine simulator)).Accepting
          (BoundedTapeMemory.graph (PlainCode T Gamma) (word.length + 1))
          (forgetDirection
            ((markedPorts simulator (word.length + 1)).endpoint finish)) := by
  let simulator :=
    EndmarkerNonclamping.deterministicSimMachine machine acceptEmpty
  have hsource :=
    sourceLanguage_iff_deterministicSimMachineAccepts
      machine acceptEmpty word
  have heuler := sourceAccepts_iff_markedEuler simulator
    (EndmarkerNonclamping.deterministicSimMachine_terminalAcceptance
      machine acceptEmpty) word
  exact hsource.trans (by
    simpa [simulator, BoundedEulerBridge.simulatorStart] using heuler)

end

end MarkedEulerProbe

end GraphWalking

end
