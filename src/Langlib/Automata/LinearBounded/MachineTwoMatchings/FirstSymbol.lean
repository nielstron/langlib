module

public import Langlib.Automata.LinearBounded.MachineTwoMatchings.Definition
public import Langlib.Automata.LinearBounded.FiniteAcyclicRank
import Mathlib.Tactic

@[expose]
public section

/-!
# A nonconstant exact-two-matching language

This module records the smallest useful counterexample to an overly strong reading of the
clamped-boundary obstruction.  A right-moving transition has a two-predecessor target at the
right boundary, but an ordinary nonclamped target scans the next tape cell instead.  By making
the clamped target scan `⊢` while the next phase is enabled only on a chosen terminal, a machine
can move off the left marker and recognize a genuinely input-dependent language while its
complete raw configuration relation is still an exact union of two directed matchings.

The machine recognizes exactly the words whose first symbol is a fixed `chosen` terminal.
-/

namespace LBA.MachineTwoMatchings.FirstSymbol

open Relation

variable {T Γ : Type*} [DecidableEq T]

/-- The three phases of the two-step first-symbol recognizer. -/
public inductive State where
  | start
  | scan
  | halt
  deriving DecidableEq, Fintype, Repr

/-- The canonical tape symbol representing an input terminal. -/
public abbrev terminal (symbol : T) : EndAlpha T Γ :=
  Sum.inl (some (Sum.inl symbol))

/-- A two-step machine: move right from `⊢`, then accept exactly on the chosen terminal. -/
public def machine (chosen : T) : Machine (EndAlpha T Γ) State where
  transition
    | .start, .inr false => {(.scan, leftMark, .right)}
    | .scan, .inl (some (.inl symbol)) =>
        if symbol = chosen then {(.halt, terminal chosen, .stay)} else ∅
    | _, _ => ∅
  accept
    | .halt => true
    | _ => false
  initial := .start

@[simp]
public theorem machine_initial (chosen : T) : (machine (Γ := Γ) chosen).initial = .start := rfl

@[simp]
public theorem machine_accept_eq_true_iff (chosen : T) (state : State) :
    (machine (Γ := Γ) chosen).accept state = true ↔ state = .halt := by
  cases state <;> simp [machine]

/-- The color of a step is determined by its source.  A nonclamped first move has color zero;
the clamped first move and the terminal-checking stay move have color one. -/
public def stepColor {n : ℕ} (source : DLBA.Cfg (EndAlpha T Γ) State n) : Fin 2 :=
  match source.state with
  | .start => if source.tape.head.val < n then 0 else 1
  | .scan => 1
  | .halt => 1

/-- The two raw configuration layers of the example. -/
public def stepLayer (chosen : T) {n : ℕ} (color : Fin 2)
    (source target : DLBA.Cfg (EndAlpha T Γ) State n) : Prop :=
  Step (machine chosen) source target ∧ color = stepColor source

/-- The coloring is an exact partition of the complete raw step relation. -/
public theorem stepLayer_partition (chosen : T) {n : ℕ}
    (source target : DLBA.Cfg (EndAlpha T Γ) State n) :
    Step (machine chosen) source target ↔
      ∃! color, stepLayer chosen color source target := by
  constructor
  · intro hstep
    refine ⟨stepColor source, ⟨hstep, rfl⟩, ?_⟩
    intro color hcolor
    exact hcolor.2
  · rintro ⟨color, hcolor, _⟩
    exact hcolor.1

public theorem stepLayer_sub_step (chosen : T) {n : ℕ} (color : Fin 2)
    (source target : DLBA.Cfg (EndAlpha T Γ) State n)
    (hlayer : stepLayer chosen color source target) :
    Step (machine chosen) source target :=
  hlayer.1

/-! ## Exact descriptions of the two kinds of steps -/

private theorem step_from_start
    (chosen : T) {n : ℕ} {source target : DLBA.Cfg (EndAlpha T Γ) State n}
    (hstate : source.state = .start) (hstep : Step (machine chosen) source target) :
    source.tape.read = leftMark ∧
      target = ⟨.scan, (source.tape.write leftMark).moveHead .right⟩ := by
  rcases source with ⟨state, tape⟩
  simp only at hstate
  subst state
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  change (next, written, direction) ∈
    (machine chosen).transition .start tape.read at henabled
  rcases hread : tape.contents tape.head with (_ | marker)
  · simp [machine, hread] at henabled
  · cases marker
    · simp [machine, hread] at henabled
      rcases henabled with ⟨rfl, rfl, rfl⟩
      exact ⟨by simpa [DLBA.BoundedTape.read] using hread, rfl⟩
    · simp [machine, hread] at henabled

private theorem step_from_scan
    (chosen : T) {n : ℕ} {source target : DLBA.Cfg (EndAlpha T Γ) State n}
    (hstate : source.state = .scan) (hstep : Step (machine chosen) source target) :
    source.tape.read = terminal chosen ∧
      target = ⟨.halt, source.tape⟩ := by
  rcases source with ⟨state, tape⟩
  simp only at hstate
  subst state
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  change (next, written, direction) ∈
    (machine chosen).transition .scan tape.read at henabled
  rcases hread : tape.contents tape.head with (interior | marker)
  · rcases interior with (_ | tagged)
    · simp [machine, hread] at henabled
    · rcases tagged with (symbol | work)
      · by_cases hsymbol : symbol = chosen
        · subst symbol
          simp [machine, hread] at henabled
          rcases henabled with ⟨rfl, rfl, rfl⟩
          constructor
          · simpa [DLBA.BoundedTape.read] using hread
          · cases tape with
            | mk contents head =>
              simpa [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead] using hread.symm
        · simp [machine, hread, hsymbol] at henabled
      · simp [machine, hread] at henabled
  · simp [machine, hread] at henabled

private theorem no_step_from_halt
    (chosen : T) {n : ℕ} {source target : DLBA.Cfg (EndAlpha T Γ) State n}
    (hstate : source.state = .halt) :
    ¬ Step (machine chosen) source target := by
  rcases source with ⟨state, tape⟩
  simp only at hstate
  subst state
  rintro ⟨next, written, direction, henabled, _⟩
  simp [machine] at henabled

private theorem step_target_state
    (chosen : T) {n : ℕ} {source target : DLBA.Cfg (EndAlpha T Γ) State n}
    (hstep : Step (machine chosen) source target) :
    (source.state = .start ∧ target.state = .scan) ∨
      (source.state = .scan ∧ target.state = .halt) := by
  rcases source with ⟨state, tape⟩
  cases state with
  | start =>
      left
      exact ⟨rfl, congrArg DLBA.Cfg.state (step_from_start chosen rfl hstep).2⟩
  | scan =>
      right
      exact ⟨rfl, congrArg DLBA.Cfg.state (step_from_scan chosen rfl hstep).2⟩
  | halt => exact False.elim (no_step_from_halt chosen rfl hstep)

/-! ## Matching properties -/

private theorem write_read {A : Type*} {n : ℕ} (tape : DLBA.BoundedTape A n) :
    tape.write tape.read = tape := by
  cases tape with
  | mk contents head =>
    simp [DLBA.BoundedTape.write, DLBA.BoundedTape.read,
      Function.update_eq_self]

omit [DecidableEq T] in
private theorem nonclamped_right_source_eq_of_target_eq
    {n : ℕ} {left right : DLBA.BoundedTape (EndAlpha T Γ) n}
    (hleft : left.head.val < n) (hright : right.head.val < n)
    (htarget : left.moveHead .right = right.moveHead .right) :
    left = right := by
  have hcontents : left.contents = right.contents := by
    simpa [DLBA.BoundedTape.moveHead] using
      congrArg (fun tape => tape.contents) htarget
  have hheadSucc : left.head.val + 1 = right.head.val + 1 := by
    have := congrArg (fun tape => tape.head.val) htarget
    simpa [DLBA.BoundedTape.moveHead, hleft, hright] using this
  cases left with
  | mk leftContents leftHead =>
    cases right with
    | mk rightContents rightHead =>
      simp only at hcontents hheadSucc
      congr
      exact Fin.ext (by omega)

omit [DecidableEq T] in
private theorem clamped_right_source_eq_of_target_eq
    {n : ℕ} {left right : DLBA.BoundedTape (EndAlpha T Γ) n}
    (hleft : ¬ left.head.val < n) (hright : ¬ right.head.val < n)
    (htarget : left.moveHead .right = right.moveHead .right) :
    left = right := by
  have hcontents : left.contents = right.contents := by
    simpa [DLBA.BoundedTape.moveHead] using
      congrArg (fun tape => tape.contents) htarget
  have hleftHead : left.head.val = n := by omega
  have hrightHead : right.head.val = n := by omega
  cases left with
  | mk leftContents leftHead =>
    cases right with
    | mk rightContents rightHead =>
      simp only at hcontents hleftHead hrightHead
      congr
      exact Fin.ext (by omega)

private theorem stepLayer_rightUnique (chosen : T) {n : ℕ} (color : Fin 2) :
    Relator.RightUnique
      (stepLayer (Γ := Γ) chosen (n := n) color) := by
  intro source left right hleft hright
  cases hsource : source.state with
  | start =>
      have hl := (step_from_start chosen hsource hleft.1).2
      have hr := (step_from_start chosen hsource hright.1).2
      exact hl.trans hr.symm
  | scan =>
      have hl := (step_from_scan chosen hsource hleft.1).2
      have hr := (step_from_scan chosen hsource hright.1).2
      exact hl.trans hr.symm
  | halt => exact False.elim (no_step_from_halt chosen hsource hleft.1)

private theorem stepLayer_leftUnique (chosen : T) {n : ℕ} (color : Fin 2) :
    Relator.LeftUnique
      (stepLayer (Γ := Γ) chosen (n := n) color) := by
  intro left right target hleft hright
  rcases step_target_state chosen hleft.1 with hlstart | hlscan
  · rcases step_target_state chosen hright.1 with hrstart | hrscan
    · have hlmove := (step_from_start chosen hlstart.1 hleft.1).2
      have hrmove := (step_from_start chosen hrstart.1 hright.1).2
      have hleftRead := (step_from_start chosen hlstart.1 hleft.1).1
      have hrightRead := (step_from_start chosen hrstart.1 hright.1).1
      have hleftWrite : left.tape.write leftMark = left.tape := by
        rw [← hleftRead]
        exact write_read left.tape
      have hrightWrite : right.tape.write leftMark = right.tape := by
        rw [← hrightRead]
        exact write_read right.tape
      have htapeTarget : left.tape.moveHead .right = right.tape.moveHead .right := by
        have h := congrArg DLBA.Cfg.tape (hlmove.symm.trans hrmove)
        simpa [hleftWrite, hrightWrite] using h
      have hcolor : stepColor left = stepColor right := hleft.2.symm.trans hright.2
      simp [stepColor, hlstart.1, hrstart.1] at hcolor
      have htape : left.tape = right.tape := by
        by_cases hnonclamped : left.tape.head.val < n
        · have hrightNonclamped : right.tape.head.val < n := by
            simpa [hnonclamped] using hcolor
          exact nonclamped_right_source_eq_of_target_eq
            hnonclamped hrightNonclamped htapeTarget
        · have hrightClamped : ¬ right.tape.head.val < n := by
            simpa [hnonclamped] using hcolor
          exact clamped_right_source_eq_of_target_eq
            hnonclamped hrightClamped htapeTarget
      cases left with
      | mk leftState leftTape =>
        cases right with
        | mk rightState rightTape =>
          simp only at hlstart hrstart htape
          cases hlstart.1
          cases hrstart.1
          cases htape
          rfl
    · exact False.elim (State.noConfusion (hlstart.2.symm.trans hrscan.2))
  · rcases step_target_state chosen hright.1 with hrstart | hrscan
    · exact False.elim (State.noConfusion (hlscan.2.symm.trans hrstart.2))
    · have hl := (step_from_scan chosen hlscan.1 hleft.1).2
      have hr := (step_from_scan chosen hrscan.1 hright.1).2
      have htape : left.tape = right.tape := by
        have hhalt :
            (⟨State.halt, left.tape⟩ : DLBA.Cfg (EndAlpha T Γ) State n) =
              ⟨State.halt, right.tape⟩ := hl.symm.trans hr
        injection hhalt
      cases left with
      | mk leftState leftTape =>
        cases right with
        | mk rightState rightTape =>
          simp only at hlscan hrscan htape
          cases hlscan.1
          cases hrscan.1
          cases htape
          rfl

public theorem stepLayer_biUnique (chosen : T) {n : ℕ} (color : Fin 2) :
    Relator.BiUnique (stepLayer (Γ := Γ) chosen (n := n) color) :=
  ⟨stepLayer_leftUnique chosen color, stepLayer_rightUnique chosen color⟩

public theorem stepLayer_pathLengthAtMostOne
    (chosen : T) {n : ℕ} (color : Fin 2) :
    LinearTwoDiforestReachability.PathLengthAtMostOne
      (stepLayer (Γ := Γ) chosen (n := n) color) := by
  intro first middle last hfirst hlast
  rcases step_target_state chosen hfirst.1 with hfirstStart | hfirstScan
  · have hmiddle : middle.state = .scan := hfirstStart.2
    have hlastKind := step_target_state chosen hlast.1
    rcases hlastKind with hlastStart | hlastScan
    · simp [hmiddle] at hlastStart
    · have hfirstColor : color = stepColor first := hfirst.2
      have hlastColor : color = 1 := by simpa [stepColor, hmiddle] using hlast.2
      have hclamped : ¬ first.tape.head.val < n := by
        intro hlt
        have : color = 0 := by simpa [stepColor, hfirstStart.1, hlt] using hfirstColor
        exact Fin.zero_ne_one (this.symm.trans hlastColor)
      have htarget := (step_from_start chosen hfirstStart.1 hfirst.1).2
      have hreadMiddle : middle.tape.read = leftMark := by
        have hhead : first.tape.head.val = n := by omega
        have hread := (step_from_start chosen hfirstStart.1 hfirst.1).1
        have hwrite : first.tape.write leftMark = first.tape := by
          rw [← hread]
          exact write_read first.tape
        have hmoveStay : first.tape.moveHead .right = first.tape := by
          simp [DLBA.BoundedTape.moveHead, hclamped]
        have hmiddleTape := congrArg DLBA.Cfg.tape htarget
        rw [hwrite, hmoveStay] at hmiddleTape
        rw [hmiddleTape]
        exact hread
      have hreadChosen := (step_from_scan chosen hmiddle hlast.1).1
      cases hreadMiddle.symm.trans hreadChosen
  · have hmiddle : middle.state = .halt := hfirstScan.2
    exact no_step_from_halt chosen hmiddle hlast.1

/-- The example has an exact two-directed-matching partition at every raw tape width. -/
public theorem machine_hasTwoMatchingStepPartition (chosen : T) :
    (machine (Γ := Γ) chosen).HasTwoMatchingStepPartition := by
  refine ⟨fun _ => stepLayer chosen, ?_, ?_, ?_, ?_⟩
  · intro n source target
    exact stepLayer_partition chosen source target
  · intro n color source target
    exact stepLayer_sub_step chosen color source target
  · intro n color
    exact stepLayer_biUnique chosen color
  · intro n color
    exact stepLayer_pathLengthAtMostOne chosen color

/-! ## Global acyclicity -/

private def stateRank : State → ℕ
  | .start => 0
  | .scan => 1
  | .halt => 2

public theorem machine_configurationAcyclic (chosen : T) :
    (machine (Γ := Γ) chosen).ConfigurationAcyclic := by
  intro n cfg
  apply FiniteAcyclicRank.acyclic_of_strictRank
    (rank := fun current => stateRank current.state)
  intro source target hstep
  rcases step_target_state chosen hstep with hstart | hscan
  · simp [stateRank, hstart.1, hstart.2]
  · simp [stateRank, hscan.1, hscan.2]

/-! ## Exact recognized language -/

/-- Words whose first symbol is the chosen terminal. -/
public def language (chosen : T) : Language T :=
  fun word => word.head? = some chosen

private theorem accepts_start_iff
    (chosen : T) {n : ℕ} (tape : DLBA.BoundedTape (EndAlpha T Γ) n) :
    Accepts (machine chosen) ⟨.start, tape⟩ ↔
      tape.read = leftMark ∧
        ((tape.write leftMark).moveHead .right).read = terminal chosen := by
  constructor
  · rintro ⟨target, hreach, haccept⟩
    have htargetState : target.state = .halt :=
      (machine_accept_eq_true_iff chosen target.state).1 haccept
    rcases ReflTransGen.cases_head hreach with heq | ⟨middle, hfirst, htail⟩
    · subst target
      simp at htargetState
    · have hfirstData := step_from_start chosen rfl hfirst
      rcases ReflTransGen.cases_head htail with heq | ⟨last, hsecond, hrest⟩
      · subst middle
        simp [hfirstData.2] at htargetState
      · have hsecondData := step_from_scan chosen
          (congrArg DLBA.Cfg.state hfirstData.2) hsecond
        exact ⟨hfirstData.1, by simpa [hfirstData.2] using hsecondData.1⟩
  · rintro ⟨hleft, hchosen⟩
    let middle : DLBA.Cfg (EndAlpha T Γ) State n :=
      ⟨.scan, (tape.write leftMark).moveHead .right⟩
    let final : DLBA.Cfg (EndAlpha T Γ) State n := ⟨.halt, middle.tape⟩
    have hfirst : Step (machine chosen) ⟨.start, tape⟩ middle := by
      refine ⟨.scan, leftMark, .right, ?_, rfl⟩
      change (State.scan, leftMark, DLBA.Dir.right) ∈
        (machine chosen).transition .start tape.read
      rw [hleft]
      simp [machine]
    have hsecond : Step (machine chosen) middle final := by
      refine ⟨.halt, terminal chosen, .stay, ?_, ?_⟩
      · change middle.tape.read = terminal chosen at hchosen
        change (State.halt, terminal chosen, DLBA.Dir.stay) ∈
          (machine chosen).transition .scan middle.tape.read
        rw [hchosen]
        simp [machine]
      · change middle.tape.read = terminal chosen at hchosen
        have hwrite : middle.tape.write (terminal chosen) = middle.tape := by
          rw [← hchosen]
          exact write_read middle.tape
        simp [final, hwrite, DLBA.BoundedTape.moveHead]
    exact ⟨final, ReflTransGen.head hfirst (ReflTransGen.single hsecond), rfl⟩

omit [DecidableEq T] in
private theorem loadEnd_after_first_move_read
    (chosen : T) (word : List T) :
    (((loadEnd (Γ := Γ) word).write leftMark).moveHead .right).read = terminal chosen ↔
      word.head? = some chosen := by
  cases word with
  | nil =>
      simp [loadEnd, terminal, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead, DLBA.BoundedTape.read]
  | cons first rest =>
      simp [loadEnd, terminal, DLBA.BoundedTape.write,
        DLBA.BoundedTape.moveHead, DLBA.BoundedTape.read]

/-- The machine recognizes exactly the fixed-first-symbol language. -/
public theorem languageEnd_machine_eq (chosen : T) :
    LanguageEnd (machine (Γ := Γ) chosen) = language chosen := by
  funext word
  apply propext
  change Accepts (machine chosen) ⟨.start, loadEnd word⟩ ↔
    word.head? = some chosen
  rw [accepts_start_iff]
  have hleft : (loadEnd (Γ := Γ) word).read = leftMark := by
    simp [loadEnd, DLBA.BoundedTape.read]
  constructor
  · rintro ⟨_, hfirst⟩
    exact (loadEnd_after_first_move_read (Γ := Γ) chosen word).1 hfirst
  · intro hfirst
    exact ⟨hleft,
      (loadEnd_after_first_move_read (Γ := Γ) chosen word).2 hfirst⟩

end LBA.MachineTwoMatchings.FirstSymbol

/-! ## Language-class witnesses -/

/-- Every fixed-first-symbol language has an acyclic exact-two-matching LBA presentation. -/
public theorem is_AcyclicTwoMatchingLBA_firstSymbol
    {T : Type} [Fintype T] [DecidableEq T] (chosen : T) :
    is_AcyclicTwoMatchingLBA
      (LBA.MachineTwoMatchings.FirstSymbol.language chosen) := by
  let M := LBA.MachineTwoMatchings.FirstSymbol.machine (Γ := Unit) chosen
  refine ⟨Unit, LBA.MachineTwoMatchings.FirstSymbol.State,
    inferInstance, inferInstance, inferInstance, inferInstance, M, ?_, ?_, ?_⟩
  · exact LBA.MachineTwoMatchings.FirstSymbol.machine_configurationAcyclic chosen
  · exact LBA.MachineTwoMatchings.FirstSymbol.machine_hasTwoMatchingStepPartition chosen
  · exact LBA.MachineTwoMatchings.FirstSymbol.languageEnd_machine_eq chosen

/-- Forgetting acyclicity gives the corresponding witness in the general exact-two-matching
class. -/
public theorem is_TwoMatchingLBA_firstSymbol
    {T : Type} [Fintype T] [DecidableEq T] (chosen : T) :
    is_TwoMatchingLBA
      (LBA.MachineTwoMatchings.FirstSymbol.language chosen) :=
  is_TwoMatchingLBA_of_is_AcyclicTwoMatchingLBA
    (is_AcyclicTwoMatchingLBA_firstSymbol chosen)

/-- In particular the exact-two-matching class contains a nonconstant language over every
inhabited finite alphabet: the empty word is rejected and `[chosen]` is accepted. -/
public theorem exists_nonconstant_acyclicTwoMatchingLBA
    (T : Type) [Fintype T] [DecidableEq T] [Nonempty T] :
    ∃ L : Language T,
      is_AcyclicTwoMatchingLBA L ∧ ¬ L [] ∧ ∃ word, L word := by
  let chosen : T := Classical.choice inferInstance
  refine ⟨LBA.MachineTwoMatchings.FirstSymbol.language chosen,
    is_AcyclicTwoMatchingLBA_firstSymbol chosen, ?_, [chosen], ?_⟩
  · simp [LBA.MachineTwoMatchings.FirstSymbol.language]
  · simp [LBA.MachineTwoMatchings.FirstSymbol.language]

/-- General-class form of the same nonconstancy witness. -/
public theorem exists_nonconstant_twoMatchingLBA
    (T : Type) [Fintype T] [DecidableEq T] [Nonempty T] :
    ∃ L : Language T,
      is_TwoMatchingLBA L ∧ ¬ L [] ∧ ∃ word, L word := by
  obtain ⟨L, hclass, hempty, word, hword⟩ :=
    exists_nonconstant_acyclicTwoMatchingLBA T
  exact ⟨L, is_TwoMatchingLBA_of_is_AcyclicTwoMatchingLBA hclass,
    hempty, word, hword⟩

end
