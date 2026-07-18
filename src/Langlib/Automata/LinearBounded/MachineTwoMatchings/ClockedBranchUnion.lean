module

public import Langlib.Automata.LinearBounded.AcyclicClock.Functional
public import Langlib.Automata.LinearBounded.AcyclicClock.LanguageEquivalence
public import Langlib.Automata.LinearBounded.MachineTwoMatchings.BranchFunctional
import Mathlib.Tactic

@[expose]
public section

/-!
# One acyclic machine for all clocked first-move branches

For a machine whose nondeterminism is confined to its first configuration edge,
`Machine.pinFirst` gives one functional machine for every possible first transition triple.
Applying the guarded clock separately makes every one of those machines globally acyclic, but
initially leaves a finite family of machines rather than one presentation.

This file folds that family into one endmarker LBA.  A fresh outer boot state chooses the finite
branch index by a symbol-preserving stay move.  The running state then carries that index forever
and executes the corresponding clocked pinned machine verbatim.  Thus all branches share one
finite tape alphabet and one finite control type.  The wrapper is globally configuration-acyclic,
its running states are locally functional, and its canonical language is exactly the union of
the clocked (hence also the unclocked) pinned languages.
-/

namespace LBA.MachineTwoMatchings.ClockedBranchUnion

open Classical Relation

variable {T Γ Λ : Type*}

/-- An index for the machine obtained by pinning one possible source transition triple. -/
public abbrev BranchIndex (T Γ Λ : Type*) :=
  Λ × EndAlpha T Γ × DLBA.Dir

/-- The common tape alphabet of every clocked pinned branch. -/
public abbrev TapeAlpha (T Γ Λ : Type*)
    [Fintype T] [Fintype Γ] [Fintype Λ] :=
  AcyclicClock.TapeAlpha T Γ (FirstMoveState Λ)

/-- A fresh choice state followed by a tagged state of one clocked pinned branch. -/
public inductive State (T Γ Λ : Type*) where
  | boot
  | run (first : BranchIndex T Γ Λ)
      (state : AcyclicClock.State (FirstMoveState Λ))
deriving Fintype, DecidableEq

variable [Fintype T] [Fintype Γ] [Fintype Λ]

/-- The globally acyclic clocked machine belonging to one pinned first transition. -/
@[expose]
public noncomputable def branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) :
    Machine (TapeAlpha T Γ Λ) (AcyclicClock.State (FirstMoveState Λ)) :=
  AcyclicClock.machine (M.pinFirst first)

/-- Tag a transition of one clocked branch with its immutable branch index. -/
@[expose]
public def liftMove (first : BranchIndex T Γ Λ)
    (move : AcyclicClock.State (FirstMoveState Λ) × TapeAlpha T Γ Λ × DLBA.Dir) :
    State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir :=
  (.run first move.1, move.2.1, move.2.2)

/-- The transition table of the common branch-union machine.

The outer boot move only records the branch index.  It rewrites the scanned symbol with itself
and stays in place, so the selected clocked branch starts on exactly the original tape. -/
@[expose]
public noncomputable def transition
    (M : Machine (EndAlpha T Γ) Λ) :
    State T Γ Λ → TapeAlpha T Γ Λ →
      Set (State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir)
  | .boot, symbol =>
      Set.range fun first : BranchIndex T Γ Λ =>
        (.run first (branch M first).initial, symbol, .stay)
  | .run first state, symbol =>
      liftMove first '' (branch M first).transition state symbol

/-- One common endmarker machine containing every clocked pinned branch. -/
@[expose]
public noncomputable def machine
    (M : Machine (EndAlpha T Γ) Λ) :
    Machine (TapeAlpha T Γ Λ) (State T Γ Λ) where
  transition := transition M
  accept
    | .boot => false
    | .run first state => (branch M first).accept state
  initial := .boot

/-- Embed a configuration of one clocked branch in the tagged running phase. -/
@[expose]
public def runCfg (first : BranchIndex T Γ Λ) {n : ℕ}
    (cfg : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n :=
  ⟨.run first cfg.state, cfg.tape⟩

/-- Put a tape at the fresh outer choice state. -/
@[expose]
public def bootCfg {n : ℕ} (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n :=
  ⟨.boot, tape⟩

/-- Rewriting the currently scanned symbol and staying put leaves a bounded tape unchanged. -/
private theorem write_read_stay {A : Type*} {n : ℕ}
    (tape : DLBA.BoundedTape A n) :
    (tape.write tape.read).moveHead .stay = tape := by
  rcases tape with ⟨contents, head⟩
  rw [DLBA.BoundedTape.mk.injEq]
  constructor
  · simp [DLBA.BoundedTape.write, DLBA.BoundedTape.moveHead,
      Function.update_eq_self]
  · rfl

/-- Choosing an index performs one symbol-preserving outer boot step. -/
public theorem step_boot
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    Step (machine M) (bootCfg tape)
      (runCfg first ⟨(branch M first).initial, tape⟩) := by
  refine ⟨.run first (branch M first).initial, tape.read, .stay, ?_, ?_⟩
  · exact ⟨first, rfl⟩
  · rw [DLBA.Cfg.mk.injEq]
    exact ⟨rfl, (write_read_stay tape).symm⟩

/-- Every step in a running branch is reproduced exactly by the common wrapper. -/
public theorem step_run_of_step_branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    (hstep : Step (branch M first) source target) :
    Step (machine M) (runCfg first source) (runCfg first target) := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  exact ⟨.run first next, written, direction, ⟨(next, written, direction), henabled, rfl⟩,
    rfl⟩

/-- A wrapper step from a running branch preserves its index and projects to a branch step. -/
public theorem step_branch_of_step_run
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    {source : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n}
    (hstep : Step (machine M) (runCfg first source) target) :
    ∃ branchTarget,
      target = runCfg first branchTarget ∧
      Step (branch M first) source branchTarget := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  rcases henabled with ⟨move, hmove, heq⟩
  rcases move with ⟨branchNext, branchWritten, branchDirection⟩
  simp only [liftMove] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  exact ⟨⟨branchNext, (source.tape.write written).moveHead direction⟩,
    rfl, ⟨branchNext, written, direction, hmove, rfl⟩⟩

/-- A complete branch run lifts to the tagged phase of the wrapper. -/
public theorem reaches_run_of_reaches_branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    (hreach : Reaches (branch M first) source target) :
    Reaches (machine M) (runCfg first source) (runCfg first target) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (step_run_of_step_branch M first hstep)

/-- A wrapper run beginning in a tagged branch never changes branch and projects exactly. -/
public theorem reaches_branch_of_reaches_run
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    {source : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n}
    (hreach : Reaches (machine M) (runCfg first source) target) :
    ∃ branchTarget,
      target = runCfg first branchTarget ∧
      Reaches (branch M first) source branchTarget := by
  induction hreach with
  | refl => exact ⟨source, rfl, .refl⟩
  | @tail middle target hreach hstep ih =>
      obtain ⟨branchMiddle, rfl, hbranchReach⟩ := ih
      obtain ⟨branchTarget, rfl, hbranchStep⟩ :=
        step_branch_of_step_run M first hstep
      exact ⟨branchTarget, rfl, hbranchReach.tail hbranchStep⟩

/-- Acceptance of one clocked branch lifts through the fresh outer choice state. -/
public theorem accepts_machine_of_accepts_branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (haccept : Accepts (branch M first) ⟨(branch M first).initial, tape⟩) :
    Accepts (machine M) (bootCfg tape) := by
  obtain ⟨target, hreach, hfinal⟩ := haccept
  exact ⟨runCfg first target,
    ReflTransGen.head (step_boot M first tape)
      (reaches_run_of_reaches_branch M first hreach), hfinal⟩

/-- Every step out of the outer boot state chooses one branch and leaves the tape unchanged. -/
public theorem exists_eq_runCfg_of_step_boot
    (M : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n}
    (hstep : Step (machine M) (bootCfg tape) target) :
    ∃ first : BranchIndex T Γ Λ,
      target = runCfg first ⟨(branch M first).initial, tape⟩ := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  rcases henabled with ⟨first, heq⟩
  rcases heq with ⟨rfl, rfl, rfl⟩
  refine ⟨first, ?_⟩
  rw [DLBA.Cfg.mk.injEq]
  exact ⟨rfl, write_read_stay tape⟩

/-- Wrapper acceptance from the outer boot state is exactly acceptance by one clocked branch. -/
public theorem accepts_machine_iff_exists_accepts_branch
    (M : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    Accepts (machine M) (bootCfg tape) ↔
      ∃ first : BranchIndex T Γ Λ,
        Accepts (branch M first) ⟨(branch M first).initial, tape⟩ := by
  constructor
  · rintro ⟨target, hreach, hfinal⟩
    rcases ReflTransGen.cases_head hreach with heq | ⟨middle, hfirst, htail⟩
    · subst target
      simp [bootCfg, machine] at hfinal
    · obtain ⟨first, rfl⟩ := exists_eq_runCfg_of_step_boot M tape hfirst
      obtain ⟨branchTarget, rfl, hbranchReach⟩ :=
        reaches_branch_of_reaches_run M first htail
      exact ⟨first, branchTarget, hbranchReach, hfinal⟩
  · rintro ⟨first, haccept⟩
    exact accepts_machine_of_accepts_branch M first tape haccept

/-- The common machine recognizes the finite union of the clocked branch languages. -/
public theorem languageEnd_machine_iff_exists_languageEnd_branch
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    LanguageEnd (machine M) input ↔
      ∃ first : BranchIndex T Γ Λ, LanguageEnd (branch M first) input := by
  exact accepts_machine_iff_exists_accepts_branch M (loadEnd input)

/-- Clocking does not change any pinned branch language, so the wrapper is also exactly the
finite union of the original unclocked pinned languages. -/
public theorem languageEnd_machine_iff_exists_languageEnd_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    LanguageEnd (machine M) input ↔
      ∃ first : BranchIndex T Γ Λ, LanguageEnd (M.pinFirst first) input := by
  rw [languageEnd_machine_iff_exists_languageEnd_branch]
  constructor
  · rintro ⟨first, hfirst⟩
    refine ⟨first, ?_⟩
    change LanguageEnd (AcyclicClock.machine (M.pinFirst first)) input at hfirst
    exact (congrFun (AcyclicClock.languageEnd_machine_eq (M.pinFirst first)) input).mp hfirst
  · rintro ⟨first, hfirst⟩
    refine ⟨first, ?_⟩
    change LanguageEnd (AcyclicClock.machine (M.pinFirst first)) input
    exact (congrFun (AcyclicClock.languageEnd_machine_eq (M.pinFirst first)) input).mpr hfirst

/-- Under the exact two-matching hypothesis, the common clocked wrapper recognizes the source
machine's language. -/
public theorem languageEnd_machine_eq
    (M : Machine (EndAlpha T Γ) Λ) (hlayers : M.HasTwoMatchingStepPartition) :
    LanguageEnd (machine M) = LanguageEnd M := by
  funext input
  apply propext
  rw [languageEnd_machine_iff_exists_languageEnd_pinFirst]
  exact (M.languageEnd_pinFirst_iff hlayers input).symm

/-- Every transition target is a running state; the fresh outer boot state has no incoming
edges, even on malformed tapes. -/
public theorem target_ne_boot_of_step
    (M : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n}
    (hstep : Step (machine M) source target) :
    target.state ≠ .boot := by
  rcases source with ⟨sourceState, tape⟩
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  cases sourceState with
  | boot =>
      rcases henabled with ⟨first, heq⟩
      rcases heq with ⟨rfl, rfl, rfl⟩
      simp
  | run first state =>
      rcases henabled with ⟨move, _hmove, heq⟩
      rcases move with ⟨nextState, nextSymbol, nextDirection⟩
      simp only [liftMove] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      simp

/-- The target of every nonempty wrapper path is a running state. -/
public theorem target_ne_boot_of_transGen
    (M : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n}
    (hreach : TransGen (Step (machine M)) source target) :
    target.state ≠ .boot := by
  induction hreach using TransGen.head_induction_on with
  | single hstep => exact target_ne_boot_of_step M hstep
  | head _ _ ih => exact ih

/-- Positive wrapper paths starting inside a branch project edge-for-edge to positive paths of
that clocked branch. -/
public theorem transGen_branch_of_transGen_run
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    {source : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    {target : DLBA.Cfg (TapeAlpha T Γ Λ) (State T Γ Λ) n}
    (hreach : TransGen (Step (machine M)) (runCfg first source) target) :
    ∃ branchTarget,
      target = runCfg first branchTarget ∧
      TransGen (Step (branch M first)) source branchTarget := by
  induction hreach with
  | single hstep =>
      obtain ⟨branchTarget, rfl, hbranchStep⟩ :=
        step_branch_of_step_run M first hstep
      exact ⟨branchTarget, rfl, .single hbranchStep⟩
  | @tail middle target hreach hstep ih =>
      obtain ⟨branchMiddle, rfl, hbranchReach⟩ := ih
      obtain ⟨branchTarget, rfl, hbranchStep⟩ :=
        step_branch_of_step_run M first hstep
      exact ⟨branchTarget, rfl, hbranchReach.tail hbranchStep⟩

/-- Folding all clocked branches under one fresh choice state preserves global configuration
acyclicity. -/
public theorem machine_configurationAcyclic
    (M : Machine (EndAlpha T Γ) Λ) :
    (machine M).ConfigurationAcyclic := by
  intro n cfg hcycle
  rcases cfg with ⟨state, tape⟩
  cases state with
  | boot =>
      exact target_ne_boot_of_transGen M hcycle rfl
  | run first state =>
      change TransGen (Step (machine M))
        (runCfg first (⟨state, tape⟩ : DLBA.Cfg (TapeAlpha T Γ Λ)
          (AcyclicClock.State (FirstMoveState Λ)) n))
        (runCfg first (⟨state, tape⟩ : DLBA.Cfg (TapeAlpha T Γ Λ)
          (AcyclicClock.State (FirstMoveState Λ)) n)) at hcycle
      obtain ⟨branchTarget, heq, hbranchCycle⟩ :=
        transGen_branch_of_transGen_run M first hcycle
      have htarget : branchTarget =
          (⟨state, tape⟩ : DLBA.Cfg (TapeAlpha T Γ Λ)
            (AcyclicClock.State (FirstMoveState Λ)) n) := by
        cases branchTarget
        simp only [runCfg] at heq
        cases heq
        rfl
      subst branchTarget
      exact AcyclicClock.machine_configurationAcyclic (M.pinFirst first)
        n ⟨state, tape⟩ hbranchCycle

/-- The wrapper packages the two properties needed by the sequential finite-union compiler:
global termination and exact preservation of the original two-matching language. -/
public theorem machine_acyclic_and_language_eq
    (M : Machine (EndAlpha T Γ) Λ) (hlayers : M.HasTwoMatchingStepPartition) :
    (machine M).ConfigurationAcyclic ∧
      LanguageEnd (machine M) = LanguageEnd M :=
  ⟨machine_configurationAcyclic M, languageEnd_machine_eq M hlayers⟩

/-- Every tagged running state is locally functional.  This is the clock compiler's
functionality-preservation theorem applied to the functional pinned branch. -/
public theorem transition_run_subsingleton
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ)
    (state : AcyclicClock.State (FirstMoveState Λ))
    (symbol : TapeAlpha T Γ Λ) :
    ((machine M).transition (.run first state) symbol).Subsingleton := by
  exact (AcyclicClock.machine_functional (M.pinFirst first)
    (M.pinFirst_functional first) state symbol).image (liftMove first)

/-- The outer transition triple that selects `first` while preserving the scanned symbol. -/
@[expose]
public noncomputable def outerMove (M : Machine (EndAlpha T Γ) Λ)
    (first : BranchIndex T Γ Λ) (symbol : TapeAlpha T Γ Λ) :
    State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir :=
  (.run first (branch M first).initial, symbol, .stay)

/-- Every outer branch-selection move is enabled at the wrapper's boot state. -/
public theorem outerMove_mem
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ)
    (symbol : TapeAlpha T Γ Λ) :
    outerMove M first symbol ∈ (machine M).transition .boot symbol :=
  ⟨first, rfl⟩

/-- If the source transition set at a running configuration is a subsingleton, a pinned machine
replays a supplied source step exactly in its running phase. -/
private theorem step_pinFirst_run_of_step_of_subsingleton
    {A Q : Type*} (N : Machine A Q) (pinned : Q × A × DLBA.Dir) {n : ℕ}
    {source target : DLBA.Cfg A Q n}
    (hsub : (N.transition source.state source.tape.read).Subsingleton)
    (hstep : Step N source target) :
    Step (N.pinFirst pinned) (N.pinFirstRunCfg source)
      (N.pinFirstRunCfg target) := by
  rcases hstep with ⟨next, written, direction, henabled, rfl⟩
  obtain ⟨selected, hselected⟩ := N.exists_selectedMove_of_mem henabled
  have hselectedEq : selected = (next, written, direction) :=
    hsub (N.selectedMove_mem hselected) henabled
  subst selected
  refine ⟨.run next, written, direction, ?_, rfl⟩
  change (FirstMoveState.run next, written, direction) ∈
    (match N.selectedMove source.state source.tape.read with
    | none => ∅
    | some move => {(FirstMoveState.run move.1, move.2.1, move.2.2)})
  rw [hselected]
  rfl

/-- One clocked branch step lifts through a pinned outer choice. -/
public theorem step_pinFirst_run_of_step_branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ)
    (pinned : State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir) {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    (hstep : Step (branch M first) source target) :
    Step ((machine M).pinFirst pinned)
      ((machine M).pinFirstRunCfg (runCfg first source))
      ((machine M).pinFirstRunCfg (runCfg first target)) := by
  apply step_pinFirst_run_of_step_of_subsingleton
    (machine M) pinned (transition_run_subsingleton M first source.state source.tape.read)
  exact step_run_of_step_branch M first hstep

/-- A whole clocked branch run lifts through a pinned outer choice. -/
public theorem reaches_pinFirst_run_of_reaches_branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ)
    (pinned : State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir) {n : ℕ}
    {source target : DLBA.Cfg (TapeAlpha T Γ Λ)
      (AcyclicClock.State (FirstMoveState Λ)) n}
    (hreach : Reaches (branch M first) source target) :
    Reaches ((machine M).pinFirst pinned)
      ((machine M).pinFirstRunCfg (runCfg first source))
      ((machine M).pinFirstRunCfg (runCfg first target)) := by
  induction hreach with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.tail (step_pinFirst_run_of_step_branch M first pinned hstep)

/-- Pinning the outer selection move for a branch preserves every accepting run of that branch. -/
public theorem accepts_pinFirst_outerMove_of_accepts_branch
    (M : Machine (EndAlpha T Γ) Λ) (first : BranchIndex T Γ Λ) {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n)
    (haccept : Accepts (branch M first) ⟨(branch M first).initial, tape⟩) :
    Accepts ((machine M).pinFirst (outerMove M first tape.read))
      ((machine M).pinFirstBootCfg tape) := by
  obtain ⟨target, hreach, hfinal⟩ := haccept
  have hboot := (machine M).step_pinFirst_boot tape
    (outerMove M first tape.read) (outerMove_mem M first tape.read)
  simp only [outerMove] at hboot
  rw [write_read_stay tape] at hboot
  have hrun := reaches_pinFirst_run_of_reaches_branch M first
    (outerMove M first tape.read) hreach
  exact ⟨(machine M).pinFirstRunCfg (runCfg first target),
    ReflTransGen.head hboot hrun, hfinal⟩

/-- The wrapper's only nondeterminism is its outer choice: its language from every boot tape is
exactly the union of all machines obtained by pinning one outer transition triple. -/
public theorem accepts_machine_iff_exists_accepts_pinFirst
    (M : Machine (EndAlpha T Γ) Λ) {n : ℕ}
    (tape : DLBA.BoundedTape (TapeAlpha T Γ Λ) n) :
    Accepts (machine M) (bootCfg tape) ↔
      ∃ pinned : State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir,
        Accepts ((machine M).pinFirst pinned)
          ((machine M).pinFirstBootCfg tape) := by
  constructor
  · intro haccept
    obtain ⟨first, hbranch⟩ :=
      (accepts_machine_iff_exists_accepts_branch M tape).mp haccept
    exact ⟨outerMove M first tape.read,
      accepts_pinFirst_outerMove_of_accepts_branch M first tape hbranch⟩
  · rintro ⟨pinned, haccept⟩
    exact (machine M).accepts_of_accepts_pinFirst pinned tape haccept

/-- On canonical inputs, the common wrapper language is exactly the finite union of all its
pinned-first-transition languages. -/
public theorem languageEnd_machine_iff_exists_languageEnd_outerPinFirst
    (M : Machine (EndAlpha T Γ) Λ) (input : List T) :
    LanguageEnd (machine M) input ↔
      ∃ pinned : State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir,
        LanguageEnd ((machine M).pinFirst pinned) input := by
  exact accepts_machine_iff_exists_accepts_pinFirst M (loadEnd input)

/-- Every pinned outer branch is functional. -/
public theorem pinFirst_functional
    (M : Machine (EndAlpha T Γ) Λ)
    (pinned : State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir) :
    ((machine M).pinFirst pinned).Functional :=
  (machine M).pinFirst_functional pinned

/-- Every pinned outer branch is globally configuration-acyclic. -/
public theorem pinFirst_configurationAcyclic
    (M : Machine (EndAlpha T Γ) Λ)
    (pinned : State T Γ Λ × TapeAlpha T Γ Λ × DLBA.Dir) :
    ((machine M).pinFirst pinned).ConfigurationAcyclic :=
  (machine M).configurationAcyclic_pinFirst (machine_configurationAcyclic M) pinned

end LBA.MachineTwoMatchings.ClockedBranchUnion

end
