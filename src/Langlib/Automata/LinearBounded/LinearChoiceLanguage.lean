module

public import Langlib.Automata.LinearBounded.GraphWalking.MarkedEulerProbe.ClassEquivalence
public import Langlib.Automata.LinearBounded.TwoMatchingChoiceBound

@[expose]
public section

/-!
# Languages with linearly many accepting branch events

This module promotes `LBA.BoundedNondeterminism.HasLinearAcceptingChoiceBound` from a promise on
one machine to a language class.  The bound is existential at the presentation level: one fixed
finite endmarker LBA and one fixed constant must work for every accepted input.  Rejected inputs
carry no promise.

Every deterministic-LBA language belongs to this class with constant zero.  Indeed, the standard
canonical-endmarker translation of a DLBA is functional, so none of its accepting paths encounters
a genuine branch configuration.  Conversely, compiling every linear-choice presentation to a
concrete DLBA remains open in the repository.

The negation is a useful possible-separation criterion.  If an LBA language has no linear-choice
presentation, then it is not a DLBA language.  More explicitly, every finite LBA presentation of
such a language and every proposed constant has an accepted input for which the bounded-choice
search fails.  This is a language-level lower bound over *all presentations*, unlike the existing
exponential-diamond witnesses for one particular presentation.
-/

open Classical

/-- A language has a finite canonical-endmarker LBA presentation in which every accepted input
has an accepting run using at most a fixed linear number of genuine branch events. -/
@[expose]
public def is_LinearChoiceLBA
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  ∃ (Gamma State : Type) (_ : Fintype Gamma) (_ : Fintype State)
    (_ : DecidableEq Gamma) (_ : DecidableEq State)
    (M : LBA.Machine (LBA.EndAlpha T Gamma) State) (choicesPerCell : Nat),
    LBA.BoundedNondeterminism.HasLinearAcceptingChoiceBound M choicesPerCell ∧
      LBA.LanguageEnd M = L

/-- Languages admitting a finite linear-choice LBA presentation. -/
@[expose]
public def LinearChoiceLBA
    {T : Type} [Fintype T] [DecidableEq T] : Set (Language T) :=
  setOf is_LinearChoiceLBA

namespace LBA.BoundedNondeterminism

/-- A functional LBA uses no genuine branch events on any accepting run. -/
public theorem acceptsWithChoiceEvents_zero_of_functional
    {Gamma State : Type} [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine Gamma State) (hfunctional : M.Functional)
    {n : Nat} {source : DLBA.Cfg Gamma State n}
    (haccept : LBA.Accepts M source) :
    AcceptsWithChoiceEvents M source 0 := by
  obtain ⟨target, hreach, hfinal⟩ := haccept
  have hnotBranch : ∀ cfg : DLBA.Cfg Gamma State n,
      ¬ (cfgGraph M).Branching cfg := by
    intro cfg hbranch
    obtain ⟨left, right, hleft, hright, hne⟩ :=
      (cfgGraph_branching_iff M cfg).mp hbranch
    exact hne (M.configurationStep_rightUnique_of_functional hfunctional hleft hright)
  have graphReach :
      Relation.ReflTransGen (cfgGraph M).Edge source target :=
    hreach.mono fun old new hstep ↦ (cfgGraph_edge_iff M old new).2 hstep
  have deterministicReach :
      Relation.ReflTransGen (cfgGraph M).DeterministicStep source target :=
    graphReach.mono fun old _new hedge ↦ ⟨hedge, hnotBranch old⟩
  have replay : (cfgGraph M).ReplayTrace [] source target :=
    (cfgGraph M).replayTrace_of_branchTrace (.finish deterministicReach)
  refine ⟨FiniteChoiceGraph.Schedule.ofList [] (by simp), target, ?_, hfinal⟩
  simpa using replay

/-- Consequently, every functional canonical-endmarker presentation satisfies the linear-choice
promise with the sharp constant zero. -/
public theorem hasLinearAcceptingChoiceBound_zero_of_functional
    {T Gamma State : Type} [Fintype T] [Fintype Gamma] [Fintype State]
    [DecidableEq T] [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine (LBA.EndAlpha T Gamma) State)
    (hfunctional : M.Functional) :
    HasLinearAcceptingChoiceBound M 0 := by
  intro input haccept
  simpa using acceptsWithChoiceEvents_zero_of_functional M hfunctional haccept

end LBA.BoundedNondeterminism

/-- Forgetting the accepting-choice promise gives an ordinary LBA presentation. -/
public theorem is_LBA_of_is_LinearChoiceLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_LinearChoiceLBA L) : is_LBA L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      M, _choicesPerCell, _hbound, hlanguage⟩
  exact ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState, M, hlanguage⟩

/-- The linear-choice class is contained in ordinary nondeterministic linear space. -/
public theorem LinearChoiceLBA_subset_LBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (LinearChoiceLBA : Set (Language T)) ⊆ LBA :=
  fun _ hL => is_LBA_of_is_LinearChoiceLBA hL

/-- Every exact-two-matching language has a linear-choice presentation, with constant one. -/
public theorem is_LinearChoiceLBA_of_is_TwoMatchingLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_TwoMatchingLBA L) : is_LinearChoiceLBA L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      M, hlayers, hlanguage⟩
  letI := hGamma
  letI := hState
  letI := hdecGamma
  letI := hdecState
  exact ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState, M, 1,
    LBA.BoundedNondeterminism.hasLinearAcceptingChoiceBound_one_of_twoMatchings
      M hlayers,
    hlanguage⟩

/-- Exact-two-matching languages form a subclass of the linear-choice languages. -/
public theorem TwoMatchingLBA_subset_LinearChoiceLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (TwoMatchingLBA : Set (Language T)) ⊆ LinearChoiceLBA :=
  fun _ hL => is_LinearChoiceLBA_of_is_TwoMatchingLBA hL

/-- Every deterministic-LBA language has a functional canonical-endmarker presentation and hence
a linear-choice presentation with constant zero. -/
public theorem is_LinearChoiceLBA_of_is_DLBA
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : is_DLBA L) : is_LinearChoiceLBA L := by
  rcases hL with
    ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
      acceptEmpty, M, hlanguage⟩
  letI := hGamma
  letI := hState
  letI := hdecGamma
  letI := hdecState
  let simulator := LBA.simMachine (DLBA.toLBA' M) acceptEmpty
  have hfunctional : simulator.Functional :=
    GraphWalking.EndmarkerNonclamping.simMachine_toLBA_functional M acceptEmpty
  refine ⟨Gamma, LBA.SimState (Option State), inferInstance, inferInstance,
    inferInstance, inferInstance, simulator, 0,
    LBA.BoundedNondeterminism.hasLinearAcceptingChoiceBound_zero_of_functional
      simulator hfunctional, ?_⟩
  rw [LBA.language_simMachine_eq, ← hlanguage]
  have key : DLBA.LanguageViaEmbed M (fun t ↦ some (Sum.inl t)) =
      LBA.LanguageViaEmbed (DLBA.toLBA' M) (fun t ↦ some (Sum.inl t)) :=
    dlba_language_eq_lba_language M (fun t ↦ some (Sum.inl t))
  funext word
  simp only [DLBA.LanguageRecognized, LBA.LanguageRecognized, key]

/-- The checked deterministic inclusion in the linear-choice class. -/
public theorem DLBA_subset_LinearChoiceLBA
    {T : Type} [Fintype T] [DecidableEq T] :
    (DLBA : Set (Language T)) ⊆ LinearChoiceLBA :=
  fun _ hL => is_LinearChoiceLBA_of_is_DLBA hL

/-- Candidate anti-pumping property: the language is LBA-recognizable but admits no presentation
with a fixed linear accepting-choice bound. -/
@[expose]
public def RequiresSuperlinearChoice
    {T : Type} [Fintype T] [DecidableEq T] (L : Language T) : Prop :=
  is_LBA L ∧ ¬ is_LinearChoiceLBA L

/-- A language requiring superlinear accepting choice cannot be deterministic linear-space. -/
public theorem not_is_DLBA_of_requiresSuperlinearChoice
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : RequiresSuperlinearChoice L) : ¬ is_DLBA L := by
  intro hdet
  exact hL.2 (is_LinearChoiceLBA_of_is_DLBA hdet)

/-- For a language satisfying the anti-pumping property, every particular finite LBA
presentation and every proposed linear constant fail on some accepted input. -/
public theorem exists_choiceBound_counterexample_of_requiresSuperlinearChoice
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hL : RequiresSuperlinearChoice L)
    {Gamma State : Type} [Fintype Gamma] [Fintype State]
    [DecidableEq Gamma] [DecidableEq State]
    (M : LBA.Machine (LBA.EndAlpha T Gamma) State)
    (hlanguage : LBA.LanguageEnd M = L) (choicesPerCell : Nat) :
    ∃ input : List T,
      LBA.Accepts M (LBA.initCfgEnd M input) ∧
        ¬ LBA.BoundedNondeterminism.AcceptsWithChoiceEvents M
          (LBA.initCfgEnd M input) ((input.length + 2) * choicesPerCell) := by
  have hnotBound :
      ¬ LBA.BoundedNondeterminism.HasLinearAcceptingChoiceBound
        M choicesPerCell := by
    intro hbound
    exact hL.2 ⟨Gamma, State, inferInstance, inferInstance,
      inferInstance, inferInstance, M, choicesPerCell, hbound, hlanguage⟩
  apply Classical.byContradiction
  intro hnone
  apply hnotBound
  intro input haccept
  by_contra hnotChoices
  exact hnone ⟨input, haccept, hnotChoices⟩

/-- Conversely, presentation-wise counterexamples to every proposed linear bound rule out the
linear-choice class.  This packages the quantifier order required of a genuine separating
language argument. -/
public theorem requiresSuperlinearChoice_of_presentation_counterexamples
    {T : Type} [Fintype T] [DecidableEq T] {L : Language T}
    (hLBA : is_LBA L)
    (hcounter :
      ∀ (Gamma State : Type) (_ : Fintype Gamma) (_ : Fintype State)
        (_ : DecidableEq Gamma) (_ : DecidableEq State)
        (M : LBA.Machine (LBA.EndAlpha T Gamma) State),
        LBA.LanguageEnd M = L →
          ∀ choicesPerCell : Nat,
            ∃ input : List T,
              LBA.Accepts M (LBA.initCfgEnd M input) ∧
                ¬ LBA.BoundedNondeterminism.AcceptsWithChoiceEvents M
                  (LBA.initCfgEnd M input)
                    ((input.length + 2) * choicesPerCell)) :
    RequiresSuperlinearChoice L := by
  refine ⟨hLBA, ?_⟩
  rintro ⟨Gamma, State, hGamma, hState, hdecGamma, hdecState,
    M, choicesPerCell, hbound, hlanguage⟩
  obtain ⟨input, haccept, hnotChoices⟩ :=
    hcounter Gamma State hGamma hState hdecGamma hdecState M
      hlanguage choicesPerCell
  exact hnotChoices (hbound input haccept)

end
