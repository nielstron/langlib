module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerFaithfulFiniteWindowRecurrence
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.RootFiniteWindowSchemaRecurrence

@[expose]
public section

/-!
# Critical-marker finite-window recurrence from root-syntactic sinking

The faithful recurrence cancels semantic equality through one fixed tuple of
arguments.  Root-syntactic sinking carries the stronger information needed
by the proof directly: a bounded prefix is induced by an open run from the
current root symbol template to one of its formal parameters.  Such a witness
replays on the open schema and selects a literal child without any
faithfulness assumption.

This file isolates the remaining operational premise.  A windowed pivot
trajectory has a uniform root window when, from every position of every
edge, either the remaining suffix is short or a bounded prefix root-sinks.
Conditional on that property, the complete critical-marker quantitative
construction follows with the same count-independent depth recurrence as the
faithful version.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

namespace TracePath

namespace StructuredPivotChain

namespace WindowedPivotTrajectory

/-- The minimal root-syntactic finite-window property used by the schema
recurrence.  It deliberately records only suffix length in the short branch:
the exact edge run is already a field of the trajectory. -/
@[expose] public def HasRootFiniteWindowBound
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (window : ℕ) : Prop :=
  ∀ j (position : trajectory.EdgePosition j),
    ((trajectory.toPivotTrajectory.edgeWords j).drop
        position.offset).length ≤ window ∨
      ∃ word remainder,
        (trajectory.toPivotTrajectory.edgeWords j).drop
            position.offset =
          word ++ remainder ∧
        word.length ≤ window ∧
        g.RootSinksBy position.term word

/-- Enlarging the positional window preserves the root-window property. -/
public theorem HasRootFiniteWindowBound.mono
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    {trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain}
    {small large : ℕ}
    (hrootWindow : trajectory.HasRootFiniteWindowBound small)
    (hle : small ≤ large) :
    trajectory.HasRootFiniteWindowBound large := by
  intro j position
  rcases hrootWindow j position with
    hshort | ⟨word, remainder, hword, hlength, hsinks⟩
  · exact Or.inl (hshort.trans hle)
  · exact Or.inr ⟨word, remainder, hword,
      hlength.trans hle, hsinks⟩

/-- The root-syntactic `M₂` dichotomy supplies the positional finite-window
property for every canonical windowed pivot trajectory. -/
public theorem hasRootFiniteWindowBound
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    (hbound : 0 < bound) :
    trajectory.HasRootFiniteWindowBound
      (g.structuredPivotM2Bound bound) := by
  intro j position
  rcases trajectory.edgePosition_reachesPivot_or_rootSinks
      hbound j position with hpivot | hsinks
  · obtain ⟨word, hword, hlength, _hrun⟩ := hpivot
    exact Or.inl (by simpa [hword] using hlength)
  · exact Or.inr hsinks

/-- Convert the positional root-window property to the ordinary-action
finite-window premise for one chosen edge. -/
public theorem boundedReachOrRootSinkAlong_of_edge_actions
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    {window : ℕ}
    (hrootWindow : trajectory.HasRootFiniteWindowBound window)
    (j : ℕ)
    (actions : List Action)
    (hedge :
      trajectory.toPivotTrajectory.edgeWords j =
        actions.map Sum.inl) :
    g.BoundedReachOrRootSinkAlong
      (trajectory.toPivotTrajectory.representatives j)
      actions window := by
  intro consumed remaining current hactions hcurrent
  have hdrop :
      (trajectory.toPivotTrajectory.edgeWords j).drop
          consumed.length =
        remaining.map Sum.inl := by
    rw [hedge, hactions, List.map_append]
    simp
  have hoffset :
      consumed.length ≤
        (trajectory.toPivotTrajectory.edgeWords j).length := by
    rw [hedge, hactions, List.length_map, List.length_append]
    omega
  let position : trajectory.EdgePosition j :=
    { offset := consumed.length
      offset_le := hoffset
      term := current
      run := by
        have htake :
            (trajectory.toPivotTrajectory.edgeWords j).take
                consumed.length =
              consumed.map Sum.inl := by
          rw [hedge, hactions, List.map_append]
          simp
        simpa [runActions?, htake] using hcurrent }
  rcases hrootWindow j position with
    hshort | ⟨word, labelRemainder, hword, hlength, hsinks⟩
  · left
    simpa [position, hdrop] using hshort
  · right
    have hmapSplit :
        remaining.map Sum.inl = word ++ labelRemainder := by
      rw [← hdrop]
      simpa [position] using hword
    obtain ⟨sinking, rest, hremaining, hwordMap,
        _hremainderMap⟩ :=
      List.map_eq_append_iff.mp hmapSplit
    refine ⟨sinking, rest, hremaining, ?_, ?_⟩
    · have hwordLength := congrArg List.length hwordMap
      simp at hwordLength
      omega
    · simpa [position, hwordMap] using hsinks

/-- Package the ordinary edge word, its exact run, and the induced
`BoundedReachOrRootSinkAlong` premise. -/
public theorem exists_actions_boundedReachOrRootSinkAlong_edge
    {g : EncodedFirstOrderGrammar Action}
    {initialLeft initialRight : RegularTerm}
    {path : TracePath g initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : g.groundPairCode initialLeft initialRight = true}
    {hinitial : g.TraceEquivalent initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path) hg hground hinitial bound}
    {chain : StructuredPivotChain
      hg hground hinitial bound initial}
    (trajectory : WindowedPivotTrajectory
      hg hground hinitial bound chain)
    {window : ℕ}
    (hrootWindow : trajectory.HasRootFiniteWindowBound window)
    (j : ℕ) :
    ∃ actions : List Action,
      trajectory.toPivotTrajectory.edgeWords j =
          actions.map Sum.inl ∧
        g.runActions? actions
            (trajectory.toPivotTrajectory.representatives j) =
          some (trajectory.toPivotTrajectory.representatives (j + 1)) ∧
        g.BoundedReachOrRootSinkAlong
          (trajectory.toPivotTrajectory.representatives j)
          actions window := by
  obtain ⟨actions, hedge⟩ := trajectory.exists_actions_edge j
  refine ⟨actions, hedge, ?_,
    trajectory.boundedReachOrRootSinkAlong_of_edge_actions
      hrootWindow j actions hedge⟩
  simpa [runActions?, hedge] using
    (trajectory.toPivotTrajectory.edge_run j)

end WindowedPivotTrajectory

namespace MarkerFreeGuardedProgressPresentation

/-- One guarded structured edge has a uniformly depth-bounded open successor
under the root-window premise, with no faithfulness condition on the fixed
argument tuple. -/
public theorem exists_rootFiniteWindowSchemaSuccessor
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (hrootWindows :
      chain.toWindowedPivotTrajectory.HasRootFiniteWindowBound
        (g.criticalMarkerStructuredPivotM2Bound bound))
    (j sourceDepth : ℕ)
    (hcurrentDepth :
      (package.presentation.schema j)
        |>.UnfoldingDepthAtMost sourceDepth) :
    Nonempty (FaithfulFiniteWindowSchemaSuccessor
      (g.withCriticalMarkers count)
      package.presentation.arity package.presentation.width
      package.presentation.arguments
      (package.presentation.schema (j + 1))
      (g.criticalMarkerResidualUnfoldingDepthBound
        (g.criticalMarkerStructuredPivotM2Bound bound)
        sourceDepth)) := by
  let extended := g.withCriticalMarkers count
  let trajectory := chain.toWindowedPivotTrajectory
  let pivotTrajectory := trajectory.toPivotTrajectory
  let edgeIndex := package.rebase.start + j
  obtain ⟨edgeActions, hedge, hedgeRun, hrootWindow⟩ :=
    trajectory.exists_actions_boundedReachOrRootSinkAlong_edge
      hrootWindows edgeIndex
  obtain ⟨originalActions, _hnonempty, hedgeOriginal,
      hactions, hschemaRun⟩ :=
    package.exists_originalActions_schema_succ_transition j
  have hedgeActions :
      edgeActions = originalActions.map Sum.inl := by
    apply (List.map_inj_right
      (fun _ _ h => Sum.inl.inj h :
        Function.Injective
          (Sum.inl :
            (Action ⊕ ℕ) → Label (Action ⊕ ℕ)))).mp
    exact hedge.symm.trans
      (by
        simpa [trajectory, pivotTrajectory, edgeIndex] using
          hedgeOriginal)
  subst edgeActions
  have hnoVariable :
      extended.NoVariableBefore
        (package.presentation.schema j)
        (originalActions.map Sum.inl) :=
    (package.noVariableAlong_suffix hactions).noVariableBefore
  have hsourceGround :
      (pivotTrajectory.representatives edgeIndex)
        |>.Ground extended.ranks :=
    pivotTrajectory.representative_ground edgeIndex
  have hcurrentWellFormed :
      (package.presentation.schema j).WellFormed
        extended.ranks package.presentation.arity :=
    (package.presentation.schema_supported j).1
  have hnextWellFormed :
      (package.presentation.schema (j + 1)).WellFormed
        extended.ranks package.presentation.arity :=
    (package.presentation.schema_supported (j + 1)).1
  have hsourceCurrent :
      (pivotTrajectory.representatives edgeIndex)
        |>.UnfoldingEquivalent
          ((package.presentation.schema j).instantiate
            package.presentation.arguments) := by
    simpa [pivotTrajectory, edgeIndex] using
      (package.presentation.schema_instance_matches j).symm
  have hschemaWindow :
      extended.BoundedReachOrSchemaSinkAlong
        (package.presentation.schema j)
        (originalActions.map Sum.inl)
        (g.criticalMarkerStructuredPivotM2Bound bound) := by
    apply hrootWindow.toSchema
      (g.withCriticalMarkers_wellFormed hg count)
      package.presentation.rankMax_le_arity
      hcurrentWellFormed
      (package.presentation.schema_hasPrefixWitness j)
      package.presentation.arguments_ground
      hsourceGround hsourceCurrent hedgeRun hnoVariable
  obtain ⟨successor⟩ :=
    exists_exactFiniteWindowSchemaSuccessor
      (g.withCriticalMarkers_wellFormed hg count)
      (arguments := package.presentation.arguments)
      package.presentation.rankMax_le_arity
      hcurrentWellFormed
      (package.presentation.schema_hasPrefixWitness j)
      hcurrentDepth hnextWellFormed hschemaRun hschemaWindow
  exact ⟨successor.mono
    (g.withCriticalMarkers_residualUnfoldingDepthBound_le
      count
      (g.criticalMarkerStructuredPivotM2Bound bound)
      sourceDepth)⟩

/-- The root-window recurrence propagates the same count-independent
semantic-depth bound through every guarded schema, without a faithful
argument tuple. -/
public theorem schema_unfoldingDepthAtMost_of_rootFiniteWindows
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (hrootWindows :
      chain.toWindowedPivotTrajectory.HasRootFiniteWindowBound
        (g.criticalMarkerStructuredPivotM2Bound bound)) :
    ∀ j,
      (package.presentation.schema j).UnfoldingDepthAtMost
        (g.criticalMarkerFiniteWindowSchemaDepth bound j) := by
  intro j
  induction j with
  | zero =>
      exact package.schema_zero_unfoldingDepthAtMost
  | succ j ih =>
      obtain ⟨successor⟩ :=
        package.exists_rootFiniteWindowSchemaSuccessor
          hrootWindows j
          (g.criticalMarkerFiniteWindowSchemaDepth bound j)
          ih
      intro depth index hdescendant
      have hdepth :=
        successor.equivalent_actual.unfoldingDepthAtMost
          successor.unfoldingDepthAtMost hdescendant
      simpa [criticalMarkerFiniteWindowSchemaDepth] using hdepth

/-- Every guarded schema has a finite guarded compaction under the
root-window premise. -/
public theorem
    exists_guardedFiniteSchemaCompaction_of_rootFiniteWindows
    {g : EncodedFirstOrderGrammar Action}
    {count : ℕ}
    {initialLeft initialRight filler : RegularTerm}
    {path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight}
    {hg : g.WellFormed}
    {hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true}
    {hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight}
    {bound : ℕ}
    {initial : StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (hrootWindows :
      chain.toWindowedPivotTrajectory.HasRootFiniteWindowBound
        (g.criticalMarkerStructuredPivotM2Bound bound))
    (j : ℕ) :
    Nonempty (GuardedFiniteSchemaCompaction g.ranks
      package.presentation.arity package.presentation.width
      package.presentation.depth
      (g.criticalMarkerFiniteWindowSchemaDepth bound j)
      (g.CriticalBoundaryGuard count
        (g.criticalDepthPrefix package.presentation.depth
          package.rebase.base))
      (package.presentation.schema j)) := by
  apply
    _root_.DCFEquivalence.EncodedFirstOrderGrammar.exists_guardedFiniteSchemaCompaction
      (package.presentation.schema_wellFormed_original j)
      (package.presentation.schema_hasPrefixWitness j)
      package.presentation.width_le_arity
  · have hrank := package.presentation.rankMax_le_arity
    rw [g.withCriticalMarkers_rankMax count] at hrank
    exact hrank
  · exact package.presentation.schema_guarded j
  · exact package.schema_unfoldingDepthAtMost_of_rootFiniteWindows
      hrootWindows j

end MarkerFreeGuardedProgressPresentation

end StructuredPivotChain

end TracePath

/-- Uniform root-syntactic finite windows for every marker-free,
nonrepeating maximal-progress package.  This is the sole additional
operational premise of the faithfulness-free critical recurrence. -/
@[expose] public def HasUniformMarkerStableRootFiniteWindows
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : Prop :=
  ∀ (hg : g.WellFormed)
    (count : ℕ)
    (initialLeft initialRight : RegularTerm)
    (path : TracePath (g.withCriticalMarkers count)
      initialLeft initialRight)
    (hground : (g.withCriticalMarkers count).groundPairCode
      initialLeft initialRight = true)
    (hinitial : (g.withCriticalMarkers count).TraceEquivalent
      initialLeft initialRight)
    (_hnoRepeat : ¬path.HasDerivedRepeat)
    (initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound)
    (chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial)
    (_package :
      TracePath.StructuredPivotChain.MarkerFreeGuardedProgressPresentation
        (hg := hg) (filler := initialLeft) chain),
    chain.toWindowedPivotTrajectory.HasRootFiniteWindowBound
      (g.criticalMarkerStructuredPivotM2Bound bound)

/-- Every positive structured-pivot bound gives the marker-count-independent
root window required by the critical recurrence. -/
public theorem hasUniformMarkerStableRootFiniteWindows
    (g : EncodedFirstOrderGrammar Action)
    (bound : ℕ) (hbound : 0 < bound) :
    g.HasUniformMarkerStableRootFiniteWindows bound := by
  intro _hg count _initialLeft _initialRight _path
    _hground _hinitial _hnoRepeat _initial chain _package
  exact
    (chain.toWindowedPivotTrajectory.hasRootFiniteWindowBound hbound).mono
      (g.withCriticalMarkers_structuredPivotM2Bound_le count bound)

/-- Uniform root windows discharge the complete guarded-compaction contract,
with the explicit count-independent depth recurrence. -/
public theorem
    hasUniformMarkerStableGuardedCompactionBound_of_rootFiniteWindows
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    (hrootWindows :
      g.HasUniformMarkerStableRootFiniteWindows bound) :
    g.HasUniformMarkerStableGuardedCompactionBound bound
      (g.criticalMarkerFiniteWindowSchemaDepth bound) := by
  intro hg count initialLeft initialRight path
    hground hinitial hnoRepeat initial chain package j
  exact
    package.exists_guardedFiniteSchemaCompaction_of_rootFiniteWindows
      (hrootWindows hg count initialLeft initialRight path
        hground hinitial hnoRepeat initial chain package)
      j

/-- Conditional on uniform root-syntactic finite windows, all qualitative
and quantitative branches assemble into the marker-stable stair base. -/
public theorem
    hasUniformMarkerStableWitnessedRegularActiveStairBase_of_rootFiniteWindows
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (hrootWindows :
      g.HasUniformMarkerStableRootFiniteWindows bound) :
    g.HasUniformMarkerStableWitnessedRegularActiveStairBase
      (g.criticalDepthPrefixTailBound bound) :=
  g.hasUniformMarkerStableWitnessedRegularActiveStairBase_of_guardedCompactionBound
    hg hnormal hexposureBound
    (g.criticalMarkerFiniteWindowSchemaDepth bound)
    (g.hasUniformMarkerStableGuardedCompactionBound_of_rootFiniteWindows
      hrootWindows)

end EncodedFirstOrderGrammar

end DCFEquivalence
