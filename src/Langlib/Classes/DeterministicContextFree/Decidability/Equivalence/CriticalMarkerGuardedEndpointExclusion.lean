module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedSchemaTransitions
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerWindowedTrajectoryInvariants
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailArgumentProtection
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.FixedTailSchemaTransitions

@[expose]
public section

/-!
# Excluding endpoint variables on marker-free guarded trajectories

`NoVariableBefore` intentionally says nothing about the endpoint of its
protected word.  On the canonical marker-free pivot trajectory that endpoint
case is nevertheless impossible: every next strong pivot edge is nonempty,
contains only injected original actions, and executes symbolically from the
current schema.  A variable-root schema cannot execute the first ordinary
action.

Consequently the guarded presentation enjoys the inclusive
`NoVariableAlong` invariant on every accumulated suffix, not merely the
proper-prefix version used for reflection.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- A nonempty ordinary-action word is disabled at every term semantically
equal to a variable. -/
public theorem runActions?_eq_none_of_unfoldingEquivalent_variable
    {g : EncodedFirstOrderGrammar Action}
    {source : RegularTerm} {x : ℕ} {word : List Action}
    (hsource :
      source.UnfoldingEquivalent (RegularTerm.variableTerm x))
    (hword : word ≠ []) :
    g.runActions? word source = none := by
  cases word with
  | nil => exact (hword rfl).elim
  | cons action word =>
      have hroot :
          source.rootNode? = some (.inl x) :=
        rootNode?_variable_of_unfoldingEquivalent
          hsource.symm
          (RegularTerm.variableTerm_rootNode? x)
      simp [runActions?, step?, rootRewrite?,
        RegularTerm.rootApplication?, hroot]

namespace TracePath.StructuredPivotChain

namespace MarkerFreeGuardedProgressPresentation

/-- Every canonical edge following the operational rebase is nonempty. -/
public theorem edgeWords_nonempty
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
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (j : ℕ) :
    ((chain.toWindowedPivotTrajectory).toPivotTrajectory
      |>.edgeWords j) ≠ [] := by
  have hbound : 0 < bound := by
    rw [← package.depth_eq]
    exact package.presentation.depth_positive
  change
    (chain.chosenWindowedPivotEdge j).toPivotEdge.word ≠ []
  exact (chain.chosenWindowedPivotEdge j).word_nonempty hbound

/-- Successive schemas in the marker-free guarded presentation are connected
by one nonempty word of injected original actions. -/
public theorem exists_originalActions_schema_succ_transition
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
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (j : ℕ) :
    ∃ originalActions : List Action,
      originalActions ≠ [] ∧
        ((chain.toWindowedPivotTrajectory).toPivotTrajectory
          |>.edgeWords (package.rebase.start + j)) =
            ((originalActions.map Sum.inl).map Sum.inl) ∧
        package.presentation.actions (j + 1) =
          package.presentation.actions j ++
            originalActions.map Sum.inl ∧
        (g.withCriticalMarkers count).runActions?
            (originalActions.map Sum.inl)
            (package.presentation.schema j) =
          some (package.presentation.schema (j + 1)) := by
  let trajectory :=
    (chain.toWindowedPivotTrajectory).toPivotTrajectory
  have hbound : 0 < bound := by
    rw [← package.depth_eq]
    exact package.presentation.depth_positive
  have hedges : ∀ k,
      NoCriticalMarkerActions (trajectory.edgeWords k) := by
    simpa [trajectory] using
      chain.toWindowedPivotTrajectory_edgeWords_noCriticalMarkerActions
        hg hbound package.endpoint_noMarkerActions
  obtain ⟨extendedActions, hedgeExtended⟩ :=
    package.rebase.exists_actions_edge j
  have hnoMarker :
      NoCriticalMarkerActions
        (extendedActions.map Sum.inl) := by
    rw [← hedgeExtended]
    exact hedges (package.rebase.start + j)
  obtain ⟨originalActions, hextended⟩ :=
    exists_originalActions_of_noCriticalMarkerActions hnoMarker
  have hedge :
      trajectory.edgeWords (package.rebase.start + j) =
        (originalActions.map Sum.inl).map Sum.inl := by
    rw [hedgeExtended, hextended]
  have horiginalNonempty : originalActions ≠ [] := by
    intro hnil
    subst originalActions
    apply package.edgeWords_nonempty
      (package.rebase.start + j)
    simpa [trajectory] using hedge
  have hmaps :
      (package.presentation.actions (j + 1)).map
          (Sum.inl :
            (Action ⊕ ℕ) → Label (Action ⊕ ℕ)) =
        (package.presentation.actions j ++
            originalActions.map Sum.inl).map
          (Sum.inl :
            (Action ⊕ ℕ) → Label (Action ⊕ ℕ)) := by
    rw [← package.presentation.labels_eq_actions (j + 1)]
    rw [package.rebase.labels_succ j]
    rw [package.presentation.labels_eq_actions j, hedge]
    exact List.map_append.symm
  have hactions :
      package.presentation.actions (j + 1) =
        package.presentation.actions j ++
          originalActions.map Sum.inl :=
    (List.map_inj_right
      (fun _ _ h => Sum.inl.inj h :
        Function.Injective
          (Sum.inl :
            (Action ⊕ ℕ) →
              Label (Action ⊕ ℕ)))).mp hmaps
  exact ⟨originalActions, horiginalNonempty, by
    simpa [trajectory] using hedge, hactions,
    package.presentation.symbolic_run_suffix hactions⟩

/-- No residual schema in a marker-free guarded progress presentation can
have a variable root, because it must execute the following nonempty edge. -/
public theorem schema_not_unfoldingEquivalent_variable
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
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (j x : ℕ) :
    ¬(package.presentation.schema j).UnfoldingEquivalent
      (RegularTerm.variableTerm x) := by
  intro hvariable
  obtain ⟨originalActions, hnonempty, _hedge,
      _hactions, hrun⟩ :=
    package.exists_originalActions_schema_succ_transition j
  have hnone :
      (g.withCriticalMarkers count).runActions?
          (originalActions.map Sum.inl)
          (package.presentation.schema j) = none :=
    runActions?_eq_none_of_unfoldingEquivalent_variable
      hvariable (by simpa using hnonempty)
  rw [hnone] at hrun
  contradiction

/-- The source critical-prefix proof also becomes inclusive: its only
previously unprotected point was the presented endpoint schema itself. -/
public theorem noVariableAlong_fromCriticalPrefix
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
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    (j : ℕ) :
    (g.withCriticalMarkers count).NoVariableAlong
      ((g.criticalDepthPrefix package.presentation.depth
        package.rebase.base).head.toRegularTerm)
      (package.presentation.actions j) := by
  have hbefore :=
    (package.presentation.residual j).noVariableBefore
  have hfull :=
    (package.presentation.residual j).symbolic_run
  intro stem remainder hword residual x hrun hvariable
  by_cases hremainder : remainder = []
  · subst remainder
    have hstem :
        stem = package.presentation.actions j := by
      simpa using hword.symm
    subst stem
    have hresidual :
        residual = package.presentation.schema j :=
      Option.some.inj (hrun.symm.trans hfull)
    subst residual
    exact package.schema_not_unfoldingEquivalent_variable j x
      hvariable
  · exact hbefore stem remainder hword hremainder
      residual x hrun hvariable

/-- The proper-prefix invariant of the guarded presentation strengthens to
inclusive endpoint protection on every accumulated action suffix. -/
public theorem noVariableAlong_suffix
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
    {initial : TracePath.StructuredDerivedBalancingState
      (path := path)
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound}
    {chain : TracePath.StructuredPivotChain
      (g.withCriticalMarkers_wellFormed hg count)
      hground hinitial bound initial}
    (package : MarkerFreeGuardedProgressPresentation
      (hg := hg) (filler := filler) chain)
    {first second : ℕ} {suffix : List (Action ⊕ ℕ)}
    (hactions :
      package.presentation.actions second =
        package.presentation.actions first ++ suffix) :
    (g.withCriticalMarkers count).NoVariableAlong
      (package.presentation.schema first) suffix := by
  have hbefore :=
    package.presentation.noVariableBefore_suffix hactions
  have hfull :=
    package.presentation.symbolic_run_suffix hactions
  intro stem remainder hsuffix residual x hrun hvariable
  by_cases hremainder : remainder = []
  · subst remainder
    have hstem : stem = suffix := by
      simpa using hsuffix.symm
    subst stem
    have hresidual :
        residual = package.presentation.schema second :=
      Option.some.inj (hrun.symm.trans hfull)
    subst residual
    exact package.schema_not_unfoldingEquivalent_variable second x
      hvariable
  · exact hbefore stem remainder hsuffix hremainder
      residual x hrun hvariable

end MarkerFreeGuardedProgressPresentation

end TracePath.StructuredPivotChain

end EncodedFirstOrderGrammar

end DCFEquivalence
