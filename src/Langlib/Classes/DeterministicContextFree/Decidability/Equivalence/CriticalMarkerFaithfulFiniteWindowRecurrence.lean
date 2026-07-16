module

public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedCompactedStairBase
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerGuardedEndpointExclusion
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.CriticalMarkerUniformM2
public import Langlib.Classes.DeterministicContextFree.Decidability.Equivalence.StructuredPivotFiniteWindowPremise

@[expose]
public section

/-!
# The faithful Proposition-49 recurrence on marker-free pivot packages

The structured pivot edge supplies the exact `M₂` reach-or-sink dichotomy at
every consumed prefix.  The guarded fixed-tail presentation supplies the
same exact edge between successive open schemas and excludes variables even
at its endpoint.  Consequently the general faithful finite-window
recurrence applies pointwise.

This file packages the entire quantitative construction, including a
marker-count-independent depth recurrence and guarded finite compactions.
The only remaining semantic hypothesis is explicit: the fixed boundary-tail
tuple of the presentation must reflect open unfolding equivalence.
-/

namespace DCFEquivalence

namespace EncodedFirstOrderGrammar

variable {Action : Type} [DecidableEq Action]

/-- Count-independent semantic-depth bound for the first guarded schema. -/
@[expose] public def criticalMarkerFiniteWindowInitialDepth
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ :=
  g.criticalMarkerResidualUnfoldingDepthBound
    (g.criticalMarkerStructuredPivotM2Bound bound)
    (FiniteHead.compiledDepthBound
      (g.ranks.foldr max 0) bound)

/-- Proposition-49 recurrence after the initial guarded residual. -/
@[expose] public def criticalMarkerFiniteWindowSchemaDepth
    (g : EncodedFirstOrderGrammar Action) (bound : ℕ) : ℕ → ℕ
  | 0 => g.criticalMarkerFiniteWindowInitialDepth bound
  | j + 1 =>
      g.criticalMarkerResidualUnfoldingDepthBound
        (g.criticalMarkerStructuredPivotM2Bound bound)
        (g.criticalMarkerFiniteWindowSchemaDepth bound j)

namespace TracePath.StructuredPivotChain

namespace MarkerFreeGuardedProgressPresentation

/-- The exact semantic condition needed to cancel equal fixed-tail
instances back to equal open schemas during every sinking descent. -/
@[expose] public def HasFaithfulArguments
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
      (hg := hg) (filler := filler) chain) : Prop :=
  (g.withCriticalMarkers count).UnfoldingFaithfulArguments
    package.presentation.arity
    package.presentation.arguments

/-- One rebased structured edge satisfies every premise of the faithful
finite-window recurrence.  Its result is widened immediately to the
count-independent marker envelope. -/
public theorem exists_faithfulFiniteWindowSchemaSuccessor
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
    (hfaithful : package.HasFaithfulArguments)
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
  have hbound : 0 < bound := by
    rw [← package.depth_eq]
    exact package.presentation.depth_positive
  obtain ⟨edgeActions, hedge, hedgeRun, hwindow⟩ :=
    trajectory.exists_actions_boundedReachOrSinkAlong_edge
      hbound edgeIndex
  obtain ⟨originalActions, _hnonempty, hedgeOriginal,
      hactions, _hschemaRun⟩ :=
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
  have hwindowUniform :
      extended.BoundedReachOrSinkAlong
        (pivotTrajectory.representatives edgeIndex)
        (originalActions.map Sum.inl)
        (g.criticalMarkerStructuredPivotM2Bound bound) := by
    apply hwindow.mono
    exact g.withCriticalMarkers_structuredPivotM2Bound_le
      count bound
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
  have htargetNext :
      (pivotTrajectory.representatives (edgeIndex + 1))
        |>.UnfoldingEquivalent
          ((package.presentation.schema (j + 1)).instantiate
            package.presentation.arguments) := by
    have hmatches :=
      (package.presentation.schema_instance_matches (j + 1)).symm
    simpa [pivotTrajectory, edgeIndex, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hmatches
  obtain ⟨successor⟩ :=
    _root_.DCFEquivalence.EncodedFirstOrderGrammar.exists_faithfulFiniteWindowSchemaSuccessor
      (g.withCriticalMarkers_wellFormed hg count)
      package.presentation.rankMax_le_arity
      hfaithful package.presentation.arguments_ground
      hcurrentWellFormed
      (package.presentation.schema_hasPrefixWitness j)
      hcurrentDepth hnextWellFormed hsourceGround
      hsourceCurrent htargetNext hedgeRun
      hwindowUniform hnoVariable
  exact ⟨successor.mono
    (g.withCriticalMarkers_residualUnfoldingDepthBound_le
      count
      (g.criticalMarkerStructuredPivotM2Bound bound)
      sourceDepth)⟩

/-- The zeroth guarded schema already has the uniform initial depth bound:
its accumulated rebase prefix is `M₂`-bounded and starts from the finite
critical depth-prefix head. -/
public theorem schema_zero_unfoldingDepthAtMost
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
      (hg := hg) (filler := filler) chain) :
    (package.presentation.schema 0).UnfoldingDepthAtMost
      (g.criticalMarkerFiniteWindowInitialDepth bound) := by
  let extended := g.withCriticalMarkers count
  let decomposition :=
    g.criticalDepthPrefix package.presentation.depth
      package.rebase.base
  have hrankedOriginal :
      decomposition.head.RankedBy g.ranks :=
    g.criticalDepthPrefix_head_rankedBy_original
      package.presentation.base_ground
      package.presentation.depth
  have hrankedExtended :
      decomposition.head.RankedBy extended.ranks := by
    simpa [extended, withCriticalMarkers_ranks] using
      hrankedOriginal.appendRanks
  have hvalid : decomposition.Valid :=
    g.criticalDepthPrefix_valid package.rebase.base
      package.presentation.depth
  have harity :
      decomposition.schemaArity extended.ranks =
        package.presentation.arity := by
    unfold DepthPrefix.schemaArity
      CriticalGuardedFixedTailPivotPresentation.arity
    rw [show extended.ranks.foldr max 0 =
        g.ranks.foldr max 0 by
      simpa [extended] using
        g.withCriticalMarkers_rankMax count]
    simp [decomposition, DepthPrefix.schemaArity]
  have hsourceWellFormed :
      decomposition.head.toRegularTerm.WellFormed
        extended.ranks package.presentation.arity := by
    rw [← harity]
    exact
      decomposition.head_wellFormed_schemaArity
        hvalid hrankedExtended
  have hsourceDepthExact :
      decomposition.head.toRegularTerm.UnfoldingDepthAtMost
        decomposition.head.compiledNodeCount :=
    FiniteHead.toRegularTerm_unfoldingDepthAtMost
      hrankedOriginal
  have hcompiled :
      decomposition.head.compiledNodeCount ≤
        FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) bound := by
    have hsize :=
      g.criticalDepthPrefix_schema_nodes_length_le
        package.presentation.base_ground
        package.presentation.depth
    rw [← package.depth_eq]
    simpa [decomposition,
      FiniteHead.toRegularTerm_nodes_length] using hsize
  have hsourceDepth :
      decomposition.head.toRegularTerm.UnfoldingDepthAtMost
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) bound) :=
    hsourceDepthExact.mono hcompiled
  have hsymbolicRun :
      extended.runActions? (package.presentation.actions 0)
          decomposition.head.toRegularTerm =
        some (package.presentation.schema 0) := by
    simpa [extended, decomposition] using
      (package.presentation.residual 0).symbolic_run
  have hactionsLengthLocal :
      (package.presentation.actions 0).length ≤
        extended.structuredPivotM2Bound bound := by
    have hlength := package.labels_zero_length_le
    rw [package.presentation.labels_eq_actions,
      List.length_map] at hlength
    exact hlength
  have hdepthExact :
      (package.presentation.schema 0).UnfoldingDepthAtMost
        (extended.residualUnfoldingDepthBound
          (package.presentation.actions 0).length
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) bound)) :=
    extended.runActions?_preserves_unfoldingDepthAtMost
      (g.withCriticalMarkers_wellFormed hg count)
      ⟨package.presentation.arity, hsourceWellFormed⟩
      hsourceDepth hsymbolicRun
  have hlocalM2 :
      extended.residualUnfoldingDepthBound
          (package.presentation.actions 0).length
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) bound) ≤
        extended.residualUnfoldingDepthBound
          (g.criticalMarkerStructuredPivotM2Bound bound)
          (FiniteHead.compiledDepthBound
            (g.ranks.foldr max 0) bound) :=
    extended.residualUnfoldingDepthBound_mono_steps'
      (hactionsLengthLocal.trans
        (g.withCriticalMarkers_structuredPivotM2Bound_le
          count bound))
  intro depth index hdescendant
  exact (hdepthExact hdescendant).trans
    (hlocalM2.trans
      (g.withCriticalMarkers_residualUnfoldingDepthBound_le
        count
        (g.criticalMarkerStructuredPivotM2Bound bound)
        (FiniteHead.compiledDepthBound
          (g.ranks.foldr max 0) bound)))

/-- Faithfulness propagates the uniform semantic-depth recurrence through
all guarded schemas of the maximal-progress presentation. -/
public theorem schema_unfoldingDepthAtMost
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
    (hfaithful : package.HasFaithfulArguments) :
    ∀ j,
      (package.presentation.schema j).UnfoldingDepthAtMost
        (g.criticalMarkerFiniteWindowSchemaDepth bound j) := by
  intro j
  induction j with
  | zero =>
      exact package.schema_zero_unfoldingDepthAtMost
  | succ j ih =>
      obtain ⟨successor⟩ :=
        package.exists_faithfulFiniteWindowSchemaSuccessor
          hfaithful j
          (g.criticalMarkerFiniteWindowSchemaDepth bound j)
          ih
      intro depth index hdescendant
      have hdepth :=
        successor.equivalent_actual.unfoldingDepthAtMost
          successor.unfoldingDepthAtMost hdescendant
      simpa [criticalMarkerFiniteWindowSchemaDepth] using hdepth

/-- The faithful recurrence supplies every pointwise guarded finite
compaction required by the marker-stable stair assembly. -/
public theorem exists_guardedFiniteSchemaCompaction
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
    (hfaithful : package.HasFaithfulArguments)
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
  · exact package.schema_unfoldingDepthAtMost
      hfaithful j

end MarkerFreeGuardedProgressPresentation

end TracePath.StructuredPivotChain

/-- Uniform faithfulness of the one fixed boundary tuple selected by every
marker-free maximal-progress package.  This is now the sole semantic premise
left by the complete Proposition-49 recurrence. -/
@[expose] public def HasUniformMarkerStableFaithfulArguments
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
    (package :
      TracePath.StructuredPivotChain.MarkerFreeGuardedProgressPresentation
        (hg := hg) (filler := initialLeft) chain),
    package.HasFaithfulArguments

/-- Uniform faithfulness discharges the entire guarded-compaction contract
with the explicit count-independent semantic-depth recurrence above. -/
public theorem
    hasUniformMarkerStableGuardedCompactionBound_of_faithfulArguments
    {g : EncodedFirstOrderGrammar Action} {bound : ℕ}
    (hfaithful :
      g.HasUniformMarkerStableFaithfulArguments bound) :
    g.HasUniformMarkerStableGuardedCompactionBound bound
      (g.criticalMarkerFiniteWindowSchemaDepth bound) := by
  intro hg count initialLeft initialRight path
    hground hinitial hnoRepeat initial chain package j
  exact package.exists_guardedFiniteSchemaCompaction
    (hfaithful hg count initialLeft initialRight path
      hground hinitial hnoRepeat initial chain package)
    j

/-- Once the sole faithfulness premise is supplied, all qualitative and
quantitative branches assemble into the uniform marker-stable stair base. -/
public theorem
    hasUniformMarkerStableWitnessedRegularActiveStairBase_of_faithfulArguments
    {g : EncodedFirstOrderGrammar Action} (hg : g.WellFormed)
    (hnormal : g.ExposingNormalForm)
    {bound : ℕ}
    (hexposureBound : g.exposureBound hnormal ≤ bound)
    (hfaithful :
      g.HasUniformMarkerStableFaithfulArguments bound) :
    g.HasUniformMarkerStableWitnessedRegularActiveStairBase
      (g.criticalDepthPrefixTailBound bound) :=
  g.hasUniformMarkerStableWitnessedRegularActiveStairBase_of_guardedCompactionBound
    hg hnormal hexposureBound
    (g.criticalMarkerFiniteWindowSchemaDepth bound)
    (g.hasUniformMarkerStableGuardedCompactionBound_of_faithfulArguments
      hfaithful)

end EncodedFirstOrderGrammar

end DCFEquivalence
